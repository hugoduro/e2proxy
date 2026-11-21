#!/usr/bin/env python3
"""
e2proxy - proxy que corrige a PAT/PMT dos streams Enigma2 (porta 8001)
para que abram em qualquer player (VLC, Kodi, mpv, ...).

Usa apenas a biblioteca padrão do Python (>= 3.7), por isso também corre
na própria box Enigma2.

O que faz a cada stream:
  * lê o TS da box e espera pela PAT/PMT do serviço pedido;
  * observa durante um curto período quais os PIDs que existem mesmo;
  * gera uma PAT e uma PMT NOVAS, só com o serviço pedido, com
    - apenas os PIDs de vídeo/áudio/legendas/teletexto que estão presentes,
    - sem descritores CA (ECM), sem AIT/DSM-CC (HbbTV),
    - PCR_PID corrigido se o original não transportar PCR;
  * começa o envio com PAT+PMT e repete-as a cada ~100 ms;
  * descarta PIDs que não pertencem ao serviço (ECM, EMM, CAT, ...);
  * se nunca chegar PMT, deduz as streams a partir dos cabeçalhos PES;
  * se um PID da PMT original só aparecer mais tarde, é acrescentado
    (nova versão da PMT).

Uso:
  python3 e2proxy.py serve --box 192.168.1.10
      -> playlist: http://<este_pc>:8090/playlist.m3u
      -> canal:    http://<este_pc>:8090/stream/1:0:19:XXXX:...

  python3 e2proxy.py fix entrada.ts saida.ts [--sid 0x1B]
      -> corrige um ficheiro gravado (útil para testes)
"""

import argparse
import base64
import json
import logging
import re
import socket
import sys
import time
import urllib.parse
import urllib.request
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

log = logging.getLogger("e2proxy")

TS = 188
SYNC = 0x47
NULL_PID = 0x1FFF

# ----------------------------------------------------------------------------
# CRC32 MPEG-2
# ----------------------------------------------------------------------------

def _make_crc_table():
    table = []
    for i in range(256):
        c = i << 24
        for _ in range(8):
            c = ((c << 1) ^ 0x04C11DB7) if c & 0x80000000 else (c << 1)
        table.append(c & 0xFFFFFFFF)
    return table


_CRC = _make_crc_table()


def crc32_mpeg(data):
    crc = 0xFFFFFFFF
    for b in data:
        crc = ((crc << 8) & 0xFFFFFFFF) ^ _CRC[((crc >> 24) ^ b) & 0xFF]
    return crc


# ----------------------------------------------------------------------------
# Tipos de stream
# ----------------------------------------------------------------------------

VIDEO_TYPES = {0x01, 0x02, 0x10, 0x1B, 0x24, 0x33, 0x42, 0xEA}
AUDIO_TYPES = {0x03, 0x04, 0x0F, 0x11, 0x1C, 0x81, 0x87}
DATA_TYPES = {0x05, 0x0A, 0x0B, 0x0C, 0x0D}   # AIT, DSM-CC (HbbTV, OAD...)

DESC_CA = 0x09
DESC_AC3 = 0x6A
DESC_EAC3 = 0x7A
DESC_AAC = 0x7C
DESC_EXT = 0x7F
DESC_TELETEXT = 0x56
DESC_SUBTITLE = 0x59

TYPE_NAMES = {
    0x01: "MPEG-1 vídeo", 0x02: "MPEG-2 vídeo", 0x03: "MPEG-1 áudio",
    0x04: "MPEG-2 áudio", 0x0F: "AAC", 0x11: "AAC-LATM", 0x1B: "H.264",
    0x24: "HEVC", 0x81: "AC-3 (ATSC)", 0x87: "E-AC-3 (ATSC)",
    0x05: "dados privados (AIT?)", 0x0B: "DSM-CC", 0x0C: "DSM-CC",
    0x0D: "DSM-CC",
}


def iter_descriptors(buf):
    i = 0
    while i + 2 <= len(buf):
        tag, ln = buf[i], buf[i + 1]
        if i + 2 + ln > len(buf):
            break
        yield tag, buf[i:i + 2 + ln]
        i += 2 + ln


def strip_ca(desc):
    return b"".join(d for tag, d in iter_descriptors(desc) if tag != DESC_CA)


class ES:
    __slots__ = ("stype", "pid", "desc")

    def __init__(self, stype, pid, desc=b""):
        self.stype, self.pid, self.desc = stype, pid, desc

    def tags(self):
        return {t for t, _ in iter_descriptors(self.desc)}

    def kind(self):
        t = self.tags()
        if self.stype in VIDEO_TYPES:
            return "video"
        if self.stype in AUDIO_TYPES or t & {DESC_AC3, DESC_EAC3, DESC_AAC, DESC_EXT}:
            return "audio"
        if DESC_SUBTITLE in t:
            return "legendas"
        if DESC_TELETEXT in t:
            return "teletexto"
        if self.stype in DATA_TYPES:
            return "dados"
        return "outro"

    def describe(self):
        name = TYPE_NAMES.get(self.stype, "tipo 0x%02X" % self.stype)
        t = self.tags()
        if self.stype == 0x06:
            if DESC_AC3 in t:
                name = "AC-3"
            elif DESC_EAC3 in t:
                name = "E-AC-3"
            elif DESC_AAC in t:
                name = "AAC"
            elif DESC_SUBTITLE in t:
                name = "legendas DVB"
            elif DESC_TELETEXT in t:
                name = "teletexto"
        return "PID 0x%04X (%d) %s" % (self.pid, self.pid, name)


# ----------------------------------------------------------------------------
# Secções PSI
# ----------------------------------------------------------------------------

class SectionAssembler:
    """Junta secções PSI que podem estar repartidas por vários pacotes."""

    def __init__(self):
        self.buf = None

    def feed(self, pkt, payload_off):
        if payload_off >= TS:
            return []
        payload = pkt[payload_off:]
        out = []
        if pkt[1] & 0x40:  # payload_unit_start_indicator
            ptr = payload[0]
            if self.buf is not None:
                self.buf += payload[1:1 + ptr]
                out += self._drain()
            self.buf = bytearray(payload[1 + ptr:])
        else:
            if self.buf is None:
                return []
            self.buf += payload
        out += self._drain()
        return out

    def _drain(self):
        out = []
        while self.buf is not None and len(self.buf) >= 3:
            if self.buf[0] == 0xFF:
                self.buf = None
                break
            ln = (((self.buf[1] & 0x0F) << 8) | self.buf[2]) + 3
            if len(self.buf) < ln:
                break
            sec = bytes(self.buf[:ln])
            self.buf = self.buf[ln:]
            if ln >= 12 and crc32_mpeg(sec) == 0:
                out.append(sec)
        return out


def parse_pat(sec):
    if sec[0] != 0x00:
        return None
    tsid = (sec[3] << 8) | sec[4]
    progs = {}
    end = len(sec) - 4
    for i in range(8, end - 3, 4):
        prog = (sec[i] << 8) | sec[i + 1]
        pid = ((sec[i + 2] & 0x1F) << 8) | sec[i + 3]
        if prog != 0:
            progs[prog] = pid
    return tsid, progs


def parse_pmt(sec):
    if sec[0] != 0x02:
        return None
    prog = (sec[3] << 8) | sec[4]
    version = (sec[5] >> 1) & 0x1F
    pcr_pid = ((sec[8] & 0x1F) << 8) | sec[9]
    pil = ((sec[10] & 0x0F) << 8) | sec[11]
    prog_desc = sec[12:12 + pil]
    i = 12 + pil
    end = len(sec) - 4
    es = []
    while i + 5 <= end:
        stype = sec[i]
        pid = ((sec[i + 1] & 0x1F) << 8) | sec[i + 2]
        eil = ((sec[i + 3] & 0x0F) << 8) | sec[i + 4]
        es.append(ES(stype, pid, bytes(sec[i + 5:i + 5 + eil])))
        i += 5 + eil
    return {"prog": prog, "version": version, "pcr_pid": pcr_pid,
            "prog_desc": bytes(prog_desc), "es": es, "raw": sec}


def make_section(table_id, body):
    length = len(body) + 4
    sec = bytearray([table_id, 0xB0 | ((length >> 8) & 0x0F), length & 0xFF])
    sec += body
    sec += crc32_mpeg(sec).to_bytes(4, "big")
    return bytes(sec)


def build_pat(tsid, prog, pmt_pid, version):
    body = bytearray(tsid.to_bytes(2, "big"))
    body += bytes([0xC1 | (version << 1), 0x00, 0x00])
    body += prog.to_bytes(2, "big")
    body += (0xE000 | pmt_pid).to_bytes(2, "big")
    return make_section(0x00, body)


def build_pmt(prog, version, pcr_pid, prog_desc, es_list):
    body = bytearray(prog.to_bytes(2, "big"))
    body += bytes([0xC1 | (version << 1), 0x00, 0x00])
    body += (0xE000 | pcr_pid).to_bytes(2, "big")
    body += (0xF000 | len(prog_desc)).to_bytes(2, "big") + prog_desc
    for es in es_list:
        body.append(es.stype)
        body += (0xE000 | es.pid).to_bytes(2, "big")
        body += (0xF000 | len(es.desc)).to_bytes(2, "big") + es.desc
    return make_section(0x02, body)


# ----------------------------------------------------------------------------
# Dedução de streams a partir dos cabeçalhos PES (quando não há PMT)
# ----------------------------------------------------------------------------

def guess_es_from_pes(pid, payload):
    """payload = início de um PES (começa por 00 00 01). Devolve ES ou None."""
    if len(payload) < 9 or payload[0:3] != b"\x00\x00\x01":
        return None
    sid = payload[3]
    data = payload[9 + payload[8]:]
    if 0xE0 <= sid <= 0xEF:
        k = data.find(b"\x00\x00\x01")
        b = data[k + 3] if 0 <= k < len(data) - 3 else None
        if b in (0xB3, 0x00, 0xB5, 0xB8):
            return ES(0x02, pid)
        if b is not None and (b >> 1) & 0x3F in (32, 33, 34, 35, 39):
            return ES(0x24, pid)
        return ES(0x1B, pid)
    if 0xC0 <= sid <= 0xDF:
        if len(data) >= 2 and data[0] == 0xFF and (data[1] & 0xF0) == 0xF0 \
                and (data[1] & 0x06) == 0:
            return ES(0x0F, pid)          # AAC ADTS
        return ES(0x03, pid)              # MPEG áudio
    if sid == 0xBD and len(data) >= 6:
        if data[0] == 0x0B and data[1] == 0x77:
            bsid = data[5] >> 3
            if bsid > 10:
                return ES(0x06, pid, bytes([DESC_EAC3, 1, 0x00]))
            return ES(0x06, pid, bytes([DESC_AC3, 1, 0x00]))
        if data[0] == 0x20 and data[1] == 0x00:
            return ES(0x06, pid, bytes([DESC_SUBTITLE, 8]) + b"und" +
                      bytes([0x10, 0, 1, 0, 1]))
        if 0x10 <= data[0] <= 0x1F:
            return ES(0x06, pid, bytes([DESC_TELETEXT, 5]) + b"und" +
                      bytes([0x09, 0x00]))
    return None


# ----------------------------------------------------------------------------
# O corretor
# ----------------------------------------------------------------------------

class PidInfo:
    __slots__ = ("count", "has_pcr", "pusi_seen", "guess", "scrambled", "clear")

    def __init__(self):
        self.count = 0
        self.scrambled = 0      # pacotes ainda encriptados (TSC != 0)
        self.clear = 0
        self.has_pcr = False
        self.pusi_seen = False
        self.guess = None


class TSFixer:
    def __init__(self, service_id=None, probe_secs=1.0, pmt_timeout=4.0,
                 max_probe_packets=300000, keep_data=False, keep_si=False,
                 add_unlisted=False, descramble_wait=8.0, repeat_secs=0.1, repeat_packets=2000,
                 name="stream"):
        self.service_id = service_id
        self.probe_secs = probe_secs
        self.pmt_timeout = pmt_timeout
        self.max_probe_packets = max_probe_packets
        self.keep_data = keep_data
        self.keep_si = keep_si
        self.add_unlisted = add_unlisted
        self.descramble_wait = descramble_wait
        self.scr_dropped = 0
        self.scr_last_log = None
        self.repeat_secs = repeat_secs
        self.repeat_packets = repeat_packets
        self.name = name

        self.rest = b""
        self.probing = True
        self.probe_buf = []
        self.npackets = 0

        self.pids = {}
        self.asm = {}
        self.tsid = 1
        self.orig_pmt_pid = None
        self.orig_pmt = None

        self.first_pcr = None
        self.last_pcr = None     # em segundos, contínuo (sem wrap)
        self._pcr_raw = None

        # estado de saída
        self.prog = 1
        self.out_pmt_pid = 0x1000
        self.out_es = []
        self.out_pcr_pid = NULL_PID
        self.out_prog_desc = b""
        self.allowed = set()
        self.started = set()     # PIDs ES que já tiveram PUSI na saída
        self.pat_ver = 0
        self.pmt_ver = 0
        self.cc_pat = 0
        self.cc_pmt = 0
        self.pat_pkts = []
        self.pmt_pkts = []
        self.last_psi_time = None
        self.since_psi = 0

    # -------------------------------------------------------------- tempo
    def _update_pcr(self, pkt):
        if (pkt[3] & 0x20) and pkt[4] >= 7 and (pkt[5] & 0x10):
            base = (pkt[6] << 25) | (pkt[7] << 17) | (pkt[8] << 9) | \
                   (pkt[9] << 1) | (pkt[10] >> 7)
            if self._pcr_raw is None:
                self.first_pcr = 0.0
                self.last_pcr = 0.0
            else:
                diff = (base - self._pcr_raw) % (1 << 33)
                if diff < 90000 * 5:          # ignora saltos/descontinuidades
                    self.last_pcr += diff / 90000.0
            self._pcr_raw = base
            return True
        return False

    def elapsed(self):
        if self.last_pcr is None:
            return 0.0
        return self.last_pcr - self.first_pcr

    # -------------------------------------------------------------- entrada
    def feed(self, data):
        buf = self.rest + data
        out = bytearray()
        i = 0
        n = len(buf)
        while i + TS <= n:
            if buf[i] != SYNC:
                j = i + 1
                while j + TS < n and not (buf[j] == SYNC and buf[j + TS] == SYNC):
                    j += 1
                if j + TS >= n:
                    i = j
                    break
                log.debug("[%s] ressincronização (%d bytes saltados)", self.name, j - i)
                i = j
                continue
            pkt = buf[i:i + TS]
            i += TS
            self._packet(pkt, out)
        self.rest = buf[i:]
        return bytes(out)

    def flush(self):
        out = bytearray()
        if self.probing:
            self._finish_probe(out)
        return bytes(out)

    def _packet(self, pkt, out):
        self.npackets += 1
        pid = ((pkt[1] & 0x1F) << 8) | pkt[2]
        if pid == NULL_PID:
            return
        afc = (pkt[3] >> 4) & 3
        payload_off = 4
        if afc & 2:
            payload_off += 1 + pkt[4]
        has_payload = bool(afc & 1) and payload_off < TS

        info = self.pids.get(pid)
        if info is None:
            info = self.pids[pid] = PidInfo()
        tsc = pkt[3] & 0xC0
        if has_payload:
            info.count += 1
            if tsc:
                info.scrambled += 1
            else:
                info.clear += 1
        if afc & 2 and self._update_pcr(pkt):
            info.has_pcr = True
        pusi = bool(pkt[1] & 0x40)
        if pusi and has_payload and not tsc:
            info.pusi_seen = True
            if info.guess is None and pid not in (0, self.orig_pmt_pid):
                info.guess = guess_es_from_pes(pid, pkt[payload_off:])

        # PSI
        if pid == 0 and has_payload:
            for sec in self._asm(pid).feed(pkt, payload_off):
                self._on_pat(sec)
            if not self.probing:
                return
        elif pid == self.orig_pmt_pid and has_payload:
            for sec in self._asm(pid).feed(pkt, payload_off):
                self._on_pmt(sec, out)
            if not self.probing:
                return

        if self.probing:
            # pacotes encriptados não servem ao player: só guardamos o PCR
            if not tsc or (afc & 2):
                self.probe_buf.append(pkt)
            if self._probe_done():
                self._finish_probe(out)
            return

        # fase normal
        if pid not in self.allowed:
            self._maybe_late_es(pid, info, out)
            if pid not in self.allowed:
                return
        self._emit(pid, pkt, pusi, out)

    def _asm(self, pid):
        a = self.asm.get(pid)
        if a is None:
            a = self.asm[pid] = SectionAssembler()
        return a

    def _on_pat(self, sec):
        r = parse_pat(sec)
        if not r:
            return
        tsid, progs = r
        self.tsid = tsid
        if not progs:
            return
        if self.service_id is not None and self.service_id in progs:
            prog = self.service_id
        elif self.service_id is not None and self.orig_pmt_pid is None:
            prog = next(iter(progs))
            log.warning("[%s] serviço 0x%X não está na PAT %s; uso 0x%X",
                        self.name, self.service_id,
                        ["0x%X" % p for p in progs], prog)
            self.service_id = prog
        else:
            prog = self.service_id if self.service_id in progs else next(iter(progs))
        pmt_pid = progs[prog]
        if pmt_pid != self.orig_pmt_pid:
            if self.orig_pmt_pid is not None:
                log.info("[%s] PMT mudou de PID 0x%X -> 0x%X",
                         self.name, self.orig_pmt_pid, pmt_pid)
            self.orig_pmt_pid = pmt_pid
            self.asm.pop(pmt_pid, None)
        if self.service_id is None:
            self.service_id = prog

    def _on_pmt(self, sec, out):
        pmt = parse_pmt(sec)
        if not pmt:
            return
        if self.service_id is not None and pmt["prog"] != self.service_id:
            return
        changed = self.orig_pmt is None or self.orig_pmt["raw"] != pmt["raw"]
        if not changed:
            return
        first = self.orig_pmt is None
        self.orig_pmt = pmt
        if first:
            log.info("[%s] PMT original (programa 0x%X, PCR 0x%X):",
                     self.name, pmt["prog"], pmt["pcr_pid"])
            for es in pmt["es"]:
                log.info("[%s]    %s%s", self.name, es.describe(),
                         "  [CA]" if DESC_CA in es.tags() else "")
            if DESC_CA in {t for t, _ in iter_descriptors(pmt["prog_desc"])}:
                log.info("[%s]    (descritor CA ao nível do programa)", self.name)
        elif not self.probing:
            log.info("[%s] PMT original mudou (versão %d) - a regenerar",
                     self.name, pmt["version"])
            self._build_output(out, reason="PMT original mudou")

    # -------------------------------------------------------------- sondagem
    def _probe_done(self):
        t = self.elapsed()
        if self.npackets >= self.max_probe_packets:
            return True
        if self.orig_pmt is None:
            return t >= self.pmt_timeout
        wanted = [es for es in self.orig_pmt["es"] if self._wanted_kind(es)]
        av = [es for es in wanted if es.kind() in ("video", "audio")]
        all_av_seen = av and all(
            self.pids.get(es.pid) and self.pids[es.pid].pusi_seen for es in av)
        if all_av_seen and t >= 0.2:
            return True
        still_scrambled = any(
            self.pids.get(es.pid) and self.pids[es.pid].scrambled for es in av)
        if still_scrambled:
            return t >= max(self.probe_secs, self.descramble_wait)
        return t >= self.probe_secs

    def _wanted_kind(self, es):
        return self.keep_data or es.kind() != "dados"

    def _select_es(self):
        """Escolhe as ES a anunciar na PMT nova."""
        chosen, dropped = [], []
        if self.orig_pmt is not None:
            listed = set()
            for es in self.orig_pmt["es"]:
                listed.add(es.pid)
                info = self.pids.get(es.pid)
                present = info is not None and info.count > 0
                if not self._wanted_kind(es):
                    dropped.append((es, "dados/HbbTV"))
                elif not present:
                    dropped.append((es, "não existe no stream"))
                else:
                    chosen.append(ES(es.stype, es.pid, strip_ca(es.desc)))
            if self.add_unlisted:
                for pid, info in sorted(self.pids.items()):
                    if pid not in listed and info.guess is not None:
                        chosen.append(info.guess)
                        log.info("[%s] + %s (não estava na PMT, deduzido)",
                                 self.name, info.guess.describe())
            return chosen, dropped
        # sem PMT: deduz tudo
        for pid, info in sorted(self.pids.items()):
            if info.guess is not None:
                chosen.append(info.guess)
        return chosen, dropped

    def _choose_pcr(self, es_list):
        orig = self.orig_pmt["pcr_pid"] if self.orig_pmt else None
        if orig is not None and self.pids.get(orig) and self.pids[orig].has_pcr:
            return orig
        cands = [p for p, i in self.pids.items() if i.has_pcr]
        es_pids = [e.pid for e in es_list]
        for es in es_list:
            if es.kind() == "video" and es.pid in cands:
                return es.pid
        for p in es_pids:
            if p in cands:
                return p
        if cands:
            return cands[0]
        return NULL_PID

    def _finish_probe(self, out):
        self.probing = False
        if self.orig_pmt is None:
            log.warning("[%s] nenhuma PMT recebida em %.1fs - a deduzir streams "
                        "pelos cabeçalhos PES", self.name, self.elapsed())
        self._build_output(None, reason="início")
        for es in self.out_es:
            i = self.pids.get(es.pid)
            if i and i.scrambled and not i.clear:
                log.error("[%s] %s chega ENCRIPTADO (%d pacotes, 0 em claro). "
                          "A box não está a desencriptar o stream: verifica o "
                          "softcam/CI e a opção de desencriptar streams no Enigma2.",
                          self.name, es.describe(), i.scrambled)
            elif i and i.scrambled:
                log.info("[%s] %s: %d pacotes encriptados no arranque descartados",
                         self.name, es.describe(), i.scrambled)
        self._emit_psi(out)
        buf, self.probe_buf = self.probe_buf, []
        for pkt in buf:
            pid = ((pkt[1] & 0x1F) << 8) | pkt[2]
            if pid in self.allowed:
                self._emit(pid, pkt, bool(pkt[1] & 0x40), out)

    def _build_output(self, out, reason):
        es_list, dropped = self._select_es()
        if self.orig_pmt is not None:
            self.prog = self.orig_pmt["prog"]
            self.out_prog_desc = strip_ca(self.orig_pmt["prog_desc"])
        elif self.service_id:
            self.prog = self.service_id
        es_pids = {e.pid for e in es_list}
        pmt_pid = self.orig_pmt_pid if self.orig_pmt_pid else 0x1000
        while pmt_pid in es_pids or pmt_pid in (0, NULL_PID):
            pmt_pid += 1
        self.out_pmt_pid = pmt_pid
        self.out_es = es_list
        self.out_pcr_pid = self._choose_pcr(es_list)

        allowed = set(es_pids)
        if self.out_pcr_pid != NULL_PID:
            allowed.add(self.out_pcr_pid)
        if self.keep_si:
            allowed |= {0x10, 0x11, 0x12, 0x14}
        self.allowed = allowed

        if out is not None:   # regeneração em andamento
            self.pmt_ver = (self.pmt_ver + 1) & 0x1F
        self._make_psi_packets()

        log.info("[%s] PMT nova (%s): programa 0x%X, PMT PID 0x%X, PCR 0x%X",
                 self.name, reason, self.prog, self.out_pmt_pid, self.out_pcr_pid)
        for es in es_list:
            log.info("[%s]    + %s", self.name, es.describe())
        for es, why in dropped:
            log.info("[%s]    - %s  (%s)", self.name, es.describe(), why)
        if not es_list:
            log.error("[%s] nenhuma stream de vídeo/áudio encontrada!", self.name)
        if out is not None:
            self._emit_psi(out)

    def _maybe_late_es(self, pid, info, out):
        if self.orig_pmt is None or not info.pusi_seen:
            return
        for es in self.orig_pmt["es"]:
            if es.pid == pid and self._wanted_kind(es):
                log.info("[%s] PID 0x%X apareceu mais tarde - a acrescentar",
                         self.name, pid)
                self._build_output(out, reason="PID novo")
                return

    # -------------------------------------------------------------- saída
    def _make_psi_packets(self):
        pat = build_pat(self.tsid, self.prog, self.out_pmt_pid, self.pat_ver)
        pmt = build_pmt(self.prog, self.pmt_ver, self.out_pcr_pid,
                        self.out_prog_desc, self.out_es)
        self.pat_sec, self.pmt_sec = pat, pmt

    def _packetize(self, pid, section, cc):
        pkts = []
        data = b"\x00" + section
        first = True
        while data:
            chunk, data = data[:184], data[184:]
            hdr = bytes([SYNC, (0x40 if first else 0) | ((pid >> 8) & 0x1F),
                         pid & 0xFF, 0x10 | cc])
            cc = (cc + 1) & 0x0F
            first = False
            pkts.append(hdr + chunk + b"\xFF" * (184 - len(chunk)))
        return pkts, cc

    def _emit_psi(self, out):
        pkts, self.cc_pat = self._packetize(0, self.pat_sec, self.cc_pat)
        for p in pkts:
            out += p
        pkts, self.cc_pmt = self._packetize(self.out_pmt_pid, self.pmt_sec, self.cc_pmt)
        for p in pkts:
            out += p
        self.last_psi_time = self.elapsed()
        self.since_psi = 0

    def _is_keyframe_start(self, pid, pkt):
        """True se este PES de vídeo começa num ponto de acesso aleatório."""
        if (pkt[3] & 0x20) and pkt[4] > 0 and (pkt[5] & 0x40):
            return True  # random_access_indicator
        off = 4 + (1 + pkt[4] if pkt[3] & 0x20 else 0)
        pl = pkt[off:]
        if len(pl) < 9 or pl[0:3] != b"\x00\x00\x01":
            return False
        data = pl[9 + pl[8]:]
        stype = next((e.stype for e in self.out_es if e.pid == pid), 0)
        k = data.find(b"\x00\x00\x01")
        while 0 <= k < len(data) - 3:
            b = data[k + 3]
            if stype in (0x01, 0x02) and b == 0xB3:
                return True
            if stype == 0x1B and (b & 0x1F) in (5, 7):
                return True
            if stype == 0x24 and ((b >> 1) & 0x3F) in (16, 17, 18, 19, 20, 21, 32, 33):
                return True
            k = data.find(b"\x00\x00\x01", k + 3)
        return False

    def _emit(self, pid, pkt, pusi, out):
        if pkt[3] & 0xC0:
            # pacote ainda encriptado: descarta (mantém só o PCR, se houver)
            self.scr_dropped += 1
            t = self.elapsed()
            if self.scr_last_log is None or t - self.scr_last_log >= 5:
                if self.scr_last_log is not None:
                    log.warning("[%s] %d pacotes encriptados descartados nos "
                                "últimos segundos (falha do softcam/CW?)",
                                self.name, self.scr_dropped)
                    self.scr_dropped = 0
                self.scr_last_log = t
            if pid == self.out_pcr_pid and (pkt[3] & 0x20) and pkt[4] >= 7 \
                    and (pkt[5] & 0x10):
                pkt = self._strip_payload(pkt)
                pusi = False
                self.since_psi += 1
                out += pkt
            return
        if pid not in self.started:
            # não envia PES incompletos no arranque (exceto PID só de PCR);
            # o vídeo só começa num keyframe (com limite, caso não detete)
            is_video = any(e.pid == pid and e.kind() == "video" for e in self.out_es)
            if is_video and pusi:
                self.skipped = getattr(self, "skipped", 0) + 1
                if not self._is_keyframe_start(pid, pkt) and self.skipped < 150:
                    pusi = False   # trata como "ainda não começou"
            if pusi:
                self.started.add(pid)
            elif pid in {e.pid for e in self.out_es}:
                if pid == self.out_pcr_pid and (pkt[3] & 0x20):
                    # mantém o PCR mas sem payload parcial
                    pkt = self._strip_payload(pkt)
                else:
                    return
        self.since_psi += 1
        if (self.since_psi >= self.repeat_packets or
                (self.last_psi_time is not None and
                 self.elapsed() - self.last_psi_time >= self.repeat_secs)):
            self._emit_psi(out)
        out += pkt

    @staticmethod
    def _strip_payload(pkt):
        """Transforma o pacote num pacote só com adaptation field (PCR)."""
        af_len = pkt[4]
        af = bytearray(pkt[5:5 + af_len])
        new_len = 183
        af += b"\xFF" * (new_len - len(af))
        # sem payload: TSC=00 e o CC não incrementa (usamos CC-1)
        b3 = 0x20 | ((pkt[3] - 1) & 0x0F)
        return bytes([pkt[0], pkt[1] & ~0x40 & 0xFF, pkt[2], b3, new_len]) + bytes(af)


# ----------------------------------------------------------------------------
# Servidor HTTP
# ----------------------------------------------------------------------------

def service_id_from_ref(ref):
    parts = ref.split(":")
    try:
        return int(parts[3], 16) if len(parts) > 3 else None
    except ValueError:
        return None


class Handler(BaseHTTPRequestHandler):
    server_version = "e2proxy/1.0"
    cfg = None   # argparse.Namespace

    def log_message(self, fmt, *args):
        log.debug("%s - %s", self.address_string(), fmt % args)

    def _auth_header(self):
        c = self.cfg
        if c.user:
            tok = base64.b64encode(("%s:%s" % (c.user, c.password or "")).encode())
            return {"Authorization": "Basic " + tok.decode()}
        return {}

    def do_GET(self):
        path = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(path.query)
        p = urllib.parse.unquote(path.path)
        try:
            if p in ("/", "/index.html"):
                return self._index()
            if p in ("/playlist.m3u", "/playlist.m3u8"):
                return self._playlist()
            if p.startswith("/stream/"):
                ref = p[len("/stream/"):]
                url = "http://%s:%d/%s" % (self.cfg.box, self.cfg.stream_port,
                                           urllib.parse.quote(ref, safe=":"))
                return self._stream(url, service_id_from_ref(ref), ref)
            if p == "/url" and "url" in qs:
                url = qs["url"][0]
                sid = qs.get("sid", [None])[0]
                sid = int(sid, 0) if sid else service_id_from_ref(
                    urllib.parse.urlparse(url).path.lstrip("/"))
                return self._stream(url, sid, url)
            if ":" in p.lstrip("/"):   # http://proxy:8090/1:0:19:...
                ref = p.lstrip("/")
                url = "http://%s:%d/%s" % (self.cfg.box, self.cfg.stream_port,
                                           urllib.parse.quote(ref, safe=":"))
                return self._stream(url, service_id_from_ref(ref), ref)
            self.send_error(404)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _index(self):
        host = self.headers.get("Host", "localhost")
        body = ("e2proxy\n\nPlaylist: http://%s/playlist.m3u\n"
                "Canal:    http://%s/stream/<referência enigma2>\n"
                "URL:      http://%s/url?url=<url do stream>[&sid=0x...]\n"
                % (host, host, host)).encode()
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _web_get(self, path, timeout=15):
        c = self.cfg
        url = "http://%s:%d%s" % (c.box, c.web_port, path)
        req = urllib.request.Request(url, headers=self._auth_header())
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read()

    def _bouquets_json(self):
        data = json.loads(self._web_get("/api/getallservices").decode("utf-8", "replace"))
        out = []
        for b in data.get("services", []):
            out.append((b.get("servicename", ""),
                        [(s.get("servicereference", ""), s.get("servicename", ""))
                         for s in b.get("subservices", [])]))
        return out

    def _xml_services(self, sref=None):
        import re
        import xml.etree.ElementTree as ET
        path = "/web/getservices"
        if sref:
            path += "?sRef=" + urllib.parse.quote(sref, safe="")
        raw = self._web_get(path, timeout=30).decode("utf-8", "replace")
        # remove caracteres de controlo que partem o XML (nomes de canais DVB)
        raw = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x80-\x9f]", "", raw)
        root = ET.fromstring(raw)
        res = []
        for s in root.iter("e2service"):
            res.append(((s.findtext("e2servicereference") or "").strip(),
                        (s.findtext("e2servicename") or "").strip()))
        return res

    def _bouquets_xml(self):
        roots = ['1:7:1:0:0:0:0:0:0:0:FROM BOUQUET "bouquets.tv" ORDER BY bouquet']
        if self.cfg.radio:
            roots.append('1:7:2:0:0:0:0:0:0:0:FROM BOUQUET "bouquets.radio" ORDER BY bouquet')
        out = []
        for root in roots:
            for bref, bname in self._xml_services(root):
                try:
                    out.append((bname, self._xml_services(bref)))
                except Exception as e:
                    log.warning("bouquet '%s' falhou: %s", bname, e)
        return out

    def _playlist(self):
        bouquets = None
        errors = []
        for name, fn in (("/api/getallservices", self._bouquets_json),
                         ("/web/getservices (XML)", self._bouquets_xml)):
            try:
                bouquets = fn()
                if bouquets:
                    log.info("playlist obtida via %s (%d bouquets)", name, len(bouquets))
                    break
                errors.append("%s: vazio" % name)
            except Exception as e:
                log.warning("OpenWebif %s falhou: %s", name, e)
                errors.append("%s: %s" % (name, e))
        if not bouquets:
            log.error("não foi possível obter os canais: %s", "; ".join(errors))
            self.send_error(502, "OpenWebif: " + "; ".join(errors))
            return
        host = self.headers.get("Host", "localhost")
        lines = ["#EXTM3U"]
        for group, services in bouquets:
            for ref, sname in services:
                s = {"servicereference": ref, "servicename": sname}
                parts = ref.split(":")
                # ignora marcadores / separadores
                if len(parts) < 10 or parts[1] in ("64", "832", "320"):
                    continue
                name = re.sub(r"[\x00-\x1f\x80-\x9f]", "", s.get("servicename") or ref)
                name = name.replace(",", " ").strip()
                lines.append('#EXTINF:-1 group-title="%s",%s'
                             % (group.replace('"', "'"), name))
                lines.append("http://%s/stream/%s"
                             % (host, urllib.parse.quote(ref.rstrip(":") + ":", safe=":")))
        body = ("\n".join(lines) + "\n").encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "audio/x-mpegurl; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _stream(self, url, sid, name):
        c = self.cfg
        short = name if len(name) < 40 else name[:37] + "..."
        log.info("[%s] cliente %s -> %s (serviço %s)", short,
                 self.client_address[0], url,
                 "0x%X" % sid if sid is not None else "?")
        try:
            req = urllib.request.Request(url, headers=self._auth_header())
            up = urllib.request.urlopen(req, timeout=c.timeout)
        except Exception as e:
            log.error("[%s] erro a ligar à box: %s", short, e)
            self.send_error(502, "Box: %s" % e)
            return
        fixer = TSFixer(service_id=sid, probe_secs=c.probe, keep_data=c.keep_data,
                        keep_si=c.keep_si, add_unlisted=c.add_unlisted,
                        descramble_wait=c.descramble_wait, name=short)
        self.send_response(200)
        self.send_header("Content-Type", "video/mp2t")
        self.send_header("Cache-Control", "no-cache")
        self.send_header("Connection", "close")
        self.end_headers()
        sent = 0
        t0 = time.time()
        try:
            while True:
                chunk = up.read1(65536) if hasattr(up, "read1") else up.read(65536)
                if not chunk:
                    log.info("[%s] a box fechou o stream", short)
                    break
                data = fixer.feed(chunk)
                if data:
                    self.wfile.write(data)
                    sent += len(data)
        except (BrokenPipeError, ConnectionResetError, socket.timeout) as e:
            log.info("[%s] cliente desligou (%s)", short, type(e).__name__)
        finally:
            up.close()
            log.info("[%s] terminado: %.1f MB em %.0fs", short, sent / 1e6,
                     time.time() - t0)


def cmd_serve(a):
    Handler.cfg = a
    srv = ThreadingHTTPServer((a.listen, a.port), Handler)
    srv.daemon_threads = True
    log.info("e2proxy à escuta em http://%s:%d  (box %s, stream %d, web %d)",
             a.listen, a.port, a.box, a.stream_port, a.web_port)
    log.info("playlist: http://<este_ip>:%d/playlist.m3u", a.port)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


def cmd_fix(a):
    sid = int(a.sid, 0) if a.sid else None
    fixer = TSFixer(service_id=sid, probe_secs=a.probe, keep_data=a.keep_data,
                    keep_si=a.keep_si, add_unlisted=a.add_unlisted,
                    descramble_wait=a.descramble_wait, name="ficheiro")
    with open(a.input, "rb") as fi, open(a.output, "wb") as fo:
        while True:
            chunk = fi.read(188 * 2048)
            if not chunk:
                break
            fo.write(fixer.feed(chunk))
        fo.write(fixer.flush())
    log.info("escrito %s", a.output)


def main():
    ap = argparse.ArgumentParser(description="Corrige PAT/PMT de streams Enigma2")
    ap.add_argument("-v", "--verbose", action="store_true")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--probe", type=float, default=1.0,
                       help="segundos máx. a observar o stream antes de gerar a PMT")
        p.add_argument("--keep-data", action="store_true",
                       help="manter PIDs de dados (AIT/HbbTV, DSM-CC)")
        p.add_argument("--keep-si", action="store_true",
                       help="deixar passar NIT/SDT/EIT/TDT")
        p.add_argument("--descramble-wait", type=float, default=8.0,
                       help="segundos máx. à espera que o stream chegue desencriptado")
        p.add_argument("--add-unlisted", action="store_true",
                       help="acrescentar PIDs de áudio/vídeo que não estão na PMT")

    s = sub.add_parser("serve", help="arranca o proxy HTTP")
    s.add_argument("--box", required=True, help="IP/host da box Enigma2")
    s.add_argument("--stream-port", type=int, default=8001)
    s.add_argument("--web-port", type=int, default=80, help="porta do OpenWebif")
    s.add_argument("--user", help="utilizador da box (se tiver autenticação)")
    s.add_argument("--password")
    s.add_argument("--listen", default="0.0.0.0")
    s.add_argument("--port", type=int, default=8090)
    s.add_argument("--timeout", type=float, default=15)
    s.add_argument("--radio", action="store_true",
                   help="incluir também os bouquets de rádio na playlist")
    common(s)

    f = sub.add_parser("fix", help="corrige um ficheiro .ts")
    f.add_argument("input")
    f.add_argument("output")
    f.add_argument("--sid", help="service id (ex.: 0x1B)")
    common(f)

    a = ap.parse_args()
    logging.basicConfig(level=logging.DEBUG if a.verbose else logging.INFO,
                        format="%(asctime)s %(levelname)s %(message)s",
                        datefmt="%H:%M:%S")
    {"serve": cmd_serve, "fix": cmd_fix}[a.cmd](a)


if __name__ == "__main__":
    main()
