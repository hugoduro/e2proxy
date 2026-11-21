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
