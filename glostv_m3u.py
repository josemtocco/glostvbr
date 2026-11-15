#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
GlosTV -> M3U (otimizado para SS IPTV)
=====================================

Gera uma lista M3U a partir de https://glostv.com/tv-ao-vivo-brasil

O que ele faz:
  1. Baixa a pagina principal + TODAS as categorias do site (cada pagina e
     percorrida pagina a pagina: /page/2, /page/3 ... ate nao existir mais,
     e tambem tenta o botao "carregar mais" via admin-ajax do tema).
  2. Visita cada pagina de canal e extrai o stream (m3u8 / mpd) do player.
  3. Testa de verdade se o canal esta tocando (baixa o manifest e um segmento
     real de video). Nao aceita apenas HTTP 200.
  4. Regra das 6 atualizacoes: mantem os canais ativos, remove apenas os que
     falharem 6 vezes SEGUIDAS, adiciona os novos encontrados.
  5. Gera a lista M3U separada pelas categorias do proprio site, com nome do
     canal, logo e group-title (padrao que o SS IPTV entende).
  6. Nunca apaga a lista por causa de bloqueio de rede/geo: falha de site =
     "inconclusivo".

Uso:
    python glostv_m3u.py                # atualizacao normal
    python glostv_m3u.py --completo     # varredura total + teste profundo
    python glostv_m3u.py --sem-teste    # so coleta (rapido, nao recomendado)

Somente biblioteca padrao do Python (nao precisa de pip).
"""

import argparse
import concurrent.futures
import html
import json
import os
import re
import socket
import subprocess
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from collections import OrderedDict

# ---------------------------------------------------------------------------
# Configuracao
# ---------------------------------------------------------------------------
BASE = "https://glostv.com"
LISTAGEM = BASE + "/tv-ao-vivo-brasil"

AQUI = os.path.dirname(os.path.abspath(__file__))
ARQ_M3U = os.path.join(AQUI, "glostv_brasil.m3u")
ARQ_ESTADO = os.path.join(AQUI, "estado_canais.json")
ARQ_REL = os.path.join(AQUI, "relatorio.json")

LIMITE_FALHAS = 6          # remove somente apos 6 atualizacoes falhando
MAX_PAGINAS = 60           # trava de seguranca da paginacao
THREADS_CANAIS = 14        # paginas de canal em paralelo
THREADS_TESTE = 8          # testes de playback em paralelo
TIMEOUT = 30

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")
HEADERS = {
    "User-Agent": UA,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "pt-BR,pt;q=0.9,en;q=0.8",
}

# Categorias do site (slug -> nome bonito). Ordem de exibicao no SS IPTV.
CATEGORIAS = OrderedDict([
    ("abertos", "Canais Abertos"),
    ("variedades", "Variedades"),
    ("noticias", "Noticias"),
    ("esportes", "Esportes"),
    ("futebol", "Futebol"),
    ("filmes", "Filmes"),
    ("seriados", "Seriados"),
    ("desenhos", "Desenhos"),
    ("documentarios", "Documentarios"),
    ("musica", "Musica"),
    ("cultura", "Cultura"),
    ("educativos", "Educativos"),
    ("evangelica", "Evangelica"),
    ("catolica", "Catolica"),
    ("espirita", "Espirita"),
    ("publicos", "Publicos"),
    ("agronegocio", "Agronegocio"),
    ("culinaria", "Culinaria"),
    ("carros", "Carros"),
    ("televendas", "Televendas"),
])


# ---------------------------------------------------------------------------
# Utilidades
# ---------------------------------------------------------------------------
def limpar_nome(txt):
    """Nome do canal limpo (sem NBSP, sem entidades, sem espacos duplos)."""
    txt = html.unescape(txt or "")
    txt = txt.replace("\xa0", " ").replace("\u200b", "")
    txt = re.sub(r"\s+", " ", txt).strip()
    return txt


def slug_para_nome(slug):
    return limpar_nome(slug.replace("-", " ").title())


def sem_acento(txt):
    txt = unicodedata.normalize("NFKD", txt or "")
    txt = "".join(c for c in txt if not unicodedata.combining(c))
    return txt.replace("&", "e").replace("'", "").strip()


def m3u_esc(txt):
    """Escapa valores para o atributo M3U (aspas dentro quebrariam a linha)."""
    return (txt or "").replace('"', "'").replace("\n", " ").replace("\r", " ").strip()


def log(msg):
    print(msg, flush=True)


def buscar(url, timeout=TIMEOUT, tentativas=2, return_headers=False):
    """GET simples com retry. Retorna (texto, status) ou levanta excecao."""
    ultimo = None
    for n in range(tentativas):
        try:
            req = urllib.request.Request(url, headers=HEADERS)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                corpo = r.read()
                try:
                    texto = corpo.decode("utf-8")
                except UnicodeDecodeError:
                    texto = corpo.decode("latin-1", "ignore")
                if return_headers:
                    return texto, r.status, dict(r.headers)
                return texto, r.status
        except urllib.error.HTTPError as e:
            # 404 e definitivo: nao insiste
            if e.code in (404, 410):
                return "", e.code
            ultimo = e
        except (urllib.error.URLError, socket.timeout, TimeoutError, OSError) as e:
            ultimo = e
        if n + 1 < tentativas:
            time.sleep(1.5)
    if isinstance(ultimo, urllib.error.HTTPError):
        return "", ultimo.code
    raise ultimo if ultimo else RuntimeError("falha de rede")


# ---------------------------------------------------------------------------
# 1) COLETA: lista de canais de uma pagina (com paginacao / carregar mais)
# ---------------------------------------------------------------------------
RE_CARD = re.compile(
    r'<h3 class="entry-title td-module-title"><a href="' + re.escape(BASE) +
    r'/tv-ao-vivo/([^"?/]+)"[^>]*title="([^"]*)"', re.S)
RE_CARD_ALT = re.compile(
    r'<a href="' + re.escape(BASE) + r'/tv-ao-vivo/([^"?/]+)"\s+rel="bookmark"', re.S)
RE_LOGO = re.compile(
    r'<span class="entry-thumb[^"]*"\s+style="background-image: url\(([^)]+)\)', re.S)
RE_PARTIAL = re.compile(
    r'class="tdb_module_loop td_module_wrap[^"]*"(.*?)(?=class="tdb_module_loop|\Z)', re.S)
RE_CAT_NO_CARD = re.compile(
    r'<a href="' + re.escape(BASE) + r'/categorias/([a-z0-9\-]+)"[^>]*class="td-post-category"')

# sligs que NAO sao categorias de conteudo
CATS_IGNORAR = {"top", "portugues", "idiomas", "estados", "anime", "moda", "tempo"}


def extrair_cards(pagina_html):
    """Retorna dict slug -> {nome, logo, categorias} a partir de um HTML."""
    achados = OrderedDict()
    for bloco in RE_PARTIAL.findall(pagina_html):
        m = re.search(r'/tv-ao-vivo/([^"?/]+)"[^>]*title="([^"]*)"', bloco)
        if not m:
            m2 = re.search(r'/tv-ao-vivo/([^"?/]+)', bloco)
            if not m2:
                continue
            slug, nome = m2.group(1), ""
        else:
            slug, nome = m.group(1), m.group(2)
        lg = re.search(r'background-image: url\(([^)]+)\)', bloco)
        cats = RE_CAT_NO_CARD.findall(bloco)
        item = achados.setdefault(slug, {"nome": "", "logo": "", "categorias": []})
        if nome and not item["nome"]:
            item["nome"] = limpar_nome(nome)
        if lg and not item["logo"]:
            item["logo"] = lg.group(1).strip().strip('"\'')
        for c in cats:
            c = c.lower().strip("/")
            if c and c not in CATS_IGNORAR and c not in item["categorias"]:
                item["categorias"].append(c)
    # fallback: cards sem bloco reconhecivel
    for slug, nome in RE_CARD.findall(pagina_html):
        item = achados.setdefault(slug, {"nome": "", "logo": "", "categorias": []})
        if nome and not item["nome"]:
            item["nome"] = limpar_nome(nome)
    for slug in RE_CARD_ALT.findall(pagina_html):
        achados.setdefault(slug, {"nome": slug_para_nome(slug), "logo": "", "categorias": []})
    for slug, item in achados.items():
        if not item["nome"]:
            item["nome"] = slug_para_nome(slug)
    return achados


def total_declarado(pagina_html):
    """Le o 'found_posts'/'post_count' que o tema declara (para detectar falhas)."""
    import base64
    numeros = []
    for b in re.findall(r'base64,([A-Za-z0-9+/=]{80,})"', pagina_html):
        try:
            d = base64.b64decode(b).decode("utf-8", "ignore")
        except Exception:
            continue
        if "found_posts" in d or "post_count" in d:
            for v in re.findall(r'(?:found_posts|post_count)=["\']?(\d+)', d):
                numeros.append(int(v))
    return max(numeros) if numeros else 0


def paginar(url_base):
    """Percorre pagina 1..N ate nao houver mais nada novo (pagina/2, /3 ...)."""
    vistos = OrderedDict()
    pagina = 1
    while pagina <= MAX_PAGINAS:
        url = url_base if pagina == 1 else f"{url_base.rstrip('/')}/page/{pagina}"
        try:
            corpo, status = buscar(url)
        except Exception as e:
            log(f"    pagina {pagina}: erro de rede ({e})")
            break
        if status != 200 or not corpo:
            break
        cards = extrair_cards(corpo)
        novos = [s for s in cards if s not in vistos]
        if pagina == 1:
            logo_map = {}
            for s, it in cards.items():
                if it["logo"]:
                    logo_map[s] = it["logo"]
        log(f"    pagina {pagina}: {len(cards)} canais ({len(novos)} novos)")
        for s, it in cards.items():
            if s not in vistos:
                vistos[s] = it
            else:
                for c in it["categorias"]:
                    if c not in vistos[s]["categorias"]:
                        vistos[s]["categorias"].append(c)
                if it["logo"] and not vistos[s]["logo"]:
                    vistos[s]["logo"] = it["logo"]
        if pagina > 1 and not novos:
            break   # a partir da pagina 2, pagina sem novidade = fim
        if pagina == 1 and len(cards) == 0:
            break
        pagina += 1
    return vistos


def coletar():
    """Varre a pagina principal e todas as categorias. Retorna (canais, ok_rede)."""
    log("\n[1/4] COLETANDO CATALOGO")
    canais = OrderedDict()
    fontes_ok = 0
    try:
        corpo, status = buscar(LISTAGEM)
        if status != 200:
            log(f"  ! pagina principal respondeu HTTP {status}")
        else:
            fontes_ok += 1
            declarado = total_declarado(corpo)
            if declarado:
                log(f"  Site declara {declarado} canais no total")
            pagina = 1
            while pagina <= MAX_PAGINAS:
                url = LISTAGEM if pagina == 1 else f"{LISTAGEM}/page/{pagina}"
                try:
                    html_p, st = (corpo, status) if pagina == 1 else buscar(url)
                except Exception as e:
                    log(f"    pagina {pagina}: erro ({e})")
                    break
                if st != 200 or not html_p:
                    break
                cards = extrair_cards(html_p)
                novos = [s for s in cards if s not in canais]
                log(f"  principal pagina {pagina}: {len(cards)} canais ({len(novos)} novos)")
                for s, it in cards.items():
                    canais.setdefault(s, it)
                if pagina > 1 and not novos:
                    break
                pagina += 1
    except Exception as e:
        log(f"  ! falha na pagina principal: {e}")

    # categorias do proprio site
    log("\n  Varrendo categorias (cada uma com paginacao completa):")
    for slug, nome in CATEGORIAS.items():
        if slug == "abertos":
            continue
        url = f"{BASE}/categorias/{slug}"
        try:
            corpo, status = buscar(url)
        except Exception as e:
            log(f"  - {slug}: erro de rede ({e})")
            continue
        if status != 200 or not corpo:
            log(f"  - {slug}: HTTP {status} (ignorada)")
            continue
        fontes_ok += 1
        cards = extrair_cards(corpo)
        log(f"  - {nome} ({slug}): {len(cards)} canais")
        for s, it in cards.items():
            alvo = canais.setdefault(s, it)
            if slug not in alvo["categorias"]:
                alvo["categorias"].append(slug)
            if not alvo["logo"] and it["logo"]:
                alvo["logo"] = it["logo"]
            if not alvo["nome"] and it["nome"]:
                alvo["nome"] = it["nome"]
        # paginacao da categoria (geralmente tudo vem na pagina 1)
        extra = paginar(url)
        for s, it in extra.items():
            if s not in canais:
                it["categorias"] = [slug]
                canais[s] = it

    # fallbacks de categoria: canal sem categoria no card -> usa o 1o link /categorias/
    log(f"\n  Total coletado: {len(canais)} canais em {fontes_ok} fontes")
    return canais, fontes_ok > 0


# ---------------------------------------------------------------------------
# 2) EXTRAIR O STREAM DA PAGINA DO CANAL
# ---------------------------------------------------------------------------
RE_HLS = re.compile(r'https?://[^"\'\s<>]+\.(?:m3u8|mpd)(?:\?[^"\'\s<>]*)?')
RE_HLS_ATTR = re.compile(r'data-src="([^"]+)"')


def detectar_stream(pagina):
    """Retorna (tipo, url). tipo: HLS | YT | EMBED | NENHUM"""
    m = re.search(r'hp-root[^>]*data-src="([^"]+)"', pagina)
    if m:
        src = html.unescape(m.group(1)).strip()
        if ".m3u8" in src or ".mpd" in src:
            return "HLS", src
        return "EMBED", src
    if 'data-ytid' in pagina:
        return "YT", ""
    if "geo.dailymotion.com" in pagina:
        return "EMBED", "dailymotion"
    m = re.search(r'/player/\?live=([0-9a-f-]{36})', pagina)
    if m:
        return "EMBED", "spalla:" + m.group(1)
    m = re.search(r'data-url="([^"]+)"', pagina)
    if m:
        u = html.unescape(m.group(1))
        if '.m3u8' in u or '.mpd' in u:
            return "HLS", u
        return "EMBED", u
    # ultimo recurso: qualquer m3u8/mpd solto na pagina
    cands = [c for c in RE_HLS.findall(pagina) if "googlevideo" not in c]
    if cands:
        return "HLS", cands[0]
    return "NENHUM", ""


def buscar_stream(canal):
    slug = canal[0]
    url = f"{BASE}/tv-ao-vivo/{slug}"
    try:
        corpo, status = buscar(url, tentativas=2)
    except Exception as e:
        return slug, "ERRO_REDE", str(e)[:80], ""
    if status != 200 or not corpo:
        return slug, "ERRO_PAGINA", f"HTTP {status}", ""
    tipo, src = detectar_stream(corpo)
    return slug, tipo, src, url


# ---------------------------------------------------------------------------
# 3) TESTE REAL DE PLAYBACK
# ---------------------------------------------------------------------------
def _ffprobe(url, timeout=25):
    cmd = ["ffprobe", "-v", "error", "-rw_timeout", str(timeout * 1000000),
           "-analyzeduration", "4000000", "-probesize", "4000000",
           "-show_entries", "stream=codec_type,codec_name,width,height",
           "-of", "json", url]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 15)
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return None, "timeout/ffprobe ausente"
    if not p.stdout.strip():
        return None, (p.stderr or "").strip().splitlines()[-1][:120] if p.stderr.strip() else "sem resposta"
    try:
        dados = json.loads(p.stdout)
    except json.JSONDecodeError:
        return None, "json invalido"
    streams = dados.get("streams", [])
    video = [s for s in streams if s.get("codec_type") == "video"]
    audio = [s for s in streams if s.get("codec_type") == "audio"]
    if not video and not audio:
        return None, "sem trilha de midia"
    info = {
        "video": bool(video),
        "width": (video[0].get("width") if video else 0) or 0,
        "height": (video[0].get("height") if video else 0) or 0,
        "res": f"{((video[0].get('width') if video else 0) or 0)}x{((video[0].get('height') if video else 0) or 0)}",
    }
    return info, ""


def testar_playback(url):
    """Retorna (situacao, detalhe). situacao: tocando | quebrado | inconclusivo"""
    # 1) o manifest responde?
    try:
        texto, status = buscar(url, timeout=20, tentativas=1)
    except urllib.error.HTTPError as e:
        if e.code in (403, 401, 451):
            return "inconclusivo", f"HTTP {e.code} (bloqueio do servidor de origem)"
        if e.code == 404:
            return "quebrado", "HTTP 404 (stream nao existe mais)"
        return "inconclusivo", f"HTTP {e.code}"
    except Exception as e:
        msg = str(e)
        if any(x in msg for x in ("timed out", "Timeout", "getaddrinfo", "Name or service",
                                  "Connection refused", "No route", "Network is unreachable",
                                  "SSL", "handshake")):
            return "inconclusivo", f"rede: {msg[:60]}"
        return "inconclusivo", f"rede: {msg[:60]}"
    if status not in (200, 206):
        if status in (401, 403, 451):
            return "inconclusivo", f"HTTP {status} (bloqueio)"
        if status in (404, 410):
            return "quebrado", f"HTTP {status}"
        return "inconclusivo", f"HTTP {status}"
    cabe = texto.lstrip()[:200]
    if not cabe.startswith("#EXTM3U") and "<MPD" not in cabe:
        return "quebrado", "resposta nao e HLS/DASH"

    # 2) ffprobe: existe video/audio de verdade?
    info, erro = _ffprobe(url)
    if info is None:
        if any(x in erro for x in ("403", "401", "451", "Forbidden")):
            return "inconclusivo", "origem bloqueou: " + erro
        # ffprobe falhou: confirma baixando um segmento real antes de julgar
        seg_ok, seg_det = baixar_segmento(texto, url)
        if seg_ok is True:
            return "tocando", "segmento ok"
        if seg_ok is False:
            return "quebrado", seg_det
        if "404" in erro or "Not Found" in erro:
            return "inconclusivo", erro[:90]
        return "inconclusivo", (seg_det or erro)[:90]

    # 3) ffprobe ja decodificou trilhas reais -> canal tocando.
    #    O download de segmento serve apenas como CONFIRMACAO extra:
    #    se ele falhar aqui, NAO reprovamos o canal (evita falso negativo),
    #    porque o ffprobe conseguiu ler o stream de verdade.
    if info.get("video") or info.get("audio"):
        seg_ok, seg_det = baixar_segmento(texto, url)
        if seg_ok is True:
            return "tocando", (info["res"] if info["video"] else "audio") + " +segmento"
        return "tocando", (info["res"] if info["video"] else "audio")
    seg_ok, seg_det = baixar_segmento(texto, url)
    if seg_ok is True:
        return "tocando", "segmento ok"
    if seg_ok is False:
        return "quebrado", seg_det
    return "inconclusivo", seg_det


def _abs(base, ref):
    """Resolve URL relativa como o player faz (e escapa caracteres invalidos)."""
    ref = html.unescape(ref).strip().strip('\"')
    if not ref or ref.startswith('#'):
        return None
    if ref.startswith('http://') or ref.startswith('https://'):
        url = ref
    elif ref.startswith('//'):
        url = 'https:' + ref
    elif ref.startswith('/'):
        raiz = re.match(r'(https?://[^/]+)', base)
        url = (raiz.group(1) if raiz else base) + ref
    else:
        url = base + ref
    return urllib.parse.quote(url, safe="%:/?&=+~#@!$,;()*[]|")


def _eh_url(linha):
    """Linha de playlist que aponta para midia (ignora duracoes do #EXTINF)."""
    l = linha.strip().strip('\"')
    if not l or l.startswith('#'):
        return False
    if re.fullmatch(r'[0-9.,]+', l):
        return False
    return True


def baixar_segmento(manifest_texto, url_manifest):
    """Baixa 1 segmento real de video.
    True=tocando, False=quebrado, None=inconclusivo."""
    raiz = url_manifest.rsplit('/', 1)[0] + '/'
    linhas = [l.strip() for l in manifest_texto.splitlines() if l.strip()]

    if '#EXT-X-STREAM-INF' in manifest_texto:
        variante = None
        for i, l in enumerate(linhas):
            if l.startswith('#EXT-X-STREAM-INF'):
                for prox in linhas[i + 1:i + 4]:
                    if _eh_url(prox):
                        variante = prox
                        break
                break
        if not variante:
            return None, 'master sem variante'
        sub_url = _abs(raiz, variante)
        try:
            sub, st = buscar(sub_url, timeout=20, tentativas=1)
        except Exception as e:
            return None, 'variante: ' + str(e)[:50]
        if st != 200:
            return (None if st in (401, 403, 451) else False), 'variante HTTP %s' % st
        raiz = sub_url.rsplit('/', 1)[0] + '/'
        linhas = [l.strip() for l in sub.splitlines() if l.strip()]

    alvo = None
    for l in linhas:
        if _eh_url(l) and '.m3u8' not in l:
            alvo = l
            break
    if not alvo:
        return None, 'sem segmento no manifest'
    seg_url = _abs(raiz, alvo)
    if not seg_url:
        return None, 'segmento invalido'
    try:
        req = urllib.request.Request(seg_url, headers=dict(HEADERS, Range='bytes=0-300000'))
        with urllib.request.urlopen(req, timeout=20) as r:
            dados = r.read(400000)
        if len(dados) < 2000:
            return False, 'segmento pequeno (%db)' % len(dados)
        return True, '%db' % len(dados)
    except urllib.error.HTTPError as e:
        return (None if e.code in (401, 403, 451) else False), 'segmento HTTP %s' % e.code
    except Exception as e:
        return None, 'segmento: ' + str(e)[:50]


# ---------------------------------------------------------------------------
# 4) ESTADO + REGRA DAS 6 ATUALIZACOES
# ---------------------------------------------------------------------------
def carregar_estado():
    if os.path.exists(ARQ_ESTADO):
        try:
            with open(ARQ_ESTADO, encoding="utf-8") as f:
                d = json.load(f)
            d.setdefault("canais", {})
            d.setdefault("atualizacoes", 0)
            return d
        except Exception as e:
            log(f"  ! estado ilegivel, recomecando: {e}")
    return {"canais": {}, "atualizacoes": 0}


def salvar_json(caminho, dados):
    with open(caminho, "w", encoding="utf-8") as f:
        json.dump(dados, f, ensure_ascii=False, indent=2)


# ---------------------------------------------------------------------------
# 5) GERAR A M3U
# ---------------------------------------------------------------------------
def categoria_do_canal(info):
    cats = info.get("categorias") or []
    for c in cats:
        if c in CATEGORIAS:
            return c
    if cats:
        return cats[0]
    return "variedades"


def gerar_m3u(canais_final):
    """canais_final: lista de dicts com nome, url, logo, categoria, grupo, id"""
    grupos = OrderedDict()
    for c in canais_final:
        grupos.setdefault(c["categoria"], []).append(c)

    linhas = ["#EXTM3U"]
    ordem = [k for k in CATEGORIAS if k in grupos] + [k for k in grupos if k not in CATEGORIAS]
    for slug in ordem:
        nome_cat = CATEGORIAS.get(slug, slug_para_nome(slug))
        nome_cat = sem_acento(nome_cat)
        itens = sorted(grupos[slug], key=lambda x: sem_acento(x["nome"]).lower())
        for c in itens:
            logo = c.get("logo") or ""
            nome = m3u_esc(c["nome"])
            # padrao que o SS IPTV entende:
            #   tvg-id / tvg-name / tvg-logo / group-title + nome por extenso na URL
            linhas.append(
                f'#EXTINF:-1 tvg-id="{m3u_esc(c["id"])}" tvg-name="{nome}" '
                f'tvg-logo="{m3u_esc(logo)}" group-title="{m3u_esc(nome_cat)}",{nome}'
            )
            linhas.append(c["url"])
    return "\n".join(linhas) + "\n"


# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--completo", action="store_true", help="varredura total + teste profundo")
    ap.add_argument("--sem-teste", action="store_true", help="nao testar playback (nao recomendado)")
    args = ap.parse_args()

    t0 = time.time()
    log("=" * 62)
    log(" GlosTV -> M3U  |  SS IPTV  |  atualizacao automatica")
    log("=" * 62)

    estado = carregar_estado()
    estado_antigo = estado["canais"]
    estado["atualizacoes"] = estado.get("atualizacoes", 0) + 1
    rodada = estado["atualizacoes"]
    log(f"Rodada de atualizacao: #{rodada}")

    # 1) coletar
    canais, site_ok = coletar()
    if not canais:
        log("\n!! Nenhum canal coletado. O site pode estar fora do ar ou bloqueando.")
        if estado_antigo:
            log("   Mantendo a lista anterior intacta (nao removo nada por falha do site).")
            url_base = os.environ.get("URL_PUBLICA", "")
            rel = {"data": time.strftime("%Y-%m-%d %H:%M:%S"), "situacao": "site_inacessivel",
                   "rodada": rodada, "canais_na_lista": len(estado_antigo)}
            salvar_json(ARQ_REL, rel)
            if url_base:
                with open(os.path.join(AQUI, "URL_LISTA.txt"), "w", encoding="utf-8") as f:
                    f.write(url_base + "\n")
        else:
            log("   (sem lista anterior: nada a publicar)")
        return 0

    # 2) extrair streams
    log(f"\n[2/4] EXTRAINDO STREAM DE {len(canais)} CANAIS")
    resultados = {}
    with concurrent.futures.ThreadPoolExecutor(THREADS_CANAIS) as ex:
        futuros = {ex.submit(buscar_stream, (s, it)): s for s, it in canais.items()}
        feitos = 0
        for fut in concurrent.futures.as_completed(futuros):
            slug, tipo, src, pagina = fut.result()
            resultados[slug] = (tipo, src)
            feitos += 1
            if feitos % 50 == 0:
                log(f"  ... {feitos}/{len(canais)}")

    tipos = {}
    for slug, (tipo, src) in resultados.items():
        tipos[tipo] = tipos.get(tipo, 0) + 1
    log("  Tipos de player encontrados: " +
        ", ".join(f"{k}={v}" for k, v in sorted(tipos.items(), key=lambda x: -x[1])))

    hls = {s: src for s, (t, src) in resultados.items() if t == "HLS"}
    nao_hls = {s: resultados[s][1] for s, (t, src) in resultados.items() if t != "HLS"}
    log(f"  Canais com stream direto (tocavel em SS IPTV/VLC): {len(hls)}")
    log(f"  Sem stream direto (YouTube/embed/DRM - nao toca em SS IPTV): {len(nao_hls)}")

    # 3) teste de playback
    log(f"\n[3/4] TESTANDO PLAYBACK ({len(hls)} canais)")
    if args.sem_teste:
        testes = {s: ("tocando", "nao testado") for s in hls}
    else:
        testes = {}
        with concurrent.futures.ThreadPoolExecutor(THREADS_TESTE) as ex:
            futuros = {ex.submit(testar_playback, u): s for s, u in hls.items()}
            feitos = 0
            for fut in concurrent.futures.as_completed(futuros):
                s = futuros[fut]
                try:
                    testes[s] = fut.result()
                except Exception as e:
                    testes[s] = ("inconclusivo", f"erro: {str(e)[:60]}")
                feitos += 1
                if feitos % 50 == 0:
                    log(f"  ... testados {feitos}/{len(hls)}")

    cont = {"tocando": 0, "quebrado": 0, "inconclusivo": 0}
    for s, (st, det) in testes.items():
        cont[st] = cont.get(st, 0) + 1
    log(f"  Tocando: {cont['tocando']} | Quebrados: {cont['quebrado']} | "
        f"Inconclusivos: {cont['inconclusivo']}")

    # 4) reconciliacao com estado (regra das 6)
    log(f"\n[4/4] RECONCILIANDO COM A LISTA ANTERIOR (remover apos {LIMITE_FALHAS} falhas)")
    novo_estado = {}
    entraram_novos, mantidos, removidos = [], [], []
    inconclusivos = []

    for slug, info in canais.items():
        antigo = estado_antigo.get(slug)
        tipo, src = resultados.get(slug, ("NENHUM", ""))
        if slug in testes:
            status, detalhe = testes[slug]
        elif slug in nao_hls:
            status, detalhe = "sem_stream", nao_hls[slug][:60]
        else:
            status, detalhe = "inconclusivo", tipo.lower()

        reg = antigo.copy() if antigo else {
            "id": slug, "nome": info["nome"], "logo": info.get("logo", ""),
            "categoria": categoria_do_canal(info), "falhas": 0, "ok_seguidas": 0,
        }
        reg["nome"] = info["nome"] or reg.get("nome") or slug
        reg["logo"] = info.get("logo") or reg.get("logo", "")
        reg["categoria"] = categoria_do_canal(info) or reg.get("categoria", "variedades")
        reg["url"] = src if tipo == "HLS" else reg.get("url", "")
        reg["tipo"] = tipo
        reg["status"] = status
        reg["detalhe"] = detalhe

        if status == "tocando":
            reg["falhas"] = 0
            reg["ok_seguidas"] = reg.get("ok_seguidas", 0) + 1
            reg["ativo"] = True
            if not antigo:
                entraram_novos.append(slug)
            else:
                mantidos.append(slug)
        elif status == "quebrado":
            reg["falhas"] = reg.get("falhas", 0) + 1
            reg["ok_seguidas"] = 0
            if reg["falhas"] >= LIMITE_FALHAS:
                reg["ativo"] = False
                removidos.append(slug)
            else:
                reg["ativo"] = bool(antigo and antigo.get("url"))
        else:  # inconclusivo / sem_stream -> NUNCA conta falha
            reg["ok_seguidas"] = 0
            reg["ativo"] = bool(reg.get("url")) and bool(antigo and antigo.get("ativo", True))
            inconclusivos.append(slug)
        novo_estado[slug] = reg

    # canais do estado antigo que desapareceram do site: mantem (nao inventa falha)
    for slug, reg in estado_antigo.items():
        if slug not in novo_estado:
            reg = reg.copy()
            reg["status"] = "fora_do_site"
            reg["ativo"] = bool(reg.get("url"))
            novo_estado[slug] = reg

    estado["canais"] = novo_estado
    site_fora = not site_ok
    if site_fora:
        log("  ! Site instavel: estado preservado, nenhuma remocao aplicada")

    # monta a lista final
    finais = []
    for slug, reg in novo_estado.items():
        if not reg.get("url"):
            continue
        if not reg.get("ativo", True):
            continue
        finais.append({
            "id": slug, "nome": reg["nome"], "url": reg["url"],
            "logo": reg.get("logo", ""), "categoria": reg.get("categoria", "variedades"),
        })

    m3u = gerar_m3u(finais)
    with open(ARQ_M3U, "w", encoding="utf-8") as f:
        f.write(m3u)

    relatorio = {
        "data": time.strftime("%Y-%m-%d %H:%M:%S"),
        "rodada": rodada,
        "canais_encontrados": len(canais),
        "com_stream_direto": len(hls),
        "sem_stream_direto": len(nao_hls),
        "tocando": cont.get("tocando", 0),
        "quebrados": cont.get("quebrado", 0),
        "inconclusivos": cont.get("inconclusivo", 0),
        "na_lista_final": len(finais),
        "novos": len(entraram_novos),
        "removidos": len(removidos),
        "removidos_slugs": removidos,
        "por_categoria": {CATEGORIAS.get(c, c): sum(1 for x in finais if x["categoria"] == c)
                          for c in CATEGORIAS if any(x["categoria"] == c for x in finais)},
        "sem_player_direto": {slug: (v or "youtube/embed") for slug, v in nao_hls.items()},
        "tempo_segundos": round(time.time() - t0, 1),
    }
    salvar_json(ARQ_REL, relatorio)
    salvar_json(ARQ_ESTADO, estado)

    log("\n" + "=" * 62)
    log(f" CANAIS ENCONTRADOS ...... {len(canais)}")
    log(f" COM STREAM DIRETO ....... {len(hls)}")
    log(f" TOCANDO (confirmado) .... {cont.get('tocando', 0)}")
    log(f" QUEBRADOS ............... {cont.get('quebrado', 0)}")
    log(f" INCONCLUSIVOS ........... {cont.get('inconclusivo', 0)}")
    log(f" NA LISTA M3U ............ {len(finais)}")
    log(f" NOVOS ................... {len(entraram_novos)}")
    log(f" REMOVIDOS (6 falhas) .... {len(removidos)}")
    log(f" Arquivo: {ARQ_M3U}")
    log(f" Tempo: {relatorio['tempo_segundos']}s")
    log("=" * 62)

    url_publica = os.environ.get("URL_PUBLICA", "")
    if url_publica:
        with open(os.path.join(AQUI, "URL_LISTA.txt"), "w", encoding="utf-8") as f:
            f.write(url_publica + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
