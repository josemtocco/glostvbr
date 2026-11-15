@echo off
chcp 65001 >nul
title GlosTV - Gerar lista M3U (Brasil)
echo ============================================
echo  Gerando a lista a partir do Brasil
echo ============================================
where python >nul 2>nul
if errorlevel 1 (
  echo [ERRO] Python nao encontrado. Instale de python.org e marque "Add to PATH".
  pause
  exit /b 1
)
where ffprobe >nul 2>nul
if errorlevel 1 (
  echo [AVISO] ffprobe nao encontrado - teste de playback menos preciso.
  echo         Baixe o ffmpeg em ffmpeg.org e adicione a pasta bin ao PATH.
)
python glostv_m3u.py %*
echo.
echo Lista gerada: glostv_brasil.m3u
pause
