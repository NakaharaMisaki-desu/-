@echo off
chcp 65001 >nul
rem ============================================================
rem  Genshin Lyre Player - run as administrator
rem  Use this when the game is running elevated, otherwise
rem  Windows blocks simulated keystrokes (SendInput) silently.
rem ============================================================
cd /d "%~dp0"
set "PYW="
for /f "delims=" %%i in ('python -c "import sys,os;print(os.path.join(os.path.dirname(sys.executable),'pythonw.exe'))" 2^>nul') do set "PYW=%%i"
if not defined PYW set "PYW=pythonw"
powershell -NoProfile -ExecutionPolicy Bypass -Command "Start-Process -FilePath '%PYW%' -ArgumentList 'genshin_lyre.py' -WorkingDirectory '%~dp0' -Verb RunAs"
if errorlevel 1 (
    echo [ERROR] Could not elevate. Right-click this file and pick "Run as administrator".
    pause
)
