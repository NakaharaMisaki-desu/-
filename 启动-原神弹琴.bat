@echo off
chcp 65001 >nul
rem ============================================================
rem  Genshin Lyre Player - normal launcher (no console window)
rem ============================================================
cd /d "%~dp0"
set "PYW="
for /f "delims=" %%i in ('python -c "import sys,os;print(os.path.join(os.path.dirname(sys.executable),'pythonw.exe'))" 2^>nul') do set "PYW=%%i"
if defined PYW if exist "%PYW%" (
    start "" "%PYW%" "%~dp0genshin_lyre.py"
    goto :eof
)
where pythonw >nul 2>nul
if %errorlevel%==0 (
    start "" pythonw "%~dp0genshin_lyre.py"
    goto :eof
)
where python >nul 2>nul
if %errorlevel%==0 (
    python "%~dp0genshin_lyre.py"
    goto :eof
)
echo [ERROR] Python was not found on this computer.
echo         Please install Python 3.10 or newer (tkinter included) and try again.
pause
