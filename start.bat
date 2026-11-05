@echo off
cd /d "%~dp0"
echo Starting dashboard... close this window to stop.
start "" cmd /c "timeout /t 4 /nobreak >nul & start http://127.0.0.1:8000"
python -m uvicorn app:app
pause
