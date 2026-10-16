@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo 内部教学门户启动中...
start "" http://localhost:8123
node server.js
pause
