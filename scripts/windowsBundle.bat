@ECHO OFF

::::::::::::::::::: Individual Components URLS :::::::::::::::::::::::::::::::::::::::::::::::::::::
:: TODO: Take care of making versioning dynamic for VSCodium and PortableGit

:: (1) 7z to extract git, (2) Git (3) VC Redistributable for Lean Tar (4) VSCodium the editor
:: (5) Current Mathlibs Version of Lean (6) Elan Installer Script (7) Lean VSCode extension
set Z7Z_URL="https://www.7-zip.org/a/7zr.exe"
set GIT_URL="https://github.com/git-for-windows/git/releases/download/v2.41.0.windows.3/PortableGit-2.41.0.3-64-bit.7z.exe"
set VC_REDIST_URL="https://aka.ms/vs/17/release/vc_redist.x64.exe"
set VSCODIUM_URL="https://github.com/VSCodium/vscodium/releases/download/1.81.0.23216/VSCodium-win32-x64-1.81.0.23216.zip"
set MATHLIB_LEAN_TOOLCHAIN_URL="https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain"
set ELAN_INSTALLER_URL="https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
set VSCODE_LEAN4_EXT_URL="https://github.com/leanprover/vscode-lean4/releases/download/v0.0.108/lean4-0.0.108.vsix"

mkdir TryLean4Bundle
cd TryLean4Bundle

::::::::::::::::::::: Download the Components ::::::::::::::::::::::::::::::::::::::::::::::::::::::::
curl -L -C - --output "lean-toolchain" %MATHLIB_LEAN_TOOLCHAIN_URL%
curl -L -C - --output "z7z.exe" %Z7Z_URL%
curl -L -C - --output "git-install.exe" %GIT_URL%
curl -L -C - --output "vc_redist.x64.exe" %VC_REDIST_URL%
curl -L -C - --output "elan-init.sh" %ELAN_INSTALLER_URL%
curl -L -C - --output "vscodium.zip" %VSCODIUM_URL%
curl -L -C - --output "lean4ext.zip" %VSCODE_LEAN4_EXT_URL%

::::::::::::::::::: Extracting Components ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::

:: Extract Git Portable using 7zip
z7z.exe x "git-install.exe" -o".\PortableGit"
where tar
:: Extract VSCodium and  Install vscode-lean4 extension
IF NOT EXIST VSCodium mkdir VSCodium
"C:\Windows\System32\tar.exe" -x -f vscodium.zip -C ".\VSCodium"

IF NOT EXIST VSCodium\leanext mkdir VSCodium\leanext
"C:\Windows\System32\tar.exe" -x -f lean4ext.zip -C ".\VSCodium\leanext"
xcopy /E /I ".\VSCodium\leanext\extension" ".\VSCodium\data\extensions\leanprover"
rmdir /S /Q ".\VSCodium\leanext"

:: TODO: perhaps modification in the RunLean.bat script so that it detects OS version and installs
:: vc_redist if necessary. VC_Redist installation is necessary when windows is older than build
:: 18xxx (check version to make sure!!!)


:: Control Elan's location by ELAN_HOME and Cache Location by XDG_CACHE_HOME
::::::::::::::::::: Prepare Environment Variables and Clean Path
set Path=%Path%;%CD%;%CD%\PortableGit\bin\;%CD%\Elan\bin\
set ELAN_HOME=%CD%\Elan
set XDG_CACHE_HOME=%CD%\Cache
set ELECTRON_EXTRA_LAUNCH_ARGS=--disable-gpu-sandbox
set DEMOPROJ=DemoProj
set /p LEAN_TOOLCHAIN_VERSION=<lean-toolchain

cd
::::::::::::::::::: Installation of ELAN in Current Folder with Mathlibs Toolchain version
echo "./elan-init.sh -y --no-modify-path --default-toolchain %LEAN_TOOLCHAIN_VERSION%"
IF EXIST ".\PortableGit\bin\bash.exe" echo "FOUND IT"
IF NOT EXIST ".\PortableGit\bin\bash.exe" echo "NOT FOUND !!!!!! "
".\PortableGit\bin\bash.exe" -c "./elan-init.sh -y --no-modify-path --default-toolchain %LEAN_TOOLCHAIN_VERSION%"

::::::::::::::::::: Create demo Project
IF EXIST DemoProj rmdir /Q /S DemoProj
echo "lake %LEAN_TOOLCHAIN_VERSION% new %DEMOPROJ% math"
lake "+%LEAN_TOOLCHAIN_VERSION%" new %DEMOPROJ% math
"PortableGit\bin\bash.exe" -c "cd %DEMOPROJ% && lake update && lake exe cache get-"
:: Copy the lean-toolchain file because for lake does not create it
copy lean-toolchain %DEMOPROJ%\lean-toolchain

::::::::::::::::::: Packup everyithng into 7z executable archive :::::::::::::::::::::::::::::::::::
cd ..
:: Delete the executables
del "TryLean4Bundle\git-install.exe"
del "TryLean4Bundle\vscodium.zip"
del "TryLean4Bundle\elan-init.sh"
copy /B TryLean4Bundle\z7z.exe /B z7z.exe
copy /A "RunLean.bat" /A "TryLean4Bundle\RunLean.bat"

set /p LEAN_TOOLCHAIN_VERSION=<lean-toolchain
:: Use Toolchain version and date in filename
FOR /F "tokens=2,3 delims=/:" %%G IN ("%LEAN_TOOLCHAIN_VERSION%") do set ARXV_NAME=%%G-%%H
FOR /f "tokens=2-4 delims=:./ " %%G IN ("%date%") DO (SET BUNDDATE=%%I-%%H-%%G)
echo ".\z7z.exe a -sfx TryLean4Bundle_%ARXV_NAME%_%BUNDDATE%.exe TryLean4Bundle"
".\z7z.exe" a -bt -bsp2 -bso1 -sfx "TryLean4Bundle_%ARXV_NAME%_%BUNDDATE%.exe" TryLean4Bundle
