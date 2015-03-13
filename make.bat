@echo OFF
REM Change this to ON when debugging this batch file.

rem Written by Frank Schmitt (ich@frank-schmitt.net)
rem based on the work by David Charlap (shamino@writeme.com)
rem .
rem .
rem Clear PWD so emacs doesn't get confused
set GNUS_PWD_SAVE=%PWD%
set PWD=
set ERROR=:
REM set pause=

if %1p == p goto usage

echo * Installing Gnus on your system.  Operating system:
ver
rem Emacs 20.7 no longer includes emacs.bat. Use emacs.exe if the batch file is
rem not present -- this also fixes the problem about too many parameters on Win9x.
if exist %1\emacs.bat goto ebat
if exist %1\emacs.exe goto eexe
if exist %1\xemacs.exe goto xemacs
goto noemacs

:ebat
set EMACS=emacs.bat
echo.
echo ***************************************************************************
echo * Using emacs.bat  (If you've got Emacs 20.3 or higher please remove
echo * Emacs.bat, it isn't needed anymore.)
echo ***************************************************************************
echo.
goto emacs

:eexe
set EMACS=emacs.exe
echo.
echo ***************************************************************************
echo * Using emacs.exe
echo ***************************************************************************
echo.
goto emacs

:emacs
if not "%2" == "/copy" goto emacsnocopy
if not exist %1\..\site-lisp\nul mkdir %1\..\site-lisp
if not exist %1\..\site-lisp\gnus\nul mkdir %1\..\site-lisp\gnus
if not exist %1\..\site-lisp\subdirs.el set subdirwarning=yes
:emacsnocopy
set EMACS_ARGS=-batch -q -no-site-file
set GNUS_INFO_DIR=%1\..\info
set GNUS_LISP_DIR=%1\..\site-lisp\gnus\lisp
set GNUS_ETC_DIR=%1\..\site-lisp\gnus\etc
goto lisp

:xemacs
set EMACS=xemacs.exe
if not "%2" == "/copy" goto xemacsnocopy
if not exist %1\..\..\site-packages\nul mkdir %1\..\..\site-packages\
if not exist %1\..\..\site-packages\info\nul mkdir %1\..\..\site-packages\info
if not exist %1\..\..\site-packages\lisp\nul mkdir %1\..\..\site-packages\lisp
if not exist %1\..\..\site-packages\etc\nul mkdir %1\..\..\site-packages\etc
:xemacsnocopy
set EMACS_ARGS=-batch -no-autoloads
set GNUS_INFO_DIR=%1\..\..\site-packages\info
set GNUS_LISP_DIR=%1\..\..\site-packages\lisp\gnus
set GNUS_ETC_DIR=%1\..\..\site-packages\etc
echo.
echo ***************************************************************************
echo * Using xemacs.exe
echo ***************************************************************************
echo.
goto lisp

:lisp
if "%pause%" == "pause" pause
set EMACSBATCH=call %1\%EMACS% %EMACS_ARGS%
cd lisp
if exist gnus-load.el attrib -r gnus-load.el
if exist gnus-load.el del gnus-load.el
echo.
echo * Stand by while generating autoloads.
echo.
%EMACSBATCH% -l ./dgnushack.el -f dgnushack-make-cus-load .
if ErrorLevel 1 set ERROR=make-cus-load
%EMACSBATCH% -l ./dgnushack.el -f dgnushack-make-auto-load .
if ErrorLevel 1 set ERROR=%ERROR%,make-auto-load
%EMACSBATCH% -l ./dgnushack.el -f dgnushack-make-load
if ErrorLevel 1 set ERROR=%ERROR%,make-load
echo.
echo * Stand by while compiling lisp files.
echo.
%EMACSBATCH% -l ./dgnushack.el -f dgnushack-compile
if ErrorLevel 1 set ERROR=%ERROR%,compile

if not "%2" == "/copy" goto infotest
echo.
echo * Stand by while copying lisp files.
echo.
if not exist %GNUS_LISP_DIR%\nul mkdir %GNUS_LISP_DIR%
xcopy /R /Q /Y *.el* %GNUS_LISP_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-lisp
goto infotest

:infotest
cd ..\texi
if exist sieve attrib -r sieve
if exist sieve del sieve

echo * Checking if makeinfo is available...
makeinfo sieve.texi
if exist sieve goto minfo
echo * No makeinfo found, using infohack.el.
set EMACSINFO=%EMACSBATCH% -l infohack.el -f batch-makeinfo
echo.
echo ***************************************************************************
echo * Using infohack.el, if you've got makeinfo.exe put it in PATH.
echo ***************************************************************************
echo.
goto info

:minfo
set EMACSINFO=makeinfo
echo.
echo ***************************************************************************
echo * Using makeinfo
echo ***************************************************************************
echo.
goto info

:info
if "%pause%" == "pause" pause
echo.
echo * Stand by while generating info files.
echo.
%EMACSINFO% emacs-mime.texi
if ErrorLevel 1 set ERROR=%ERROR%,emacs-mime.texi
%EMACSINFO% gnus.texi
if ErrorLevel 1 set ERROR=%ERROR%,gnus.texi
%EMACSINFO% sieve.texi
if ErrorLevel 1 set ERROR=%ERROR%,sieve.texi
%EMACSINFO% pgg.texi
if ErrorLevel 1 set ERROR=%ERROR%,pgg.texi
%EMACSINFO% message.texi
if ErrorLevel 1 set ERROR=%ERROR%,message.texi
%EMACSINFO% sasl.texi
if ErrorLevel 1 set ERROR=%ERROR%,sasl.texi

if not "%2" == "/copy" goto nocopy
if not exist %GNUS_INFO_DIR%\nul mkdir %GNUS_INFO_DIR%

echo.
echo * Stand by while copying info files.
echo.
xcopy /R /Q /Y gnus       %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-gnus-info
xcopy /R /Q /Y gnus-?     %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-gnus-x-info
xcopy /R /Q /Y gnus-??    %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-gnus-xx-info
xcopy /R /Q /Y message    %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-message-info
if exist message-1 xcopy /R /Q /Y message-?  %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-message-x-info
xcopy /R /Q /Y emacs-mime %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-emacs-mime-info
xcopy /R /Q /Y sieve      %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-sieve-info
xcopy /R /Q /Y pgg        %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-pgg-info
xcopy /R /Q /Y sasl        %GNUS_INFO_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-sasl-info

echo.
echo ***************************************************************************
echo * You should add the following lines to
echo * %GNUS_INFO_DIR%\dir
echo * if they aren't already there:
echo *
echo * * PGG: (pgg).	Emacs interface to various PGP implementations.
echo * * Sieve: (sieve).	Managing Sieve scripts in Emacs.
echo * * SASL: (sasl).	The Emacs SASL library.
echo ***************************************************************************
echo.

:etc
if "%pause%" == "pause" pause
cd ..\etc
echo.
echo * Stand by while copying etc files.
echo.
REM
if not exist %GNUS_ETC_DIR% mkdir %GNUS_ETC_DIR%
echo ** gnus-tut.txt ...
xcopy /R /Q /Y gnus-tut.txt %GNUS_ETC_DIR%
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-gnus-tut-txt
REM
REM FIXME: Instead of C&P, we should use a FOR loop.
REM
set i=images
if not exist %GNUS_ETC_DIR%\%i%\nul mkdir %GNUS_ETC_DIR%\%i%
echo ** .\%i%\ ...
xcopy /R /Q /Y .\%i%\*.* %GNUS_ETC_DIR%\%i%\
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-%i%
REM
set i=images\mail
if not exist %GNUS_ETC_DIR%\%i%\nul mkdir %GNUS_ETC_DIR%\%i%
echo ** .\%i%\ ...
xcopy /R /Q /Y .\%i%\*.* %GNUS_ETC_DIR%\%i%\
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-%i%
REM
set i=images\gnus
if not exist %GNUS_ETC_DIR%\%i%\nul mkdir %GNUS_ETC_DIR%\%i%
echo ** .\%i%\ ...
xcopy /R /Q /Y .\%i%\*.* %GNUS_ETC_DIR%\%i%\
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-%i%
REM
set i=images\smilies
if not exist %GNUS_ETC_DIR%\%i%\nul mkdir %GNUS_ETC_DIR%\%i%
echo ** .\%i%\ ...
xcopy /R /Q /Y .\%i%\*.* %GNUS_ETC_DIR%\%i%\
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-%i%
REM
set i=images\smilies\grayscale
if not exist %GNUS_ETC_DIR%\%i%\nul mkdir %GNUS_ETC_DIR%\%i%
echo ** .\%i%\ ...
xcopy /R /Q /Y .\%i%\*.* %GNUS_ETC_DIR%\%i%\
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-%i%
REM
set i=images\smilies\medium
if not exist %GNUS_ETC_DIR%\%i%\nul mkdir %GNUS_ETC_DIR%\%i%
echo ** .\%i%\ ...
xcopy /R /Q /Y .\%i%\*.* %GNUS_ETC_DIR%\%i%\
if ErrorLevel 1 set ERROR=%ERROR%,copy-etc-%i%
REM
set i=
goto warnings

:nocopy
echo.
echo ***************************************************************************
echo * You chose not to copy the files, therefore you should add the
echo * following lines to the TOP of your [X]emacs customization file:
echo *
echo * (add-to-list 'load-path "/Path/to/gnus/lisp")
echo * (if (featurep 'xemacs)
echo *     (add-to-list 'Info-directory-list "c:/Path/to/gnus/texi/")
echo *   (add-to-list 'Info-default-directory-list "c:/Path/to/gnus/texi/"))
echo * (require 'gnus-load)
echo *
echo * Replace c:/Path/to/gnus with the Path where your new Gnus is (that's here
echo * and yes, you've got to use forward slashes).
echo ***************************************************************************
echo.

:warnings
if not "%subdirwarning%" == "yes" goto warngnusload
echo.
echo ***************************************************************************
echo * There's no subdirs.el file in your site-lisp directory, you should
echo * therefor add the following line to the TOP of your Emacs
echo * customization file:
echo *
echo * (add-to-list 'load-path "/Path/to/emacs-site-lisp-directory/gnus/lisp")
echo * (require 'gnus-load)
echo * Yes, it must be forward slashes.
echo ***************************************************************************
echo.
goto warnerrors

:warngnusload
echo.
echo ***************************************************************************
echo * You should add the following line to the TOP of your Emacs
echo * customization file:
echo *
echo * (require 'gnus-load)
echo ***************************************************************************
echo.

:warnerrors
if "%ERROR%"==":" goto noerrors
set errorlevel=1
echo.
echo ***************************************************************************
echo * WARNING ERRORS OCCURRED!
echo * You should look for error messages in the output of the called programs
echo * and try to find out what exactly went wrong.
echo * Errors occured in the following modules:
echo * %ERROR%
echo ***************************************************************************
echo.
goto done

:noerrors
set errorlevel=0

:done
cd ..
goto end

:noemacs
echo.
echo ***************************************************************************
echo * Unable to find emacs.exe or xemacs.exe on the path you specified!
echo * STOP!
echo ***************************************************************************
echo.
goto usage

:usage
echo.
echo ***************************************************************************
REM echo * Usage: make.bat :[X]Emacs-exe-dir: [/copy] [ ^> inst-log.txt 2^>^&1 ]
echo * Usage: make.bat :[X]Emacs-exe-dir: [/copy]
echo *
echo * where: :[X]Emacs-exe-dir: is the directory your
echo *           emacs.exe respectively xemacs.exe resides in,
echo *           e.g. G:\Programme\XEmacs\XEmacs-21.4.11\i586-pc-win32\
echo *           or G:\Emacs\bin
echo *        /copy indicates that the compiled files should be copied to your
echo *           emacs lisp, info, and etc site directories.
REM echo *        ^> inst-log.txt 2^>^&1
REM echo *           Log output to inst-log.txt
echo ***************************************************************************
echo.

:end
rem Restore environment variables
set PWD=%GNUS_PWD_SAVE%
set GNUS_PWD_SAVE=
set EMACSBATCH=
set GNUS_LISP_DIR=
set GNUS_INFO_DIR=
set GNUS_ETC_DIR=
set subdirwarning=
set ERROR=
