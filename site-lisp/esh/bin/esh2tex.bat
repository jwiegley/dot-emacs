@setlocal
@if not defined EMACS (set EMACS=emacs)
@%EMACS% -Q --script "%~dp0esh2tex" -- %*
