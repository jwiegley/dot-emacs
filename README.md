# Lua mode

[![Build Status](https://travis-ci.org/immerrr/lua-mode.svg?branch=master)](https://travis-ci.org/immerrr/lua-mode)

**lua-mode** is a major mode for editing Lua sources in Emacs.


If you have a problem or a suggestion about **lua-mode**, please, let me know about it via github's [Issue Tracker](https://github.com/immerrr/lua-mode/issues).

## INSTALLATION

### EL-GET INSTALLATION

[El-get](https://github.com/dimitri/el-get) is a package manager which greatly simplifies adding
modules to your Emacs and keeping them up-to-date. Once you have **el-get** set up, installing
**lua-mode** can be done with

    <M-x> el-get-install "lua-mode"

and updating is no more than

    <M-x> el-get-update "lua-mode"`
    
Please, consult with [el-get documentation](https://github.com/dimitri/el-get/blob/master/README.md) for further information.

### MANUAL INSTALLATION

To install, you need to make sure that `lua-mode.el` is on your load-path (and optionally byte-compile
it) and to set up Emacs to automatically enable **lua-mode** for `*.lua` files or ones that contain lua
hash-bang line (`#!/usr/bin/lua`). Putting this snippet to `.emacs` should be enough in most cases:
```lisp
    ;;;; This snippet enables lua-mode

    ;; This line is not necessary, if lua-mode.el is already on your load-path
    (add-to-list 'load-path "/path/to/directory/where/lua-mode-el/resides")

    (autoload 'lua-mode "lua-mode" "Lua editing mode." t)
    (add-to-list 'auto-mode-alist '("\\.lua$" . lua-mode))
    (add-to-list 'interpreter-mode-alist '("lua" . lua-mode))
```

## FEATURES

- syntactic indentation & highlighting (including multiline literals/comments)
- evaluation of lines/regions/functions/files in Lua subprocess or direct interaction with its REPL
- documentation lookup (using online/offline reference manual, e.g. [string.find](http://www.lua.org/manual/5.1/manual.html#pdf-string.find))
- [imenu](http://www.gnu.org/software/emacs/manual/html_node/emacs/Imenu.html) integration
- [HideShow](http://www.gnu.org/software/emacs/manual/html_node/emacs/Hideshow.html) integration

## CUSTOMIZATION

The following variables are available for customization (see more via `M-x customize-group lua`):

- Var `lua-indent-level` (default `3`): indentation offset in spaces
- Var `lua-indent-string-contents` (default `nil`): set to `t` if you like to have contents of multiline strings to be indented like comments
- Var `lua-mode-hook`: list of functions to execute when lua-mode is initialized
- Var `lua-documentation-url` (default `"http://www.lua.org/manual/5.1/manual.html#pdf-"`): base URL for documentation lookup
- Var `lua-documentation-function` (default `browse-url`): function used to show documentation (`eww` is a viable alternative for Emacs 25)

## LUA SUBPROCESS CREATION

- Var `lua-default-application` (default `"lua"`): command to start up the subprocess (REPL)
- Var `lua-default-command-switches` (default `"-i"`): arguments to pass to the subprocess on startup (make sure `-i` is there if you expect working with Lua shell interactively)
- Cmd `lua-start-process`: start new REPL process, usually happens automatically
- Cmd `lua-kill-process`: kill current REPL process

## LUA SUBPROCESS INTERACTION

- Cmd `lua-show-process-buffer`: switch to REPL buffer
- Cmd `lua-hide-process-buffer`: hide window showing REPL buffer
- Var `lua-always-show`: show REPL buffer after sending something
- Cmd `lua-send-buffer`: send whole buffer
- Cmd `lua-send-current-line`: send current line
- Cmd `lua-send-defun`: send current top-level function
- Cmd `lua-send-region`: send active region
- Cmd `lua-restart-with-whole-file`: restart REPL and send whole buffer
