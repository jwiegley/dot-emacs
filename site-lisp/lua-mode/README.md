# Lua mode

**lua-mode** is a major mode for editing Lua sources in Emacs. After a rather long hiatus, it's back in active development stage, so make sure to visit [homepage](https://github.com/immerrr/lua-mode) frequently enough.

If you have a problem or a suggestion about **lua-mode**, please, let me know about it via github's [Issue Tracker](https://github.com/immerrr/lua-mode/issues).

## INSTALLATION

To install, just copy `lua-mode.el` into a directory on your load-path (and optionally byte-compile it).
To set up Emacs to automatically edit files ending in `.lua` or with a lua hash-bang line using **lua-mode**
add the following to your init file:

    (autoload 'lua-mode "lua-mode" "Lua editing mode." t)
    (add-to-list 'auto-mode-alist '("\\.lua$" . lua-mode))
    (add-to-list 'interpreter-mode-alist '("lua" . lua-mode))

## USAGE

**lua-mode** supports c-mode style formatting and sending of lines/regions/files to a Lua interpreter. An
interpreter (see variable `lua-default-application`) will be started if you try to send some code and none
is running. You can use the process-buffer (named after the application you chose) as if it were an
interactive shell. See the documentation for `comint.el` for details.

Lua-mode also works with Hide Show minor mode (see ``hs-minor-mode``).

## TODO
Currently, there're a lot of features that need fixing (or reimplementing), including but not limited to:

1. implementing autotesting of indentation engine
1. supporting line-continuation commas
1. fixing close-brace/paren positioning
1. fix syntax handling of multiline comments/literals (including both highlighting & indentation)
1. implementing a crisp scheme of customizing the way lua-mode indents the code
1. cleaning up existing code
1. extending docs & comments

## CEDET/Semantic integration
Also, there's a rather distant goal to integrate lua-mode with [cedet's semantic](http://cedet.sourceforge.net/semantic.shtml). This would mean an almost complete rewrite, but I think the challenge is worth it. There's a slightest concern about the overhead brought by this dependency, but **semantic** is already being shipped with Emacs, so there might be no problem after all.

### Use wisent-generated grammar
First stage would be to rewrite syntax handling with help of **semantic/wisent**-generated parser based on the actual Lua grammar. Currently, syntax analysis is done ad-hoc and, despite the model is oversimplified and doesn't treat corner situation well, it's still very tricky and really hard to grasp.

### Extend cedet/semantic facilities onto Lua
And there's the cherry on the pie: after completing the wisent-generated parser, the next step will be to provide semantic with all the information it needs to do it's magic of code analysis and generation.
