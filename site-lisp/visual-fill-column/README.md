# Visual Fill Column #

`visual-fill-column-mode` is a small Emacs minor mode that mimics the effect of `fill-column` in `visual-line-mode`. Instead of wrapping lines at the window edge, which is the standard behaviour of `visual-line-mode`, it wraps lines at `fill-column`. If `fill-column` is too large for the window, the text is wrapped at the window edge.


## Installation ##

Install `visual-fill-column` via [Melpa](http://melpa.org), or put `visual-fill-column-mode.el` in your load path, (optionally) byte-compile it, and add `(require ’visual-fill-column)` to your `init.el`.


## Usage ##

`visual-fill-column-mode` is primarily intended to be used alongside `visual-line-mode`. If you’ve set the option `global-visual-line-mode`, or if you activate `visual-line-mode` in major mode hooks, you can customise the option `global-visual-fill-column-mode` or add the command `(global-visual-fill-column-mode)` to your init file. `visual-fill-column-mode` will then be activated in every buffer that uses `visual-line-mode`.

If you don’t use either of these methods to start `visual-line-mode`, and instead prefer to call `visual-line-mode` interactively (i.e., `M-x visual-line-mode`), you can add `visual-fill-column-mode` to `visual-line-mode-hook` in order to activate it automatically when you call `visual-line-mode`. 

Note that `visual-fill-column-mode` is not tied to `visual-line-mode`: it is perfectly possible to use it on its own, in buffers that use some other word-wrapping method (e.g., `auto-fill-mode`), or in buffers that do not wrap at all. You can activate it interactively with `visual-fill-column-mode` or you can add the command `visual-fill-column-mode` in mode hooks.

`visual-fill-column-mode` works by widening the right window margin. This reduces the area that is available for text display, creating the appearance that the text is wrapped at `fill-column`. The amount by which the right margin is widened depends on the window width and is automatically adjusted when the window’s width changes (e.g., when the window is split in two side-by-side windows).

In buffers that are explicitly right-to-left (i.e., those where `bidi-paragraph-direction` is set to `right-to-left`), the left margin is expanded, so that the text appears at the window’s right side.

Widening the margin causes the fringe to be pushed inward. For this reason, the fringes are placed outside the margins by setting the variable `fringes-outside-margins` to `t`.

Note that Emacs won’t vertically split a window (i.e., into two side-by-side windows) that has wide margins. As a result, displaying buffers such as `*Help*` buffers, `*Completion*` buffers, etc., won’t split a window vertically, even if there appears to be enough space for a vertical split. This is not problematic, but it may be undesirable. To remedy this, you can set the option `split-window-preferred-function` to `visual-fill-column-split-window-sensibly`. This function first unsets the margins and then calls `split-window-sensibly` to do the actual splitting.

The width of the margins is adjusted for the text size. However, interactive adjustments (e.g., with `text-size-adjust`) cannot be detected by `visual-fill-column-mode`, therefore if you adjust the text size while `visual-fill-column-mode` is active, the margins won't be adjusted. To remedy this, you can force a redisplay, e.g., by switching buffers, splitting and unsplitting the window or calling `redraw-display`.

Alternatively, you can advise the function `text-size-adjust` (or whatever function you use to adjust the text size) with the function `visual-fill-column-adjust`:

    (advice-add 'text-scale-adjust :after
      #'visual-fill-column-adjust)


## Options ##

`visual-fill-column-width`: column at which to wrap lines. If set to `nil` (the default), use the value of `fill-column` instead.

`visual-fill-column-center-text`: if set to `t`, centre the text area in the window. By default, the text is displayed at the window’s (left) edge, mimicking the effect of `fill-column`.

`visual-fill-column-fringes-outside-margins`: if set to `t`, put the fringes outside the margins.

All three options are buffer-local, so the values you set through Customize are default values. They can also be set in mode hooks or directory or file local variables in order to customise particular files or file types.
