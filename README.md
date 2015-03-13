fringe-helper
=============

helper functions for Emacs fringe bitmaps

[![Build Status](https://travis-ci.org/nschum/fringe-helper.el.png?branch=master)](https://travis-ci.org/nschum/fringe-helper.el)

fringe-helper contains helper functions for fringe bitmaps.

`fringe-helper-define` allows you to to define fringe bitmaps using a visual
string replesentation.  For example:

    (fringe-helper-define 'test-bitmap '(top repeat)
      "XX......"
      "..XX...."
      "....XX.."
      "......XX")

You can also generate arguments for `define-fringe-bitmap` yourself, by
using `fringe-helper-convert`.

fringe-helper also provides a few stock bitmaps.  They are loaded on demand
by `fringe-lib-load` and adapt to the current fringe size to a certain
extend.

- `fringe-helper-insert` inserts a fringe bitmap at point and
- `fringe-helper-insert-region` inserts a fringe bitmap along a region.
- `fringe-helper-remove` removes both kinds.

Here's an example for enhancing `flymake-mode` with fringe bitmaps:

    (require 'fringe-helper)
    (require 'flymake)

    (defvar flymake-fringe-overlays nil)
    (make-variable-buffer-local 'flymake-fringe-overlays)

    (defadvice flymake-make-overlay (after add-to-fringe first
                                     (beg end tooltip-text face mouse-face)
                                     activate compile)
      (push (fringe-helper-insert-region
             beg end
             (fringe-lib-load (if (eq face 'flymake-errline)
                                  fringe-lib-exclamation-mark
                                fringe-lib-question-mark))
             'left-fringe 'font-lock-warning-face)
            flymake-fringe-overlays))

    (defadvice flymake-delete-own-overlays (after remove-from-fringe activate
                                            compile)
      (mapc 'fringe-helper-remove flymake-fringe-overlays)
      (setq flymake-fringe-overlays nil))
