# org-present-mode

This is meant to be an extremely minimalist presentation tool for
Emacs [org-mode](http://orgmode.org/).  Simply layout your
presentation with each slide under a top-level header, start the minor
mode with 'org-present', and page through each slide with left/right
keys.

## Philosophy

Most of the time I'm giving a talk, it is a work in progress and I want to be be able to edit
as I go along. Also, to split my frame and work on code examples with my slides still visible.

## Configuration

Add something like this to your emacs config:

```lisp
(add-to-list 'load-path "~/path/to/org-present")
(autoload 'org-present "org-present" nil t)

(add-hook 'org-present-mode-hook
          (lambda ()
            (org-present-big)
            (org-display-inline-images)))

(add-hook 'org-present-mode-quit-hook
          (lambda ()
            (org-present-small)
            (org-remove-inline-images)))
```

Then start the minor mode with:

```
M-x org-present
```

Keys are left/right for movement, C-c C-= for large txt, C-c C-- for
small text, and C-c C-q for quit (which will return you back to
vanilla org-mode).

## Beautification

This works well with
[hide-mode-line](http://webonastick.com/emacs-lisp/hide-mode-line.el),
which hides the mode-line when only one frame and buffer are open.

If you're on a Mac you might also want to look at the
[fullscreen patch](http://cloud.github.com/downloads/typester/emacs/feature-fullscreen.patch).

== Copyright

Copyright (c) 2012 Richard Lister.
