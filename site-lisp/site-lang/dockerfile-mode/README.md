dockerfile-mode
===============
Known to work with Emacs 24 and later

A Dockerfile mode for emacs

``` emacs-lisp
(add-to-list 'load-path "/your/path/to/dockerfile-mode/")
(require 'dockerfile-mode)
(add-to-list 'auto-mode-alist '("Dockerfile\\'" . dockerfile-mode))
```

Adds syntax highlighting as well as the ability to build the image
directly (C-c C-b) from the buffer.

You can specify the image name in the file itself by adding a line like this
at the top of your Dockerfile.

``` emacs-lisp
## -*- docker-image-name: "your-image-name-here" -*-
```

If you don't, you'll be prompted for an image name each time you build.
