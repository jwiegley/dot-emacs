nov.el
======

.. image:: https://raw.github.com/wasamasa/nov.el/master/img/novels.gif

About
-----

``nov.el`` provides a major mode for reading EPUB documents.

Features:

- Basic navigation (jump to TOC, previous/next chapter)
- Remembering and restoring the last read position
- Jump to next chapter when scrolling beyond end
- Renders EPUB2 (.ncx) and EPUB3 (<nav>) TOCs
- Hyperlinks to internal and external targets
- Supports textual and image documents
- View source of document files
- Metadata display
- Image rescaling

Screenshot
----------

.. image:: https://raw.github.com/wasamasa/nov.el/master/img/scrot.png

Installation
------------

Set up the `MELPA <https://melpa.org/>`_ or `MELPA Stable
<https://stable.melpa.org/>`_ repository if you haven't already and
install with ``M-x package-install RET nov RET``.

Setup
-----

Make sure you have an ``unzip`` executable on ``PATH``, otherwise the
extraction of EPUB files will fail.  If you for some reason have
``unzip`` in a non-standard location, customize ``nov-unzip-program``
to its path.  You'll also need an Emacs compiled with ``libxml2``
support, otherwise rendering will fail.

Put the following in your init file:

.. code:: elisp

    (add-to-list 'auto-mode-alist '("\\.epub\\'" . nov-mode))

Customization
-------------

While the defaults make for an acceptable reading experience, it can
be improved with any of the following changes:

Default font
............

To change the default font, use ``M-x customize-face RET
variable-pitch``, pick a different family, save and apply.  If you
dislike globally customizing that face, add the following to your init
file:

.. code:: elisp

    (defun my-nov-font-setup ()
      (face-remap-add-relative 'variable-pitch :family "Liberation Serif"
                                               :height 1.0))
    (add-hook 'nov-mode-hook 'my-nov-font-setup)

To completely disable the variable pitch font, customize
``nov-variable-pitch`` to ``nil``.  Text will be displayed with the
default face instead which should be using a monospace font.

Text width
..........

By default text is filled by the window width.  You can customize
``nov-text-width`` to a number of columns to change that:

.. code:: elisp

    (setq nov-text-width 80)

It's also possible to set it to a huge number to inhibit text filling,
this can be used in combination with ``visual-line-mode`` and packages
such as ``visual-fill-column`` to implement more flexible filling:

.. code:: elisp

    (setq nov-text-width most-positive-fixnum)
    (setq visual-fill-column-center-text t)
    (add-hook 'nov-mode-hook 'visual-line-mode)
    (add-hook 'nov-mode-hook 'visual-fill-column-mode)

Rendering
.........

In case you're not happy with the rendering at all, you can either use
``nov-pre-html-render-hook`` and ``nov-post-html-render-hook`` to
adjust the HTML before and after rendering or use your own rendering
function by customizing ``nov-render-html-function`` to one that
replaces HTML in a buffer with something nicer than the default
output.

Here's an advanced example of text justification with the `justify-kp
<https://github.com/Fuco1/justify-kp>`_ package:

.. code:: elisp

    (require 'justify-kp)
    (setq nov-text-width most-positive-fixnum)

    (defun my-nov-window-configuration-change-hook ()
      (my-nov-post-html-render-hook)
      (remove-hook 'window-configuration-change-hook
                   'my-nov-window-configuration-change-hook
                   t))

    (defun my-nov-post-html-render-hook ()
      (if (get-buffer-window)
          (let ((max-width (pj-line-width))
                buffer-read-only)
            (save-excursion
              (goto-char (point-min))
              (while (not (eobp))
                (when (not (looking-at "^[[:space:]]*$"))
                  (goto-char (line-end-position))
                  (when (> (shr-pixel-column) max-width)
                    (goto-char (line-beginning-position))
                    (pj-justify)))
                (forward-line 1))))
        (add-hook 'window-configuration-change-hook
                  'my-nov-window-configuration-change-hook
                  nil t)))

    (add-hook 'nov-post-html-render-hook 'my-nov-post-html-render-hook)

This customization yields the following look:

.. image:: https://raw.github.com/wasamasa/nov.el/master/img/justify-kp.png

Usage
-----

Open the EPUB file with ``C-x C-f ~/novels/novel.epub``, scroll with
``SPC`` and switch chapters with ``n`` and ``p``.  More keybinds can
be looked up with ``F1 m``.

Contributing
------------

See `CONTRIBUTING.rst
<https://github.com/wasamasa/nov.el/blob/master/CONTRIBUTING.rst>`_.

Alternatives
------------

The first one I've heard of is `epubmode.el
<https://www.emacswiki.org/emacs/epubmode.el>`_ which is, well, see
for yourself.  You might find `ereader
<https://github.com/bddean/emacs-ereader>`_ more useful, especially if
you're after Org integration and annotation support.
