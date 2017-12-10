[![MELPA](http://melpa.org/packages/bm-badge.svg)](http://melpa.org/#/bm)
[![MELPA](http://stable.melpa.org/packages/bm-badge.svg)](http://melpa.org/#/bm)

Visible bookmarks in buffer for GNU Emacs 22.x / 23.x / 24.x / 25.x (XEmacs 21.x).
=====================

This package provides visible, buffer local, bookmarks and the ability
to jump forward and backward to the next bookmark.

It was created because I missed the bookmarks from M$ Visual Studio in
GNU Emacs. I think they provide an easy way to navigate in a buffer.


Features:
---------
* Auto remove bookmark after jump to it by `bm-next` or `bm-previous`:
* Cycle through bookmarks in all open buffers in LIFO order
* Toggle bookmarks. Jump to next/previous bookmark.
* Setting bookmarks based on a regexp. (Useful when searching logfiles.)
* Mouse navigation.
* Annotate bookmarks.
* Different wrapping modes.
* Different bookmarks styles, line-only, fringe-only or both.
* Persistent bookmarks (buffer local), also in non-file buffers (*info*) and indirect buffers.
* List bookmarks (in all buffers) in a separate buffer.
* Cycle through bookmarks in all open buffers.


Installation:
-------------

To use bm.el, put it in your load-path and add the following to your .emacs

    (require 'bm)

or

    (autoload 'bm-toggle   "bm" "Toggle bookmark in current buffer." t)
    (autoload 'bm-next     "bm" "Goto bookmark."                     t)
    (autoload 'bm-previous "bm" "Goto previous bookmark."            t)


Configuration:
--------------

To make it easier to use, assign the commands to some keys.

M$ Visual Studio key setup.

    (global-set-key (kbd "<C-f2>") 'bm-toggle)
    (global-set-key (kbd "<f2>")   'bm-next)
    (global-set-key (kbd "<S-f2>") 'bm-previous)

Click on fringe to toggle bookmarks, and use mouse wheel to move between them.

    (global-set-key (kbd "<left-fringe> <mouse-5>") 'bm-next-mouse)
    (global-set-key (kbd "<left-fringe> <mouse-4>") 'bm-previous-mouse)
    (global-set-key (kbd "<left-fringe> <mouse-1>") 'bm-toggle-mouse)

If you would like the markers on the right fringe instead of the left, add the following line:

    (setq bm-marker 'bm-marker-right)

If you would like to cycle bookmark in LIFO order, add the following line:

    (setq bm-in-lifo-order t)

If you would like to cycle through bookmarks in *all* open buffers, add the following line:

    (setq bm-cycle-all-buffers t)

If you would like to remove bookmark after jump to it by `bm-next` or `bm-previous`:

    (setq temporary-bookmark-p t)

or if you want use this feature in your library:

    (bm-bookmark-add nil nil t)


Configuring bm.el with use-package:
---------------------------------
Configuring bm.el with [use-package](https://github.com/jwiegley/use-package)

    (use-package bm
             :ensure t
             :demand t

             :init
             ;; restore on load (even before you require bm)
             (setq bm-restore-repository-on-load t)


             :config
             ;; Allow cross-buffer 'next'
             (setq bm-cycle-all-buffers t)

             ;; where to store persistant files
             (setq bm-repository-file "~/.emacs.d/bm-repository")

             ;; save bookmarks
             (setq-default bm-buffer-persistence t)

             ;; Loading the repository from file when on start up.
             (add-hook' after-init-hook 'bm-repository-load)

             ;; Restoring bookmarks when on file find.
             (add-hook 'find-file-hooks 'bm-buffer-restore)

             ;; Saving bookmarks
             (add-hook 'kill-buffer-hook #'bm-buffer-save)

             ;; Saving the repository to file when on exit.
             ;; kill-buffer-hook is not called when Emacs is killed, so we
             ;; must save all bookmarks first.
             (add-hook 'kill-emacs-hook #'(lambda nil
                                              (bm-buffer-save-all)
                                              (bm-repository-save)))

             ;; The `after-save-hook' is not necessary to use to achieve persistence,
             ;; but it makes the bookmark data in repository more in sync with the file
             ;; state.
             (add-hook 'after-save-hook #'bm-buffer-save)

             ;; Restoring bookmarks
             (add-hook 'find-file-hooks   #'bm-buffer-restore)
             (add-hook 'after-revert-hook #'bm-buffer-restore)

             ;; The `after-revert-hook' is not necessary to use to achieve persistence,
             ;; but it makes the bookmark data in repository more in sync with the file
             ;; state. This hook might cause trouble when using packages
             ;; that automatically reverts the buffer (like vc after a check-in).
             ;; This can easily be avoided if the package provides a hook that is
             ;; called before the buffer is reverted (like `vc-before-checkin-hook').
             ;; Then new bookmarks can be saved before the buffer is reverted.
             ;; Make sure bookmarks is saved before check-in (and revert-buffer)
             (add-hook 'vc-before-checkin-hook #'bm-buffer-save)


             :bind (("<f2>" . bm-next)
                    ("S-<f2>" . bm-previous)
                    ("C-<f2>" . bm-toggle))
             )



Reviews and comments:
--------------------

* [A Visual Bookmarks package for Emacs](http://emacsworld.blogspot.com/2008/09/visual-bookmarks-package-for-emacs.html)
* [Bookmark Mania](http://www.emacsblog.org/2007/03/22/bookmark-mania/)
* [EmacsWiki: VisibleBookmarks](http://www.emacswiki.org/cgi-bin/wiki/VisibleBookmarks)
* [A couple of useful Emacs modes](http://codeblog.bsdninjas.co.uk/index.php?/archives/136-A-couple-of-useful-Emacs-modes.html)
* [Part of Debian package: emacs-goodies-el](http://packages.debian.org/unstable/editors/emacs-goodies-el)
* [A solution to the question 'How to highlight a particular line in emacs?' on StackOverflow](http://stackoverflow.com/questions/14454219/how-to-highlight-a-particular-line-in-emacs)
* gnu.emacs.sources
    * [Original posting of bm.el (31 Jan 2001)](http://groups.google.com/group/gnu.emacs.sources/browse_thread/thread/2ccc0ece443a81b6/d4b97c612190d0d6?fwc=1)
    * [Posting of first version with persistence. (12 Nov 2003)](http://groups.google.com/group/gnu.emacs.sources/browse_thread/thread/8f0ec0f1eff89764/cd24c441f9bc6bef?lnk=gst#cd24c441f9bc6bef)
