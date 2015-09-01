Visible bookmarks in buffer for GNU Emacs 22.x / 23.x (XEmacs 21.x).
=====================

This package provides visible, buffer local, bookmarks and the ability to jump forward and backward to the next bookmark.

It was created because I missed the bookmarks from M$ Visual Studio in GNU Emacs. I think they provide an easy way to navigate in a buffer.

Features:
---------

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

If you would like the markers on the right fringe instead of the left, add the following to line:

    (setq bm-marker 'bm-marker-right)

Reviews and comments:
--------------------

* [A Visual Bookmarks package for Emacs](http://emacsworld.blogspot.com/2008/09/visual-bookmarks-package-for-emacs.html)
* [Bookmark Mania](http://www.emacsblog.org/2007/03/22/bookmark-mania/)
* [EmacsWiki: VisibleBookmarks](http://www.emacswiki.org/cgi-bin/wiki/VisibleBookmarks)
* [A couple of useful Emacs modes](http://codeblog.bsdninjas.co.uk/index.php?/archives/136-A-couple-of-useful-Emacs-modes.html)
* [Part of Debian package: emacs-goodies-el](http://packages.debian.org/unstable/editors/emacs-goodies-el)
* gnu.emacs.sources
    * [Original posting of bm.el (31 Jan 2001)](http://groups.google.com/group/gnu.emacs.sources/browse_thread/thread/2ccc0ece443a81b6/d4b97c612190d0d6?fwc=1)
    * [Posting of first version with persistence. (12 Nov 2003)](http://groups.google.com/group/gnu.emacs.sources/browse_thread/thread/8f0ec0f1eff89764/cd24c441f9bc6bef?lnk=gst#cd24c441f9bc6bef)
