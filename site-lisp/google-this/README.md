google-this [![Build Status](https://secure.travis-ci.org/Malabarba/emacs-google-this.png?branch=master)](http://travis-ci.org/Malabarba/emacs-google-this) [![Melpa](http://melpa.org/packages/google-this-badge.svg)](http://melpa.org/#/google-this) [![Melpa-stable](http://stable.melpa.org/packages/google-this-badge.svg)](http://melpa.org/#/google-this) [Gratipay](https://gratipay.com/Malabarba/)
------------------------

**A set of emacs functions and bindings to google under point.**

*google-this.el* is a package that provides a set of functions and keybindings for
launching google searches from within emacs.

The main function is `google-this` (bound to `C-c / g`). It does a
google search using the currently selected region, or the expression
under point. All functions are bound under `C-c /` prefix, in order to
comply with emacs' standards. To see all keybindings type `C-c / C-h`.

If you don't like this keybind, just reassign the
`google-this-mode-submap` variable.
My personal preference is `C-x g`:

       (global-set-key (kbd "C-x g") 'google-this-mode-submap)
       
To start a blank search, do `google-search` (`C-c / RET`). If you want
more control of what "under point" means for the `google-this`
command, there are the `google-word`, `google-symbol`, `google-line`
and `google-region` functions, bound as `w`, `s`, `l` and `SPC`,
respectively.
 
If a prefix argument is given to any of the functions, the search is
wrapped in quotes. (see `google-wrap-in-quotes`).

There is also a `google-error` (`C-c / e`) function. It checks the
current error in the compilation buffer, tries to do some parsing (to
remove file name, line number, etc), and googles it. It's still
experimental, and has only really been tested with gcc error reports.

INSTALLATION
===

Install `google-this` from Melpa, then activate it:

	(google-this-mode 1)

