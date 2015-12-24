Thorsten Jolitz


Table of Contents
_________________

1 outorg.el --- Org-style comment editing
.. 1.1 Copyright
.. 1.2 Licence
.. 1.3 Credits
.. 1.4 Commentary
..... 1.4.1 About outorg
..... 1.4.2 Installation
..... 1.4.3 Bugs and Shortcomings
..... 1.4.4 Emacs Version
.. 1.5 ChangeLog


1 outorg.el --- Org-style comment editing
=========================================

1.1 Copyright
~~~~~~~~~~~~~

  Copyright (C) 2013 Thorsten Jolitz

  Author: Thorsten Jolitz <tjolitz AT gmail DOT com>
  Maintainer: Thorsten Jolitz <tjolitz AT gmail DOT com>
  Version: 1.0
  Created: 11th February 2013
  Keywords: outlines, org-mode, editing


1.2 Licence
~~~~~~~~~~~

  This file is NOT (yet) part of GNU Emacs.

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or (at
  your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
  General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program. If not, see [http://www.gnu.org/licenses/].


1.3 Credits
~~~~~~~~~~~

  This library is inspired by the way source-blocks can be edited in
  temporary edit files in Org-mode (see
  [http://orgmode.org/worg/org-contrib/babel/]).


1.4 Commentary
~~~~~~~~~~~~~~

1.4.1 About outorg
------------------

  `outorg' is like "reverse Org-Babel": editing of comment-sections from
  source code files in temporary Org-mode buffers instead of editing of
  Org-mode source-blocks in temporary source-code buffers.

  It should be used together with `outline-minor-mode' and
  `outshine.el'. Keep in mind, that `outorg' only works with
  outshine-style headlines like those produced by calling
  `comment-region' on Org-mode style headlines in a source-code buffer.
  Take this file as an example for suitable outline headlines in an
  Emacs Lisp buffer. In other major-modes, the `comment-start' character
  ';' of Emacs Lisp would be replaced by that of the respective
  major-mode, e.g. '#' in PicoLisp mode or '%' in LaTeX mode.

  `outorgs' main command is

  ,---------------------------
  C-c ' (outorg-edit-as-org)
  `---------------------------

  or, depending on the outline-mode prefix

  ,---------------------------
  M-# M-# (outorg-edit-as-org)
  `---------------------------

  used in source-code buffers where `outline-minor-mode' is activated
  with `outshine' extensions. The Org-mode edit-buffer popped up by this
  command has `outorg-edit-mode' activated, a minor-mode with only 2
  commands:

  ,----------------------------------------
  M-# (outorg-copy-edits-and-exit)
  C-x C-s (outorg-save-edits-to-tmp-file)
  `----------------------------------------

  If you want to insert Org-mode source-code or example blocks in
  comment-sections, simply outcomment them in the outorg-edit buffer
  before calling `outorg-copy-edits-and-exit'.


1.4.2 Installation
------------------

  Insert

  #+begin_src emacs-lisp
   (require 'outorg)
  #+end_src

  in your .emacs.

1.4.3 Bugs and Shortcomings
---------------------------

  `outorg' is line-based, it only works with 'one-line' comments, i.e.
  with comment-sections like those produced by `comment-region' (a
  command that comments or uncomments each line in the region). Those
  special multi-line comments found in many programming languages are
  not recognized and lead to undefined behaviour.


1.4.4 Emacs Version
-------------------

  `outorg.el' works with [GNU Emacs 24.2.1 (x86_64-unknown-linux-gnu,
  GTK+ Version 3.6.4) of 2013-01-20 on eric]. No attempts of testing
  with older versions or other types of Emacs have been made (yet).


1.5 ChangeLog
~~~~~~~~~~~~~

   date              author(s)        version 
  ----------------------------------------------
   2013-05-03 Fr   Thorsten Jolitz      1.0
   2013-02-11 Mo   Thorsten Jolitz      0.9 
