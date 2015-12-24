Thorsten Jolitz


Table of Contents
_________________

1 navi-mode.el --- major-mode for easy buffer-navigation
.. 1.1 Copyright
.. 1.2 Licence
.. 1.3 Credits
.. 1.4 Commentary
..... 1.4.1 About navi-mode
..... 1.4.2 Installation
..... 1.4.3 Usage
..... 1.4.4 Emacs Version
.. 1.5 ChangeLog


1 navi-mode.el --- major-mode for easy buffer-navigation
========================================================

1.1 Copyright
~~~~~~~~~~~~~

  Copyright (C) 2013 Thorsten Jolitz

  Author: Thorsten Jolitz <tjolitz AT gmail DOT com>
  Maintainer: Thorsten Jolitz <tjolitz AT gmail DOT com>
  Version: 1.0 
  Created: 11th March 2013
  Keywords: occur, outlines, navigation


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

  This library is inspired by the Org-mode command `org-goto', which
  shows the documemt structure of an Org-mode file in a temporary
  buffer, and enables navigation in that buffer without changing the
  original-buffer's visibility-level, and by the authors frequent use of
  (M-x) `occur' (and the resulting *Occur* buffer) for buffer navigation
  purposes.


1.4 Commentary
~~~~~~~~~~~~~~

1.4.1 About navi-mode
---------------------

  This file implements extensions for occur-mode. You can think of a
  navi-buffer as a kind of 'remote-control' for an (adecuately)
  outline-structured original-buffer. It enables quick navigation and
  basic structure editing in the original-buffer without (necessarily)
  leaving the navi-buffer. When switching to the original-buffer and
  coming back after some modifications, the navi-buffer is always
  reverted (thus up-to-date).

  Besides the fundamental outline-heading-searches (8 outline-levels)
  and the 5 basic keyword-searches (:FUN, :VAR, :DB, :OBJ and :ALL), all
  languages can have their own set of searches and keybindings (see
  `navi-key-mappings' and `navi-keywords'). Heading-searches and
  keyword-searches can be combined, offering a vast amount of possible
  'views' at the original-buffer.


1.4.2 Installation
------------------

  Download (or clone the github-repos of) the three required libraries

   `navi-mode.el'  ([https://github.com/tj64/navi])
   `outshine.el'   ([https://github.com/tj64/outshine])
   `outorg.el'     ([https://github.com/tj64/outorg])

  and put them in a place where Emacs can find them (on the Emacs
  'load-path'). Follow the installation instructions in `outshine.el'
  and `outorg.el'.

  Install `navi-mode.el' by adding

   #+begin_src emacs-lisp
      (require 'navi-mode)
   #+end_src

  to your .emacs file.


1.4.3 Usage
-----------

  For `navi-mode' to work, the original-buffer must be
  outline-structured 'the outshine way', i.e. with the headlines being
  proper Org-mode headlines, marked and outcommented with
  `comment-region'. As an example, to generate a 3rd level
  outshine-headline in an Emacs Lisp file, write down

  ,-----------------------
  *** Third Level Header
  `-----------------------

  mark the header line, and apply `comment-region' on it:

  ,-----------------------
  ;; *** Third Level Header
  `-----------------------

  In a LaTeX file, an adecuate header will look like this:

  ,-----------------------
  % *** Third Level Header
  `-----------------------

  and in a PicoLisp file like this (always depending of the major-mode
  specific values of `comment-start', `comment-end', `comment-add' and
  `comment-padding'):

  ,-----------------------
  ## *** Third Level Header
  `-----------------------

  The second assumption is that `outline-minor-mode' is activated in the
  original-buffer and `outshine.el' loaded like described in its
  installation instructions, i.e.

  #+begin_src emacs-lisp
    (require 'outshine)
    (add-hook 'outline-minor-mode-hook 'outshine-hook-function)
  #+end_src

  When these pre-conditions are fullfilled (`outorg.el' must be loaded
  too), you can use 'M-s n' (`navi-search-and-switch') to open a
  navi-buffer and immediately switch to it. The new navi-buffer will
  show the first-level headings of the original-buffer, with point at
  the first entry.

  You can then:

  1. Show headlines (up-to) different levels:

   key      command             function-name
  ---------------------------------------------------
   1 ... 8  show levels 1 to 8  navi-generic-command

  2. Navigate up and down in the search results shown in the
     navi-buffer:

   key  command     function-name
  -----------------------------------
   p    previous    occur-prev
   n    next        occur-next
   DEL  down page   scroll-down-command
   SPC  up page     scroll-up-command

  3. Revert the navi-buffer (seldom necessary), show help for the
     user-defined keyword-searches, and quit the navi-buffer and
     switch-back to the original-buffer:

   key  command                    function-name
  ------------------------------------------------------
   g    revert buffer              navi-revert-function
   h    show help                  navi-show-help
   q    quit navi-mode and switch  navi-quit-and-switch

  4. Switch to the original-buffer and back to the navi-buffer, display
     and occurence in the original-buffer or go to the occurence:

   key      command                 function-name
  --------------------------------------------------------------------
   M-s n    launch navi-buffer      navi-search-and-switch
   M-s s    switch to other buffer  navi-switch-to-twin-buffer
   M-s M-s
   s
   d        display occurrence      occur-mode-display-occurrence
   o        goto occurrence         navi-goto-occurrence-other-window

  5. Structure editing on subtrees and visibility cycling

   key        command                         function-name
  -------------------------------------------------------------------
   TAB        cycle subtrees                  navi-cycle-subtree
   <backtab>  cycle buffer                    navi-cycle-buffer
   +          Demote Subtree                  navi-demote-subtree
   -          promote subtree                 navi-promote-subtree
   ^         move up subtree (same level)    navi-move-up-subtree
   <          move down subtree (same level)  navi-move-down-subtree

  6. Miscancellous actions on subtrees

   key  command                     function-name
  --------------------------------------------------------------------
   m    mark subtree                navi-mark-subtree-and-switch
   c    copy subtree                navi-copy-subtree-to-register-s
   k    kill subtree                navi-kill-subtree
   y    yank killed/copied subtree  navi-yank-subtree-from-register-s
   u    undo last change            navi-undo
   r    narrow to subtree           navi-narrow-to-subtree
   w    widen                       navi-widen
   l    query-replace               navi-query-replace
   i    isearch                     navi-isearch
   e    edit as org (outorg)        navi-edit-as-org

  7. Furthermore, there are five (semantically) predefined
     keyword-searches:

   key  keyword-symbol  searches for
  -------------------------------------------------
   f    :FUN            functions, macros etc.
   v    :VAR            vars, consts, customs etc.
   x    :OBJ            OOP (classes, methods etc)
   b    :DB             DB (store and select)
   a    :ALL            all


  8. And (potentially) many more user-defined keyword-searches
  (example Emacs Lisp):

   key  keyword-symbol  searches for
  -----------------------------------
   F    :defun          (defun
   V    :defvar         (defvar
   C    :defconst       (defconst
   G    :defgroup       (defgroup
   U    :defcustom      (defcustom
   A    :defadvice      (defadvice
   M    :defmacro       (defmacro
   E    :defface        (defface
   S    :defstruct      (defstruct
   L    :defclass       (defclass

  9. Headline-searches and keyword-searches can be combined, e.g.

  ,------
  C-2 f
  `------

  in an Emacs Lisp (outshine-)buffer shows all headlines up-to level 2
  as well as all function, macro and advice definitions in the
  original-buffer,

  ,------
  C-5 a
  `------

  shows all headlines up-to level 5 as well as all functions, variables,
  classes, methods, objects, and database-related definitions. The exact
  meaning of the standard keyword-searches 'f' and 'a' must be defined
  with a regexp in the customizable variable `navi-keywords' (just like
  the user-defined keyword-searches).

  When exploring a (potentially big) original buffer via navi-mode, a
  common usage pattern is the following:

  1. type e.g '2' and go to the relevant headline
  2. type 'r' and e.g. '3' in sequence to narrow buffers to the subtree
     at point and show one deeper level of headlines
  3. do your thing in the narrowed subtree
  4. type e.g. '2' and 'w' to first reduce the headline levels shown and
     then widen the buffers again.


1.4.4 Emacs Version
-------------------

  `navi-mode.el' works with [GNU Emacs 24.2.1 (x86_64-unknown-linux-gnu,
  GTK+ Version 3.6.4) of 2013-01-20 on eric]. No attempts of testing
  with older versions or other types of Emacs have been made (yet).


1.5 ChangeLog
~~~~~~~~~~~~~

   date            author(s)        version
  -------------------------------------------------
  2013-05-03 Fr    Thorsten Jolitz     1.0
  2013-03-11 Mo    Thorsten Jolitz     0.9
