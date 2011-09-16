;;; lib-requires.el --- Commands to list Emacs Lisp library dependencies.
;; 
;; Filename: lib-requires.el
;; Description: Commands to list Emacs Lisp library dependencies.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2004-2011, Drew Adams, all rights reserved.
;; Created: Thu Dec 30 12:29:29 2004
;; Version: 21.0
;; Last-Updated: Tue Jan  4 11:02:08 2011 (-0800)
;;           By: dradams
;;     Update #: 735
;; URL: http://www.emacswiki.org/cgi-bin/wiki/lib-requires.el
;; Keywords: libraries, files
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   `loadhist'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary:
;;
;;  Commands to list Emacs Lisp library dependencies.
;;
;;  This library extends some of the functionality in GNU Emacs
;;  library `load-hist.el'.
;; 
;;
;;  User options (variables) defined here:
;;
;;    `libreq-file-header'.
;; 
;;
;;  Functions defined here:
;;
;;    `libreq-flatten', `libreq-insert-lib-requires-as-comment',
;;    `libreq-remove-duplicates', `libreq-requires-list',
;;    `libreq-requires-tree'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change log:
;;
;; 2011/01/04 dadams
;;     Added autoload cookie for defgroup.
;; 2009/10/25 dadams
;;     Use library prefix "libreq-" for everything.  Thx to Jari Aalto.
;;       lib-requires-header -> libreq-file-header
;;       lib-requires-tree -> libreq-requires-tree
;;       lib-requires -> libreq-requires-list
;;       insert-lib-requires-as-comment -> libreq-insert-lib-requires-as-comment
;;       lr-flatten -> libreq-flatten
;;       lr-remove-duplicates -> libreq-remove-duplicates
;; 2009/05/25 dadams
;;     insert-lib-requires-as-comment:
;;       Bound comment-style to 'plain, to workaround Emacs 23 change.
;; 2008/02/29 dadams
;;     lib-requires-tree:
;;       Changed Emacs version test to consp test.  Thx to Lennart Borgman.
;; 2008/01/14 dadams
;;     lib-requires-tree:
;;       Update for Emacs 23: file-requires return value.  Thx to Lennart Borgman.
;; 2007/05/31 dadams
;;     insert-lib-requires-as-comment: Reuse requires local var.
;; 2006/05/22 dadams
;;     Added :group's for defcustom.
;; 2006/01/08 dadams
;;     lib-requires-tree: Force load of find-func.el, to sidestep Emacs 22 bug.
;; 2006/01/07 dadams
;;     Added: defgroup and :link.
;; 2005/10/21 dadams
;;     Added: lr-remove-duplicates.  Use it instead of cl:remove-duplicates.
;;     Renamed: flatten to lr-flatten.
;;     lib-requires(-tree):
;;       In doc string, mention error if no provide.
;;     lr-remove-duplicates: redefined.
;; 2005/10/19 dadams
;;     lib-requires-tree:
;;       More or less reverted changes from 10/18: Use require, not
;;       load-library; don't bind load-history to nil.
;;       Updated doc string to speak of feature, not library (likewise, text
;;       of lib-requires-header).
;; 2005/10/18 dadams
;;     Added: lib-requires-header.
;;     lib-requires-tree:
;;       Updated doc string to mention byte-compiled libraries.
;;       Use load-library, not require.
;;       Bind load-history to nil around it, to ensure use latest requires.
;;     insert-lib-requires-as-comment: Insert "None" instead of error if none.
;; 2005/10/03 dadams
;;     require cl.el for Emacs 22 too, for remove-duplicates.
;;
;;  Acknowledgement: Thanks to Kevin Rodgers <ihs_4664@yahoo.com> for
;;  feedback about the original version of `libreq-requires-tree'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

(require 'loadhist)

(and (< emacs-major-version 21)         ;; for Emacs 20, dolist, push, pop
     (eval-when-compile (require 'cl))) ;; for Emacs < 20, when, unless

;;;;;;;;;;;;;;;;;;;;;;;;


;;;###autoload
(defgroup Library-Dependencies nil
  "Commands to list Emacs-Lisp library dependencies."
  :prefix "libreq-"
  :group 'tools :group 'files
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
lib-requires.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/cgi-bin/wiki/DrewsElispLibraries")
  :link '(url-link :tag "Download"
          "http://www.emacswiki.org/cgi-bin/wiki/lib-requires.el")
  :link '(url-link :tag "Description"
          "http://www.emacswiki.org/cgi-bin/wiki/LibraryDependencies#LibRequires")
  :link '(emacs-commentary-link :tag "Commentary" "lib-requires")
  )

;;;###autoload
(defcustom libreq-file-header
  ";; Features that might be required by this library:\n;;\n"
  "*Header inserted by `libreq-insert-lib-requires-as-comment'."
  :type 'string
  :group 'Automatic-File-Header :group 'development :group 'programming)

;; We don't use `read-feature' (from `loadhist') to get the library
;; name interactively, because users should be able to use these
;; commands on a library (file) that has not yet been loaded.

;;;###autoload
(defun libreq-requires-tree (library &optional cumul)
  "The features `require'd by LIBRARY, as a tree.
The tree structure shows library dependencies: Each feature is
represented by its name or by a list of its name followed by the
features that it explicitly requires.

Argument LIBRARY is an Emacs-Lisp file name, or file name sans
extension.  This command loads LIBRARY before determining its
dependencies.  This means that LIBRARY must contain (provide LIBRARY).
If it does not, an error is raised.

Function `libreq-requires-tree' calls itself recursively on its
dependencies, so an attempt is made to load all of them.

Note: If a byte-compiled (`*.elc') version of a library is
available, it is loaded, in preference to the source library -
this is the standard behavior of `load-library'.  This means that
the tree of required features reflects the dependencies indicated
in the byte-compiled file, not the source file.  If the
byte-compiled file is out-of-date, so will be the result of
`libreq-requires-tree'.

A required feature that was loaded successfully is represented by a
  string that names the required feature.
A required file or feature that failed to load is represented by a
  symbol that names the required feature.

For example: Suppose that library `doremi.el' requires `ring+' and
`mwheel', and library `ring+' requires `ring'.  If `ring+' is
successfully loaded and `mwheel.el' is not, then the result is this:

  (mwheel (\"ring+\" (\"ring\")))

Argument CUMUL is used only for recursive calls, to accumulate the
required features.

See also command `libreq-requires-list'.

Note that `libreq-requires-tree' and `libreq-requires-list' are
roughly the opposite of `file-dependents' in library `loadhist'."
  (interactive (list (file-name-sans-extension
                      (file-name-nondirectory (read-file-name "Library :")))))
  (if (not library)
      nil
    (when (stringp library) (setq library (intern library)))
    (require library)
    ;; This line is temporary, to sidestep a bug in Emacs 22: `file-requires'
    ;; needs `find-library-name', so `find-func.el' must be loaded.
    (when (and (>= emacs-major-version 22) (not (fboundp 'find-library-name)))
      (require 'find-func))
    (let ((libraries ())
          (reqd-lib nil))
      (dolist (reqd-rec (file-requires (symbol-name library)) libraries)
        ;; They changed what `file-requires' returns to a cons, after Emacs 22.1.
        (setq reqd-lib (if (consp reqd-rec) (cdr reqd-rec) reqd-rec))
        (if (not (featurep reqd-lib))
            (push reqd-lib libraries)
          (let ((reqd-lib-requires-tree
                 (and (not (eq library reqd-lib))
                      (not (member reqd-lib cumul))
                      (libreq-requires-tree reqd-lib (cons library cumul)))))
            (if reqd-lib-requires-tree
                (push (cons (symbol-name reqd-lib) reqd-lib-requires-tree)
                      libraries)
              (push (symbol-name reqd-lib) libraries)))))
      (when (interactive-p) (pp-eval-expression (quote libraries)))
      libraries)))

;;;###autoload
(defun libreq-requires-list (library)
  "The libraries ultimately `require'd by LIBRARY, as a flat list.
Each library (file or feature) is represented only once, and the list
is sorted.

A library is represented as for `libreq-requires-tree': a file-name
string for a successfully loaded required library, a feature-name
symbol for an unsuccessfully loaded required feature.

LIBRARY must contain (provide LIBRARY); otherwise, an error is raised.

Note that `libreq-requires-tree' and `libreq-requires-list' are
essentially the opposite of `file-dependents' in library `loadhist'."
  (interactive (list (file-name-sans-extension
                      (file-name-nondirectory (read-file-name "Library :")))))
  (let ((libraries
         (sort (libreq-remove-duplicates
                (libreq-flatten (libreq-requires-tree library)))
               #'string-lessp)))
    (when (interactive-p) (pp-eval-expression (quote libraries)))
    libraries))

;;;###autoload
(defun libreq-insert-lib-requires-as-comment (library)
  "Insert a comment listing all libraries ultimately required by LIBRARY.
See also `libreq-requires-list' and `libreq-requires-tree'."
  (interactive (list (file-name-sans-extension
                      (file-name-nondirectory (read-file-name "Library:")))))
  (let ((requires       (libreq-requires-list library))
        (comment-style  'plain))
    (save-excursion
      (beginning-of-line)
      (insert libreq-file-header)
      (if (not requires)
          (insert ";;   None\n;;\n")
        (let ((beg (point))
              (fill-column (- fill-column 4)))
          (mapc (lambda (feat) (insert (format "`%s', " feat))) requires)
          (backward-delete-char 2)
          (insert ".\n")
          (let ((left-margin 2)) (fill-region-as-paragraph beg (point)))
          (comment-region beg (point) 2))
        (insert ";;\n")))))


;;; Helper Functions ;;;;;;;;;

(defun libreq-flatten (list)            ; From `misc-fns.el'.
  "Flatten LIST, returning a list with the atoms in LIST at any level.
Also works for a consp whose cdr is non-nil."
  (cond ((null list) nil)
        ((atom list) list)
        (t
         (let ((old list)
               (new ())
               item)
           (while old
             (if (atom old)             ; From consp with non-nil cdr.
                 (setq item old
                       old nil)
               (setq item (car old)
                     old (cdr old)))
             ;; Make item atomic.
             (while (consp item)
               (if (cdr item)
                   (setq old (cons (cdr item) old)))
               (setq item (car item)))
             (setq new (cons item new)))
           (reverse new)))))

;; Borrowed from `ps-print.el'
(defun libreq-remove-duplicates (list)
  "Copy of LIST with duplicate elements removed.  Tested with `equal'."
  (let ((tail list)
        new)
    (while tail
      (unless (member (car tail) new) (push (car tail) new))
      (pop tail))
    (nreverse new)))

;;;;;;;;;;;;;;;;;;;;;;

(provide 'lib-requires)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; lib-requires.el ends here
