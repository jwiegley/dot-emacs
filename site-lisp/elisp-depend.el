;;; elisp-depend.el --- Parse depend libraries of elisp file.

;; Filename: elisp-depend.el
;; Description: Parse depends library of elisp file.
;; Authors: Andy Stewart lazycat.manatee@gmail.com
;; Tom Breton (Tehom) tehom@panix.com
;; "Michael Heerdegen" <michael_heerdegen@web.de>
;; Maintainer: Tom Breton (Tehom) tehom@panix.com
;; Copyright (C) 2009, Andy Stewart, all rights reserved.
;; Copyright (C) 2010-2012, Tom Breton, all rights reserved.
;; Created: 2009-01-11 19:40:45
;; Id: $Id$
;; Version: 1.0.2
;; Last-Updated: 26 Apr, 2012
;;           By: Tom Breton
;; URL: http://www.emacswiki.org/emacs/download/elisp-depend.el
;; Keywords: elisp-depend
;; Compatibility: GNU Emacs 20 ~ GNU Emacs 23
;;
;; Features that might be required by this library:
;;
;;
;;

;;; This file is NOT part of GNU Emacs

;;; License
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; Parse depend libraries of elisp file.
;;
;; This packages is parse current elisp file and get
;; depend libraries that need.
;;
;; Default, it will use function `symbol-file' to get
;; depend file with current symbol.
;; And then use `featurep' to test this file whether
;; write `provide' sentences for feature reference.
;; If `featurep' return t, generate depend information
;; as "(require 'foo)" format.
;; If `featurep' return nil, generate depend
;; as "(autoload 'foo "FooFile")" format.
;;
;; This packages will always return depend information as `autoload'
;; format if a feature not write `provide' information in source code.
;;
;; Below are commands you can use:
;;
;; `elisp-depend-insert-require'        insert depends code.
;; `elisp-depend-insert-comment'        insert depends comment.
;;

;;; Installation:
;;
;; Put elisp-depend.el to your load-path.
;; The load-path is usually ~/elisp/.
;; It's set in your ~/.emacs like this:
;; (add-to-list 'load-path (expand-file-name "~/elisp"))
;;
;; And the following to your ~/.emacs startup file.
;;
;; (require 'elisp-depend)
;;
;; NOTE:
;;
;; Default, if your Emacs is install at "/usr/share/emacs/",
;; You can ignore below setup.
;;
;; Otherwise you need setup your Emacs directory with
;; option `elisp-depend-directory-list', like below:
;;
;; (setq elisp-depend-directory-list '("YourEmacsDirectory"))
;;

;;; Customize:
;;
;; `elisp-depend-directory-list' the install directory of emacs.
;; Or you can add others directory that you want filter.
;;
;; All of the above can customize by:
;;      M-x customize-group RET elisp-depend RET
;;

;;; Change log:
;; 2012/04/20
;;      * Switched to `read' instead of parsing the file mnaually.

;; 2010/05/10
;;      * Bugfix: Fixed error if file didn't start with a comment.
;; 2010/05/08
;;      * Added require for `thingatpt'
;;      * Now slash-style module names are treated correctly.
;;
;; 2009/02/11
;;      * Add new option `built-in' to function `elisp-depend-map'
;;        for debug.
;;
;; 2009/01/18
;;      * Complete all check work.
;;        Now can generate exact depend information.
;;      * Modified some code to compatibility Emacs 20.
;;        Thanks "Drew Adams" advice.
;;      * Fix doc.
;;
;; 2009/01/17
;;      * Don't include user init file in depend information,
;;        filter by variable `user-init-file'.
;;
;; 2009/01/11
;;      * First released.
;;

;;; Acknowledgements:
;;
;;      Drew Adams      <drew.adams@oracle.com>
;;              For advice for compatibility Emacs 20.
;;

;;; TODO
;;
;;      Fix local-variable problem:
;;          If the some local-variable (such as lambda sentence)
;;          have same name with function, will got unnecessary depend
;;          information.
;;

;;; Require
;; (None)

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Customize ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;###autoload
(defgroup elisp-depend nil
  "Parse depend library of elisp file."
  :group 'tools)

;;;###autoload
(defcustom elisp-depend-directory-list
  '("/usr/share/emacs/")
  "List of directories that search should ignore."
  :type 'list
  :group 'elisp-depend)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Interactive Functions. ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defun elisp-depend-print-dependencies (&optional built-in)
  "Print library dependencies of the current buffer.
With prefix argument, don't include built-in libraries.
Every library that has a parent directory in
`elisp-depend-directory-list' is considered built-in."
  (interactive "P")
  (let ((dep-table
         (mapconcat (lambda (dep)
                      (format "%s: %s"
                              (propertize (elisp-depend-filename (car dep)) 'face 'match)
                              (mapconcat #'symbol-name (delete-dups (cdr dep)) ", ")))
                    (elisp-depend-map nil built-in) "\n")))
    (switch-to-buffer (get-buffer-create "*Dependencies*"))
    (setq truncate-lines nil
          buffer-read-only nil)
    (erase-buffer)                         ;with != 0
    (insert dep-table)
    (goto-char (point-min))
    (view-mode +1)
    (setq view-exit-action
          (lambda (buffer)
            ;; Use `with-current-buffer' to make sure that `bury-buffer'
            ;; also removes BUFFER from the selected window.
            (with-current-buffer buffer
              (bury-buffer))))))

;;;###autoload
(defun elisp-depend-insert-require ()
  "Insert a block of (require sym) or 'autoload statements into an elisp file."
  (interactive)
  (let ((deps (elisp-depend-map))
        library-name)
    (if deps
        (dolist (element deps)
          (setq library-name (elisp-depend-filename (car element)))
          ;; Insert (require 'foo) if featurep return t.
          (if (featurep (intern library-name))
              (insert (format "(require '%s)\n" library-name))
            ;; Otherwise autoload function in `library-name'.
            (dolist (symbol (cdr element))
              (if (functionp symbol)
                  (insert (format "(autoload '%s \"%s\")\n" symbol library-name))))))
      (message "Doesn't need any extra libraries."))))

;;;###autoload
(defun elisp-depend-insert-comment ()
  "Insert a block of `sym' statements into an elisp file."
  (interactive)
  (let ((deps (elisp-depend-map)))
    (if deps
        (progn
          (insert ";; ")
          (dolist (element deps)
            (insert (format "`%s' " (elisp-depend-filename (car element))))))
      (message "Doesn't need any extra libraries."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Utilities Functions ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun elisp-depend-read-tree (&optional buffer)
   "Return the tree given by reading the buffer as elisp.
The top level is presented as a list, as if the buffer contents had been
\(list CONTENTS...\)"
   (let* 
      ((tree '()))
      (with-current-buffer (or buffer (current-buffer))
	 (save-excursion
	    (save-restriction
	       (widen)
	       (goto-char (point-min))
	       ;; Loop is deliberately terminated by a read error at EOF.
	       (condition-case nil
		  (while t
		     (setq tree (cons (read (current-buffer)) tree)))
		  (error tree)))))))

;;;; Getting the symbols from a sexp list

;; Borrowed from format
(defun elisp-depend-proper-list-p (list)
   "Return t if LIST is a proper list.
A proper list is a list ending with a nil cdr, not with an atom "
   (when (listp list)
      (while (consp list)
	 (setq list (cdr list)))
      (null list)))

;; Exploration helpers.  These generally call
;; `elisp-depend-sexp->sym-list', implicitly recursing.  They do not
;; attempt to skip symbols that are bound by arglists, let forms, etc.

(defun elisp-depend-get-syms-recurse (sexp n)
   "Gets syms from a form that ignores the first N arguments and
recurses on the rest."
   (if (elisp-depend-proper-list-p sexp)
      (apply #'append
	 (mapcar #'elisp-depend-sexp->sym-list (nthcdr n sexp)))
      ;; If it's a dotted list, complain.
      (error "Code contains a dotted list not backquoted: %s" sexp)))

(defun elisp-depend-defun-form->sym-list (sexp)
   "Gets syms from a definition form like \(DEF NAME ARGS BODY...\).

We don't try to understand argument lists or skip variables that
are mentioned in them."
   (elisp-depend-get-syms-recurse sexp 3))

(defun elisp-depend-defvar-form->sym-list (sexp)
   "Gets syms from a definition form like \(DEF NAME BODY OPTIONS...\)."
   (elisp-depend-sexp->sym-list (nth 2 sexp)))

(defun elisp-depend-let-form->sym-list (sexp)
   "Gets syms from a let form like \(LET ((NAME BODY)...) BODY...\)."
   
   (let*
      ((binding-forms (cadr sexp)))

      (append
	 (apply #'append
	    (mapcar 
	       #'(lambda (b-form)
		    (if (consp b-form)
		       (elisp-depend-sexp->sym-list (cadr b-form))
		       '()))
	       binding-forms))
	 (elisp-depend-get-syms-recurse (cddr sexp) 0))))

(defconst elisp-depend-special-explorers 
   '(
       (quote ignore)
       (\` 
	  (lambda (sexp)
	     (elisp-depend-sexp->sym-list (macroexpand sexp))))
       
       (provide ignore)
       (require ignore)
       
       (defun elisp-depend-defun-form->sym-list)
       (defmacro elisp-depend-defun-form->sym-list)
       (defvar elisp-depend-defvar-form->sym-list)
       (defconst elisp-depend-defvar-form->sym-list)
       (lambda (lambda (sexp)
		  (elisp-depend-get-syms-recurse sexp 2)))
      
       (let elisp-depend-let-form->sym-list)
       (let* elisp-depend-let-form->sym-list)
       )
   "Alist of symbols to expand specially, mapping from symbol to
explore function.  Explore functions take one argument, a sexp, and
return a list of symbols." )

(defun elisp-depend-sexp->sym-list (sexp)
   "Return all the referenced symbols from the sexp, as a list.

The result omits `defun' and similar built-ins.  The result may
contain duplicates.  It does not distinguish symbols called as
functions from variables.  

This function does not expand macros."

   ;; Don't want to drag `cl' in, so it's a tree of `if's.
   (if
      (symbolp sexp)
      (list `(var ,sexp))
      (if (consp sexp)
	 (let
	    ((functor (car sexp)))
	    (if
	       (not (symbolp functor))
	       ;; Functor is a lambda or similar.
	       (elisp-depend-get-syms-recurse sexp 0)
	       (let*
		  ((explorer
		      (assoc functor elisp-depend-special-explorers)))
		  (if explorer
		     (funcall (cadr explorer) sexp)
		     (cons 
			`(func ,functor)
			(elisp-depend-get-syms-recurse sexp 1))))))
	 ;; It's neither symbol nor form, so there are no symbols in it.
	 '())))


;; Translate symbols to requirements

(defun elisp-depend-sym-list->dependencies (sym-list current-filename built-in see-vars)
   ""

   (let
      ((symbol-seen '())
	 (dependencies '()))
      ;; Poor-man's dolist
      (while sym-list
	 (let* 
	    (  (el (car sym-list))
	       (type (car el))
	       (symbol (cadr el))
	       ;; Poor-man's and-let*.  These get set and checked below.
	       filepath filename)
	    (if
	       (and
		  ;; Haven't already treated it
		  (not (memq symbol symbol-seen))
		  ;; It's a function, or we're allowing vars.
		  (or see-vars (eq type 'func))
		  ;; and it's not a C function.
		  (not (subrp symbol))
		  ;; Get the file that defines this symbol
		  (setq filepath (symbol-file symbol))
		  ;; Get file name without extension.
		  (setq filename (elisp-depend-filename filepath))
		  ;; It's not defined in the buffer we're exploring.
		  (not (string= filename current-filename))
		  ;; It's not built in or we're allowing built-ins
		  (or built-in
		     (not
			(elisp-depend-match-built-in-library
			   filepath))))
	       (let
		  ((dentry (assoc filepath dependencies)))
		  (if dentry
		     (setcdr dentry (cons symbol (cdr dentry)))
		     (setq dependencies 
			(cons 
			   (cons filepath (list symbol)) 
			   dependencies))))))
	 (setq sym-list (cdr sym-list)))
      ;;
      dependencies))

(defun elisp-depend-map (&optional buffer built-in)
  "Return depend map with BUFFER.
If BUFFER is nil, use current buffer.
If BUILT-IN is non-nil, return built-in library information.
Return depend map as format: (filepath symbol-A symbol-B symbol-C)."
   (let* 
      (
	 (tree (elisp-depend-read-tree buffer))
	 (sym-list (elisp-depend-get-syms-recurse tree 0))
	 (dependencies
	    (elisp-depend-sym-list->dependencies
	       sym-list
	       (elisp-depend-filename (buffer-file-name buffer))
	       built-in 
	       nil)))
      
      dependencies))


(defun elisp-depend-get-load-history-line (path-sans-ext extension)
   "Return line in load-history correspoding to PATH-SANS-EXT with
   EXTENSION.
Return nil if there is none."
   (assoc 
      (concat path-sans-ext extension) 
      load-history))

(defun elisp-depend-filename (fullpath)
  "Return filename without extension and path.
FULLPATH is the full path of file."
   
   (let*
      (  
	 (true-path-sans-ext
	    (file-name-sans-extension
	       (file-truename fullpath)))
	 (file-history
	    (cdr
	       (or
		  (elisp-depend-get-load-history-line 
		     true-path-sans-ext ".elc")
		  (elisp-depend-get-load-history-line 
		     true-path-sans-ext ".el"))))
	 (lib-name
	    (when file-history
	       (cdr
		  (assq 'provide file-history)))))

      (if lib-name
	 (symbol-name lib-name)
	 ;;Fallback: Just use the base filename
	 (file-name-sans-extension 
	    (file-name-nondirectory fullpath)))))

(defun elisp-depend-match-built-in-library (fullpath)
  "Return t if FULLPATH match directory with built-in library."
  (if (or (string-equal (format "%s.el" user-init-file) fullpath)
          (string-equal (format "%s.elc" user-init-file) fullpath))
      t                                 ;return t if match `user-init-file'.
    (catch 'match
      (dolist (directory elisp-depend-directory-list)
        (if (string-match (expand-file-name directory) fullpath)
            (throw 'match t)))
      nil)))

(provide 'elisp-depend)

;;; elisp-depend.el ends here

;;; LocalWords:  YourEmacsDirectory filepath dentry deps sym featurep fullpath
;;; LocalWords:  FooFile elc subr
