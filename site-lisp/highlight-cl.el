;;; highlight-cl.el --- Highlighting `cl' functions.

;; Copyright (C) 2009  Taiki SUGAWARA

;; Author: Taiki SUGAWARA <buzz.taiki@gmail.com>
;; Keywords: faces
;; Version: 1.0.2
;; Time-stamp: <2009-10-12 17:27:45 UTC taiki>
;; URL: http://www.emacswiki.org/emacs/highlight-cl.el

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;; This package highlighting `cl' functions.
;;
;; Please byte compile this package on batch mode instead of runtime
;; byte compiling. Because this package using load state for classify
;; functions to `cl only' and `cl and other package'.

;;; Installation:
;; Run followings to byte compile this package:
;;
;;   $ emacs -Q -batch -f batch-byte-compile highlight-cl.el
;;
;; Put followings to your .emacs:
;;
;;   (require 'highlight-cl)
;;   (add-hook 'emacs-lisp-mode-hook 'highlight-cl-add-font-lock-keywords)
;;   (add-hook 'lisp-interaction-mode-hook 'highlight-cl-add-font-lock-keywords)

;;; History:
;; 2009-04-05 taiki
;;   * version 1.0.2
;;   * add highlight-cl-macro face.
;; 
;; 2009-04-03 taiki
;;   * initial release.


(defgroup highlight-cl nil
  "Highlighting `cl' functions."
  :group 'faces)

(defface highlight-cl
  '((t (:underline "red")))
  "Face for highlighting `cl' functions."
  :group 'highlight-cl)
(defface highlight-cl-macro
  '((t (:underline "steel blue")))
  "Face for highlighting `cl' macros."
  :group 'highlight-cl)
(defface highlight-cl-and-other
  '((t :underline t))
  "Face for highlighting `cl' functions but also defined other packages."
  :group 'highlight-cl)

(eval-and-compile
  (defun highlight-cl-cl-function-p (sym)
    "Return non-nil If SYM is defined in cl-* package."
    (and (fboundp sym)
	 (symbol-file sym)
	 (let ((file (file-name-sans-extension
		      (file-name-nondirectory 
		       (symbol-file sym)))))
	   (string-match "^cl\\(-.+\\)?$" file))))

  (defun highlight-cl-macro-p (sym)
    "Return non-nil If SYM is macro."
    (let ((def (symbol-function sym)))
      (or (eq (car-safe def) 'macro)
	  (and (eq (car-safe def) 'autoload)
	       (memq (nth 4 def) '(macro t)))))))
  
(eval-when-compile
  (defmacro highlight-cl-define-keywords-alist (var docstring)
    "define `cl' function keywods alist at compile time."
    (let (base-keywods)
      ;; collect non `cl' keywods
      (mapatoms
       (lambda (x)
	 (when (and (fboundp x)
		    ;; runtime workaround
		    (not (highlight-cl-cl-function-p x)))
	   (push x base-keywods))))
      ;; load cl functions
      (require 'cl)
      ;; collect `cl' keywods and define constant.
      `(defconst ,var
	 ,(let (cl-keywords cl-macro-keywords cl-and-other-keywords)
	    (mapatoms
	     (lambda (x)
	       (when (highlight-cl-cl-function-p x)
		 (cond ((memq x base-keywods)
			(push (symbol-name x) cl-and-other-keywords))
		       ((highlight-cl-macro-p x)
			(push (symbol-name x) cl-macro-keywords))
		       (t
			(push (symbol-name x) cl-keywords))))))
	    (list 'quote
		  (list (cons 'cl cl-keywords)
			(cons 'cl-macro cl-macro-keywords)
			(cons 'cl-and-other cl-and-other-keywords))))
	 ,docstring))))

(highlight-cl-define-keywords-alist
 highlight-cl-keywords-alist
 "`cl' function keywords alist.")

(defun highlight-cl-add-font-lock-keywords ()
  "Add `cl' function keywords to `font-lock-keywords'."
  (font-lock-add-keywords 
   nil 
   (mapcar
    (lambda (x)
      (list
       (format
	"(%s\\>"
	(regexp-opt (cdr (assq (car x) highlight-cl-keywords-alist)) t))
       1 (list 'quote (cdr x)) 'append))
    '((cl . highlight-cl)
      (cl-macro . highlight-cl-macro)
      (cl-and-other . highlight-cl-and-other)))
   'add))

(provide 'highlight-cl)
;;; highlight-cl.el ends here
