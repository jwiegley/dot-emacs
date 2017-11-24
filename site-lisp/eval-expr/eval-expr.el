;;; eval-expr.el --- enhanced eval-expression command

;; Copyright (C) 1991 Free Software Foundation, Inc.
;; Copyright (C) 1991 Joe Wells
;; Copyright (C) 1998, 1999, 2000 Noah S. Friedman

;; Author: Noah Friedman <friedman@splode.com>
;; Maintainer: friedman@splode.com
;; Keywords: lisp, extensions
;; Created: 1998-07-30

;; $Id: eval-expr.el,v 1.7 2000/03/13 11:13:19 friedman Exp $

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, you can either send email to this
;; program's maintainer or write to: The Free Software Foundation,
;; Inc.; 59 Temple Place, Suite 330; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Updates of this program may be available via the URL
;; http://www.splode.com/~friedman/software/emacs-lisp/

;; To use this package, put this in your .emacs:
;;
;;    (require 'eval-expr)
;;    (eval-expr-install)

;; Highlights:
;;
;;   * When reading the Lisp object interactively from the minibuffer, the
;;     minibuffer uses the Emacs Lisp Mode syntax table.  (Emacs 19.18 or
;;     later only.)
;;
;;   * If you type an incomplete or otherwise syntactically invalid
;;     expression (e.g. you forget a closing paren), you can fix your
;;     mistake without having to type it all over again.
;;
;;   * Can display the result in a buffer if it is too big to fit in the
;;     echo area.  This buffer is placed in Emacs Lisp Mode.
;;     (If you give a prefix arg, the result is placed in the current
;;     buffer instead of the echo area or a separate temporary buffer.)
;;
;;   * The variables `eval-expr-print-level' and `eval-expr-print-length'
;;     can be used to constrain the attempt to print recursive data
;;     structures.  These variables are independent of the global
;;     `print-level' and `print-length' variables so that eval-expression
;;     can be used more easily for debugging.
;;
;;   * Pretty-printing complex results via `pp' function is possible.

;; This program is loosely based on an earlier implemention written by Joe
;; Wells <jbw@cs.bu.edu> called eval-expression-fix.el (last revised
;; 1991-10-12).  That version was originally written for Emacs 18 and,
;; while it worked with some quirky side effects in Emacs 19, created even
;; more problems in Emacs 20 and didn't work in XEmacs at all.
;;
;; This rewrite should work in Emacs 19.18 or later and any version of
;; XEmacs.  However it will not work in Emacs 18.

;;; Code:

(defgroup eval-expr nil
  "Interactive lisp evaluation."
  :group 'eval-expr
  :group 'lisp)

;;;###autoload
(defcustom eval-expr-error-message-delay 3
  "*Amount of time, in seconds, to display in echo area before continuing."
  :type 'integer
  :group 'eval-expr)

;;;###autoload
(defcustom eval-expr-prompt "Eval: "
  "*Prompt used by eval-expr."
  :type 'string
  :group 'eval-expr)

;;;###autoload
(defcustom eval-expr-honor-debug-on-error t
  "*If non-nil, do not trap evaluation errors.
Instead, allow errors to throw user into the debugger, provided
debug-on-error specifies that the particular error is a debuggable condition."
  :type 'boolean
  :group 'eval-expr)

;;;###autoload
(defcustom eval-expr-use-echo-area-or-buffer 1
  "*Preference for when to use echo area of a temporary buffer for results.

If set to t or `buffer', always put results into a temporary buffer.
If set to `nil' or `echo-area', always display results in echo area.
If an integer N, use the echo area unless the results would require more
than N lines to display; in that case, use a temporary buffer.

Some versions of emacs can display arbitrarily large output in the echo
area by dynamically resizing it, so a temporary buffer is not necessary
unless you expect the output to exceed the limits of the resize thresholds
or want to be able to edit the results."
  :type '(radio
          (const   :tag "Always use temporary buffer" t)
          (const   :tag "Always use echo area" nil)
          (integer :tag "Use temporary buffer if more than this many lines"))
  :group 'eval-expr)

;;;###autoload
(defcustom eval-expr-print-level
  (cond ((boundp 'eval-expression-print-level) ; Emacs 21
         (default-value 'eval-expression-print-level))
        ((boundp 'print-level)
         (default-value 'print-level)))
  "*Like print-level, but affect results printed by `eval-expr' only."
  :type '(radio (const   :tag "Unlimited" nil)
                (integer :tag "Maximum level of" 8))
  :group 'eval-expr)

;;;###autoload
(defcustom eval-expr-print-length
  (cond ((boundp 'eval-expression-print-length) ; Emacs 21
         (default-value 'eval-expression-print-length))
        ((boundp 'print-length)
         (default-value 'print-length)))
  "*Like print-length, but affect results printed by `eval-expr' only."
  :type '(radio (const   :tag "Unlimited" nil)
                (integer :tag "Maximum length of" 8))
  :group 'eval-expr)

;;;###autoload
(defcustom eval-expr-print-function (if (fboundp 'pp) 'pp 'prin1)
  "*Function to use for printing objects.
E.g. this can be set to `pp' to generate pretty-printed results,
or `prin1' for unformatted results."
  :type '(radio (function-item pp)
                (function-item prin1)
                function)
  :group 'eval-expr)

;;; No user-settable options below.

(defvar eval-expr-output-buffer-name "*Eval Expression Output*")
(defvar eval-expr-error-buffer-name  "*Eval Expression Error*")

(defvar eval-expr-whitespace
  (mapcar 'string-to-char '(" " "\t" "\n")))

(defalias 'eval-expr-orig-command nil)


;;;###autoload
(defun eval-expr-install ()
  "Replace standard eval-expression command with enhanced eval-expr."
  (interactive)
  (or (symbol-function 'eval-expr-orig-command)
      (fset 'eval-expr-orig-command (symbol-function 'eval-expression)))
  (defalias 'eval-expression 'eval-expr))

(defun eval-expr-uninstall ()
  "Restore original, unenhanced eval-expression command."
  (interactive)
  (fset 'eval-expression (symbol-function 'eval-expr-orig-command)))

;;;###autoload
(defun eval-expr (ee::expression &optional ee::insert-value)
  "Evaluate EXPRESSION and print value in minibuffer, temp, or current buffer.
A temp output buffer is used if there is more than one line in the
evaluated result.
If invoked with a prefix arg, or second lisp argument EE::INSERT-VALUE is
non-nil, then insert final value into the current buffer at point.

Value is also consed on to front of the variable `values'."
  (interactive (list (eval-expr-read-lisp-object-minibuffer eval-expr-prompt)
                     current-prefix-arg))
  (let* ((ee::error nil)
         (ee::result (cond ((and eval-expr-honor-debug-on-error
                                 debug-on-error)
                            (eval ee::expression))
                           (t
                            (condition-case ee::err-data
                                (eval ee::expression)
                              (error
                               (setq ee::error ee::err-data)))))))
    (cond (ee::error
           (eval-expr-error-message ee::error nil t)
           (beep t))
          (ee::insert-value
           (eval-expr-print eval-expr-print-function
                            ee::result (current-buffer)))
          (t
           (setq values (cons ee::result values))
           (eval-expr-display-message eval-expr-output-buffer-name
             (function
              (lambda ()
                (eval-expr-print eval-expr-print-function ee::result))))))
    ee::result))

(defun eval-expr-read-lisp-object-minibuffer (prompt &optional input)
  (or (null input)
      (setq input (eval-expr-print 'prin1-to-string input)))

  (let ((minibuffer-setup-hook minibuffer-setup-hook)
        (retry t)
        (result nil)
	(expr nil)
        (index nil)
        (i 0))
    (add-hook 'minibuffer-setup-hook 'eval-expr-minibuffer-setup)
    (while retry
      (condition-case err-data
          (progn
            (setq input
                  (read-from-minibuffer prompt
                                        (if (numberp index)
                                            (cons input (1+ index))
                                          input)
                                        (and (boundp 'read-expression-map)
                                             read-expression-map)
                                        nil
                                        'read-expression-history))

            (setq index nil)
            (setq result (read-from-string input))
            (setq expr (car result))
            (setq index (cdr result))
            (setq i index)

            ;; This mimics a useful test done in read_minbuf (which is
            ;; called by Fread_from_minibuffer) when expflag is true.  But
            ;; this test doesn't happen when calling Fread_from_string
            ;; directly as we've done here, so do it now in lisp.
            (while (< i (length input))
              (or (memq (aref input i) eval-expr-whitespace)
                  (error "Trailing garbage following expression"))
              (setq i (1+ i)))

            (setq retry nil))
        (quit
         (setq retry nil))
	(error
         (eval-expr-error-message err-data t))))
    expr))

(defun eval-expr-minibuffer-setup ()
  (set-syntax-table emacs-lisp-mode-syntax-table))


;;; Display routines

(defun eval-expr-error-message (condition-data &optional waitp raw-error)
  (let ((error (car condition-data))
        (data  (cdr condition-data))
        (cursor-in-echo-area t)
        (error-str nil))

    (and (consp error)
         (null (cdr error))
         (setq error (car error)))

    (and (consp data)
         (null (cdr data))
         (setq data (car data)))

    (and (symbolp error)
         (not raw-error)
         (setq error-str (get error 'error-message)))

    (and (eval-expr-display-message eval-expr-error-buffer-name
           (cond ((null data)
                  (format "Error: %s" (or error-str error)))
                 ((eq error 'error)
                  (format "Error: %s" data))
                 (error-str
                  (format "%s: %s" error-str data))
                 (t
                  (format "Error: %s; Data: %s" error data))))
         waitp
         (sit-for eval-expr-error-message-delay))))

(defun eval-expr-display-message (output-buffer thunk)
  (let* ((buffer (generate-new-buffer " *"))
         (standard-output buffer)
         (echo-area-p t))
    (save-excursion
      (set-buffer buffer)
      (cond ((stringp thunk)  ; this is a cheat
             (insert thunk))
            (t
             (funcall thunk)))
      (cond ((or (memq eval-expr-use-echo-area-or-buffer '(nil echo-area))
                 (and (integerp eval-expr-use-echo-area-or-buffer)
                      (>= eval-expr-use-echo-area-or-buffer
                          (eval-expr-count-display-lines
                           nil nil (minibuffer-window)))))
             (message "%s" (buffer-string)))
            (t
             (setq echo-area-p nil)
             (with-output-to-temp-buffer output-buffer
               (save-excursion
                 (set-buffer output-buffer)
                 (or (eq major-mode 'emacs-lisp-mode)
                     (emacs-lisp-mode))
                 (insert-buffer buffer))))))
    (kill-buffer buffer)
    echo-area-p))

(put 'eval-expr-display-message 'lisp-indent-function 1)

(defun eval-expr-count-display-lines (&optional beg end window)
  (or beg (setq beg (point-min)))
  (or end (setq end (point-max)))
  (save-excursion
    (save-restriction
      (narrow-to-region beg end)
      (goto-char beg)
      (let ((lines (vertical-motion (- end beg -1) window)))
        ;; sanity check that lines > 0 when window != selected-window
        ;; This might be a problem only with emacs 21 devel sources.
        ;; FIXME: check to see if this is fixed at a later date.
        (cond ((or (null window)
                   (eq window (selected-window))))
              ((= lines 0)
               (let ((width (window-width window))
                     start stop)
                 (setq lines 0)
                 (goto-char beg)
                 (while (not (eobp))
                   (setq start (point)
                         stop (progn (end-of-line) (point)))
                   (setq lines (+ lines (max 1 (1+ (/ (- stop start) width)))))
                   (or (eobp) (forward-char 1))))))
        lines))))

(defun eval-expr-print (func &rest args)
  (let ((print-level  eval-expr-print-level)
        (print-length eval-expr-print-length))
    (apply func args)))

(provide 'eval-expr)

;;; eval-expr.el ends here.
