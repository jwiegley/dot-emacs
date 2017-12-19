;;; operate-on-number.el --- Operate on number at point with arithmetic functions

;; Copyright (c) 2014-2015 Akinori MUSHA
;;
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
;; ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
;; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
;; OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
;; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
;; LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
;; OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGE.

;; Author: Akinori MUSHA <knu@iDaemons.org>
;; URL: https://github.com/knu/operate-on-number.el
;; Created: 15 May 2014
;; Version: 1.2.0
;; Keywords: editing

;;; Commentary:
;;
;; Suppose the point is on some number.  If you want to double it,
;; invoke `operate-on-number-at-point' followed by some keys: * 2 RET.
;;
;; Alternatively, you can bind `apply-operation-to-number-at-point' to
;; <some prefix> *, and you will be able to just type the sequence to
;; double a number, which function uses the last key typed as function
;; specifier and supplies with a default argument which in this case
;; of * is 2.  This command takes numeric argument, so you can type
;; M-3 <some prefix> * to triple the number.
;;
;; For the predefined operation list and how to define a new
;; operation, see `operate-on-number-at-point-alist'.
;;
;; It is recommended using smartrep to bind the functions like this:
;;
;;   (smartrep-define-key global-map "C-."
;;     '(("+" . apply-operation-to-number-at-point)
;;       ("-" . apply-operation-to-number-at-point)
;;       ("*" . apply-operation-to-number-at-point)
;;       ("/" . apply-operation-to-number-at-point)
;;       ("\\" . apply-operation-to-number-at-point)
;;       ("^" . apply-operation-to-number-at-point)
;;       ("<" . apply-operation-to-number-at-point)
;;       (">" . apply-operation-to-number-at-point)
;;       ("#" . apply-operation-to-number-at-point)
;;       ("%" . apply-operation-to-number-at-point)
;;       ("'" . operate-on-number-at-point)))
;;

;;; Code:

(require 'calc-bin)

(defun oon--parse-number-at-point ()
  "Parse the text around point for a number and return a vector
with the following elements if found:

0: base
1: beginning position of the literal
2: position for a sign; if nil, no negative number is allowed for this literal
3: beginning position of the number part
4: end position of the number part
5: end position of the literal

Return nil if no number is found."
  (let (num bounds
            (case-fold-search nil))
    (save-excursion
      (if (looking-back "[[:digit:]]")
          (backward-char 1))
      (cond
       ;; Decimal numbers as sexp: e.g. "100", "3.1415", "1e3"
       ((save-excursion
          (and
           (setq num (number-at-point))
           (setq bounds (bounds-of-thing-at-point 'sexp))
           (not (char-equal (char-after (car bounds)) ?#))))
        (let* ((beg (car bounds))
               (end (cdr bounds))
               (char (char-after beg))
               (sign (or (char-equal char ?-) (char-equal char ?+)))
               (nbeg (if sign (1+ beg) beg)))
          (vector 10 beg beg nbeg end end)))
       ;; Hexadecimal literals: e.g. "0x1e", "#x1e"
       ((save-excursion
          (and (looking-at "\\([+-]?0?[xX]?\\|#?[xX]?[+-]?\\)[[:xdigit:]]*")
               (goto-char (match-end 0)))
          (looking-back "\\(\\([+-]\\|\\b\\)0[xX]\\|#[xX]\\([+-]?\\)\\)\\([[:xdigit:]]+\\)"
                        (line-beginning-position) t))
        (vector 16
                (match-beginning 0)
                (or (match-beginning 2)
                    (match-beginning 3))
                (match-beginning 4)
                (match-end 4)
                (match-end 0)))
       ;; Hexadecimal string literals: e.g. "\u{fffd}", "\x0f", "U+3000"
       ((save-excursion
          (and (looking-at "\\(\\\\?[ux]?{?\\|U?\\+?\\)[[:xdigit:]]*")
               (goto-char (match-end 0)))
          (looking-back "\\(\\\\[ux]{?\\|\\bU\\+\\)\\([[:xdigit:]]+\\)"
                        (line-beginning-position) t))
        (let ((beg (match-beginning 0))
              (nbeg (match-beginning 2))
              (nend (match-end 2)))
          (vector 16
                  beg
                  nil
                  nbeg
                  nend
                  (if (and (= (char-before nbeg) ?{)
                           (= (char-after  nend) ?}))
                      (1+ nend) nend))))
       ;; Octal number literals: e.g. "0o770", "#o770"
       ((save-excursion
          (and (looking-at "\\([+-]?0?[oO]?\\|#?[oO]?[+-]?\\)[0-7]*") (goto-char (match-end 0)))
          (and (not (looking-at "[[:digit:]]"))
               (looking-back "\\(\\([+-]\\|\\b\\)0[oO]\\|#[oO]\\([+-]?\\)\\)\\([0-7]+\\)"
                             (line-beginning-position) t)))
        (vector 8
                (match-beginning 0)
                (or (match-beginning 2)
                    (match-beginning 3))
                (match-beginning 4)
                (match-end 4)
                (match-end 0)))
       ;; Octal character literals: e.g. \033"
       ((save-excursion
          (and (looking-at "\\\\?[0-7]\\{1,3\\}") (goto-char (match-end 0)))
          (looking-back "\\\\\\([0-7]\\{3\\}\\)"
                        (line-beginning-position) t))
        (vector 8
                (match-beginning 0)
                nil
                (match-beginning 1)
                (match-end 1)
                (match-end 0)))
       ;; Binary number literals: e.g. "0b110", "#b110"
       ((save-excursion
          (and (looking-at "\\([+-]?0?[bB]?\\|#?[bB]?[+-]?\\)[01]*") (goto-char (match-end 0)))
          (and (not (looking-at "[[:digit:]]"))
               (looking-back "\\(\\([+-]\\|\\b\\)0[bB]\\|#[bB]\\([+-]?\\)\\)\\([01]+\\)"
                             (line-beginning-position) t)))
        (vector 2
                (match-beginning 0)
                (or (match-beginning 2)
                    (match-beginning 3))
                (match-beginning 4)
                (match-end 4)
                (match-end 0)))
       ;; Just a sequence of decimal digits inside a word
       ((save-excursion
          (and (looking-at "[+-]?[[:digit:]]*") (goto-char (match-end 0)))
          (looking-back "\\([+-]\\)?\\([[:digit:]]+\\)"
                        (line-beginning-position) t))
        (vector 10
                (match-beginning 0)
                (match-beginning 1)
                (match-beginning 2)
                (match-end 2)
                (match-end 0)))))))

(defun oon--format-number (abs base sample)
  "Format an absolute number ABS in BASE like SAMPLE."
  (let ((str
         (if (= base 10)
             (format "%s" abs)
           (let* ((calc-number-radix base)
                  (str (math-format-radix (setq abs (floor abs))))
                  (case-fold-search nil))
             (if (string-match "[A-Z]" sample)
                 str (downcase str))))))
    (cond ((and (integerp abs)
                (string-match "\\`0[[:xdigit:]]+\\'" sample))
           (let ((zlen (- (length sample) (length str))))
             (if (not (natnump zlen)) str
               (concat (make-string zlen ?0) str))))
          (t
           str))))

(defun oon--parsed-number (parsed)
  "Parse a vector PARSED into a number it represents."
  (let* ((base (elt parsed 0))
         (spos (elt parsed 2))
         (nbeg (elt parsed 3))
         (nend (elt parsed 4))
         (str (buffer-substring-no-properties nbeg nend))
         (abs (string-to-number str base)))
    (if (and spos (= (char-after spos) ?-))
        (- abs) abs)))

(defun oon--original-number-for-display (parsed)
  (let* ((base (elt parsed 0))
         (nbeg (elt parsed 3))
         (nend (elt parsed 4))
         (str (buffer-substring-no-properties nbeg nend))
         (num (oon--parsed-number parsed))
         (ssign (if (natnump num) "" "-")))
    (if (= base 10)
        (concat ssign str)
      (concat ssign (format "%d#" base) str (format " (%s)" num)))))

(defun oon--replace-number (parsed number)
  "Replace a number specified by PARSED with NUMBER."
  (let* ((base (elt parsed 0))
         (beg  (elt parsed 1))
         (spos (elt parsed 2))
         (nbeg (elt parsed 3))
         (nend (elt parsed 4))
         (str (buffer-substring-no-properties nbeg nend))
         (abs (abs number))
         (sign (if (natnump number) ?+ ?-)))
    (if (and (null spos)
             (= sign ?-))
        (error "cannot replace with a negative number!"))
    (goto-char nbeg)
    (delete-region nbeg nend)
    (insert (oon--format-number abs base str))
    (if spos
        (save-excursion
          (goto-char spos)
          (if (or (when (looking-at "[+-]")
                    (delete-char 1) t)
                  (= sign ?-))
              (insert-char sign))))))

;;;###autoload
(defun find-number-at-point ()
  "Search the current line till EOL for a number.
If a pure number is found, move point to the end of the number
and return the value.  Raise an error otherwise."
  (interactive)
  (let ((parsed (or (oon--parse-number-at-point)
                    (error "No number found at point"))))
    (goto-char (elt parsed 4))
    (oon--parsed-number parsed)))

(defgroup operate-on-number nil
  "Operate on number at point."
  :prefix "apply-on-number-at-point-"
  :group 'editing)

(defcustom operate-on-number-at-point-alist
  '((?+ (1) +)
    (?- (1) -)
    (?* (2) *)
    (?/ (2) /)
    (?\\ (2) %
         :read t)
    (?^ (2) expt)
    (?< (1) ash
        :display "<<")
    (?> (1) (lambda (a b) (ash a (- b)))
        :display ">>")
    (?b () math-format-binary)
    (?o () (lambda (a) (format "%o" a)))
    (?x () (lambda (a) (format "%x" a)))
    (?X () (lambda (a) (format "%X" a)))
    (?# (10) (lambda (a b)
               (let ((calc-number-radix b))
                 (math-format-radix a)))
        :display "in base"
        :read t)
    (?% ("%s") (lambda (a b) (format b a))
        :display "formatted with"
        :read t))
  "A list of (KEY DEFARGS FUNC ...).

KEY is used immediately following `apply-on-number-at-point' to
select an operation.

DEFARGS is a list of default arguments, which length is taken as
the number of additional operands required for the operation.
Currently this length must be zero or one.

FUNC is a function for the operation.

After that comes an optional inline property list in which the
following keys are available:

:display	Specifies the human readable representation for
		the operation.

:read		If this property is non-nil,
		`apply-operation-to-number-at-point' always asks
		user for an additional argument, using a value in
		DEFARGS as default."
  :type '(repeat
          (list (character :tag "Key")
                (repeat :tag "Default Arguments"
                        (sexp :tag "Argument"))
                (function :tag "Function")
                (repeat :inline t :tag "Property List"
                        (list :inline t
                              (symbol :tag "Option")
                              (sexp :tag "Value")))))
  :set (lambda (sym val)
         (set-default sym
                      (mapcar #'(lambda (entry)
                                  (let ((key (nth 0 entry))
                                        (arg1 (nth 1 entry))
                                        (arg2 (nth 2 entry))
                                        (plist (nthcdr 3 entry)))
                                    (if (and (listp arg2)
                                             (>= 1 (length arg2)))
                                        ;; compatibility
                                        (append (list key arg2 arg1) plist)
                                      entry))) val)))
  :group 'operate-on-number)

(defun apply-to-number-at-point (func args &optional plist)
  "Apply FUNC on a number at point with ARGS.
For possible keys of PLIST, see `operate-on-number-at-point-alist'."
  (let* ((parsed (or (oon--parse-number-at-point)
                     (error "No number found at point")))
         (num (oon--parsed-number parsed))
         (result (apply func num args)))
    (oon--replace-number parsed result)))

;;;###autoload
(defun apply-operation-to-number-at-point (&optional key read-args)
  "Apply an operation specified by KEY on a number at point.

If called interactively, use the last key input as KEY.

If the operation requires an additional operand, it is taken from
one of the following sources in the order named:

1. Prefix argument if given

2. Value read from keyboard if READ-ARGS is non-nil or the :read
   property is non-nil

3. Default argument predefined in `operate-on-number-at-point-alist'"
  (interactive (list
                (let ((keys (this-command-keys-vector)))
                  (elt keys (1- (length keys))))
                nil))
  (let* ((arg (and current-prefix-arg
                   (prefix-numeric-value current-prefix-arg)))
         (parsed (or (oon--parse-number-at-point)
                     (error "No number found at point")))
         (oargs (or (cdr (assoc key operate-on-number-at-point-alist))
                    (error "Unknown operator: %c" key)))
         (formatted (oon--original-number-for-display parsed))
         (defargs (nth 0 oargs))
         (defarg (car defargs))
         (func (nth 1 oargs))
         (plist (nthcdr 2 oargs))
         (display (or (plist-get plist :display) (string key)))
         (args (cond ((null defargs)
                      nil)
                     ((and (numberp defarg)
                           arg)
                      (list arg))
                     ((or read-args
                          (plist-get plist :read))
                      (let* ((prompt (format "Insert %s %s " formatted display))
                             (input (if (numberp defarg)
                                        (read-number prompt defarg)
                                      (read-string prompt nil nil
                                                   defarg))))
                        (list input)))
                     (t
                      defargs))))
    (apply-to-number-at-point func args plist)))

;;;###autoload
(defun operate-on-number-at-point (&optional arg)
  "Operate on number at point.

The kind of operation to perform is specified by the following
key typed.

An optional number ARG becomes a counter operand to the number at
point for the operation if applicable."
  (interactive "*p")
  (let* ((parsed (or (oon--parse-number-at-point)
                     (error "No number found at point")))
         (formatted (oon--original-number-for-display parsed))
         (key (read-char (format "Apply on %s:" formatted) t)))
    (apply-operation-to-number-at-point key t)))

(provide 'operate-on-number)

;;; operate-on-number.el ends here
