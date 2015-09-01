;;; bytecomp-simplify.el --- byte compile warnings for simplifications

;; Copyright 2009, 2010, 2011, 2012 Kevin Ryde

;; Author: Kevin Ryde <user42@zip.com.au>
;; Version: 13
;; Keywords: extensions, byte-compile
;; URL: http://user42.tuxfamily.org/bytecomp-simplify/index.html

;; bytecomp-simplify.el is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; bytecomp-simplify.el is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General
;; Public License for more details.
;;
;; You can get a copy of the GNU General Public License online at
;; <http://www.gnu.org/licenses/>.


;;; Commentary:

;; This spot of code add warnings to the byte compiler to report on possible
;; simplifications in the code compiled.  Eg. (kill-buffer (current-buffer))
;; can be simplified to (kill-buffer nil).
;;
;; The reports include
;;
;;     char-before           \
;;     char-after            | argument `point' omitted
;;     push-mark             /
;;     delete-windows-on     `current-buffer' omitted for Emacs 23 up
;;     eq nil                can be `null'
;;     equal 'sym            can be `eq'
;;     kill-buffer           `current-buffer' nil or omitted for Emacs 23
;;     lisp-indent-function  `declare' within macro for Emacs 23 up
;;     princ "\n"            `terpri'
;;     re-search-forward     \ constant pattern `search-forward'
;;     re-search-backward    /   or `search-backward'
;;     search-forward        \
;;     search-backward       | `point-min' or `point-max' limit nil
;;     re-search-forward     |
;;     re-search-backward    /
;;     switch-to-buffer      to `(other-buffer)' can be nil
;;     up-list               \ count==1 can be omitted for Emacs 21 up
;;     down-list             /
;;     write-region          point-min to point-max can be nil for Emacs 22 up
;;
;;
;; Things like `delete-windows-on' which are version-dependent are reported
;; only when the Emacs in use allows the simplification.  So
;; `delete-windows-on' is only reported in Emacs 23 up, and the message
;; includes a note that it's for 23 up.
;;
;; The version-dependent bits might have scope for a kind of reverse check,
;; warning about a feature newer than a specified target Emacs supports.
;; Except conditionalized code would trigger it far too often.  There might
;; also be scope to declare a target Emacs version level, so as not to warn
;; about simplifications only possible in newer Emacs.
;;
;; Checks not done:
;;
;; `local-variable-p' argument `current-buffer' can be omitted in Emacs, but
;; not in XEmacs.  Reporting that would only spam out dual-targeted code.

;;; Install:

;; Put bytecomp-simplify.el somewhere in one of your `load-path' directories
;; and in your .emacs
;;
;;     (eval-after-load "bytecomp" '(require 'bytecomp-simplify))
;;
;; It's normal to byte compile with "emacs -q -no-site-file", which doesn't
;; read your .emacs.  If your makefile or configure has a controllable
;; $(EMACS) you can work bytecomp-simplify.el into it with
;;
;;     make EMACS="emacs -l /path/to/my/files/bytecomp-simplify.el"
;;
;; This is a tedious, but "-q -no-site-file" is the right thing when byte
;; compiling to avoid site or user settings, so there must be special action
;; to use an extension like bytecomp-simplify.

;;; Emacsen:

;; Designed for Emacs 21 and up, works in XEmacs 21.

;;; History:

;; Version 1 - the first version
;; Version 2 - fix customize setup reported by Drew Adams
;;           - fixes for search point-max and negated regexp
;; Version 3 - new up-list,down-list, char-before,char-after
;;           - fixes for emacs21
;; Version 4 - undo defadvice on unload-feature
;; Version 5 - express dependency on 'advice
;; Version 6 - new eq nil, princ "\n", put 'lisp-indent-function
;; Version 7 - new equal 'symbol
;; Version 8 - avoid stray "unresolved put-warn-indent" in emacs21
;; Version 9 - new push-mark (point)
;; Version 10 - fix check of "declare indent" availability
;; Version 11 - in fixed-match warning show the regexp
;; Version 12 - fix for put 'lisp-indent-function on unevaluated toplevels
;; Version 13 - new switch-to-buffer and write-region

;;; Code:

;;;###autoload (eval-after-load "bytecomp" '(require 'bytecomp-simplify))

;; for `ad-find-advice' macro when running uncompiled
;; (don't unload 'advice before our -unload-function)
(require 'advice)

;; for apropos-macrop
(require 'apropos)


;;-----------------------------------------------------------------------------
;; generic

(put 'bytecomp-simplify-quoted-symbol 'side-effect-free 'error-free)
(put 'bytecomp-simplify-quoted-symbol 'pure t)
(defun bytecomp-simplify-quoted-symbol (obj)
  "If OBJ is a list `(quote SYMBOL)' return SYMBOL, otherwise nil."
  (and (consp obj)
       (equal 2 (safe-length obj))
       (eq 'quote (car obj))
       (symbolp (cadr obj))
       (cadr obj)))


;;-----------------------------------------------------------------------------
;; `simplify' warnings type

;; In emacs21 when byte-compile-warnings is t, the bytecomp code let-binds
;; it to the full `byte-compile-warning-types' list, so must add `simplify'
;; there to have it take effect.  Likewise xemacs21 out of
;; `byte-compile-default-warnings'.
;;
(eval-after-load "bytecomp"
  '(progn
     (when (boundp 'byte-compile-warning-types) ;; not in xemacs21
       (add-to-list 'byte-compile-warning-types 'simplify))

     (when (boundp 'byte-compile-default-warnings) ;; xemacs21 incompatibility
       (add-to-list 'byte-compile-default-warnings 'simplify))

     ;; Add to `byte-compile-warnings' custom options.
     ;; In xemacs21 `byte-compile-warnings' is only a defvar, so nothing there.
     ;;
     ;; Maybe should copy the value, but `copy-tree' needs 'cl in emacs21
     ;; and bringing that in might hide missing cl's in the code being byte
     ;; compiled
     ;;
     (let ((type (get 'byte-compile-warnings 'custom-type)))
       (when (eq 'choice (car-safe type))
         (let ((set (assq 'set type)))
           (when (and set (not (member '(const simplify) set)))
             (nconc set '((const simplify)))))))))


;;-----------------------------------------------------------------------------

(put  'bytecomp-simplify-warning-enabled-p 'side-effect-free t)
(defun bytecomp-simplify-warning-enabled-p (&optional warning-type)
  "Return non-nil if simplify warnings are enabled in `byte-compile-warnings'."
  (unless warning-type
    (setq warning-type 'simplify))
  (cond ((eval-when-compile (fboundp 'byte-compile-warning-enabled-p))
         ;; emacs22 up
         (byte-compile-warning-enabled-p warning-type))

        ;; emacs21 doesn't have `byte-compile-warning-enabled-p'
        ((eq t byte-compile-warnings)
         t)
        ((eq 'not (car byte-compile-warnings))
         (not (memq warning-type (cdr byte-compile-warnings))))
        (t
         (memq warning-type byte-compile-warnings))))

(defun bytecomp-simplify-warn (form)
  "Warn about possible code simplifications in FORM.
A check is made of a plain call (FOO ...), anything else is
ignored.  Just the FOO call is checked, not any calls within
argument expressions."
  (when (bytecomp-simplify-warning-enabled-p)
    (let ((fn (car-safe form)))
      (when (symbolp fn)
        (let ((handler (get fn 'bytecomp-simplify-warn)))
          ;; func or list of functions
          (run-hook-with-args 'handler fn form))))))

;;-----------------------------------------------------------------------------
;; nasty hook-ins to bytecomp.el

;; Is it better to look at `byte-compile-form', or after macro expansions in
;; `byte-compile-normal-call'?  Macros might produce naive code with
;; simplifications which are not interesting, or on the other hand things in
;; the macro expander might in fact have genuine simplifications possible.

;; (defadvice byte-compile-form (before bytecomp-simplify activate)
;;   "Notice simplifications."
;;   ;; (message "form simplify: %S" form)
;;   (bytecomp-simplify-warn form))

(defadvice byte-compile-normal-call (before bytecomp-simplify activate)
  "Notice simplifications."
  (bytecomp-simplify-warn form))

;; emacs23 `char-before'
(defadvice byte-compile-char-before (before bytecomp-simplify activate)
  "Notice simplifications."
  (bytecomp-simplify-warn form))

;; for `char-after'
(defadvice byte-compile-zero-or-one-arg (before bytecomp-simplify activate)
  "Notice simplifications."
  ;; (message "zero-one simplify: %S" form)
  (bytecomp-simplify-warn form))

;; for `char-after' in xemacs21
(defadvice byte-compile-zero-or-one-arg-with-one-extra (before bytecomp-simplify activate)
  "Notice simplifications."
  ;; (message "zero-one-extra simplify: %S" form)
  (bytecomp-simplify-warn form))

;; for `eq'
(defadvice byte-compile-two-args (before bytecomp-simplify activate)
  "Notice simplifications."
  ;; (message "two-args simplify: %S" form)
  (bytecomp-simplify-warn form))

;; for `eq' in xemacs21
(defadvice byte-compile-two-args-19->20 (before bytecomp-simplify activate)
  "Notice simplifications."
  ;; (message "two-args-19->20 simplify: %S" form)
  (bytecomp-simplify-warn form))

;; get a look at 'cl `eql' before it's optimized down to eq or equal
(defadvice compiler-macroexpand (before bytecomp-simplify activate)
  "Notice simplifications."
  (bytecomp-simplify-warn form))

(defun bytecomp-simplify-unload-function ()
  "Remove defadvices applied by bytecomp-simplify.
This is called by `unload-feature'."
  (dolist (func '(byte-compile-normal-call
                  byte-compile-defmacro
                  byte-compile-char-before
                  byte-compile-zero-or-one-arg
                  byte-compile-zero-or-one-arg-with-one-extra
                  byte-compile-two-args
                  byte-compile-two-args-19->20
                  byte-compile-defmacro
                  byte-compile-file-form-defmacro
                  byte-optimize-char-before
                  compiler-macroexpand))
    (when (ad-find-advice func 'before 'bytecomp-simplify)
      (ad-remove-advice   func 'before 'bytecomp-simplify)
      (ad-activate        func)))
  nil) ;; and do normal unload-feature actions too

      
;;-----------------------------------------------------------------------------
;; char-before, char-after, push-mark

;; APEL poe.el has a bit for mule emacs19 or something when the POS argument
;; to char-before and char-after was mandatory.  Don't think need to worry
;; about that.

(defun bytecomp-simplify-char-defaultpoint (fn form)
  ;; checkdoc-params: (fn form)
  "`(point)' argument can be omitted."
  (when (equal (cdr form) '((point)))
    (byte-compile-warn "`%S' can be simplified to `(%S)'" form fn)))

(put 'char-before 'bytecomp-simplify-warn 'bytecomp-simplify-char-defaultpoint)
(put 'char-after  'bytecomp-simplify-warn 'bytecomp-simplify-char-defaultpoint)
(put 'push-mark   'bytecomp-simplify-warn 'bytecomp-simplify-char-defaultpoint)

;; in emacs21 and xemacs21 `char-before' is byte-optimized to `char-after'
;; before it reaches `byte-compile-form' etc, so catch it before that
(defadvice byte-optimize-char-before (before bytecomp-simplify activate)
  "Notice simplifications."
  ;; (message "byte-optimize-char-before simplify: %S" form)
  (bytecomp-simplify-warn form))


;;-----------------------------------------------------------------------------
;; delete-windows-on

(defconst bytecomp-simplify-delete-windows-on--optarg
  (condition-case nil
      (with-temp-buffer
        (eval '(delete-windows-on))
        t)
    (error nil))
  "Non-nil if `delete-windows-on' buffer arg is optional in this Emacs.")

(put 'delete-windows-on 'bytecomp-simplify-warn
     (lambda (fn form)
       (when (and bytecomp-simplify-delete-windows-on--optarg
                  (equal form '(delete-windows-on (current-buffer))))
         (byte-compile-warn "`%S' can be simplified to `(%S)', for Emacs 23 up"
                            form fn))))


;;-----------------------------------------------------------------------------
;; eq, equal, eql

(defun bytecomp-simplify-eq (fn form)
  ;; checkdoc-params: (fn form)
  "`(eq nil X)' can be `(null X)'."
  (when (memq nil form)
    (byte-compile-warn "`(%S nil X)' can be simplified to `(null X)'" fn)))

(defun bytecomp-simplify-equal (fn form)
  ;; checkdoc-params: (fn form)
  "`(equal 'foo X)' can be `(eq 'foo X)'."
  (bytecomp-simplify-eq fn form)

  (while (setq form (cdr form))
    (when (bytecomp-simplify-quoted-symbol (car form))
      (setq form nil) ;; end loop
      (byte-compile-warn "`(%S 'symbol ...)' can be simplified to `(eq 'symbol ...)'" fn))))

(put 'eq    'bytecomp-simplify-warn 'bytecomp-simplify-eq)
(put 'equal 'bytecomp-simplify-warn 'bytecomp-simplify-equal)
(put 'equal-including-properties
     'bytecomp-simplify-warn 'bytecomp-simplify-equal)
;; core now, 'cl in past
(put 'eql   'bytecomp-simplify-warn 'bytecomp-simplify-equal)
;; 'cl
(put 'equalp 'bytecomp-simplify-warn 'bytecomp-simplify-equal)


;;-----------------------------------------------------------------------------
;; kill-buffer

(defconst bytecomp-simplify-kill-buffer--optarg
  (condition-case nil
      (with-temp-buffer
        (eval '(kill-buffer))
        t)
    (error nil))
  "Non-nil if `kill-buffer' buffer arg is optional in this Emacs.")

(put 'kill-buffer 'bytecomp-simplify-warn
     (lambda (fn form)
       (when (equal form '(kill-buffer (current-buffer)))
         (if bytecomp-simplify-kill-buffer--optarg
             (byte-compile-warn
              "`%S' can be simplified to `(%S nil)', or in Emacs 23 to `(%S)'"
              form fn fn)
           (byte-compile-warn "`%S' can be simplified to `(%S nil)" form fn)))

       (when (and bytecomp-simplify-kill-buffer--optarg
                  (equal form '(kill-buffer nil)))
         (byte-compile-warn
          "`%S' can be simplified to `(%S), for Emacs 23 up"
          form fn))))


;;-----------------------------------------------------------------------------
;; princ -- princ "\n" can be terpri

(put 'princ 'bytecomp-simplify-warn
     (lambda (fn form)
       (when (equal (cdr form) '("\n"))
         (byte-compile-warn "`%S \"\\n\"' can be simplified to `terpri'" fn))))


;;-----------------------------------------------------------------------------
;; put
;;
;; Believe `(declare (indent N))' within a macro is a simplification in that
;; it's easier if renaming or cutting and pasting, though it makes no
;; difference to how the code comes out.

(defconst bytecomp-simplify-put--declare-indent-p
  (condition-case nil
      (eval
       '(progn
          (defmacro bytecomp-simplify-put--declare-indent-p--test
            (foo &rest body)
            (declare (indent 1))
            nil)
          (prog1
              (equal 1 (get 'bytecomp-simplify-put--declare-indent-p--test
                            'lisp-indent-function))
            (fmakunbound 'bytecomp-simplify-put--declare-indent-p--test))))
    (error nil))
  "Non-nil if `(declare (indent N))' can be used in this Emacs.")

(defvar bytecomp-simplify-put--pending-indents nil
  "List of as-yet unknown symbols with (put 'lisp-indent-function).")
(defvar bytecomp-simplify-put--known-macros nil
  "List of defmacro defined symbols.")

(defun bytecomp-simplify-put-warn-indent (symbol)
  "Report lisp-indent-function on SYMBOL can be `declare' instead."
  (setq bytecomp-simplify-put--pending-indents
        (remove symbol bytecomp-simplify-put--pending-indents))
  (byte-compile-warn "(put '%S 'lisp-indent-function) can be simplified to `(declare (indent N))' in the macro, for Emacs 23 up" symbol))

(put 'put 'bytecomp-simplify-warn
     (lambda (fn form)
       (when (and bytecomp-simplify-put--declare-indent-p
                  (equal 4 (safe-length form))
                  (equal '(quote lisp-indent-function) (nth 2 form))
                  (setq fn (bytecomp-simplify-quoted-symbol (nth 1 form))))
         ;; `byte-compile-macro-environment' entry cdr non-nil for macro,
         ;; nil for macro redefined as function.  `declare' only for macros,
         ;; not functions
         (if (or (memq fn bytecomp-simplify-put--known-macros)
                 (cdr (assq fn byte-compile-macro-environment))
                 (and (fboundp fn)
                      (apropos-macrop fn)))
             (bytecomp-simplify-put-warn-indent fn)
           ;; not yet defined
           (add-to-list 'bytecomp-simplify-put--pending-indents fn)))

       (when (and (equal 4 (safe-length form))
                  (eq 'lisp-indent-function (nth 2 form))
                  (bytecomp-simplify-warning-enabled-p 'suspicious))
         (byte-compile-warn "(put ...) unquoted lisp-indent-function probably wrong (being the value of lisp-indent-function not the symbol)"))))

(defun bytecomp-simplify-defmacro (form)
  (when bytecomp-simplify-put--declare-indent-p
    (let ((symbol (cadr form))) ;; macro name
      (push symbol bytecomp-simplify-put--known-macros)
      (when (memq symbol bytecomp-simplify-put--pending-indents)
        (bytecomp-simplify-put-warn-indent symbol)))))
(defadvice byte-compile-defmacro (before bytecomp-simplify activate)
  "Check for previous encountered (put 'lisp-indent-function)."
  (bytecomp-simplify-defmacro (ad-get-arg 0)))
(defadvice byte-compile-file-form-defmacro (before bytecomp-simplify activate)
  "Check for previous encountered (put 'lisp-indent-function)."
  (bytecomp-simplify-defmacro (ad-get-arg 0)))


;;-----------------------------------------------------------------------------
;; search-forward
;; search-backward

(defun bytecomp-simplify-search-limit (fn form)
  ;; checkdoc-params: (fn form)
  "Search limit `point-min' or `point-max' can be nil."
  (let ((default (if (string-match "forward" (symbol-name fn))
                     '(point-max)
                   '(point-min))))
    (when (equal (nth 2 form) default)
      (byte-compile-warn "`%S' argument %S can be simplified to `nil'"
                         fn (nth 2 form)))))

(put 'search-forward 'bytecomp-simplify-warn
     'bytecomp-simplify-search-limit)
(put 'search-backward 'bytecomp-simplify-warn
     'bytecomp-simplify-search-limit)


;;-----------------------------------------------------------------------------
;; re-search-forward
;; re-search-backward

(defun bytecomp-simplify-regexp-fixed-p (regexp)
  "Return non-nil if REGEXP matches only a fixed string.
All backslashed alphabeticals like \\X are treated as not a fixed
match.  Unknown ones will match only a literal X, but you
shouldn't rely on that in case the regexp engine gets new
specials in the future."
  (string-match (concat "\\`\\("
                        "[^.*+?[^$\\]"     ;; not a special
                        "\\|"              ;; OR
                        "\\\\[.*+?[^$\\]"  ;; a special but backslashed
                        "\\|"              ;; OR
                        "\\[[^^]]"         ;; a char-class of single character
                        "\\)*\\'")
                regexp))

(defun bytecomp-simplify-re-search-fixed (fn form)
  ;; checkdoc-params: (fn form)
  "Fixed string `re-search-' can be plain `search-'."
  (when (and (stringp (nth 1 form))
             (bytecomp-simplify-regexp-fixed-p (nth 1 form)))
    (byte-compile-warn
     "`%S' with fixed-string regexp %s can be simplified to `%s'"
     fn
     (let ((print-escape-newlines t))
       (prin1-to-string (nth 1 form)))
     (substring (symbol-name fn) 3))))

(put 're-search-forward 'bytecomp-simplify-warn
     '(bytecomp-simplify-re-search-fixed
       bytecomp-simplify-search-limit))
(put 're-search-backward 'bytecomp-simplify-warn
     '(bytecomp-simplify-re-search-fixed
       bytecomp-simplify-search-limit))


;;-----------------------------------------------------------------------------
;; up-list, down-list

(defconst bytecomp-simplify-updown-list--optarg
  (condition-case nil
      (with-temp-buffer
        (insert "()")
        (goto-char (point-min))
        (eval '(down-list))
        t)
    (error nil))
  "Non-nil if `up-list' and `down-list' count arg is optional in this Emacs.")

(defun bytecomp-simplify-updown-list (fn form)
  ;; checkdoc-params: (fn form)
  "`(up-list 1)' arg can be omitted as `(up-list)', in Emacs 21 up."
  (when (and bytecomp-simplify-updown-list--optarg
             (equal (cdr form) '(1)))
    (byte-compile-warn "`%S' can be simplified to `(%S)', for Emacs 21 up"
                       form fn)))

(put 'down-list 'bytecomp-simplify-warn 'bytecomp-simplify-updown-list)
(put 'up-list   'bytecomp-simplify-warn 'bytecomp-simplify-updown-list)


;;-----------------------------------------------------------------------------
;; switch-to-buffer -- nil means (other-buffer)
;; not actually documented in older Emacs, but goes back at least to Emacs 20

(put 'switch-to-buffer 'bytecomp-simplify-warn
     (lambda (fn form)
       (when (equal form '(switch-to-buffer (other-buffer)))
         (byte-compile-warn "`%S' can be simplified to `(%S nil)" form fn))))


;;-----------------------------------------------------------------------------
;; write-region

(defconst bytecomp-simplify--write-region-nil
  (condition-case nil
      (with-temp-buffer
        (write-region nil nil null-device)
        t)
    (error nil))
  "Non-nil if `write-region' accepts nil for whole buffer in this Emacs.
`write-region' has this in GNU Emacs 22 and up (and not in XEmacs 21.4).")

(put 'write-region 'bytecomp-simplify-warn
     (lambda (fn form)
       (when (and bytecomp-simplify--write-region-nil
                  (equal (car-safe form) 'write-region)
                  (equal (car-safe (cdr-safe form)) '(point-min))
                  (equal (car-safe (cdr-safe (cdr-safe form))) '(point-max)))
         (byte-compile-warn "`(%S (point-min) (point-max)' can be simplified to `(%S nil nil', for Emacs 22 up"
                            fn fn))))

;;-----------------------------------------------------------------------------

;; LocalWords: conditionalized spam defadvices alphabeticals

(provide 'bytecomp-simplify)

;;; bytecomp-simplify.el ends here
