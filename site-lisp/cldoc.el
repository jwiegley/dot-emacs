;;; cldoc.el --- show Common Lisp operators and variables information in echo area

;; Copyright (C) 1996, 97, 98, 99, 2000 Free Software Foundation, Inc.
;; Copyright (C) 2004 Yuji Minejima

;; This program (cldoc.el) is based on eldoc.el.
;; Eldoc Author: Noah Friedman <friedman@splode.com>
;; Keywords: extensions

;; $Id: cldoc.el,v 1.16 2004/12/01 02:06:43 yuji Exp $

;; This file is not part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; cldoc.el is basically an eldoc clone for Common Lisp.
;; The following comment is from eldoc.el
;; > This program was inspired by the behavior of the "mouse documentation
;; > window" on many Lisp Machine systems; as you type a function's symbol
;; > name as part of a sexp, it will print the argument list for that
;; > function.  Behavior is not identical; for example, you need not actually
;; > type the function name, you need only move point around in a sexp that
;; > calls it.  Also, if point is over a documented variable, it will print
;; > the one-line documentation for that variable instead, to remind you of
;; > that variable's meaning.
;;
;; cldoc.el has a database of parameters and results of Common Lisp's standard
;; functions, and syntax rules of standard macros and special operators.
;; cldoc.el automatically uses SLIME's autodoc facility if available to display
;; parameters of user defined functions and macros, and the values of global
;; variables.


;; One useful way to enable this minor mode is to put the following in your
;; .emacs:
;;
;; ;; all users
;; (autoload 'turn-on-cldoc-mode "cldoc" nil t)
;; (add-hook 'lisp-mode-hook 'turn-on-cldoc-mode)
;;
;; ;; ilisp users
;; (add-hook 'ilisp-mode-hook 'turn-on-cldoc-mode)
;; (setq ilisp-bindings-*bind-space-p* nil)
;; 
;; ;; slime users
;; (add-hook 'slime-repl-mode-hook
;;           #'(lambda ()
;;               (turn-on-cldoc-mode)
;;               (define-key slime-repl-mode-map " " nil)))
;; (add-hook 'slime-mode-hook
;;           #'(lambda () (define-key slime-mode-map " " nil)))
;; (setq slime-use-autodoc-mode nil)

;; todo
;; * handling of operators with multiple syntax rules (e.g. file-position).
;; * handling of operators which implementations are allowed to extend
;;   (e.g. directory)


;;; Code:
(require 'cl)

;; Use idle timers if available in the version of emacs running.
;; Please don't change this to use `require'; this package works
;; as-is in XEmacs 19.14 and later and I am striving to maintain
;; compatibility between emacs variants.
(or (featurep 'timer)
    (load "timer" t))

(defgroup cldoc nil
  "Show function arglist or variable docstring in echo area."
  :group 'lisp
  :group 'extensions)

;;;###autoload
(defcustom cldoc-mode nil
  "*If non-nil, show the defined parameters for the elisp function near point.

For the emacs lisp function at the beginning of the sexp which point is
within, show the defined parameters for the function in the echo area.
This information is extracted directly from the function or macro if it is
in pure lisp.  If the emacs function is a subr, the parameters are obtained
from the documentation string if possible.

If point is over a documented variable, print that variable's docstring
instead.

This variable is buffer-local."
  :type 'boolean
  :group 'cldoc)
(make-variable-buffer-local 'cldoc-mode)

(defcustom cldoc-idle-delay 0.50
  "*Number of seconds of idle time to wait before printing.
If user input arrives before this interval of time has elapsed after the
last input, no documentation will be printed.

If this variable is set to 0, no idle time is required."
  :type 'number
  :group 'cldoc)

;;;###autoload
(defcustom cldoc-minor-mode-string " Cldoc"
  "*String to display in mode line when Cldoc Mode is enabled."
  :type 'string
  :group 'cldoc)

(defcustom cldoc-argument-case 'upcase
  "Case to display argument names of functions, as a symbol.
This has two preferred values: `upcase' or `downcase'.
Actually, any name of a function which takes a string as an argument and
returns another string is acceptable."
  :type '(radio (function-item upcase)
		(function-item downcase)
                function)
  :group 'cldoc)

(defcustom cldoc-echo-area-use-multiline-p 'truncate-sym-name-if-fit
  "*Allow long cldoc messages to resize echo area display.
If value is `t', never attempt to truncate messages; complete symbol name
and function arglist or 1-line variable documentation will be displayed
even if echo area must be resized to fit.

If value is any non-nil value other than `t', symbol name may be truncated
if it will enable the function arglist or documentation string to fit on a
single line without resizing window.  Otherwise, behavior is just like
former case.

If value is nil, messages are always truncated to fit in a single line of
display in the echo area.  Function or variable symbol name may be
truncated to make more of the arglist or documentation string visible.

Non-nil values for this variable have no effect unless
`cldoc-echo-area-multiline-supported-p' is non-nil."
  :type '(radio (const :tag "Always" t)
                (const :tag "Never" nil)
                (const :tag "Yes, but truncate symbol names if it will\
 enable argument list to fit on one line" truncate-sym-name-if-fit))
  :group 'cldoc)

;;; No user options below here.

;; Non-nil if this version of emacs supports dynamically resizable echo areas.
(defvar cldoc-echo-area-multiline-supported-p
  (and (string-lessp "21" emacs-version)
       (save-match-data
         (numberp (string-match "^GNU Emacs" (emacs-version))))))

;; Commands after which it is appropriate to print in the echo area.
;; Cldoc does not try to print function arglists, etc. after just any command,
;; because some commands print their own messages in the echo area and these
;; functions would instantly overwrite them.  But self-insert-command as well
;; as most motion commands are good candidates.
;; This variable contains an obarray of symbols; do not manipulate it
;; directly.  Instead, use `cldoc-add-command' and `cldoc-remove-command'.
(defvar cldoc-message-commands nil)

;; This is used by cldoc-add-command to initialize cldoc-message-commands
;; as an obarray.
;; It should probably never be necessary to do so, but if you
;; choose to increase the number of buckets, you must do so before loading
;; this file since the obarray is initialized at load time.
;; Remember to keep it a prime number to improve hash performance.
(defvar cldoc-message-commands-table-size 31)

;; Bookkeeping; elements are as follows:
;;   0 - contains the last symbol read from the buffer.
;;   1 - contains the string last displayed in the echo area for that
;;       symbol, so it can be printed again if necessary without reconsing.
;;   2 - 'function if function args, 'variable if variable documentation.
(defvar cldoc-last-data (make-vector 3 nil))
(defvar cldoc-last-message nil)

;; Idle timers are supported in Emacs 19.31 and later.
(defvar cldoc-use-idle-timer-p (fboundp 'run-with-idle-timer))

;; cldoc's timer object, if using idle timers
(defvar cldoc-timer nil)

;; idle time delay currently in use by timer.
;; This is used to determine if cldoc-idle-delay is changed by the user.
(defvar cldoc-current-idle-delay cldoc-idle-delay)

;; Put minor mode string on the global minor-mode-alist.
;;;###autoload
(cond ((fboundp 'add-minor-mode)
       (add-minor-mode 'cldoc-mode 'cldoc-minor-mode-string))
      ((assq 'cldoc-mode (default-value 'minor-mode-alist)))
      (t
       (setq-default minor-mode-alist
                     (append (default-value 'minor-mode-alist)
                             '((cldoc-mode cldoc-minor-mode-string))))))


;;;###autoload
(defun cldoc-mode (&optional prefix)
  "*Enable or disable cldoc mode.
See documentation for the variable of the same name for more details.

If called interactively with no prefix argument, toggle current condition
of the mode.
If called with a positive or negative prefix argument, enable or disable
the mode, respectively."
  (interactive "P")
  (setq cldoc-last-message nil)
  (cond (cldoc-use-idle-timer-p
         (add-hook 'post-command-hook 'cldoc-schedule-timer)
         (add-hook 'pre-command-hook 'cldoc-pre-command-refresh-echo-area))
        (t
         ;; Use post-command-idle-hook if defined, otherwise use
         ;; post-command-hook.  The former is only proper to use in Emacs
         ;; 19.30; that is the first version in which it appeared, but it
         ;; was obsolesced by idle timers in Emacs 19.31.
         (add-hook (if (boundp 'post-command-idle-hook)
                       'post-command-idle-hook
                     'post-command-hook)
                   'cldoc-print-current-symbol-info t t)
         ;; quick and dirty hack for seeing if this is XEmacs
         (and (fboundp 'display-message)
              (add-hook 'pre-command-hook
                        'cldoc-pre-command-refresh-echo-area t t))))
  (setq cldoc-mode (if prefix
                       (>= (prefix-numeric-value prefix) 0)
                     (not cldoc-mode)))
  (and (interactive-p)
       (if cldoc-mode
           (message "cldoc-mode is enabled")
         (message "cldoc-mode is disabled")))
  (when (and cldoc-mode (and (boundp 'slime-autodoc-mode) slime-autodoc-mode))
    (slime-autodoc-mode -1))
  cldoc-mode)

;;;###autoload
(defun turn-on-cldoc-mode ()
  "Unequivocally turn on cldoc-mode (see variable documentation)."
  (interactive)
  (cldoc-mode 1))


;; Idle timers are part of Emacs 19.31 and later.
(defun cldoc-schedule-timer ()
  (or (and cldoc-timer
           (memq cldoc-timer timer-idle-list))
      (setq cldoc-timer
            (run-with-idle-timer cldoc-idle-delay t
                                 'cldoc-print-current-symbol-info)))

  ;; If user has changed the idle delay, update the timer.
  (cond ((not (= cldoc-idle-delay cldoc-current-idle-delay))
         (setq cldoc-current-idle-delay cldoc-idle-delay)
         (timer-set-idle-time cldoc-timer cldoc-idle-delay t))))

(defun cldoc-message (&rest args)
  (let ((omessage cldoc-last-message))
    (cond ((eq (car args) cldoc-last-message))
          ((or (null args)
               (null (car args)))
           (setq cldoc-last-message nil))
          ;; If only one arg, no formatting to do so put it in
          ;; cldoc-last-message so eq test above might succeed on
          ;; subsequent calls.
          ((null (cdr args))
           (setq cldoc-last-message (car args)))
          (t
           (setq cldoc-last-message (apply 'format args))))
    ;; In emacs 19.29 and later, and XEmacs 19.13 and later, all messages
    ;; are recorded in a log.  Do not put cldoc messages in that log since
    ;; they are Legion.
    (cond ((fboundp 'display-message)
           ;; XEmacs 19.13 way of preventing log messages.
           (cond (cldoc-last-message
                  (display-message 'no-log cldoc-last-message))
                 (omessage
                  (clear-message 'no-log))))
          (t
           ;; Emacs way of preventing log messages.
           (let ((message-log-max nil))
             (cond (cldoc-last-message
                    (message "%s" cldoc-last-message))
                   (omessage
                    (message nil)))))))
  cldoc-last-message)

;; This function goes on pre-command-hook for XEmacs or when using idle
;; timers in Emacs.  Motion commands clear the echo area for some reason,
;; which make cldoc messages flicker or disappear just before motion
;; begins.  This function reprints the last cldoc message immediately
;; before the next command executes, which does away with the flicker.
;; This doesn't seem to be required for Emacs 19.28 and earlier.
(defun cldoc-pre-command-refresh-echo-area ()
  (and cldoc-last-message
       (if (cldoc-display-message-no-interference-p)
           (cldoc-message cldoc-last-message)
         (setq cldoc-last-message nil))))

;; Decide whether now is a good time to display a message.
(defun cldoc-display-message-p ()
  (and (cldoc-display-message-no-interference-p)
       (cond (cldoc-use-idle-timer-p
              ;; If this-command is non-nil while running via an idle
              ;; timer, we're still in the middle of executing a command,
              ;; e.g. a query-replace where it would be annoying to
              ;; overwrite the echo area.
              (and (not this-command)
                   (symbolp last-command)
                   (intern-soft (symbol-name last-command)
                                cldoc-message-commands)))
             (t
              ;; If we don't have idle timers, this function is
              ;; running on post-command-hook directly; that means the
              ;; user's last command is still on `this-command', and we
              ;; must wait briefly for input to see whether to do display.
              (and (symbolp this-command)
                   (intern-soft (symbol-name this-command)
                                cldoc-message-commands)
                   (sit-for cldoc-idle-delay))))))

;; Check various conditions about the current environment that might make
;; it undesirable to print cldoc messages right this instant.
(defun cldoc-display-message-no-interference-p ()
  (and cldoc-mode
       (not executing-kbd-macro)
       (not (and (boundp 'edebug-active) edebug-active))
       ;; Having this mode operate in an active minibuffer/echo area causes
       ;; interference with what's going on there.
       (not cursor-in-echo-area)
       (not (eq (selected-window) (minibuffer-window)))))


(defun cldoc-print-current-symbol-info ()
  (and (cldoc-display-message-p)
       (let* ((current-symbol (cldoc-current-symbol))
              (current-fnsym  (cldoc-fnsym-in-current-sexp))
              (doc (cond ((eq current-symbol current-fnsym)
                          (or (cldoc-get-fnsym-args-string current-fnsym)
                              (cldoc-get-var-value current-symbol)))
                         (t
                          (or (cldoc-get-var-value current-symbol)
                              (cldoc-get-fnsym-args-string current-fnsym))))))
         (cldoc-message doc))))


(defun cldoc-get-fnsym-signature-from-lisp-process (sym)
  (cond
    ((fboundp 'slime-space)
     ;; from slime.el
     (when (and slime-space-information-p
                (slime-connected-p)
                (or (not (slime-busy-p))))
       (let ((result (slime-eval
                      `(swank:arglist-for-echo-area '(,(symbol-name sym))))))
         (when (stringp result) (cdar (read-from-string result))))))
    ;;((fboundp 'ilisp-arglist-message-lisp-space)
    ;; (cldoc-ilisp-signature))
    (t nil)))

;; Return a string containing the function parameter list, or 1-line
;; docstring if function is a subr and no arglist is obtainable from the
;; docstring or elsewhere.
(defun cldoc-get-fnsym-args-string (sym)
  (let* ((entry (intern-soft (downcase (symbol-name sym)) cl-operator-signatures))
         (signature (if (and entry (boundp entry))
                        (symbol-value entry)
                        (cldoc-get-fnsym-signature-from-lisp-process sym))))
    (setq doc
          (cond
            ((null signature) nil)
            ((stringp signature)
             (cldoc-docstring-format-sym-doc sym signature))
            (t
             (let* ((tail (member '=> signature))
                    (result (cldoc-function-resultstring-format (cdr tail)))
                    (args (cldoc-function-argstring-format (ldiff signature tail)))
                    (args-and-result (if tail
                                       (format "%s => %s" args result)
                                       (format "%s" args))))
               (cldoc-docstring-format-sym-doc sym args-and-result)))))))

(defun cldoc-function-resultstring-format (results)
  (let (str)
    (do* ((results results (cdr results))
          result)
         ((endp results))
      (setq result (funcall cldoc-argument-case (symbol-name (car results))))
      (if str
          (setq str (format "%s, %s" str result))
          (setq str (format "%s" result))))
    str))


;; Return a string containing a brief (one-line) documentation string for
;; the variable.
(defun cldoc-get-var-value (sym)
  (cond
    ((fboundp 'slime-autodoc) ;; from slime.el
     (let* ((name (slime-autodoc-global-at-point))
            (value (when (and name
                              slime-space-information-p
                              (slime-connected-p)
                              (or (not (slime-busy-p)))
                              (slime-global-variable-name-p name))
                     (slime-eval `(swank:variable-desc-for-echo-area ,name)))))
       value))
    (t nil)))

(defun cldoc-last-data-store (symbol doc type)
  (aset cldoc-last-data 0 symbol)
  (aset cldoc-last-data 1 doc)
  (aset cldoc-last-data 2 type))

;; Note that any leading `*' in the docstring (which indicates the variable
;; is a user option) is removed.
(defun cldoc-docstring-first-line (doc)
  (and (stringp doc)
       (substitute-command-keys
        (save-match-data
          (let ((start (if (string-match "^\\*" doc) (match-end 0) 0)))
            (cond ((string-match "\n" doc)
                   (substring doc start (match-beginning 0)))
                  ((zerop start) doc)
                  (t (substring doc start))))))))

;; If the entire line cannot fit in the echo area, the symbol name may be
;; truncated or eliminated entirely from the output to make room for the
;; description.
(defun cldoc-docstring-format-sym-doc (sym doc)
  (save-match-data
    (let* ((name (symbol-name sym))
           (ea-multi (and cldoc-echo-area-multiline-supported-p
                          cldoc-echo-area-use-multiline-p))
           ;; Subtract 1 from window width since emacs will not write
           ;; any chars to the last column, or in later versions, will
           ;; cause a wraparound and resize of the echo area.
           (ea-width (1- (window-width (minibuffer-window))))
           (strip (- (+ (length name) (length ": ") (length doc)) ea-width)))
      (cond ((or (<= strip 0)
                 (eq ea-multi t)
                 (and ea-multi (> (length doc) ea-width)))
             (format "%s: %s" sym doc))
            ((> (length doc) ea-width)
             (substring (format "%s" doc) 0 ea-width))
            ((>= strip (length name))
             (format "%s" doc))
            (t
             ;; Show the end of the partial symbol name, rather
             ;; than the beginning, since the former is more likely
             ;; to be unique given package namespace conventions.
             (setq name (substring name strip))
             (format "%s: %s" name doc))))))


(defun cldoc-fnsym-in-current-sexp ()
  (let ((p (point)))
    (cldoc-beginning-of-sexp)
    (prog1
        ;; Don't do anything if current word is inside a string.
        (if (= (or (char-after (1- (point))) 0) ?\")
            nil
          (cldoc-current-symbol))
      (goto-char p))))

(defun cldoc-beginning-of-sexp ()
  (let ((parse-sexp-ignore-comments t))
    (condition-case err
        (while (progn
                 (forward-sexp -1)
                 (or (= (or (char-after (1- (point)))) ?\")
                     (> (point) (point-min)))))
      (error nil))))

(defun cldoc-current-symbol ()
  (let ((c (char-after (point))))
    (and c
         (memq (char-syntax c) '(?w ?_))
         (intern (current-word)))))

;; Do indirect function resolution if possible.
(defun cldoc-symbol-function (fsym)
  (let ((defn (and (fboundp fsym)
                   (symbol-function fsym))))
    (and (symbolp defn)
         (condition-case err
             (setq defn (indirect-function fsym))
           (error (setq defn nil))))
    defn))

(defun cldoc-function-arglist (fn)
  (let* ((prelim-def (cldoc-symbol-function fn))
         (def (if (eq (car-safe prelim-def) 'macro)
                  (cdr prelim-def)
                prelim-def))
         (arglist (cond ((null def) nil)
                        ((byte-code-function-p def)
                         (cond ((fboundp 'compiled-function-arglist)
                                (funcall 'compiled-function-arglist def))
                               (t
                                (aref def 0))))
                        ((eq (car-safe def) 'lambda)
                         (nth 1 def))
                        (t t))))
    arglist))

(defun cldoc-function-argstring (fn)
  (cldoc-function-argstring-format (cldoc-function-arglist fn)))

(defun cldoc-function-arg-format (arg)
  (typecase arg
    (symbol (if (memq arg '(&allow-other-keys &aux &body &environment &key &optional
                            &rest &whole))
                (symbol-name arg)
                (funcall cldoc-argument-case (symbol-name arg))))
    (string (if (member arg '("&allow-other-keys" "&aux" "&body" "&environment"
                              "&key" "&optional" "&rest" "&whole"))
                arg
                (funcall cldoc-argument-case (symbol-name arg))))
    (cons (cldoc-function-argstring-format arg))
    (t (format "%s" arg))))

(defun cldoc-function-argstring-format (arglist)
  (concat "(" (mapconcat #'cldoc-function-arg-format arglist " ") ")"))


;; Alist of predicate/action pairs.
;; Each member of the list is a sublist consisting of a predicate function
;; used to determine if the arglist for a function can be found using a
;; certain pattern, and a function which returns the actual arglist from
;; that docstring.
;;
;; The order in this table is significant, since later predicates may be
;; more general than earlier ones.
;;
;; Compiler note for Emacs/XEmacs versions which support dynamic loading:
;; these functions will be compiled to bytecode, but can't be lazy-loaded
;; even if you set byte-compile-dynamic; to do that would require making
;; them named top-level defuns, which is not particularly desirable either.
(defvar cldoc-function-argstring-from-docstring-method-table
  (list
   ;; Try first searching for args starting with symbol name.
   ;; This is to avoid matching parenthetical remarks in e.g. sit-for.
   (list (function (lambda (doc fn)
                     (string-match (format "^(%s[^\n)]*)$" fn) doc)))
         (function (lambda (doc)
                     ;; end does not include trailing ")" sequence.
                     (let ((end (- (match-end 0) 1)))
                       (if (string-match " +" doc (match-beginning 0))
                           (substring doc (match-end 0) end)
                         "")))))

   ;; Try again not requiring this symbol name in the docstring.
   ;; This will be the case when looking up aliases.
   (list (function (lambda (doc fn)
                     ;; save-restriction has a pathological docstring in
                     ;; Emacs/XEmacs 19.
                     (and (not (eq fn 'save-restriction))
                          (string-match "^([^\n)]+)$" doc))))
         (function (lambda (doc)
                     ;; end does not include trailing ")" sequence.
                     (let ((end (- (match-end 0) 1)))
                       (and (string-match " +" doc (match-beginning 0))
                            (substring doc (match-end 0) end))))))

   ;; Emacs subr docstring style:
   ;;   (fn arg1 arg2 ...): description...
   (list (function (lambda (doc fn)
                     (string-match "^([^\n)]+):" doc)))
         (function (lambda (doc)
                     ;; end does not include trailing "):" sequence.
                     (let ((end (- (match-end 0) 2)))
                       (and (string-match " +" doc (match-beginning 0))
                            (substring doc (match-end 0) end))))))

   ;; XEmacs subr docstring style:
   ;;   "arguments: (arg1 arg2 ...)
   (list (function (lambda (doc fn)
                     (string-match "^arguments: (\\([^\n)]+\\))" doc)))
         (function (lambda (doc)
                     ;; also skip leading paren, but the first word is
                     ;; actually an argument, not the function name.
                     (substring doc (match-beginning 1) (match-end 1)))))

   ;; This finds the argstring for `condition-case'.  Any others?
   (list (function (lambda (doc fn)
                     (string-match
                      (format "^Usage looks like \\((%s[^\n)]*)\\)\\.$" fn)
                      doc)))
         (function (lambda (doc)
                     ;; end does not include trailing ")" sequence.
                     (let ((end (- (match-end 1) 1)))
                       (and (string-match " +" doc (match-beginning 1))
                            (substring doc (match-end 0) end))))))

   ;; This finds the argstring for `setq-default'.  Any others?
   (list (function (lambda (doc fn)
                     (string-match (format "^[ \t]+\\((%s[^\n)]*)\\)$" fn)
                                   doc)))
         (function (lambda (doc)
                     ;; end does not include trailing ")" sequence.
                     (let ((end (- (match-end 1) 1)))
                       (and (string-match " +" doc (match-beginning 1))
                            (substring doc (match-end 0) end))))))

   ;; This finds the argstring for `start-process'.  Any others?
   (list (function (lambda (doc fn)
                     (string-match "^Args are +\\([^\n]+\\)$" doc)))
         (function (lambda (doc)
                     (substring doc (match-beginning 1) (match-end 1)))))

   ;; These common subrs don't have arglists in their docstrings.  So cheat.
   (list (function (lambda (doc fn)
                     (memq fn '(and or list + -))))
         (function (lambda (doc)
                     ;; The value nil is a placeholder; otherwise, the
                     ;; following string may be compiled as a docstring,
                     ;; and not a return value for the function.
                     ;; In interpreted lisp form they are
                     ;; indistinguishable; it only matters for compiled
                     ;; forms.
                     nil
                     "&rest args")))
   ))

(defun cldoc-function-argstring-from-docstring (fn)
  (let ((docstring (documentation fn 'raw))
        (table cldoc-function-argstring-from-docstring-method-table)
        (doc nil)
        (doclist nil))
    (save-match-data
      (while table
        (cond ((funcall (car (car table)) docstring fn)
               (setq doc (funcall (car (cdr (car table))) docstring))
               (setq table nil))
              (t
               (setq table (cdr table)))))

      (cond ((not (stringp doc))
             nil)
            ((string-match "&" doc)
             (let ((p 0)
                   (l (length doc)))
               (while (< p l)
                 (cond ((string-match "[ \t\n]+" doc p)
                        (setq doclist
                              (cons (substring doc p (match-beginning 0))
                                    doclist))
                        (setq p (match-end 0)))
                       (t
                        (setq doclist (cons (substring doc p) doclist))
                        (setq p l))))
               (cldoc-function-argstring-format (nreverse doclist))))
            (t
             (concat "(" (funcall cldoc-argument-case doc) ")"))))))


;; When point is in a sexp, the function args are not reprinted in the echo
;; area after every possible interactive command because some of them print
;; their own messages in the echo area; the cldoc functions would instantly
;; overwrite them unless it is more restrained.
;; These functions do display-command table management.

(defun cldoc-add-command (&rest cmds)
  (or cldoc-message-commands
      (setq cldoc-message-commands
            (make-vector cldoc-message-commands-table-size 0)))

  (let (name sym)
    (while cmds
      (setq name (car cmds))
      (setq cmds (cdr cmds))

      (cond ((symbolp name)
             (setq sym name)
             (setq name (symbol-name sym)))
            ((stringp name)
             (setq sym (intern-soft name))))

      (and (symbolp sym)
           (fboundp sym)
           (set (intern name cldoc-message-commands) t)))))

(defun cldoc-add-command-completions (&rest names)
  (while names
      (apply 'cldoc-add-command
             (all-completions (car names) obarray 'fboundp))
      (setq names (cdr names))))

(defun cldoc-remove-command (&rest cmds)
  (let (name)
    (while cmds
      (setq name (car cmds))
      (setq cmds (cdr cmds))

      (and (symbolp name)
           (setq name (symbol-name name)))

      (if (fboundp 'unintern)
          (unintern name cldoc-message-commands)
        (let ((s (intern-soft name cldoc-message-commands)))
          (and s
               (makunbound s)))))))

(defun cldoc-remove-command-completions (&rest names)
  (while names
    (apply 'cldoc-remove-command
           (all-completions (car names) cldoc-message-commands))
    (setq names (cdr names))))


;; Prime the command list.
(cldoc-add-command-completions
 "backward-" "beginning-of-" "delete-other-windows" "delete-window"
 "end-of-" "forward-" "indent-for-tab-command" "goto-" "mouse-set-point"
 "next-" "other-window" "previous-" "recenter" "scroll-"
 "self-insert-command" "split-window-"
 "up-list" "down-list")


(defvar cl-operator-signatures (make-vector 67 0))

;; note
;; these symbols are used,  => =>|
(mapcar (lambda (entry)
          (let ((symbol (intern (symbol-name (car entry)) cl-operator-signatures)))
            (set symbol (cdr entry))))
        
        '(;; evaluation and compilation
          (lambda . "lambda-list [[declaration* | documentation]] form* => function")
          (compile function-name-or-nil &optional lambda-expression-or-function => function warnings-p failure-p)
          (eval form => result*)
          (eval-when . "(situation*) form* => result*")
          (load-time-value . "form &optional read-only-p => object")
          (quote object => object)
          (compiler-macro-function name &optional (environment nil) => function)
          (define-compiler-macro . "name lambda-list [[declaration* | documentation]] form* => name")
          (defmacro . "name lambda-list [[declaration* | documentation]] form* => name")
          (macro-function symbol &optional (environment nil) => macro-function-or-nil)
          (macroexpand form &optional (environment nil) => expansion expanded-p)
          (macroexpand-1 form &optional (environment nil) => expansion expanded-p)
          (define-symbol-macro . "symbol expansion => symbol")
          (symbol-macrolet . "((symbol expansion)*) declaration* form* => result*")
          (proclaim declaration-specifier => implementation-dependent)
          (declaim . "declaration-specifier* => implementation-dependent")
          (locally declaration* form* => result*)
          (the value-type form => result*)
          (special-operator-p symbol => generalized-boolean)
          (constantp form &optional (environment nil) => generalized-boolean)

          
          ;; types and classes
          (coerce object result-type => result)
          (deftype . "name lambda-list [[declaration* | documentation]] form* => name")
          (subtypep subtype type &optional (environment nil) => subtype-p valid-p)
          (typep object type-specifier &optional (environment nil) => generalized-boolean)
          (type-error-datum condition => datum)
          (type-error-expected-type condition => expected-type)


          ;; data and control flow
          (apply function &rest args+ => result*)
          (defun . "function-name lambda-list [[declaration* | documentation]] form* => function-name")
          (fdefinition function-name => definition)
          (fboundp function-name => generalized-boolean)
          (fmakunbound function-name => function-name)
          (flet . "((function-name lambda-list [[local-declaration* | local-documentation]] local-form*)*) declaration* form* => result*")
          (labels . "((function-name lambda-list [[local-declaration* | local-documentation]] local-form*)*) declaration* form* => result*")
          (macrolet . "((name lambda-list [[local-declaration* | local-documentation]] local-form*)*) declaration* form* => result*")

          (funcall function &rest args => result*)
          (function . "function-name-or-lambda-expression => function")
          (function-lambda-expression function => lambda-expression closure-p name)
          (functionp object => generalized-boolean)
          (compiled-function-p object => generalized-boolean)
          (defconstant . "name initial-value [documentation] => name")
          (defparameter . "name initial-value [documentation] => name")
          (defvar . "name [initial-value [documentation]] => name")
          (destructuring-bind . "destructuring-lambda-list expression declaration* form* => result*")
          (let . "({var | (var [init-form])}*) declaration* form* => result*")
          (let* . "({var | (var [init-form])}*) declaration* form* => result*")
          (progv . "symbols values form* => result*")
          (setq . "{pair}* => result")
          (psetq . "{pair}* => nil")
          (block . "name-symbol form* => result*")
          (catch . "tag-form form* => result*")
          (go . "tag =>|")
          (return-from . "name [result-form] =>|")
          (return . "[result-form] =>|")
          (tagbody . "{tag | statement}* => nil")
          (throw . "tag-form result-form =>|")
          (unwind-protect . "protected-form cleanup-form* => result*")
          (not x => boolean)
          (eq x y => generalized-boolean)
          (eql x y => generalized-boolean)
          (equal x y => generalized-boolean)
          (equalp x y => generalized-boolean)
          (identity object => object)
          (complement function => complement-function)
          (constantly value => function-constantly-returning-value)
          (every predicate &rest sequences+ => generalized-boolean)
          (some predicate &rest sequences+ => result)
          (notevery predicate &rest sequences+ => generalized-boolean)
          (notany predicate &rest sequences+ => generalized-boolean)
          (and . "form* => result*")
          (cond . "{(test-form form*)}* => result*")
          (if . "test-form then-form [else-form] => result*")
          (or . "form* => results*")
          (when . "test-form form* => result*")
          (unless . "test-form form* => result*")
          (case . "keyform {(keys form*)}* [({otherwise | t} form*)] => result*")
          (ccase . "keyplace {(keys form*)}* => result*")
          (ecase . "keyform {(keys form*)}* => result*")
          (typecase . "keyform {(type form*)}* [({otherwise | t} form*)] => result*")
          (ctypecase . "keyplace {(type form*)}* => result*")
          (etypecase . "keyform {(type form*)}* => result*")
          (multiple-value-bind . "(var*) values-form declaration* form* => result*")
          (multiple-value-call . "function-form form* => result*")
          (multiple-value-list . "form => list")
          (multiple-value-prog1 . "first-form form* => first-form-results")
          (multiple-value-setq . "vars form => result")
          (values &rest object => object*)
          (values-list list => element*)
          (nth-value . "n-form form => object")
          (prog . "({var | (var [init-form])}*) declaration* {tag | statement}* => result*")
          (prog* . "({var | (var [init-form])}*) declaration* {tag | statement}* => result*")
          (prog1 . "first-form form* => primary-value-of-evaluated-first-form")
          (prog2 . "first-form second-form form* => primary-value-of-evaluated-second-form")
          (progn . "form* => result*")
          (define-modify-macro . "name lambda-list function [documentation] => name")
          ;;(defsetf . "access-fn update-fn [documentation] => access-fn")
          ;;(defsetf . " access-fn lambda-list (store-variable*) [[declaration* | documentation]] form* => access-fn")
          (define-setf-expander . "access-fn lambda-list [[declaration* | documentation]] form* => access-fn")
          (get-setf-expansion place &optional (environment nil) => vars vals store-vars writer-form reader-form)
          (setf . "{place newvalue}* => result*")
          (psetf . "{place newvalue}* => nil")
          (shiftf . "place+ newvalue => old-value-1")
          (rotatef . "place* => nil")

          
          ;; iteration
          (do . "({var | (var [init-form [step-form]])}*) (end-test-form result-form*) declaration* {tag | statement}* => result*")
          (do* . "({var | (var [init-form [step-form]])}*) (end-test-form result-form*) declaration* {tag | statement}* => result*")
          (dotimes . "(var count-form [result-form]) declaration* {tag | statement}* => result*")
          (dolist . "(var list-form [result-form]) declaration* {tag | statement}* => result*")
          ;;(loop . "compound-form* => result*")
          ;;(loop . "[name-clause] {variable-clause}* {main-clause}* => result*")
          (loop-finish . " =>|")


          ;; objects
          (function-keywords method => keys allow-other-keys-p)
          (ensure-generic-function function-name &key argument-precedence-order declare documentation environment generic-function-class lambda-list method-class method-combination => generic-function)
          (allocate-instance class &rest initargs &key &allow-other-keys => new-instance)
          (reinitialize-instance instance &rest initargs &key &allow-other-keys => instance)
          (shared-initialize instance slot-names &rest initargs &key &allow-other-keys => instance)
          (update-instance-for-different-class previous current &rest initargs &key &allow-other-keys => implementation-dependent)
          (update-instance-for-redefined-class instance added-slots discarded-slots property-list &rest initargs &key &allow-other-keys => result*)
          (change-class instance new-class &key &allow-other-keys => instance)
          (slot-boundp instance slot-name => generalized-boolean)
          (slot-exists-p object slot-name => generalized-boolean)
          (slot-makunbound instance slot-name => instance)
          (slot-missing class object slot-name operation &optional new-value => result*)
          (slot-unbound class instance slot-name => result*)
          (slot-value object slot-name => value)
          (method-qualifiers method => qualifiers)
          (no-applicable-method generic-function &rest function-arguments => result*)
          (no-next-method generic-function method &rest args => result*)
          (remove-method generic-function method => generic-function)
          (make-instance class-designator &rest initargs &key &allow-other-keys => instance)
          (make-instances-obsolete class-designator => class)
          (make-load-form object &optional (environment nil) => creation-form \[initialization-form\])
          (make-load-form-saving-slots object &key slot-names (environment nil) => creation-form initialization-form)
          (with-accessors . "(slot-entry*) instance-form declaration* form* => result*")
          (with-slots . "({slot-name | (variable-name slot-name)}*) instance-form declaration* form* => result*")
          (defclass . "class-name ({superclass-name}*) ({slot-specifier}*) [[class-option]] => new-class")
          (defgeneric . "function-name gf-lambda-list [[option | {method-description}*]] => new-generic)")
          (defmethod . "function-name {method-qualifier}* specialized-lambda-list [[declaration* | documentation]] form* => new-method")
          (find-class symbol &optional (errorp t) environment => class)
          (next-method-p => generalized-boolean)
          (call-method method &optional next-method-list => result*)
          (make-method form => method-object)
          (call-next-method &rest args => result*)
          (compute-applicable-methods generic-function function-arguments => methods)
          ;;(define-method-combination . "name [[short-form-option]] => name")
          ;;(define-method-combination . "name lambda-list (method-group-specifier*) [(:arguments . args-lambda-list)] [(:generic-function generic-function-symbol)] [[declaration* | documentation]] form* => name")
          (find-method generic-function method-qualifiers specializers &optional (errorp t) => method)
          (add-method generic-function method => generic-function)
          (initialize-instance instance &rest initargs &key &allow-other-keys => instance)
          (class-name class => name)
          (class-of object => class)
          (unbound-slot-instance condition => instance)

          ;; structures
          (defstruct . "name-and-options [documentation] {slot-description}* => structure-name")
          (copy-structure structure => copy)


          ;; conditions
          (cell-error-name condition => name)
          (assert . "test-form [(place*) [datum-form argument-form*]] => nil")
          (error datum &rest arguments =>|)
          (cerror continue-format-control datum &rest arguments => nil)
          (check-type . "place typespec [string] => nil")
          (invalid-method-error method format-control &rest args => implementation-dependent)
          (method-combination-error format-control &rest args => implementation-dependent)
          (signal datum &rest arguments => nil)
          (simple-condition-format-control condition => format-control)
          (simple-condition-format-arguments condition => format-arguments)
          (warn datum &rest arguments => nil)
          (invoke-debugger condition =>|)
          (break &optional (format-control *implementation-dependent-format-control*) &rest format-arguments => nil)
          (handler-bind . "({(type handler)}*) form* => result*")
          (handler-case . "expression [[{error-clause}* | no-error-clause]] => result*
clause::= error-clause | no-error-clause 
error-clause::= (typespec ([var]) declaration* form*) 
no-error-clause::= (:no-error lambda-list declaration* form*)")
          (ignore-errors . "form* => result*")
          (define-condition . "name (parent-type*) ({slot-spec}*) option* => name")
          (make-condition type &rest slot-initializations => condition)
          (compute-restarts &optional (condition nil) => restarts)
          (find-restart identifier &optional (condition nil) => restart)
          (invoke-restart restart-designator &rest arguments => result*)
          (invoke-restart-interactively restart-designator => result*)
          (restart-bind . "({(name function {key-val-pair}*)}) form* => result*")
          (restart-case . "restartable-form {clause} => result*")
          (restart-name restart => name)
          (with-condition-restarts . "condition-form restarts-form form* => result*")
          (with-simple-restart . "(name format-control format-argument*) form* => result*")
          (abort &optional (condition nil) =>|)
          (continue &optional (condition nil) => nil)
          (muffle-warning &optional (condition nil) =>|)
          (store-value value &optional (condition nil) => nil)
          (use-value value &optional (condition nil) => nil)


          ;; symbols
          (symbolp object => generalized-boolean)
          (keywordp object => generalized-boolean)
          (make-symbol name-string => new-symbol)
          (copy-symbol symbol &optional (copy-properties nil) => new-symbol)
          (gensym &optional string-or-non-negative-integer => new-symbol)
          (gentemp &optional (prefix "T") (package *package*) => new-symbol)
          (symbol-function symbol => contents)
          (symbol-name symbol => name)
          (symbol-package symbol => package-or-nil)
          (symbol-plist symbol => plist)
          (symbol-value symbol => value)
          (get symbol indicator &optional (default nil) => value)
          (remprop symbol indicator => generalized-boolean)
          (boundp symbol => generalized-boolean)
          (makunbound symbol => symbol)
          (set symbol value => value)


          ;; packages
          (export designator-for-a-list-of-symbols &optional (package *package*) => t)
          (find-symbol string &optional (package *package*) => symbol status)
          (find-package string-designator-or-package => package)
          (find-all-symbols string-designator => symbols)
          (import designator-for-a-list-of-symbols &optional (package *package*))
          (list-all-packages => packages)
          (rename-package package new-name &optional (new-nicknames '()) => package-object)
          (shadow symbol-names &optional (package *package*) => t)
          (shadowing-import designator-for-a-list-of-symbols &optional (package *package*) => t)
          (delete-package package-designator => generalized-boolean)
          (make-package package-name &key (nicknames '()) (use *implementation-defined-use-list*) => package)
          (with-package-iterator . "(name package-list-form &rest symbol-types) declaration* form* => result*")
          (unexport designator-for-a-list-of-symbols &optional (package *package*) => t)
          (unintern symbol &optional (package *package*) => generalized-boolean)
          (in-package . "name => package")
          (unuse-package packages-to-unuse &optional (package *package*) => t)
          (use-package packages-to-use &optional (package *package*) => t)
          (defpackage . "defined-package-name [[option]] => package
option::= (:nicknames nickname*)* |  
          (:documentation string) |  
          (:use package-name*)* |  
          (:shadow {symbol-name}*)* |  
          (:shadowing-import-from package-name {symbol-name}*)* |  
          (:import-from package-name {symbol-name}*)* |  
          (:export {symbol-name}*)* |  
          (:intern {symbol-name}*)* |  
          (:size integer) ")
          (do-symbols . "(var [package [result-form]]) declaration* {tag | statement}* => result*")
          (do-external-symbols . "(var [package [result-form]]) declaration* {tag | statement}* => result*")
          (do-all-symbols . "(var [result-form]) declaration* {tag | statement}* => result*")
          (intern string &optional (package *package*) => symbol status)
          (package-name package-designator => name)
          (package-nicknames package-designator => nicknames)
          (package-shadowing-symbols package-designator => symbols)
          (package-use-list package-designator => use-list)
          (package-used-by-list package-designator => used-by-list)
          (packagep object => generalized-boolean)
          (package-error-package condition => package)


          ;; numbers
          (= &rest numbers+ => generalized-boolean)
          (/= &rest numbers+ => generalized-boolean)
          (< &rest numbers+ => generalized-boolean)
          (> &rest numbers+ => generalized-boolean)
          (<= &rest numbers+ => generalized-boolean)
          (>= &rest numbers+ => generalized-boolean)
          (max &rest reals+ => max-real)
          (min &rest reals+ => min-real)
          (minusp real => generalized-boolean)
          (plusp real => generalized-boolean)
          (zerop number => generalized-boolean)
          (floor number &optional (divisor 1) => quotient remainder)
          (ffloor number &optional (divisor 1) => quotient remainder)
          (ceiling number &optional (divisor 1) => quotient remainder)
          (fceiling number &optional (divisor 1) => quotient remainder)
          (truncate number &optional (divisor 1) => quotient remainder)
          (ftruncate number &optional (divisor 1) => quotient remainder)
          (round number &optional (divisor 1) => quotient remainder)
          (fround number &optional (divisor 1) => quotient remainder)
          (sin radians => number)
          (cos radians => number)
          (tan radians => number)
          (asin number => radians)
          (acos number => radians)
          (atan number1 &optional number2 => radians)
          (sinh number => result)
          (cosh number => result)
          (tanh number => result)
          (asinh number => result)
          (acosh number => result)
          (atanh number => result)
          (* &rest numbers => product)
          (+ &rest numbers => sum)
          ;;(- number => negation)
          ;;(- minuend &rest subtrahends+ => difference)
          ;;(/ number => reciprocal)
          ;;(/ numerator &rest denominators+ => quotient)
          (1+ number => successor)
          (1- number => predecessor)
          (abs number => absolute-value)
          (evenp integer => generalized-boolean)
          (oddp integer => generalized-boolean)
          (exp number => result)
          (expt base-number power-number => result)
          (gcd &rest integers => greatest-common-denominator)
          (incf . "place [delta-form] => new-value")
          (decf . "place [delta-form] => new-value")
          (lcm &rest integers => least-common-multiple)
          (log number &optional (base *E-base-of-the-natural-logarithms*) => logarithm)
          (mod number divisor => modulus)
          (rem number divisor => remainder)
          (signum number => signed-prototype)
          (sqrt number => root)
          (isqrt natural => natural-root)
          (make-random-state &optional (state nil) => new-state)
          (random limit &optional (random-state *random-state*) => random-number)
          (random-state-p object => generalized-boolean)
          (numberp object => generalized-boolean)
          (cis radians => number)
          (complex realpart &optional (imagpart (coerce 0 (type-of realpart))) => complex)
          (complexp object => generalized-boolean)
          (conjugate number => conjugate)
          (phase number => phase)
          (realpart number => real)
          (imagpart number => real)
          (upgraded-complex-part-type typespec &optional (environment nil) => upgraded-typespec)
          (realp object => generalized-boolean)
          (numerator rational => numerator)
          (denominator rational => denominator)
          (rational number => rational)
          (rationalize number => rational)
          (rationalp object => generalized-boolean)
          (ash integer count => shifted-integer)
          (integer-length integer => number-of-bits)
          (integerp object => generalized-boolean)
          (parse-integer string &key (start 0) (end nil) (radix 10) junk-allowed => integer pos)
          (boole op integer-1 integer-2 => result-integer)
          (logand &rest integers => result-integer)
          (logandc1 integer-1 integer-2 => result-integer)
          (logandc2 integer-1 integer-2 => result-integer)
          (logeqv &rest integers => result-integer)
          (logior &rest integers => result-integer)
          (lognand integer-1 integer-2 => result-integer)
          (lognor integer-1 integer-2 => result-integer)
          (lognot integer => result-integer)
          (logorc1 integer-1 integer-2 => result-integer)
          (logorc2 integer-1 integer-2 => result-integer)
          (logxor &rest integers => result-integer)
          (logbitp index integer => generalized-boolean)
          (logcount integer => number-of-on-bits)
          (logtest integer-1 integer-2 => generalized-boolean)
          (byte size position => bytespec)
          (byte-size bytespec => size)
          (byte-position bytespec => position)
          (deposit-field newbyte bytespec integer => result-integer)
          (dpb newbyte bytespec integer => result-integer)
          (ldb bytespec integer => byte)
          (ldb-test bytespec integer => generalized-boolean)
          (mask-field bytespec integer => masked-integer)
          (decode-float float => significand exponent sign)
          (scale-float float integer => scaled-float)
          (float-radix float => float-radix)
          (float-sign float-1 &optional (float-2 (float 1 float-1)) => signed-float)
          (float-digits float => digits1)
          (float-precision float => digits2)
          (integer-decode-float float => significand exponent integer-sign)
          (float number &optional prototype => float)
          (floatp object)
          (arithmetic-error-operands condition => operands)
          (arithmetic-error-operation condition => operation)

          ;; characters
          (char= &rest characters+ => generalized-boolean)
          (char/= &rest characters+ => generalized-boolean)
          (char< &rest characters+ => generalized-boolean)
          (char> &rest characters+ => generalized-boolean)
          (char<= &rest characters+ => generalized-boolean)
          (char>= &rest characters+ => generalized-boolean)
          (char-equal &rest characters+ => generalized-boolean)
          (char-not-equal &rest characters+ => generalized-boolean)
          (char-lessp &rest characters+ => generalized-boolean)
          (char-greaterp &rest characters+ => generalized-boolean)
          (char-not-greaterp &rest characters+ => generalized-boolean)
          (char-not-lessp &rest characters+ => generalized-boolean)
          (character character-designator => denoted-character)
          (characterp object => generalized-boolean)
          (alpha-char-p character => generalized-boolean)
          (alphanumericp character => generalized-boolean)
          (digit-char weight &optional (radix 10) => char)
          (digit-char-p char &optional (radix 10) => weight)
          (graphic-char-p char => generalized-boolean)
          (standard-char-p character => generalized-boolean)
          (char-upcase character => corresponding-character)
          (char-downcase character => corresponding-character)
          (upper-case-p character => generalized-boolean)
          (lower-case-p character => generalized-boolean)
          (both-case-p character => generalized-boolean)
          (char-code character => code)
          (char-int character => integer)
          (code-char code => char-p)
          (char-name character => name)
          (name-char name => character-or-nil)

          
          ;; conses
          (cons car cdr => cons)
          (consp object => generalized-boolean)
          (atom object => generalized-boolean)
          (rplaca cons object => cons)
          (rplacd cons object => cons)
          (car list => car-of-list)
          (cdr list => cdr-of-list)
          (copy-tree tree => new-tree)
          (sublis alist tree &key key test test-not => new-tree)
          (nsublis alist tree &key key test test-not => new-tree)
          (subst new old tree &key key test test-not => new-tree)
          (subst-if new predicate tree &key key => new-tree)
          (subst-if-not new predicate tree &key key => new-tree)
          (nsubst new old tree &key key test test-not => new-tree)
          (nsubst-if new predicate tree &key key => new-tree)
          (nsubst-if-not new predicate tree &key key => new-tree)
          (tree-equal tree-1 tree-2 &key test test-not => generalized-boolean)
          (copy-list list => copy)
          (list &rest objects => list)
          (list* &rest objects+ => result)
          (list-length list => length)
          (listp object => generalized-boolean)
          (make-list size &key (initial-element nil) => list)
          (push . "item place => new-place-value")
          (pop . "place => element")
          (nth n list => object)
          (endp list => generalized-boolean)
          (null object => boolean)
          (nconc &rest lists => concatenated-list)
          (append &rest lists => result)
          (revappend list tail => result-list)
          (nreconc list tail => result-list)
          (butlast list &optional (n 1) => result-list)
          (nbutlast list &optional (n 1) => result-list)
          (last list &optional (n 1) => tail)
          (ldiff list possible-tail => result-list)
          (tailp possible-tail list => generalized-boolean)
          (nthcdr n list => tail)
          (rest list => tail)
          (member item list &key key test test-not => tail)
          (member-if predicate list &key key => tail)
          (member-if-not predicate list &key key => tail)
          (mapc function &rest lists+ => list-1)
          (mapcar function &rest lists+ => result-list)
          (mapcan function &rest lists+ => concatenated-results)
          (mapl function &rest lists+ => list-1)
          (maplist function &rest lists+ => result-list)
          (mapcon function &rest lists+ => concatenated-results)
          (acons key datum alist => new-alist)
          (assoc item alist &key key test test-not => entry)
          (assoc-if predicate alist &key key => entry)
          (assoc-if-not predicate alist &key key => entry)
          (copy-alist alist => new-alist)
          (pairlis keys data &optional (alist '()) => new-alist)
          (rassoc item alist &key key test test-not => entry)
          (rassoc-if predicate alist &key key => entry)
          (rassoc-if-not predicate alist &key key => entry)
          (get-properties plist indicator-list => indicator value tail)
          (getf plist indicator &optional (default nil) => value)
          (remf place indicator => generalized-boolean)
          (intersection list-1 list-2 &key key test test-not => result-list)
          (nintersection list-1 list-2 &key key test test-not => result-list)
          (adjoin item list &key key test test-not => new-list)
          (pushnew item place &key key test test-not => new-place-value)
          (set-difference list-1 list-2 &key key test test-not => result-list)
          (nset-difference list-1 list-2 &key key test test-not => result-list)
          (set-exclusive-or list-1 list-2 &key key test test-not => result-list)
          (nset-exclusive-or list-1 list-2 &key key test test-not => result-list)
          (subsetp list-1 list-2 &key key test test-not => generalized-boolean)
          (union list-1 list-2 &key key test test-not => result-list)
          (nunion list-1 list-2 &key key test test-not => result-list)

          ;; arrays
          (make-array dimensions &key (element-type t) initial-element initial-contents (adjustable nil) (fill-pointer nil) (displaced-to nil) (displaced-index-offset 0) => new-array)
          (adjust-array array new-dimensions &key element-type initial-element initial-contents (fill-pointer nil) displaced-to displaced-index-offset => adjusted-array)
          (adjustable-array-p array => generalized-boolean)
          (aref array &rest subscripts => element)
          (array-dimension array axis-number => dimension)
          (array-dimensions array => dimensions)
          (array-element-type array => typespec)
          (array-has-fill-pointer-p array => generalized-boolean)
          (array-displacement array => displaced-to displaced-index-offset)
          (array-in-bounds-p array &rest subscripts => generalized-boolean)
          (array-rank array => rank)
          (array-row-major-index array &rest subscripts => index)
          (array-total-size array => size)
          (arrayp object => generalized-boolean)
          (fill-pointer vector => fill-pointer)
          (row-major-aref array index => element)
          (upgraded-array-element-type typespec &optional (environment nil) => upgraded-typespec)
          (simple-vector-p object => generalized-boolean)
          (svref simple-vector index => element)
          (vector &rest objects => vector)
          (vector-pop vector => element)
          (vector-push new-element vector => new-index-p)
          (vector-push-extend new-element vector &optional (extension *implementation-dependent-extension*) => new-index)
          (vectorp object => generalized-boolean)
          (bit bit-array &rest subscripts => bit)
          (sbit bit-array &rest subscripts => bit)
          (bit-and bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-andc1 bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-andc2 bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-eqv bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-ior bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-nand bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-nor bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-orc1 bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-orc2 bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-xor bit-array1 bit-array2 &optional (opt-arg nil) => resulting-bit-array)
          (bit-not bit-array &optional (opt-arg nil) => resulting-bit-array)
          (bit-vector-p object => generalized-boolean)
          (simple-bit-vector-p object => generalized-boolean)


          ;; strings
          (simple-string-p object => generalized-boolean)
          (char string index => character)
          (schar simple-string index => character)
          (string string-or-symbol-or-character => string)
          (string-upcase string-designator &key (start 0) (end nil) => cased-string)
          (string-downcase string-designator &key (start 0) (end nil) => cased-string)
          (string-capitalize string-designator &key (start 0) (end nil) => cased-string)
          (nstring-upcase string &key (start 0) (end nil) => modified-string)
          (nstring-downcase string &key (start 0) (end nil) => modified-string)
          (nstring-capitalize string &key (start 0) (end nil) => modified-string)

          (string-trim character-bag string => trimmed-string)
          (string-left-trim character-bag string => trimmed-string)
          (string-right-trim character-bag string => trimmed-string)
          (string= string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => generalized-boolean)
          (string/= string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string< string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string> string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string<= string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string>= string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string-equal string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => generalized-boolean)
          (string-not-equal string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string-lessp string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string-greaterp string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string-not-greaterp string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (string-not-lessp string1 string2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => mismatch-index)
          (stringp object => generalized-boolean)
          (make-string size &key (initial-element *implementation-dependent-character*) (element-type 'character) => string)


          ;; sequences
          (copy-seq proper-sequence => copied-sequence)
          (elt proper-sequence index => object)
          (fill proper-sequence item &key (start 0) (end nil) => sequence) ;
          (make-sequence result-type size &key (initial-element *implementation-dependent-element*) => sequence)
          (subseq sequence start &optional (end nil) => subsequence)
          (map result-sequence-type function &rest sequences+ => result)
          (map-into result-sequence function &rest sequences => result-sequence)
          (reduce function sequence &key key (from-end nil) (start 0) (end nil) initial-value => result)
          (count item sequence &key (from-end nil) (start 0) (end nil) key test test-not => n)
          (count-if predicate sequence &key (from-end nil) (start 0) (end nil) key => n)
          (count-if-not predicate sequence &key (from-end nil) (start 0) (end nil) key => n)
          (length sequence => n)
          (reverse sequence => reversed-sequence)
          (nreverse sequence => reversed-sequence)
          (sort sequence predicate &key key => destructively-sorted-sequence)
          (stable-sort sequence predicate &key key => destructively-sorted-sequence)
          (find item sequence &key (from-end nil) test test-not (start 0) (end nil) key => element)
          (find-if predicate sequence &key (from-end nil) (start 0) (end nil) key => element)
          (find-if-not predicate sequence &key (from-end nil) (start 0) (end nil) key => element)
          (position item sequence &key (from-end nil) test test-not (start 0) (end nil) key => position)
          (position-if predicate sequence &key (from-end nil) (start 0) (end nil) key => position)
          (position-if-not predicate sequence &key (from-end nil) (start 0) (end nil) key => position)
          (search subsequence sequence &key (from-end nil) test test-not key (start1 0) (start2 0) (end1 nil) (end2 nil) => position)
          (mismatch sequence-1 sequence-2 &key (from-end nil) test test-not key (start1 0) (start2 0) (end1 nil) (end2 nil) => position)
          (replace sequence-1 sequence-2 &key (start1 0) (end1 nil) (start2 0) (end2 nil) => destructively-modified-sequence-1)
          (substitute newitem olditem sequence &key (from-end nil) test test-not (start 0) (end nil) (count nil) key => result-sequence)
          (substitute-if newitem predicate sequence &key (from-end nil) (start 0) (end nil) (count nil) key => result-sequence)
          (substitute-if-not newitem predicate sequence &key (from-end nil) (start 0) (end nil) (count nil) key => result-sequence)
          (nsubstitute newitem olditem sequence &key (from-end nil) test test-not (start 0) (end nil) (count nil) key => sequence)
          (nsubstitute-if newitem predicate sequence &key (from-end nil) (start 0) (end nil) (count nil) key=> sequence)
          (nsubstitute-if-not newitem predicate sequence &key (from-end nil) (start 0) (end nil) (count nil) key => sequence)
          (concatenate result-type &rest sequences => result-sequence)
          (merge result-type sequence-1 sequence-2 predicate &key key => result-sequence)
          (remove item sequence &key (from-end nil) test test-not (start 0) (end nil) (count nil) key => result-sequence)
          (remove-if test sequence &key (from-end nil) (start 0) (end nil) (count nil) key => result-sequence)
          (remove-if-not test sequence &key (from-end nil) (start 0) (end nil) (count nil) key => result-sequence)
          (delete item sequence &key (from-end nil) test test-not (start 0) (end nil) (count nil) key => result-sequence)
          (delete-if test sequence &key (from-end nil) (start 0) (end nil) (count nil) key => result-sequence)
          (delete-if-not test sequence &key (from-end nil) (start 0) (end nil) (count nil) key => result-sequence)
          (remove-duplicates sequence &key (from-end nil) test test-not (start 0) (end nil) key => result-sequence)
          (delete-duplicates sequence &key (from-end nil) test test-not (start 0) (end nil) key => result-sequence)


          ;; hash tables
          (make-hash-table &key (test #'eql) (size *implementation-dependent-size*) (rehash-size *implementation-dependent-rehash-size*) (rehash-threshold *implementation-dependent-threshold) => hash-table)
          (hash-table-p object => generalized-boolean)
          (hash-table-count hash-table => count)
          (hash-table-rehash-size hash-table => rehash-size)
          (hash-table-rehash-threshold hash-table => rehash-threshold)
          (hash-table-size hash-table => size)
          (hash-table-test hash-table => test)
          (gethash key hash-table &optional (default nil) => value present-p)
          (remhash key hash-table => generalized-boolean)
          (maphash function hash-table => nil)
          (with-hash-table-iterator . "(name hash-table) declaration* form* => result*")
          (clrhash hash-table => hash-table)
          (sxhash object => hash-code)

          ;; filenames
          (pathname pathspec => pathname)
          (make-pathname &key host device directory name type version defaults case => pathname)
          (pathnamep object => generalized-boolean)
          (pathname-host pathname-designator &key (case :local) => host)
          (pathname-device pathname-designator &key (case :local) => device)
          (pathname-directory pathname-designator &key (case :local) => directory)
          (pathname-name pathname-designator &key (case :local) => name)
          (pathname-type pathname-designator &key (case :local) => type)
          (pathname-version pathname-designator => version)
          (load-logical-pathname-translations host => just-loaded)
          (logical-pathname-translations host => translations)
          (logical-pathname pathspec => logical-pathname)
          (namestring pathname-designator => namestring)
          (file-namestring pathname-designator => namestring)
          (directory-namestring pathname-designator => namestring)
          (host-namestring pathname-designator => namestring)
          (enough-namestring pathname-designator &optional (defaults *default-pathname-defaults*) => namestring)
          (parse-namestring thing &optional host (default-pathname *default-pathname-defaults*) &key (start 0) (end nil) (junk-allowed nil) => pathname position)
          (wild-pathname-p pathname &optional (field-key nil) => generalized-boolean)
          (pathname-match-p pathname wildcard => generalized-boolean)
          (translate-logical-pathname pathname &key => physical-pathname)
          (translate-pathname source from-wildcard to-wildcard &key => translated-pathname)
          (merge-pathnames pathname &optional (default-pathname *default-pathname-defaults*) (default-version :newest) => merged-pathname)
          
          ;; files
          (directory pathspec &key => pathnames)
          (probe-file pathspec => truename)
          (ensure-directories-exist pathspec &key verbose => pathspec created)
          (truename filespec => truename)
          (file-author pathspec => author)
          (file-write-date pathspec => date)
          (rename-file filespec new-name => defaulted-new-name old-truename new-truename)
          (delete-file filespec => t)
          (file-error-pathname condition => pathspec)

          ;; streams
          (input-stream-p stream => generalized-boolean)
          (output-stream-p stream => generalized-boolean)
          (interactive-stream-p stream => generalized-boolean)
          (open-stream-p stream => generalized-boolean)
          (stream-element-type stream => typespec)
          (streamp object => generalized-boolean)
          (read-byte stream &optional (eof-error-p t) (eof-value nil) => byte)
          (write-byte byte stream => byte)
          (peek-char &optional (peek-type nil) (input-stream *standard-input*) (eof-error-p t) (eof-value nil) (recursive-p nil) => char)
          (read-char &optional (input-stream *standard-input*) (eof-error-p t) (eof-value nil) (recursive-p nil) => char)
          (read-char-no-hang &optional (input-stream *standard-input*) (eof-error-p t) (eof-value nil) (recursive-p nil) => char)
          (terpri &optional (output-stream *standard-output*) => nil)
          (fresh-line &optional (output-stream *standard-output*) => generalized-boolean)
          (unread-char character &optional (input-stream *standard-input*) => nil)
          (write-char character &optional (output-stream *standard-output*) => character)
          (read-line &optional (input-stream *standard-input*) (eof-error-p t) (eof-value nil) (recursive-p nil) => line missing-newline-p)
          (write-string string &optional (output-stream *standard-output*) &key (start 0) (end nil) => string)
          (write-line string &optional (output-stream *standard-output*) &key (start 0) (end nil) => string)
          (read-sequence sequence stream &key (start 0) (end nil) => position)
          (write-sequence sequence stream &key (start 0) (end nil) => sequence)
          (file-length stream => length)
          ;;(file-position stream => position)
          ;;(file-position stream position-spec => success-p)
          (file-string-length stream object => length)
          (open filespec &key (direction :input) (element-type 'character) if-exists if-does-not-exist external-format => stream)
          (stream-external-format stream => format)
          (with-open-file . "(stream filespec options*) declaration* form* => results")
          (close stream &key (abort nil) => result)
          (with-open-stream . "(var stream) declaration* form* => result*")
          (listen &optional (input-stream *standard-input*) => generalized-boolean)
          (clear-input &optional (input-stream *standard-input*) => nil)
          (finish-output &optional (output-stream *standard-output*) => nil)
          (force-output &optional (output-stream *standard-output*) => nil)
          (clear-output &optional (output-stream *standard-output*) => nil)
          (y-or-n-p &optional control &rest arguments => generalized-boolean)
          (yes-or-no-p &optional control &rest arguments => generalized-boolean)
          (make-synonym-stream symbol => synonym-stream)
          (synonym-stream-symbol synonym-stream => symbol)
          (broadcast-stream-streams broadcast-stream => streams)
          (make-broadcast-stream &rest streams => broadcast-stream)
          (make-two-way-stream input-stream output-stream => two-way-stream)
          (two-way-stream-input-stream two-way-stream => input-stream)
          (two-way-stream-output-stream two-way-stream => output-stream)
          (echo-stream-input-stream echo-stream => input-stream)
          (echo-stream-output-stream echo-stream => output-stream)
          (make-echo-stream input-stream output-stream => echo-stream)
          (concatenated-stream-streams concatenated-stream => streams)
          (make-concatenated-stream &rest input-streams => concatenated-stream)
          (get-output-stream-string string-output-stream => string)
          (make-string-input-stream string &optional (start 0) (end nil) => string-stream)
          (make-string-output-stream &key (element-type 'character) => string-stream)
          (with-input-from-string . "(var string &key index start end) declaration* form* => result*")
          (with-output-to-string . "(var &optional string-form &key element-type) declaration* form* => result*")
          (stream-error-stream condition => stream)

          ;; printer
          (copy-pprint-dispatch &optional (table *print-pprint-dispatch*) => new-table)
          (formatter control-string => function)
          (pprint-dispatch object &optional (table *print-pprint-dispatch*) => function found-p)
          (pprint-exit-if-list-exhausted => nil)
          (pprint-fill stream object &optional (colon-p t) (at-sign-p *implementation-dependent-at-sign-p*) => nil)
          (pprint-linear stream object &optional (colon-p t) (at-sign-p *implementation-dependent-at-sign-p*) => nil)
          (pprint-tabular stream object &optional (colon-p t) (at-sign-p *implementation-dependent-at-sign-p*) (tabsize 16) => nil)
          (pprint-indent relative-to n &optional (stream *standard-output*) => nil)
          (pprint-logical-block . "(stream-symbol object &key prefix per-line-prefix suffix) declaration* form* => nil")
          (pprint-newline kind &optional (stream *standard-output*) => nil)
          (pprint-pop => object)
          (pprint-tab kind colnum colinc &optional stream => nil)
          (print-object object stream => object)
          (print-unreadable-object . "(object stream &key type identity) form* => nil")
          (set-pprint-dispatch type-specifier function &optional (priority 0) (table *print-pprint-dispatch*) => nil)
          (write object &key array base case circle escape gensym length level lines miser-width pprint-dispatch pretty radix readably right-margin (stream *standard-output*) => object)
          (prin1 object &optional (output-stream *standard-output*) => object)
          (princ object &optional (output-stream *standard-output*) => object)
          (print object &optional (output-stream *standard-output*) => object)
          (pprint object &optional (output-stream *standard-output*) => <no values>)
          (write-to-string object &key array base case circle escape gensym length level lines miser-width pprint-dispatch pretty radix readably right-margin => string)
          (prin1-to-string object => string)
          (princ-to-string object => string)
          (print-not-readable-object condition => object)
          (format destination control-string &rest args => result)

          ;; reader
          (copy-readtable &optional (from-readtable *readtable*) (to-readtable nil) => readtable)
          (make-dispatch-macro-character char &optional (non-terminating-p nil) (readtable *readtable*) => t)
          (read &optional input-stream (eof-error-p t) (eof-value nil) (recursive-p nil) => object)
          (read-preserving-whitespace &optional input-stream (eof-error-p t) (eof-value nil) (recursive-p nil) => object)
          (read-delimited-list char &optional (input-stream *standard-input*) (recursive-p nil) => list)
          (read-from-string string &optional (eof-error-p t) (eof-value nil) &key (start 0) (end nil) (preserve-whitespace nil) => object position)
          (readtable-case readtable => case-sensitivity-mode)
          (readtablep object => generalized-boolean)
          (get-dispatch-macro-character disp-char sub-char &optional (readtable *readtable*) => function)
          (set-dispatch-macro-character disp-char sub-char new-function &optional (readtable *readtable*) => t)
          (get-macro-character char &optional (readtable *readtable*) => function non-terminating-p)
          (set-macro-character char new-function &optional (non-terminating-p nil) (readtable *readtable*) => t)
          (set-syntax-from-char to-char from-char &optional (to-readtable *readtable*) (from-readtable +standard-readtable+) => t)
          (with-standard-io-syntax . "form* => result*")

          ;; system construction
          (compile-file input-file &key (output-file *implementation-defined-output-file*) (verbose *compile-verbose*) (print *compile-print*) (external-format :default) => output-truename warnings-p failure-p)
          (compile-file-pathname input-file &key (output-file *implementation-defined-output-file*) &allow-other-keys => pathname)
          (load filespec &key (verbose *load-verbose*) (print *load-print*) (if-does-not-exist t) (external-format :default) => generalized-boolean)
          (with-compilation-unit . "([[:override override-form]]) form* => result*")
          (provide module-name => implementation-dependent)
          (require module-name &optional pathname-list => implementation-dependent)

          ;; environment
          (decode-universal-time universal-time &optional time-zone => second minute hour date month year day daylight-p zone)
          (encode-universal-time second minute hour date month year &optional time-zone => universal-time)
          (get-universal-time => universal-time)
          (get-decoded-time => second minute hour date month year day daylight-p zone)
          (sleep seconds => nil)
          (apropos string &optional (package nil) => <no values>)
          (apropos-list string &optional (package nil) => symbols)
          (describe object &optional (stream *standard-output*) => <no values>)
          (describe-object object stream => implementation-dependent)
          (trace . "function-name* => trace-result")
          (untrace . "function-name* => untrace-result")
          (step . "form => result*")
          (time . "form => result*")
          (get-internal-real-time => internal-time)
          (get-internal-run-time => internal-time)
          (disassemble extended-function-designator-or-lambda-expression => nil)
          (documentation x doc-type => documentation)
          (room &optional x => implementation-dependent)
          (ed &optional x => implementation-dependent)
          (inspect object => implementation-dependent)
          (dribble &optional pathname => implementation-dependent)
          (lisp-implementation-type => description)
          (lisp-implementation-version => description)
          (short-site-name => description)
          (long-site-name => description)
          (machine-instance => description)
          (machine-type => description)
          (machine-version => description)
          (software-type => description)
          (software-version => description)
          (user-homedir-pathname &optional host => pathname)
          ))


(provide 'cldoc)

;;; cldoc.el ends here
