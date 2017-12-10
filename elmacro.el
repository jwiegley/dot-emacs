;;; elmacro.el --- Convert keyboard macros to emacs lisp

;; Author: Philippe Vaucher <philippe.vaucher@gmail.com>
;; URL: https://github.com/Silex/elmacro
;; Keywords: macro, elisp, convenience
;; Version: 1.1.0
;; Package-Requires: ((s "1.11.0") (dash "2.13.0"))

;; This file is NOT part of GNU Emacs.

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

;;; Code:

(require 's)
(require 'dash)

(defgroup elmacro nil
  "Show macros as emacs lisp."
  :group 'keyboard
  :group 'convenience)

(defvar elmacro-command-history '()
  "Where elmacro process commands from variable `command-history'.")

(defcustom elmacro-processors '(elmacro-processor-filter-unwanted
                                elmacro-processor-prettify-inserts
                                elmacro-processor-concatenate-inserts
                                elmacro-processor-handle-special-objects)
  "List of processors functions used to improve code listing.

Each function is passed the list of commands meant to be displayed and
is expected to return a modified list of commands."
  :group 'elmacro
  :type '(repeat symbol))

(defcustom elmacro-show-last-commands-default 30
  "Number of commands shown by default in `elmacro-show-last-commands'."
  :group 'elmacro
  :type 'integer)

(defcustom elmacro-additional-recorded-functions '(copy-file
                                                   copy-directory
                                                   rename-file
                                                   delete-file
                                                   make-directory)
  "List of non-interactive functions that you also want to be recorded.

For example, `dired-copy-file' (the C key in dired) doesn't reads its
arguments as an interactive specification, and thus the file name is
never stored."
  :group 'elmacro
  :type '(repeat symbol))

(defcustom elmacro-unwanted-commands-regexps '("^(ido.*)$" "^(smex)$")
  "Regexps used to filter unwanted commands."
  :group 'elmacro
  :type '(repeat regexp))

(defcustom elmacro-special-objects '(("#<frame .+? \\(0x[0-9a-f]+\\)>" ",(elmacro-get-frame \"\\1\")")
                                     ("#<window \\([0-9]+\\).*?>"      ",(elmacro-get-window \\1)")
                                     ("#<buffer \\(.+?\\)>"            ",(get-buffer \"\\1\")"))
  "List of (regexp replacement) for special objects.

This will be used as arguments for `replace-regexp-in-string'."
  :group 'elmacro
  :type '(repeat (list regexp string)))

(defcustom elmacro-debug nil
  "Set to true to turn debugging in buffer \"* elmacro debug *\"."
  :group 'elmacro
  :type 'boolean)

(defun elmacro-process-commands (history)
  "Apply `elmacro-processors' to HISTORY."
  (let ((commands (reverse history)))
    (--each elmacro-processors
      (setq commands (funcall it commands)))
    commands))

(defun elmacro-pp-to-string (object)
  "Like `pp-to-string', but make sure all options are set like desired.

Also handles nil as parameter for defuns."
  (let ((pp-escape-newlines t)
        (print-quoted t)
        (print-length nil)
        (print-level nil))
    (replace-regexp-in-string "\\((defun +[^ ]+\\) +nil" "\\1 ()" (pp-to-string object))))

(defun elmacro-processor-filter-unwanted (commands)
  "Remove unwanted commands using `elmacro-unwanted-commands-regexps'"
  (--remove (let ((str (elmacro-pp-to-string it)))
              (--any? (s-matches? it str) elmacro-unwanted-commands-regexps))
            commands))

(defun elmacro-processor-prettify-inserts (commands)
  "Transform all occurences of `self-insert-command' into `insert'."
  (let (result)
    (--each commands
      (-let (((previous-command previous-arg1 previous-arg2) (car result))
             ((current-command current-arg) it))
        (if (and (eq 'setq previous-command)
                 (eq 'last-command-event previous-arg1)
                 (eq 'self-insert-command current-command))
            (setcar result `(insert ,(make-string current-arg previous-arg2)))
          (!cons it result))))
    (reverse result)))

(defun elmacro-processor-concatenate-inserts (commands)
  "Concatenate multiple inserts together"
  (let (result)
    (--each commands
      (-let (((previous-command previous-args) (car result))
             ((current-command current-args) it))
        (if (and (eq 'insert current-command) (eq 'insert previous-command))
            (setcar result `(insert ,(concat previous-args current-args)))
          (!cons it result))))
    (reverse result)))

(defun elmacro-processor-handle-special-objects (commands)
  "Turn special objects into usable objects."
  (--map (let ((str (elmacro-pp-to-string it)))
           (--each elmacro-special-objects
             (setq str (eval `(replace-regexp-in-string ,@it str))))
           (condition-case nil
               (car (read-from-string (s-replace "'(" "`(" str)))
             (error `(ignore ,str))))
         commands))

(defun elmacro-get-frame (name)
  "Return the frame named NAME."
  (--first (s-matches? (format "^#<frame .* %s>$" name) (elmacro-pp-to-string it))
           (frame-list)))

(defun elmacro-get-window (n)
  "Return the window numbered N."
  (--first (s-matches? (format "^#<window %d " n) (elmacro-pp-to-string it))
           (window-list)))

(defun elmacro-assert-enabled ()
  "Ensure `elmacro-mode' is turned on."
  (unless elmacro-mode
    (error "elmacro is turned off! do `M-x elmacro-mode' first.")))

(defun elmacro-debug-message (s &rest args)
  (when elmacro-debug
    (with-current-buffer (get-buffer-create "* elmacro - debug *")
      (insert (apply #'format s args) "\n"))))

(defun elmacro-setq-last-command-event ()
  "Return a sexp setting up `last-command-event'."
  (if (symbolp last-command-event)
      `(setq last-command-event ',last-command-event)
    `(setq last-command-event ,last-command-event)))

(defun elmacro-record-command (advised-function function &optional record keys)
  "Advice for `call-interactively' which makes it temporarily record
commands in variable `command-history'."
  (let ((original-record record)
        retval)
    (elmacro-debug-message "[%s] ----- START -----" function)
    (setq record (or original-record (not (minibufferp)))) ;; don't record when in minibuffer
    (elmacro-debug-message "[%s] before - history %s record %s original %s"
                           function (car command-history) record original-record)
    (setq retval (funcall advised-function function record keys))
    (elmacro-debug-message "[%s] after - history %s" function (car command-history))
    (let* ((sexp (car command-history))
           (cmd (car sexp)))
      (when record
        (elmacro-debug-message "[%s] recording %s" function cmd)
        (when (or (eq cmd 'self-insert-command) (command-remapping 'self-insert-command))
          (!cons (elmacro-setq-last-command-event) elmacro-command-history))
        (!cons sexp elmacro-command-history)
        (!cdr command-history)
        (elmacro-debug-message "[%s] clean %s" function (car command-history)))
      (elmacro-debug-message "[%s] ----- STOP -----" function)
      retval)))

(defun elmacro-quoted-arguments (args)
  "Helper to correctly quote functions arguments of `elmacro-additional-recorded-functions'."
  (--map-when (and (symbolp it)
                   (not (keywordp it))
                   (not (eq nil it))
                   (not (eq t it)))
              `(quote ,it) args))

(defun elmacro-make-advice-lambda (function)
  "Generate the `defadvice' lambda used to record FUNCTION.

See the variable `elmacro-additional-recorded-functions'."
  `(lambda (&rest args)
     (!cons ,(list '\` (list function ',@(elmacro-quoted-arguments args)))
            elmacro-command-history)))

(defun elmacro-mode-on ()
  "Turn elmacro mode on."
  (--each elmacro-additional-recorded-functions
    (advice-add it :before (elmacro-make-advice-lambda it)))
  (advice-add 'call-interactively :around #'elmacro-record-command))

(defun elmacro-mode-off ()
  "Turn elmacro mode off."
  (--each elmacro-additional-recorded-functions
    (advice-remove it (elmacro-make-advice-lambda it)))
  (advice-remove 'call-interactively #'elmacro-record-command))

(defun elmacro-make-defun (symbol commands)
  "Makes a function named SYMBOL containing COMMANDS."
  `(defun ,symbol ()
     (interactive)
     ,@commands))

(defun elmacro-show-defun (name commands)
  "Create a buffer containing a defun named NAME from COMMANDS."
  (let* ((buffer (generate-new-buffer (format "* elmacro - %s *" name))))
    (set-buffer buffer)
    (erase-buffer)
    (insert (elmacro-pp-to-string (elmacro-make-defun (make-symbol name) commands)))
    (emacs-lisp-mode)
    (indent-region (point-min) (point-max))
    (pop-to-buffer buffer)
    (goto-char (point-min))))

(defun elmacro-extract-last-macro (history)
  "Extract the last keyboard macro from HISTORY."
  (let ((starters '(start-kbd-macro kmacro-start-macro kmacro-start-macro-or-insert-counter))
        (finishers '(end-kbd-macro kmacro-end-macro kmacro-end-or-call-macro kmacro-end-and-call-macro)))
    (elmacro-process-commands (-drop 1 (--take-while (not (-contains? starters (car it)))
                                                     (--drop-while (not (-contains? finishers (car it))) history))))))

;;;###autoload
(defun elmacro-show-last-macro (name)
  "Show the last macro as emacs lisp with NAME."
  (interactive (list (read-string "Defun name: " "last-macro" nil "last-macro")))
  (elmacro-assert-enabled)
  (-if-let (commands (elmacro-extract-last-macro elmacro-command-history))
      (elmacro-show-defun name commands)
    (message "No macros found. Please record one before using this command (F3/F4).")))

;;;###autoload
(defun elmacro-show-last-commands (&optional count)
  "Take the latest COUNT commands and show them as emacs lisp.

This is basically a better version of `kmacro-edit-lossage'.

The default number of commands shown is modifiable in variable
`elmacro-show-last-commands-default'.

You can also modify this number by using a numeric prefix argument or
by using the universal argument, in which case it'll ask for how many
in the minibuffer."
  (interactive
   (list
    (cond
     ((equal current-prefix-arg nil)
      elmacro-show-last-commands-default)
     ((equal current-prefix-arg '(4))
      (read-number "How many commands?" elmacro-show-last-commands-default))
     (t
      (prefix-numeric-value current-prefix-arg)))))
  (elmacro-assert-enabled)
  (elmacro-show-defun (format "last-%s-commands" count) (-take-last count (elmacro-process-commands elmacro-command-history))))

;;;###autoload
(defun elmacro-clear-command-history ()
  "Clear the list of recorded commands."
  (interactive)
  (setq elmacro-command-history '()))

;;;###autoload
(define-minor-mode elmacro-mode
  "Toggle emacs activity recording (elmacro mode).
With a prefix argument ARG, enable elmacro mode if ARG is
positive, and disable it otherwise. If called from Lisp, enable
the mode if ARG is omitted or nil."
  nil
  " elmacro"
  nil
  :global t
  :group 'elmacro
  (if elmacro-mode
      (elmacro-mode-on)
    (elmacro-mode-off)))

(provide 'elmacro)

;;; elmacro.el ends here
