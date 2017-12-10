;;; parinfer.el --- Simpler Lisp editing

;; Copyright (c) 2016, Shi Tianshu

;; Author: Shi Tianshu
;; Homepage: https://github.com/DogLooksGood/parinfer-mode
;; Version: 0.4.10
;; Package-Requires: ((dash "2.13.0") (cl-lib "0.5"))
;; Keywords: Parinfer

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Installation

;; * Clone this repo.
;; #+BEGIN_SRC shell
;;   cd /some/path/parinfer-mode
;;   git clone https://github.com/DogLooksGood/parinfer-mode.git
;; #+END_SRC
;; * Emacs configurations.
;; #+BEGIN_SRC emacs-lisp
;;   ;; Add parinfer-mode to load-path.
;;   (add-to-list 'load-path "~/some/path/parinfer-mode")
;;   ;; Require it!
;;   (require 'parinfer)
;; #+END_SRC

;;; Commentary:
;; For now, project will be updated frequently.
;; The document is hosted on github.
;; https://github.com/DogLooksGood/parinfer-mode

;; * Credits
;; - [[https://github.com/shaunlebron][shaunlebron]] :: Create Parinfer.
;; - [[https://github.com/oakmac][oakmac]] :: Bring Parinfer to Emacs.
;; - [[https://github.com/tumashu][tumashu]] :: Help me a lot in writing this plugin.
;; - [[https://github.com/purcell][purcell]] & [[https://github.com/syohex][syohex]] :: Advice and Tips for writing Emacs plugin.
;; * License
;; Licensed under the GPLv3.

;;; Code:

;; -----------------------------------------------------------------------------
;; Requires
;; -----------------------------------------------------------------------------
(require 'cl-lib)
(require 'dash)
(require 'parinferlib)
(require 'mode-local)
(require 'ediff)

;; -----------------------------------------------------------------------------
;; Custom variables
;; -----------------------------------------------------------------------------
(defvar parinfer-debug nil
  "Enable parinfer debug when set to t.")

(defvar parinfer-auto-switch-indent-mode nil
  "Auto switch back to Indent Mode after insert ).")

(defvar parinfer-auto-switch-indent-mode-when-closing nil
  "Auto switch back to Indent Mode when paren matches after we insert a close parens.")

(defvar parinfer-lighters
  '(" Parinfer:Indent" . " Parinfer:Paren")
  "Parinfer lighters in mode line.

The car of it is used in parinfer indent mode, the cdr
used in parinfer paren mode.")

(defvar parinfer-extensions
  '(defaults pretty-parens smart-yank)
 "Parinfer extensions, which will be enabled when run parinfer.")

(defvar parinfer-mode-enable-hook nil
  "Call after parinfer mode is enabled.")

(defvar parinfer-mode-disable-hook nil
  "Call after parinfer mode is disabled.")

(defvar parinfer-switch-mode-hook nil
  "Call after parinfer mode switch between Indent Mode & Paren Mode.

One argument for hook function, MODE present for the mode will be used.")

(defvar parinfer-after-execute-hook nil
  "Call after parinfer executed.")

(defvar parinfer-preview-cursor-scope nil
  "Set it to t will show cursor scop in Indent Mode.

It will show the cursor's scope on an empty line by inserting
close-parens after it.")

(defvar parinfer-delay-invoke-threshold 6000
  "Threshold for 'parinfer-mode' delay processing.")

(defvar parinfer-delay-invoke-idle 0.3
  "The delay time(seconds) for parinfer delay processing.")

(defvar parinfer-display-error nil
  "If display error when parinfer failed in Indent Mode.")

(defvar parinfer-strategy
  '((default
     self-insert-command delete-indentation kill-line
     comment-dwim kill-word delete-char newline kill-region comment-or-uncomment-region newline-and-indent)
    (instantly
     delete-region newline)
    (skip))

  "Parinfer invoke strategy.)

This variable is an association list, user can use `parinfer-strategy-parse'
to parse it and use `parinfer-strategy-add' to set it.

Its elements is like below:

 (STRATEGY-NAME COMMAND COMMAND1 ...  CMDS-REGEXP CMDS-REGEXP1 ...)

The COMMAND is a symbol and CMDS-REGEXP is a regexp string which
used to match command.

 strategy name    Description
 --------------   -------------------------------------------
 default          Invoke parinfer (delay on large sexp)
 instantly        Invoke parinfer instantly
 skip             Do not invoke parinfer")

;; -----------------------------------------------------------------------------
;; Internal variable and constants
;; -----------------------------------------------------------------------------

(defconst parinfer--extension-prefix "parinfer-ext::"
  "The prefix of parinfer extensions.")

(defvar parinfer--mode 'paren
  "Parinfer mode style, 'paren or 'indent.")
(make-variable-buffer-local 'parinfer--mode)

(defvar parinfer--first-load t
  "NOT MODIFY THIS, If haven't switch to indent mode yet.")
(make-variable-buffer-local 'parinfer--first-load)

(defvar parinfer--region-shifted nil
  "If shift the region after mark activate.")
(make-variable-buffer-local 'parinfer--region-shifted)

(defvar parinfer--text-modified nil
  "If last command modified text.")
(make-variable-buffer-local 'parinfer--text-modified)

(defvar parinfer--last-line-number -1
  "Holds the last line number after invoke-parinfer-when-necessary.")
(make-variable-buffer-local 'parinfer--last-line-number)

(defvar parinfer--delay-timer nil
  "Current delay timer.")
(make-variable-buffer-local 'parinfer--delay-timer)

(defvar parinfer--x-after-shift nil
  "Where the cursor x should be, after shift region.")
(make-variable-buffer-local 'parinfer--x-after-shift)

;; -----------------------------------------------------------------------------
;; Alias
;; -----------------------------------------------------------------------------

(if (fboundp 'save-mark-and-excursion)
    (defalias 'parinfer-save-excursion 'save-mark-and-excursion)
  (defalias 'parinfer-save-excursion 'save-excursion))

;; -----------------------------------------------------------------------------
;; Macros
;; -----------------------------------------------------------------------------

(defmacro parinfer-silent (&rest body)
  "Local set function `message' to `format', then execute BODY."
  `(cl-letf (((symbol-function 'message) #'format))
     ,@body))

(defmacro parinfer-paren-run (&rest body)
  "Run BODY in paren mode.  Keep S-sexp in correct indentation."
  (let ((toggle (make-symbol "toggle")))
    `(let ((,toggle (eq parinfer--mode 'indent)))
       (parinfer-silent
        (when ,toggle
          (parinfer--switch-to-paren-mode))
        ,@body
        (when ,toggle
          (parinfer--reindent-sexp)
          (parinfer--indent-and-switch-to-indent-mode))))))

(defmacro parinfer-run (&rest body)
  "Run BODY, then invoke parinfer.

Reset delay if exists."
  `(progn
     ,@body
     (parinfer--setq-text-modified t)
     (parinfer--invoke-parinfer)))

(defmacro parinfer-do (&rest body)
  "Run BODY, then invoke parinfer.

Clean up delay if exists."
  `(progn
     (when parinfer--delay-timer
       (parinfer--clean-up))
     ,@body
     (parinfer--setq-text-modified t)
     (parinfer--invoke-parinfer)))

(defmacro parinfer--setq-text-modified (value)
  "Set ‘parinfer--text-modified’ to VALUE."
  `(progn
     (setq parinfer--text-modified ,value)
     (when parinfer-debug
       (message "parinfer: set parinfer--text-modified to %S."
                parinfer--text-modified))))

(defmacro parinfer--switch-to (mode &rest body)
  "Macro which used to switch indent/paren MODE, after execute BODY."
  (declare (indent 1))
  (let ((m (make-symbol "mode")))
    `(let ((,m ,mode))
       ,@body
       (cl-case ,m
         (indent (parinfer--extension-lifecycle :indent))
         (paren (parinfer--extension-lifecycle :paren)))
       (force-mode-line-update))))

(defmacro parinfer-define-extension (name doc-str &rest clauses)
  "Define an extension.

Usage:
\(parinfer-define-extension NAME
  DOC-STR
  CLAUSES)

CLAUSES are the codes for lifecycle.
:mount    called when 'parinfer-mode' enabled.
:unmount  called when 'parinfer-mode' disabled.
:paren    called when 'parinfer-mode' switch to Paren Mode.
:indent   called when 'parinfer-mode' switch to Indent Mode."
  (declare (indent 1) (doc-string 2))
  (let* ((alist (parinfer--plist2alist clauses))
         (keys (delete-dups (mapcar #'car alist)))
         (name-str (symbol-name name))
         clause)
    (dolist (key keys)
      (push
       `(defun ,(intern (concat parinfer--extension-prefix
                                name-str
                                (symbol-name key)))
            ()
          (progn
            ,@(cdr (assq key alist))))
       clause))
    `(progn ,@clause)))


;; -----------------------------------------------------------------------------
;; Helpers
;; -----------------------------------------------------------------------------

(defun parinfer--reindent-sexp ()
  "Reindent current sexp."
  (interactive)
  (parinfer-silent
   (when (not (parinfer--in-comment-or-string-p))
     (let ((p (point-marker)))
       (set-marker-insertion-type p t)
       (indent-region
        (parinfer-save-excursion
          (beginning-of-defun 1) (point))
        (parinfer-save-excursion
          (end-of-defun 1) (point)))
       (goto-char p)))))

(defun parinfer--paren-balanced-p ()
  "Return if current sexp is parens-balanced."
  (parinfer-save-excursion
    (parinfer--goto-current-toplevel)
    (let ((old-point (point)))
      (ignore-errors (forward-sexp))
      (unless (eq old-point (point))
        (eq (point) (line-end-position))))))

(defun parinfer--unfinished-string-p ()
  (parinfer-save-excursion
    (goto-char (point-max))
    (parinfer--in-string-p)))

(defun parinfer--plist2alist (plist)
  "Convert a property PLIST to an association list."
  (let (key output)
    (dolist (x plist)
      (if (keywordp x)
          (progn (setq key x)
                 (push (list key) output))
        (push `(,@(assq key output) ,x) output)))
    output))

(defun parinfer--extension-funcall (extension lifecycle)
  "For specified EXTENSION, call its LIFECYCLE function."
  (let ((func (intern (concat parinfer--extension-prefix
                              (symbol-name extension)
                              (symbol-name lifecycle)))))
    (when parinfer-debug
      (message "Load extension: %s, available:%s" func
               (functionp func)))
    (when (functionp func)
      (funcall func))))

(defun parinfer--extension-lifecycle (lifecycle)
  "Execute LIFECYCLE function for `parinfer-extensions'."
  (dolist (extension parinfer-extensions)
    (parinfer--extension-funcall extension lifecycle)))

(defun parinfer-current-mode ()
  "Return the current `parinfer--mode'."
  parinfer--mode)

(defun parinfer-strategy-parse (strategy-name)
  "Parse strategy, which is named STRATEGY-NAME in `parinfer-strategy'.

Its output is a plist, which context is *similar* the below:

 :commands cmd1 cmd2 cmd3
 :regexps regexp1 regexp2 regexp3"
  (let ((list (cdr (assq strategy-name parinfer-strategy))))
    `(:commands ,(cl-remove-if-not #'symbolp list)
      :regexps  ,(cl-remove-if-not #'stringp list))))

(defun parinfer-strategy-add (strategy commands)
  "Append new commands to STRATEGY.
The results will save to `parinfer-strategy'.

COMMANDS can be:

1. A command (symbol)
2. A commands list (symbol list)
3. A regexp which is used to match commands
4. A list of regexps which are used to match commands"
  (declare (indent 1))
  (let* ((commands (if (listp commands)
                       commands
                     (list commands)))
         (orig-value (cdr (assq strategy parinfer-strategy)))
         (keys (mapcar #'car parinfer-strategy))
         (new-value (cl-remove-duplicates
                     (append orig-value commands)
                     :test #'equal
                     :from-end t))
         output)
    (dolist (x parinfer-strategy)
      (if (eq (car x) strategy)
          (push (cons strategy new-value) output)
        (push x output)))
    (when (not (memq strategy keys))
      (push (cons strategy new-value) output))
    (setq parinfer-strategy (reverse output))))

(defun parinfer--strategy-match-p (command strategy-name)
  "Return t if COMMAND's parinfer invoke strategy is STRATEGY-NAME."
  (let* ((output (parinfer-strategy-parse strategy-name))
         (cmds (plist-get output :commands))
         (regexps (plist-get output :regexps)))
    (if (member command cmds)
        t
      (-any-p (lambda (regexp)
                (string-match-p
                 regexp (symbol-name command)))
              regexps))))

(defun parinfer--set-text-modified ()
  "Set ‘parinfer--text-modified’ to t when `this-command' use default invoke strategy."
  (when (and (symbolp this-command)
             (parinfer--strategy-match-p this-command 'default))
    (parinfer--setq-text-modified t)))

(defun parinfer--switch-to-indent-mode-1 ()
  "Switch to indent mode auxiliary function."
  (parinfer--switch-to 'indent
    (setq parinfer--mode 'indent)
    (setq parinfer--first-load nil)
    (run-hook-with-args 'parinfer-switch-mode-hook 'indent)))

(defun parinfer--switch-to-indent-mode ()
  "Switch to Indent Mode, this will apply indent fix on whole buffer.
If this is the first switching for current buffer and indent mode will change
Buffer text, we should see a confirm message."
  (if (or (not parinfer--first-load)
          (string= (buffer-name) " *temp*"))
      (progn
        (parinfer-indent-buffer)
        (parinfer--switch-to-indent-mode-1))
    (when (parinfer-indent-with-confirm)
      (parinfer--switch-to-indent-mode-1))))

(defun parinfer--init ()
  "Init Parinfer Mode, switch to Paren firstly, then Indent."
  (parinfer--switch-to-paren-mode)
  (when (parinfer--indent-with-message)
    (parinfer--switch-to-indent-mode)))

(defun parinfer--indent-and-switch-to-indent-mode ()
  "Switch to Indent mode and call Indent Mode immediately."
  (interactive)
  (parinfer--switch-to-indent-mode-1)
  (parinfer--invoke-parinfer-when-necessary))

(defun parinfer--switch-to-paren-mode ()
  "Switch to paren mode."
  (parinfer--switch-to 'paren
    (when parinfer--delay-timer
      (parinfer--clean-up))
    (setq parinfer--mode 'paren)
    (run-hook-with-args 'parinfer-switch-mode-hook 'paren)))

(defun parinfer--in-comment-or-string-p ()
  "Return if we are in comment or string."
  (let ((f (get-text-property (point) 'face)))
    (or (nth 3 (syntax-ppss))
        (nth 4 (syntax-ppss))
        (eq f 'font-lock-comment-face)
        (eq f 'font-lock-comment-delimiter-face))))

(defun parinfer--in-string-p ()
  "Return if we are in string."
  (nth 3 (syntax-ppss)))

(defun parinfer--goto-line (n)
  "Goto the beginning of line N."
  (goto-char (point-min))
  (forward-line (1- n))
  (beginning-of-line))

(defun parinfer--empty-line-p ()
  (or (eq (line-beginning-position) (line-end-position))
      (string-match-p
       "^[[:blank:]]+$"
       (buffer-substring-no-properties (line-beginning-position)
                                       (line-end-position)))))

(defun parinfer--goto-current-toplevel ()
  "Goto the beginning of current toplevel sexp."
  (back-to-indentation)
  (let ((prev-pos (point-max)))
    (while (and (not (eq (point) (point-min)))
                (not (eq (point) prev-pos))
                (or (parinfer--in-comment-or-string-p)
                    (parinfer--empty-line-p)
                    (not (eq (point) (line-beginning-position)))
                    (not (parinfer--toplevel-line-p))))
      (setq prev-pos (point))
      (forward-line -1)
      (back-to-indentation))
    ;; when insert parens after some whitespaces at first line,
    ;; we need consider the beginning of buffer as the begin of processing range.
    (when (eq prev-pos (point))
      (beginning-of-line))))

(defun parinfer--toplevel-line-p ()
  (string-match-p "^[({\\[#`]" (buffer-substring-no-properties
                                (line-beginning-position)
                                (line-end-position))))

(defun parinfer--goto-next-toplevel ()
  "Goto the beggining of next toplevel sexp."
  (if (eq (line-end-position) (point-max))
      (end-of-line)
    (progn
      (forward-line 1)
      (let ((found nil))
        (while (not found)
          (if (eq (line-end-position) (point-max))
              (progn
                (end-of-line)
                (setq found t))
            (progn
              (back-to-indentation)
              (if (and (not (or (parinfer--in-comment-or-string-p)
                                (parinfer--empty-line-p)))
                       (eq (point) (line-beginning-position))
                       (parinfer--toplevel-line-p))
                  (progn
                    (beginning-of-line)
                    (setq found t))
                (forward-line 1)))))))))

(defun parinfer--goto-previous-toplevel ()
  "Goto the beggining of previous toplevel sexp."
  (parinfer--goto-current-toplevel)
  (forward-line -1)
  (parinfer--goto-current-toplevel))

(defun parinfer--lighter ()
  "Return the lighter for specify mode."
  (if (eq 'paren parinfer--mode)
      (cdr parinfer-lighters)
    (car parinfer-lighters)))

(defun parinfer--ediff-init-keys ()
  "Inits for ediff.  since we don't need all features, simplify opeators."
  (local-set-key (kbd "q") 'parinfer-ediff-quit))

(defun parinfer--cursor-x ()
  "Get the cursor-x which is need by parinferlib computation."
  (abs (- (line-beginning-position) (point))))

(defun parinfer--invoke-parinfer-instantly (&optional pos)
  "Call Parinfer at POS immediately."
  (if (and pos (not (eq pos (point))))
      (let ((ln (line-number-at-pos))
            (x (parinfer--cursor-x)))
        (goto-char pos)
        (parinfer--invoke-parinfer-instantly)
        (parinfer--goto-line ln)
        (forward-char x))
     (cond
      ((eq 'paren parinfer--mode) (parinfer-paren))
      ((eq 'indent parinfer--mode) (parinfer-indent-instantly))
      (t "nothing"))))

(defun parinfer--invoke-parinfer (&optional pos)
  "Supposed to be called after each content change.
POS is the position we want to call parinfer."
  (if (and pos (not (eq pos (point))))
      (let ((current-pos (point)))
        (goto-char pos)
        (parinfer--invoke-parinfer)
        (goto-char current-pos))
    (cond
     ((eq 'paren parinfer--mode) (parinfer-paren))
     ((eq 'indent parinfer--mode) (parinfer-indent))
     (t "nothing"))))
    
(defun parinfer--should-skip-this-command-p ()
  "Should parinfer skip this command."
  (parinfer--strategy-match-p this-command 'skip))

(defun parinfer--should-invoke-instantly-p ()
  "Should parinfer be invoked instantly."
  (parinfer--strategy-match-p this-command 'instantly))

(defun parinfer--should-invoke-p ()
  "Should parinfer be invoked normally."
  (parinfer--strategy-match-p this-command 'default))

(defun parinfer--should-clean-up-p ()
  "Should parinfer do clean job."
  (and (eq parinfer--mode 'indent)
       parinfer--text-modified
       (not (equal parinfer--last-line-number (line-number-at-pos)))))

(defun parinfer--unsafe-p ()
  "If should prevent call parinfer absolutely."
  (or (bound-and-true-p multiple-cursors-mode)
      (use-region-p)))

(defun parinfer--clean-up ()
  "Parinfer do clean job.

This will finish delay processing immediately."
  (when parinfer--delay-timer
    (cancel-timer parinfer--delay-timer)
    (setq parinfer--delay-timer nil))
  (parinfer--invoke-parinfer-instantly
   (parinfer-save-excursion
     (parinfer--goto-line parinfer--last-line-number)
     (line-beginning-position))))

(defun parinfer--comment-line-p ()
  (parinfer-save-excursion
    (back-to-indentation)
    (let ((f (get-text-property (point) 'face)))
      (and (string-match-p "^;+.*$" (buffer-substring-no-properties (point) (line-end-position)))
           (parinfer-save-excursion
             (end-of-line)
             (or (nth 4 (syntax-ppss))
                 (eq f 'font-lock-comment-face)
                 (eq f 'font-lock-comment-delimiter-face)))))))

(defun parinfer--invoke-parinfer-when-necessary ()
  "Invoke parinfer when necessary."
  ;; correct parinfer-region-mode for any command.
  (when (and (not (bound-and-true-p parinfer-region-mode))
             (use-region-p))
    (parinfer--region-mode-enable))

  (when (and (bound-and-true-p parinfer-region-mode)
             (not (use-region-p)))
    (parinfer--region-mode-disable))
  
  (when this-command
    (cond
     ((not (symbolp this-command))
      nil)

     ((parinfer--should-clean-up-p)
      (parinfer--clean-up))

     ((parinfer--in-comment-or-string-p) nil)

     ((parinfer--should-skip-this-command-p) nil)

     ((parinfer--should-invoke-instantly-p)
      (parinfer--invoke-parinfer-instantly (point)))

     ((parinfer--should-invoke-p)
      (parinfer--invoke-parinfer (point)))

     (t nil)))
  (setq parinfer--last-line-number (line-number-at-pos (point))))

(defun parinfer--update-text-modified ()
  (when (and (symbolp this-command)
             (parinfer--strategy-match-p this-command 'default)
             (not (parinfer--in-string-p)))
    (setq parinfer--text-modified t)))

(defun parinfer--active-line-region ()
  "Auto adjust region so that the shift can work properly."
  (setq parinfer--x-after-shift (- (point) (line-beginning-position)))
  (let* ((begin (region-beginning))
         (end (region-end))
         (new-begin (parinfer-save-excursion
                      (goto-char begin)
                      (line-beginning-position))))
    (goto-char new-begin)
    (set-mark-command nil)
    (goto-char end)
    (setq deactivate-mark nil)
    (setq parinfer--region-shifted t)))

(defun parinfer--shift (distance)
  "Shift text.  For right, DISTANCE > 0, for left, DISTANCE < 0."
  (when (use-region-p)
    (when (not parinfer--region-shifted)
      (parinfer--active-line-region))
    (let ((mark (mark)))
      (parinfer-save-excursion
        (indent-rigidly (region-beginning)
                        (region-end)
                        distance)
        (push-mark mark t t)
        (setq parinfer--x-after-shift
              (+ parinfer--x-after-shift distance))
        (setq deactivate-mark nil)))))

(defun parinfer-mode-enable ()
  "Enable 'parinfer-mode'."
  (setq-mode-local parinfer-mode indent-tabs-mode nil)
  (require 'parinfer-ext)
  (setq parinfer--last-line-number (line-number-at-pos (point)))
  (add-hook 'post-command-hook 'parinfer--invoke-parinfer-when-necessary t t)
  (add-hook 'post-command-hook 'parinfer--update-text-modified t t)
  (parinfer--extension-lifecycle :mount)
  (parinfer--init)
  (run-hooks 'parinfer-mode-enable-hook))

(defun parinfer-mode-disable ()
  "Disable 'parinfer-mode'."
  (remove-hook 'post-command-hook 'parinfer--update-text-modified t)
  (remove-hook 'post-command-hook 'parinfer--invoke-parinfer-when-necessary t)
  (parinfer--extension-lifecycle :unmount)
  (parinfer--region-mode-disable)
  (run-hooks 'parinfer-mode-disable-hook))

(defun parinfer--region-mode-enable ()
  "Run when region activated."
  (parinfer-region-mode 1))

(defun parinfer--region-mode-disable ()
  "Run when region deactivated, indent code if ‘parinfer--mode’ is 'indent."
  (when (and (eq 'indent parinfer--mode)
             parinfer--region-shifted)
    (beginning-of-line)
    (parinfer-indent-instantly)
    (when parinfer--x-after-shift
      (if (> parinfer--x-after-shift
             (- (line-end-position) (line-beginning-position)))
          (end-of-line)
        (when (> parinfer--x-after-shift 0)
          (forward-char parinfer--x-after-shift))))
    (setq parinfer--region-shifted nil)
    (setq parinfer--x-after-shift nil))
  (parinfer-region-mode -1))

(defun parinfer--prepare ()
  "Prepare input arguments for parinferlib."
  (let* ((window-start-pos (window-start))
         (start (parinfer-save-excursion (parinfer--goto-previous-toplevel) (point)))
         (end (parinfer-save-excursion (parinfer--goto-next-toplevel) (point)))
         (text (buffer-substring-no-properties start end))
         (line-number (line-number-at-pos))
         (cursor-line (- line-number (line-number-at-pos start)))
         (cursor-x (parinfer--cursor-x))
         (opts (list :cursor-x cursor-x
                     :cursor-line cursor-line
                     :preview-cursor-scope parinfer-preview-cursor-scope))
         (orig (list :start start
                     :end end
                     :window-start-pos window-start-pos
                     :line-number line-number)))
    (when parinfer-debug
      (message "text:%s" text))
    (list :text text :opts opts :orig orig)))

(defun parinfer--apply-result (result context)
  "Apply parinfer RESULT to current buffer.
CONTEXT is the context for parinfer execution."
  (let* ((orig (plist-get context :orig))
         (start (plist-get orig :start))
         (end (plist-get orig :end))
         (window-start-pos (plist-get orig :window-start-pos))
         (line-number (plist-get orig :line-number))
         (err (plist-get result :error)))
    (if (and parinfer-display-error err)
        (let ((err-line (+ (line-number-at-pos start) (plist-get err :line-no))))
          (message "Parinfer error:%s at line: %s column:%s"
                   (plist-get err :message)
                   err-line
                   (parinfer-save-excursion
                     (parinfer--goto-line err-line)
                     (forward-char (plist-get err :x))
                     (current-column))))
      (let ((changed-lines (plist-get result :changed-lines)))
        (when (and (plist-get result :success)
                   changed-lines)
          (cl-loop for l in changed-lines do
                   (parinfer--goto-line (+ (line-number-at-pos start) (plist-get l :line-no)))
                   (parinfer-save-excursion
                     (delete-region (line-beginning-position)
                                    (line-end-position)))
                   (insert (plist-get l :line)))
          (parinfer--goto-line line-number)
          (forward-char (plist-get result :cursor-x))))
      (parinfer--setq-text-modified nil))))

(defun parinfer--execute-instantly (context)
  "Execute parinfer instantly with context CONTEXT."
  (unless (parinfer--unsafe-p)
    (let* ((orig (plist-get context :orig))
           (start (plist-get orig :start))
           (end (plist-get orig :end)))
      (let* ((text (plist-get context :text))
             (opts (plist-get context :opts))
             (result (parinferlib-indent-mode text opts)))
        (parinfer--apply-result result context)
        (run-hooks 'parinfer-after-execute-hook)))))

(defun parinfer--execute (context)
  "Execute parinfer with context CONTEXT."
  (when parinfer--delay-timer
    (cancel-timer parinfer--delay-timer)
    (setq parinfer--delay-timer nil))
  (let ((text (plist-get context :text)))
    (if (> (length text) parinfer-delay-invoke-threshold)
        (setq parinfer--delay-timer
              (run-with-idle-timer
               parinfer-delay-invoke-idle
               nil
               #'parinfer-indent-instantly))
      (parinfer--execute-instantly context))))

(defun parinfer--auto-switch-indent-mode-p ()
  (and (parinfer--paren-balanced-p)
       (not parinfer--first-load)
       (or parinfer-auto-switch-indent-mode
           (and parinfer-auto-switch-indent-mode-when-closing
                (let ((keys (this-command-keys)))
                  (and (stringp keys)
                       (string-match-p "\\s)" keys)))))))

;; -----------------------------------------------------------------------------
;; Parinfer commands
;; -----------------------------------------------------------------------------

(defun parinfer-untabify-buffer ()
  "Untabify whole buffer.

Currently parinfer can not handle indentation with tab.
Use this to remove tab indentation of your code."
  (interactive)
  (untabify (point-min) (point-max)))

(defun parinfer-auto-fix ()
  "Untabify whole buffer then reindent whole buffer."
  (interactive)
  (parinfer-untabify-buffer)
  (dolist (cmd '(mark-whole-buffer
                 indent-region
                 keyboard-quit
                 parinfer-indent-buffer))
    (call-interactively cmd)))

(defun parinfer-indent ()
  "Parinfer indent."
  (let ((context (parinfer--prepare)))
    (parinfer--execute context)))

(defun parinfer-indent-instantly ()
  "Parinfer indent instantly."
  (let ((context (parinfer--prepare)))
    (parinfer--execute-instantly context)))

(defun parinfer-indent-buffer ()
  "Call parinfer indent on whole buffer."
  (interactive)
  (let* ((window-start-pos (window-start))
         (cursor-line (1- (line-number-at-pos)))
         (cursor-x (parinfer--cursor-x))
         (opts (list :cursor-x cursor-x
                     :cursor-line cursor-line
                     :preview-cursor-scope parinfer-preview-cursor-scope))
         (text (buffer-substring-no-properties (point-min) (point-max)))
         (result (parinferlib-indent-mode text opts))
         (changed-lines (plist-get result :changed-lines)))
    (when (and (plist-get result :success)
               changed-lines)
      (cl-loop for l in changed-lines do
               (parinfer--goto-line (1+ (plist-get l :line-no)))
               (parinfer-save-excursion
                 (delete-region (line-beginning-position)
                                (line-end-position)))
               (insert (plist-get l :line)))
      (parinfer--goto-line (1+ cursor-line))
      (forward-char (plist-get result :cursor-x))
      (set-window-start (selected-window) window-start-pos))))

(defun parinfer--indent-with-message ()
  "Call parinfer indent on whole buffer, display message depend on result.

If there's any change, display a warning message and style in Paren Mode.
If There's no change, switch to Indent Mode."
  (let* ((window-start-pos (window-start))
         (cursor-line (1- (line-number-at-pos)))
         (cursor-x (parinfer--cursor-x))
         (opts (list :cursor-line cursor-line :cursor-x cursor-x))
         (text (buffer-substring-no-properties (point-min) (point-max)))
         (result (parinferlib-indent-mode text opts))
         (success (plist-get result :success))
         (changed-lines (plist-get result :changed-lines)))
    (if (not success)
        (progn
          (message (concat "Parinfer: Pairs unmatched, switch to Paren mode. "
                           "When pair fixed, You can switch to indent mode."))
          nil)
      (if (and changed-lines
               (not (string= text (plist-get result :text))))
          (progn
            (message
             (substitute-command-keys
              (concat "Parinfer: Paren Mode, use \\[parinfer-toggle-mode] "
                      "to switch to Indent Mode.")))
            nil)
        t))))

(defun parinfer-indent-with-confirm ()
  "Call parinfer indent on whole buffer.

If there's any change, display a confirm message in minibuffer."
  (interactive)
  (let* ((window-start-pos (window-start))
         (cursor-line (1- (line-number-at-pos)))
         (cursor-x (parinfer--cursor-x))
         (opts (list :cursor-line cursor-line :cursor-x cursor-x))
         (text (buffer-substring-no-properties (point-min) (point-max)))
         (result (parinferlib-indent-mode text opts))
         (success (plist-get result :success))
         (changed-lines (plist-get result :changed-lines)))
    (if (not success)
        (progn
          (message (concat "Pairs unmatched, switch to Paren mode. "
                           "When pair fixed, You can switch to indent mode."))
          nil)
      (if (and changed-lines
               (not (string= text (plist-get result :text))))
          (if (y-or-n-p "Parinfer: Switch to indent will modify this buffer, continue? ")
              (progn (cl-loop for l in changed-lines do
                              (parinfer--goto-line (1+ (plist-get l :line-no)))
                              (delete-region (line-beginning-position)
                                             (line-end-position))
                              (insert (plist-get l :line)))
                     (parinfer--goto-line (1+ cursor-line))
                     (forward-char (plist-get result :cursor-x))
                     (set-window-start (selected-window) window-start-pos)
                     (setq parinfer--first-load nil)
                     t)
            nil)
        t))))

(defun parinfer-paren ()
  "Do parinfer paren  on current & previous top level S-exp."
  (when (and (ignore-errors (parinfer--reindent-sexp))
             (parinfer--auto-switch-indent-mode-p))
    (parinfer--switch-to-indent-mode-1)))

(defun parinfer-ediff-quit ()
  "Quit ‘parinfer-diff’ directly, without confirm."
  (interactive)
  (ediff-really-quit nil)
  (with-current-buffer "*Parinfer Result*"
    (kill-buffer-and-window)))

(defun parinfer-backward-delete-char ()
  "Replacement in command ‘parinfer-mode’ for ‘backward-delete-char’ command."
  (interactive)
  (if (eq 'paren parinfer--mode)
      (parinfer-run
       (if (string-match-p "^[[:space:]]+$"
                           (buffer-substring-no-properties
                            (line-beginning-position)
                            (point)))
           (delete-indentation)
         (backward-delete-char 1)))
    (progn
      (backward-delete-char 1)
      (if (parinfer--in-string-p)
          (parinfer--setq-text-modified nil)
        (parinfer--invoke-parinfer)))))

(defun parinfer-backward-kill-word ()
  "Replacement in symbol 'parinfer-mode' for 'backward-kill-word' command."
  (interactive)
  (parinfer-run
   (call-interactively 'backward-kill-word)))

(defun parinfer-delete-char ()
  "Replacement in 'parinfer-mode' for 'delete-char' command."
  (interactive)
  (parinfer-run
   (delete-char 1)))

(defun parinfer-kill-word ()
  "Replacement in 'parinfer-mode' for 'kill-word' command."
  (interactive)
  (parinfer-run
   (call-interactively 'kill-word)))

(defun parinfer-kill-line ()
  "Replacement in 'parinfer-mode' for 'kill-line' command."
  (interactive)
  (parinfer-run
   (call-interactively 'kill-line)))

(defun parinfer-delete-indentation ()
  "Replacement in 'parinfer-mode' for 'delete-indentation' command."
  (interactive)
  (parinfer-paren-run
   (call-interactively 'delete-indentation)))

(defun parinfer-raise-sexp ()
  "Raise sexp and Indent code."
  (interactive)
  (call-interactively 'raise-sexp)
  (parinfer--reindent-sexp))

 (defun parinfer-region-delete-region ()
    (interactive)
    (if (region-active-p)
        (call-interactively 'delete-region)
      (call-interactively 'parinfer-backward-delete-char))
    (deactivate-mark t)
    (parinfer-run))

(defun parinfer-yank ()
  "Replacement in 'parinfer-mode' for 'yank' command."
  (interactive)
  (call-interactively 'yank)
  (parinfer--setq-text-modified t)
  (parinfer-indent-buffer))

(defun parinfer-mouse-drag-region ()
  "Should do clean up if it is needed."
  (interactive)
  (when parinfer--delay-timer
    (parinfer--clean-up))
  (call-interactively 'mouse-drag-region))

(defun parinfer-kill-region ()
  "Replacement in 'parinfer-mode' for 'kill-region' command."
  (interactive)
  (parinfer-run
   (call-interactively 'kill-region)))

(defun parinfer-newline ()
  "Replacement in 'parinfer-mode' for 'newline' command."
  (interactive)
  (parinfer-do
   (call-interactively 'newline)))

(defun parinfer-semicolon ()
  "Insert semicolon, always indent after insertion.

This is the very special situation, since we always need
invoke parinfer after every semicolon input."
  (interactive)
  (call-interactively 'self-insert-command)
  (parinfer-indent)
  (parinfer--setq-text-modified t))

(defun parinfer-double-quote ()
  "Insert a pair of quotes, or a single quote after backslash. "
  (interactive)
  (if (parinfer--in-string-p)
      (let* ((orig-end (parinfer-save-excursion (parinfer--goto-next-toplevel) (line-number-at-pos)))
             (orig-end-is-max (eq (line-number-at-pos (point-max)) orig-end)))
        (insert "\"")
        (let ((new-end (parinfer-save-excursion (parinfer--goto-next-toplevel) (line-number-at-pos))))
          (unless (or (< orig-end new-end)
                      (and orig-end-is-max
                           (parinfer--unfinished-string-p)))
            (parinfer--invoke-parinfer))))
    (call-interactively 'self-insert-command)))

(defun parinfer-delete-indentation ()
  "Replacement in 'parinfer-mode' for 'delete-indentation' command."
  (interactive)
  (parinfer-paren-run
   (call-interactively 'delete-indentation)))

(defun parinfer-toggle-mode ()
  "Switch parinfer mode between Indent Mode and Paren Mode."
  (interactive)
  (if (eq 'paren parinfer--mode)
      (parinfer--switch-to-indent-mode)
    (parinfer--switch-to-paren-mode)))

(defun parinfer-diff ()
  "Diff current code and the code after applying Indent Mode in Ediff.
Use this to browse and apply the changes."
  (interactive)
  (let* ((orig-text (buffer-substring-no-properties (point-min) (point-max)))
         (new-buffer (generate-new-buffer "*Parinfer Result*"))
         (orig-buffer (current-buffer))
         (m major-mode)
         (result (parinferlib-indent-mode orig-text nil)))
    (with-current-buffer new-buffer
      (erase-buffer)
      (insert (plist-get result :text))
      (funcall m)
      (ediff-buffers orig-buffer new-buffer '(parinfer--ediff-init-keys)))))

(defun parinfer-region-mode-switch-mode ()
  "While when 'parinfer-region-mode’ is enabled, we can't switch to Paren Mode."
  (interactive)
  (message "Can't toggle Parinfer Mode when region is active."))

(defun parinfer-shift-right ()
  "In Indent Mode with region active, shift text left."
  (interactive)
  (when (eq 'indent parinfer--mode)
    (parinfer--shift 1)))

(defun parinfer-shift-left ()
  "In Indent Mode with region active, shift text left."
  (interactive)
  (when (eq 'indent parinfer--mode)
    (parinfer--shift -1)))

;; -----------------------------------------------------------------------------
;; Keymaps
;; -----------------------------------------------------------------------------

(defvar parinfer-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [remap backward-delete-char-untabify] 'parinfer-backward-delete-char)
    (define-key map [remap delete-backward-char] 'parinfer-backward-delete-char)
    (define-key map [remap mouse-drag-region] 'parinfer-mouse-drag-region)
    (define-key map [remap delete-indentation] 'parinfer-delete-indentation)
    (define-key map ";" 'parinfer-semicolon)
    (define-key map "\"" 'parinfer-double-quote)
    (define-key map [remap yank] 'parinfer-yank)
    map))

(defvar parinfer-region-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<tab>") 'parinfer-shift-right)
    (define-key map (kbd "S-<tab>") 'parinfer-shift-left)
    (define-key map (kbd "TAB") 'parinfer-shift-right)
    (define-key map (kbd "<backtab>") 'parinfer-shift-left)
    (define-key map (kbd "<backspace>") 'parinfer-region-delete-region)
    (define-key map [remap parinfer-toggle-mode] 'parinfer-region-mode-switch-mode)
    map))

;; -----------------------------------------------------------------------------
;; Mode
;; -----------------------------------------------------------------------------

;;;###autoload
(define-minor-mode parinfer-mode
  "Parinfer mode."
  nil (:eval (parinfer--lighter)) parinfer-mode-map
  (if parinfer-mode
      (parinfer-mode-enable)
    (parinfer-mode-disable)))

;;;###autoload
(define-minor-mode parinfer-region-mode
  "Available when region is active."
  :init-value nil
  :keymap parinfer-region-mode-map)

(provide 'parinfer)
;;; parinfer.el ends here
