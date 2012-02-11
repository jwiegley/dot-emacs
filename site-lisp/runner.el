;;; runner.el --- improved "open with" suggestions for dired ---

;; Author: Thamer Mahmoud <thamer.mahmoud@gmail.com>
;; Version: 1.0
;; Time-stamp: <2012-02-01 22:42:26 thamer>
;; URL: http://www.emacswiki.org/emacs/download/runner.el
;; Keywords: shell command, dired, file extension, open with
;; Compatibility: Tested on GNU Emacs 23.3 and 24.0.92.1
;; Copyright (C) 2012 Thamer Mahmoud.

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING. If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; This library allows for a set of shell commands to be linked to
;; file or directory names. These commands can then be used in dired
;; mode using `dired-do-shell-command' (or pressing "!"). Since this
;; library modifies the behavior of `dired-guess-shell-alist-user',
;; the command syntax will follow that variable's syntax (see the
;; documentation of `dired-guess-shell-alist-user' for more).
;;
;;; Features:
;;
;; * Provides a widget.el interface to add, edit, and sort shell
;;   commands.
;;
;; * Gets rid of the "A command is running - kill it? Yes or No?"
;;   message.
;;
;; * If `runner-run-in-background' is set to t, send the stdout buffer
;;   to the background except when the command string includes
;;   `{run:out}'.
;;
;; * If the command string contains `{run:shell}', run the command
;;   using the function specified in `runner-shell-function'.
;;
;;; Install:
;;
;; Put this file in your Emacs-Lisp load path, and add the following
;; into your $HOME/.emacs startup file.
;;
;;     (require 'runner)
;;
;;; Usage:
;;
;; While in dired mode, position point on any file or directory you
;; wish to add a shell command to, then do:
;;
;; M-x runner-add-file (for file or directory names)
;; M-x runner-add-extension (for file extension)
;;
;; A new buffer will be created allowing you to specify what commands
;; to run.
;;
;; A file name or extension can be linked to multiple set of
;; commands. You can view and edit which pattern is being applied to a
;; file by positioning point on a file and running,
;;
;; M-x runner-edit-file-at-point
;;
;; You can also add, edit, or delete any specific pattern by doing:
;;
;; M-x runner-add-empty
;; M-x runner-edit
;; M-x runner-delete
;;
;; The command database will be saved to the variable
;; `runner-init-file' (default is "~/.emacs.d/runner-conf.el"). You
;; may choose a different location by doing:
;;
;; M-x customize-variable runner-init-file
;;
;; The functions `dired-guess-default' (from dired-x.el) and
;; `dired-run-shell-command' (from dired-aux.el) will be redefined.
;;
;;

;;; Code:
(require 'dired)
(require 'dired-x)
(require 'dired-aux)

(defgroup runner nil "runner group"
  :group 'convenience
  :group 'dired)

(defcustom runner-init-file
  (convert-standard-filename "~/.emacs.d/runner-conf.el")
  "Name of file used to save pattern and command database."
  :type 'file
  :group 'runner)

(defcustom runner-run-in-background nil
  "Hide all stdout buffers unless the command was run with
{run:out} in the command string."
  :type 'boolean
  :group 'runner
  :set (lambda (symbol value)
         (set symbol value)
         (if value
             (add-to-list
              'special-display-buffer-names
              '("*Runner Output*" runner-background-frame-function nil))
           (setq special-display-buffer-names
                 (remove
                  '("*Runner Output*" runner-background-frame-function nil)
                  special-display-buffer-names)))))

(defcustom runner-shell-function 'runner-shell-function-eshell
  "Function to use to execute commands when `{run:shell}' is
  found in the command string. The function must accept one
  argument, a command as string."
  :type 'function
  :group 'runner)

(defvar runner-names nil
  "List holding the names of file types as strings")

(defvar runner-alist nil
  "An alist holding types associated with a set of commands. Each
  type has the following structure:
 NAME         ;; Unique name used as key.
 PATTERN-type ;; See the types.
 PATTERN      ;; Pattern is string representing a Regexp
 COMMAND-LIST ;; A list of lists holding commands with the following structure:
    LABEL     ;; Optional command label currently used as comment.
    COMMAND   ;; Command string.
    PRIORITY  ;; Priority of processing this command. Default is 5.")

(defun runner-shell-function-eshell (command)
  "Default function to run commands in an interactive shell"
  (require 'eshell)
  (eshell-command command))

(defun runner-settings-save ()
  (let ((file (expand-file-name runner-init-file)))
    (save-excursion
      (with-temp-buffer
        (print runner-names (current-buffer))
        (print runner-alist (current-buffer))
        (write-file file nil)
        (message "runner: Settings saved")))))

(defun runner-settings-load ()
  (let ((file (expand-file-name runner-init-file)))
    (save-excursion
      (with-temp-buffer
        (if (not (file-exists-p file))
            (message "runner: No runner config file found.\
 Please run runner-add first.")
          (insert-file-contents file)
          (goto-char (point-min))
          (condition-case eof
              (setq runner-names (read (current-buffer)))
            (end-of-file (message "runner: Failed to load
            pattern names. File exists but empty or corrupt.")))
          (condition-case eof
              (setq runner-alist (read (current-buffer)))
            (end-of-file (message "runner: Failed to load
            pattern list File exists but empty or corrupt.")))
          (setq runner-custom-loaded t))))))

(defun runner-add-name (name doc-string)
  "Adds name to an alist, but checks if a name already exists and
triggers an error."
  (when (equal name "")
    (error (format "runner: %s name cannot be empty." doc-string))))

(defun runner-add-filename ()
  "Used for defining a set of commands for a file or directory name"
  (interactive)
  (let* ((regexp (concat "^" (file-name-nondirectory (dired-get-filename)) "$"))
         (name (concat "file-" (file-name-nondirectory (dired-get-filename)))))
    (runner-add-name name "File type")
    (if (assoc name runner-alist)
        (runner-edit name)
      (add-to-list 'runner-alist `(,name 1 ,regexp (("" "" 5))))
      (add-to-list 'runner-names name)
      (runner-settings-save)
      (runner-edit name))))

(defun runner-add-extension ()
  "Used to define a set of commands for an extension"
  (interactive)
  (let* ((ext (file-name-extension (dired-get-filename)))
         (name (concat "ext-" ext)))
    (if (eq ext nil)
        (error "Runner: No extension found")
      (runner-add-name name "File type")
      (if (assoc name runner-alist)
          (runner-edit name)
        (add-to-list 'runner-alist `(,name 0 ,ext (("" "" 5))))
        (add-to-list 'runner-names name)
        (runner-settings-save)
        (runner-edit name)))))

(defun runner-add-empty (name)
  "Add a new empty file type"
  (interactive
   (append
    (let* ((name (read-string (format "New name for a file type: "))))
      (list name))))
  (runner-add-name name "File type")
  ;; Default alist structure
  (add-to-list 'runner-alist `(,name 0 "" (("" "" 5))))
  (add-to-list 'runner-names name)
  (runner-settings-save)
  (runner-edit name))

(defun runner-delete (name)
  (interactive
   (list
    (completing-read
     "Choose a file type to delete: " runner-names nil t)))
  "Deletes a file type and all its parameters."
  ;; Delete all types
  (runner nil)
  ;; No assoc-delete-all?
  (setq runner-alist
        (remove (assoc name runner-alist) runner-alist))
  (setq runner-names (remove name runner-names))
  (runner-settings-save)
  (runner t))

(defvar runner-widgets nil
  "List holding widget information.")

(defun runner-create-edit-buffer (name)
  (switch-to-buffer
   (concat "*Customize runner type `" name "'*"))
  (let* ((inhibit-read-only t)
         (map (make-sparse-keymap))
         (current (assoc name runner-alist))
         ;; Numbers here should reflect the order of the widget.el
         ;; buffer
         (pattern-type (nth 1 current))
         (pattern (nth 2 current))
         (command-list (nth 3 current)))
    (kill-all-local-variables)
    (make-local-variable 'runner-widgets)
    (erase-buffer)
    (remove-overlays)
    (require 'widget)
    (widget-insert "Type `C-c C-c' or press [Save] after you have \
finished editing.\n\n" )
    (setq runner-widgets
          (list
           ;; This widget also includes the current name of the type
           ;; being edited.
           (let ((wid (widget-create
                       'editable-field :value name
                       :format "Type Name (edit to rename): %v\n" "")))
             (widget-put wid :being-edited name)
             wid)
           (widget-create
            'editable-field :value pattern
            :format "Pattern: %v" "")
           (ignore (widget-insert "\nPattern Type:\n"))
           (widget-create
            'radio-button-choice
            :value pattern-type
            '(item :tag "A list of space-separated extension \
regexps. Ex. jpe?g gif png (case-insensitive)" 0)
            '(item :tag "Regexp on file name." 1))
           (widget-create
            'repeat
            :tag "\nCommands to run on files matching this pattern"
            :value command-list
            '(list :tag ""
                   (string :tag "Label (optional)")
                   (string :tag "Command")
                   (choice :tag "Priority"
                           (const :tag "0" 0)
                           (const :tag "1" 1)
                           (const :tag "2" 2)
                           (const :tag "3" 3)
                           (const :tag "4" 4)
                           (const :tag "5" 5)
                           (const :tag "6" 6)
                           (const :tag "7" 7)
                           (const :tag "8" 8)
                           (const :tag "9" 9))))
           (ignore (widget-insert "\n"))))
    ;; Delete empty widget-insert
    (delq nil runner-widgets)
    (widget-insert "\n")
    ;; Buttons
    (widget-create
     'push-button
     :button-face 'custom-button
     :notify (lambda (&rest ignore)
               (runner-save runner-widgets)
               (kill-buffer)) "Save")
    (widget-insert " ")
    (widget-create 'push-button
                   :button-face 'custom-button
                   :notify (lambda (&rest ignore)
                             (kill-buffer))
                   "Cancel")
    (widget-insert "\n\n")
    ;; This is needed to get rid of cus-edit bindings.
    ;; Keymaps
    (widget-put (get 'editable-field 'widget-type) :keymap nil)
    (set-keymap-parent map widget-keymap)
    (define-key map (kbd "C-c C-c")
      '(lambda () (interactive)
         (runner-save runner-widgets)
         (kill-buffer)))
    (use-local-map map)
    (widget-setup))
  (goto-char (point-min))
  (widget-forward 1))

(defun runner-edit (name)
  "Edit a file type"
  (interactive
   (list (completing-read "Edit runner pattern: "
                          runner-names nil t)))
  (when (equal name "")
    (error "Runner: File type cannot be empty"))
  (runner-create-edit-buffer name))

(defun runner-edit-file-at-point ()
  "Edit this file or extension based on checking whether a type applies or not"
  (interactive)
  ;; Create a list of patterns matching current file
  (let ((pat-list (runner-find-pattern
                   (dired-get-filename 'no-dir) runner-names)))
    (if (eq (length pat-list) 1)
        (runner-create-edit-buffer (car pat-list))
      (progn
        (unless pat-list
          (error "Runner: No pattern defined for this file or extension.\
 Use runner-add-file or runner-add-extension."))
        (runner-create-edit-buffer
         (completing-read
          "Edit runner pattern for this files: "
          pat-list nil t))))))

(defun runner-find-pattern (file-name names-list)
  (let ((matched))
    (while names-list
      (if (string-match
           ;; Check if type is a list of extensions or filename
           (if (eq (nth 1 (assoc (car names-list) runner-alist)) 0)
               (runner-ext-regexp
                (nth 2 (assoc (car names-list) runner-alist)))
             (nth 2 (assoc (car names-list) runner-alist)))
           file-name)
          (add-to-list 'matched (car names-list)))
      (setq names-list (cdr names-list)))
    matched))

(defun runner-save (widget-list)
  "Adds values of widget to type lists, saves them to file and
update."
  (let* ((old-name (widget-get (nth 0 widget-list) :being-edited))
         (current (assoc old-name runner-alist))
         (name (widget-value (nth 0 widget-list)))
         (pattern (widget-value (nth 1 widget-list)))
         (pattern-type (widget-value (nth 2 widget-list)))
         (commands-list (widget-value (nth 3 widget-list))))
    ;; Replace old type with new type
    (setq runner-alist
          (remove (assoc old-name runner-alist)
                  runner-alist))
    (setq runner-names (remove old-name runner-names))
    ;; Update variables
    (add-to-list 'runner-alist
                 (list name pattern-type pattern commands-list))
    (add-to-list 'runner-names name)
    (runner-settings-save)
    (runner nil)
    (runner t)))

(defun runner-apply (pattern command-list)
  (add-to-list 'dired-guess-shell-alist-user
               (nconc (list pattern) command-list) t))

(defun runner-remove (pattern command-list)
  (setq dired-guess-shell-alist-user
        (remove (assoc pattern dired-guess-shell-alist-user)
                dired-guess-shell-alist-user)))

(defun runner-ext-regexp (extensions)
  "Given a list of extensions, return a regexp usable to
dired-guess-shell-alist-user"
  (let ((extensions-split (split-string extensions)))
    (mapconcat
     (lambda (str) (format "\\.%s$" str )) extensions-split "\\|")))

(defun runner-commands (command-list)
  "Get a list of commands usable for
dired-guess-shell-alist-user. Also the nth 1 is the position of
the command in runner-list."
  (mapcar (lambda (item) (list (nth 1 item) (nth 2 item))) command-list))

(defun runner (enable)
  (if (not (length runner-names))
      (error "Runner: No file types have been \
defined. Define a new file type using runner-add.")
    (let ((runner-names-done runner-names))
      ;; Process each pattern
      (while runner-names-done
        (let* ((ft-list (assoc (car runner-names-done) runner-alist))
               (ft-name (nth 0 ft-list))
               (ft-type (nth 1 ft-list))
               (ft-pattern (nth 2 ft-list))
               (ft-command-list (nth 3 ft-list)))
          (cond
           ;; Type is a list of extensions
           ((eq ft-type 0)
            (if enable
                (runner-apply (runner-ext-regexp ft-pattern)
                              (runner-commands ft-command-list))
              (runner-remove (runner-ext-regexp ft-pattern)
                             (runner-commands ft-command-list))))
           ;; Type is a file or directory name
           ((eq ft-type 1)
            (if enable
                (runner-apply ft-pattern
                              (runner-commands ft-command-list))
              (runner-remove ft-pattern
                             (runner-commands ft-command-list))))))
        (setq runner-names-done (cdr runner-names-done))))))

;;;;;;;;;;;;;;;;;;;;;;; Redefined functions ;;;;;;;;;;;;;;;;;;;;;;;;;
(defun dired-guess-default (files)
  "Guess shell commands for FILES. Returns a list of
commands. Redefined to handle priorities and multiple regexps."
  (let* ((case-fold-search dired-guess-shell-case-fold-search)
         (regexp-list dired-guess-shell-alist-user)
         (file (car files))
         (flist (cdr files))
         elt regexp matched-regexp cmds)

    ;; Process user command list
    (while regexp-list
      (setq elt (car regexp-list)
            regexp (car elt)
            regexp-list (cdr regexp-list))
      (when (string-match regexp file)
        (setq matched-regexp regexp)
        (setq cmds (append cmds (cdr elt)))))

    ;; Sort based on priority number (1 is highest, more is lower) and
    ;; strip out the priorities.
    (setq cmds (append cmds nil))
    (setq cmds
          (mapcar
           (lambda (elem) (nth 0 elem))
           (sort cmds
                 (lambda (item1 item2) (< (nth 1 item1) (nth 1 item2))))))

    ;; Process default command list
    (setq regexp-list dired-guess-shell-alist-default)
    (while regexp-list
      (setq elt (car regexp-list)
            regexp (car elt)
            regexp-list (cdr regexp-list))
      (when (string-match regexp file)
        (setq matched-regexp regexp)
        (setq cmds (append cmds (cdr elt))
              regexp-list nil)))

    ;; Set the shell-command. FIXME: Sometimes (like when combining
    ;; 001 and 002) not all regexps are applied.
    (while (and flist matched-regexp
                (string-match matched-regexp (car flist)))
      (setq flist (cdr flist)))
    (setq cmds (and (not flist) cmds))
    (cond ((not (cdr cmds))
           (eval (car cmds))) ; one command
          (t
           (mapcar (function eval) cmds)))))

(defun dired-run-shell-command (command)
  ;; Process special syntax. Make sure it supports ? and *.
  (let ((scf (function shell-command))
        run-in-shell keep-output)
    (while (string-match "{run:shell} ?" command)
      (setq command (replace-match "" t t command))
      (setq run-in-shell t))
    (while (string-match "{run:out} ?" command)
      (setq command (replace-match "" t t command))
      (setq keep-output t))

    (if (and run-in-shell
             (functionp runner-shell-function))
        (progn
          (setq scf runner-shell-function)
          (let ((handler
                 (find-file-name-handler (directory-file-name default-directory)
                                         'scf)))
            (if handler (apply handler scf (list command))
              (funcall scf command))))
      ;; not running in a shell
      (let ((handler
             (find-file-name-handler (directory-file-name default-directory)
                                     'scf)))
        (if keep-output
            (let ((outbuf (concat "*Runner Command*: " command)))
              ;; Make a unique buffer if buffer is busy.
              (when (get-buffer-process outbuf)
                (with-current-buffer outbuf
                  (rename-buffer (concat "*Runner Command More*: " command) t)))
              (if handler (apply handler
                                 scf (list command outbuf))
                (funcall scf command outbuf)))
          (progn
            ;; Make a unique buffer if buffer is busy.
            (when (get-buffer-process "*Runner Output*")
              (with-current-buffer "*Runner Output*"
                (rename-buffer "*Runner Output More*" t)))
            (if handler (apply handler scf (list command "*Runner Output*"))
              (funcall scf command "*Runner Output*")))))))
  ;; return nil
  nil)

(defun runner-background-frame-function (buf par-list)
  (other-window 1)
  (goto-char (point-min)))

;; FIXME: Do we really need to set this to nil?
(setq dired-guess-shell-alist-user nil)
(runner-settings-load)
(runner t)

(when runner-run-in-background
  ;; Output buffers should go to the background.
  (add-to-list 'special-display-buffer-names
               '("*Runner Output*" runner-background-frame-function nil)))

(provide 'runner)
;;; runner.el ends here.
