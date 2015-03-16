;;; interaction-log.el --- exhaustive log of interactions with Emacs


;; Copyright (C) 2012-2014 Michael Heerdegen

;; Author: Michael Heerdegen <michael_heerdegen@web.de>
;; Maintainer: Michael Heerdegen <michael_heerdegen@web.de>
;; Created: Dec 29 2012
;; Keywords: convenience
;; Homepage: https://github.com/michael-heerdegen/interaction-log.el
;; Version: 1.2
;; Package-Requires: ((cl-lib "0"))


;; This file is not part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:
;;;
;;; This package provides a buffer *Emacs Log* showing the last hit
;;; keys and executed commands, messages and file loads in
;;; chronological order.  This enables you to reconstruct the last
;;; seconds of your work with Emacs.  It's also useful for
;;; giving presentations or making screencasts with Emacs.
;;;
;;; Installation: Put this file in your load path and byte-compile it.
;;; To start logging automatically at startup, add this to your init
;;; file:
;;;
;;; (require 'interaction-log)
;;; (interaction-log-mode +1)
;;;
;;; You probably will want to have a hotkey for showing the log
;;; buffer, so also add something like
;;;
;;; (global-set-key
;;;  (kbd "C-h C-l")
;;;  (lambda () (interactive) (display-buffer ilog-buffer-name)))
;;;
;;; Alternatively, there is a command `ilog-show-in-new-frame' that
;;; you can use to display the log buffer in a little new frame whose
;;; parameters can be controlled by customizing
;;; `ilog-new-frame-parameters'.
;;;
;;; Usage: Use `interaction-log-mode' to toggle logging.  Enabling the
;;; mode will cause all messages and all pressed keys (along with the
;;; actually executed command and the according buffer) to be logged
;;; in the background.  Also loading of files will be logged.  If an
;;; executed command causes any buffer to change, it will be
;;; highlighted in orange so you can check if you made changes by
;;; accident.  If a command caused any message to be displayed in the
;;; echo area (e.g. if an error occurred), it is highlighted in red.
;;; 
;;; If you find any bugs or have suggestions for improvement, please
;;; tell me!


;;; Code:

(require 'cl-lib)
(require 'timer)
(require 'font-lock)
(require 'easymenu)


;;; Customizable stuff

(defgroup interaction-log nil
  "Emacs Interaction Log."
  :prefix "ilog-"
  :group 'convenience)

(defface ilog-non-change-face
  '((((class color) (min-colors 88) (background light)) :foreground "ForestGreen")
    (((class color) (min-colors 88) (background dark))  :foreground "YellowGreen")
    (((class color) (min-colors 8))                     :foreground "Green"))
  "Face for keys that didn't cause buffer changes."
  :group 'interaction-log)

(defface ilog-change-face
  '((((class color) (min-colors 88)) :foreground "DarkOrange")
    (((class color) (min-colors 8))  :foreground "Yellow"))
  "Face for keys that caused buffer changes."
  :group 'interaction-log)

(defface ilog-echo-face
  '((((class color) (min-colors 8)) :foreground "Red")
    (t :inverse-video t))
  "Face for keys that caused text being displayed in the echo area."
  :group 'interaction-log)

(defface ilog-buffer-face
  '((((class color) (min-colors 88) (background light)) :foreground "DarkBlue")
    (((class color) (min-colors 88) (background dark))  :foreground "LightSlateBlue")
    (((class color) (min-colors 8))                     :foreground "Blue"))
  "Face for buffer names."
  :group 'interaction-log)

(defface ilog-load-face
  '((((class color) (min-colors 88) (background light)) :foreground "Gold4")
    (((class color) (min-colors 88) (background dark))  :foreground "Yellow")
    (((class color) (min-colors 8))                     :foreground "Magenta"))
  "Face for lines describing file loads."
  :group 'interaction-log)

(defface ilog-message-face
  '((((class color grayscale) (min-colors 88) (background light))
     :foreground "grey50")
    (((class color grayscale) (min-colors 88) (background dark))
     :foreground "grey70"))
  "Face for messages."
  :group 'interaction-log)

(defcustom ilog-tail-mode 'strict
  "When non-nil, let the cursor follow the end of the log buffer.
When t, this is like in *Messages*: if you put the cursor at the
end of the *Emacs Log* buffer, it will stay at the buffer's end
when more stuff is added.  When nil, the cursor will stay at the
same text position.  When the value is strict, move
`window-point' to the end even when it was not there, except for
the case that the log buffer window is current."
  :group 'interaction-log
  :type '(choice
          (const    nil)
          (const      t)
          (const strict)))

(defcustom ilog-log-max t
  "Maximum number of lines to keep in the *Emacs Log* buffer.
If t, don't truncate the buffer when it becomes large.

Note: Displaying a very large log buffer may increase Emacs CPU
usage as long as the buffer is displayed.  Don't set this to t if
you plan to display the log all the time."
  :group 'interaction-log :type '(choice (const  :tag "Unlimited" t)
                                         (number :tag "lines")))

(defcustom ilog-idle-time .1
  "Refresh log every this many seconds idle time."
  :group 'interaction-log :type 'number)

(defcustom ilog-initially-show-buffers nil
  "Whether to show buffer names initially.
You can also toggle displaying buffer names in the log buffer by
typing \\<ilog-log-buffer-mode-map>\\[ilog-toggle-display-buffer-names]."
  :group 'interaction-log :type 'boolean)

(defvar ilog-log-buffer-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [?t] #'ilog-toggle-view)
    (define-key map [?b] #'ilog-toggle-display-buffer-names)
    (define-key map [?q] #'bury-buffer)
    map)
  "Keymap for `ilog-log-buffer-mode'.")

(defcustom interaction-log-mode-hook '()
  "Hook run when entering `interaction-log-mode'."
  :group 'interaction-log :type 'hook)

(defcustom ilog-log-buffer-mode-hook '()
  "Hook run when entering `ilog-log-buffer-mode'."
  :group 'interaction-log :type 'hook)

(defcustom ilog-print-lambdas nil
  "Whether to print anonymous functions in the log.
Controls how commands that are not associated with a symbol are
printed.
When nil, replace all anonymous commands with a placeholder.
When t, print all anonymous commands.
Any other value means: print uncompiled lambda expressions, but use a
placeholder for byte code functions."
  :group 'interaction-log
  :type '(choice
          (const :tag "Don't print anonymous commands"   nil)
          (const :tag "Print lambdas, but not byte code" not-compiled)
          (const :tag "Always print anonymous commands"  t)))

(defcustom ilog-new-frame-parameters
  '((menu-bar-lines .         0)
    (vertical-scroll-bars . nil)
    (border-width .           0)
    (left-fringe  .           0)
    (right-fringe .           1)
    (left         .      (- -17))
    (user-position .          t)
    (width        .          35)
    (height       .          20)
    (font         .         "8")
    (background-color . "black")
    (foreground-color . "gray90")
    (background-mode  . dark))
  "Alist of frame parameters for `ilog-show-in-new-frame'.
These parameters are applied to the new frame."
  :group 'interaction-log
  :type '(repeat (cons :format "%v"
		       (symbol :tag "Parameter")
		       (sexp :tag "Value"))))


;;; Other stuff

(easy-menu-define ilog-minor-mode-menu ilog-log-buffer-mode-map
  "Menu used when `ilog-log-buffer-mode' is active."
  '("ILog"
    ["Toggle view"           ilog-toggle-view]
    ["Toggle buffer names"   ilog-toggle-display-buffer-names]))


;;; Internal Variables

(defvar ilog-recent-commands nil)

(defvar ilog-changing-log-buffer-p nil
  "Non-nil means buffer changes should not be recorded.
Bound to t  when adding to the log buffer.")

(defvar ilog-buffer-name "*Emacs Log*"
  "The name used for the log buffer.")

(defvar ilog-recent-commands-messages-marker
  (with-current-buffer (get-buffer-create "*Messages*")
    (let ((marker (point-min-marker)))
      (set-marker-insertion-type marker nil)
      marker))
  "Marking how far we got with copying from *Messages*.")

(defvar ilog-truncation-timer nil)

(defvar ilog-insertion-timer nil)

(defvar ilog-display-state nil)

(defvar ilog-last-inserted-command nil
  "Last inserted command, as a `ilog-log-entry' struct.
nil when the last inserted line was not a command (even if a
post-messg).")

(defvar ilog-self-insert-command-regexps
  '("self-insert-command$" "isearch-printing-char" "term-send-raw")
  "List of regexps matching self inserting commands.
Commands whose names are matched by any of these regexps are
displayed specially in the log buffer.  Successive invocations
are accumulated in one line, while command and buffer name are
neglected.")


;;; User commands

(define-minor-mode interaction-log-mode
  "Global minor mode logging keys, commands, file loads and messages.
Logged stuff goes to the *Emacs Log* buffer."
  :group 'interaction-log
  :lighter nil
  :global t
  :after-hook interaction-log-mode-hook
  (if interaction-log-mode
      (progn
        (add-hook 'after-change-functions #'ilog-note-buffer-change)
        (add-hook 'pre-command-hook       #'ilog-record-this-command)
        (add-hook 'post-command-hook      #'ilog-post-command)
        (setq ilog-truncation-timer (run-at-time 30 30 #'ilog-truncate-log-buffer))
        (setq ilog-insertion-timer (run-with-timer ilog-idle-time ilog-idle-time
						   #'ilog-timer-function))
        (message "Interaction Log: started logging in %s" ilog-buffer-name)
	(easy-menu-add ilog-minor-mode-menu))
    (remove-hook 'after-change-functions #'ilog-note-buffer-change)
    (remove-hook 'pre-command-hook       #'ilog-record-this-command)
    (remove-hook 'post-command-hook      #'ilog-post-command)
    (when (timerp ilog-truncation-timer) (cancel-timer ilog-truncation-timer))
    (setq ilog-truncation-timer nil)
    (when (timerp ilog-insertion-timer) (cancel-timer ilog-insertion-timer))
    (setq ilog-insertion-timer nil)))

(defun ilog-toggle-view ()
  "Toggle between different view states.
Toggle successively between showing only messages, only
commands, only file loads, and everything."
  (interactive)
  (ilog-log-buf-current-or-barf)
  (cl-case ilog-display-state
    ((nil)
     (add-to-invisibility-spec 'ilog-command)
     (add-to-invisibility-spec 'ilog-buffer)
     (add-to-invisibility-spec 'ilog-load)
     (setq ilog-display-state 'messages)
     (message "Showing only messages"))
   ((messages)
    (remove-from-invisibility-spec 'ilog-command)
    (when ilog-initially-show-buffers
      (remove-from-invisibility-spec 'ilog-buffer))
    (add-to-invisibility-spec 'ilog-message)
    (setq ilog-display-state 'commands)
    (message "Showing only commands"))
   ((commands)
    (remove-from-invisibility-spec 'ilog-load)
    (add-to-invisibility-spec 'ilog-command)
    (add-to-invisibility-spec 'ilog-buffer)
    (add-to-invisibility-spec 'ilog-message)
    (setq ilog-display-state 'loads)
    (message "Showing only file loads"))
   ((loads)
    (remove-from-invisibility-spec 'ilog-load)
    (remove-from-invisibility-spec 'ilog-command)
    (when ilog-initially-show-buffers
      (remove-from-invisibility-spec 'ilog-buffer))
    (remove-from-invisibility-spec 'ilog-message)
    (setq ilog-display-state nil)
    (message "Showing everything"))))

(defun ilog-toggle-display-buffer-names ()
  "Toggle display of buffers in log buffer."
  (interactive)
  (ilog-log-buf-current-or-barf)
  (unless (memq 'ilog-command buffer-invisibility-spec)
    (if (memq 'ilog-buffer buffer-invisibility-spec)
	(remove-from-invisibility-spec 'ilog-buffer)
      (add-to-invisibility-spec 'ilog-buffer))))

(defun ilog-show-in-new-frame ()
  "Display log in a pop up frame.
Customize `ilog-new-frame-parameters' to specify parameters of
the newly created frame."
  (interactive)
  (unless interaction-log-mode (interaction-log-mode +1))
  (let ((win (display-buffer-pop-up-frame
	      (get-buffer ilog-buffer-name)
	      `((pop-up-frame-parameters . ,ilog-new-frame-parameters)))))
    (set-window-dedicated-p win t)
    win))

;;; Helper funs

(defun ilog-self-insert-command-p (object)
  "Whether OBJECT is a self inserting command.
This is the case when OBJECT is an `fboundp' symbol whose name is
matched by any regexp in  `ilog-self-insert-command-regexps'."
  (let (name)
    (and (symbolp object)
	 (setq name (symbol-name object))
	 (catch 'match
	   (mapc (lambda (regexp) (when (string-match-p regexp name) (throw 'match t)))
		 ilog-self-insert-command-regexps)
	   nil)
	 (fboundp object))))

(defun ilog-log-buf-current-or-barf ()
  "Barf if the ilog log buffer is not current."
  (unless (eq (current-buffer) (get-buffer ilog-buffer-name))
    (error "You can use this command in %s only" ilog-buffer-name)))

(define-minor-mode ilog-log-buffer-mode
  "Minor mode for the ilog log buffer.

Key bindings:

\\{ilog-log-buffer-mode-map}"
  :keymap ilog-log-buffer-mode-map :lighter " Log"
  :after-hook ilog-log-buffer-mode-hook)

(cl-defstruct ilog-log-entry
  keys command buffer-name (pre-messages "") (post-messages "") changed-buffer-p (mult 1))

(defun ilog-log-file-load (file)
  "Annotate a file load."
  (when ilog-recent-commands
    (cl-callf concat (ilog-log-entry-post-messages (car ilog-recent-commands))
      (ilog-get-last-messages)
      (propertize
       (concat
	(file-name-sans-extension (file-name-nondirectory file)) " was loaded"
	(if load-file-name
	    (concat " by " (file-name-sans-extension (file-name-nondirectory load-file-name)))
	  "")
	" from " file)
       'load-message t)
      "\n")))

(add-hook 'after-load-functions #'ilog-log-file-load)

(defun ilog-get-last-messages ()
  "Return a string including the last messages.
This is a multiline string containing all messages that appeared
in *Messages* since the last call of this function."
  (with-current-buffer (get-buffer-create "*Messages*")
    (prog1 (if (< ilog-recent-commands-messages-marker (point-max))
               (buffer-substring ilog-recent-commands-messages-marker (point-max))
             "")
      (move-marker ilog-recent-commands-messages-marker (point-max)))))

(defun ilog-entering-password-p ()
  "Whether the user is currently entering a password."
  (and
   (boundp 'read-passwd-map)
   (keymapp read-passwd-map)
   (eq read-passwd-map (current-local-map))))

(defun ilog-record-this-command ()
  "Push info about the current command to `ilog-recent-commands'."
  (let ((keys (if (ilog-entering-password-p) [??] ;hide passwords!
		(apply #'vector
		       (mapcar
			(lambda (key) (if (consp key) ;; (mouse-... event-data)
				     (car key)
				   key))
			(this-command-keys-vector)))))
	(command (cond
		  ((ilog-entering-password-p) "(entering-password)")
		  ((symbolp this-command) this-command)
		  ((not ilog-print-lambdas) "<anonymous command>")
		  ((or (not (byte-code-function-p this-command))
		       (eq t ilog-print-lambdas))
		   this-command)
		  (t "<byte code>")))
	(buffer-name (buffer-name))
	(pre-messages (ilog-get-last-messages))
	(last-log-entry (car ilog-recent-commands)))
    (if (and last-log-entry ;check whether we can accumulate while recording
	     (not (ilog-self-insert-command-p command))
	     (equal keys        (ilog-log-entry-keys        last-log-entry))
	     (equal command     (ilog-log-entry-command     last-log-entry))
	     (equal buffer-name (ilog-log-entry-buffer-name last-log-entry))
	     (string= "" pre-messages)
	     (string= "" (ilog-log-entry-post-messages last-log-entry)))
	(cl-incf (ilog-log-entry-mult last-log-entry))
      (push (make-ilog-log-entry
	     :keys keys
	     :command command
	     :buffer-name buffer-name
	     :pre-messages pre-messages)
	    ilog-recent-commands))))

(defun ilog-post-command ()
  "DTRT after a command was executed.
Goes to `post-command-hook'."
  (add-hook 'after-change-functions #'ilog-note-buffer-change) ;$$$$ bug#16796
  (when ilog-recent-commands
    (cl-callf concat
        (ilog-log-entry-post-messages (car ilog-recent-commands)) (ilog-get-last-messages))))

(defun ilog-last-line-pos (&optional beg-of-last-line)
  "Where to move point in log buffer after insertion.
This is `point-max' or the beginning of the last line when
BEG-OF-LAST-LINE is non-nil."
  (save-excursion
    (goto-char (point-max))
    (if beg-of-last-line (line-beginning-position) (point))))

(defun ilog-timer-function ()
  "Transform and insert pending data into the log buffer."
  (when (let ((current-idle-time (current-idle-time)))
	  (and current-idle-time (> (time-to-seconds current-idle-time) ilog-idle-time)))
    (let* ((ilog-buffer
	    (or (get-buffer ilog-buffer-name)
		(with-current-buffer (generate-new-buffer ilog-buffer-name)
		  (setq buffer-invisibility-spec (if ilog-initially-show-buffers '() '(ilog-buffer)))
		  (set (make-local-variable 'scroll-margin) 0)
		  (set (make-local-variable 'scroll-conservatively) 10000)
		  (set (make-local-variable 'scroll-step) 1)
		  (set (make-local-variable 'cursor-in-non-selected-windows) nil)
		  (setq buffer-read-only t)
		  (ilog-log-buffer-mode)
		  (current-buffer))))
	   eob ateobp ilog-eob-wins)
      (with-current-buffer ilog-buffer
	(when ilog-tail-mode
	  (setq eob (ilog-last-line-pos truncate-lines))
	  (setq ateobp (>= (point) eob))
	  (setq ilog-eob-wins
		(if (eq t ilog-tail-mode)
		    (delq nil
			  (mapcar (lambda (win) (and (>= (window-point win) eob) win))
				  (get-buffer-window-list ilog-buffer nil t)))
		  (delq (selected-window) (get-buffer-window-list ilog-buffer nil t)))))
	(let ((ilog-changing-log-buffer-p t) (deactivate-mark nil) (inhibit-read-only t) (firstp t))
	  (save-excursion
	    (goto-char (point-max))
	    (if ilog-recent-commands
		(dolist (entry (nreverse ilog-recent-commands))
		  (let ((keys        (ilog-log-entry-keys             entry))
			(command     (ilog-log-entry-command          entry))
			(buf         (ilog-log-entry-buffer-name      entry))
			(pre-mess    (ilog-log-entry-pre-messages     entry))
			(post-mess   (ilog-log-entry-post-messages    entry))
			(changedp    (ilog-log-entry-changed-buffer-p entry))
			(mult        (ilog-log-entry-mult             entry)))
		    
		    ;; Insert cached commands
		    ;; 
		    ;; Accumulating commands satisfying `ilog-self-insert-command-p'
		    ;; is done by simply going backwards.
		    ;; 
		    ;; Other commands were accumulated right from recording.  We have
		    ;; to check whether	the first cached command may be	added to the last
		    ;; inserted line.
		    ;;
		    ;; Newline characters are always prepended to a chunk when
		    ;; appropriate and share its invisible spec.
		    
		    (when firstp
		      (setq firstp nil)
		      ;; check whether to combine with last inserted line
		      (when (and ilog-last-inserted-command
				 (not (ilog-self-insert-command-p command))
				 (equal keys    (ilog-log-entry-keys    ilog-last-inserted-command))
				 (equal command (ilog-log-entry-command ilog-last-inserted-command))
				 (equal buf (ilog-log-entry-buffer-name ilog-last-inserted-command))
				 (string= pre-mess "") (string= post-mess "")
				 (equal changedp (ilog-log-entry-changed-buffer-p
						  ilog-last-inserted-command))				 )
			(cl-incf mult (ilog-log-entry-mult ilog-last-inserted-command))
			(cl-incf (ilog-log-entry-mult entry)
			      (ilog-log-entry-mult ilog-last-inserted-command))
			;; delete last log line
			(search-backward-regexp "[^[:space:]]")
			(beginning-of-line)
			(delete-region (point) (point-max))))
		    (insert (if (ilog-self-insert-command-p command)
				(progn
				  ;; check whether to add to last line
				  (if (not (and ilog-last-inserted-command
						(equal pre-mess "")
						(ilog-self-insert-command-p
						 (ilog-log-entry-command ilog-last-inserted-command))))
				      (insert (propertize (if (looking-back "\\`\\|\n") "" "\n")
							  'invisible 'ilog-command))
				    (search-backward-regexp "[^[:space:]]")
				    (forward-char 1)
				    (delete-region (point) (point-max))
				    (goto-char (point-max)))
				  (propertize (key-description keys)
					      'face (cl-case changedp
						      ((t)    'ilog-change-face)
						      ((echo) 'ilog-echo-face)
						      (t      'ilog-non-change-face))
					      'invisible 'ilog-command))
			      (concat
			       (ilog-format-messages pre-mess)
			       (propertize (if (looking-back "\\`\\|\n") "" "\n")
					   'invisible 'ilog-command)
			       (propertize (concat (if (> mult 1) (format "%s * " mult) "")
						   (key-description keys))
					   'face (cl-case changedp
						   ((t)    'ilog-change-face)
						   ((echo) 'ilog-echo-face)
						   (t      'ilog-non-change-face))
					   'invisible 'ilog-command)
			       (propertize (concat " " (format "%s" command))
					   'invisible 'ilog-command)
			       (propertize (format " %s" buf)
					   'face 'ilog-buffer-face
					   'invisible 'ilog-buffer)))
			    (ilog-format-messages post-mess))
		    (setq ilog-last-inserted-command (and (equal post-mess "") entry))))
	      ;; No keys were hit.  Only collect new messages.
	      (let ((messages (ilog-get-last-messages)))
		(unless (string= messages "")
		  (insert (ilog-format-messages messages))
		  (setq ilog-last-inserted-command nil))))
	    (setq ilog-recent-commands ())))
	(when (buffer-modified-p)
	  ;; only do stuff triggering redisplay when buffer was modified
	  (set-buffer-modified-p nil)
	  (when ilog-tail-mode
	    (let ((end (ilog-last-line-pos truncate-lines)))
	      (if ilog-eob-wins
		  (dolist (win ilog-eob-wins)
		    (set-window-point win end))
		(when ateobp (goto-char end))))))))))

(defun ilog-cut-surrounding-newlines (string)
  "Cut all newlines at beginning and end of STRING.
Return the result."
  (when (string-match "\n+\\'" string)
    (setq string (substring string 0 (match-beginning 0))))
  (when (string-match "\\`\n+" string)
    (setq string (substring string (match-end 0))))
  string)

(defun ilog-format-messages (string)
  "Format and propertize messages in STRING."
  (if (and (stringp string) (not (equal string "")))
      (let ((messages (ilog-cut-surrounding-newlines string)))
	(mapconcat 
	 (lambda (line)
	   (let ((load-mesg-p (get-text-property 0 'load-message line)))
	     (propertize
	      (concat  "\n"
		       ;; (if load-mesg-p (make-string load-mesg-p ?\ ) "") ;;
		       line)
	      'face (if load-mesg-p 'ilog-load-face 'ilog-message-face)
	      'invisible (if load-mesg-p 'ilog-load 'ilog-message))))
	 (split-string messages "\n") ""))
    ""))

(defun ilog-note-buffer-change (&rest _)
  "Remember that this command changed any buffer.
Also remember whether this command caused any output in the Echo
Area."
  ;; I could alternatively use `command-error-function' for catching
  ;; errors
  (when (and (not ilog-changing-log-buffer-p)
             ilog-recent-commands)
    (setf (ilog-log-entry-changed-buffer-p (car ilog-recent-commands))
	  (if (string-match "\\` \\*Echo Area" (buffer-name))
	      'echo
	    t))))

(defun ilog-truncate-log-buffer ()
  "Truncate the log buffer to `ilog-log-max' lines."
  (let ((buf (get-buffer ilog-buffer-name)))
    (when (and buf
               (not (eq buf (current-buffer))) ; avoid truncation when log buffer is current
               (numberp ilog-log-max))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (save-excursion
            (goto-char (point-max))
            (forward-line (- ilog-log-max))
            (delete-region (point-min) (point))
	    (set-buffer-modified-p nil)))))))


(provide 'interaction-log)

;;; interaction-log.el ends here
