;; proof.el  Proof General loader.  All files require this one.
;;
;; Copyright (C) 1998,9 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 `(progn
    (defvar ,var nil ,docstring)
    (make-variable-buffer-local (quote ,var))
    (setq-default ,var ,value)))

(require 'proof-site)			; site config

;; cl is dumped with my XEmacs 20.4, but not FSF Emacs 20.2.
(require 'cl)				



(require 'proof-config)			; configuration variables

(require 'proof-splash)			; display splash screen

;;;
;;; Emacs libraries
;;;

;; browse-url function doesn't seem to be autoloaded in
;; XEmacs 20.4, but it is in FSF Emacs 20.2.
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

(autoload 'font-lock-fontify-region "font-lock")
(autoload 'font-lock-append-text-property "font-lock")

;;;
;;; Autoloads for main code
;;;

(autoload 'proof-mode "proof-script"
  "Proof General major mode class for proof scripts.")

(autoload 'proof-shell-mode "proof-shell"
  "Proof General shell mode class for proof assistant processes")

;; FIXME: toolbar defines scripting menu as well as toolbar,
;; so FSF *does* need to load it.  Could consider separating
;; menu code from proof-toolbar.

;;(if (featurep 'toolbar)
    ;; toolbar code is only loaded for XEmacs
    (autoload 'proof-toolbar-setup "proof-toolbar"
      "Initialize Proof General toolbar and enable it for the current buffer" t)
;;;  (defun proof-toolbar-setup ()))


;;;
;;; More autoloads to help define interface between files
;;;

(autoload 'proof-shell-available-p "proof-shell"
  "Returns non-nil if there is a proof shell active and available.")

(autoload 'proof-shell-invisible-command "proof-shell"
  "Send CMD to the proof process without revealing it to the user.")

(autoload 'proof-x-symbol-toggle "proof-x-symbol"
  "Toggle support for x-symbol.  With optional ARG, force on if ARG<>0."
  t)

(autoload 'proof-x-symbol-decode-region "proof-x-symbol"
  "Call (x-symbol-decode-region START END), if x-symbol support is enabled.")

(autoload 'proof-x-symbol-shell-config "proof-x-symbol"
  "Activate/deactivate x-symbol in Proof General shell, goals, and response buffer.")

(autoload 'proof-x-symbol-mode "proof-x-symbol"
  "Turn on or off x-symbol mode in the current buffer.")

;;;
;;; Global variables
;;;

(deflocal proof-buffer-type nil 
  "Symbol indicating the type of this buffer: 'script, 'shell, or 'pbp.")

(defvar proof-shell-busy nil 
  "A lock indicating that the proof shell is processing.
When this is non-nil, proof-shell-ready-prover will give
an error.")

(defvar proof-included-files-list nil 
  "List of files currently included in proof process.
This list contains files in canonical truename format
(see `file-truename').

Whenever a new file is being processed, it gets added to this list
via the proof-shell-process-file configuration settings.
When the prover retracts a file, this list is resynchronised via the
proof-shell-retract-files-regexp and proof-shell-compute-new-files-list 
configuration settings.

Only files which have been *fully* processed should be included here.
Proof General itself will automatically add the filenames of a script
buffer which has been completely read when scripting is deactivated.
It will automatically remove the filename of a script buffer which
is completely unread when scripting is deactivated.

NB: Currently there is no generic provision for removing files which
are only partly read-in due to an error, so ideally the proof assistant
should only output a processed message when a file has been successfully
read.")


(defvar proof-script-buffer nil
  "The currently active scripting buffer or nil if none.")

(defvar proof-shell-buffer nil
  "Process buffer where the proof assistant is run.")

(defvar proof-goals-buffer nil
  "The goals buffer (also known as the pbp buffer).")

(defvar proof-response-buffer nil
  "The response buffer.")

(defvar proof-shell-proof-completed nil
  "Flag indicating that a completed proof has just been observed.")

;; FIXME da: remove proof-terminal-string.  At the moment some
;; commands need to have the terminal string, some don't.
;; It's used variously in proof-script and proof-shell.
;; We should assume commands are terminated at the specific level.

(defvar proof-terminal-string nil 
  "End-of-line string for proof process.")



;;;
;;; Utilities/macros used in several files  (-> proof-utils)
;;;

;; -----------------------------------------------------------------
;; Handy macros

(defmacro proof-with-current-buffer-if-exists (buf &rest body)
  "As with-current-buffer if BUF exists, otherwise nothing."
  `(if (buffer-live-p ,buf)
       (with-current-buffer ,buf
	 ,@body)))

;; -----------------------------------------------------------------
;; Buffers and filenames

(defun proof-file-truename (filename)
  "Returns the true name of the file FILENAME or nil if file non-existent."
  (and filename (file-exists-p filename) (file-truename filename)))

(defun proof-file-to-buffer (filename)
  "Find a buffer visiting file FILENAME, or nil if there isn't one."
  (let* ((buffers (buffer-list))
	 (pos
	  (position (file-truename filename)
		    (mapcar 'proof-file-truename
			    (mapcar 'buffer-file-name
				    buffers))
		    :test 'equal)))
    (and pos (nth pos buffers))))

(defun proof-files-to-buffers (filenames)
  "Converts a list of FILENAMES into a list of BUFFERS."
  (if (null filenames) nil
    (let* ((buffer (proof-file-to-buffer (car filenames)))
	  (rest (proof-files-to-buffers (cdr filenames))))
      (if buffer (cons buffer rest) rest))))

(defun proof-buffers-in-mode (mode &optional buflist)
  "Return a list of the buffers in the buffer list in major-mode MODE.
Restrict to BUFLIST if it's set."
  (let ((bufs-left (or buflist (buffer-list))) 
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf (eq mode major-mode))
	  (setq bufs-got (cons buf bufs-got))))))

;; -----------------------------------------------------------------
;; Key functions

(defun proof-define-keys (map kbl)
  "Adds keybindings KBL in MAP.
The argument KBL is a list of tuples (k . f) where `k' is a keybinding
(vector) and `f' the designated function."
  (mapcar
   (lambda (kbl)
     (let ((k (car kbl)) (f (cdr kbl)))
         (define-key map k f)))
   kbl))

;; -----------------------------------------------------------------
;; Display functions

;; FIXME: this function should be combined with
;; proof-shell-maybe-erase-response-buffer.  Should allow
;; face of nil for unfontified output.
(defun proof-response-buffer-display (str &optional face)
  "Display STR with FACE in response buffer and return fontified STR."
  (let (start end)
    (with-current-buffer proof-response-buffer
      ;; da: I've moved newline before the string itself, to match
      ;; the other cases when messages are inserted and to cope
      ;; with warnings after delayed output (non newline terminated).
      (goto-char (point-max))
      (newline)				
      (setq start (point))
      (insert str) 
      (proof-x-symbol-decode-region start (point))
      (setq end (point-max))
      (save-excursion
	(font-lock-set-defaults)		;required for FSF Emacs 20.2
;; FIXME da: does this break anything in LEGO or others?
;DvO	(font-lock-fontify-region start end)
	(if face (font-lock-append-text-property start end 'face face)))
      (buffer-substring start end))))

;; FIXME da: this window dedicated stuff is a real pain and I've
;; spent ages inserting workarounds.  Why do we want it??
;; The latest problem is that with
;;  (setq special-display-regexps
;;       (cons "\\*Inferior .*-\\(goals\\|response\\)\\*"
;;	     special-display-regexps))
;; I get the script buffer made into a dedicated buffer,
;; presumably because the wrong window is selected below?

(defun proof-display-and-keep-buffer (buffer &optional pos)
  "Display BUFFER and mark window according to `proof-window-dedicated'.
If optional POS is present, will set point to POS.  
Otherwise move point to the end of the buffer.
Ensure that point is visible in window."
  (let (window)
    (save-excursion
      (set-buffer buffer)
      (display-buffer buffer)
      (setq window (get-buffer-window buffer 'visible))
      (set-window-dedicated-p window proof-window-dedicated)
      (and window
	   (save-selected-window
	     (select-window window)
	     
	     ;; tms: I don't understand why the point in
	     ;; proof-response-buffer is not at the end anyway.
	     ;; Is there a superfluous save-excursion somewhere?
	     ;; da replies: I think it's because of a *missing*
	     ;; save-excursion above around the font-lock stuff.
	     ;; Adding one has maybe fixed this problem.
	     ;; 10.12.98 Experiment removing this so that point
	     ;; doesn't always go to end of goals buffer
	     ;; RESULT: point doesn't go to end of response
	     ;; buffer.  Hypothesis above was wrong, so this
	     ;; is re-added and optional POS argument added
	     ;; for this function.
	     (goto-char (or pos (point-max)))
	     (if pos (beginning-of-line)) ;  Normalization

	     ;; Ensure point visible
	     (or (pos-visible-in-window-p (point) window)
		 (recenter -1)))))))

(defun proof-clean-buffer (buffer)
  "Erase buffer and hide from display if proof-auto-delete-windows set.
Auto deletion only affects selected frame.  (We assume that the selected
frame is the one showing the script buffer.)"
  (with-current-buffer buffer
    ;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
    (erase-buffer)
    (if proof-auto-delete-windows
	(delete-windows-on buffer t))))

(defun proof-message (&rest args)
  "Issue the message ARGS in the response buffer and display it."
    (proof-response-buffer-display (apply 'concat args))
    (proof-display-and-keep-buffer proof-response-buffer))

(defun proof-warning (&rest args)
  "Issue the warning ARGS in the response buffer and display it.
The warning is coloured with proof-warning-face."
    (proof-response-buffer-display (apply 'concat args) 'proof-warning-face)
    (proof-display-and-keep-buffer proof-response-buffer))

(defmacro proof-debug (&rest args)
  "Issue the debugging messages ARGS in the response buffer, display it.
If proof-show-debug-messages is nil, do nothing."
  (if proof-show-debug-messages
      `(proof-warning ,@args)))



;; -----------------------------------------------------------------
;; Function for submitting bug reports.

(defun proof-submit-bug-report ()
  "Submit an bug report or other report for Proof General."
  (interactive)
  (require 'reporter)
  (let
      ((reporter-prompt-for-summary-p 
	"(Very) brief summary of problem or suggestion: "))
    (reporter-submit-bug-report
     "proofgen@dcs.ed.ac.uk"
     "Proof General" 
     (list 'proof-general-version 'proof-assistant)
     nil nil
     "[When reporting a bug, please include a small test case for us to repeat it.]")))




(provide 'proof)
;; proof.el ends here
