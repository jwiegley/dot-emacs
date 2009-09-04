;;; scomint.el --- Simplified comint for less interactive shells
;;
;; Copyright (C) 2009 LFCS Edinburgh.
;; Author:    David Aspinall
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$

;;; Commentary:
;; 
;; This is a heavily simplified comint for Proof General.
;; Much of the code is taken from comint.el.
;;
;; The reason to provide this is to remove some of
;; the interactive features which are otherwise 
;; hard to disentangle.  
;;

(defface scomint-highlight-input '((t (:weight bold)))
  "Face to use to highlight user input."
  :group 'scomint)

(defface scomint-highlight-prompt
  '((((min-colors 88) (background dark)) (:foreground "cyan1"))
    (((background dark)) (:foreground "cyan"))
    (t (:foreground "dark blue")))
  "Face to use to highlight prompts."
  :group 'scomint)

(defvar scomint-buffer-maximum-size 800000
  "The maximum size in characters for SComint buffers.
SComint buffers are truncated from the top to be no greater than this number,
if non-nil.")

(defvar scomint-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-m" 'scomint-send-input)
    (define-key map "\C-c\C-c" 'interrupt-process)
    map))

(defvar scomint-last-input-start nil)
(defvar scomint-last-input-end nil)
(defvar scomint-last-output-start nil)

(defvar scomint-exec-hook nil
  "Hook run each time a process is exec'd by `scomint-exec'.
This is called after the process is cranked up.  It is useful for things that
must be done each time a process is executed in a Comint mode buffer (e.g.,
`(process-kill-without-query)').")

(put 'scomint-mode 'mode-class 'special)


(define-derived-mode scomint-mode fundamental-mode "SComint"
  "Major mode for interacting with a background inferior interpreter.
Interpreter name is same as buffer name, sans the asterisks.
Return at end of buffer sends line as input.
Return not at end copies rest of line to end and sends it.

\\{scomint-mode-map}

Entry to this mode runs the hooks on `scomint-mode-hook'."
  (setq mode-line-process '(":%s"))
  (set (make-local-variable 'scomint-last-input-start) (point-min-marker))
  (set (make-local-variable 'scomint-last-input-end) (point-min-marker))
  (set (make-local-variable 'scomint-last-output-start) (make-marker))
  (set (make-local-variable 'window-point-insertion-type) t)
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults '(nil t))
  (add-hook 'change-major-mode-hook 'font-lock-defontify nil t)
  (set (make-local-variable 'next-line-add-newlines) nil))

(defun scomint-check-proc (buffer)
  "Return non-nil if there is a living process associated w/buffer BUFFER.
Living means the status is `open', `run', or `stop'.
BUFFER can be either a buffer or the name of one."
  (let ((proc (get-buffer-process buffer)))
    (and proc (memq (process-status proc) '(open run stop)))))

;;;###autoload
(defun scomint-make-in-buffer (name buffer program &optional startfile &rest switches)
  "Make a Comint process NAME in BUFFER, running PROGRAM.
If BUFFER is nil, it defaults to NAME surrounded by `*'s.
PROGRAM should be either a string denoting an executable program to create
via `start-file-process', or a cons pair of the form (HOST . SERVICE) denoting
a TCP connection to be opened via `open-network-stream'.  If there is already
a running process in that buffer, it is not restarted.  Optional fourth arg
STARTFILE is the name of a file to send the contents of to the process.

If PROGRAM is a string, any more args are arguments to PROGRAM."
  (unless (or (fboundp 'start-process)
	      (fboundp 'start-file-process))
      (error "Multi-processing is not supported for this system"))
  (setq buffer (get-buffer-create (or buffer (concat "*" name "*"))))
  ;; If no process, or nuked process, crank up a new one and put buffer in
  ;; comint mode.  Otherwise, leave buffer and existing process alone.
  (unless (scomint-check-proc buffer)
    (with-current-buffer buffer
      (unless (derived-mode-p 'scomint-mode)
	(scomint-mode))) ; Install local vars, mode, keymap, ...
    (scomint-exec buffer name program startfile switches))
  buffer)

;;;###autoload
(defun scomint-make (name program &optional startfile &rest switches)
  "Make a Comint process NAME in a buffer, running PROGRAM.
The name of the buffer is made by surrounding NAME with `*'s.
PROGRAM should be either a string denoting an executable program to create
via `start-file-process', or a cons pair of the form (HOST . SERVICE) denoting
a TCP connection to be opened via `open-network-stream'.  If there is already
a running process in that buffer, it is not restarted.  Optional third arg
STARTFILE is the name of a file to send the contents of the process to.

If PROGRAM is a string, any more args are arguments to PROGRAM."
  (apply #'scomint-make-in-buffer name nil program startfile switches))


(defun scomint-exec (buffer name command startfile switches)
  "Start up a process named NAME in buffer BUFFER for Comint modes.
Runs the given COMMAND with SWITCHES with output to STARTFILE.
Blasts any old process running in the buffer.  Doesn't set the buffer mode.
You can use this to cheaply run a series of processes in the same Comint
buffer.  The hook `scomint-exec-hook' is run after each exec."
  (with-current-buffer buffer
    (let ((proc (get-buffer-process buffer)))	; Blast any old process.
      (if proc (delete-process proc)))
    ;; Crank up a new process
    (let ((proc
	   (if (consp command)
	       (open-network-stream name buffer (car command) (cdr command))
	     (scomint-exec-1 name buffer command switches))))
      (set-process-filter proc 'scomint-output-filter)
      ;; Jump to the end, and set the process mark.
      (goto-char (point-max))
      (set-marker (process-mark proc) (point))
      ;; Feed it the startfile.
      (cond (startfile
	     ;;This is guaranteed to wait long enough
	     ;;but has bad results if the comint does not prompt at all
	     ;;	     (while (= size (buffer-size))
	     ;;	       (sleep-for 1))
	     ;;I hope 1 second is enough!
	     (sleep-for 1)
	     (goto-char (point-max))
	     (insert-file-contents startfile)
	     (setq startfile (buffer-substring (point) (point-max)))
	     (delete-region (point) (point-max))
	     (scomint-send-string proc startfile)))
      (run-hooks 'scomint-exec-hook)
      buffer)))

;; This auxiliary function cranks up the process for comint-exec in
;; the appropriate environment.

(defun scomint-exec-1 (name buffer command switches)
  (let ((process-environment
	 (nconc
	  ;; If using termcap, we specify `emacs' as the terminal type
	  ;; because that lets us specify a width.
	  ;; If using terminfo, we specify `dumb' because that is
	  ;; a defined terminal type.  `emacs' is not a defined terminal type
	  ;; and there is no way for us to define it here.
	  ;; Some programs that use terminfo get very confused
	  ;; if TERM is not a valid terminal type.
	  ;; ;; There is similar code in compile.el.
	  (if (and (boundp 'system-uses-terminfo) system-uses-terminfo)
	      (list "TERM=dumb" "TERMCAP="
		    (format "COLUMNS=%d" (window-width)))
	    (list "TERM=emacs"
		  (format "TERMCAP=emacs:co#%d:tc=unknown:" (window-width))))
	  (unless (getenv "EMACS")
	    (list "EMACS=t"))
	  (list (format "INSIDE_EMACS=%s,comint" emacs-version))
	  process-environment))
	(default-directory
	  (if (file-accessible-directory-p default-directory)
	      default-directory
	    "/"))
	proc decoding encoding changed)
    (let ((exec-path (if (file-name-directory command)
			 ;; If the command has slashes, make sure we
			 ;; first look relative to the current directory.
			 (cons default-directory exec-path) exec-path)))
      (setq proc (apply (if (fboundp 'start-file-process) 
			    ;; da: start-file-process is Emacs23 only
			    'start-file-process 'start-process) 
			name buffer command switches)))
    ;; Some file name handler cannot start a process, fe ange-ftp.
    (unless (processp proc) (error "No process started"))
    (let ((coding-systems (process-coding-system proc)))
      (setq decoding (car coding-systems)
	    encoding (cdr coding-systems)))
    ;; Even if start-file-process left the coding system for encoding data
    ;; sent from the process undecided, we had better use the same one
    ;; as what we use for decoding.  But, we should suppress EOL
    ;; conversion.
    (if (and decoding (not encoding))
	(setq encoding (coding-system-change-eol-conversion decoding 'unix)
	      changed t))
    (if changed
	(set-process-coding-system proc decoding encoding))
    proc))




(defalias 'scomint-send-string 'process-send-string)

(defun scomint-send-eof ()
  "Send an EOF to the current buffer's process."
  (interactive)
  (scomint-send-input t t)
  (process-send-eof))

(defun scomint-send-input (&optional no-newline artificial)
  "Send input to process.
After the process output mark, sends all text from the process mark to
point as input to the process.  

This command also sends and inserts a final newline, unless
NO-NEWLINE is non-nil."
  (interactive)
  ;; Note that the input string does not include its terminal newline.
  (let ((proc (get-buffer-process (current-buffer))))
    (if (not proc) (error "Current buffer has no process")
      (widen)
      (let* ((pmark (process-mark proc))
             (input (if (>= (point) (marker-position pmark))
			(buffer-substring pmark (point)))))
	
        (unless no-newline
          (insert ?\n))

        (let ((beg (marker-position pmark))
              (end (if no-newline (point) (1- (point))))
              (inhibit-modification-hooks t))
          (when (> end beg)
            (add-text-properties beg end
                                 '(front-sticky t
                                   font-lock-face scomint-highlight-input))

          (unless no-newline
            ;; Cover the terminating newline
            (add-text-properties end (1+ end)
                                 '(rear-nonsticky t
                                   field boundary
                                   inhibit-line-move-field-capture t))))

        ;; Update the markers before we send the input
        ;; in case we get output amidst sending the input.
        (set-marker scomint-last-input-start pmark)
        (set-marker scomint-last-input-end (point))
        (set-marker (process-mark proc) (point))
	(scomint-send-string 
	 proc 
	 (concat input (unless no-newline "\n"))))))))


;; TODO: run this on a timer rather than on every I/O
(defun scomint-truncate-buffer (&optional string)
  "Truncate the buffer to `scomint-buffer-maximum-size'."
  (interactive)
  (if scomint-buffer-maximum-size
      (save-excursion
	(save-restriction
	  (widen)
	  (if (> (point-max) scomint-buffer-maximum-size)
	      (let ((inhibit-read-only t))
		(delete-region (point-min)
			       (- (point-max) 
				  scomint-buffer-maximum-size))))))))

(defun scomint-strip-ctrl-m (&optional string)
  "Strip trailing `^M' characters from the current output group."
  (interactive)
  (let ((pmark (process-mark (get-buffer-process (current-buffer)))))
    (save-excursion
      (condition-case nil
	  (goto-char
	   (if (interactive-p) scomint-last-input-end scomint-last-output-start))
	(error nil))
      (while (re-search-forward "\r+$" pmark t)
	(replace-match "" t t)))))

;; The purpose of using this filter for comint processes
;; is to keep comint-last-input-end from moving forward
;; when output is inserted.
(defun scomint-output-filter (process string)
  (let ((oprocbuf (process-buffer process)))
    ;; First check for killed buffer or no input.
    (when (and string oprocbuf (buffer-name oprocbuf))
      (with-current-buffer oprocbuf
	;; Insert STRING
	(let ((inhibit-read-only t)
              ;; The point should float after any insertion we do.
	      (saved-point (copy-marker (point) t)))

	  ;; We temporarly remove any buffer narrowing, in case the
	  ;; process mark is outside of the restriction
	  (save-restriction
	    (widen)

	    (goto-char (process-mark process))
	    (set-marker scomint-last-output-start (point))

	    ;; insert-before-markers is a bad thing. XXX
	    ;; Luckily we don't have to use it any more, we use
	    ;; window-point-insertion-type instead.
	    (insert string)

	    ;; Advance process-mark
	    (set-marker (process-mark process) (point))

	    ;; Run these hooks with point where the user had it.
	    (goto-char saved-point)
	    (run-hook-with-args 'scomint-output-filter-functions string)
	    ;; (scomint-truncate-buffer)

	    (set-marker saved-point (point))

	    (goto-char (process-mark process)) ; in case a filter moved it

	    (let ((inhibit-read-only t)
		  (inhibit-modification-hooks t))
	      (add-text-properties scomint-last-output-start (point)
				   '(front-sticky
				     (field inhibit-line-move-field-capture)
				     rear-nonsticky t
				     field output
				     inhibit-line-move-field-capture t)))

	    ;; Highlight the prompt, where we define `prompt' to mean
	    ;; the most recent output that doesn't end with a newline.
;;	    (let ((prompt-start (save-excursion (forward-line 0) (point)))
;;		  (inhibit-read-only t)
;;		  (inhibit-modification-hooks t))
;; 	      (when comint-prompt-read-only
;; 		(or (= (point-min) prompt-start)
;; 		    (get-text-property (1- prompt-start) 'read-only)
;; 		    (put-text-property
;; 		     (1- prompt-start) prompt-start 'read-only 'fence))
;; 		(add-text-properties
;; 		 prompt-start (point)
;; 		 '(read-only t rear-nonsticky t front-sticky (read-only))))
;; 	      (unless (and (bolp) (null comint-last-prompt-overlay))
;; 		;; Need to create or move the prompt overlay (in the case
;; 		;; where there is no prompt ((bolp) == t), we still do
;; 		;; this if there's already an existing overlay).
;; 		(if comint-last-prompt-overlay
;; 		    ;; Just move an existing overlay
;; 		    (move-overlay comint-last-prompt-overlay
;; 				  prompt-start (point))
;; 		  ;; Need to create the overlay
;; 		  (setq comint-last-prompt-overlay
;; 			(make-overlay prompt-start (point)))
;; 		  (overlay-put comint-last-prompt-overlay
;; 			       'font-lock-face 'scomint-highlight-prompt))))

	    (goto-char saved-point)))))))



(provide 'scomint)

;;; scomint.el ends here
