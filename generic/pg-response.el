;; pg-response.el  Proof General response buffer mode.
;;
;; Copyright (C) 1994-2002 LFCS Edinburgh. 
;; Authors:   David Aspinall, Healfdene Goguen, 
;;		Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; This mode is used for the response buffer proper, and
;; also the trace and theorems buffer.


;; A sub-module of proof-shell; assumes proof-script loaded.
(require 'pg-assoc)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Response buffer mode
;;

(eval-and-compile
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  ;; font-lock-keywords isn't automatically buffer-local in Emacs 21.2
  (make-local-variable 'font-lock-keywords)
  (define-key proof-response-mode-map [q] 'bury-buffer)
  (define-key proof-response-mode-map [c] 'pg-response-clear-displays)
  (make-local-hook 'kill-buffer-hook)
  (add-hook 'kill-buffer-hook 'pg-save-from-death nil t)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)
  (easy-menu-add proof-assistant-menu proof-response-mode-map)
  (proof-toolbar-setup)
  (setq pg-response-next-error nil)
  (erase-buffer)
  (buffer-disable-undo)
  (set-buffer-modified-p nil)))

(easy-menu-define proof-response-mode-menu
		  proof-response-mode-map
		  "Menu for Proof General response buffer."
		  proof-aux-menu)


(defun proof-response-config-done ()
  "Complete initialisation of a response-mode derived buffer."
  (proof-font-lock-configure-defaults nil)
  (proof-x-symbol-configure))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Multiple frames for goals and response buffers
;;
;;  -- because who's going to bother do this by hand?
;;

(defvar proof-shell-special-display-regexp nil
  "Regexp for special-display-regexps for multiple frame use.
Internal variable, setting this will have no effect!")

(defun proof-multiple-frames-enable ()
  (cond
   (proof-multiple-frames-enable
    (setq special-display-regexps
	  (union special-display-regexps 
		 (list proof-shell-special-display-regexp)))
    ;; If we're on XEmacs with toolbar, turn off toolbar and
    ;; menubar for the small frames to save space.
    ;; FIXME: this could be implemented more smoothly
    ;; with property lists, and specifiers should perhaps be set
    ;; for the frame rather than the buffer.  Then could disable
    ;; minibuffer, too.
    ;; FIXME: add GNU Emacs version here.
    (if (featurep 'toolbar) 
	(proof-map-buffers
	 (list proof-response-buffer proof-goals-buffer proof-trace-buffer)
	 (set-specifier default-toolbar-visible-p nil (current-buffer))
	 ; (set-specifier minibuffer (minibuffer-window) (current-buffer))
	 ;(set-specifier has-modeline-p nil (current-buffer))
	 (remove-specifier has-modeline-p (current-buffer))
	 (remove-specifier menubar-visible-p (current-buffer))
	 ;; gutter controls buffer tab visibility in XE 21.4
	 (and (boundp 'default-gutter-visible-p)
	      (remove-specifier default-gutter-visible-p (current-buffer)))))
    ;; Try to trigger re-display of goals/response buffers,
    ;; on next interaction.  
    ;; FIXME: would be nice to do the re-display here, rather
    ;; than waiting for next re-display
    (delete-other-windows 
     (if proof-script-buffer
	 (get-buffer-window proof-script-buffer t))))
   (t
    ;; FIXME: would be nice to kill off frames automatically,
    ;; but let's leave it to the user for now.
    (setq special-display-regexps
	  (delete proof-shell-special-display-regexp 
		  special-display-regexps)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Displaying in the response buffer
;;

;; Flag and function to keep response buffer tidy.
(defvar pg-response-erase-flag nil
  "Indicates that the response buffer should be cleared before next message.")

(defun proof-shell-maybe-erase-response
  (&optional erase-next-time clean-windows force)
  "Erase the response buffer according to pg-response-erase-flag.
ERASE-NEXT-TIME is the new value for the flag.
If CLEAN-WINDOWS is set, use proof-clean-buffer to do the erasing.
If FORCE, override pg-response-erase-flag.

If the user option proof-tidy-response is nil, then
the buffer is only cleared when FORCE is set.

No effect if there is no response buffer currently.
Returns non-nil if response buffer was cleared."
  (when (buffer-live-p proof-response-buffer)
    (let ((doit (or (and
		     proof-tidy-response
		     (not (eq pg-response-erase-flag 'invisible))
		     pg-response-erase-flag) 
		    force)))
      (if doit
	  (if clean-windows
	      (proof-clean-buffer proof-response-buffer)
	  ;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
	  ;; (erase-buffer proof-response-buffer)
	    (with-current-buffer proof-response-buffer
	      (setq pg-response-next-error nil)	; all error msgs lost!
	      (erase-buffer)
	      (set-buffer-modified-p nil))))
      (setq pg-response-erase-flag erase-next-time)
      doit)))

(defun pg-response-display (str)
  "Show STR as a response in the response buffer."
  (unless pg-use-specials-for-fontify
    (setq str (pg-assoc-strip-subterm-markup str)))
  (proof-shell-maybe-erase-response t nil)
  (pg-response-display-with-face str)
  (proof-display-and-keep-buffer proof-response-buffer))
  
;; FIXME: this function should be combined with
;; proof-shell-maybe-erase-response-buffer. 
(defun pg-response-display-with-face (str &optional face)
  "Display STR with FACE in response buffer."
  ;; 3.4: no longer return fontified STR, it wasn't used.
  (cond
   ((string-equal str ""))
   ((string-equal str "\n"))		; quick exit, no display.
   (t
    (let (start end)
      (with-current-buffer proof-response-buffer
	;; da: I've moved newline before the string itself, to match
	;; the other cases when messages are inserted and to cope
	;; with warnings after delayed output (non newline terminated).
	(goto-char (point-max))
	;; insert a newline before the new message unless the
	;; buffer is empty
	(unless (eq (point-min) (point-max))
	  (newline))
	(setq start (point))
	(insert str)
	(unless (bolp) (newline))
	(setq end (proof-fontify-region start (point)))
	;; This is one reason why we don't keep the buffer in font-lock
	;; minor mode: it destroys this hacky property as soon as it's
	;; made!  (Using the minor mode is much more convenient, tho')
	(if (and face proof-output-fontify-enable)
	    (font-lock-append-text-property start end 'face face))
	;; This returns the decorated string, but it doesn't appear 
	;; decorated in the minibuffer, unfortunately.
	;; [ FIXME: users have asked for that to be fixed ]
	;; 3.4: remove this for efficiency.
	;; (buffer-substring start (point-max))
	(set-buffer-modified-p nil))))))


(defun pg-response-clear-displays ()
  "Clear Proof General response and tracing buffers.
You can use this command to clear the output from these buffers when
it becomes overly long.  Particularly useful when `proof-tidy-response'
is set to nil, so responses are not cleared automatically."
  (interactive)
  (proof-map-buffers (list proof-response-buffer proof-trace-buffer)
    (erase-buffer)
    (set-buffer-modified-p nil)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Next error function.
;;

(defvar pg-response-next-error nil
  "Error counter in response buffer to count for next error message.")

;;;###autoload
(defun proof-next-error (&optional argp)
  "Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.
Just C-u as a prefix means reparse the error message buffer
and start at the first error."
  (interactive "P")
  (if (and ;; At least one setting must be configured
       pg-next-error-regexp
       ;; Response buffer must be live
       (or
	(buffer-live-p proof-response-buffer)
	(error "proof-next-error: no response buffer to parse!")))
      (let ((wanted-error    (or (and (not (consp argp))
				      (+ (prefix-numeric-value argp)
					 (or pg-response-next-error 0)))
				 (and (consp argp) 1)
				 (or pg-response-next-error 1)))
	    line column file errpos)
	(set-buffer proof-response-buffer)
	(goto-char (point-min))
	(if (re-search-forward pg-next-error-regexp 
			       nil t wanted-error)
	    (progn
	      (setq errpos (save-excursion
			     (goto-char (match-beginning 0))
			     (beginning-of-line)
			     (point)))
	      (setq line (match-string 2)) ; may be unset
	      (if line (setq line (string-to-int line)))
	      (setq column (match-string 3)) ; may be unset
	      (if column (setq column (string-to-int column)))
	      (setq pg-response-next-error wanted-error)
	      (if (and
		   pg-next-error-filename-regexp
		     ;; Look for the most recently mentioned filename
		     (re-search-backward
		      pg-next-error-filename-regexp nil t))
		    (setq file 
			  (if (file-exists-p (match-string 2))
			      (match-string 2)
			    ;; May need post-processing to extract filename
			    (if pg-next-error-extract-filename
				(format 
				 pg-next-error-extract-filename 
				 (match-string 2))))))
		;; Now find the other buffer we need to display
		(let*
		    ((errbuf	
		      (if file
			  (find-file-noselect file)
			(or proof-script-buffer 
			    ;; We could make more guesses here,
			    ;; e.g. last script buffer active 
			    ;; (keep a record of it?)
			    (error 
			     "proof-next-error: can't guess file for error message"))))
		     (pop-up-windows t)
		     (rebufwindow
		      (or (get-buffer-window proof-response-buffer 'visible)
			  ;; Pop up a window.
			  (display-buffer proof-response-buffer))))
		  ;; Make sure the response buffer stays where it is,
		  ;; and make sure source buffer is visible
		  (select-window rebufwindow)
		  (pop-to-buffer errbuf)
		  ;; Display the error message in the response buffer
		  (set-window-point rebufwindow errpos)
		  (set-window-start rebufwindow errpos)
		  ;; Find the error location in the error buffer
		  (set-buffer errbuf)
		  ;; FIXME: no handling of selective display here
		  (goto-line line)
		  (if (and column (> column 1))
		      (move-to-column (1- column)))))
	    (setq pg-response-next-error nil)
	    (error "proof-next-error: couldn't find a next error.")))))

   



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tracing buffers
;;

;; An analogue of pg-response-display-with-face 
(defun proof-trace-buffer-display (str)
  "Display STR in the trace buffer."
  (let (start)
    (with-current-buffer proof-trace-buffer
      (goto-char (point-max))
      (newline)				
      (setq start (point))
      (insert str)
      (unless (bolp) (newline))
      (proof-fontify-region start (point))
      (set-buffer-modified-p nil))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Theorems buffer
;;
;; New in PG 3.5.  
;;
;; Revives an old idea from Isamode: a buffer displaying a bunch
;; of theorem names.
;;


(defun pg-thms-buffer-clear ()
  "Clear the theorems buffer."
  (with-current-buffer proof-thms-buffer
      (goto-char (point-max))
      (newline)				
      (setq start (point))
      (insert str)
      (unless (bolp) (newline))
      (proof-fontify-region start (point))
      (set-buffer-modified-p nil)))








(provide 'pg-response)
;; pg-response.el ends here.
