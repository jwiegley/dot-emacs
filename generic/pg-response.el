;; pg-response.el  Proof General response buffer mode.
;;
;; Copyright (C) 1994-2002 LFCS Edinburgh. 
;; Authors:   David Aspinall, Healfdene Goguen, 
;;		Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Response buffer mode
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-and-compile
(define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    ;; Doesn't seem to supress TAB, RET
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map 
		       proof-universal-keys)))

(eval-and-compile
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  (define-key proof-response-mode-map [q] 'bury-buffer)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)
  (easy-menu-add proof-assistant-menu proof-response-mode-map)
  (proof-toolbar-setup)
  (setq proof-shell-next-error nil)	; all error msgs lost!
  (erase-buffer)))

(easy-menu-define proof-response-mode-menu
		  proof-response-mode-map
		  "Menu for Proof General response buffer."
		  (cons proof-general-name 
			(append
			 proof-toolbar-scripting-menu
			 proof-shared-menu
			 proof-config-menu
			 proof-bug-report-menu)))


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
	 ;; (set-specifier minibuffer (minibuffer-window) (current-buffer))
	 (set-specifier has-modeline-p nil (current-buffer))
	 (set-specifier menubar-visible-p nil (current-buffer))
	 ;; gutter controls buffer tab visibility in XE 21.4
	 (and (boundp 'default-gutter-visible-p)
	      (set-specifier default-gutter-visible-p nil (current-buffer)))))
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

;;
;; Flag and function to keep response buffer tidy.
;;
;;
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
	      (setq proof-shell-next-error nil)	; all error msgs lost!
	      (erase-buffer))))
      (setq pg-response-erase-flag erase-next-time)
      doit)))

(defun pg-response-display (str)
  "Show STR as a response in the response buffer."
  (unless pg-use-specials-for-fontify
    (setq str (pg-goals-strip-subterm-markup str)))
  (proof-shell-maybe-erase-response t nil)
  (pg-response-display-with-face str)
  (proof-display-and-keep-buffer proof-response-buffer))
  
;; FIXME: this function should be combined with
;; proof-shell-maybe-erase-response-buffer. 
(defun pg-response-display-with-face (str &optional face)
  "Display STR with FACE in response buffer."
  ;; 3.4: no longer return fontified STR, it wasn't used.
  (if (string-equal str "\n")	
      str				; quick exit, no display.
  (let (start end)
    (with-current-buffer proof-response-buffer
      ;; da: I've moved newline before the string itself, to match
      ;; the other cases when messages are inserted and to cope
      ;; with warnings after delayed output (non newline terminated).
      ; (ugit (format "End is %i" (point-max)))
      (goto-char (point-max))
      (newline)				
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
      ;; 3.4: remove this for efficiency.
      ;; (buffer-substring start (point-max))
      ))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tracing buffers
;;

;; An analogue of pg-response-display-with-face 
(defun proof-trace-buffer-display (str)
  "Display STR in the trace buffer."
  (let (start end)
    (with-current-buffer proof-trace-buffer
      (goto-char (point-max))
      (newline)				
      (setq start (point))
      (insert str)
      (unless (bolp) (newline))
      (proof-fontify-region start (point)))))




(provide 'pg-response)
;; pg-response.el ends here.
