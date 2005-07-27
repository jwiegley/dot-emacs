
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
;;HERE changed t nil to t FORCE
  (proof-shell-maybe-erase-response t nil)
  ;;(unless (or (string-equal str "") (string-equal str "\n"))
    ;; don't display an empty buffer [ NB: above test repeated below,
    ;; but response-display reused elsewhere ]


  (pg-response-display-with-face str)
  ;; NB: this displays an empty buffer sometimes when it's not
  ;; so useful.  It _is_ useful if the user has requested to
  ;; see the proof state and there is none 
  ;; (Isabelle/Isar displays nothing: might be better if it did).
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
	(proof-fontify-region start (point))
	;; This is one reason why we don't keep the buffer in font-lock
	;; minor mode: it destroys this hacky property as soon as it's
	;; made!  (Using the minor mode is much more convenient, tho')
	(if (and face proof-output-fontify-enable)
	    (font-lock-append-text-property 
	     start (point-max) 'face face))
	;; This returns the decorated string, but it doesn't appear 
	;; decorated in the minibuffer, unfortunately.
	;; [ FIXME: users have asked for that to be fixed ]
	;; 3.4: remove this for efficiency.
	;; (buffer-substring start (point-max))
	(set-buffer-modified-p nil))))))


(defun pg-response-clear-displays ()
  "Clear Proof General response  buffers.
You can use this command to clear the output from these buffers when
it becomes overly long.  Particularly useful when `proof-tidy-response'
is set to nil, so responses are not cleared automatically."
  (interactive)
  (proof-map-buffers (list proof-response-buffer proof-trace-buffer proof-resolve-buffer)
    (erase-buffer)
    (set-buffer-modified-p nil)))






;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Displaying in the resolution buffer
;;

;; Flag and function to keep resolve buffer tidy.
(defvar pg-resolve-erase-flag nil
  "Indicates that the resolve buffer should be cleared before next message.")

(defun proof-shell-maybe-erase-resolve
  (&optional erase-next-time clean-windows force)
  "Erase the resolve buffer according to pg-resolve-erase-flag.
ERASE-NEXT-TIME is the new value for the flag.
If CLEAN-WINDOWS is set, use proof-clean-buffer to do the erasing.
If FORCE, override pg-resolve-erase-flag.

If the user option proof-tidy-resolve is nil, then
the buffer is only cleared when FORCE is set.

No effect if there is no resolve buffer currently.
Returns non-nil if resolve buffer was cleared."
  (when (buffer-live-p proof-resolve-buffer)
    (let ((doit (or (and
		     proof-tidy-resolve
		     (not (eq pg-resolve-erase-flag 'invisible))
		     pg-resolve-erase-flag) 
		    force)))
      (if doit
	  (if clean-windows
	      (proof-clean-buffer proof-resolve-buffer)
	  ;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
	  ;; (erase-buffer proof-resolve-buffer)
	    (with-current-buffer proof-resolve-buffer
	      (setq pg-resolve-next-error nil)	; all error msgs lost!
	      (erase-buffer)
	      (set-buffer-modified-p nil))))
      (setq pg-resolve-erase-flag erase-next-time)
      doit)))

(defun pg-resolve-display (str)
  "Show STR as a resolve in the resolve buffer."
  (unless pg-use-specials-for-fontify
    (setq str (pg-assoc-strip-subterm-markup str)))
  (proof-shell-maybe-erase-resolve t nil)
  ;;(unless (or (string-equal str "") (string-equal str "\n"))
    ;; don't display an empty buffer [ NB: above test repeated below,
    ;; but resolve-display reused elsewhere ]


  (pg-resolve-display-with-face str)
  ;; NB: this displays an empty buffer sometimes when it's not
  ;; so useful.  It _is_ useful if the user has requested to
  ;; see the proof state and there is none 
  ;; (Isabelle/Isar displays nothing: might be better if it did).
  (proof-display-and-keep-buffer proof-resolve-buffer))
  

;; FIXME: this function should be combined with
;; proof-shell-maybe-erase-resolve-buffer. 
(defun pg-resolve-display-with-face (str &optional face)
  "Display STR with FACE in resolve buffer."
  ;; 3.4: no longer return fontified STR, it wasn't used.
  (cond
   ((string-equal str ""))
   ((string-equal str "\n"))		; quick exit, no display.
   (t
    (let (start end)
      (with-current-buffer proof-resolve-buffer
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
	(proof-fontify-region start (point))
	;; This is one reason why we don't keep the buffer in font-lock
	;; minor mode: it destroys this hacky property as soon as it's
	;; made!  (Using the minor mode is much more convenient, tho')
	(if (and face proof-output-fontify-enable)
	    (font-lock-append-text-property 
	     start (point-max) 'face face))
	;; This returns the decorated string, but it doesn't appear 
	;; decorated in the minibuffer, unfortunately.
	;; [ FIXME: users have asked for that to be fixed ]
	;; 3.4: remove this for efficiency.
	;; (buffer-substring start (point-max))
	(set-buffer-modified-p nil))))))


(defun pg-resolve-clear-displays ()
  "Clear Proof General resolve buffer.
You can use this command to clear the output from these buffers when
it becomes overly long.  Particularly useful when `proof-tidy-resolve'
is set to nil, so resolves are not cleared automatically."
  (interactive)
  (proof-map-buffers (list proof-resolve-buffer proof-trace-buffer proof-resolve-buffer)
    (erase-buffer)
    (set-buffer-modified-p nil)))






