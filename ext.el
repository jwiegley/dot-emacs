; The text structure is supposed to be given by annotations of the
; form %annotation text|annotated text@,  The % and @ signs act as
; opening and closing parentheses, so that the annotated text may itself
; contain extra annotations.  Analysing this structure yields the
; uncorrupted text (only "annotated text"), but the annotation are recorded
; into Emacs Extents that span over the text.

;To construct these extents, one scans the whole text for the characters
; % and @.  When finding a %, its location is simply kept on a stack
; *location-stack*.  When finding a @, one looks in the stack to get
; the position of the last % and creates an extent with these two positions.
; The annotation is then removed and stored in the extent's properties
; and the last bits are cleared.

(defvar *script-buffer*)
(defvar lego-goals-buffer)
(defvar lego-error-buffer)

(defun lego-pbp-analyse-structure ()
  (map-extents
      (lambda (ext maparg)
          (when (extent-property ext 'lego-pbp) (delete-extent ext))))
  (beginning-of-buffer)
  (setq *location-stack* ())
  (setq *extent-count* 0)
  (while (search-forward "Discharge.. " () t)
    (beginning-of-line)
    (kill-line))
  (beginning-of-buffer)
  (while (re-search-forward "[%@&]" () t)
    (cond ((string= (char-to-string (preceding-char)) "%")
	   (progn (delete-backward-char 1)(location-push (point))))
          ((string= (char-to-string (preceding-char)) "&")
           (let ((prev-ampersand (location-pop)))
             (if prev-ampersand (lego-pbp-make-top-extent prev-ampersand))
	     (delete-backward-char 1)
	     (location-push (point))))
	  (t (lego-pbp-make-extent))))
  (end-of-buffer)
  (lego-pbp-make-top-extent (location-pop)))


(defun lego-pbp-make-top-extent (previous-ampersand)
  (save-excursion
    (beginning-of-line) (backward-char) 
    (let ((extent (make-extent previous-ampersand (point))))
      (set-extent-property extent 'mouse-face 'highlight)
      (set-extent-property extent 'lego-top-element 
			   (lego-pbp-compute-extent-name extent))
      (set-extent-property extent 'keymap *lego-pbp-keymap*))))

(defun lego-pbp-make-extent ()
   (let ((extent (make-extent (or (location-pop) 1) (point))))
	 (set-extent-property extent 'mouse-face 'highlight)
	 (set-extent-property extent 'keymap *lego-pbp-keymap*)
         (let ((pos1 (extent-start-position extent))
               (annot()))
               (goto-char pos1)
               (if (search-forward "|" () t)
                   (progn
                        (setq annot 
                              (buffer-substring pos1 (- (point) 1)))
                        (delete-region pos1 (point))
                        (set-extent-property extent 'lego-pbp annot)))
                        (goto-char (extent-end-position extent))
                        (delete-backward-char 1))))

(defun lego-pbp-compute-extent-name (extent)
  (save-excursion
    (goto-char (extent-start-position extent))
    ; the search for an hypothesis name is ambiguous: any binder in
    ; logical formula will be recognized.  This is why we have to
    ; check first that we are not in a goal, and then look for the
    ; first identifier.
    (if (re-search-forward " *\\?\\([0-9][0-9]*\\) *:" 
			   (extent-end-position extent) t)
        (cons 'goal (match-string 1))
        (if (re-search-forward "\\([a-zA-Z][a-zA-Z_0-9]*\\) *:" 
			       (extent-end-position extent) t)
	    (cons 'hyp (match-string 1))
	  (bug "top element does not start with a name")))))

; Receiving the data from Lego is performed that a filter function
; added among the comint-output-filter-functions of the shell-mode.

(defvar lego-pbp-last-mark)
(defvar lego-pbp-next-mark)
(defvar lego-pbp-sanitise t)

(defun lego-pbp-sanitise-region (start end)
  (if lego-pbp-sanitise 
      (progn
	(goto-char start)
	(if (search-forward "-- Start of Goals --" end t) 
	    (backward-delete-char 21))
	(if (search-forward "-- End of Goals --" end t) 
	    (backward-delete-char 19))
	(goto-char start)
	(while (search-forward "@" end t) (backward-delete-char 1))
	(goto-char start)
	(while (search-forward "&" end t) (backward-delete-char 1))
	(goto-char start)
	(while (setq start (search-forward "%" end t)) 
	  (search-forward "|" end t)
	  (delete-region (- start 1) (point))))))

(defun lego-pbp-display-error (start end)
  (set-buffer lego-goals-buffer)
  (goto-char (point-max))
  (if (or (search-backward "Error:" nil t) 
	  (search-backward "Lego parser;" nil t))
      (delete-region (- (point) 2) (point-max)))
  (newline 2)
  (insert-buffer-substring (proof-shell-buffer) start end))

(defun lego-pbp-process-region (pbp-start pbp-end)
  (let (start end)
   (save-excursion 
    (goto-char pbp-start)
    (cond 
     ((search-forward "KillRef: ok, not in proof state" pbp-end t)
      (erase-buffer lego-goals-buffer))
     
     ((search-forward "*** QED ***" pbp-end t)
      (erase-buffer lego-goals-buffer)
      (insert-string "\n   *** QED ***" lego-goals-buffer))
     
     ((or (search-forward "Error:" pbp-end t)
	  (search-forward "Lego parser;" pbp-end t))
      (setq start (match-beginning 0))
      (lego-pbp-sanitise-region pbp-start pbp-end)
      (lego-pbp-display-error start pbp-end))

     ((search-forward "-- Start of Goals --" pbp-end t)
      (goto-char pbp-end)
      (setq start (+ 20 (search-backward "-- Start of Goals --" pbp-start t)))
      (setq end (- (search-forward "-- End of Goals --" pbp-end t) 18))
      (set-buffer lego-goals-buffer)
      (erase-buffer)
      (insert-buffer-substring (proof-shell-buffer) start end)
      (lego-pbp-analyse-structure))

     ((search-forward "-- Pbp result --" () t)
      (end-of-line)
      (setq start (point))
      (search-forward "-- End Pbp result --" () t)
      (beginning-of-line)
      (setq end (- (point) 1))
      (proof-simple-send (buffer-substring start end))
      (if (boundp '*script-buffer*)
	  (progn (set-buffer *script-buffer*)
		 (end-of-buffer)
		 (insert-buffer-substring (proof-shell-buffer) start end))))
     ))))


;; NEED TO SET LAST_MARK ***BEFORE*** calling process-region 

(defun lego-pbp-filter (string)
  (save-excursion
    (set-buffer (proof-shell-buffer))

    (if (and (boundp 'lego-pbp-last-mark) 
	     (equal (marker-buffer lego-pbp-last-mark) (proof-shell-buffer)))
	() 
       (goto-char (point-max))
       (setq lego-pbp-last-mark (point-marker)))
    (let (old-mark)
      (while (progn (goto-char lego-pbp-last-mark)
		    (re-search-forward proof-shell-prompt-pattern () t))
	(setq old-mark lego-pbp-last-mark)
	(setq lego-pbp-last-mark (point-marker))
	(goto-char (match-beginning 0))
	(lego-pbp-process-region old-mark (point-marker))
	(lego-pbp-sanitise-region old-mark lego-pbp-last-mark)))))

(defun lego-goals-init ()
  (setq lego-goals-buffer (get-buffer-create "*lego goals*"))
  (erase-buffer lego-goals-buffer))


; Now, using the extents in a mouse behavior is quite simple:
; from the mouse position, find the relevant extent, then get its annotation
; and produce a piece of text that will be inserted in the right buffer.
; Attaching this behavior to the mouse is simply done by attaching a keymap
; to all the extents.

(defvar *lego-pbp-keymap*)

(setq *lego-pbp-keymap*
  (make-keymap 'Lego-PBP-keymap))

(define-key *lego-pbp-keymap* 'button1
   'pbp-button-action)

(defun pbp-button-action (event)
   (interactive "e")
   (mouse-set-point event)
   (pbp-construct-command))


(defun pbp-construct-command ()
   (let ((ext (extent-at (point) () 'lego-pbp))
         (top-ext (extent-at (point) () 'lego-top-element)))

      (cond ((and (extentp top-ext) (extentp ext))
	     (let ((path (extent-property ext 'lego-pbp))
		   (top-info (extent-property top-ext 'lego-top-element)))
	       (proof-simple-send 
		(if (eq 'hyp (car top-info))
		    (concat "PbpHyp " (cdr top-info) " " path ";")
		  (concat "Pbp " (cdr top-info) " " path ";")))))
	    ((extentp top-ext)
	     (let ((top-info (extent-property top-ext 'lego-top-element)))
	       (let ((value (if (eq 'hyp (car top-info))
		    (concat "Refine " (cdr top-info) ";")
		  (concat "Next +" (cdr top-info) ";"))))
	       (proof-simple-send
		    value)
		(if *script-buffer*
		    (progn (set-buffer *script-buffer*)
			   (end-of-buffer)
			   (insert-string value)))))))))




; a little package to manage a stack of locations

(defun location-push (value)
   (setq *location-stack* (cons value *location-stack*)))

(defun location-pop ()
   (if *location-stack*
       (let ((result (car *location-stack*)))
	 (setq *location-stack* (cdr *location-stack*))
	 result)))

(defvar *location-stack* ())

(provide 'ext)




