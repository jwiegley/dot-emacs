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
; This function is a two state function.  It may happen that the
; last string that was processed was in the middle of a goal listing,
; in this case one must go on reading the rest of the goals.

(defun lego-pbp-filter (string)
  (save-excursion
    (set-buffer *lego-tmp-goals*)
    (goto-char (point-max))
    (insert string)
    (while (progn (goto-char (point-min))
		  (re-search-forward proof-shell-prompt-pattern () t))
      (narrow-to-region (point-min) (point))
      (lego-pbp-process-region)
      (delete-region (point-min) (point-max))
      (widen))))

(defun lego-pbp-process-region ()
  (save-excursion 
    (goto-char (point-min))
    (cond ((search-forward "KillRef: ok, not in proof state" () t)
	   (erase-buffer *lego-goals*))
	  ((search-forward "*** QED ***" () t)
	   (erase-buffer *lego-goals*)
	   (insert-string "\n   *** QED ***" *lego-goals*))
	  ((search-forward "-- Start of Goals --" () t)
	   (delete-region (point-min) (point))
	   (search-forward "-- End of Goals --" () t)
	   (backward-char 18)
	   (delete-region (point)(point-max))
	   (set-buffer *lego-goals*)
	   (erase-buffer)
	   (insert-buffer-substring *lego-tmp-goals*)
	   (lego-pbp-analyse-structure))
	  ((search-forward "-- Pbp result --" () t)
	   (end-of-line)
	   (delete-region 1 (point))
	   (search-forward "-- End Pbp result --" () t)
	   (beginning-of-line)
	   (delete-region (- (point) 1) (point-max))
	   (proof-simple-send (buffer-substring 1 (point-max)))
	   (if *script-buffer*
	       (progn (set-buffer *script-buffer*)
		      (end-of-buffer)
		      (insert-buffer-substring *lego-tmp-goals*)))))))


(defun lego-goals-init ()
  (setq *lego-tmp-goals* (get-buffer-create "*lego-tmp-goals*"))
  (setq *lego-goals* (get-buffer-create "*lego goals*"))
  (erase-buffer *lego-goals*)
  (erase-buffer *lego-tmp-goals*)
  (bury-buffer *lego-tmp-goals*))

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




