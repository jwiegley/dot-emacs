;; pbp.el Major mode for proof by pointing
;; Subpackage of proof
;; Copyright (C) 1996 LFCS Edinburgh & INRIA Sophia Antipolis
;; Author: Yves Bertot < Yves.Bertot@sophia.inria.fr>
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Time-stamp: <26 Nov 96 tms /home/tms/elisp/pbp.el>
;; Reference: Yves Bertot and Laurent Théry
;;            A Generic Approach to Building User Interfaces for
;;            Theorem Provers
;;            J. Symbolic Computation (1996)
;;            Accepted for Publication

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

(require 'proof)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Variables used by pbp, all auto-buffer-local                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal pbp-annotation-open "%"
  "Opening parenthesis for annotations.")

(deflocal pbp-annotation-close "@"
  "Closing parenthesis for annotations.")

(deflocal pbp-annotation-field "&"
  "A character marking the beginning of a new fiels e.g., an
  assumption or a goal.") 

(deflocal pbp-annotation-separator "|"
  "A character separting text form annotations.")

(deflocal pbp-wakeup-character "\t"
  "A character terminating the prompt in annotation mode")

(deflocal pbp-assumption-regexp nil
  "A regular expression matching the name of assumptions.")

(deflocal pbp-goal-regexp nil
  "A regular expressin matching the identifier of a goal.")

(deflocal pbp-start-goals-string "-- Start of Goals --"
  "String indicating the start of the proof state.")

(deflocal pbp-end-goals-string "-- End of Goals --"
  "String indicating the end of the proof state.")

(deflocal pbp-goal-command "Pbp %s"
  "Command informing the prover that `pbp-buttion-action' has been
  requested on a goal.")

(deflocal pbp-hyp-command "PbpHyp %s"
  "Command informing the prover that `pbp-buttion-action' has been
  requested on an assumption.")

(deflocal pbp-result-start "-- Pbp result --"
  "String indicating the start of an output from the prover following
  a `pbp-goal-command' or a `pbp-hyp-command'.")

(deflocal pbp-result-end "-- End Pbp result --"
  "String indicating the end of an output from the prover following a
  `pbp-goal-command' or a `pbp-hyp-command'.") 

(deflocal pbp-script-buffer nil
  "The buffer in which commands corresponding to proof-by-pointing
  actions will be recorded. The proof process is responsible for
  updating this variable")

(deflocal pbp-goals-buffer-name nil
  "The name of the buffer in which goals are displayed in pbp mode")

(deflocal pbp-goals-buffer nil
  "The buffer in which goals are displayed in pbp mode")

(deflocal pbp-regexp-noise-goals-buffer nil
  "Unwanted information output from the proof process within
  `pbp-start-goals-string' and `pbp-end-goals-string'.")

(deflocal pbp-keymap (make-keymap 'Pbp-keymap) 
  "Keymap for pbp mode")

(defun pbp-analyse-structure ()
  (map-extents
      (lambda (ext maparg)
          (when (extent-property ext 'pbp) (delete-extent ext))))
  (beginning-of-buffer)
  (setq pbp-location-stack ())
  (while (re-search-forward pbp-regexp-noise-goals-buffer () t)
    (beginning-of-line)
    (kill-line))
  (beginning-of-buffer)
  (while (re-search-forward
	  (concat "["
		  pbp-annotation-open pbp-annotation-close
		  pbp-annotation-field "]") () t)
    (cond ((string= (char-to-string (preceding-char)) pbp-annotation-open)
	   (progn (delete-backward-char 1)(pbp-location-push (point))))
          ((string= (char-to-string (preceding-char)) pbp-annotation-field)
           (let ((prev-ampersand (pbp-location-pop)))
             (if prev-ampersand (pbp-make-top-extent prev-ampersand))
	     (delete-backward-char 1)
	     (pbp-location-push (point))))
	  (t (pbp-make-extent))))
  (end-of-buffer)
  (pbp-make-top-extent (pbp-location-pop)))

(defun pbp-make-top-extent (previous-ampersand)
  (save-excursion
    (beginning-of-line) (backward-char) 
    (let ((extent (make-extent previous-ampersand (point))))
      (set-extent-property extent 'mouse-face 'highlight)
      (set-extent-property extent 'pbp-top-element 
			   (pbp-compute-extent-name extent))
      (set-extent-property extent 'keymap pbp-keymap))))

(defun pbp-make-extent ()
   (let ((extent (make-extent (or (pbp-location-pop) 1) (point))))
	 (set-extent-property extent 'mouse-face 'highlight)
	 (set-extent-property extent 'keymap pbp-keymap)
         (let ((pos1 (extent-start-position extent))
               (annot()))
               (goto-char pos1)
               (if (search-forward pbp-annotation-separator () t)
                   (progn
                        (setq annot 
                              (buffer-substring pos1 (- (point) 1)))
                        (delete-region pos1 (point))
                        (set-extent-property extent 'pbp annot)))
                        (goto-char (extent-end-position extent))
                        (delete-backward-char 1))))

(defun pbp-compute-extent-name (extent)
  (save-excursion
    (goto-char (extent-start-position extent))
    (cond ((looking-at pbp-goal-regexp)
	   (cons 'goal (match-string 1)))
	  ((looking-at pbp-assumption-regexp)
	   (cons 'hyp (match-string 1)))
	  (t
	   (bug "top element does not start with a name")))))

; Receiving the data from Lego is performed that a filter function
; added among the comint-output-filter-functions of the shell-mode.

(deflocal pbp-last-mark nil "last mark")
(deflocal pbp-sanitise t "sanitise output?")

(defun pbp-sanitise-region (start end)
  (if pbp-sanitise 
      (progn
	(goto-char start)
	(if (search-forward pbp-start-goals-string end t) 
	    (backward-delete-char (+ (length pbp-start-goals-string) 1)))
	(if (search-forward pbp-end-goals-string end t) 
	    (backward-delete-char (+ (length pbp-end-goals-string) 1)))
	(goto-char start)
	(while (search-forward pbp-annotation-close end t)
	  (backward-delete-char 1))
	(goto-char start)
        (while (search-forward pbp-wakeup-character nil t)
          (replace-match " " nil t))
	(goto-char start)
	(while (search-forward pbp-annotation-field end t)
	  (backward-delete-char 1))
        (lego-zap-commas-region start end (- end start))
	(goto-char start)
	(while (setq start (search-forward pbp-annotation-open end t)) 
	  (search-forward pbp-annotation-separator end t)
	  (delete-region (- start 1) (point))))))

(defun pbp-display-error (start end)
  (set-buffer pbp-goals-buffer)
  (goto-char (point-max))
  (if (re-search-backward proof-error-regexp nil t) 
      (delete-region (- (point) 2) (point-max)))
  (newline 2)
  (insert-buffer-substring (proof-shell-buffer) start end))

(defun pbp-send-and-remember (string)
  (save-excursion
    (proof-simple-send string)
    (if (and (boundp 'pbp-script-buffer) pbp-script-buffer)
	(progn (set-buffer pbp-script-buffer)
	       (end-of-buffer)
	       (insert-string string)))))

(defun pbp-process-region (pbp-start pbp-end)
  (let (start end)
   (save-excursion 
    (goto-char pbp-start)
    (cond 
     ((re-search-forward proof-shell-abort-goal-regexp pbp-end t)
      (erase-buffer pbp-goals-buffer))
     
     ((re-search-forward proof-shell-proof-completed-regexp pbp-end t)
      (erase-buffer pbp-goals-buffer)
      (insert-string (concat "\n" (match-string 0))
		     pbp-goals-buffer))
     
     ((re-search-forward proof-error-regexp pbp-end t)
      (setq start (match-beginning 0))
      (pbp-sanitise-region pbp-start pbp-end)
      (pbp-display-error start pbp-end))

     ((search-forward pbp-start-goals-string pbp-end t)
      (goto-char pbp-end)
      (setq start
	    (+ (length pbp-start-goals-string)
	       (search-backward pbp-start-goals-string pbp-start t)))
      (setq end (- (search-forward pbp-end-goals-string pbp-end t)
		   (length pbp-end-goals-string)))
      (set-buffer pbp-goals-buffer)
      (erase-buffer)
      (insert-buffer-substring (proof-shell-buffer) start end)
      (pbp-analyse-structure))

     ((search-forward pbp-result-start () t)
      (end-of-line)
      (setq start (point))
      (search-forward pbp-result-end () t)
      (beginning-of-line)
      (setq end (- (point) 1))
      (pbp-send-and-remember (buffer-substring start end)))))))

(defun pbp-filter (string) 
  (if (string-match pbp-wakeup-character string)
      (save-excursion
	(set-buffer (proof-shell-buffer))
	(let (old-mark)
	  (while (progn (goto-char pbp-last-mark)
			(re-search-forward proof-shell-prompt-pattern () t))
	    (setq old-mark pbp-last-mark)
	    (setq pbp-last-mark (point-marker))
	    (goto-char (match-beginning 0))
	    (pbp-process-region old-mark (point-marker))
	    (pbp-sanitise-region old-mark pbp-last-mark))))))

; Call after the shell is started

(defun pbp-goals-init ()
  (setq pbp-goals-buffer (get-buffer-create pbp-goals-buffer-name ))
  (erase-buffer pbp-goals-buffer)
  (add-hook 'comint-output-filter-functions 'pbp-filter t)
  (pbp-sanitise-region (point-min) (point-max))
  (setq pbp-last-mark (point-max-marker (proof-shell-buffer)))
  (add-hook 'proof-shell-exit-hook
	    (lambda ()
	      (remove-hook 'comint-output-filter-functions 'pbp-filter))))

; Now, using the extents in a mouse behavior is quite simple:
; from the mouse position, find the relevant extent, then get its annotation
; and produce a piece of text that will be inserted in the right buffer.
; Attaching this behavior to the mouse is simply done by attaching a keymap
; to all the extents.

(define-key pbp-keymap 'button2 'pbp-button-action)

(defun pbp-button-action (event)
   (interactive "e")
   (mouse-set-point event)
   (pbp-construct-command))


(defun pbp-construct-command ()
   (let ((ext (extent-at (point) () 'pbp))
         (top-ext (extent-at (point) () 'pbp-top-element)))

      (cond ((and (extentp top-ext) (extentp ext))
	     (let* ((top-info (extent-property top-ext 'pbp-top-element))
		   (path
		    (concat (cdr top-info) " " (extent-property ext 'pbp))))
	       (proof-command
		(if (eq 'hyp (car top-info))
		    (format pbp-hyp-command path)
		  (format pbp-goal-command  path))

		; t would send the command silently
                ; however, this doesn't work as the output by LEGO
                ; apparently gets inserted before pbp-last-mark.
		; I don't understand why.
		nil)))
	    ((extentp top-ext)
	     (let ((top-info (extent-property top-ext 'pbp-top-element)))
	       (let ((value (if (eq 'hyp (car top-info))
		    (format pbp-hyp-command (cdr top-info))
		  (format proof-shell-change-goal (cdr top-info)))))
               (pbp-send-and-remember value)))))))




; a little package to manage a stack of locations

(defun pbp-location-push (value)
   (setq pbp-location-stack (cons value pbp-location-stack)))

(defun pbp-location-pop ()
   (if pbp-location-stack
       (let ((result (car pbp-location-stack)))
	 (setq pbp-location-stack (cdr pbp-location-stack))
	 result)))

(deflocal pbp-location-stack () "location stack" )

(provide 'pbp)




