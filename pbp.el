;; pbp.el Major mode for proof by pointing
;; Subpackage of proof
;; Copyright (C) 1996 LFCS Edinburgh & INRIA Sophia Antipolis
;; Author: Yves Bertot < Yves.Bertot@sophia.inria.fr>
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Time-stamp: <13 Dec 96 tms /home/tms/elisp/pbp.el>
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

(deflocal pbp-annotation-char ?@ "Annotation Mark")

(deflocal pbp-goal-char ?g "goal mark")
(deflocal pbp-start-char ?s "annotation start")
(deflocal pbp-end-char ?e "annotation end")
(deflocal pbp-field-char ?x "annotated field end")

(deflocal pbp-wakeup-character "\t"
  "A character terminating the prompt in annotation mode")

(deflocal pbp-assumption-regexp nil
  "A regular expression matching the name of assumptions.")

(deflocal pbp-goal-regexp nil
  "A regular expressin matching the identifier of a goal.")

(deflocal pbp-annotated-prompt-string "Lego> \t"
  "Annotated prompt pattern")

(deflocal pbp-start-goals-string "@s Start of Goals @e"
  "String indicating the start of the proof state.")

(deflocal pbp-end-goals-string "@s End of Goals @e"
  "String indicating the end of the proof state.")

(deflocal pbp-goal-command "Pbp %s;"
  "Command informing the prover that `pbp-buttion-action' has been
  requested on a goal.")

(deflocal pbp-hyp-command "PbpHyp %s;"
  "Command informing the prover that `pbp-buttion-action' has been
  requested on an assumption.")

(deflocal pbp-result-start "@s Pbp result @e"
  "String indicating the start of an output from the prover following
  a `pbp-goal-command' or a `pbp-hyp-command'.")

(deflocal pbp-result-end "@s End Pbp result @e"
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

(define-key pbp-keymap 'button2 'pbp-button-action)

(deflocal pbp-mode-is nil
  "The actual mode for Proof-by-Pointing.")

(defun pbp-make-top-extent (start end)
  (let (extent name)
    (goto-char start)
    (setq name (cond ((looking-at pbp-goal-regexp)
		      (cons 'goal (match-string 1)))
		     ((looking-at pbp-assumption-regexp)
		      (cons 'hyp (match-string 1)))))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq extent (make-extent start (point)))
    (set-extent-property extent 'mouse-face 'highlight)
    (set-extent-property extent 'keymap pbp-keymap)
    (set-extent-property extent 'pbp-top-element name)))

(defun pbp-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) (l (length string)) (stack ()) (topl ()) ext n
	   (out (make-string l ?x )) )
      (while (< ip l)
	(if (not (char-equal (aref string ip) pbp-annotation-char))
	    (progn (aset out op (aref string ip))
		   (setq op (+ 1 op)))
	  (setq ip (+ 1 ip))
	  (cond 
	    ((char-equal (aref string ip) pbp-goal-char)
	     (setq topl (append topl (list (+ 1 op)) )))
	    ((char-equal (aref string ip) pbp-start-char)
	     (setq n (setq ip (+ 1 ip)))
	     (while (not (char-equal (aref string ip) pbp-annotation-char))
	       (setq ip (+ 1 ip)))
	     (setq stack (cons op (cons (substring string n ip) stack)))
	     (setq ip (+ 1 ip)))
	    ((char-equal (aref string ip) pbp-field-char)
	     (setq ext (make-extent (car stack) op out))
	     (set-extent-property ext 'mouse-face 'highlight)
	     (set-extent-property ext 'keymap pbp-keymap)
	     (set-extent-property ext 'pbp (cadr stack))
	     (set-extent-property ext 'duplicable t)
	     (setq stack (cddr stack)))))
	(setq ip (+ 1 ip)))
      
      (pop-to-buffer pbp-goals-buffer)
      (erase-buffer)
      (insert (substring out 0 op))
      (while (setq ip (car topl) 
		   topl (cdr topl))
	(pbp-make-top-extent ip (car topl)))
      (pbp-make-top-extent ip (point-max)))))

; Receiving the data from Lego is performed that a filter function
; added among the comint-output-filter-functions of the shell-mode.

(deflocal pbp-mark-ext nil "last mark")
(deflocal pbp-sanitise t "sanitise output?")

(defun pbp-sanitise-string (string)
  (if pbp-sanitise 
      (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
	(while (< ip l)
	  (if (char-equal (aref string ip) pbp-annotation-char)
	      (if (char-equal (aref string (setq ip (+ 1 ip))) 
			      pbp-start-char)
		  (progn
		    (while (not (char-equal (aref string ip) 
					    pbp-annotation-char))
		      (setq ip (+ 1 ip)))
		    (setq ip (+ 1 ip))))
	    (aset out op (aref string ip))
	    (setq op (+ 1 op)))
	  (setq ip (+ 1 ip)))
	(substring out 0 op))
    string))

(defun pbp-display-error (string)
  (save-excursion
    (pop-to-buffer pbp-goals-buffer)
    (goto-char (point-max))
    (if (re-search-backward proof-error-regexp nil t) 
	(delete-region (- (point) 2) (point-max)))
    (newline 2)
    (let ((start (point)))
	  (insert-string string)
	  
	  ;; tms - I don't really understand what this is doing, but omitting it
	  ;; will not give any fontification via font-lock
	  (font-lock-fontify-syntactically-region start (point-max))
	  
	   ;; display complete region in red
	  (put-nonduplicable-text-property start (point-max)
					   'face font-lock-error-face)
	  ;; fontify according to the appropriate font-lock table
	  (font-lock-fontify-keywords-region start (point-max)))))

(defun pbp-send-and-remember (string)
  (save-excursion
    (proof-simple-send string)
    (if (and (boundp 'pbp-script-buffer) pbp-script-buffer)
	(progn (set-buffer pbp-script-buffer)
	       (end-of-buffer)
	       (insert-string string)))))

(defun pbp-process-string (string)
  
  (let (start end)
    (save-excursion 
      (cond 
       ((string-match proof-error-regexp string)
	(pbp-display-error 
	 (pbp-sanitise-string (substring string (match-beginning 0)))))

       ((string-match proof-shell-abort-goal-regexp string)
	(erase-buffer pbp-goals-buffer))
     
       ((string-match proof-shell-proof-completed-regexp string)
	(erase-buffer pbp-goals-buffer)
	(insert-string (concat "\n" (match-string 0 string)) pbp-goals-buffer))
     
       ((string-match pbp-start-goals-string string)
	(while (progn (setq start (match-end 0))
		      (string-match pbp-start-goals-string string start)))
	(string-match pbp-end-goals-string string start)
	(setq end (match-beginning 0))
	(pbp-analyse-structure (substring string start end)))

       ((string-match pbp-result-start string)
	(setq start (+ 1 (match-end 0)))
	(string-match pbp-result-end string)
	(setq end (- (match-beginning 0) 1))
	(pbp-send-and-remember (substring string start end)))))))

(defun pbp-filter (str) 
  (if (string-match pbp-wakeup-character str)
      (save-excursion
	(set-buffer (proof-shell-buffer))
	(let (string mrk)
	  (while (progn (goto-char (extent-start-position pbp-mark-ext))
			(setq mrk (point-marker))                        
			(search-forward pbp-annotated-prompt-string nil t))
	    (set-extent-endpoints pbp-mark-ext (point) (point))
	    (backward-char (length pbp-annotated-prompt-string))
	    (setq string (buffer-substring mrk (point)))
	    (delete-region mrk (point))
	    (insert (pbp-sanitise-string string))
	    (goto-char (extent-start-position pbp-mark-ext))
	    (backward-delete-char 1)
	    (pbp-process-string string))))))

; Call after the shell is started

(defun pbp-goals-init ()
  (save-excursion
    (setq pbp-goals-buffer (get-buffer-create pbp-goals-buffer-name ))
    (set-buffer pbp-goals-buffer)
    (funcall pbp-mode-is)
    (erase-buffer pbp-goals-buffer)
    (add-hook 'comint-output-filter-functions 'pbp-filter t)
    (set-buffer (proof-shell-buffer))
    (setq pbp-mark-ext (make-extent (point-max) (point-max)))
    (set-extent-property pbp-mark-ext 'detachable nil)
    (set-extent-property pbp-mark-ext 'start-open nil)
    (set-extent-property pbp-mark-ext 'end-open t)
    (add-hook 'proof-shell-exit-hook
	      (lambda ()
		(remove-hook 'comint-output-filter-functions 'pbp-filter)))))

; Now, using the extents in a mouse behavior is quite simple:
; from the mouse position, find the relevant extent, then get its annotation
; and produce a piece of text that will be inserted in the right buffer.
; Attaching this behavior to the mouse is simply done by attaching a keymap
; to all the extents.


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
		  (format pbp-goal-command  path)))))

	     ((extentp top-ext)
	      (let ((top-info (extent-property top-ext 'pbp-top-element)))
		(if (eq 'hyp (car top-info))
		    (proof-command (format pbp-hyp-command (cdr top-info)))
		  (pbp-send-and-remember 
		   (format proof-shell-change-goal (cdr top-info)))))))))

(define-derived-mode pbp-mode fundamental-mode "Pbp" "Proof by Pointing"
  (suppress-keymap pbp-mode-map))

(provide 'pbp)
