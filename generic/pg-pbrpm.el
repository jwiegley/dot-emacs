;; pg-pbrpm.el  Proof General - Proof By Rules Pop-up Menu - mode.
;;
;; Copyright (C) 2004 - Universite de Savoie, France.
;; Authors:   Jean-Roch SOTTY, Christophe Raffalli
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;

;; analysis of the goal buffer


(defvar pg-pbrpm-use-buffer-menu t
  "if t, pbrpm will use a menu displayed in a dialog fram instead of a popup menu")
(defvar pg-pbrpm-buffer-menu nil)
(defvar pg-pbrpm-goal-description nil)

(defun pg-pbrpm-create-reset-buffer-menu ()
  "Create if necessary and erase all text in the buffer menu"
  (if (or (not pg-pbrpm-buffer-menu) (not (buffer-live-p pg-pbrpm-buffer-menu)))
      (progn
	(setq pg-pbrpm-buffer-menu
	      (generate-new-buffer (generate-new-buffer-name "*proof-menu*")))
	(set-buffer pg-pbrpm-buffer-menu)
	(phox-mode)))
  (erase-buffer pg-pbrpm-buffer-menu)
  (set-buffer pg-pbrpm-buffer-menu))

(defun pg-pbrpm-analyse-goal-buffer ()
  "This function analyses the goal buffer and produces a table to find goals and hypothesis.
   If stores, in the variable pg-pbrpm-goal-description, a list with shape

   (start-goal end-goal goal-name start-concl hyps ...) with 5 elements for each goal:

     start-goal: the position of the first char of the goal
     end-goal: the position of the last char of the goal
     goal-name: the goal name (or number)
     start-concl: the position of first char of the conclusion of the goal
     hyps: the list of hypothesis with the shape:
       
  (start-hyp start-hyp-text end-hyp hyp-name ...) with 4 elemets per hypothesis:
     start-hyp: the position of the first char of the hypothesis (including its name)
     start-hyp-text: the position of the first char of the hypothesis formula (no name)
     end-hyp: the position of the last char of the hypothesis
     hyp-name: then name of the hypothesis.
"
  (save-excursion
    (set-buffer proof-goals-buffer)
    (goto-char 0)
    (let 
	((goals nil))
      (progn 
	(while (search-forward-regexp pg-pbrpm-start-goal-regexp nil t)
	  (let
	      ((hyps nil)
	       (start-goal (match-end 0))
	       (goal-num (match-string pg-pbrpm-start-goal-regexp-par-num))
	       (end-goal (search-forward-regexp pg-pbrpm-end-goal-regexp nil t)))
	    (goto-char start-goal)
	    (while (search-forward-regexp pg-pbrpm-start-hyp-regexp end-goal t)
	      (let
		  ((start-hyp (match-beginning 0))
		   (start-hyp-text (match-end 0))
		   (hyp-name (match-string pg-pbrpm-start-hyp-regexp-par-num))
		   (end-hyp (- (if
				(search-forward-regexp pg-pbrpm-start-hyp-regexp end-goal t)
				(match-beginning 0)
			      (search-forward-regexp pg-pbrpm-start-concl-regexp end-goal t)
			      (match-beginning 0)) 1)))
		(goto-char start-hyp-text)
		(setq hyps 
		      (append
		       (list start-hyp start-hyp-text end-hyp hyp-name) 
		       hyps))))
	    
	    (setq goals 
		  (append
		   (list start-goal end-goal goal-num 
			 (search-forward-regexp pg-pbrpm-start-concl-regexp nil t) hyps)
		   goals))))
	  (setq pg-pbrpm-goal-description goals)))))

(add-hook 'proof-shell-handle-delayed-output-hook 'pg-pbrpm-analyse-goal-buffer)


;;--------------------------------------------------------------------------;;
;; the Rules Popup Menu functions
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-button-action (event)
"This function is bound to a CTRL-RightClick in the Proof General goals buffer."
   (interactive "e")
   (save-excursion
   (pg-pbrpm-build-menu event (point-marker) (mark-marker))
   )
)

(defun pg-pbrpm-build-menu (event start end)
"Build a Proof By Rules pop-up menu according to the state of the proof, the event and a selected region (between the start and end markers).
The prover command is processed via pg-pbrpm-run-command."
   ;first, run the prover specific (name, rule)'s list generator
   (setq click-info (pg-pbrpm-process-click event start end)) ; retrieve click informations
   (if click-info
       (progn
	 (setq pbrpm-list 
	       (mapcar 'cdr
	       (sort 
		(proof-pbrpm-generate-menu
		 click-info
		 (pg-pbrpm-process-region start end))
		(lambda (l1 l2) (< (car l1) (car l2))))))
					; retrieve selected region informations
					; then make that list a menu description
	 
	 (if (not pg-pbrpm-use-buffer-menu)
	     (progn
	       (setq pbrpm-menu-desc '("PBRPM-menu"))
	       (while pbrpm-list
		 (setq pbrpm-list-car (pop pbrpm-list))
		 (setq pbrpm-menu-desc
		       (append pbrpm-menu-desc
			       (list (vector
				      (pop pbrpm-list-car)
				      (list 'pg-pbrpm-run-command (pop pbrpm-list-car)))))))
					; finally display the pop-up-menu
	       (popup-menu pbrpm-menu-desc))
	   (pg-pbrpm-create-reset-buffer-menu)
	   (while pbrpm-list
	     (setq pbrpm-list-car (pop pbrpm-list))
	     (setq description (pop pbrpm-list-car))
	     (setq command (pop pbrpm-list-car))
	     (setq pos (point))
	     (insert-string " ")
	     (insert-string description)
	     (insert-gui-button (make-gui-button "Go" 'pg-pbrpm-run-command command) pos)
	     (insert "\n"))
	   (insert-gui-button (make-gui-button 
			       "Cancel" 
			       (lambda (n) (erase-buffer pg-pbrpm-buffer-menu) (delete-frame)) nil))
	   (x-symbol-decode)
	   (make-dialog-frame '(width 80 height 30))))))

(defun pg-pbrpm-run-command (command)
"Insert COMMAND into the proof queue and then run it.
-- adapted from proof-insert-pbp-command --"
   (if pg-pbrpm-use-buffer-menu 
       (progn
	 (erase-buffer pg-pbrpm-buffer-menu)
	 (delete-frame)))
   (set-buffer proof-script-buffer)
   (proof-activate-scripting)
   (let (span)
      (proof-goto-end-of-locked)
      (set-buffer proof-script-buffer)
      (proof-activate-scripting)
      (insert (concat "\n" command))
      (setq span (make-span (proof-locked-end) (point)))
      ; TODO : define the following properties for PBRPM, I don't understand their use ...
      (set-span-property span 'type 'pbp)
      (set-span-property span 'cmd command)
      (proof-start-queue (proof-unprocessed-begin) (point)
         (list (list span command 'proof-done-advancing))))
)

;;--------------------------------------------------------------------------;;
;; Click Informations extractors
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-get-pos-info (pos)
  "return (n . s) where
    n is the goal name
    s if either the hypothesis name, \"none\" (for the conclusion) of \"whole\" in strange cases"
  (let ((l pg-pbrpm-goal-description)
	(found nil))
    (while (and l (not found)) 
      (setq start-goal (car l))
      (setq end-goal (cadr l))
      (setq goal-name (caddr l))
      (setq start-concl (cadddr l))
      (setq hyps (car (cddddr l)))
      (setq l (cdr (cddddr l)))
      (if (and (<= start-goal pos) (<= pos end-goal))
	  (progn
	    (setq found t)
	    (setq the-goal-name goal-name))))
    (if found 
	(progn  
	  (if (<= start-concl pos)
	      (setq the-click-info "none")
	    (setq found nil)
	    (while (and hyps (not found))
	      (setq start-hyp (car hyps))
	      (setq start-hyp-text (cadr hyps))
	      (setq end-hyp (caddr hyps))
	      (setq hyp-name (cadddr hyps))
	      (setq hyps (cddddr hyps))
	      (if (and (<= start-hyp pos) (<= pos end-hyp))
		  (progn 
		    (setq found t)
		    (setq the-click-info hyp-name))))
	    (if (not found)
		(setq the-click-info "whole")))
	  (cons the-goal-name the-click-info)))))

(defun pg-pbrpm-get-region-info (start end)
   "see pg-pbrpm-get-pos-info and source code :-)"
   (setq r1 (pg-pbrpm-get-pos-info start))
   (setq r2 (pg-pbrpm-get-pos-info start))
   (if (and r1 r2 (string-equal (car r1) (car r2)))
       (if (string-equal (cdr r1) (cdr r2))
	   r1
	 (cons (car r1) "whole"))
     nil))
	 
(defun auto-select-arround-pos ()
  "extract some text arround the current  cursor position"
  (save-excursion
    (let ((pos (point)))
      (beginning-of-line)
      (block 'loop
	(while (< (point) pos)
	  (if (not (search-forward-regexp pg-pbrpm-auto-select-regexp nil t)) (return-from 'loop ""))
	  (if (and (<= (match-beginning 0) pos) (<= pos (match-end 0)))
	      (return-from 'loop (match-string 0))))
	(return-from 'loop "")))))
    
(defun pg-pbrpm-process-click (event start end)
"Returns the list of informations about the click needed to call generate-menu. EVENT is an event."
  (save-excursion
    (mouse-set-point event)
    (let* ((pos (point))
	  (r (pg-pbrpm-get-pos-info pos)))
      (if r (list
	     (string-to-int (car r)) ; should not be an int for other prover
	     (cdr r)
	     (if (and start end (string-equal (buffer-name proof-goals-buffer) (buffer-name (marker-buffer end))) (<= (marker-position start) pos) (<= pos  (marker-position end)))
		 (pg-pbrpm-region-expression start end)
	       (auto-select-arround-pos)))))))

;;--------------------------------------------------------------------------;;
;; Selected Region informations extractors
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-process-region (start end)
"Returns the list of informations about the the selected region needed to call generate-menu. START and END are markers"
   (if (and start end) ; if a region is selected
      (if (string-equal (buffer-name proof-goals-buffer) (buffer-name (marker-buffer end)))
	  (progn
	    (setq r (pg-pbrpm-get-region-info (marker-position start) (marker-position end)))
	    (if r 
		(list
		 (string-to-int (car r)) ; should not be an int for other prover
		 (cdr r)
		 (pg-pbrpm-region-expression start end))
	      (progn
		(set-buffer (marker-buffer start))
		(list 0 "none" (pg-pbrpm-region-expression start end)))))
	(progn
	  (set-buffer (marker-buffer start))
	  (list 0 "none" (pg-pbrpm-region-expression start end))))
     nil ; TODO : define how to manage this error case
     ))

(defun pg-pbrpm-region-expression (start end)
"Valid parenthesis'd expression."
   ; an expression is valid if it has as many left paren' as right paren'
   (let
      ((pbrpm-region-char (marker-position start))
      (pbrpm-left-pars 0)
      (pbrpm-right-pars 0))
     (while (<= pbrpm-region-char (marker-position end))
       (if (proof-pbrpm-left-paren-p (char-after pbrpm-region-char))
	   (setq pbrpm-left-pars (+ pbrpm-left-pars 1)))
       (if (proof-pbrpm-right-paren-p (char-after pbrpm-region-char))
	   (setq pbrpm-right-pars (+ pbrpm-right-pars 1)))
       (setq pbrpm-region-char (+ pbrpm-region-char 1)))
     (if (= pbrpm-left-pars pbrpm-right-pars)
	 (buffer-substring (marker-position start) (marker-position end) (marker-buffer start))
       (progn
	 nil ; TODO : define how to manage this error case
					;we could call (pg-pbrpm-dialog "Selected region is not valid), then what about the state of the process ?
	 ))))

;;--------------------------------------------------------------------------;;

(require 'pg-goals)
(define-key proof-goals-mode-map [(button3)] 'pg-pbrpm-button-action)
(define-key proof-goals-mode-map [(control button3)] 'pg-goals-yank-subterm)

(provide 'pg-pbrpm)
;; pg-pbrpm ends here