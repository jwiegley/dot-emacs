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
	(phox-mode)
	(x-symbol-mode t) ; just to be sure
	(font-lock-mode t) ; just to be sure (not activated on OSX ??
	))
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
(defun pg-pbrpm-exists (f l0)
  (if (null l0) nil
    (or (funcall f (car l0)) (pg-pbrpm-exists f (cdr l0)))))

(defun pg-pbrpm-eliminate-id (acc l)
  (if (null l) (reverse acc)
    (if 
	(pg-pbrpm-exists (lambda (x) 
			   (string= (car x) (car (car l)))) acc)
	(pg-pbrpm-eliminate-id acc (cdr l))
      (pg-pbrpm-eliminate-id (cons (car l) acc) (cdr l)))))

(defun pg-pbrpm-build-menu (event start end)
"Build a Proof By Rules pop-up menu according to the state of the proof, the event and a selected region (between the start and end markers).
The prover command is processed via pg-pbrpm-run-command."
   ;first, run the prover specific (name, rule)'s list generator
   (setq click-info (pg-pbrpm-process-click event start end)) ; retrieve click informations
   (if click-info
       (let
	 ((pbrpm-list 
	   (pg-pbrpm-eliminate-id nil (mapcar 'cdr
					      (sort 
					       (proof-pbrpm-generate-menu
						click-info
						(pg-pbrpm-process-regions-list))
					       (lambda (l1 l2) (< (car l1) (car l2)))))))
	  (count 0))
					; retrieve selected region informations
					; then make that list a menu description
	 (if pbrpm-list
	     (if (not pg-pbrpm-use-buffer-menu)
		 (progn
		   (setq pbrpm-menu-desc '("PBRPM-menu"))
		   (while pbrpm-list
		     (let* ((pbrpm-list-car (pop pbrpm-list))
			    (description (pop pbrpm-list-car))
			    (command (concat "(*" description "*)\n" (pop pbrpm-list-car))))
		       (setq pbrpm-menu-desc
			     (append pbrpm-menu-desc
				     (list (vector
					    description
					    (list 'pg-pbrpm-run-command command)))))))
					; finally display the pop-up-menu
		   (popup-menu pbrpm-menu-desc))
	       (pg-pbrpm-create-reset-buffer-menu)
	       (while pbrpm-list
		 (let* ((pbrpm-list-car (pop pbrpm-list))
		       (description (pop pbrpm-list-car))
		       (command (concat "(*" description "*)\n" (pop pbrpm-list-car)))
		       (pos (point)))
		   (insert-string " ")
		   (insert-string description)
		   (setq count (+ 1 count))
		   (insert-gui-button (make-gui-button 
				       (concat (int-to-string count) ")")
				       'pg-pbrpm-run-command command) pos)
		   (insert "\n")))
		 (insert-gui-button (make-gui-button 
				   "Cancel" 
				   (lambda (n) (erase-buffer pg-pbrpm-buffer-menu) (delete-frame)) nil))
		 (x-symbol-decode)
		 (make-dialog-frame '(width 80 height 30)))
	       (beep)))))

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
    
(defun pg-pbrpm-translate-position (buffer pos)
  "return pos if buffer is goals-buffer otherwise, return the point position in 
   the goal buffer"
  (if (eq proof-goals-buffer buffer) pos
    (point proof-goals-buffer)))

(defun pg-pbrpm-process-click (event start end)
"Returns the list of informations about the click needed to call generate-menu. EVENT is an event."
  (save-excursion
    (save-window-excursion
      (mouse-set-point event)
      (let* ((pos (event-point event))
	     (buffer (event-buffer event))
	     (r (pg-pbrpm-get-pos-info  (pg-pbrpm-translate-position buffer pos))))
	(if r (list
	       (string-to-int (car r)) ; should not be an int for other prover
	       (if (eq proof-goals-buffer buffer) (cdr r) (auto-select-arround-pos))
	       (if (and start end (eq proof-goals-buffer buffer) 
			(<= (marker-position start) pos) (<= pos  (marker-position end)))
		   (pg-pbrpm-region-expression buffer (marker-position start) 
					       (marker-position end))
		 (auto-select-arround-pos))))))))

;;--------------------------------------------------------------------------;;
;; Selected Region informations extractors
;;--------------------------------------------------------------------------;;
(defvar pg-pbrpm-remember-region-selected-region nil)
(defvar pg-pbrpm-regions-list nil)

(defun pg-pbrpm-erase-regions-list ()
  (message "erase list")
  (mapc (lambda (span) (delete-span span)) pg-pbrpm-regions-list)
  (setq pg-pbrpm-regions-list nil)
  nil)

(add-hook 'mouse-track-drag-up-hook (lambda (event count) 
				      (if (not (member 'control (event-modifiers event)))
					  (pg-pbrpm-erase-regions-list))))

(defun pg-pbrpm-filter-regions-list ()
  (let ((l pg-pbrpm-regions-list))
    (setq pg-pbrpm-regions-list nil)
    (mapc (lambda (span) (if (span-live-p span)
			     (setq pg-pbrpm-regions-list (cons span pg-pbrpm-regions-list))
			   (delete-span span))) l)))

(defface pg-pbrpm-multiple-selection-face
  (proof-face-specs
   (:background "orange")
   (:background "darkorange")   
   (:italic t))
  "*Face for showing (multiple) selection."
  :group 'proof-faces)

(defun pg-pbrpm-do-remember-region (start end)
  (pg-pbrpm-filter-regions-list)
   (if (and start end (not (eq start end))) ; if a region is selected
       (let ((span (make-span start end))
	     (found nil))
	 (setq pg-pbrpm-regions-list (mapcar (lambda (oldspan) 
		   (let ((oldstart (span-start oldspan))
			 (oldend (span-end oldspan)))
		     (if (and (eq (current-buffer) (span-buffer oldspan))
			      (or (and (<= start oldstart) (<= oldstart end))
				  (and (<= start oldend) (<= oldend end))))
			 (progn
			   (setq found t)
			   (delete-span oldspan)
			   span) 
			 oldspan))) pg-pbrpm-regions-list))
	 (if (not found) (setq pg-pbrpm-regions-list (cons span pg-pbrpm-regions-list))) 
	 (set-span-property span 'face 'pg-pbrpm-multiple-selection-face))))

; the follwing are adapted from mouse-track-insert from mouse.el

(defun pg-pbrpm-remember-region-drag-up-hook (event click-count)
  (setq pg-pbrpm-remember-region-selected-region
	(default-mouse-track-return-dragged-selection event)))

(defun pg-pbrpm-remember-region-click-hook (event click-count)
  (default-mouse-track-drag-hook event click-count nil)
  (pg-pbrpm-remember-region-drag-up-hook event click-count)
  t)

(defun pg-pbrpm-remember-region (event &optional delete)
  "Allow multiple selection as a list of spam stored in ???. The current (standard)
   selection in the same buffer is also stored"
  (interactive "*e")
  (setq pg-pbrpm-remember-region-selected-region nil)
  (let ((mouse-track-drag-up-hook 'pg-pbrpm-remember-region-drag-up-hook)
 	(mouse-track-click-hook 'pg-pbrpm-remember-region-click-hook)
	(start (point)) (end (mark)))
	       (if (and start end) (pg-pbrpm-do-remember-region start end))
	       (mouse-track event)
	       (if (consp pg-pbrpm-remember-region-selected-region)
		   (let ((pair pg-pbrpm-remember-region-selected-region))
		     (pg-pbrpm-do-remember-region (car pair) (cdr pair))))))

(defun pg-pbrpm-process-region (span)
"Returns the list of informations about the the selected region needed to call generate-menu. span is a span covering the selected region"
   (let ((start (span-start span))
	 (end (span-end span))
	 (buffer (span-buffer span)))
     (if (and start end) ; if a region is selected
	 (if (eq proof-goals-buffer buffer)
	  (progn
	    (setq r (pg-pbrpm-get-region-info start end))
	    (if r 
		(progn (message "1%s %d %d" (pg-pbrpm-region-expression buffer start end) start end)
		(list
		 (string-to-int (car r)) ; should not be an int for other prover
		 (cdr r)
		 (pg-pbrpm-region-expression buffer start end)))
	      (progn
		(message "2%s" (pg-pbrpm-region-expression buffer start end))
		(list 0 "none" (pg-pbrpm-region-expression buffer start end)))))
	(progn
	  (message "3%s" (pg-pbrpm-region-expression buffer start end))
	  (list 0 "none" (pg-pbrpm-region-expression buffer start end)))))))

(defun pg-pbrpm-process-regions-list ()
  (pg-pbrpm-do-remember-region (point-marker) (mark-marker))
  (mapcar (lambda (span) (pg-pbrpm-process-region span)) pg-pbrpm-regions-list))

(defun pg-pbrpm-region-expression (buffer start end)
"Valid parenthesis'd expression."
   ; an expression is valid if it has as many left paren' as right paren'
    (buffer-substring start end buffer))
;    (let
;      ((pbrpm-left-pars 0)
;      (pbrpm-right-pars 0)
;      (pos start))
;     (while (< pos end)
;       (if (proof-pbrpm-left-paren-p (char-after pos))
;	   (setq pbrpm-left-pars (+ pbrpm-left-pars 1)))
;       (if (proof-pbrpm-right-paren-p (char-after pos))
;	   (setq pbrpm-right-pars (+ pbrpm-right-pars 1)))
;       (setq pos (+ pos 1)))
;     (if (= pbrpm-left-pars pbrpm-right-pars)
;	 (buffer-substring start end buffer)
;       (progn
;	 nil ; TODO : define how to manage this error case
;					;we could call (pg-pbrpm-dialog "Selected region is not valid), then what about the state of the process ?
;	 ))))

;;--------------------------------------------------------------------------;;

(require 'pg-goals)
(define-key proof-goals-mode-map [(button3)] 'pg-pbrpm-button-action)
(define-key proof-goals-mode-map [(control button3)] 'pg-goals-yank-subterm)
(define-key proof-goals-mode-map [(control button1)] 'pg-pbrpm-remember-region)
(define-key pg-span-context-menu-keymap [(button3)] 'pg-pbrpm-button-action)
(define-key pg-span-context-menu-keymap [(control button3)] 'pg-span-context-menu)
(define-key proof-mode-map [(button3)] 'pg-pbrpm-button-action)
(define-key proof-mode-map [(control button3)] 'pg-goals-yank-subterm)
(define-key proof-mode-map [(control button1)] 'pg-pbrpm-remember-region)

(provide 'pg-pbrpm)
;; pg-pbrpm ends here