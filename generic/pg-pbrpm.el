;; pg-pbrpm.el  Proof General - Proof By Rules Pop-up Menu - mode.
;;
;; Copyright (C) 2004 - Universite de Savoie, France.
;; Authors:   Jean-Roch SOTTY, Christophe Raffalli
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;

;;--------------------------------------------------------------------------;;
;; the Rules Popup Menu functions
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-button-action (event)
"This function is bound to a CTRL-RightClick in the Proof General goals buffer."
   (interactive "e")
   (save-excursion
   (proof-pbrpm-regexps)
   (pg-pbrpm-build-menu event (point-marker) (mark-marker))
   )
)

(defun pg-pbrpm-build-menu (event start end)
"Build a Proof By Rules pop-up menu according to the state of the proof, the event and a selected region (between the start and end markers).
The prover command is processed via pg-pbrpm-run-command."
   ;first, run the prover specific (name, rule)'s list generator
   (setq pbrpm-list 
      (proof-pbrpm-generate-menu
         (pg-pbrpm-process-click event) ; retrieve click informations
         (pg-pbrpm-process-region start end) ; retrieve selected region informations
      )
   )
   ; then make that list a menu description
   (setq pbrpm-menu-desc '("PBRPM-menu"))
   (while pbrpm-list
      (setq pbrpm-list-car (pop pbrpm-list))
      (setq pbrpm-menu-desc
         (append pbrpm-menu-desc
            (list (vector
                  (pop pbrpm-list-car)
                  (list 'pg-pbrpm-run-command (pop pbrpm-list-car))
            ))
         )
      )
   )
   ; finally display the pop-up-menu
   (popup-menu pbrpm-menu-desc)
)

(defun pg-pbrpm-run-command (command)
"Insert COMMAND into the proof queue and then run it.
-- adapted from proof-insert-pbp-command --"
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

(defun pg-pbrpm-process-click (event)
"Returns the list of informations about the click needed to call generate-menu. EVENT is an event."
   (list
      (pg-pbrpm-click-goal-number event)
      (pg-pbrpm-click-hyp-or-ccl event)
      (pg-pbrpm-click-expression event)
      (pg-pbrpm-click-tree-depth event)
   )
)

(defun pg-pbrpm-click-goal-number (event)
"Number of the goal where the cliked happened"
   (mouse-set-point event)
   (search-backward-regexp goal-backward-regexp)
   (setq str (match-string 0))
   (string-match goal-number-regexp str)
   (string-to-int (match-string 0 str))
)

(defun pg-pbrpm-click-hyp-or-ccl (event)
"none -> a conclusion, Hyp-name -> an hypothesis, whole -> the whole goal"
   (mouse-set-point event)
   (let
       ((save-point (point))
	(gl-point (search-backward-regexp goal-backward-regexp 0 t 1)))
     (goto-char save-point)
     (if (search-backward-regexp ccl-backward-regexp gl-point t 1)
	    (identity "none")
	    (if (search-backward-regexp hyp-backward-regexp 0 t)
		(match-string 1)
	      (identity "whole")
	     )
      )
   )
)

(defun pg-pbrpm-click-expression (event)
"Valid parenthesis'd expression."
   (mouse-set-point event)
   (setq pbrpm-exp-start (event-point event))
   (setq pbrpm-exp-end (event-point event))
   ; TODO : add invisible parenthesis management and limits' conditions (regexps)
;   (while (not (proof-pbrpm-left-paren-p (char-after pbrpm-exp-start)))
;      (setq pbrpm-exp-start (- pbrpm-exp-start 1)))
;   (while (not (proof-pbrpm-right-paren-p (char-after pbrpm-exp-end)))
;      (setq pbrpm-exp-end (+ pbrpm-exp-end 1)))
   (buffer-substring-no-properties pbrpm-exp-start (+ pbrpm-exp-end 1))
   ; buffer-substring or buffer-substring-no-properties ?
)

(defun pg-pbrpm-click-tree-depth (event)
"Click depth in the tree. If clicking on a parenthesis, the whole expression is considered."
   (pg-pbrpm-click-or-region-tree-depth (event-point event))
)


;;--------------------------------------------------------------------------;;
;; Selected Region informations extractors
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-process-region (start end)
"Returns the list of informations about the the selected region needed to call generate-menu. START and END are markers"
   (if (and start end) ; if a region is selected
      (if (string-equal (buffer-name proof-goals-buffer) (buffer-name (marker-buffer end)))
         (list
            (pg-pbrpm-region-goal-number start end)
            (pg-pbrpm-region-hyp-or-ccl start end)
            (pg-pbrpm-region-expression start end)
            (pg-pbrpm-region-tree-depth start end)
         )
         (progn
            (set-buffer (marker-buffer start))
            (list 0 "none" (buffer-substring (marker-position start) (marker-position end)) nil)
         )
      )
      nil ; TODO : define how to manage this error case
   )
)

(defun pg-pbrpm-region-goal-number (start end)
"Goal number of the region"
   (goto-char (min (marker-position start) (marker-position end)))
   (search-backward-regexp goal-backward-regexp)
   (setq str (match-string 0))
   (string-match goal-number-regexp str)
   (string-to-int (match-string 0 str))
)

(defun pg-pbrpm-region-hyp-or-ccl (start end)
"none -> a conclusion, Hyp-name -> an hypothesis, whole -> the whole goal"
   (goto-char (min (marker-position start) (marker-position end)))
   (let
       ((save-point (point))
	(gl-point (search-backward-regexp goal-backward-regexp 0 t 1)))
     (goto-char save-point)
     (if (search-backward-regexp ccl-backward-regexp gl-point t 1)
	 (identity "none")
       (if (search-backward-regexp hyp-backward-regexp 0 t)
	   (match-string 1)
         (identity "whole")
      )
   )
))

(defun pg-pbrpm-region-expression (start end)
"Valid parenthesis'd expression."
   ; an expression is valid if it has as many left paren' as right paren'
   (setq
      pbrpm-region-char (marker-position start)
      pbrpm-left-pars 0
      pbrpm-right-pars 0)
   (while (<= pbrpm-region-char (marker-position end))
      (if (proof-pbrpm-left-paren-p (char-after pbrpm-region-char))
         (setq pbrpm-left-pars (+ pbrpm-left-pars 1)))
      (if (proof-pbrpm-right-paren-p (char-after pbrpm-region-char))
         (setq pbrpm-right-pars (+ pbrpm-right-pars 1)))
      (setq pbrpm-region-char (+ pbrpm-region-char 1))
   )
   (if (= pbrpm-left-pars pbrpm-right-pars)
      (buffer-substring (marker-position start) (marker-position end))
      nil ; TODO : define how to manage this error case
      ;we could call (pg-pbrpm-dialog "Selected region is not valid), then what about the state of the process ?
   )
)

(defun pg-pbrpm-region-tree-depth (start end)
"Region depth in the tree. If beginning the region on a parenthesis, the whole expression is considered."
   (pg-pbrpm-click-or-region-tree-depth (marker-position start))
)


;;--------------------------------------------------------------------------;;
;; Generic informations extractors
;;--------------------------------------------------------------------------;;

(defun pg-pbrpm-click-or-region-tree-depth (position)
"Click or Region depth in the tree. If the (char-after position) is a parenthesis, the whole expression is considered."
   ; TODO : check again this algorithm ...
   (goto-char position)
   ;first, wether a ccl, hyp or goal, find the forward seeking start point
   (if (search-backward-regexp ccl-backward-regexp 1 t 1)
      (setq pbrpm-ccl (match-end 0))
      (setq pbrpm-ccl 1))
   (if (search-backward-regexp hyp-backward-regexp 1 t 1)
      (setq pbrpm-hyp (match-end 0))
      (setq pbrpm-hyp 1))
   (if (search-backward-regexp goal-backward-regexp 1 t 1)
      (setq pbrpm-goal (match-end 0))
      (setq pbrpm-goal 1))
   (setq pbrpm-exp-char (max pbrpm-ccl pbrpm-hyp pbrpm-goal))

   ;work the tree depth list out
   (setq
      pbrpm-exp-end position
      pbrpm-depth 0
      pbrpm-tree-list '())
   (while (<= pbrpm-exp-char pbrpm-exp-end) ; TODO : check this test ...
      ; openning parenthesis case
      (if (proof-pbrpm-left-paren-p (char-after pbrpm-exp-char))
         (progn
            (if (= pbrpm-depth (length pbrpm-tree-list))
               (push 1 pbrpm-tree-list)
            (setq pbrpm-tree-list (list (+ (car pbrpm-tree-list) 1) (cdr pbrpm-tree-list)))
            )
         (setq pbrpm-depth (+ pbrpm-depth 1))
         )
      )
      ; closing parenthesis case
      (if (proof-pbrpm-right-paren-p (char-after pbrpm-exp-char))
         (progn
            (if (< (length pbrpm-tree-list) pbrpm-depth)
               (setq pbrpm-tree-list (cdr pbrpm-tree-list))
            )
            (setq pbrpm-depth (- pbrpm-depth 1))
         )
      )
      (setq pbrpm-exp-char (+ pbrpm-exp-char 1))
   )
   (reverse pbrpm-tree-list)
)

;;--------------------------------------------------------------------------;;
;; Error messages management
;;--------------------------------------------------------------------------;;

; unused for now ...
(defun pg-pbrpm-dialog (message)
   (make-dialog-box 'question
   :title "PBRPM-ERROR"
   :modal t
   :question message
   :buttons (list (vector " OK " '(identity nil) t)))
)

; TODO : use also log messages in the minibuffer ...


;;--------------------------------------------------------------------------;;

(require 'pg-goals)
(define-key proof-goals-mode-map [(button3)] 'pg-pbrpm-button-action)
(define-key proof-goals-mode-map [(control button3)] 'pg-goals-yank-subterm)

(provide 'pg-pbrpm)
;; pg-pbrpm ends here