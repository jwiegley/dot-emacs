;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; program extraction.
;;
;; note : program extraction is still experimental
;;--------------------------------------------------------------------------;;

(defun af2-compile-theorem(name)
  "Interactive function : 
ask for the name of a theorem and send a compile command to af2 for it."
  (interactive "stheorem : ")
  (proof-shell-invisible-command (concat "compile " name ".\n")))

(defun af2-compile-theorem-around-point()
"Interactive function : 
send a compile command to af2 for the theorem which name is under the cursor."
  (interactive)
  (let (start end)
    (save-excursion
      (forward-word 1)
      (setq start (point))
      (forward-word -1)
      (setq end (point)))
    (af2-compile-theorem (buffer-substring start end))))


(setq
 af2-forget-id-command "del %s.\n"
 af2-sy-definition-regexp "^[ \t\n\r]*\\(Cst\\|def\\)[ \t\n\r]*\\(\\(rInfix\\|lInfix\\|Infix\\|Prefix\\|Postfix\\)[^\"]*\"\\([^\"]*\\)\\)" 
 af2-definition-regexp "^[ \t\n\r]*\\(Cst\\|def\\|claim\\|Sort\\)[ \t\n\r]*\\([^ =\\[]*\\)"
)

(defun string-search (sstr str &optional ipos)
  (if str 
      (let 
	  ((pos (if ipos ipos 0)) (len (length sstr)) (end (- (length str) (length sstr))))
	(if (not pos) (setq pos 0))
	(while (and (<= pos end) 
		    (not (string= sstr (substring str pos (+ pos len))))) 
	  (setq pos (+ pos 1)))
	(if (> pos end) nil pos)))) 

(defun proof-remove-comment (str)
  (if str (let 
	      ((astr "")
	       (pos 0)
	       (lpos 0)
	       (spos -1)
               (epos -1)
	       (lvl 0))
	    (while (or spos epos)
	      (setq
	       spos (if (and spos (< spos lpos)) 
			(string-search proof-comment-start str lpos) spos)
	       epos (if (and epos (< epos lpos)) 
			(string-search proof-comment-end str lpos) epos))
	      (message (format "pos: %d, spos: %d, epos: %d, astr: %s ///" 
			       pos (if spos spos -1) (if epos epos -1) astr))
	      (if (and spos (or (not epos) (< spos epos)))
		  (progn
		    (if (= lvl 0) (setq astr 
					(concat astr 
						(substring str pos spos))))
	  (setq lpos (+ spos 1) lvl (+ lvl 1)))
		(if (and epos (> lvl 0)) 
		    (progn
		      (setq lpos (+ epos 1) lvl (- lvl 1))
		      (if (= lvl 0) (setq pos (+ epos 2)))))))
	    (setq astr (concat astr (substring str pos)))
	    (message astr)
	    astr)))

;(defun proof-string-match-ignore-comments (regexp str matchpos)
;  (let 
;      (pos (proof-string-match regexp (proof-remove-comment str)))
;    (if pos (string-match matchpos str) nil)))

(defun af2-find-and-forget (span)
  (let (str ans tmp)
    (while span
      (setq str (proof-remove-comment (span-property span 'cmd)))
      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat ans
			  (format af2-forget-id-command
				  (span-property span 'name)))))

       ((proof-string-match af2-sy-definition-regexp str)
	(message "sy-definition:")
	(message tmp)
	(setq ans 
	      (concat ans (format af2-forget-id-command 
				  (concat "$" (match-string 4 str))))))

       ((proof-string-match af2-definition-regexp str)
	(message "definition:")
	(message tmp)
	(setq ans (concat ans (format af2-forget-id-command 
				      (match-string 2 str))))))


      (setq span (next-span span 'type)))

      (or ans proof-no-command)))

;;--------------------------------------------------------------------------;;
;;
;;    Deleting symbols
;;
;;--------------------------------------------------------------------------;;


(defun af2-delete-symbol(symbol)
  "Interactive function : 
ask for a symbol and send a delete command to af2 for it."
  (interactive "ssymbol : ")
  (proof-shell-invisible-command (concat "del " symbol ".\n")))

(defun af2-delete-symbol-around-point()
"Interactive function : 
send a delete command to af2 for the symbol whose name is under the cursor."
  (interactive)
  (let (start end)
    (save-excursion
      (forward-word -1)
      (setq start (point))
      (forward-word 1)
      (setq end (point)))
    (if (char-equal (char-after (- end 1)) ?.)(setq end (- end 1)))
    (af2-delete-symbol (buffer-substring start end))))

;; retract current goal

(defun proof-retract-current-goal ()
  "Retract the current proof, and move point to its start."
  (interactive)
  (proof-maybe-save-point
   (let
      ((span (proof-last-goal-or-goalsave)))
     (if (and span (not (eq (span-property span 'type) 'goalsave))
	      (< (span-end span) (proof-unprocessed-begin)))
	 (progn
	   (goto-char (span-start span))
	   (proof-retract-until-point-interactive)
	   (proof-maybe-follow-locked-end))
       (error "Not proving")))))

(require 'proof-script)

(proof-define-assistant-command-witharg proof-find-string-in-names
  "Search for items containing a given string in their names."
   proof-find-string-in-names-command
   "Find item with name containing"
 (proof-shell-invisible-command arg))

(provide 'af2-fun)