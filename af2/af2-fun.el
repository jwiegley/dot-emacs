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
 af2-sy-definition-regexp "^[ \t\n\r]*\\(Cst\\|def\\)[ \t\n\r]+\\(\\(rInfix\\|lInfix\\|Infix\\|Prefix\\|Postfix\\)[^\"]+\"\\([^\"]+\\)\\)" 
 af2-definition-regexp "\\(Cst\\|def\\|claim\\|Sort\\)[ \t\n\r]+\\([^ =\\[]+\\)"
)

(defun af2-find-and-forget (span)
  (let (str ans tmp (lsp -1))
    (while span 
      (setq str (proof-remove-comment (span-property span 'cmd)))

      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat (format af2-forget-id-command
				  (span-property span 'name)) ans)))

       ((proof-string-match af2-sy-definition-regexp str)
	(setq ans 
	      (concat (format af2-forget-id-command 
				  (concat "$" (match-string 4 str))) ans)))

       ((proof-string-match af2-definition-regexp str)
	(setq ans (concat (format af2-forget-id-command 
				      (match-string 2 str)) ans))))


      (setq lsp (span-start span))
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

(provide 'af2-fun)