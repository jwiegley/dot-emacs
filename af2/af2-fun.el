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
 af2-forget-new-elim-command "edel elim %s.\n"
 af2-forget-new-intro-command "edel intro %s.\n"
 af2-forget-new-rewrite-command "edel rewrite %s.\n"
 af2-forget-close-def-command "edel closed %s.\n"
 af2-comments-regexp "[ \n\t\r]*\\((\\*\\([^*]\\|\\(\\*[^)]\\)\\)*\\*)[ \n\t\r]*\\)*"
 af2-ident-regexp "\\(\\([^ \n\t\r=\\[.]\\|\\(\\.[^ \n\t\r]\\)\\)+\\)"
 af2-spaces-regexp "[ \n\t\r]*"
 af2-sy-definition-regexp (concat 
   "\\(Cst\\|def\\)"
   af2-comments-regexp
   "\\(\\(rInfix\\|lInfix\\|Infix\\|Prefix\\|Postfix\\)[^\"]+\"\\([^\"]+\\)\\)") 
 af2-definition-regexp (concat
   "\\(Cst\\|def\\|claim\\|Sort\\)"
   af2-comments-regexp
   af2-ident-regexp)
 af2-new-elim-regexp (concat
   "new_elim\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)*[ \n\t\r)]"
   af2-ident-regexp)
 af2-new-intro-regexp (concat
   "new_intro\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)*[ \n\t\r)]"
   af2-ident-regexp)
 af2-new-rewrite-regexp (concat
   "new_rewrite\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)*[ \n\t\r)]"
   af2-ident-regexp)
 af2-close-def-regexp (concat
   "close_def"
   af2-comments-regexp
   "\\(\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)+\\)[. \n\t\r]")
)

(defun af2-find-and-forget (span)
  (let (str ans tmp (lsp -1))
    (while span 
      (setq str (span-property span 'cmd))

      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat (format af2-forget-id-command
				  (span-property span 'name)) ans)))

       ((proof-string-match af2-new-elim-regexp str)
	(setq ans 
	      (concat (format af2-forget-new-elim-command 
				  (match-string 3 str)) ans)))

       ((proof-string-match af2-new-intro-regexp str)
	(setq ans 
	      (concat (format af2-forget-new-intro-command 
				  (match-string 3 str)) ans)))

       ((proof-string-match af2-new-rewrite-regexp str)
	(setq ans 
	      (concat (format af2-forget-new-rewrite-command 
				  (match-string 3 str)) ans)))

       ((proof-string-match af2-close-def-regexp str)
	(setq ans 
	      (concat (format af2-forget-close-def-command 
				  (match-string 4 str)) ans)))

       ((proof-string-match af2-sy-definition-regexp str)
	(setq ans 
	      (concat (format af2-forget-id-command 
				  (concat "$" (match-string 7 str))) ans)))

       ((proof-string-match af2-definition-regexp str)
	(setq ans (concat (format af2-forget-id-command 
				      (match-string 5 str)) ans))))


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
    (if (char-equal (char-after (- end 1)) ?\.)(setq end (- end 1)))
    (af2-delete-symbol (buffer-substring start end))))

;;
;; Doing commands
;;

(defun af2-assert-next-command-interactive ()
  "Process until the end of the next unprocessed command after point.
If inside a comment, just process until the start of the comment."
  (interactive)
  (message "test")
  (if (and (> (point) 1) (char-equal (char-before (point)) ?\.)) (insert "\n"))
  (proof-with-script-buffer
   (proof-maybe-save-point
    (goto-char (proof-queue-or-locked-end))
    (proof-assert-next-command))
   (proof-maybe-follow-locked-end)))

(provide 'af2-fun)

