;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; program extraction.
;;
;; note : program extraction is still experimental
;;--------------------------------------------------------------------------;;

(defun phox-compile-theorem(name)
  "Interactive function : 
ask for the name of a theorem and send a compile command to PhoX for it."
  (interactive "stheorem : ")
  (proof-shell-invisible-command (concat "compile " name ".\n")))

(defun phox-compile-theorem-around-point()
"Interactive function : 
send a compile command to PhoX for the theorem which name is under the cursor."
  (interactive)
  (let (start end)
    (save-excursion
      (forward-word 1)
      (setq start (point))
      (forward-word -1)
      (setq end (point)))
    (phox-compile-theorem (buffer-substring start end))))


(setq
 phox-forget-id-command "del %s.\n"
 phox-forget-new-elim-command "edel elim %s.\n"
 phox-forget-new-intro-command "edel intro %s.\n"
 phox-forget-new-rewrite-command "edel rewrite %s.\n"
 phox-forget-close-def-command "edel closed %s.\n"
; phox-comments-regexp : a sequence of comments and white spaces
 phox-comments-regexp "[ \n\t\r]*\\((\\*\\([^*]\\|\\(\\*[^)]\\)\\)*\\*)[ \n\t\r]*\\)*"
; phox-strict-comments-regexp : a not empty sequence of comments and white spaces
 phox-strict-comments-regexp "\\([ \n\t\r]+\\((\\*\\([^*]\\|\\(\\*[^)]\\)\\)*\\*)[ \n\t\r]*\\)*\\|\\((\\*\\([^*]\\|\\(\\*[^)]\\)\\)*\\*)[ \n\t\r]*\\)+\\)"
 phox-ident-regexp "\\(\\([^() \n\t\r=\\[.]\\|\\(\\.[^() \n\t\r]\\)\\)+\\)"
 phox-spaces-regexp "[ \n\t\r]*"
 phox-sy-definition-regexp (concat 
   "\\(Cst\\|def\\)"
   phox-comments-regexp
   "\\(\\(rInfix\\|lInfix\\|Infix\\|Prefix\\|Postfix\\)[^\"]+\"\\([^\"]+\\)\\)") 
 phox-definition-regexp (concat
   "\\(Cst\\|def\\(_thlist\\)?\\|claim\\|Sort\\)"
   phox-comments-regexp
   phox-ident-regexp)
 phox-new-elim-regexp (concat
   "new_elim\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)*[ \n\t\r)]"
   phox-ident-regexp)
 phox-new-intro-regexp (concat
   "new_intro\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)*[ \n\t\r)]"
   phox-ident-regexp)
 phox-new-rewrite-regexp (concat
   "new_rewrite\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)*[ \n\t\r)]"
   phox-ident-regexp)
 phox-close-def-regexp (concat
   "close_def"
   phox-comments-regexp
   "\\(\\([^.]\\|\\(\\.[^ \n\t\r]\\)\\)+\\)[. \n\t\r]")
)

(defun phox-find-and-forget (span)
  (let (str ans tmp (lsp -1))
    (while span 
      (setq str (span-property span 'cmd))

      (cond

       ((eq (span-property span 'type) 'comment))       

       ((eq (span-property span 'type) 'proof)
	(setq ans (concat (format phox-forget-id-command
				  (span-property span 'name)) ans)))

       ((proof-string-match phox-new-elim-regexp str)
	(setq ans 
	      (concat (format phox-forget-new-elim-command 
				  (match-string 3 str)) ans)))

       ((proof-string-match phox-new-intro-regexp str)
	(setq ans 
	      (concat (format phox-forget-new-intro-command 
				  (match-string 3 str)) ans)))

       ((proof-string-match phox-new-rewrite-regexp str)
	(setq ans 
	      (concat (format phox-forget-new-rewrite-command 
				  (match-string 3 str)) ans)))

       ((proof-string-match phox-close-def-regexp str)
	(setq ans 
	      (concat (format phox-forget-close-def-command 
				  (match-string 4 str)) ans)))

       ((proof-string-match phox-sy-definition-regexp str)
	(setq ans 
	      (concat (format phox-forget-id-command 
				  (concat "$" (match-string 7 str))) ans)))

       ((proof-string-match phox-definition-regexp str)
	(setq ans (concat (format phox-forget-id-command 
				      (match-string 6 str)) ans))))


      (setq lsp (span-start span))
      (setq span (next-span span 'type)))

      (or ans proof-no-command)))

;;--------------------------------------------------------------------------;;
;;
;;    Deleting symbols
;;
;;--------------------------------------------------------------------------;;


(defun phox-delete-symbol(symbol)
  "Interactive function : 
ask for a symbol and send a delete command to PhoX for it."
  (interactive "ssymbol : ")
  (proof-shell-invisible-command (concat "del " symbol ".\n")))

(defun phox-delete-symbol-around-point()
"Interactive function : 
send a delete command to PhoX for the symbol whose name is under the cursor."
  (interactive)
  (let (start end)
    (save-excursion
      (forward-word -1)
      (setq start (point))
      (forward-word 1)
      (setq end (point)))
    (if (char-equal (char-after (- end 1)) ?\.)(setq end (- end 1)))
    (phox-delete-symbol (buffer-substring start end))))

;;
;; Doing commands
;;

(defun phox-assert-next-command-interactive ()
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

(provide 'phox-fun)

