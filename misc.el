(defun wrap-thread-methods ()
  (interactive)
  (save-excursion
    (while (re-search-forward "synchronized\\s-*(\\s-*\\(\\S-+\\)\\s-*)\\s-*\n\\s-*{" nil t)
      (unless (save-excursion
		(save-match-data
		  (goto-char (line-beginning-position))
		  (looking-at "\\s-*//")))
	(let ((var (match-string 1))
	      (beg (copy-marker( match-beginning 0)))
	      (inside (copy-marker (match-end 0)))
	      (paren (copy-marker (1- (match-end 0)))))
	  (goto-char beg)
	  (insert (format "System.out.println( \"%s:%s: synchronizing %s...\" );\n"
			  (file-name-nondirectory (buffer-file-name))
			  (line-number-at-pos) var))
	  (indent-according-to-mode)
	  (goto-char inside)
	  (insert ?\n)
	  (indent-according-to-mode)
	  (insert (format "System.out.println( \"%s:%s: synchronized %s\" );"
			  (file-name-nondirectory (buffer-file-name))
			  (line-number-at-pos) var))
	  (goto-char paren)
	  (forward-sexp)
	  (insert ?\n)
	  (indent-according-to-mode)
	  (insert (format "System.out.println( \"%s:%s: de-synchronized %s\" );"
			  (file-name-nondirectory (buffer-file-name))
			  (line-number-at-pos) var))
	  (goto-char paren)))))
  (while (re-search-forward "\\(\\(\\S-+\\)\\.\\)?\\(wait\\|notify\\|notifyAll\\)();" nil t)
    (unless (save-excursion
	      (save-match-data
		(goto-char (line-beginning-position))
		(looking-at "\\s-*//")))
      (let ((var (match-string 0))
	    (end (copy-marker (match-end 0))))
	(goto-char (match-beginning 0))
	(insert (format "System.out.println( \"%s:%s: calling %s ...\" );\n"
			(file-name-nondirectory (buffer-file-name))
			(line-number-at-pos) var))
	(indent-according-to-mode)
	(goto-char end)
	(insert ?\n)
	(indent-according-to-mode)
	(insert (format "System.out.println( \"%s:%s: called %s\" );\n"
			(file-name-nondirectory (buffer-file-name))
			(line-number-at-pos) var))))))
