;;;###autoload
(defun redo-footnotes ()
  "Redo all footnotes in a buffer, renumbering and redefining them.
This is useful for resuming work on an article, or for renumbering
after lots of editing has occurred.

If a textual footnote references a non-existent definition, the
footnote mark is removed.  If a definition is no longer referenced, it
is also deleted."
  (interactive)
  (save-excursion
    (setq footnote-text-marker-alist nil
	  footnote-pointer-marker-alist nil)

    (let ((markers (make-vector 128 nil))
	  index sublist element)

      (goto-char (point-min))
      (while (re-search-forward "\\[\\([0-9]+\\)\\]" nil t)
	(setq index (string-to-int (match-string 1))
	      sublist (aref markers index))
	(goto-char (match-beginning 0))
	(if (bolp)
	    (goto-char (match-end 0))
	  (delete-region (match-beginning 0) (match-end 0))
	  (setq element (list (point-marker)))
	  (if sublist
	      (nconc sublist element)
	    (aset markers index element))))

      (goto-char (point-min))
      (re-search-forward footnote-section-tag-regexp)
      (while (re-search-forward "^\\[\\([0-9]+\\)\\]\\s-*+" nil t)
	(setq index (string-to-int (match-string 1))
	      sublist (aref markers index))
	(let ((start (match-beginning 0))
	      (beg (point)))
	  (re-search-forward "\\(\n[ \t]*\n\\|\n?\\'\\)")
	  (if sublist
	      (aset markers index
		    (cons (buffer-substring-no-properties
			   beg (match-beginning 0))
			  sublist)))
	  (delete-region start (match-end 0))))

      (setq index 1)
      (dotimes (i (length markers))
	(when (setq sublist (aref markers i))
	  (let ((text (car sublist)) inserted)
	    (when (stringp text)
	      (dolist (loc (cdr sublist))
		(goto-char loc)
		(if inserted
		    (Footnote-insert-numbered-footnote index)
		  (Footnote-add-footnote)
		  (insert text)
		  (setq inserted t)))
	      (setq index (1+ index))))))

      (message "%d footnotes have been redone" (1- index)))))

(defun latexize-footnotes ()
  (interactive)
  (save-excursion
    (setq footnote-text-marker-alist nil
	  footnote-pointer-marker-alist nil)

    (let ((markers (make-vector 128 nil))
	  index sublist element)

      (goto-char (point-min))
      (while (re-search-forward
	      "[^\n]\\[\\([0-9]+\\)\\]" nil t)
	(setq index (string-to-int (match-string 1))
	      sublist (aref markers index))
	(goto-char (1+ (match-beginning 0)))
	(delete-region (1+ (match-beginning 0)) (match-end 0))
	(setq element (list (point-marker)))
	(if sublist
	    (nconc sublist element)
	  (aset markers index element)))

      (goto-char (point-min))
      (re-search-forward "^Footnotes:")
      (while (re-search-forward
	      "^\\[\\([0-9]+\\)\\]\\s-*+" nil t)
	(setq index (string-to-int (match-string 1))
	      sublist (aref markers index))
	(let ((start (match-beginning 0)) (beg (point)))
	  (re-search-forward "\\(\n[ \t]*\n\\|\n?\\'\\)")
	  (if sublist
	      (aset markers index
		    (cons (buffer-substring-no-properties
			   beg (match-beginning 0)) sublist)))
	  (delete-region start (match-end 0))))

      (setq index 1)
      (dotimes (i (length markers))
	(when (setq sublist (aref markers i))
	  (let ((text (car sublist)) inserted)
	    (when (stringp text)
	      (dolist (loc (cdr sublist))
		(goto-char loc)
		(insert "\\footnote{" text "}"))
	      (setq index (1+ index)))))))))
