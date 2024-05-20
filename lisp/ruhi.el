(defun replicate (len str)
  (let (result)
    (dotimes (_i len)
      (setq result (concat result str)))
    result))

(defun ruhi-convert-underscores ()
  (interactive)
  (if (re-search-forward "�+" nil t)
      (let ((len (length (match-string 0))))
        (replace-match (concat "[[fg:purple][​" (replicate len "_​") "]]")))))

(defun ruhi-convert-quotations ()
  (interactive)
  (if (re-search-forward "\\(“.+?”\\)\\([0-9]+\\)" nil t)
      (replace-match (concat "#+begin_quote\n*" (match-string 1)
                             "*[fn:u1r" (match-string 2)
                             "]\n#+end_quote"))))

(defun ruhi-convert-numbered-list ()
  (interactive)
  (if (re-search-forward "^\\([0-9]+\\)\\." nil t)
      (replace-match (concat (match-string 1)
                             ". [@"
                             (match-string 1)
                             "]"))))

(defun ruhi-convert-footnote-definitions ()
  (interactive)
  (if (re-search-forward "^\\([0-9]+\\)\\." nil t)
      (replace-match (concat "[fn:u2r" (match-string 1) "]"))))

(provide 'ruhi)
