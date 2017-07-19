(defcustom coq-use-Case t
  "Whether to use the Case hack for constructor alternatives."
  :type 'boolean
  :group 'coq-config)

(defcustom coq-use-bullets t
  "Whether to use bullets for scoping constructor alternatives."
  :type 'boolean
  :group 'coq-config)

(defun coq-insert-induction (name pos)
  "Given the name of a variable in scope, insert induction cases for it."
  (interactive "sInduction over term: ")
  (proof-shell-ready-prover)
  (let* ((leader
          (save-excursion
            (beginning-of-line)
            (let ((beg (point)))
              (skip-syntax-forward " ")
              (- (point) beg))))
         (thetype
          (ignore-errors
            (with-temp-buffer
              (insert (proof-shell-invisible-cmd-get-result
                       (concat "Check " name ".")))
              (goto-char (point-max))
              (skip-syntax-backward " ")
              (delete-region (point) (point-max))
              (search-backward " : ")
              (delete-region (point-min) (match-end 0))
              (goto-char (point-min))
              (forward-word 1)
              (buffer-substring (point-min) (point)))))
         (indstr
          (ignore-errors
            (with-temp-buffer
              (insert (proof-shell-invisible-cmd-get-result
                       (concat "Show Match " thetype ".")))
              (goto-char (point-min))
              (let (ctors)
                (while (re-search-forward "| \\(.+?\\) =>" nil t)
                  (push (match-string 1) ctors))
                (goto-char (point-min))
                (re-search-forward "| \\S-+ ")
                (delete-region (point-min) (point))
                (insert "[")
                (while (re-search-forward "=>\\(.\\|\n\\)+?| \\S-+ " nil t)
                  (replace-match "|"))
                (goto-char (point-max))
                (search-backward "=>" nil t)
                (delete-region (point) (point-max))
                (insert "].")
                (mapc #'(lambda (x)
                          (insert ?\n (make-string leader ? ))
                          (when coq-use-bullets
                            (insert "- "))
                          (when coq-use-Case
                            (insert (format "Case \"%s = %s\"." name x))))
                      (nreverse ctors))
                (buffer-string))))))
    indstr))

(provide 'prover)
