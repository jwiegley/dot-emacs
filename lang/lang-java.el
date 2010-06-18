;;;_ * java-mode

(defun my-java-mode-hook ()
  (c-set-style "ceg")
  (setq c-basic-offset 3)
  (setq indent-tabs-mode nil)
  (setq tab-width 3)
  (column-marker-3 100)
  (set-fill-column 100))

(add-hook 'java-mode-hook 'my-java-mode-hook)

(defun repair ()
  (interactive)
  (goto-char (point-min))
  (re-search-forward "   _o\\([a-zA-Z0-9]+\\)\\.close();")
  (let ((type (match-string 1)))
    (while (re-search-forward "Exception;$" nil t)
      (goto-char (match-end 0))
      (delete-backward-char 1)
      (let (method)
	(save-excursion
	  (re-search-backward " \\([a-zA-Z0-9]+\\)(")
	  (setq method (match-string 1)))
	(insert ?\n "   {")
	(insert ?\n (format "      return _o%s.%s();" type method))
	(insert ?\n "   }")))))
