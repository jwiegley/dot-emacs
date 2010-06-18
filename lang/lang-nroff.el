;;;_ * nroff-mode

(defun update-nroff-timestamp ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^\\.Dd ")
      (let ((stamp (format-time-string "%B %e, %Y")))
	(unless (looking-at stamp)
	  (delete-region (point) (line-end-position))
	  (insert stamp)
	  (let (after-save-hook)
	    (save-buffer)))))))

(add-hook 'nroff-mode-hook
	  (function
	   (lambda ()
	     (add-hook 'after-save-hook 'update-nroff-timestamp nil t))))

