(defvar org-my-archive-expiry-days 7
  "The number of days after which a completed task should be auto-archived.
This can be 0 for immediate, or a floating point value.")

(defconst org-my-ts-regexp "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
  "Regular expression for fast inactive time stamp matching.")

(defun org-my-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((done-regexp
	   (concat "\\* \\(" (regexp-opt org-done-keywords) "\\) "))
	  (state-regexp
	   (concat "- State \"\\(?:" (regexp-opt org-done-keywords)
		   "\\)\"\\s-*\\[\\([^]\n]+\\)\\]"))
	  (inactive-regexp))
      (while (re-search-forward done-regexp nil t)
	(let ((end (save-excursion
		     (outline-next-heading)
		     (point)))
	      begin)
	  (goto-char (line-beginning-position))
	  (setq begin (point))
	  (if (or (re-search-forward state-regexp end t)
		  (re-search-forward org-my-ts-regexp end t))
	      (let* ((time-string (match-string 1))
		     (when-closed (org-parse-time-string time-string)))
		(if (>= (time-to-number-of-days
			 (time-subtract (current-time)
					(apply #'encode-time when-closed)))
			org-my-archive-expiry-days)
		    (org-archive-subtree)))
	    (goto-char end)))))
    (save-buffer)))

(defalias 'archive-done-tasks 'org-my-archive-done-tasks)

(defun org-get-inactive-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward org-my-ts-regexp begin t)
	   (time-to-seconds (org-time-string-to-time (match-string 0)))))))

(defun org-get-completed-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward "\\(- State \"\\(DONE\\|DEFERRED\\|CANCELLED\\)\"\\s-+\\[\\(.+?\\)\\]\\|CLOSED: \\[\\(.+?\\)\\]\\)" begin t)
	   (time-to-seconds (org-time-string-to-time (or (match-string 3)
							 (match-string 4))))))))

(defun org-my-sort-done-tasks ()
  (interactive)
  (goto-char (point-min))
  (org-sort-entries-or-items nil ?F #'org-get-inactive-time)
  (let (after-save-hook)
    (save-buffer))
  (org-overview))

(defalias 'sort-done-tasks 'org-my-sort-done-tasks)

(defun org-insert-new-element (txt)
  "Given a task subtree as TXT, insert it into the current org-mode buffer."
  (when (org-on-heading-p t)
    (org-back-to-heading t)
    (let* ((spos (org-get-location (current-buffer) org-remember-help))
	   (exitcmd (cdr spos))
	   (spos (car spos))
	   (level (funcall outline-level))
	   (reversed t))
      (if (not spos) (error "No heading selected"))
      (goto-char spos)
      (cond
       ((eq exitcmd 'return)
	(if reversed
	    (outline-next-heading)
	  (org-end-of-subtree)
	  (if (not (bolp))
	      (if (looking-at "[ \t]*\n")
		  (beginning-of-line 2)
		(end-of-line 1)
		(insert "\n"))))
	(org-paste-subtree (org-get-legal-level level 1) txt))
       ((eq exitcmd 'left)
	;; before current
	(org-paste-subtree level txt))
       ((eq exitcmd 'right)
	;; after current
	(org-end-of-subtree t)
	(org-paste-subtree level txt))
       (t (error "This should not happen"))))))

