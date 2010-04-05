(require 'smtpmail)

(eval-when-compile
  (defvar smtpmail-address-buffer)
  (defvar smtpmail-recipient-address-list)
  (defvar user-mail-address))

(defun apple-mail-send-it ()
  (let ((errbuf (if mail-interactive
		    (generate-new-buffer " apple-mail errors")
		  0))
	(tembuf (generate-new-buffer " apple-mail temp"))
	(case-fold-search nil)
	delimline
	(mailbuf (current-buffer))
	(apple-mail-address
         (or (and mail-specify-envelope-from (mail-envelope-from))
             user-mail-address))
	(apple-mail-recipients)
	(apple-mail-recipients))
    (unwind-protect
	(save-excursion
	  (set-buffer tembuf)
	  (erase-buffer)
	  ;; Use the same buffer-file-coding-system as in the mail
	  ;; buffer, otherwise any write-region invocations (e.g., in
	  ;; mail-do-fcc below) will annoy with asking for a suitable
	  ;; encoding.
	  (set-buffer-file-coding-system 'utf-8 nil t)
	  (insert-buffer-substring mailbuf)
	  (goto-char (point-max))
	  ;; require one newline at the end.
	  (or (= (preceding-char) ?\n)
	      (insert ?\n))
	  ;; Change header-delimiter to be what sendmail expects.
	  (mail-sendmail-undelimit-header)
	  (setq delimline (point-marker))
	  ;;	  (sendmail-synch-aliases)
	  (if mail-aliases
	      (expand-mail-aliases (point-min) delimline))
	  (goto-char (point-min))
	  ;; ignore any blank lines in the header
	  (while (and (re-search-forward "\n\n\n*" delimline t)
		      (< (point) delimline))
	    (replace-match "\n"))
	  (let ((case-fold-search t))
	    ;; We used to process Resent-... headers here,
	    ;; but it was not done properly, and the job
	    ;; is done correctly in smtpmail-deduce-address-list.
	    ;; Don't send out a blank subject line
	    (goto-char (point-min))
	    (if (re-search-forward "^Subject:\\([ \t]*\n\\)+\\b" delimline t)
		(replace-match "")
	      ;; This one matches a Subject just before the header delimiter.
	      (if (and (re-search-forward "^Subject:\\([ \t]*\n\\)+" delimline t)
		       (= (match-end 0) delimline))
		  (replace-match "")))
	    ;; Put the "From:" field in unless for some odd reason
	    ;; they put one in themselves.
	    (goto-char (point-min))
	    (if (not (re-search-forward "^From:" delimline t))
		(let* ((login apple-mail-address)
		       (fullname (user-full-name)))
		  (cond ((eq mail-from-style 'angles)
			 (insert "From: " fullname)
			 (let ((fullname-start (+ (point-min) 6))
			       (fullname-end (point-marker)))
			   (goto-char fullname-start)
			   ;; Look for a character that cannot appear unquoted
			   ;; according to RFC 822.
			   (if (re-search-forward "[^- !#-'*+/-9=?A-Z^-~]"
						  fullname-end 1)
			       (progn
				 ;; Quote fullname, escaping specials.
				 (goto-char fullname-start)
				 (insert "\"")
				 (while (re-search-forward "[\"\\]"
							   fullname-end 1)
				   (replace-match "\\\\\\&" t))
				 (insert "\""))))
			 (insert " <" login ">\n"))
			((eq mail-from-style 'parens)
			 (insert "From: " login " (")
			 (let ((fullname-start (point)))
			   (insert fullname)
			   (let ((fullname-end (point-marker)))
			     (goto-char fullname-start)
			     ;; RFC 822 says \ and nonmatching parentheses
			     ;; must be escaped in comments.
			     ;; Escape every instance of ()\ ...
			     (while (re-search-forward "[()\\]" fullname-end 1)
			       (replace-match "\\\\\\&" t))
			     ;; ... then undo escaping of matching parentheses,
			     ;; including matching nested parentheses.
			     (goto-char fullname-start)
			     (while (re-search-forward
				     "\\(\\=\\|[^\\]\\(\\\\\\\\\\)*\\)\\\\(\\(\\([^\\]\\|\\\\\\\\\\)*\\)\\\\)"
				     fullname-end 1)
			       (replace-match "\\1(\\3)" t)
			       (goto-char fullname-start))))
			 (insert ")\n"))
			((null mail-from-style)
			 (insert "From: " login "\n")))))
	    ;; Insert a `Message-Id:' field if there isn't one yet.
	    (goto-char (point-min))
	    (unless (re-search-forward "^Message-Id:" delimline t)
	      (insert "Message-Id: " (message-make-message-id) "\n"))
	    ;; Insert a `Date:' field if there isn't one yet.
	    (goto-char (point-min))
	    (unless (re-search-forward "^Date:" delimline t)
	      (insert "Date: " (message-make-date) "\n"))
	    ;; Possibly add a MIME header for the current coding system
	    (goto-char (point-min))
	    (and (eq mail-send-nonascii 'mime)
		 (not (re-search-forward "^MIME-version:" delimline t))
		 (progn (skip-chars-forward "\0-\177")
			(/= (point) (point-max)))
		 (goto-char delimline)
		 (insert "MIME-version: 1.0\n"
			 "Content-type: text/plain; charset=utf-8"
			 "\nContent-Transfer-Encoding: 8bit\n"))
	    ;; Insert an extra newline if we need it to work around
	    ;; Sun's bug that swallows newlines.
	    (goto-char (1+ delimline))
	    (if (eval mail-mailer-swallows-blank-line)
		(newline))
	    ;; Find and handle any FCC fields.
	    (goto-char (point-min))
	    (if (re-search-forward "^FCC:" delimline t)
		;; Force mail-do-fcc to use the encoding of the mail
		;; buffer to encode outgoing messages on FCC files.
		(let ((coding-system-for-write 'utf-8))
		  (mail-do-fcc delimline)))
	    (if mail-interactive
		(with-current-buffer errbuf
		  (erase-buffer))))
	  ;;
	  ;;
	  ;;
	  (setq smtpmail-address-buffer (generate-new-buffer "*smtp-mail*"))
	  (setq smtpmail-recipient-address-list
		(smtpmail-deduce-address-list tembuf (point-min) delimline))
	  (kill-buffer smtpmail-address-buffer)

	  (smtpmail-do-bcc delimline)
					; Send or queue
	  (if (not smtpmail-queue-mail)
	      (if (not (null smtpmail-recipient-address-list))
		  (if (not (smtpmail-via-smtp
			    smtpmail-recipient-address-list tembuf))
		      (error "Sending failed; SMTP protocol error"))
		(error "Sending failed; no recipients"))
	    (let* ((file-data
		    (expand-file-name
		     (format "%s_%i"
			     (format-time-string "%Y-%m-%d_%H:%M:%S")
			     (setq smtpmail-queue-counter
				   (1+ smtpmail-queue-counter)))
		     smtpmail-queue-dir))
		   (file-data (convert-standard-filename file-data))
		   (file-elisp (concat file-data ".el"))
		   (buffer-data (create-file-buffer file-data))
		   (buffer-elisp (create-file-buffer file-elisp))
		   (buffer-scratch "*queue-mail*"))
	      (unless (file-exists-p smtpmail-queue-dir)
		(make-directory smtpmail-queue-dir t))
	      (with-current-buffer buffer-data
		(erase-buffer)
		(set-buffer-file-coding-system smtpmail-code-conv-from nil t)
		(insert-buffer-substring tembuf)
		(write-file file-data)
		(set-buffer buffer-elisp)
		(erase-buffer)
		(insert (concat
			 "(setq smtpmail-recipient-address-list '"
			 (prin1-to-string smtpmail-recipient-address-list)
			 ")\n"))
		(write-file file-elisp)
		(set-buffer (generate-new-buffer buffer-scratch))
		(insert (concat file-data "\n"))
		(append-to-file (point-min)
				(point-max)
				smtpmail-queue-index)
		)
	      (kill-buffer buffer-scratch)
	      (kill-buffer buffer-data)
	      (kill-buffer buffer-elisp))))
      (kill-buffer tembuf)
      (if (bufferp errbuf)
	  (kill-buffer errbuf)))))

(provide 'am-send)
