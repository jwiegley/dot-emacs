;;; -*- mode: emacs-lisp -*-

;; $Revision: 147 $

;;;_* customizations

;;;_ + variables

(custom-set-variables
 '(smtpmail-starttls-credentials (quote (("mail.johnwiegley.com" 587 nil nil) ("smtp.gmail.com" 587 nil nil))))
 '(smtpmail-smtp-service 587 t)
 '(smtpmail-smtp-server "mail.johnwiegley.com" t)
 '(smtpmail-default-smtp-server "mail.johnwiegley.com")
 '(sendmail-program "/opt/local/bin/msmtp")
 '(send-mail-function (quote sendmail-send-it))
 '(nnmail-scan-directory-mail-source-once t)
 '(nnmail-extra-headers (quote (To)))
 '(nnmail-expiry-wait 30)
 '(nnmail-crosspost nil)
 '(mm-text-html-renderer (quote html2text))
 '(mm-discouraged-alternatives (quote ("application/msword" "text/richtext" "text/html")))
 '(message-x-completion-alist (quote (("\\([rR]esent-\\|[rR]eply-\\)?[tT]o:\\|[bB]?[cC][cC]:" . pick-email-address) ((if (boundp (quote message-newgroups-header-regexp)) message-newgroups-header-regexp message-newsgroups-header-regexp) . message-expand-group))))
 '(message-setup-hook (quote (message-check-recipients (lambda nil (message-remove-header "From")))))
 '(message-sent-hook (quote (gnus-score-followup-article)))
 '(message-sendmail-envelope-from (quote header))
 '(message-send-mail-partially-limit nil)
 '(message-send-mail-function (quote message-send-mail-with-sendmail))
 '(message-mode-hook (quote (footnote-mode auto-fill-mode)))
 '(message-mail-alias-type nil)
 '(message-interactive t)
 '(message-fill-column 78)
 '(message-directory "~/Library/Mail/Gnus/Mail/")
 '(mail-user-agent (quote gnus-user-agent))
 '(mail-specify-envelope-from t)
 '(mail-sources (quote ((file))))
 '(mail-source-report-new-mail-interval 15)
 '(mail-source-delete-old-incoming-confirm nil)
 '(mail-source-delete-incoming t)
 '(mail-setup-with-from nil)
 '(mail-envelope-from (quote header) t)
 '(mail-archive-file-name "~/Library/Mail/sent.txt")
 '(gnus-use-trees t)
 '(gnus-use-cache t)
 '(gnus-use-adaptive-scoring (quote (line)))
 '(gnus-uncacheable-groups "^nnml")
 '(gnus-tree-minimize-window nil)
 '(gnus-treat-wash-html t)
 '(gnus-treat-unsplit-urls t)
 '(gnus-treat-strip-trailing-blank-lines t)
 '(gnus-treat-strip-multiple-blank-lines t)
 '(gnus-treat-strip-leading-blank-lines t)
 '(gnus-treat-strip-cr t)
 '(gnus-treat-hide-citation-maybe t)
 '(gnus-treat-date-lapsed (quote head))
 '(gnus-topic-line-format "%i[ %A: %(%{%n%}%) ]%v
")
 '(gnus-topic-display-empty-topics nil)
 '(gnus-thread-sort-functions (quote (gnus-thread-sort-by-number gnus-thread-sort-by-subject (not gnus-thread-sort-by-date) gnus-thread-sort-by-total-score)))
 '(gnus-thread-hide-subtree nil)
 '(gnus-suspend-gnus-hook (quote (gnus-group-save-newsrc)))
 '(gnus-summary-mark-below -100)
 '(gnus-summary-line-format "%U%R%I%(%ut: %uS %S, %uZ%)
")
 '(gnus-summary-expunge-below -100)
 '(gnus-subscribe-newsgroup-method (quote gnus-subscribe-topics))
 '(gnus-started-hook (quote ((lambda nil (run-hooks (quote gnus-after-getting-new-news-hook))))))
 '(gnus-split-methods (quote ((gnus-save-site-lisp-file) (gnus-article-archive-name) (gnus-article-nndoc-name))))
 '(gnus-sort-gathered-threads-function (quote gnus-thread-sort-by-date) t)
 '(gnus-simplify-subject-functions (quote (gnus-simplify-subject-fuzzy)))
 '(gnus-signature-separator (quote ("^-- $" "^-- *$" "^_____+$")))
 '(gnus-select-method (quote (nnml "")))
 '(gnus-select-group-hook (quote (gnus-group-set-timestamp)))
 '(gnus-select-article-hook (quote (gnus-agent-fetch-selected-article)))
 '(gnus-secondary-select-methods nil)
 '(gnus-score-find-score-files-function (quote (gnus-score-find-hierarchical)))
 '(gnus-score-expiry-days 30)
 '(gnus-score-default-duration (quote p))
 '(gnus-save-newsrc-file nil)
 '(gnus-save-killed-list nil)
 '(gnus-refer-article-method (quote (current (nnregistry) (nnweb "gmane" (nnweb-type gmane)) (nnweb "google" (nnweb-type google)))))
 '(gnus-read-newsrc-file nil)
 '(gnus-posting-styles (quote ((".*"))))
 '(gnus-post-method (quote (nngateway "mail2news@nym.alias.net" (nngateway-header-transformation nngateway-mail2news-header-transformation))))
 '(gnus-novice-user nil)
 '(gnus-message-archive-group "nnimap+VPS:INBOX")
 '(gnus-local-domain "boostpro.com")
 '(gnus-large-newsgroup 4000)
 '(gnus-ignored-mime-types (quote ("application/x-pkcs7-signature" "application/ms-tnef" "text/x-vcard")))
 '(gnus-ignored-from-addresses "\\(johnw\\|jwiegley\\)@\\(gnu\\.org\\|\\(forumjobs\\|3dex\\|gmail\\|hotmail\\|newartisans\\|boostpro\\)\\.com\\)")
 '(gnus-home-directory "~/Library/Mail/Gnus/")
 '(gnus-group-sort-function (quote gnus-group-sort-by-method))
 '(gnus-group-mode-hook (quote (gnus-topic-mode)))
 '(gnus-group-line-format "%S%p%P%5y%5T: %(%G%)
")
 '(gnus-group-default-list-level 4)
 '(gnus-generate-tree-function (quote gnus-generate-horizontal-tree))
 '(gnus-gcc-mark-as-read t)
 '(gnus-extra-headers (quote (To)))
 '(gnus-default-article-saver (quote gnus-summary-write-to-file))
 '(gnus-default-adaptive-score-alist (quote ((gnus-dormant-mark (from 20) (subject 100)) (gnus-ticked-mark (subject 30)) (gnus-read-mark (subject 30)) (gnus-del-mark (subject -150)) (gnus-catchup-mark (subject -150)) (gnus-killed-mark (subject -1000)) (gnus-expirable-mark (from -1000) (subject -1000)))))
 '(gnus-asynchronous t)
 '(gnus-article-date-lapsed-new-header t)
 '(gnus-always-read-dribble-file t)
 '(gnus-agent-synchronize-flags t)
 '(gnus-agent-go-online t)
 '(gnus-agent-expire-days 14)
 '(gnus-agent-expire-all t)
 '(gnus-after-getting-new-news-hook (quote (gnus-score-groups gnus-group-list-groups gnus-display-time-event-handler gnus-group-save-newsrc)))
 '(gnus-activate-level 2)
 '(eudc-inline-expansion-format (quote ("%s <%s>" name email)))
 '(check-mail-summary-function (quote check-mail-box-summary))
 '(check-mail-boxes (quote ("~/Library/Mail/incoming/mail\\..*\\.spool")))
 '(canlock-password "8d2ee9a7e4658c4ff6d863f91a3dd5340b3918ec"))

;;;_ + faces

(custom-set-faces
 '(message-separator ((((class color)) (:foreground "Tan"))))
 '(message-mml ((((class color)) (:foreground "DarkGreen"))))
 '(message-header-xheader ((((class color)) (:foreground "Blue"))))
 '(message-header-subject ((((class color)) (:foreground "black"))))
 '(message-header-other ((((class color)) (:foreground "Firebrick"))))
 '(message-header-name ((((class color)) (:bold nil :foreground "Blue"))))
 '(message-header-cc ((((class color)) (:bold t :foreground "green2"))))
 '(message-cited-text ((((class color)) (:foreground "Blue")))))

;;;_* configuration

(load "gnus")
(load "gnus-agent")
(load "starttls")

(gnus-registry-initialize)

(eval-after-load "message"
  '(load "message-x"))

(defun gnus-goto-article (message-id)
  (gnus-summary-read-group "nnimap+VPS:INBOX" 1 t)
  (gnus-summary-refer-article message-id))

(defun gnus-current-message-id ()
  (with-current-buffer gnus-original-article-buffer
    (nnheader-narrow-to-headers)
    (message-fetch-field "message-id")))

(defun gnus-open-article-in-apple-mail ()
  (interactive)
  (let ((message-id (gnus-current-message-id)))
    (start-process (concat "open message:" message-id) nil
                   "open" (concat "message://<"
                                  (substring message-id 1 -1) ">"))))

(eval-after-load "gnus-sum"
  '(define-key gnus-summary-mode-map [?O ?O] 'gnus-open-article-in-apple-mail))

(defadvice message-goto-from (after insert-boostpro-address activate)
  (if (looking-back ": ")
      (insert "John Wiegley <johnw@boostpro.com>"))
  (goto-char (line-end-position))
  (re-search-backward ": ")
  (goto-char (match-end 0)))

(setq my-smtpmailer-alist 
      '((".*@\\(boostpro.com\\)"
         ("johnw@boostpro.com" . "smtp.gmail.com"))
        (".*@\\(3dex\\|smartceg\\).com"
         ("johnw@3dex.com" . "smtp.gmail.com"))
        (".*@\\(gmail.com\\)"
         ("jwiegley@gmail.com" . "smtp.gmail.com"))
        (".*"
         ("johnw@newartisans.com" . "mail.johnwiegley.com"))))

(defun my-set-smtp-server ()
  (let* ((to-field (cadr (mail-extract-address-components
                          (message-field-value "to"))))
         (from (let ((field (message-field-value "from")))
                 (and field (cadr (mail-extract-address-components field)))))
         (result
          (car (assoc-default (or from to-field)
                              my-smtpmailer-alist
                              'string-match
                              (cons user-mail-address
                                    (if (boundp 'smtpmail-default-smtp-server)
                                        smtpmail-default-smtp-server
                                      ""))))))
    (if from
        (setq smtpmail-mail-address from
              mail-envelope-from from
              smtpmail-smtp-server (cdr result)
              smtpmail-smtp-service 587)
      ;; set mailer address and port
      (setq smtpmail-mail-address (car result)
            mail-envelope-from (car result)
            smtpmail-smtp-server (cdr result)
            smtpmail-smtp-service 587)
      (message-remove-header "From")
      (message-add-header
       (format "From: %s <%s>" user-full-name (car result))))))

(add-hook 'message-send-hook 'my-set-smtp-server)

;;;_ + Determine layout of the summary windows

(gnus-add-configuration
      '(article
	(vertical 1.0
		  (horizontal 0.25
			      (summary 0.75 point)
			      (tree 1.0))
		  (article 1.0))))

;;;_ + Cleanup all Gnus buffers on exit

(defun exit-gnus-on-exit ()
  (if (and (fboundp 'gnus-group-exit)
	   (gnus-alive-p))
      (with-current-buffer (get-buffer "*Group*")
	(let (gnus-interactive-exit)
	  (gnus-group-exit)))))

(add-hook 'kill-emacs-hook 'exit-gnus-on-exit)

;;;_ + Scoring

(defun gnus-score-groups ()
  (interactive)
  (save-excursion
    (let (info newsrc group entry)
      (setq newsrc (cdr gnus-newsrc-alist))
      (while (setq info (pop newsrc))
	(setq group (gnus-info-group info)
	      entry (gnus-gethash group gnus-newsrc-hashtb))
	(when (and
	       (<= (gnus-info-level info) gnus-level-subscribed)
	       (and (car entry)
		    (or (eq (car entry) t)
			(not (zerop (car entry))))))
	  (ignore-errors
	    (gnus-summary-read-group group nil t))
	  (when (and gnus-summary-buffer
		     (buffer-live-p gnus-summary-buffer)
		     (eq (current-buffer) (get-buffer gnus-summary-buffer)))
	    (gnus-summary-exit)))))))

;;;_ + Summary line formats

(defun gnus-user-format-function-Z (header)
  (let ((to (cdr (assq 'To (mail-header-extra header))))
	(newsgroups (cdr (assq 'Newsgroups (mail-header-extra header))))
	(mail-parse-charset gnus-newsgroup-charset)
	(mail-parse-ignored-charsets
	 (save-excursion
	   (set-buffer gnus-summary-buffer)
	   gnus-newsgroup-ignored-charsets)))
    (cond
     ((and to gnus-ignored-from-addresses
	   (string-match gnus-ignored-from-addresses
			 (mail-header-from header)))
      (concat "-> "
	      (or (car (funcall gnus-extract-address-components
				(funcall
				 gnus-decode-encoded-word-function to)))
		  (funcall gnus-decode-encoded-word-function to))))
     ((and newsgroups gnus-ignored-from-addresses
	   (string-match gnus-ignored-from-addresses
			 (mail-header-from header)))
      (concat "=> " newsgroups))
     (t
      (let* ((from (mail-header-from header))
	     (data (condition-case nil
		       (mail-extract-address-components from)
		     (error nil)))
	     (name (car data))
	     (net (car (cdr data))))
	(or name net))))))

(defsubst dot-gnus-tos (time)
  "Convert TIME to a floating point number."
  (+ (* (car time) 65536.0)
     (cadr time)
     (/ (or (car (cdr (cdr time))) 0) 1000000.0)))

(defun gnus-user-format-function-S (header)
  "Return how much time it's been since something was sent."
  (condition-case err
      (let ((date (mail-header-date header)))
	(if (> (length date) 0)
	    (let* ((then (dot-gnus-tos
			  (apply 'encode-time (parse-time-string date))))
		   (now (dot-gnus-tos (current-time)))
		   (diff (- now then)))
	      (cond ((>= diff (* 86400.0 7.0 52.0))
		     (if (>= diff (* 86400.0 7.0 52.0 10.0))
			 (format "%3dY" (floor (/ diff (* 86400.0 7.0 52.0))))
		       (format "%3.1fY" (/ diff (* 86400.0 7.0 52.0)))))
		    ((>= diff (* 86400.0 30.0))
		     (if (>= diff (* 86400.0 30.0 10.0))
			 (format "%3dM" (floor (/ diff (* 86400.0 30.0))))
		       (format "%3.1fM" (/ diff (* 86400.0 30.0)))))
		    ((>= diff (* 86400.0 7.0))
		     (if (>= diff (* 86400.0 7.0 10.0))
			 (format "%3dw" (floor (/ diff (* 86400.0 7.0))))
		       (format "%3.1fw" (/ diff (* 86400.0 7.0)))))
		    ((>= diff 86400.0)
		     (if (>= diff (* 86400.0 10.0))
			 (format "%3dd" (floor (/ diff 86400.0)))
		       (format "%3.1fd" (/ diff 86400.0))))
		    ((>= diff 3600.0)
		     (if (>= diff (* 3600.0 10.0))
			 (format "%3dh" (floor (/ diff 3600.0)))
		       (format "%3.1fh" (/ diff 3600.0))))
		    ((>= diff 60.0)
		     (if (>= diff (* 60.0 10.0))
			 (format "%3dm" (floor (/ diff 60.0)))
		       (format "%3.1fm" (/ diff 60.0))))
		    (t
		     (format "%3ds" (floor diff)))))))
    (error "    ")))

(eval-when-compile
  (defvar thread)
  (defvar gnus-tmp-level))

(defun gnus-user-format-function-t (header)
  (let ((tcount (gnus-summary-number-of-articles-in-thread
		 (and (boundp 'thread) (car thread)) gnus-tmp-level)))
    (if (> tcount 1)
	(number-to-string tcount)
      " ")))

;;;_ + Selecting an e-mail address

(defvar pick-addr-cache nil)

(defun pick-email-address ()
  (interactive)
  (let ((stub (word-at-point))
        (choices
         (or pick-addr-cache
             (setq pick-addr-cache
                   (split-string
                    (shell-command-to-string
                     "contacts -H -S -f '%n <%e>' | grep -v '<>'") "\n" t)))))
    (backward-kill-word 1)
    (insert (ido-completing-read "E-mail address: " choices nil t stub))))

;;;_* keybindings

;;;_ + gnus-group-score

(eval-after-load "gnus-group"
  '(define-key gnus-group-score-map [?s] 'gnus-score-groups))

;;; .gnus.el ends here
