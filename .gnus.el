;;; -*- mode: emacs-lisp -*-

;; $Revision: 147 $

;;;_* customizations

;;;_ + variables

(custom-set-variables
 '(nnmail-scan-directory-mail-source-once t)
 '(nnmail-message-id-cache-file "~/Documents/Mail/.nnmail-cache")
 '(nnmail-extra-headers (quote (To)))
 '(nnmail-expiry-wait 30)
 '(nnmail-expiry-target (quote my-gnus-expiry-target))
 '(nnmail-crosspost nil)
 '(nndraft-directory "~/Documents/Mail/" t)
 '(mm-text-html-renderer (quote html2text))
 '(mm-discouraged-alternatives (quote ("application/msword" "text/richtext" "text/html")))
 '(message-setup-hook (quote (gnus-fix-gcc-header)))
 '(message-sent-hook (quote (gnus-score-followup-article gnus-record-recipients)))
 '(message-sendmail-envelope-from (quote header))
 '(message-send-mail-partially-limit nil)
 '(message-mode-hook (quote (flyspell-mode footnote-mode)))
 '(message-mail-alias-type nil)
 '(message-interactive t)
 '(message-directory "~/Documents/Mail/")
 '(message-default-headers "From: John Wiegley <johnw@newartisans.com>
")
 '(mail-user-agent (quote gnus-user-agent))
 '(mail-sources (quote ((file))))
 '(mail-source-report-new-mail-interval 15)
 '(mail-source-delete-old-incoming-confirm nil)
 '(mail-source-delete-incoming t)
 '(gnus-use-trees t)
 '(gnus-use-cache t)
 '(gnus-use-adaptive-scoring (quote (line)))
 '(gnus-uncacheable-groups "^nnml")
 '(gnus-tree-minimize-window nil)
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
 '(gnus-startup-file "~/Documents/Mail/.newsrc")
 '(gnus-started-hook (quote ((lambda nil (run-hooks (quote gnus-after-getting-new-news-hook))))))
 '(gnus-split-methods (quote ((gnus-save-site-lisp-file) (gnus-article-archive-name) (gnus-article-nndoc-name))))
 '(gnus-sort-gathered-threads-function (quote gnus-thread-sort-by-date) t)
 '(gnus-simplify-subject-functions (quote (gnus-simplify-subject-fuzzy)))
 '(gnus-signature-separator (quote ("^-- $" "^-- *$" "^_____+$")))
 '(gnus-select-method (quote (nnml)))
 '(gnus-select-group-hook (quote (gnus-group-set-timestamp)))
 '(gnus-secondary-select-methods nil)
 '(gnus-score-find-score-files-function (quote (gnus-score-find-hierarchical)))
 '(gnus-score-expiry-days 30)
 '(gnus-score-default-duration (quote p))
 '(gnus-save-newsrc-file nil)
 '(gnus-save-killed-list nil)
 '(gnus-read-newsrc-file nil)
 '(gnus-posting-styles (quote (("ceg" ("From" "\"John Wiegley\" <johnw@3dex.com>")))))
 '(gnus-post-method (quote (nngateway "mail2news@nym.alias.net" (nngateway-header-transformation nngateway-mail2news-header-transformation))))
 '(gnus-novice-user nil)
 '(gnus-message-archive-group (quote gnus-determine-archive-group))
 '(gnus-local-domain "newartisans.com")
 '(gnus-large-newsgroup 4000)
 '(gnus-ignored-mime-types (quote ("application/x-pkcs7-signature" "application/ms-tnef" "text/x-vcard")))
 '(gnus-ignored-from-addresses "\\(johnw\\|jwiegley\\)@\\(gnu\\.org\\|\\(forumjobs\\|3dex\\|gmail\\|hotmail\\|newartisans\\)\\.com\\)")
 '(gnus-home-directory "~/Documents")
 '(gnus-group-sort-function (quote gnus-group-sort-by-method))
 '(gnus-group-mode-hook (quote (gnus-topic-mode)))
 '(gnus-group-line-format "%S%p%P%5y%5T: %(%G%)%l
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
 '(gnus-agent-expire-days 14)
 '(gnus-agent-expire-all t)
 '(gnus-after-getting-new-news-hook (quote (gnus-score-groups gnus-group-list-groups gnus-display-time-event-handler gnus-fixup-nnimap-unread-after-getting-new-news gnus-group-save-newsrc)))
 '(eudc-inline-expansion-format (quote ("%s <%s>" name email)))
 '(check-mail-summary-function (quote check-mail-box-summary))
 '(check-mail-boxes (quote ("~/Documents/Mail/incoming/mail\\..*\\.spool")))
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
(load "eudc")

(eval-after-load "message"
  '(load "message-x"))

;;(eval-after-load "gnus-sum"
;;  '(defalias 'gnus-summary-refer-article 'gnus-goto-article))

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

;;;_ + A function to expire old mail into an archive mailbox

(defun my-gnus-expiry-target (group)
  "inbox and sent are archived, the rest is deleted"
  (if (string-match "drafts" group)
      group
    (concat "nnml:" group "."
	    (format-time-string "%Y" (my-gnus-get-article-date)))))

(defun my-gnus-get-article-date ()
  "Extracts the date from the current article and converts it to Emacs time"
  (save-excursion
    (goto-char (point-min))
    (ignore-errors
      (gnus-date-get-time (mail-header-date gnus-current-headers)))))

;;;_ + Record e-mail addresses that I send e-mail to

;; (defun gnus-record-recipients ()
;;   (save-excursion
;;     (save-restriction
;;       (message-narrow-to-headers)
;;       (let ((addrs
;; 	     (append
;; 	      (mail-extract-address-components
;; 	       (concat (mail-fetch-field "to") ","
;; 		       (mail-fetch-field "cc") ","
;; 		       (mail-fetch-field "bcc")) t))))
;; 	(dolist (addr addrs)
;; 	  (if (and addr (cdr addr))
;; 	      (call-process-shell-command "/home/johnw/bin/addmail"
;; 					  nil nil nil (cadr addr))))))))
;; 
;; (defun gnus-goto-article (message-id)
;;   (let ((info (nnml-find-group-number message-id "nnml")))
;;     (gnus-summary-read-group (concat "nnml:" (car info)) 100 t)
;;     (gnus-summary-goto-article (cdr info) nil t)))

;;;_ + Saving articles from gnu.emacs.sources

(defun gnus-save-site-lisp-file (newsgroup)
  (if (equal newsgroup "gnu.emacs.sources")
      (let ((subj (mail-header-subject gnus-current-headers)))
	(if (string-match "[-A-Za-z0-9_]+\\.el" subj)
	    (concat "~/Emacs/misc/" (match-string 0 subj))
	  "~/Emacs/misc"))))

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
			(not (zerop (car entry)))))
	       ;; (string-match "^nnml:list" group)
	       )
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

;;;_ + Smart Gcc: header generation

(defun gnus-fix-gcc-header ()
  "Called to fix any problems with the Gcc header."
  (let ((gcc (gnus-fetch-field "Gcc")))
    (when gcc
      (when (string-match "\\`nndoc:\\(.+?\\)-[0-9]+\\'" gcc)
	(setq gcc (match-string 1 gcc))
	(message-remove-header "Gcc")
	(message-add-header (format "Gcc: %s" gcc)))
      (cond
       ((string-match "\\`nnml:list\\." gcc)
	(let* ((split-addr
		(function
		 (lambda (field)
		   (let ((value (gnus-fetch-field field)))
		     (if value
			 (mapcar 'downcase
				 (split-string
				  (gnus-mail-strip-quoted-names value)
				  "\\s-*,\\s-*")))))))
	       (addrs (append (funcall split-addr "To")
			      (funcall split-addr "Cc")))
	       (to-addr (or (gnus-group-get-parameter gcc 'to-address)
			    (gnus-group-get-parameter gcc 'to-list)))
	       (list-addr (and to-addr (downcase to-addr))))
	  (when (and list-addr (member list-addr addrs))
	    (message-remove-header "Gcc")
	    (message-add-header "FCC: ~/Documents/Mail/listposts"))))))))

;;;_ + Archive groups

(defcustom gnus-archive-groups nil
  "*A list of regexp->group pairs, for compounding archive groups."
  :type '(repeat (cons regexp (string :tag "Group")))
  :group 'nnmail)

(defun gnus-determine-archive-group (group)
  (let* (lookup
	 (group
	  (cond
	   ((string-match "^nntp.*:\\(.*\\)" group)
	    (setq lookup t)
	    (match-string 1 group))
	   ((or (null group)
		(string= group ""))
	    "nnfolder:sent")
	   ((string-match "^\\([^:.]+\\.[^:]+\\)" group)
	    (setq lookup t)
	    (match-string 1 group))
	   (t group)))
	 (table gnus-archive-groups))
    (if lookup
      (while table
	(if (string-match (caar table) group)
	    (setq group (cdar table)
		  table nil)
	  (setq table (cdr table)))))
    group))

;;;_* keybindings

;;;_ + gnus-group-score

(eval-after-load "gnus-group"
  '(define-key gnus-group-score-map [?s] 'gnus-score-groups))

;;;_ + mml

(eval-after-load "mml"
  '(define-key mml-mode-map [(control ?c) (control ?m) ?w]
     'muse-message-markup))

;;; .gnus.el ends here
