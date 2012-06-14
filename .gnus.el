;;;_ , Gnus

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(check-mail-boxes (quote ("~/Messages/incoming/mail\\..*\\.spool")))
 '(check-mail-summary-function (quote check-mail-box-summary))
 '(gnus-activate-level 2)
 '(gnus-after-getting-new-news-hook (quote (gnus-group-list-groups gnus-group-save-newsrc gnus-display-time-event-handler)))
 '(gnus-agent-expire-all t)
 '(gnus-agent-expire-days 14)
 '(gnus-agent-go-online t)
 '(gnus-agent-mark-unread-after-downloaded nil)
 '(gnus-agent-synchronize-flags t)
 '(gnus-alias-default-identity "Gmail")
 '(gnus-alias-identity-alist (quote (("Gmail" "" nil "" nil "" "") ("BoostPro" "" "\"John Wiegley\" <johnw@boostpro.com>" "BoostPro Computing, Inc." nil "" "John Wiegley
BoostPro Computing
http://www.boostpro.com") ("NewArtisans" "" "\"John Wiegley\" <johnw@newartisans.com>" "New Artisans LLC" nil "" ""))))
 '(gnus-alias-identity-rules (quote (("Ledger Mailing List" ("To" "ledger-cli@googlegroups\\.com" current) "Newartisans") ("BoostPro Mail" ("From" "@boostpro\\.com" current) "BoostPro") ("BoostPro Clients" ("To" "@\\(ti\\)\\.com" current) "BoostPro") ("BoostPro Clients (Copied)" ("Cc" "@\\(ti\\)\\.com" current) "BoostPro") ("C++, LLVM, Boost, and Clang Groups" ("Newsgroups" "\\(c\\+\\+\\|clang\\|llvm\\|[Bb]oost\\|[Rr]yppl\\)" current) "BoostPro") ("C++, LLVM, Boost, and Clang Mailing Lists" ("To" "\\(c\\+\\+\\|clang\\|llvm\\|[Bb]oost\\|[Rr]yppl\\)" current) "BoostPro"))))
 '(gnus-alias-override-user-mail-address t)
 '(gnus-alias-unknown-identity-rule (quote error))
 '(gnus-always-read-dribble-file t)
 '(gnus-article-date-lapsed-new-header t)
 '(gnus-article-update-date-headers nil)
 '(gnus-asynchronous t)
 '(gnus-check-new-newsgroups nil)
 '(gnus-completing-read-function (quote gnus-ido-completing-read))
 '(gnus-default-adaptive-score-alist (quote ((gnus-dormant-mark (from 20) (subject 100)) (gnus-ticked-mark (subject 30)) (gnus-read-mark (subject 30)) (gnus-del-mark (subject -150)) (gnus-catchup-mark (subject -150)) (gnus-killed-mark (subject -1000)) (gnus-expirable-mark (from -1000) (subject -1000)))))
 '(gnus-default-article-saver (quote gnus-summary-write-to-file))
 '(gnus-gcc-mark-as-read t)
 '(gnus-generate-tree-function (quote gnus-generate-horizontal-tree))
 '(gnus-group-default-list-level 2)
 '(gnus-group-line-format "%S%p%P%M%5y: %(%B%G%B%)
")
 '(gnus-group-mode-hook (quote (gnus-topic-mode gnus-agent-mode hl-line-mode)))
 '(gnus-group-use-permanent-levels t)
 '(gnus-harvest-sender-alist (quote ((".*@\\(boostpro\\|boost-consulting\\|ti\\)\\.com" . johnw@boostpro\.com) (".*@gnu\\.org" . johnw@gnu\.org))))
 '(gnus-home-directory "~/Messages/Gnus/")
 '(gnus-ignored-from-addresses "\\(johnw\\|jwiegley\\)\\(-[^@]+\\)?@\\(gnu\\.org\\|\\(forumjobs\\|3dex\\|gmail\\|hotmail\\|newartisans\\|boostpro\\)\\.com\\|public\\.gmane\\.org\\)")
 '(gnus-ignored-mime-types (quote ("application/x-pkcs7-signature" "application/ms-tnef" "text/x-vcard")))
 '(gnus-interactive-exit (quote quiet))
 '(gnus-large-newsgroup 4000)
 '(gnus-local-domain "boostpro.com")
 '(gnus-mailing-list-groups "\\`\\(list\\|wg21\\)\\.")
 '(gnus-mark-unpicked-articles-as-read t)
 '(gnus-message-archive-group (quote ((format-time-string "sent.%Y"))))
 '(gnus-message-replyencrypt nil)
 '(gnus-novice-user nil)
 '(gnus-parameters (quote (("list\\." (subscribed . t)) ("list\\.wg21\\.\\(.*\\)" (to-address . "c++std-\\1@accu.org") (to-list . "c++std-\\1@accu.org") (gcc-self . t) (gnus-list-identifiers "\\[c\\+\\+std-.+?\\]") (sieve header :contains "list-id" "<c++std-\\1.accu.org>")) ("\\(johnw\\|INBOX\\)" (total-expire . t) (expiry-target . "mail.archive")) ("johnw" (expiry-wait . immediate)) ("INBOX" (expiry-wait . 14)) ("mail\\." (gnus-use-scoring nil)) ("mail\\.archive" (gnus-summary-line-format "%«%U%R %uS %ur %»%(%*%-14,14f   %4u&size; %1«%B%s%»%)
")) ("list\\.ledger\\.devel" (to-address . "ledger-cli@googlegroups.com") (to-list . "ledger-cli@googlegroups.com") (gcc-self . t) (sieve header :contains "list-id" "<ledger-cli.googlegroups.com>")) ("list\\.bahai\\.tarjuman" (to-address . "TARJUMAN-LIST@listserv.buffalo.edu") (to-list . "TARJUMAN-LIST@listserv.buffalo.edu") (sieve header :contains "sender" "TARJUMAN-LIST@LISTSERV.BUFFALO.EDU")) ("list\\.emacs\\.devel" (to-address . "emacs-devel@gnu.org") (to-list . "emacs-devel@gnu.org") (sieve header :contains "list-id" "<emacs-devel.gnu.org>")) ("list\\.emacs\\.orgmode" (to-address . "emacs-orgmode@gnu.org") (to-list . "emacs-orgmode@gnu.org") (list-identifier . "\\[O\\]") (sieve header :contains "list-id" "<emacs-orgmode.gnu.org>")) ("list\\.boost\\.cppnow" (to-address . "boostcon-plan@googlegroups.com") (to-list . "boostcon-plan@googlegroups.com") (sieve header :contains "list-id" "<boostcon-plan.googlegroups.com>")) ("list\\.boost\\.ryppl" (to-address . "ryppl-dev@googlegroups.com") (to-list . "ryppl-dev@googlegroups.com") (sieve header :contains "list-id" "<ryppl-dev.googlegroups.com>")) ("list\\.boost\\.devel" (to-address . "boost@lists.boost.org") (to-list . "boost@lists.boost.org") (list-identifier . "\\[boost\\]") (sieve header :contains "list-id" "<boost.lists.boost.org>")) ("list\\.boost\\.users" (to-address . "boost-users@lists.boost.org") (to-list . "boost-users@lists.boost.org") (list-identifier . "\\[Boost-users\\]") (sieve header :contains "list-id" "<boost-users.lists.boost.org>")) ("list\\.isocpp\\.\\(proposals\\|discussion\\)" (to-address . "std-\\1@isocpp.org") (to-list . "std-\\1@isocpp.org") (list-identifier . "\\\\[\\\\(lang\\\\|lib\\\\|std\\\\)-\\1\\\\]") (sieve header :contains "list-id" "<std-\\1.isocpp.org>")) ("list\\.clang\\.devel" (to-address . "cfe-dev@cs.uiuc.edu") (to-list . "cfe-dev@cs.uiuc.edu") (list-identifier . "\\[\\(cfe-dev\\|LLVMdev\\)\\]") (sieve header :contains "list-id" "<cfe-dev.cs.uiuc.edu>")) ("list\\.llvm\\.devel" (to-address . "llvmdev@cs.uiuc.edu") (to-list . "llvmdev@cs.uiuc.edu") (list-identifier . "\\[\\(cfe-dev\\|LLVMdev\\)]") (sieve header :contains "list-id" "<llvmdev.cs.uiuc.edu>")))))
 '(gnus-permanently-visible-groups "INBOX")
 '(gnus-read-active-file nil)
 '(gnus-read-newsrc-file nil)
 '(gnus-refer-article-method (quote (current (nnir "nnimap:Local") (nntp "LocalNews" (nntp-address "localhost") (nntp-port-number 9119)) (nntp "Gmane" (nntp-address "news.gmane.org")) (nntp "Eternal September" (nntp-address "news.eternal-september.org") (nntp-authinfo-user "jwiegley")))))
 '(gnus-refer-thread-use-nnir t)
 '(gnus-registry-ignored-groups (quote (("nntp" t) ("^INBOX" t))))
 '(gnus-save-killed-list nil)
 '(gnus-save-newsrc-file nil)
 '(gnus-score-default-duration (quote p))
 '(gnus-score-expiry-days 30)
 '(gnus-score-find-score-files-function (quote (gnus-score-find-hierarchical)))
 '(gnus-select-group-hook (quote (gnus-group-set-timestamp)))
 '(gnus-select-method (quote (nnimap "Local" (nnimap-stream shell) (nnimap-shell-program "/usr/local/libexec/dovecot/imap"))))
 '(gnus-sieve-crosspost nil)
 '(gnus-sieve-file "~/Messages/dovecot.sieve")
 '(gnus-sieve-select-method "nnimap:Local")
 '(gnus-signature-separator (quote ("^-- $" "^-- *$" "^_____+$")))
 '(gnus-simplify-subject-functions (quote (gnus-simplify-subject-fuzzy)))
 '(gnus-sort-gathered-threads-function (quote gnus-thread-sort-by-date) t)
 '(gnus-split-methods (quote ((gnus-save-site-lisp-file) (gnus-article-archive-name) (gnus-article-nndoc-name))))
 '(gnus-started-hook (quote ((lambda nil (run-hooks (quote gnus-after-getting-new-news-hook))))))
 '(gnus-subscribe-newsgroup-method (quote gnus-subscribe-topics))
 '(gnus-sum-thread-tree-single-indent "  ")
 '(gnus-summary-expunge-below -100)
 '(gnus-summary-line-format "%«%U%R %uS %ur %»%(%*%-14,14f   %1«%B%s%»%)
")
 '(gnus-summary-mark-below -100)
 '(gnus-summary-pick-line-format "%U%R %uS %ur %(%*%-14,14f  %B%s%)
")
 '(gnus-summary-save-parts-default-mime ".*")
 '(gnus-suspend-gnus-hook (quote (gnus-group-save-newsrc)))
 '(gnus-thread-expunge-below -1000)
 '(gnus-thread-hide-subtree t)
 '(gnus-thread-sort-functions (quote (gnus-thread-sort-by-most-recent-number gnus-thread-sort-by-total-score)))
 '(gnus-topic-display-empty-topics nil)
 '(gnus-topic-line-format "%i[ %A: %(%{%n%}%) ]%v
")
 '(gnus-treat-date-lapsed (quote head))
 '(gnus-treat-hide-citation-maybe t)
 '(gnus-treat-strip-cr t)
 '(gnus-treat-strip-leading-blank-lines t)
 '(gnus-treat-strip-multiple-blank-lines t)
 '(gnus-treat-strip-trailing-blank-lines t)
 '(gnus-treat-unsplit-urls t)
 '(gnus-tree-minimize-window nil)
 '(gnus-uncacheable-groups "^nnml")
 '(gnus-use-adaptive-scoring (quote (line)))
 '(gnus-use-cache t)
 '(gnus-verbose 4)
 '(mail-envelope-from (quote header))
 '(mail-setup-with-from nil)
 '(mail-source-delete-incoming t)
 '(mail-source-delete-old-incoming-confirm nil)
 '(mail-source-report-new-mail-interval 15)
 '(mail-sources (quote ((file :path "/var/mail/johnw"))))
 '(mail-specify-envelope-from t)
 '(mail-user-agent (quote gnus-user-agent))
 '(message-alternative-emails "\\(johnw?\\|jwiegley\\)@\\(gmail\\|newartisans\\|boostpro\\).com")
 '(message-directory "~/Messages/Gnus/Mail/")
 '(message-fill-column 78)
 '(message-interactive t)
 '(message-mail-alias-type nil)
 '(message-mode-hook (quote (abbrev-mode footnote-mode turn-on-auto-fill turn-on-flyspell turn-on-orgstruct (lambda nil (set-fill-column 78)))))
 '(message-send-mail-function (quote message-send-mail-with-sendmail))
 '(message-send-mail-partially-limit nil)
 '(message-sendmail-envelope-from (quote header))
 '(message-sent-hook (quote (my-gnus-score-followup)))
 '(message-setup-hook (quote (gnus-harvest-set-from message-check-recipients)))
 '(message-signature-separator "^-- *$")
 '(message-subscribed-address-functions (quote (gnus-find-subscribed-addresses)))
 '(message-x-completion-alist (quote (("\\([rR]esent-\\|[rR]eply-\\)?[tT]o:\\|[bB]?[cC][cC]:" . gnus-harvest-find-address) ((if (boundp (quote message-newgroups-header-regexp)) message-newgroups-header-regexp message-newsgroups-header-regexp) . message-expand-group))))
 '(mm-attachment-override-types (quote ("text/x-vcard" "application/pkcs7-mime" "application/x-pkcs7-mime" "application/pkcs7-signature" "application/x-pkcs7-signature" "image/.*")))
 '(mm-decrypt-option (quote always))
 '(mm-discouraged-alternatives (quote ("application/msword" "text/richtext")))
 '(mm-inline-text-html-with-images t)
 '(mm-text-html-renderer (quote w3m))
 '(mm-verify-option (quote always))
 '(mm-w3m-safe-url-regexp nil)
 '(nnir-imap-default-search-key "imap")
 '(nnmail-crosspost nil)
 '(nnmail-expiry-wait 30)
 '(nnmail-extra-headers (quote (To Cc Newsgroups)))
 '(nnmail-scan-directory-mail-source-once t)
 '(sc-citation-leader "")
 '(sc-confirm-always-p nil)
 '(sc-default-attribution "")
 '(sc-preferred-attribution-list nil)
 '(sc-use-only-preference-p t)
 '(send-mail-function (quote sendmail-send-it))
 '(smtpmail-default-smtp-server "smtp.gmail.com")
 '(smtpmail-queue-dir "~/Messages/Gnus/Mail/queue/")
 '(smtpmail-smtp-server "smtp.gmail.com")
 '(smtpmail-smtp-service 587)
 '(smtpmail-smtp-user "jwiegley@gmail.com")
 '(smtpmail-starttls-credentials (quote (("mail.johnwiegley.com" 587 nil nil) ("smtp.gmail.com" 587 nil nil))))
 '(smtpmail-stream-type (quote starttls)))

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(message-cited-text ((((class color)) (:foreground "Blue"))))
 '(message-header-cc ((((class color)) (:bold t :foreground "green2"))))
 '(message-header-name ((((class color)) (:bold nil :foreground "Blue"))))
 '(message-header-other ((((class color)) (:foreground "Firebrick"))))
 '(message-header-subject ((((class color)) (:foreground "black"))))
 '(message-header-xheader ((((class color)) (:foreground "Blue"))))
 '(message-mml ((((class color)) (:foreground "DarkGreen"))))
 '(message-separator ((((class color)) (:foreground "Tan")))))

(require 'gnus)
(require 'gnus-group)
(require 'gnus-sum)
(require 'gnus-art)
(require 'starttls)
(require 'nnmairix)
(require 'message)

(gnus-compile)
(gnus-delay-initialize)

(add-hook 'gnus-group-mode-hook 'gnus-topic-mode)
(add-hook 'gnus-group-mode-hook 'hl-line-mode)

(add-hook 'gnus-summary-mode-hook 'hl-line-mode)

(defun my-message-header-setup-hook ()
  (message-remove-header "From")
  (let ((gcc (message-field-value "Gcc")))
   (when (or (null gcc)
             (string-match "nnfolder\\+archive:" gcc))
     (message-remove-header "Gcc")
     (message-add-header
      (format "Gcc: %s"
              (if (string-match "\\`list\\." (or gnus-newsgroup-name ""))
                  "mail.sent"
                "INBOX"))))))

(add-hook 'message-header-setup-hook 'my-message-header-setup-hook)

(defun queue-message-if-not-connected ()
  (set (make-local-variable 'gnus-agent-queue-mail)
       (if (quickping "smtp.gmail.com") t 'always)))

(add-hook 'message-send-hook 'queue-message-if-not-connected)

(defun kick-postfix-if-needed ()
  (if (and (quickping "imap.gmail.com")
           (= 0 (call-process "/usr/bin/sudo" nil nil nil
                              "/opt/local/libexec/postfix/master" "-t")))
      (start-process "postfix" nil "/usr/bin/sudo"
                     "/opt/local/libexec/postfix/master" "-e" "60")))

(add-hook 'message-sent-hook 'kick-postfix-if-needed)

(defun exit-gnus-on-exit ()
  (if (and (fboundp 'gnus-group-exit)
           (gnus-alive-p))
      (with-current-buffer (get-buffer "*Group*")
        (let (gnus-interactive-exit)
          (gnus-group-exit)))))

(add-hook 'kill-emacs-hook 'exit-gnus-on-exit)

(defun gmail-report-spam ()
  "Report the current or marked mails as spam.
This moves them into the Spam folder."
  (interactive)
  (gnus-summary-move-article nil "mail.spam"))

(defun my-gnus-trash-article (arg)
  (interactive "P")
  (if (string-match "\\(drafts\\|queue\\|delayed\\)" gnus-newsgroup-name)
      (gnus-summary-delete-article arg)
    (gnus-summary-move-article arg "mail.trash")))

(define-key gnus-summary-mode-map [(meta ?q)] 'gnus-article-fill-long-lines)
(define-key gnus-summary-mode-map [?$] 'gmail-report-spam)
(define-key gnus-summary-mode-map [?B delete] 'gnus-summary-delete-article)
(define-key gnus-summary-mode-map [?B backspace] 'my-gnus-trash-article)

(define-key gnus-article-mode-map [(meta ?q)] 'gnus-article-fill-long-lines)

(defface gnus-summary-expirable-face
  '((((class color) (background dark))
     (:foreground "grey50" :italic t :strike-through t))
    (((class color) (background light))
     (:foreground "grey55" :italic t :strike-through t)))
  "Face used to highlight articles marked as expirable."
  :group 'gnus-summary-visual)

(push '((eq mark gnus-expirable-mark) . gnus-summary-expirable-face)
      gnus-summary-highlight)

(if window-system
    (setq
     gnus-sum-thread-tree-false-root      "┌┬▷ "
     gnus-sum-thread-tree-single-indent   ""
     gnus-sum-thread-tree-root            "┌┬▶ "
     gnus-sum-thread-tree-vertical        "│"
     gnus-sum-thread-tree-leaf-with-other "├┬▶ "
     gnus-sum-thread-tree-single-leaf     "╰┬▶ "
     gnus-sum-thread-tree-indent          " "))

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
            (let*
                ((then (dot-gnus-tos
                        (apply 'encode-time (parse-time-string date))))
                 (now (dot-gnus-tos (current-time)))
                 (diff (- now then))
                 (str
                  (cond
                   ((>= diff (* 86400.0 7.0 52.0))
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
                    (format "%3ds" (floor diff)))))
                 (stripped
                  (replace-regexp-in-string "\\.0" "" str)))
              (concat (cond
                       ((= 2 (length stripped)) "  ")
                       ((= 3 (length stripped)) " ")
                       (t ""))
                      stripped))))
    (error "    ")))

(defvar gnus-count-recipients-threshold 5
  "*Number of recipients to consider as large.")

(defun gnus-user-format-function-r (header)
  "Given a Gnus message header, returns priority mark.
If I am the only recipient, return \"!\".
If I am one of a few recipients, but I'm listed in To:, return \"*\".
If I am one of a few recipients, return \"/\".
If I am one of many recipients, return \".\".
Else, return \" \"."
  (let* ((to (or (cdr (assoc 'To (mail-header-extra header))) ""))
         (cc (or (cdr (assoc 'Cc (mail-header-extra header))) "")))
    (cond
     ((string-match gnus-ignored-from-addresses to)
      (let ((len (length (split-string to "\\s-*,\\s-*"))))
        (cond
         ((and (= len 1) (string= cc "")) "▻")
         ((= len 1) "►")
         ((< len gnus-count-recipients-threshold) "»")
         (t "☀"))))
     ((string-match gnus-ignored-from-addresses
                    (concat to ", " cc))
      (if (< (length (split-string (concat to ", " cc) "\\s-*,\\s-*"))
             gnus-count-recipients-threshold)
          "·"
        ":"))
     (t " "))))

(use-package message-x)

(use-package gnus-dired
  :commands gnus-dired-mode
  :init
  (add-hook 'dired-mode-hook 'gnus-dired-mode))

(use-package my-gnus-score
  :init
  (progn
    (defun gnus-group-get-all-new-news ()
      (interactive)
      (gnus-group-get-new-news 5)
      (gnus-group-list-groups 4)
      (my-gnus-score-groups)
      (gnus-group-list-groups 4))

    (define-key gnus-group-mode-map [?v ?g] 'gnus-group-get-all-new-news)))

(use-package gnus-demon
  :init
  (progn
    (defun gnus-demon-scan-news-2 ()
      (when gnus-plugged
        (let ((win (current-window-configuration))
              (gnus-read-active-file nil)
              (gnus-check-new-newsgroups nil)
              (gnus-verbose 2)
              (gnus-verbose-backends 5)
              (level 21))
          (unwind-protect
              (save-window-excursion
                (when (gnus-alive-p)
                  (with-current-buffer gnus-group-buffer
                    (gnus-group-get-new-news level))))
            (set-window-configuration win)))))

    (gnus-demon-add-handler 'gnus-demon-scan-news-2 5 2)

    (defun save-gnus-newsrc ()
      (if (and (fboundp 'gnus-group-exit)
               (gnus-alive-p))
          (with-current-buffer (get-buffer "*Group*")
            (gnus-save-newsrc-file))))

    (gnus-demon-add-handler 'save-gnus-newsrc nil 1)))

(use-package nnir
  :init
  (progn
    (defun activate-gnus ()
      (unless (get-buffer "*Group*") (gnus)))

    (defun gnus-goto-article (message-id)
      (activate-gnus)
      (gnus-summary-read-group "INBOX" 15 t)
      (gnus-summary-refer-article message-id))

    (defvar gnus-query-history nil)

    (defun gnus-query (query &optional arg)
      (interactive
       (list (read-string "Mail Query: "
                          (format-time-string "SINCE %d-%b-%Y "
                                              (time-subtract (current-time)
                                                             (days-to-time 90)))
                          'gnus-query-history)
             current-prefix-arg))
      (activate-gnus)
      (let ((nnir-imap-default-search-key "imap")
            (nnir-ignored-newsgroups
             (if arg
                 nnir-ignored-newsgroups
               "\\(list\\.\\|mail\\.\\(spam\\)\\)")))
        (gnus-group-make-nnir-group
         nil `((query    . ,query)
               (criteria . "")
               (server   . "nnimap:Local")))))

    (define-key global-map [(alt meta ?f)] 'gnus-query)))

(use-package gnus-harvest
  :init
  (if (featurep 'message-x)
      (gnus-harvest-install 'message-x)
    (gnus-harvest-install)))

(use-package gnus-alias
  :commands (gnus-alias-determine-identity
             gnus-alias-message-x-completion
             gnus-alias-select-identity)
  :init
  (progn
    (add-hook 'message-setup-hook 'gnus-alias-determine-identity)

    (if (featurep 'message-x)
        (add-hook 'message-x-after-completion-functions
                  'gnus-alias-message-x-completion))

    (define-key message-mode-map "\C-c\C-f\C-p" 'gnus-alias-select-identity)))

(use-package rs-gnus-summary
  :init
  (progn
    (defalias 'gnus-user-format-function-size
      'rs-gnus-summary-line-message-size)

    (setq gnus-balloon-face-0 'rs-gnus-balloon-0)
    (setq gnus-balloon-face-1 'rs-gnus-balloon-1)))

(use-package supercite
  :commands sc-cite-original
  :init
  (add-hook 'mail-citation-hook 'sc-cite-original)
  :config
  (defun sc-fill-if-different (&optional prefix)
    "Fill the region bounded by `sc-fill-begin' and point.
Only fill if optional PREFIX is different than `sc-fill-line-prefix'.
If `sc-auto-fill-region-p' is nil, do not fill region.  If PREFIX is
not supplied, initialize fill variables.  This is useful for a regi
`begin' frame-entry."
    (if (not prefix)
        (setq sc-fill-line-prefix ""
              sc-fill-begin (line-beginning-position))
      (if (and sc-auto-fill-region-p
               (not (string= prefix sc-fill-line-prefix)))
          (let ((fill-prefix sc-fill-line-prefix))
            (unless (or (string= fill-prefix "")
                        (save-excursion
                          (goto-char sc-fill-begin)
                          (looking-at ">+  +")))
              (fill-region sc-fill-begin (line-beginning-position)))
            (setq sc-fill-line-prefix prefix
                  sc-fill-begin (line-beginning-position)))))
    nil))

(use-package browse-url
  :commands browse-url
  :init
  (progn
    (defun gnus-article-get-urls-region (min max)
      "Return a list of urls found in the region between MIN and MAX"
      (let (url-list)
        (save-excursion
          (save-restriction
            (narrow-to-region min max)
            (goto-char (point-min))
            (while (re-search-forward gnus-button-url-regexp nil t)
              (let ((match-string (match-string-no-properties 0)))
                (if (and (not (equal (substring match-string 0 4) "file"))
                         (not (member match-string url-list)))
                    (setq url-list (cons match-string url-list)))))))
        url-list))

    (defun gnus-article-get-current-urls ()
      "Return a list of the urls found in the current `gnus-article-buffer'"
      (let (url-list)
        (with-current-buffer gnus-article-buffer
          (setq url-list
                (gnus-article-get-urls-region (point-min) (point-max))))
        url-list))

    (defun gnus-article-browse-urls ()
      "Visit a URL from the `gnus-article-buffer' by showing a
buffer with the list of URLs found with the `gnus-button-url-regexp'."
      (interactive)
      (gnus-configure-windows 'article)
      (gnus-summary-select-article nil nil 'pseudo)
      (let ((temp-buffer (generate-new-buffer " *Article URLS*"))
            (urls (gnus-article-get-current-urls))
            (this-window (selected-window))
            (browse-window (get-buffer-window gnus-article-buffer))
            (count 0))
        (save-excursion
          (save-window-excursion
            (with-current-buffer temp-buffer
              (mapc (lambda (string)
                      (insert (format "\t%d: %s\n" count string))
                      (setq count (1+ count))) urls)
              (not-modified)
              (pop-to-buffer temp-buffer)
              (setq count
                    (string-to-number
                     (char-to-string (if (fboundp
                                          'read-char-exclusive)
                                         (read-char-exclusive)
                                       (read-char)))))
              (kill-buffer temp-buffer)))
          (if browse-window
              (progn (select-window browse-window)
                     (browse-url (nth count urls)))))
        (select-window this-window)))

    (define-key gnus-summary-mode-map [(control ?c) (control ?o)]
      'gnus-article-browse-urls)
    (define-key gnus-article-mode-map [(control ?c) (control ?o)]
      'gnus-article-browse-urls)))

;; Local Variables:
;;   mode: emacs-lisp
;;   mode: allout
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; emacs.el ends here
