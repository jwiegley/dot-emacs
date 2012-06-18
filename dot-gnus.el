;;;_ , Gnus

(load "gnus-settings")

(require 'gnus)
(require 'starttls)
(require 'nnmairix)
(require 'message)

(gnus-compile)
(gnus-delay-initialize)

(defvar switch-to-gnus-unplugged nil)
(defvar switch-to-gnus-run nil)

(defun switch-to-gnus (&optional arg)
  (interactive "P")
  (let* ((alist '("\\`\\*unsent" "\\`\\*Article"
                  "\\`\\*Summary" "\\`\\*Group"))
         (candidate
          (catch 'found
            (dolist (regexp alist)
              (dolist (buf (buffer-list))
                (if (string-match regexp (buffer-name buf))
                    (throw 'found buf)))))))
    (if (and switch-to-gnus-run candidate)
        (if (featurep 'ido)
            (ido-visit-buffer candidate ido-default-buffer-method)
          (switch-to-buffer candidate))
      (let ((switch-to-gnus-unplugged arg))
        (gnus)
        (gnus-group-list-groups gnus-activate-level)
        (setq switch-to-gnus-run t)))))

(use-package fetchmail-ctl
  :init
  (progn
    (defun maybe-start-fetchmail-and-news ()
      (interactive)
      (when (and (not switch-to-gnus-unplugged)
                 (quickping "imap.gmail.com"))
        (do-applescript "tell application \"Notify\" to run")
        (start-fetchmail)
        (save-window-excursion
          (fetchnews-fetch))))

    (add-hook 'gnus-startup-hook 'maybe-start-fetchmail-and-news)))

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

(defadvice gnus-summary-resend-message-edit (after call-my-mhs-hook activate)
  (my-message-header-setup-hook))

(defun my-gnus-summary-save-parts (&optional arg)
  (interactive "P")
  (let ((directory "~/Downloads"))
    (message "Saving all MIME parts to %s..." directory)
    (gnus-summary-save-parts ".*" directory arg)
    (message "Saving all MIME parts to %s...done" directory)))

(bind-key "X m" 'my-gnus-summary-save-parts gnus-summary-mode-map)

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
     gnus-sum-thread-tree-false-root      ""
     gnus-sum-thread-tree-single-indent   ""
     gnus-sum-thread-tree-root            ""
     gnus-sum-thread-tree-vertical        "|"
     gnus-sum-thread-tree-leaf-with-other "+-> "
     gnus-sum-thread-tree-single-leaf     "\\-> "
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
              (gnus-verbose-backends 5))
          (unwind-protect
              (save-window-excursion
                (when (gnus-alive-p)
                  (with-current-buffer gnus-group-buffer
                    (gnus-group-get-new-news gnus-activate-level))))
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

(provide 'dot-gnus)

;; Local Variables:
;;   mode: emacs-lisp
;;   mode: allout
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; dot-gnus.el ends here
