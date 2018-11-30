;;;_ , Gnus

(eval-and-compile
  (require 'cl-lib)
  (require 'use-package)
  (setq use-package-verbose nil)
  (setq use-package-expand-minimally t)
  (load "gnus-settings"))

(eval-when-compile
  (require 'cl)
  (setplist 'string-to-multibyte
            (use-package-plist-delete
             (symbol-plist 'string-to-multibyte) 'byte-obsolete-info)))

(require 'gnus)
(require 'starttls)
(require 'message)
(eval-and-compile
  (require 'gnus-start)
  (require 'gnus-sum)
  (require 'gnus-art)
  (require 'mml))

(gnus-delay-initialize)

(defvar switch-to-gnus-unplugged nil)
(defvar switch-to-gnus-run nil)

(eval-when-compile
  (defvar ido-default-buffer-method)
  (declare-function ido-visit-buffer "ido"))

(defun switch-to-gnus (&optional arg)
  (interactive "P")
  (push-window-configuration)
  (let* ((alist '("\\`\\*unsent" "\\`\\*Summary" "\\`\\*Group"))
         (candidate
          (catch 'found
            (dolist (regexp alist)
              (dolist (buf (buffer-list))
                (if (string-match regexp (buffer-name buf))
                    (throw 'found buf)))))))
    (if (and switch-to-gnus-run candidate)
        (progn
          (if (featurep 'ido)
              (ido-visit-buffer candidate ido-default-buffer-method)
            (switch-to-buffer candidate))
          (if (string-match "Group" (buffer-name candidate))
              (gnus-group-get-new-news)))
      (let ((switch-to-gnus-unplugged arg))
        ;; (gnus)
        (gnus-unplugged)
        (gnus-group-list-groups gnus-activate-level)
        (setq switch-to-gnus-run t)))))

(defun quickping (host)
  (= 0 (call-process "ping" nil nil nil "-c1" "-W50" "-q" host)))

(fset 'retrieve-attached-mail
      [?\C-d ?\C-n ?B ?c ?I ?N ?B ?O ?X return ?q ?\C-p ?B backspace ?\M-g])

(use-package fetchmail-ctl
  :after gnus-group
  :bind (:map gnus-group-mode-map
              ("v b" . switch-to-fetchmail)
              ("v d" . shutdown-fetchmail)
              ("v k" . kick-fetchmail)
              ;; ("v p" . fetchnews-post)
              ))

(use-package gnus-sum
  :bind (:map gnus-summary-mode-map
              ("F" . gnus-summary-wide-reply-with-original)))

(use-package gnus-art
  :bind (:map gnus-article-mode-map
              ("F" . gnus-article-wide-reply-with-original)))

(add-hook 'gnus-group-mode-hook 'gnus-topic-mode)
(add-hook 'gnus-group-mode-hook 'hl-line-mode)

(add-hook 'gnus-summary-mode-hook 'hl-line-mode)

(defun my-message-header-setup-hook ()
  (message-remove-header "From")
  (let ((gcc (message-field-value "Gcc")))
   (when (or (null gcc)
             (string-match "nnfolder\\+archive:" gcc))
     (message-remove-header "Gcc")
     (message-add-header (format "Bcc: %s" user-mail-address))
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

(eval-when-compile
  (defvar gnus-agent-queue-mail))

(defun queue-message-if-not-connected ()
  (set (make-local-variable 'gnus-agent-queue-mail)
       (if (quickping "smtp.gmail.com") t 'always)))

(add-hook 'message-send-hook 'queue-message-if-not-connected)
(add-hook 'message-sent-hook 'gnus-score-followup-thread)

(defun exit-gnus-on-exit ()
  (if (and (fboundp 'gnus-group-exit)
           (gnus-alive-p))
      (with-current-buffer (get-buffer "*Group*")
        (let (gnus-interactive-exit)
          (gnus-group-exit)))))

(add-hook 'kill-emacs-hook 'exit-gnus-on-exit)

(defun switch-in-other-buffer (buf)
  (when buf
    (split-window-vertically)
    (balance-windows)
    (switch-to-buffer-other-window buf)))

(defun my-gnus-trash-article (arg)
  (interactive "P")
  (if (string-match "\\(drafts\\|queue\\|delayed\\)" gnus-newsgroup-name)
      (gnus-summary-delete-article arg)
    (gnus-summary-move-article arg "mail.trash")))

(define-key gnus-summary-mode-map [(meta ?q)] 'gnus-article-fill-long-lines)
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

(defun gnus-user-format-function-X (header)
  (let* ((to (or (cdr (assoc 'To (mail-header-extra header))) ""))
         (cc (or (cdr (assoc 'Cc (mail-header-extra header))) ""))
         )
    (message "to-address: %s" to-address)
    (message "recipients: %s" recipients)
    (if (and recipients to-address (not (member to-address recipients)))
        (propertize "X" 'face 'font-lock-warning-face)
      " ")))

(defvar gnus-count-recipients-threshold 5
  "*Number of recipients to consider as large.")

(defun gnus-user-format-function-r (header)
  "Given a Gnus message header, returns priority mark.
Here are the meanings:

The first column represent my relationship to the To: field.  It can be:

         I didn't appear (and the letter had one recipient)
   :     I didn't appear (and the letter had more than one recipient)
   <     I was the sole recipient
   +     I was among a few recipients
   *     There were many recipients

The second column represents the Cc: field:

         I wasn't mentioned, nor was anyone else
    .    I wasn't mentioned, but one other was
    :    I wasn't mentioned, but others were
    ^    I was the only Cc mentioned
    &    I was among a few Cc recipients
    %    I was among many Cc recipients
    X    This is a mailing list, but it wasn't on the recipients list

These can combine in some ways to tell you at a glance how visible the message
is:

   <.    Someone wrote to me and one other
    &    I was copied along with several other people
   *:    Mail to lots of people in both the To and Cc!"
  (ignore-errors
    (let* ((to (or (cdr (assoc 'To (mail-header-extra header))) ""))
           (cc (or (cdr (assoc 'Cc (mail-header-extra header))) ""))
           (to-len (length (split-string to "\\s-*,\\s-*")))
           (cc-len (length (split-string cc "\\s-*,\\s-*")))
           (msg-recipients (concat to (and to cc ", ") cc))
           (recipients
            (mapcar 'mail-strip-quoted-names
	            (message-tokenize-header msg-recipients)))
           (to-address
            (alist-get 'to-address
                       (gnus-parameters-get-parameter gnus-newsgroup-name)))
           (privatized
            (and recipients to-address (not (member to-address recipients)))))
      (cond ((string-match gnus-ignored-from-addresses to)
             (cond ((= to-len 1)
                    (cond (privatized "<X")
                          ((string= cc "") "< ")
                          ((= cc-len 1) "<.")
                          (t "<:")))
                   ((< to-len gnus-count-recipients-threshold)
                    (cond (privatized "+X")
                          ((string= cc "") "+ ")
                          ((= cc-len 1) "+.")
                          (t "+:")))
                   (t
                    (cond (privatized "*X")
                          ((string= cc "") "* ")
                          ((= cc-len 1) "*.")
                          (t "*:")))))

            ((string-match gnus-ignored-from-addresses cc)
             (cond (privatized " X")
                   ((= cc-len 1)
                    (cond ((= to-len 1) " ^")
                          (t ":^")))
                   ((< cc-len gnus-count-recipients-threshold)
                    (cond ((= to-len 1) " &")
                          (t ":&")))
                   (t
                    (cond ((= to-len 1) " %")
                          (t ":%")))))
            (t "  ")))))

(use-package message-x)

(use-package gnus-dired
  :commands gnus-dired-mode
  :init
  (add-hook 'dired-mode-hook 'gnus-dired-mode))

(use-package my-gnus-score
  :commands (my-gnus-score-groups my-gnus-score-followup)
  :init
  (defun gnus-group-get-all-new-news (&optional arg)
    (interactive "P")
    (gnus-group-get-new-news 5)
    (gnus-group-list-groups (or arg 4))
    (my-gnus-score-groups)
    (gnus-group-list-groups (or arg 3))
    (gnus-group-save-newsrc t))

  (define-key gnus-group-mode-map [?v ?g] 'gnus-group-get-all-new-news))

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

    ;; (gnus-demon-add-handler 'gnus-demon-scan-news-2 5 2)

    (defun save-gnus-newsrc ()
      (if (and (fboundp 'gnus-group-exit)
               (gnus-alive-p))
          (with-current-buffer (get-buffer "*Group*")
            (gnus-save-newsrc-file))))

    (gnus-demon-add-handler 'save-gnus-newsrc nil 1)
    (gnus-demon-add-handler 'gnus-demon-close-connections nil 3)))

(defun activate-gnus ()
  (unless (get-buffer "*Group*") (gnus)))

(use-package epa
  :defer t
  :config
  (defun epa--key-widget-value-create (widget)
    (let* ((key (widget-get widget :value))
           (primary-sub-key (car (last (epg-key-sub-key-list key) 3)))
           (primary-user-id (car (epg-key-user-id-list key))))
      (insert (format "%c "
                      (if (epg-sub-key-validity primary-sub-key)
                          (car (rassq (epg-sub-key-validity primary-sub-key)
                                      epg-key-validity-alist))
                        ? ))
              (epg-sub-key-id primary-sub-key)
              " "
              (if primary-user-id
                  (if (stringp (epg-user-id-string primary-user-id))
                      (epg-user-id-string primary-user-id)
                    (epg-decode-dn (epg-user-id-string primary-user-id)))
                "")))))

(use-package nnir
  :init
  (defun gnus-goto-article (message-id)
    (activate-gnus)
    (gnus-summary-read-group "INBOX" 15 t)
    (let ((nnir-imap-default-search-key "imap")
          (nnir-ignored-newsgroups
           (concat "\\(\\(list\\.wg21\\|archive\\)\\.\\|"
                   "mail\\.\\(spam\\|save\\|trash\\|sent\\)\\)")))
      (gnus-summary-refer-article message-id)))

  (defvar gnus-query-history nil)

  (defun gnus-query (query &optional arg)
    (interactive
     (list (read-string (format "IMAP Query %s: "
                                (if current-prefix-arg "All" "Mail"))
                        (format-time-string "SENTSINCE %d-%b-%Y "
                                            (time-subtract (current-time)
                                                           (days-to-time 90)))
                        'gnus-query-history)
           current-prefix-arg))
    (activate-gnus)
    (let ((nnir-imap-default-search-key "imap"))
      (gnus-group-make-nnir-group
       nil (list (cons 'nnir-query-spec
                       (list (cons 'query query)
                             (cons 'criteria "")))
                 (cons 'nnir-group-spec
                       (list (list "nnimap:Local")))))))

  (define-key global-map [(alt meta ?f)] 'gnus-query))

(use-package gnus-harvest
  :load-path "lisp/gnus-harvest"
  :commands gnus-harvest-install
  :demand t
  :config
  (if (featurep 'message-x)
      (gnus-harvest-install 'message-x)
    (gnus-harvest-install)))

(use-package gnus-alias
  :commands (gnus-alias-determine-identity
             gnus-alias-message-x-completion
             gnus-alias-select-identity
             gnus-alias-use-identity)
  :bind (:map  message-mode-map
               ("C-c C-f C-p" . gnus-alias-select-identity))
  :preface
  (defsubst match-in-strings (re strs)
    (cl-some (apply-partially #'string-match re) strs))

  (defun my-gnus-alias-determine-identity ()
    (let ((addrs
           (ignore-errors
             (with-current-buffer (gnus-copy-article-buffer)
               (apply #'nconc
                      (mapcar
                       #'(lambda (x)
                           (split-string (or (gnus-fetch-field x) "") ","))
                       '("To" "Cc" "From" "Reply-To")))))))
      (cond
       ((or (match-in-strings "johnw@gnu\\.org" addrs)
            (match-in-strings "emacs-.*@gnu" addrs)
            (string-match "\\(gnu\\|emacs\\)" gnus-newsgroup-name))
        (gnus-alias-use-identity "Gnu"))
       ((or (match-in-strings "jwiegley@gmail.com" addrs)
            (match-in-strings "@baesystems\\.com" addrs)
            (string-match "\\(brass\\|safe\\|riscv\\)" gnus-newsgroup-name))
        (gnus-alias-use-identity "Gmail"))
       ((or (match-in-strings "johnw@newartisans\\.com" addrs)
            (string-match "\\(haskell\\|coq\\|agda\\|idris\\|acl2\\)"
                          gnus-newsgroup-name))
        (gnus-alias-use-identity "NewArtisans"))
       ((match-in-strings "john\\.wiegley@baesystems\\.com" addrs)
        (gnus-alias-use-identity "BAE"))
       (t
        (gnus-alias-determine-identity)))))
  :init
  (when (featurep 'message-x)
    (add-hook 'message-x-after-completion-functions
              'gnus-alias-message-x-completion))

  (add-hook 'message-setup-hook #'my-gnus-alias-determine-identity))

(use-package gnus-recent
  :after gnus
  :bind (("M-s a" . gnus-recent-goto-ivy)
         :map gnus-summary-mode-map
         ("l" . gnus-recent-goto-previous)
         :map gnus-group-mode-map
         ("C-c L" . gnus-recent-goto-previous)))

(eval-when-compile
  (defvar gnus-balloon-face-0)
  (defvar gnus-balloon-face-1))

(use-package rs-gnus-summary
  :config
  (defalias 'gnus-user-format-function-size
    'rs-gnus-summary-line-message-size)

  (setq gnus-balloon-face-0 'rs-gnus-balloon-0)
  (setq gnus-balloon-face-1 'rs-gnus-balloon-1))

(use-package supercite
  :commands sc-cite-original
  :init
  (add-hook 'mail-citation-hook 'sc-cite-original)

  (defun sc-remove-existing-signature ()
    (save-excursion
      (goto-char (region-beginning))
      (when (re-search-forward message-signature-separator (region-end) t)
        (delete-region (match-beginning 0) (region-end)))))

  (add-hook 'mail-citation-hook 'sc-remove-existing-signature)

  (defun sc-remove-if-not-mailing-list ()
    (unless (assoc "list-id" sc-mail-info)
      (setq attribution sc-default-attribution
            citation (concat sc-citation-delimiter
                             sc-citation-separator))))

  (add-hook 'sc-attribs-postselect-hook 'sc-remove-if-not-mailing-list)

  :config
  (defun sc-fill-if-different (&optional prefix)
    "Fill the region bounded by `sc-fill-begin' and point.
Only fill if optional PREFIX is different than
`sc-fill-line-prefix'.  If `sc-auto-fill-region-p' is nil, do not
fill region.  If PREFIX is not supplied, initialize fill
variables.  This is useful for a regi `begin' frame-entry."
    (if (not prefix)
        (setq sc-fill-line-prefix ""
              sc-fill-begin (line-beginning-position))
      (if (and sc-auto-fill-region-p
               (not (string= prefix sc-fill-line-prefix)))
          (let ((fill-prefix sc-fill-line-prefix))
            (unless (or (string= fill-prefix "")
                        (save-excursion
                          (goto-char sc-fill-begin)
                          (or (looking-at ">+  +")
                              (< (length
                                  (buffer-substring (point)
                                                    (line-end-position)))
                                 65))))
              (fill-region sc-fill-begin (line-beginning-position)))
            (setq sc-fill-line-prefix prefix
                  sc-fill-begin (line-beginning-position)))))
    nil))

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
          (set-buffer-modified-p nil)
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

(use-package mml
  :defer t
  :preface
  (defvar mml-signing-attachment nil)
  (defun mml-sign-attached-file (file &optional type description disposition)
    (unless (or mml-signing-attachment
                (null current-prefix-arg))
      (let ((signature
             (expand-file-name (concat (file-name-nondirectory file) ".sig")
                               temporary-file-directory))
            (mml-signing-attachment t))
        (message "Signing %s..." file)
        (if t
            (call-process epg-gpg-program file nil nil
                          "--output" signature "--detach-sign" file)
          (with-temp-file signature
            (setq buffer-file-coding-system 'raw-text-unix)
            (call-process epg-gpg-program file t nil "--detach-sign")))
        (message "Signing %s...done" file)
        (mml-attach-file signature))))
  :config
  (advice-add 'mml-attach-file :after #'mml-sign-attached-file))

;; Local Variables:
;;   mode: emacs-lisp
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; dot-gnus.el ends here
