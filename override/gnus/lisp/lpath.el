;; Shut up.

(defun maybe-fbind (args)
  (while args
    (or (fboundp (car args))
	(defalias (car args) 'ignore))
    (setq args (cdr args))))

(defun maybe-bind (args)
  (mapcar (lambda (var) (unless (boundp var) (set var nil))) args))

(unless (featurep 'xemacs)
  (maybe-fbind '(pgg-display-output-buffer url-generic-parse-url))
  (maybe-bind '(help-xref-stack-item url-version))

  (when (<= emacs-major-version 23)
    (maybe-bind '(mail-encode-mml)))

  (when (<= emacs-major-version 22)
    (defun ecomplete-add-item (type key text))
    (defun ecomplete-save nil)
    (defun hashcash-wait-async (&optional buffer))
    (defun mail-add-payment (&optional arg async))
    (defun mail-add-payment-async (&optional arg))
    (defun netrc-get (alist type))
    (defun netrc-machine (list machine &optional port defaultport))
    (defun netrc-machine-user-or-password (mode authinfo-file-or-list machines
						ports defaults))
    (defun netrc-parse (file))
    (defun shr-put-image (data alt &optional flags))
    (maybe-fbind
     '(Info-index
       Info-index-next Info-menu bbdb-complete-name bookmark-default-handler
       bookmark-get-bookmark-record bookmark-make-record-default
       bookmark-prop-get completion-at-point display-time-event-handler
       epg-check-configuration find-coding-system frame-device gnutls-negotiate
       libxml-parse-html-region recenter-top-bottom rmail-swap-buffers-maybe
       shr-insert-document w3m-detect-meta-charset w3m-region))
    (maybe-bind
     '(epa-file-encrypt-to w3m-link-map))))

(when (featurep 'xemacs)
  (defun canlock-insert-header (&optional id-for-key id-for-lock password))
  (defun ecomplete-add-item (type key text))
  (defun ecomplete-save nil)
  (defun hashcash-wait-async (&optional buffer))
  (defun mail-add-payment (&optional arg async))
  (defun mail-add-payment-async (&optional arg))
  (defun netrc-get (alist type))
  (defun netrc-machine (list machine &optional port defaultport))
  (defun netrc-machine-user-or-password (mode authinfo-file-or-list machines
					      ports defaults))
  (defun netrc-parse (file))
  (defun split-line (&optional arg))
  (defun shr-put-image (data alt &optional flags))
  (eval-after-load "rmail"
    '(defun rmail-toggle-header (&optional arg)))
  (maybe-fbind
   '(beginning-of-visual-line
     bookmark-default-handler bookmark-get-bookmark-record
     bookmark-make-record-default bookmark-prop-get clear-string codepage-setup
     coding-system-from-name completion-at-point cp-supported-codepages
     create-image debbugs-gnu delete-overlay detect-coding-string
     display-time-event-handler epg-check-configuration event-click-count
     event-end event-start find-coding-systems-for-charsets
     find-coding-systems-region find-coding-systems-string find-image
     float-time gnutls-negotiate font-lock-ensure font-lock-flush help-buffer
     ido-completing-read image-size image-type-available-p insert-image
     jka-compr-get-compression-info jka-compr-info-uncompress-args
     jka-compr-info-uncompress-message jka-compr-info-uncompress-program
     jka-compr-installed-p jka-compr-make-temp-name libxml-parse-html-region
     mail-abbrevs-setup make-mode-line-mouse-map make-network-process make-term
     mouse-minibuffer-check mouse-movement-p mouse-scroll-subr overlay-lists
     pgg-display-output-buffer posn-point posn-window process-type put-image
     read-char-choice read-event recenter-top-bottom
     rmail-msg-restore-non-pruned-header rmail-swap-buffers-maybe
     select-safe-coding-system set-network-process-option shr-insert-document
     sort-coding-systems spam-initialize term-char-mode term-mode track-mouse
     ucs-to-char url-generic-parse-url url-insert-file-contents
     vcard-pretty-print w3m-detect-meta-charset w3m-region
     window-edges network-interface-list))
  (maybe-bind
   '(adaptive-fill-first-line-regexp
     buffer-display-table buffer-save-without-query completion-styles
     completion-styles-alist cursor-in-non-selected-windows
     default-enable-multibyte-characters default-file-name-coding-system
     epa-file-encrypt-to eudc-protocol filladapt-mode
     gnus-agent-expire-current-dirs help-xref-stack-item idna-program
     installation-directory iswitchb-mode iswitchb-temp-buflist line-spacing
     mail-encode-mml mark-active mouse-selection-click-count
     mouse-selection-click-count-buffer ps-print-color-p rmail-default-file
     rmail-default-rmail-file rmail-insert-mime-forwarded-message-function
     show-trailing-whitespace smtpmail-default-smtp-server
     temporary-file-directory tool-bar-mode transient-mark-mode url-version
     w3m-link-map))

  (when (or (and (= emacs-major-version 21) (= emacs-minor-version 4))
	    (featurep 'sxemacs))
    (maybe-fbind
     '(current-idle-time
       custom-autoload decode-char display-graphic-p display-images-p
       display-visual-class get-display-table help-function-arglist
       make-temp-file next-single-char-property-change put-display-table
       select-frame-set-input-focus set-buffer-multibyte set-char-table-range
       string-as-multibyte timer-set-function unicode-precedence-list
       unicode-to-char))
    (maybe-bind
     '(header-line-format
       scroll-margin timer-list)))

  (unless (featurep 'mule)
    (maybe-fbind
     '(ccl-execute-on-string
       char-charset charsetp coding-system-get find-charset-region
       get-charset-property pgg-display-output-buffer unicode-precedence-list))
    (maybe-bind
     '(current-language-environment
       language-info-alist)))

  (unless (featurep 'file-coding)
    (maybe-fbind
     '(coding-system-aliasee
       coding-system-base coding-system-change-eol-conversion coding-system-list
       coding-system-p decode-coding-region decode-coding-string
       detect-coding-region encode-coding-region encode-coding-string
       find-coding-system))
    (maybe-bind
     '(buffer-file-coding-system
       coding-system-for-read coding-system-for-write
       enable-multibyte-characters file-name-coding-system))))

(provide 'lpath)
