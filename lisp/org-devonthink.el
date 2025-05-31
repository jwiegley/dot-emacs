;;; org-devonthink.el - Support for links to DEVONthink messages by their UUID

;; version 1.1, by John Wiegley <johnw@gnu.org>

(require 'org)
(require 'org-roam)

(org-add-link-type "x-devonthink-item" 'org-devonthink-open)

(defsubst org-devonthink-open (record-location)
  "Visit the DEVONthink message with the given Message-ID."
  (browse-url (concat "x-devonthink-item://" record-location)))

(defsubst org-devonthink-message-open (message-id)
  (org-devonthink-open
   (concat "%3C" (url-encode-url (substring message-id 2)) "%3E"))

  ;; (browse-url
  ;;  (concat "https://app.fastmail.com/mail/search:msgid%3A"
  ;;          (url-encode-url (substring message-id 2))
  ;;          "/?u=d30140a0"))

  ;; (require 'gnus-util)
  ;; (if (get-buffer "*Group*")
  ;;     (gnus-goto-article
  ;;      (gnus-string-remove-all-properties (substring message-id 2)))
  ;;   (error "Gnus is not running"))
  )

(when nil
  (org-devonthink-message-open "//ledger/ledger/pull/2419/review/2876546626@github.com"))

(defun org-devonthink-get-link (&optional given-name)
  (interactive)
  (let ((name (or given-name
                  (do-applescript (format "
	tell application \"DEVONthink 3\"
	    try
		get name of content record
	    on error errMsg
		get name of current group
	    end try
	end tell"))))
	(location (do-applescript (format "
	tell application \"DEVONthink 3\"
	    try
		get uuid of content record
	    on error errMsg
		get uuid of current group
	    end try
	end tell"))))
    (org-make-link-string
     (concat "x-devonthink-item://" (org-remove-double-quotes location))
     (org-remove-double-quotes name))))

(defun org-devonthink-set-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property (if (org-entry-get (point-marker) "URL")
                        "URL"
                      "URL2")
                    (org-devonthink-get-link))
  (org-toggle-tag "LINK" 'on))

(defun org-devonthink-insert-link ()
  (interactive)
  (let (name)
    (when (region-active-p)
      (setq name (buffer-substring-no-properties (region-beginning)
                                                 (region-end)))
      (delete-region (region-beginning) (region-end)))
    (insert (org-devonthink-get-link name))))

(defun org-devonthink-store-link ()
  "Store a link to an DEVONthink e-mail message by Message-ID."
  (let ((link-name
	 (with-temp-buffer
	   (clipboard-yank)
	   (buffer-string))))
    (org-store-link-props
     :type "x-devonthink-item"
     :link (cons (concat "x-devonthink-item://" link-name)
		 (concat "x-devonthink-item://" link-name))
     :description (file-name-nondirectory link-name))))

(defun org-devonthink-uuid-to-path (uuid)
  "Visit the message with the given MESSAGE-ID.
This will use the command `open' with the message URL."
  (interactive)
  (when (and uuid
             (string-match "\\`\\(\\[*x-devonthink-item://\\)?\\([-A-Fa-z0-9]+\\)"
                           uuid))
    (let ((base-uuid (match-string 2 uuid)))
      (read (do-applescript
             (format "tell application \"DEVONthink 3\"
    set searchResult to get record with uuid \"%s\"
    path of searchResult
end tell" base-uuid))))))

(provide 'org-devonthink)

;;; org-devonthink.el ends here
