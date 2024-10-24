;;; org-devonthink.el - Support for links to DEVONthink messages by their UUID

;; version 1.1, by John Wiegley <johnw@gnu.org>

(require 'org)
(require 'org-roam)

(org-add-link-type "x-devonthink-item" 'org-devonthink-open)

(defun org-devonthink-open (record-location)
  "Visit the DEVONthink message with the given Message-ID."
  (browse-url (concat "x-devonthink-item://" record-location)))

(defun org-devonthink-get-link (&optional given-name)
  (interactive)
  (let ((name (or given-name
                  (do-applescript (format "
	tell application \"DEVONthink 3\"
		get name of content record
	end tell"))))
	(location (do-applescript (format "
	tell application \"DEVONthink 3\"
		get uuid of content record
	end tell"))))
    (org-make-link-string
     (concat "x-devonthink-item://" (org-remove-double-quotes location))
     (org-remove-double-quotes name))))

(defun org-devonthink-set-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "URL" (org-devonthink-get-link))
  (org-roam-tag-add '("LINK")))

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

(defun org-devonthink-message-open ()
  "Visit the message with the given MESSAGE-ID.
This will use the command `open' with the message URL."
  (interactive)
  (re-search-backward "\\[\\[message://\\(.+?\\)\\]\\[")
  (do-applescript
   (format "tell application \"DEVONthink 3\"
    set searchResults to search \"%%3C%s%%3E\" within URLs
    open window for record (get beginning of searchResults)
end tell" (shell-quote-argument (match-string 1)))))

(provide 'org-devonthink)

;;; org-devonthink.el ends here
