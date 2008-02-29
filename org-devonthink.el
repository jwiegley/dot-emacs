;;; org-devonthink.el - Support for links to dtp messages by Message-ID

;; version 1.1, by John Wiegley <johnw@gnu.org>

(require 'org)

(org-add-link-type "dtp" 'org-dtp-open)

;(add-hook 'org-store-link-functions 'org-dtp-store-link)

(defun org-dtp-open (record-location)
  "Visit the dtp message with the given Message-ID."
  (do-applescript (format "
	tell application \"DEVONthink Pro\"
		activate
		open window for record (get record at \"%s\")
	end tell" (replace-regexp-in-string "%20" " " record-location))))

(defun org-insert-dtp-link ()
  (interactive)
  (let ((name (read (do-applescript (format "
	tell application \"DEVONthink Pro\"
		get name of content record
	end tell"))))
	(location (read (do-applescript (format "
	tell application \"DEVONthink Pro\"
		get location of content record
	end tell")))))
    (insert (org-make-link-string
	     (concat "dtp://" (concat location name)) name))))

(defun org-dtp-store-link ()
  "Store a link to an dtp e-mail message by Message-ID."
  (let ((link-name
	 (with-temp-buffer
	   (clipboard-yank)
	   (buffer-string))))
    (org-store-link-props
     :type "dtp"
     :link (cons (concat "dtp:" link-name)
		 (concat "dtp:" link-name))
     :description (file-name-nondirectory link-name))))

(provide 'org-devonthink)

;;; org-devonthink.el ends here
