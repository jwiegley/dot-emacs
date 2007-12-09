;;; org-message.el - Support for links to nnml messages by Message-ID

;; version 1.1, by John Wiegley <johnw@gnu.org>

(require 'org)

(org-add-link-type "message" 'org-message-open)

(defun org-message-open (message-id)
  "Visit the nnml message with the given Message-ID."
  (start-process (concat "open message:" message-id) nil
		 "open" (concat "message:" message-id)))

(defun org-insert-message-link ()
  (interactive)
  (let ((subject (do-applescript "tell application \"Mail\"
	set theMessages to selection
	subject of beginning of theMessages
end tell"))
	(message-id (do-applescript "tell application \"Mail\"
	set theMessages to selection
	message id of beginning of theMessages
end tell")))
    (insert (org-make-link-string
	     (concat "message://"
		     (substring message-id 1 (1- (length message-id))))
	     (substring subject 1 (1- (length subject)))))))

(provide 'org-message)

;;; org-message.el ends here
