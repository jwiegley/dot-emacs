;;; org-nnml.el - Support for links to nnml messages by Message-ID

;; version 1.1, by John Wiegley <johnw@gnu.org>

(require 'org)

(eval-when-compile
  (require 'nnml)
  (require 'gnus-sum))

(org-add-link-type "nnml" 'org-nnml-open)

(add-hook 'org-store-link-functions 'org-nnml-store-link)

(defun org-nnml-open (message-id)
  "Visit the nnml message with the given Message-ID."
  (let ((info (nnml-find-group-number message-id "nnml")))
    (gnus-summary-read-group (concat "nnml:" (car info)) 100 t)
    (gnus-summary-goto-article (cdr info) nil t)))

(defun org-nnml-store-link ()
  "Store a link to an nnml e-mail message by Message-ID."
  (when (memq major-mode '(gnus-summary-mode gnus-article-mode))
    (and (eq major-mode 'gnus-article-mode) (gnus-article-show-summary))
    (let* ((article (gnus-summary-article-number))
	   (header (gnus-summary-article-header article))
	   (message-id (mail-header-id header)))
      (if (eq (aref message-id 0) ?\<)
	  (setq message-id
		(substring message-id 1 (1- (length message-id)))))
      (org-store-link-props
       :type "nnml"
       :link (cons (concat "nnml:" message-id)
		   (concat "nnml:" message-id))
       :description (mail-header-subject header)))))

(provide 'org-nnml)

;;; org-nnml.el ends here
