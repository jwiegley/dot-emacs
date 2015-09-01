;;; org-debbugs.el - Support for links to debbugs messages by their UUID

;; version 1.1, by John Wiegley <johnw@gnu.org>

(require 'org)

(org-add-link-type "x-debbugs-gnu" 'org-debbugs-open)

(defun org-debbugs-open (record-location)
  "Visit the debbugs-gnu bug with the given id."
  (message "(gnus-read-ephemeral-emacs-bug-group %d)" (string-to-number record-location))
  (gnus-read-ephemeral-emacs-bug-group (string-to-number record-location)))

(defun org-get-debbugs-link (&optional given-name)
  (interactive)
  (let* ((status (debbugs-gnu-current-status))
         (id (cdr (assq 'id status)))
         (subject (cdr (assq 'subject status))))
    (cons (format "x-debbugs-gnu:%d" id)
          (or given-name subject))))

(defun org-insert-debbugs-link ()
  (interactive)
  (let (name)
    (when (region-active-p)
      (setq name (buffer-substring-no-properties (region-beginning)
                                                 (region-end)))
      (delete-region (region-beginning) (region-end)))
    (let ((link-data  (org-get-debbugs-link name)))
      (insert (org-make-link-string (car link-data) (cdr link-data))))))

(defun org-debbugs-store-link ()
  "Store a link to an debbugs-gnu bug by its id."
  (let ((link-data (org-get-debbugs-link)))
    (org-store-link-props
     :type "x-debbugs-gnu"
     :link (cons (car link-data) (car link-data))
     :description (cdr link-data))))

(provide 'org-debbugs)

;;; org-debbugs.el ends here
