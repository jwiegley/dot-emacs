;;; org-ext-test.el --- Tests for recording imports -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)

(defvar org-ext-recording-queue-directory)
(defvar org-ext-recording-receipt-directory)
(defvar org-ext-recording-inbox-directories)

(let ((source (expand-file-name "org-ext.el"
                                (file-name-directory load-file-name))))
  (with-temp-buffer
    (insert-file-contents source)
    (goto-char (point-min))
    (unless (re-search-forward "^(defun org-ext-recording-note-files\\_>" nil t)
      (error "org-ext-recording-note-files is missing"))
    (goto-char (match-beginning 0))
    (eval (read (current-buffer)) t)
    (goto-char (point-min))
    (when (re-search-forward "^(defun org-ext-reformat-recording\\_>" nil t)
      (goto-char (match-beginning 0))
      (eval (read (current-buffer)) t))
    (dolist (name '(org-ext-recording-file-hash
                    org-ext-recording-receipt-file
                    org-ext-recording-imported-p
                    org-ext-write-recording-receipt
                    org-ext-import-recording-note))
      (goto-char (point-min))
      (when (re-search-forward (format "^(defun %s\\_>" name) nil t)
        (goto-char (match-beginning 0))
        (eval (read (current-buffer)) t)))))

(ert-deftest org-ext-recording-note-files-combines-local-and-legacy-inboxes ()
  (let* ((root (make-temp-file "org-ext-recordings-" t))
         (legacy (expand-file-name "legacy" root))
         (queue (expand-file-name "queue" root))
         (legacy-note (expand-file-name "legacy.m4a.txt" legacy))
         (queued-note (expand-file-name "queued.m4a.txt" queue)))
    (unwind-protect
        (progn
          (make-directory legacy)
          (make-directory queue)
          (write-region "legacy" nil legacy-note nil 'silent)
          (write-region "queued" nil queued-note nil 'silent)
          (write-region "audio" nil (expand-file-name "ignored.m4a" queue) nil 'silent)
          (let ((org-ext-recording-inbox-directories (list queue legacy)))
            (should (equal (org-ext-recording-note-files)
                           (sort (list legacy-note queued-note) #'string-lessp)))))
      (delete-directory root t))))

(ert-deftest org-ext-import-recording-note-is-exactly-once ()
  (let* ((root (make-temp-file "org-ext-recording-import-" t))
         (queue (expand-file-name "queue" root))
         (receipts (expand-file-name ".imported" queue))
         (note (expand-file-name "17-28-31.m4a.txt" queue))
         (inbox (expand-file-name "inbox.org" root))
         (hash nil)
         (hook-runs 0)
         (org-ext-recording-queue-directory queue)
         (org-ext-recording-receipt-directory receipts))
    (unwind-protect
        (progn
          (make-directory queue)
          (write-region "Buy milk" nil note nil 'silent)
          (setq hash
                (with-temp-buffer
                  (insert-file-contents-literally note)
                  (secure-hash 'sha256 (current-buffer))))
          (let ((buffer (find-file-noselect inbox)))
            (unwind-protect
                (with-current-buffer buffer
                  (org-mode)
                  (setq-local org-capture-before-finalize-hook
                              (list (lambda () (setq hook-runs (1+ hook-runs)))))
                  (cl-letf (((symbol-function 'org-ext-move-recording-audio) #'ignore))
                    (org-ext-import-recording-note note))
                  (should (equal (buffer-string)
                                 (format "** TODO Buy milk\n:PROPERTIES:\n:RECORDING_TRANSCRIPT_SHA256: %s\n:END:\n" hash)))
                  (should-not (buffer-modified-p)))
              (kill-buffer buffer)))
          (should (= hook-runs 1))
          (should-not (file-exists-p note))
          (should (equal (with-temp-buffer
                           (insert-file-contents
                            (expand-file-name "17-28-31.m4a.txt.sha256" receipts))
                           (buffer-string))
                         (concat hash "\n")))

          ;; Simulate a crash after inbox save but before queue cleanup. The
          ;; persisted hash suppresses a duplicate entry on retry.
          (write-region "Buy milk" nil note nil 'silent)
          (setq hash (secure-hash 'sha256 note))
          (let ((buffer (find-file-noselect inbox)))
            (unwind-protect
                (with-current-buffer buffer
                  (cl-letf (((symbol-function 'org-ext-move-recording-audio) #'ignore))
                    (org-ext-import-recording-note note))
                  (goto-char (point-min))
                  (should (= (how-many "^\\*\\* TODO Buy milk$") 1)))
              (kill-buffer buffer)))
          (should-not (file-exists-p note)))
      (delete-directory root t))))

(ert-deftest org-ext-import-recording-note-keeps-queue-on-save-failure ()
  (let* ((root (make-temp-file "org-ext-recording-save-failure-" t))
         (queue (expand-file-name "queue" root))
         (receipts (expand-file-name ".imported" queue))
         (note (expand-file-name "failure.m4a.txt" queue))
         (org-ext-recording-queue-directory queue)
         (org-ext-recording-receipt-directory receipts))
    (unwind-protect
        (progn
          (make-directory queue)
          (write-region "Keep me" nil note nil 'silent)
          (with-temp-buffer
            (org-mode)
            (setq buffer-file-name (expand-file-name "inbox.org" root))
            (cl-letf (((symbol-function 'save-buffer)
                       (lambda (&rest _) (error "injected save failure")))
                      ((symbol-function 'org-ext-move-recording-audio) #'ignore))
              (should-error (org-ext-import-recording-note note))))
          (should (file-exists-p note))
          (should-not (file-exists-p receipts)))
      (delete-directory root t))))

;;; org-ext-test.el ends here
