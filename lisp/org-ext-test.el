;;; org-ext-test.el --- Tests for recording imports -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)

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
    (goto-char (point-min))
    (when (re-search-forward "^(defun org-ext-import-recording-note\\_>" nil t)
      (goto-char (match-beginning 0))
      (eval (read (current-buffer)) t))))

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

(ert-deftest org-ext-import-recording-note-consumes-queue-file ()
  (let* ((root (make-temp-file "org-ext-recording-import-" t))
         (note (expand-file-name "17-28-31.m4a.txt" root))
         (hook-runs 0))
    (unwind-protect
        (progn
          (write-region "Buy milk" nil note nil 'silent)
          (with-temp-buffer
            (org-mode)
            (setq-local org-capture-before-finalize-hook
                        (list (lambda () (setq hook-runs (1+ hook-runs)))))
            (cl-letf (((symbol-function 'org-ext-move-recording-audio) #'ignore))
              (org-ext-import-recording-note note))
            (should (equal (buffer-string) "** TODO Buy milk\n")))
          (should (= hook-runs 1))
          (should-not (file-exists-p note)))
      (delete-directory root t))))

;;; org-ext-test.el ends here
