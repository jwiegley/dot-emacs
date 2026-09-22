;;; dired-ext-test.el --- Directory group tests -*- lexical-binding: t; -*-

(require 'ert)
(require 'dired-ext)

(defvar magit-display-buffer-function)
(declare-function magit-display-buffer-fullframe-status-v1 "magit-mode" (buffer))

(defun dired-ext-test--assert-layout (directories mode)
  "Check directory order, geometry, and focus for DIRECTORIES in MODE."
  (let ((windows
         (mapcar (lambda (directory)
                   (cl-find-if
                    (lambda (window)
                      (with-current-buffer (window-buffer window)
                        (and (eq major-mode mode)
                             (file-equal-p default-directory directory))))
                    (window-list)))
                 directories)))
    (should (= (length (window-list)) (length directories)))
    (should (cl-every #'window-live-p windows))
    (should (eq (selected-window) (or (cadr windows) (car windows))))
    (when (cdr windows)
      (let ((left (window-edges (car windows)))
            (right (window-edges (cadr windows))))
        (should (= (nth 2 left) (car right)))
        (should (= (nth 3 left) (nth 3 right)))
        (if (cddr windows)
            (let ((top (window-edges (caddr windows))))
              (should (= (car top) (car left)))
              (should (= (nth 2 top) (nth 2 left)))
              (should (= (nth 3 top) (cadr left)))
              (should (= (cadr top) (cadr right))))
          (should (= (cadr left) (cadr right))))))))

(ert-deftest dired-ext-groups-read-suffixes-and-preserve-layouts ()
  (let* ((root (make-temp-file "dired-ext-test-" t))
         (dired-ext-directory-groups
          (mapcar (lambda (group)
                    (cons (car group)
                          (mapcar (lambda (directory)
                                    (expand-file-name
                                     (file-name-nondirectory directory) root))
                                  (cdr group))))
                  dired-ext-directory-groups)))
    (unwind-protect
        (save-window-excursion
          (dolist (group dired-ext-directory-groups)
            (dolist (directory (cdr group)) (make-directory directory t))
            (let ((unread-command-events (listify-key-sequence (car group))))
              (call-interactively #'dired-ext-open-group)
              (should-not unread-command-events))
            (dired-ext-test--assert-layout (cdr group) 'dired-mode))
          ;; Settings take effect immediately, without rebuilding a global map.
          (let* ((directory (cadar dired-ext-directory-groups))
                 (dired-ext-directory-groups `(("x " ,directory)))
                 (unread-command-events (list ?x ?\s)))
            (call-interactively #'dired-ext-open-group)
            (dired-ext-test--assert-layout (list directory) 'dired-mode)))
      (dolist (buffer (buffer-list))
        (when (string-prefix-p root (buffer-local-value 'default-directory buffer))
          (kill-buffer buffer)))
      (delete-directory root t))))

(ert-deftest dired-ext-prefix-opens-real-magit-buffers ()
  (skip-unless (require 'magit nil t))
  (let* ((root (make-temp-file "dired-ext-magit-test-" t))
         (directories (mapcar (lambda (name) (expand-file-name name root))
                              '("one" "two" "three")))
         ;; Deliberately hostile display policy: group layout must still win.
         (magit-display-buffer-function #'magit-display-buffer-fullframe-status-v1))
    (unwind-protect
        (save-window-excursion
          (dolist (directory directories)
            (make-directory directory)
            (should (zerop (call-process "git" nil nil nil "init" "-q" directory))))
          ;; A subdirectory should show its existing repo, not offer git init.
          (let ((subdir (expand-file-name "subdir" (car directories))))
            (make-directory subdir)
            (dolist (count '(1 2 3))
              (let* ((dirs (cl-subseq directories 0 count))
                     (dired-ext-directory-groups `(("ddI" ,subdir ,@(cdr dirs))))
                     (overriding-terminal-local-map (make-sparse-keymap)))
                (define-key overriding-terminal-local-map (kbd "C-c j")
                            #'dired-ext-open-group)
                (execute-kbd-macro (kbd "C-u C-c j d d I"))
                (dired-ext-test--assert-layout dirs 'magit-status-mode)))))
      (dolist (buffer (buffer-list))
        (when (string-prefix-p root (buffer-local-value 'default-directory buffer))
          (kill-buffer buffer)))
      (delete-directory root t))))

(ert-deftest dired-ext-invalid-groups-leave-windows-unchanged ()
  (save-window-excursion
    (let ((before (current-window-configuration)))
      (dolist (directories '(nil ("") (42) ("/" . "/")
                            ("/" "/" "/" "/")))
        (let ((dired-ext-directory-groups `(("x" ,@directories))))
          (should-error (dired-ext-open-group "x") :type 'user-error)))
      (should-error (dired-ext-open-group "unknown") :type 'user-error)
      (let ((unread-command-events (list ?\C-g)))
        (should (eq (condition-case nil
                        (call-interactively #'dired-ext-open-group)
                      (quit 'quit))
                    'quit)))
      (let ((dired-ext-directory-groups
             `(("x" ,(make-temp-name (expand-file-name "missing-" temporary-file-directory))))))
        (should-error (dired-ext-open-group "x") :type 'user-error))
      (when (require 'magit nil t)
        (let* ((root (make-temp-file "dired-ext-not-git-" t))
               (dired-ext-directory-groups `(("x" ,root))))
          (unwind-protect
              (should-error (dired-ext-open-group "x" '(4)) :type 'user-error)
            (delete-directory root))))
      (should (window-configuration-equal-p before (current-window-configuration))))))

(provide 'dired-ext-test)
;;; dired-ext-test.el ends here
