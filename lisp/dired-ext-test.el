;;; dired-ext-test.el --- Directory group tests -*- lexical-binding: t; -*-

(require 'ert)
(require 'bookmark)
(require 'dired-ext)

(defvar magit-display-buffer-function)
(declare-function magit-display-buffer-fullframe-status-v1 "magit-mode" (buffer))

(defun dired-ext-test--assert-layout (targets mode)
  "Check order, geometry, and focus for TARGETS.
A directory target must be shown in MODE; a buffer target as itself."
  (let ((windows
         (mapcar (lambda (target)
                   (cl-find-if
                    (lambda (window)
                      (if (bufferp target)
                          (eq (window-buffer window) target)
                        (with-current-buffer (window-buffer window)
                          (and (eq major-mode mode)
                               (file-equal-p default-directory target)))))
                    (window-list)))
                 targets)))
    (should (= (length (window-list)) (length targets)))
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

(defmacro dired-ext-test--with-bookmarks (specs &rest body)
  "Run BODY with only the bookmarks (NAME FILE POSITION) in SPECS defined.
The user's bookmark file is never loaded."
  (declare (indent 1))
  `(let ((bookmark-alist
          (list ,@(mapcar (lambda (spec)
                            `(list ,(car spec) (cons 'filename ,(cadr spec))
                                   (cons 'position ,(caddr spec))))
                          specs)))
         (bookmark-default-file
          (make-temp-name (expand-file-name "dired-ext-bookmarks-"
                                            temporary-file-directory)))
         (bookmark-bookmarks-timestamp nil)
         (bookmark-watch-bookmark-file nil))
     ,@body))

(defun dired-ext-test--kill-buffers-in (root)
  "Kill every buffer whose directory is under ROOT."
  (dolist (buffer (buffer-list))
    (when (string-prefix-p root (buffer-local-value 'default-directory buffer))
      (kill-buffer buffer))))

(ert-deftest dired-ext-groups-read-suffixes-and-preserve-layouts ()
  (let* ((root (make-temp-file "dired-ext-test-" t))
         (dired-ext-directory-groups
          (mapcar (lambda (group)
                    (cons (car group)
                          (mapcar (lambda (directory)
                                    (expand-file-name
                                     (file-name-nondirectory directory) root))
                                  (cdr group))))
                  ;; Bookmark groups need real bookmarks; tested below.
                  (cl-remove-if-not (lambda (group) (cl-every #'stringp (cdr group)))
                                    dired-ext-directory-groups))))
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
      (dired-ext-test--kill-buffers-in root)
      (delete-directory root t))))

(ert-deftest dired-ext-bookmarks-open-at-their-positions ()
  (let* ((root (file-name-as-directory (make-temp-file "dired-ext-bookmark-test-" t)))
         (file (expand-file-name "focus.txt" root))
         (left (expand-file-name "left" root))
         (top (expand-file-name "top" root))
         (position 30)
         (other 5)
         jumps)
    (make-directory left)
    (make-directory top)
    (with-temp-file file (dotimes (i 20) (insert (format "line %d\n" i))))
    (unwind-protect
        (dired-ext-test--with-bookmarks (("Focus" file position)
                                         ("Other" file other))
          (let ((bookmark-after-jump-hook
                 (list (lambda () (push (cons (current-buffer) (point)) jumps)))))
            (save-window-excursion
              ;; Already visiting the file elsewhere must not override the bookmark.
              (find-file file)
              (goto-char (point-min))
              (let ((buffer (current-buffer))
                    (dired-ext-directory-groups '(("f" (bookmark "Focus")))))
                (let ((unread-command-events (list ?f)))
                  (call-interactively #'dired-ext-open-group))
                (dired-ext-test--assert-layout (list buffer) nil)
                (should (= (window-point) position))
                (should (equal jumps (list (cons buffer position))))
                ;; The Magit prefix leaves bookmarks alone.
                (goto-char (point-min))
                (dired-ext-open-group "f" '(4))
                (dired-ext-test--assert-layout (list buffer) nil)
                (should (= (window-point) position))
                ;; Bookmarks mix with both directory forms in every position.
                (dolist (items `((,left (bookmark "Focus"))
                                 ((bookmark "Focus") (directory ,left))
                                 ((directory ,left) (bookmark "Focus") ,top)
                                 ((bookmark "Focus") ,left (directory ,top))))
                  (with-current-buffer buffer (goto-char (point-min)))
                  (let ((dired-ext-directory-groups `(("x" ,@items))))
                    (dired-ext-open-group "x"))
                  (dired-ext-test--assert-layout
                   (mapcar (lambda (item)
                             (pcase item
                               (`(bookmark ,_) buffer)
                               (`(directory ,dir) dir)
                               (_ item)))
                           items)
                   'dired-mode)
                  (should (= (window-point (get-buffer-window buffer)) position)))
                ;; Two bookmarks into one buffer keep separate positions,
                ;; even when invoked from another buffer.
                (dired left)
                (let ((dired-ext-directory-groups
                       '(("x" (bookmark "Focus") (bookmark "Other")))))
                  (dired-ext-open-group "x"))
                (should (eq (window-buffer (window-in-direction 'left)) buffer))
                (should (= (window-point (window-in-direction 'left)) position))
                (should (eq (window-buffer) buffer))
                (should (= (window-point) other))))))
      (dired-ext-test--kill-buffers-in root)
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
      (dired-ext-test--kill-buffers-in root)
      (delete-directory root t))))

(ert-deftest dired-ext-invalid-groups-leave-windows-unchanged ()
  (save-window-excursion
    (let ((before (current-window-configuration)))
      (dired-ext-test--with-bookmarks (("Broken" "/" 1))
        (dolist (items '(nil ("") (42) ("/" . "/") ("/" "/" "/" "/")
                         ((directory)) ((directory "")) ((directory "/" "/"))
                         ((bookmark)) ((bookmark "")) ((bookmark 42))
                         ((bookmark "Missing")) ("/" (file "/"))))
          (let ((dired-ext-directory-groups `(("x" ,@items))))
            (should-error (dired-ext-open-group "x") :type 'user-error)))
        ;; A bookmark that fails while jumping must not disturb the layout.
        (push `(handler . ,(lambda (_) (error "Jump failed")))
              (cdar bookmark-alist))
        (let ((dired-ext-directory-groups '(("x" "/" (bookmark "Broken")))))
          (should-error (dired-ext-open-group "x"))))
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

(ert-deftest dired-ext-custom-type-accepts-all-item-forms ()
  (require 'wid-edit)
  (let ((type (widget-convert (get 'dired-ext-directory-groups 'custom-type))))
    (dolist (groups (list (eval (car (get 'dired-ext-directory-groups
                                          'standard-value))
                                t)
                          '(("x" "/" (directory "/") (bookmark "Focus")))))
      (should (widget-apply type :match groups)))
    (dolist (groups '((("x")) (("x" (bookmark))) (("x" (file "/")))
                      (("x" "/" "/" "/" "/"))))
      (should-not (widget-apply type :match groups)))))

(provide 'dired-ext-test)
;;; dired-ext-test.el ends here
