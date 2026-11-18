;;; apply-init-edits-test.el --- Tests for apply-init-edits.el -*- lexical-binding: t; -*-

;; Run with:
;;   emacs --batch -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit

(require 'ert)

(load (expand-file-name "apply-init-edits.el"
                        (file-name-directory (or load-file-name
                                                 buffer-file-name)))
      nil t)

(defun xdg-init-edits-test--bytes (file)
  "Return the contents of FILE as a unibyte string."
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (insert-file-contents-literally file)
    (buffer-string)))

(defun xdg-init-edits-test--fixture (&optional transform)
  "Write a scratch file holding every text the edits replace.
TRANSFORM, if given, is called on the list of texts and returns the
list to write.  A UTF-8 character outside the edits checks that the
file is handled as bytes."
  (let ((file (make-temp-file "init-edits-test-" nil ".org"))
        (texts (mapcar (lambda (edit) (plist-get edit :old)) xdg-init-edits))
        (coding-system-for-write 'no-conversion))
    (when transform
      (setq texts (funcall transform texts)))
    (with-temp-file file
      (set-buffer-multibyte nil)
      (insert "#+title: fixture \303\251\n\n")
      (dolist (text texts)
        (insert text "\nfiller between edits\n\n")))
    file))

(ert-deftest xdg-init-edits-test-edits-are-plain-ascii ()
  (dolist (edit xdg-init-edits)
    (dolist (key '(:old :new))
      (should (string-match-p "\\`[[:ascii:]]+\\'" (plist-get edit key))))
    (should-not (equal (plist-get edit :old) (plist-get edit :new)))))

(ert-deftest xdg-init-edits-test-check-writes-nothing ()
  (let* ((file (xdg-init-edits-test--fixture))
         (before (xdg-init-edits-test--bytes file)))
    (unwind-protect
        (progn
          (should (xdg-init-edits-apply file t))
          (should (equal before (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-apply-then-apply-again ()
  (let ((file (xdg-init-edits-test--fixture)))
    (unwind-protect
        (let (once)
          (should (xdg-init-edits-apply file))
          (setq once (xdg-init-edits-test--bytes file))
          (dolist (edit xdg-init-edits)
            (should (string-search (plist-get edit :new) once)))
          (should-not (string-search "(defconst user-data-directory" once))
          (should-not (string-search "~/.local/share/emacs/backups" once))
          (should (string-prefix-p "#+title: fixture \303\251\n" once))
          ;; A second run finds every edit done and leaves the bytes alone.
          (should (xdg-init-edits-apply file))
          (should (equal once (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-each-path-names-its-root ()
  ;; Which root a file belongs to is the point of most edits, so pin it.
  (let ((file (xdg-init-edits-test--fixture)))
    (unwind-protect
        (let (text)
          (should (xdg-init-edits-apply file))
          (setq text (xdg-init-edits-test--bytes file))
          (dolist (name '("backups" "network-security.data" "bm-repository"
                          "bmk-bmenu-state.el" "nov-places"
                          "persistent-scratch" "prescient-save.el"
                          "projectile-bookmarks.eld" "recentf" "history"
                          "places" "slime-history.eld" "lsp-session-v1"
                          "org-clock-save.el" "org-id-locations"))
            (should (string-search (format "(user-state %S)" name) text))
            (should-not (string-search (format "(user-data %S)" name) text)))
          (should (string-search "(user-data \"lsp/\")" text))
          (dolist (name '("projectile.cache" "org-roam.db" "xeft.db"))
            (should (string-search (format "(user-cache %S)" name) text))
            (should-not (string-search (format "(user-data %S)" name) text)))
          ;; The old names of the lsp files are gone with their old root.
          (should-not (string-search ".lsp-session-v1" text))
          (should-not (string-search ".cache/lsp" text))
          (should-not (string-search "~/.local/share/emacs/backups" text)))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-a-touched-block-is-not-inserted-twice ()
  ;; The first edit inserts a block before a heading that stays in the
  ;; file.  Someone who later rewords that block must not get a second
  ;; copy on the next run.
  (let ((file (xdg-init-edits-test--fixture)))
    (unwind-protect
        (let (text)
          (should (xdg-init-edits-apply file))
          (setq text (xdg-init-edits-test--bytes file))
          (with-temp-file file
            (set-buffer-multibyte nil)
            (insert (string-replace ";; Refuse to run on state"
                                    ";; Do not run on state" text)))
          (should (xdg-init-edits-apply file))
          (setq text (xdg-init-edits-test--bytes file))
          (should (= 1 (with-temp-buffer
                         (insert text)
                         (how-many "(user-paths-check-migrated)"
                                   (point-min) (point-max))))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-missing-text-aborts-everything ()
  (let* ((file (xdg-init-edits-test--fixture #'butlast))
         (before (xdg-init-edits-test--bytes file)))
    (unwind-protect
        (progn
          (should-not (xdg-init-edits-apply file))
          (should (equal before (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-ambiguous-text-aborts-everything ()
  (let* ((file (xdg-init-edits-test--fixture
                (lambda (texts) (append texts (last texts)))))
         (before (xdg-init-edits-test--bytes file)))
    (unwind-protect
        (progn
          (should-not (xdg-init-edits-apply file))
          (should (equal before (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(provide 'apply-init-edits-test)

;;; apply-init-edits-test.el ends here
