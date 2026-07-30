;;; org-ext-test.el --- Tests for org-ext -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-agenda)
(require 'ox-md)
(require 'mdformat)

(defvar org-ext-recording-queue-directory)
(defvar org-ext-recording-receipt-directory)
(defvar org-ext-recording-inbox-directories)
(defvar org-capture-plist)
(defvar org-constants-drafts-path)
(defvar org-constants-positron-team-file)
(defvar org-ext-location-command-timeout)

(defconst org-ext-test-directory
  (file-name-directory (or load-file-name buffer-file-name)))

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
    (dolist (name '(org-ext-copy-subtree-as-markdown
                    org-ext-move-recording-audio
                    org-ext-recording-file-hash
                    org-ext-recording-receipt-file
                    org-ext-recording-imported-p
                    org-ext-write-recording-receipt
                    org-ext-import-recording-note))
      (goto-char (point-min))
      (when (re-search-forward (format "^(defun %s\\_>" name) nil t)
        (goto-char (match-beginning 0))
        (eval (read (current-buffer)) t)))))

(let ((source (expand-file-name "org-ext.el"
                                (file-name-directory load-file-name))))
  ;; Eval additional functions needed by the regression tests below,
  ;; handling defun, defsubst, and defalias forms.
  (dolist (name '(org-ext--import-agenda-notes
                  org-ext-goto-inbox-heading
                  org-ext-goto-inbox
                  org-ext-agenda-show
                  org-ext-agenda-show-and-scroll-up
                  org-ext-jump-to-agenda
                  org-ext--with-agenda-entry
                  org-ext-entry-span
                  org-ext-with-entry-narrowed
                  org-ext-entire-properties-block
                  org-ext-move-properties-drawer
                  org-ext-fix-all-properties
                  org-ext-move-subtree-to-point
                  org-ext-cleanup-whitespace
                  org-ext--cleanup-whitespace-region
                  org-ext-fixup-slack
                  org-ext-set-stored-link
                  org-ext-update-date-field
                  org-ext-todoize
                  org-ext-set-id-and-created
                  org-ext-with-property-search
                  org-ext-get-inactive-time
                  org-ext-parent-priority
                  org-ext-ancestor-keywords
                  org-ext-open-all-links-in-subtree
                  org-ext-edit-link-name
                  org-ext-swap-link-name
                  org-ext-unlink-region
                  org-ext-follow-tag-link
                  org-ext-gnus-drop-link-parameter
                  org-ext-update-team
                  org-ext-linkify
                  org-ext-current-tags
                  org-ext-get-location
                  org-ext-insert-code-block
                  org-ext-get-all-categories
                  org-ext-get-all-categories-detailed
                  org-ext-show-all-categories
                  org-ext-agenda-files-except
                  org-ext-chain-blockers-in-region
                  org-ext--split-heading-title
                  org-ext--join-heading-title
                  org-ext--set-heading-component
                  org-ext--fast-selection-keywords
                  org-ext--first-child-todo
                  org-ext-first-child-todo
                  org-ext-has-preceding-todo-p
                  org-ext-task-p))
    (with-temp-buffer
      (insert-file-contents source)
      (goto-char (point-min))
      (let ((found nil))
        (dolist (re (list (format "^(defun %s\\_>" name)
                          (format "^(defmacro %s\\_>" name)
                          (format "^(defsubst %s\\_>" name)
                          (format "^(defalias '%s\\_>" name)))
          (unless found
            (goto-char (point-min))
            (when (re-search-forward re nil t)
              (setq found t)
              (goto-char (match-beginning 0))
              (eval (read (current-buffer)) t))))
        (unless found
          (error "could not load %s from org-ext.el" name))))))
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

(ert-deftest org-ext-copy-subtree-as-markdown-formats-before-copying ()
  (skip-unless (not (get-buffer "*Org MD Export*")))
  (let ((output-buffer (get-buffer-create "*Org MD Export*")))
    (unwind-protect
        (progn
          (with-current-buffer output-buffer
            (insert "STALE\n"))
          (with-temp-buffer
            (org-mode)
            (insert "#+OPTIONS: toc:t d:t tasks:nil todo:t\n"
                    "* Before\nOutside\n"
                    "* Container\n"
                    "** TODO Parent\nBody\n"
                    "- State \"TODO\"       from \"PROMPT\"     [2026-07-24 Fri 10:05]\n"
                    "- Keep this ordinary list item.\n"
                    "See [[#child][child]].\n"
                    ":LOGBOOK:\n"
                    "- State \"NEXT\" from \"TODO\" [2026-07-24 Fri]\n"
                    ":END:\n"
                    ":NOTES:\n"
                    "Keep drawer text.\n"
                    ":END:\n"
                    "*** DONE Child\n"
                    ":PROPERTIES:\n"
                    ":CUSTOM_ID: child\n"
                    ":END:\n"
                    "Nested\n"
                    "** Sibling\nNot copied\n"
                    "* After\nOutside\n")
            (let* ((original (buffer-string))
                   (narrow-start
                    (progn
                      (goto-char (point-min))
                      (re-search-forward "^\\*\\* TODO Parent$")
                      (line-beginning-position)))
                   (narrow-end
                    (progn
                      (re-search-forward "^\\* After$")
                      (line-beginning-position))))
              (narrow-to-region narrow-start narrow-end)
              (goto-char narrow-start)
              (forward-line)
              (set-mark (point))
              (end-of-line)
              (setq mark-active t)
              (let ((original-point (point))
                    (org-md-headline-style 'setext)
                    (org-md-toplevel-hlevel 2)
                    (org-export-with-toc t)
                    (org-export-with-drawers t)
                    (org-export-with-tasks nil)
                    (org-export-with-todo-keywords t)
                    (interprogram-cut-function nil)
                    (interprogram-paste-function nil)
                    copied
                    displayed
                    events)
                (cl-letf (((symbol-function 'mdformat-buffer)
                           (lambda ()
                             (setq events (append events '(format)))
                             (goto-char (point-max))
                             (insert "FORMATTED\n")))
                          ((symbol-function 'kill-new)
                           (lambda (string &optional _replace)
                             (setq copied string
                                   events (append events '(copy)))))
                          ((symbol-function 'pop-to-buffer)
                           (lambda (buffer &rest _)
                             (setq displayed buffer
                                   events (append events '(pop)))
                             buffer)))
                  (org-ext-copy-subtree-as-markdown))
                (let ((markdown
                       (with-current-buffer output-buffer
                         (buffer-string))))
                  (should (equal events '(format copy pop)))
                  (should (eq displayed output-buffer))
                  (should (equal copied markdown))
                  (should (string-match-p "^# Parent$" markdown))
                  (should (string-match-p "^## Child$" markdown))
                  (should-not
                   (string-match-p
                    "^#+ .*\\_<\\(?:TODO\\|DONE\\|NEXT\\|PROMPT\\)\\_>"
                    markdown))
                  (should (string-match-p "\\[child\\](#child)" markdown))
                  (should (string-match-p "Keep this ordinary list item\\."
                                          markdown))
                  (should (string-match-p "Keep drawer text\\." markdown))
                  (should-not (string-match-p "Table of Contents" markdown))
                  (should-not (string-match-p "<a id=" markdown))
                  (should-not (string-match-p "State \"" markdown))
                  (should-not (string-match-p "Sibling" markdown))
                  (should-not (string-match-p "STALE" markdown))
                  (should (string-suffix-p "FORMATTED\n" markdown)))
                (with-current-buffer output-buffer
                  (should (eq major-mode 'text-mode))
                  (should (= (point) (point-min))))
                (should (= original-point (point)))
                (should mark-active)
                (should (= narrow-start (point-min)))
                (should (= narrow-end (point-max)))
                (save-restriction
                  (widen)
                  (should (equal original (buffer-string))))))))
      (when (buffer-live-p output-buffer)
        (kill-buffer output-buffer)))))

(ert-deftest org-ext-copy-subtree-as-markdown-keeps-clipboard-on-format-error ()
  (skip-unless (not (get-buffer "*Org MD Export*")))
  (let ((output-buffer (get-buffer-create "*Org MD Export*")))
    (unwind-protect
        (progn
          (with-current-buffer output-buffer
            (insert "STALE\n"))
          (with-temp-buffer
            (org-mode)
            (insert "* Parent\nBody\n")
            (goto-char (point-min))
            (let* ((kill-ring '("existing clipboard"))
                   (kill-ring-yank-pointer kill-ring)
                   (interprogram-cut-function nil)
                   (interprogram-paste-function nil)
                   format-buffer
                   unformatted
                   copy-called
                   pop-called)
              (cl-letf (((symbol-function 'mdformat-buffer)
                         (lambda ()
                           (setq format-buffer (current-buffer)
                                 unformatted (buffer-string))
                           (user-error "format failed")))
                        ((symbol-function 'kill-new)
                         (lambda (&rest _) (setq copy-called t)))
                        ((symbol-function 'pop-to-buffer)
                         (lambda (&rest _) (setq pop-called t))))
                (should-error (org-ext-copy-subtree-as-markdown)
                              :type 'user-error))
              (should (eq format-buffer output-buffer))
              (should-not copy-called)
              (should-not pop-called)
              (should (equal kill-ring '("existing clipboard")))
              (with-current-buffer output-buffer
                (should (equal (buffer-string) unformatted))
                (should (string-match-p "^# Parent$" (buffer-string)))
                (should-not (string-match-p "STALE" (buffer-string)))))))
      (when (buffer-live-p output-buffer)
        (kill-buffer output-buffer)))))

(ert-deftest org-ext-copy-subtree-as-markdown-keeps-clipboard-on-export-error ()
  (skip-unless (not (get-buffer "*Org MD Export*")))
  (let ((output-buffer (get-buffer-create "*Org MD Export*")))
    (unwind-protect
        (progn
          (with-current-buffer output-buffer
            (insert "STALE\n"))
          (with-temp-buffer
            (org-mode)
            (insert "* Parent\nBody\n")
            (goto-char (point-min))
            (let* ((kill-ring '("existing clipboard"))
                   (kill-ring-yank-pointer kill-ring)
                   (interprogram-cut-function nil)
                   (interprogram-paste-function nil)
                   format-called
                   copy-called
                   pop-called)
              (cl-letf (((symbol-function 'org-export-as)
                         (lambda (&rest _) (user-error "export failed")))
                        ((symbol-function 'mdformat-buffer)
                         (lambda () (setq format-called t)))
                        ((symbol-function 'kill-new)
                         (lambda (&rest _) (setq copy-called t)))
                        ((symbol-function 'pop-to-buffer)
                         (lambda (&rest _) (setq pop-called t))))
                (should-error (org-ext-copy-subtree-as-markdown)
                              :type 'user-error))
              (should-not format-called)
              (should-not copy-called)
              (should-not pop-called)
              (should (equal kill-ring '("existing clipboard")))
              (with-current-buffer output-buffer
                (should (string-empty-p (buffer-string)))))))
      (when (buffer-live-p output-buffer)
        (kill-buffer output-buffer)))))

(ert-deftest org-ext-story-a-draft-survives-save-failure ()
  (let* ((root (make-temp-file "org-ext-draft-save-" t))
         (draft (expand-file-name "draft.txt" root))
         (inbox (expand-file-name "inbox.org" root))
         (original "* Inbox\n"))
    (unwind-protect
        (progn
          (write-region "Draft body" nil draft nil 'silent)
          (write-region original nil inbox nil 'silent)
          (let ((buffer (find-file-noselect inbox)))
            (unwind-protect
                (with-current-buffer buffer
                  (goto-char (point-max))
                  (cl-letf (((symbol-function 'org-ext-reformat-draft) #'ignore)
                            ((symbol-function 'save-buffer)
                             (lambda (&rest _) (error "injected save failure"))))
                    (should-error
                     (org-ext--import-agenda-notes (list draft) nil)))
                  (should (buffer-modified-p))
                  (should (file-exists-p draft))
                  (should (equal original
                                 (with-temp-buffer
                                   (insert-file-contents inbox)
                                   (buffer-string)))))
              (with-current-buffer buffer
                (set-buffer-modified-p nil))
              (kill-buffer buffer))))
      (delete-directory root t))))

(ert-deftest org-ext-story-a-paste-failure-preserves-source ()
  (let* ((root (make-temp-file "org-ext-move-subtree-" t))
         (source-file (expand-file-name "source.org" root))
         (original "* Source\nBody\n"))
    (unwind-protect
        (progn
          (write-region original nil source-file nil 'silent)
          (let ((source-buffer (find-file-noselect source-file)))
            (unwind-protect
                (with-temp-buffer
                  (org-mode)
                  (insert "* Destination\n")
                  (goto-char (point-max))
                  (setq buffer-read-only t)
                  (cl-letf (((symbol-function 'org-id-find)
                             (lambda (&rest _) (cons source-file 1))))
                    (should-error (org-ext-move-subtree-to-point "source")))
                  (with-current-buffer source-buffer
                    (should (equal original (buffer-string)))
                    (should-not (buffer-modified-p)))
                  (should (equal original
                                 (with-temp-buffer
                                   (insert-file-contents source-file)
                                   (buffer-string)))))
              (kill-buffer source-buffer))))
      (delete-directory root t))))

(ert-deftest org-ext-story-a-capture-cleanup-stays-within-markers ()
  (with-temp-buffer
    (org-mode)
    (insert "Outside  \n"
            "* Capture\nBody\u00a0  \n\n\n"
            "* After\nKeep  \n")
    (goto-char (point-min))
    (re-search-forward "^\\* Capture$")
    (let ((beg (copy-marker (line-beginning-position)))
          end before after)
      (re-search-forward "^\\* After$")
      (setq end (copy-marker (line-beginning-position))
            before (buffer-substring-no-properties (point-min) beg)
            after (buffer-substring-no-properties end (point-max)))
      (goto-char beg)
      (let ((org-capture-plist t))
        (cl-letf (((symbol-function 'org-capture-get)
                   (lambda (key &optional _local)
                     (pcase key
                       (:begin-marker beg)
                       (:end-marker end)))))
          (org-ext-cleanup-whitespace)))
      (should (equal before
                     (buffer-substring-no-properties (point-min) beg)))
      (should (equal after
                     (buffer-substring-no-properties end (point-max))))
      (should-not (string-match-p "\u00a0"
                                  (buffer-substring-no-properties beg end)))
      (should-not (string-match-p " +$"
                                  (buffer-substring-no-properties beg end))))))

(ert-deftest org-ext-story-a-property-drawers-are-structural ()
  (with-temp-buffer
    (org-mode)
    (insert "* Example only\n"
            "#+begin_example\n"
            ":PROPERTIES:\n:X: y\n:END:\n"
            "#+end_example\n")
    (goto-char (point-min))
    (let ((original (buffer-string)))
      (should-not (org-ext-entire-properties-block))
      (org-ext-move-properties-drawer)
      (should (equal original (buffer-string))))
    (erase-buffer)
    (insert "* One\nBody\n:PROPERTIES:\n:A: 1\n:END:\n"
            "* Two\nBody\n:PROPERTIES:\n:B: 2\n:END:\n")
    (goto-char (point-max))
    (org-back-to-heading t)
    (org-ext-fix-all-properties)
    (goto-char (point-min))
    (re-search-forward "^\\* One$")
    (forward-line)
    (should (looking-at-p ":PROPERTIES:"))
    (re-search-forward "^\\* Two$")
    (forward-line)
    (should (looking-at-p ":PROPERTIES:"))))

;;; org-ext-test.el ends here
