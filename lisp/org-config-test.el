;;; org-config-test.el --- Tests for Org configuration -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org-config)
(require 'org-agenda)
(require 'org-super-agenda)
(require 'vulpea-ext)

(defun org-config-test--agenda-headings ()
  "Return source headings from the current agenda buffer."
  (let (headings)
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (when-let* ((marker (get-text-property (point) 'org-hd-marker)))
          (push (org-with-point-at marker (org-get-heading t t t t)) headings))
        (forward-line 1)))
    (nreverse headings)))

(ert-deftest org-config-test-lab-notebook-agenda ()
  "Show open tasks in active agenda files whose paths contain journal."
  (let* ((root (make-temp-file "org-config-test-" t))
         (journal (expand-file-name "journal" root))
         (old (expand-file-name "20260101-lab-notebook.org" journal))
         (new (expand-file-name "20260102-lab-notebook.org" journal))
         (inactive (expand-file-name "inactive.org" journal))
         (other-journal (expand-file-name "project-journal.org" root))
         (outside (expand-file-name "todo.org" root))
         (org-directory (file-name-as-directory root))
         (org-agenda-files (list outside))
         (org-todo-keywords '((sequence "TODO" "WAIT" "DEFER" "|" "DONE")))
         (org-agenda-persistent-filter nil)
         (org-agenda-window-setup 'current-window)
         (org-agenda-sticky nil)
         (org-agenda-archives-mode nil)
         (org-agenda-todo-ignore-scheduled 'all)
         (org-agenda-tags-todo-honor-ignore-options t)
         (org-agenda-sorting-strategy '((todo priority-down category-keep)
                                        (tags priority-down category-keep)))
         (org-super-agenda-groups '((:name "High priority" :priority "A")
                                    (:name "Other tasks" :anything t))))
    (unwind-protect
        (progn
          (make-directory journal)
          (with-temp-file old
            (insert "#+category: Journal\n"
                    "* WAIT Later same day\n:PROPERTIES:\n:CREATED: [2026-01-01 Thu 18:00]\n:END:\n"
                    "** TODO Nested task\n:PROPERTIES:\n:CREATED: [2026-01-01 Thu 12:00]\n:END:\n"
                    "* TODO [#C] Earliest task\n:PROPERTIES:\n:CREATED: [2026-01-01 Thu 08:00]\n:END:\n"
                    "* DONE Completed task\n"))
          (with-temp-file new
            (insert "#+category: Different\n"
                    "* DEFER [#A] Newest task\nSCHEDULED: <2026-01-03 Sat>\n"
                    ":PROPERTIES:\n:CREATED: [2026-01-02 Fri 09:00]\n:END:\n"))
          (with-temp-file other-journal
            (insert "* TODO Other journal task\n:PROPERTIES:\n"
                    ":CREATED: [2026-01-03 Sat 09:00]\n:END:\n"))
          (with-temp-file inactive (insert "* TODO Inactive file task\n"))
          (with-temp-file outside (insert "* TODO Outside task\n"))
          (cl-letf (;; Use the same refresh advice as the running configuration.
                    ((symbol-function 'vulpea-project-list)
                     (lambda () (list outside new old other-journal))))
            (vulpea-auto-update-install)
            (org-super-agenda-mode 1)
            (org-agenda nil "j")
            (should (equal (org-config-test--agenda-headings)
                           '("Later same day" "Nested task" "Earliest task"
                             "Newest task" "Other journal task")))
            ;; Refresh must retain both the scope and chronological ordering.
            (org-agenda-redo)
            (should (equal (org-config-test--agenda-headings)
                           '("Later same day" "Nested task" "Earliest task"
                             "Newest task" "Other journal task")))
            ;; Other agenda commands must still receive Vulpea's project list.
            (org-agenda nil "t")
            (should (member "Outside task" (org-config-test--agenda-headings)))))
      (advice-remove 'org-agenda #'vulpea-update-agenda-files)
      (advice-remove 'org-todo-list #'vulpea-update-agenda-files)
      (org-super-agenda-mode -1)
      (dolist (file (list old new inactive other-journal outside))
        (when-let* ((buffer (get-file-buffer file)))
          (kill-buffer buffer)))
      (when-let* ((buffer (get-buffer org-agenda-buffer-name)))
        (kill-buffer buffer))
      (delete-directory root t))))

(provide 'org-config-test)
;;; org-config-test.el ends here
