;;; org-drafts-ext-test.el --- Tests for org-drafts-ext -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-element)
(require 'seq)

;;; Code:

(unless (featurep 'org-drafts)
  (defvar org-drafts-alt-task-body-function nil)
  (defun org-drafts-prompt (&optional _alt)
    "Stand-in for `org-drafts-prompt' when testing without that package.")
  (provide 'org-drafts))

(unless (featurep 'gptel-ext)
  (defun gptel-ext-title ()
    "Stand-in for `gptel-ext-title' when testing without that package.")
  (provide 'gptel-ext))

(let ((load-prefer-newer t))
  (require 'org-drafts-ext))

(ert-deftest org-drafts-ext-test-paste-prompt ()
  (let ((old-binding (lookup-key org-mode-map (kbd "H-p")))
        (org-drafts-alt-task-body-function nil))
    (unwind-protect
        (progn
          (org-drafts-ext-install)
          (should (eq (lookup-key org-mode-map (kbd "H-p"))
                      #'org-drafts-ext-paste-prompt))
          (should (eq org-drafts-alt-task-body-function
                      #'org-drafts-ext-ai-title-body-function))
          (dolist (case '((heading "First **bold** line" "First *bold* line" t)
                          (property "- First item\n- Second item"
                                    "- First item\n- Second item" nil)
                          (body "Another paragraph" "Another paragraph" t)))
            (with-temp-buffer
              (org-mode)
              (let* ((start (nth 0 case))
                     (markdown (nth 1 case))
                     (converted (nth 2 case))
                     (expect-fill (nth 3 case))
                     (org-todo-keywords
                      '((sequence "TODO" "DRAFT" "PROMPT" "|" "DONE")))
                     (kill-ring (list markdown))
                     (kill-ring-yank-pointer kill-ring)
                     (interprogram-paste-function nil)
                     received
                     filled
                     prompt-alt)
                (org-set-regexps-and-options)
                (insert "* DRAFT [2026-07-26 Sun 23:41]\n"
                        ":PROPERTIES:\n:ID: test\n:END:\n"
                        "Existing body.\n")
                (goto-char (point-min))
                (pcase start
                  ('property (search-forward ":ID:"))
                  ('body (search-forward "Existing")))
                (cl-letf (((symbol-function 'markdown-to-org-region)
                           (lambda (beg end)
                             (setq received
                                   (buffer-substring-no-properties beg end))
                             (delete-region beg end)
                             (goto-char beg)
                             (insert converted)))
                          ((symbol-function 'fill-region)
                           (lambda (&rest _args) (setq filled t)))
                          ((symbol-function 'org-drafts-prompt)
                           (lambda (&optional alt) (setq prompt-alt alt))))
                  (org-drafts-ext-paste-prompt))
                (should (equal received markdown))
                (should (eq filled expect-fill))
                (should (eq prompt-alt t))
                (goto-char (point-min))
                (re-search-forward ":END:\n")
                (should
                 (equal (buffer-substring-no-properties (point) (point-max))
                        (concat converted "\nExisting body.\n"))))))
          (with-temp-buffer
            (org-mode)
            (insert "* PROMPT [2026-07-26 Sun 23:41]\nBody\n")
            (goto-char (point-min))
            (let ((current-prefix-arg nil)
                  title-called)
              (cl-letf (((symbol-function 'gptel-ext-title)
                         (lambda () (setq title-called t))))
                (funcall org-drafts-alt-task-body-function
                         (point-marker) nil nil))
              (should title-called)
              (should (equal (buffer-substring-no-properties
                              (line-beginning-position) (line-end-position))
                             "* PROMPT")))))
      (define-key org-mode-map (kbd "H-p") old-binding))))

(provide 'org-drafts-ext-test)
;;; org-drafts-ext-test.el ends here
