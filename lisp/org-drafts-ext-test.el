;;; org-drafts-ext-test.el --- Tests for org-drafts-ext -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-element)
(require 'seq)

;;; Code:

(let ((source (expand-file-name "../init.org"
                                (file-name-directory load-file-name))))
  (with-temp-buffer
    (insert-file-contents source)
    (goto-char (point-min))
    (re-search-forward "^[ \t]*(defun markdown-to-org-region\\_>")
    (goto-char (match-beginning 0))
    (eval (read (current-buffer)) t)))

(let ((load-prefer-newer t))
  (require 'org-drafts)
  (require 'gptel-ext)
  (require 'org-drafts-ext))

(declare-function org-drafts-ext-paste-prompt "org-drafts-ext")

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
                          (body "# Nested heading" "* Nested heading" nil)))
            (with-temp-buffer
              (org-mode)
              (let* ((start (nth 0 case))
                     (markdown (nth 1 case))
                     (converted (nth 2 case))
                     (expect-fill (nth 3 case))
                     (expected (if (eq start 'body)
                                   "** Nested heading"
                                 converted))
                     (org-todo-keywords
                      '((sequence "TODO" "DRAFT" "PROMPT" "|" "DONE")))
                     (kill-ring (list markdown))
                     (kill-ring-yank-pointer kill-ring)
                     (interprogram-paste-function nil)
                     (current-prefix-arg nil)
                     fill-bounds
                     fill-text
                     title-called)
                (org-set-regexps-and-options)
                (insert "* DRAFT [2026-07-26 Sun 23:41]  \n"
                        ":PROPERTIES:\n:ID: test\n:END:\n"
                        "Existing **body**.\n")
                (goto-char (point-min))
                (pcase start
                  ('property (search-forward ":ID:"))
                  ('body (search-forward "Existing")))
                (cl-letf (((symbol-function 'fill-region)
                           (lambda (beg end &rest _args)
                             (setq fill-bounds
                                   (list beg end (point-min) (point-max))
                                   fill-text
                                   (buffer-substring-no-properties
                                    (point-min) (point-max)))))
                          ((symbol-function 'gptel-ext-title)
                           (lambda () (setq title-called t))))
                  (org-drafts-ext-paste-prompt))
                (if expect-fill
                    (progn
                      (should (equal fill-text (concat expected "\n")))
                      (should (= (nth 0 fill-bounds) (nth 2 fill-bounds)))
                      (should (= (nth 1 fill-bounds) (nth 3 fill-bounds))))
                  (should-not fill-bounds))
                (should title-called)
                (goto-char (point-min))
                (should (looking-at-p "^\\* PROMPT$"))
                (re-search-forward ":END:\n")
                (should
                 (equal (buffer-substring-no-properties (point) (point-max))
                        (concat expected "\nExisting **body**.\n")))
                (should (equal (car kill-ring)
                               (concat expected "\nExisting **body**."))))))
          (with-temp-buffer
            (org-mode)
            (let* ((org-todo-keywords
                    '((sequence "TODO" "DRAFT" "PROMPT" "|" "DONE")))
                   (text "# Failing prompt")
                   (kill-ring (list text))
                   (kill-ring-yank-pointer kill-ring)
                   (interprogram-paste-function nil)
                   (current-prefix-arg nil)
                   (original
                    "* DRAFT [2026-07-26 Sun 23:41]\n:PROPERTIES:\n:ID: test\n:END:\n"))
              (org-set-regexps-and-options)
              (insert original)
              (goto-char (point-min))
              (let ((process-environment (copy-sequence process-environment))
                    title-called)
                (setenv "PATH" "/nonexistent")
                (cl-letf (((symbol-function 'gptel-ext-title)
                           (lambda () (setq title-called t))))
                  (should-error (org-drafts-ext-paste-prompt)
                                :type 'user-error))
                (should-not title-called))
              (should (equal (buffer-string) original))
              (should (equal (car kill-ring) text)))))
      (define-key org-mode-map (kbd "H-p") old-binding))))

(provide 'org-drafts-ext-test)
;;; org-drafts-ext-test.el ends here
