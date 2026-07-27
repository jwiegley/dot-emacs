;;; org-drafts-ext-test.el --- Tests for org-drafts-ext -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-element)
(require 'seq)

;;; Code:

(let ((source (expand-file-name "org-drafts-ext.el"
                                (file-name-directory load-file-name))))
  (with-temp-buffer
    (insert-file-contents source)
    (goto-char (point-min))
    (re-search-forward "^(defun org-drafts-ext-paste-prompt\\_>")
    (goto-char (match-beginning 0))
    (eval (read (current-buffer)) t)))

(ert-deftest org-drafts-ext-test-paste-prompt ()
  (dolist (case '(("First paragraph line one\n line two\n\nSecond paragraph.\n" t)
                  ("- First item\n- Second item\n" nil)))
    (with-temp-buffer
      (org-mode)
      (let* ((text (car case))
             (expect-fill (cadr case))
             (org-todo-keywords
              '((sequence "TODO" "DRAFT" "PROMPT" "|" "DONE")))
             (kill-ring (list text))
             (kill-ring-yank-pointer kill-ring)
             (interprogram-paste-function nil)
             converted
             filled
             prompt-alt)
        (org-set-regexps-and-options)
        (insert "* DRAFT [2026-07-26 Sun 23:41]\n"
                ":PROPERTIES:\n:ID: test\n:END:\n")
        (goto-char (point-min))
        (cl-letf (((symbol-function 'markdown-to-org-region)
                   (lambda (beg end)
                     (setq converted
                           (buffer-substring-no-properties beg end))))
                  ((symbol-function 'fill-region)
                   (lambda (&rest _args) (setq filled t)))
                  ((symbol-function 'org-drafts-prompt)
                   (lambda (&optional alt) (setq prompt-alt alt))))
          (org-drafts-ext-paste-prompt))
        (should (equal converted text))
        (should (eq filled expect-fill))
        (should prompt-alt)
        (goto-char (point-min))
        (re-search-forward ":END:\n")
        (should (looking-at (regexp-quote text)))))))

(provide 'org-drafts-ext-test)
;;; org-drafts-ext-test.el ends here
