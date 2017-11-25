(ert-deftest py-ert-last-exeption-buffer-test ()
  (should (boundp 'py-last-exeption-buffer)))

(ert-deftest py-ert-keywords-test ()
  (should (boundp 'py-keywords)))

(ert-deftest py-ert-pdbtrack-is-tracking-p-test ()
  (should (boundp 'py-pdbtrack-is-tracking-p)))

(ert-deftest py-ert-underscore-word-syntax-p-test ()
  (should (boundp 'py-underscore-word-syntax-p)))

(ert-deftest py-ert-auto-fill-mode-orig-test ()
  (should (boundp 'py-auto-fill-mode-orig)))

(ert-deftest py-ert-kill-empty-line-test ()
  (should (boundp 'py-kill-empty-line)))

(ert-deftest py-ert-match-paren-key-test ()
  (should (boundp 'py-match-paren-key)))

(ert-deftest py-ert-match-paren-mode-test ()
  (should (boundp 'py-match-paren-mode)))

(ert-deftest py-ert-ipython-shell-mode-map-test ()
  (should (boundp 'py-ipython-shell-mode-map)))

(ert-deftest py-ert-python-shell-mode-map-test ()
  (should (boundp 'py-python-shell-mode-map)))

(ert-deftest py-ert-shell-map-test ()
  (should (boundp 'py-shell-map)))

(ert-deftest py-ert-eldoc-string-code-test ()
  (should (boundp 'py-eldoc-string-code)))

(ert-deftest py-ert-chars-after-test ()
  (should (boundp 'py-chars-after)))

(ert-deftest py-ert-chars-before-test ()
  (should (boundp 'py-chars-before)))

(ert-deftest py-ert-ask-about-save-test ()
  (should (boundp 'py-ask-about-save)))

(ert-deftest py-ert-auto-complete-p-test ()
  (should (boundp 'py-auto-complete-p)))

(ert-deftest py-ert--auto-complete-timer-delay-test ()
  (should (boundp 'py--auto-complete-timer-delay)))

(ert-deftest py-ert-auto-fill-mode-test ()
  (should (boundp 'py-auto-fill-mode)))

(ert-deftest py-ert-autofill-timer-delay-test ()
  (should (boundp 'py-autofill-timer-delay)))

(ert-deftest py-ert-autopair-mode-test ()
  (should (boundp 'py-autopair-mode)))

(ert-deftest py-ert-backslashed-lines-indent-offset-test ()
  (should (boundp 'py-backslashed-lines-indent-offset)))

(ert-deftest py-ert-beep-if-tab-change-test ()
  (should (boundp 'py-beep-if-tab-change)))

(ert-deftest py-ert-block-comment-prefix-test ()
  (should (boundp 'py-block-comment-prefix)))

(ert-deftest py-ert-block-comment-prefix-p-test ()
  (should (boundp 'py-block-comment-prefix-p)))

(ert-deftest py-ert-check-command-test ()
  (should (boundp 'py-check-command)))

(ert-deftest py-ert-close-provides-newline-test ()
  (should (boundp 'py-close-provides-newline)))

(ert-deftest py-ert-closing-list-dedents-bos-test ()
  (should (boundp 'py-closing-list-dedents-bos)))

(ert-deftest py-ert-closing-list-keeps-space-test ()
  (should (boundp 'py-closing-list-keeps-space)))

(ert-deftest py-ert-closing-list-space-test ()
  (should (boundp 'py-closing-list-space)))

(ert-deftest py-ert-comment-fill-column-test ()
  (should (boundp 'py-comment-fill-column)))

(ert-deftest py-ert-company-pycomplete-p-test ()
  (should (boundp 'py-company-pycomplete-p)))

(ert-deftest py-ert-compilation-regexp-alist-test ()
  (should (boundp 'py-compilation-regexp-alist)))

(ert-deftest py-ert-complete-ac-sources-test ()
  (should (boundp 'py-complete-ac-sources)))

(ert-deftest py-ert-complete-function-test ()
  (should (boundp 'py-complete-function)))

(ert-deftest py-ert-continuation-offset-test ()
  (should (boundp 'py-continuation-offset)))

(ert-deftest py-ert-current-defun-delay-test ()
  (should (boundp 'py-current-defun-delay)))

(ert-deftest py-ert-current-defun-show-test ()
  (should (boundp 'py-current-defun-show)))

(ert-deftest py-ert-custom-temp-directory-test ()
  (should (boundp 'py-custom-temp-directory)))

(ert-deftest py-ert-debug-p-test ()
  (should (boundp 'py-debug-p)))

(ert-deftest py-ert-dedent-keep-relative-column-test ()
  (should (boundp 'py-dedent-keep-relative-column)))

(ert-deftest py-ert-dedicated-process-p-test ()
  (should (boundp 'py-dedicated-process-p)))

(ert-deftest py-ert-defun-use-top-level-p-test ()
  (should (boundp 'py-defun-use-top-level-p)))

(ert-deftest py-ert-delete-function-test ()
  (should (boundp 'py-delete-function)))

(ert-deftest py-ert-docstring-fill-column-test ()
  (should (boundp 'py-docstring-fill-column)))

(ert-deftest py-ert-docstring-style-test ()
  (should (boundp 'py-docstring-style)))

(ert-deftest py-ert-edit-only-p-test ()
  (should (boundp 'py-edit-only-p)))

(ert-deftest py-ert-electric-colon-active-p-test ()
  (should (boundp 'py-electric-colon-active-p)))

(ert-deftest py-ert-electric-colon-bobl-only-test ()
  (should (boundp 'py-electric-colon-bobl-only)))

(ert-deftest py-ert-electric-colon-greedy-p-test ()
  (should (boundp 'py-electric-colon-greedy-p)))

(ert-deftest py-ert-electric-colon-newline-and-indent-p-test ()
  (should (boundp 'py-electric-colon-newline-and-indent-p)))

(ert-deftest py-ert-electric-comment-add-space-p-test ()
  (should (boundp 'py-electric-comment-add-space-p)))

(ert-deftest py-ert-electric-comment-p-test ()
  (should (boundp 'py-electric-comment-p)))

(ert-deftest py-ert-electric-kill-backward-p-test ()
  (should (boundp 'py-electric-kill-backward-p)))

(ert-deftest py-ert-electric-yank-active-p-test ()
  (should (boundp 'py-electric-yank-active-p)))

(ert-deftest py-ert-empty-comment-line-separates-paragraph-p-test ()
  (should (boundp 'py-empty-comment-line-separates-paragraph-p)))

(ert-deftest py-ert-empty-line-closes-p-test ()
  (should (boundp 'py-empty-line-closes-p)))

(ert-deftest py-ert-encoding-string-test ()
  (should (boundp 'py-encoding-string)))

(ert-deftest py-ert-error-markup-delay-test ()
  (should (boundp 'py-error-markup-delay)))

(ert-deftest py-ert-execute-directory-test ()
  (should (boundp 'py-execute-directory)))

(ert-deftest py-ert-execute-no-temp-p-test ()
  (should (boundp 'py-execute-no-temp-p)))

(ert-deftest py-ert-extensions-test ()
  (should (boundp 'py-extensions)))

(ert-deftest py-ert-fast-completion-delay-test ()
  (should (boundp 'py-fast-completion-delay)))

(ert-deftest py-ert-fast-process-p-test ()
  (should (boundp 'py-fast-process-p)))

(ert-deftest py-ert-ffap-p-test ()
  (should (boundp 'py-ffap-p)))

(ert-deftest py-ert-fileless-buffer-use-default-directory-p-test ()
  (should (boundp 'py-fileless-buffer-use-default-directory-p)))

(ert-deftest py-ert-flake8-command-test ()
  (should (boundp 'py-flake8-command)))

(ert-deftest py-ert-flake8-command-args-test ()
  (should (boundp 'py-flake8-command-args)))

(ert-deftest py-ert-fontify-shell-buffer-p-test ()
  (should (boundp 'py-fontify-shell-buffer-p)))

(ert-deftest py-ert-force-py-shell-name-p-test ()
  (should (boundp 'py-force-py-shell-name-p)))

(ert-deftest py-ert-guess-py-install-directory-p-test ()
  (should (boundp 'py-guess-py-install-directory-p)))

(ert-deftest py-ert-hide-comments-when-hiding-all-test ()
  (should (boundp 'py-hide-comments-when-hiding-all)))

(ert-deftest py-ert-hide-show-hide-docstrings-test ()
  (should (boundp 'py-hide-show-hide-docstrings)))

(ert-deftest py-ert-hide-show-keywords-test ()
  (should (boundp 'py-hide-show-keywords)))

(ert-deftest py-ert-hide-show-minor-mode-p-test ()
  (should (boundp 'py-hide-show-minor-mode-p)))

(ert-deftest py-ert-highlight-error-source-p-test ()
  (should (boundp 'py-highlight-error-source-p)))

(ert-deftest py-ert-history-filter-regexp-test ()
  (should (boundp 'py-history-filter-regexp)))

(ert-deftest py-ert-honor-IPYTHONDIR-p-test ()
  (should (boundp 'py-honor-IPYTHONDIR-p)))

(ert-deftest py-ert-honor-PYTHONHISTORY-p-test ()
  (should (boundp 'py-honor-PYTHONHISTORY-p)))

(ert-deftest py-ert-if-name-main-permission-p-test ()
  (should (boundp 'py-if-name-main-permission-p)))

(ert-deftest py-ert--imenu-create-index-function-test ()
  (should (boundp 'py--imenu-create-index-function)))

(ert-deftest py-ert--imenu-create-index-p-test ()
  (should (boundp 'py--imenu-create-index-p)))

(ert-deftest py-ert-imenu-show-method-args-p-test ()
  (should (boundp 'py-imenu-show-method-args-p)))

(ert-deftest py-ert-import-check-point-max-test ()
  (should (boundp 'py-import-check-point-max)))

(ert-deftest py-ert-indent-comments-test ()
  (should (boundp 'py-indent-comments)))

(ert-deftest py-ert-indent-honors-inline-comment-test ()
  (should (boundp 'py-indent-honors-inline-comment)))

(ert-deftest py-ert-indent-honors-multiline-listing-test ()
  (should (boundp 'py-indent-honors-multiline-listing)))

(ert-deftest py-ert-indent-no-completion-p-test ()
  (should (boundp 'py-indent-no-completion-p)))

(ert-deftest py-ert-indent-offset-test ()
  (should (boundp 'py-indent-offset)))

(ert-deftest py-ert-indent-paren-spanned-multilines-p-test ()
  (should (boundp 'py-indent-paren-spanned-multilines-p)))

(ert-deftest py-ert-indent-tabs-mode-test ()
  (should (boundp 'py-indent-tabs-mode)))

(ert-deftest py-ert-input-filter-re-test ()
  (should (boundp 'py-input-filter-re)))

(ert-deftest py-ert-install-directory-test ()
  (should (boundp 'py-install-directory)))

(ert-deftest py-ert-ipython-command-test ()
  (should (boundp 'py-ipython-command)))

(ert-deftest py-ert-ipython-command-args-test ()
  (should (boundp 'py-ipython-command-args)))

(ert-deftest py-ert-ipython-execute-delay-test ()
  (should (boundp 'py-ipython-execute-delay)))

(ert-deftest py-ert-ipython-history-test ()
  (should (boundp 'py-ipython-history)))

(ert-deftest py-ert-ipython-send-delay-test ()
  (should (boundp 'py-ipython-send-delay)))

(ert-deftest py-ert-jump-on-exception-test ()
  (should (boundp 'py-jump-on-exception)))

(ert-deftest py-ert-jython-command-test ()
  (should (boundp 'py-jython-command)))

(ert-deftest py-ert-jython-command-args-test ()
  (should (boundp 'py-jython-command-args)))

(ert-deftest py-ert-jython-packages-test ()
  (should (boundp 'py-jython-packages)))

(ert-deftest py-ert-keep-shell-dir-when-execute-p-test ()
  (should (boundp 'py-keep-shell-dir-when-execute-p)))

(ert-deftest py-ert-keep-windows-configuration-test ()
  (should (boundp 'py-keep-windows-configuration)))

(ert-deftest py-ert-kill-empty-line-test ()
  (should (boundp 'py-kill-empty-line)))

(ert-deftest py-ert-lhs-inbound-indent-test ()
  (should (boundp 'py-lhs-inbound-indent)))

(ert-deftest py-ert-load-pymacs-p-test ()
  (should (boundp 'py-load-pymacs-p)))

(ert-deftest py-ert-load-skeletons-p-test ()
  (should (boundp 'py-load-skeletons-p)))

(ert-deftest py-ert-mark-decorators-test ()
  (should (boundp 'py-mark-decorators)))

(ert-deftest py-ert-master-file-test ()
  (should (boundp 'py-master-file)))

(ert-deftest py-ert-match-paren-key-test ()
  (should (boundp 'py-match-paren-key)))

(ert-deftest py-ert-match-paren-mode-test ()
  (should (boundp 'py-match-paren-mode)))

(ert-deftest py-ert-max-help-buffer-p-test ()
  (should (boundp 'py-max-help-buffer-p)))

(ert-deftest py-ert-max-specpdl-size-test ()
  (should (boundp 'py-max-specpdl-size)))

(ert-deftest py-ert-message-executing-temporary-file-test ()
  (should (boundp 'py-message-executing-temporary-file)))

(ert-deftest py-ert-modeline-acronym-display-home-p-test ()
  (should (boundp 'py-modeline-acronym-display-home-p)))

(ert-deftest py-ert-modeline-display-full-path-p-test ()
  (should (boundp 'py-modeline-display-full-path-p)))

(ert-deftest py-ert-newline-delete-trailing-whitespace-p-test ()
  (should (boundp 'py-newline-delete-trailing-whitespace-p)))

(ert-deftest py-ert-new-shell-delay-test ()
  (should (boundp 'py-new-shell-delay)))

(ert-deftest py-ert-org-cycle-p-test ()
  (should (boundp 'py-org-cycle-p)))

(ert-deftest py-ert-outline-minor-mode-p-test ()
  (should (boundp 'py-outline-minor-mode-p)))

(ert-deftest py-ert-outline-mode-keywords-test ()
  (should (boundp 'py-outline-mode-keywords)))

(ert-deftest py-ert-pdb-executable-test ()
  (should (boundp 'py-pdb-executable)))

(ert-deftest py-ert-pdb-path-test ()
  (should (boundp 'py-pdb-path)))

(ert-deftest py-ert-pdbtrack-do-tracking-p-test ()
  (should (boundp 'py-pdbtrack-do-tracking-p)))

(ert-deftest py-ert-pdbtrack-filename-mapping-test ()
  (should (boundp 'py-pdbtrack-filename-mapping)))

(ert-deftest py-ert-pdbtrack-minor-mode-string-test ()
  (should (boundp 'py-pdbtrack-minor-mode-string)))

(ert-deftest py-ert-pep8-command-test ()
  (should (boundp 'py-pep8-command)))

(ert-deftest py-ert-pep8-command-args-test ()
  (should (boundp 'py-pep8-command-args)))

(ert-deftest py-ert-prompt-on-changed-p-test ()
  (should (boundp 'py-prompt-on-changed-p)))

(ert-deftest py-ert-pychecker-command-test ()
  (should (boundp 'py-pychecker-command)))

(ert-deftest py-ert-pychecker-command-args-test ()
  (should (boundp 'py-pychecker-command-args)))

(ert-deftest py-ert-pyflakes-command-test ()
  (should (boundp 'py-pyflakes-command)))

(ert-deftest py-ert-pyflakes-command-args-test ()
  (should (boundp 'py-pyflakes-command-args)))

(ert-deftest py-ert-pyflakespep8-command-test ()
  (should (boundp 'py-pyflakespep8-command)))

(ert-deftest py-ert-pyflakespep8-command-args-test ()
  (should (boundp 'py-pyflakespep8-command-args)))

(ert-deftest py-ert-pylint-command-test ()
  (should (boundp 'py-pylint-command)))

(ert-deftest py-ert-pylint-command-args-test ()
  (should (boundp 'py-pylint-command-args)))

(ert-deftest py-ert-python2-command-test ()
  (should (boundp 'py-python2-command)))

(ert-deftest py-ert-python2-command-args-test ()
  (should (boundp 'py-python2-command-args)))

(ert-deftest py-ert-python3-command-test ()
  (should (boundp 'py-python3-command)))

(ert-deftest py-ert-python3-command-args-test ()
  (should (boundp 'py-python3-command-args)))

(ert-deftest py-ert-python-command-test ()
  (should (boundp 'py-python-command)))

(ert-deftest py-ert-python-command-args-test ()
  (should (boundp 'py-python-command-args)))

(ert-deftest py-ert-python-history-test ()
  (should (boundp 'py-python-history)))

(ert-deftest py-ert-python-send-delay-test ()
  (should (boundp 'py-python-send-delay)))

(ert-deftest py-ert-remove-cwd-from-path-test ()
  (should (boundp 'py-remove-cwd-from-path)))

(ert-deftest py-ert-return-key-test ()
  (should (boundp 'py-return-key)))

(ert-deftest py-ert-separator-char-test ()
  (should (boundp 'py-separator-char)))

(ert-deftest py-ert-session-p-test ()
  (should (boundp 'py-session-p)))

(ert-deftest py-ert-set-complete-keymap-p-test ()
  (should (boundp 'py-set-complete-keymap-p)))

(ert-deftest py-ert-set-pager-cat-p-test ()
  (should (boundp 'py-set-pager-cat-p)))

(ert-deftest py-ert-sexp-function-test ()
  (should (boundp 'py-sexp-function)))

(ert-deftest py-ert-shebang-startstring-test ()
  (should (boundp 'py-shebang-startstring)))

(ert-deftest py-ert-shell-input-prompt-1-regexp-test ()
  (should (boundp 'py-shell-input-prompt-1-regexp)))

(ert-deftest py-ert-shell-input-prompt-2-regexp-test ()
  (should (boundp 'py-shell-input-prompt-2-regexp)))

(ert-deftest py-ert-shell-local-path-test ()
  (should (boundp 'py-shell-local-path)))

(ert-deftest py-ert-shell-name-test ()
  (should (boundp 'py-shell-name)))

(ert-deftest py-ert-shell-prompt-output-regexp-test ()
  (should (boundp 'py-shell-prompt-output-regexp)))

(ert-deftest py-ert-shell-prompt-read-only-test ()
  (should (boundp 'py-shell-prompt-read-only)))

(ert-deftest py-ert-shell-prompt-regexp-test ()
  (should (boundp 'py-shell-prompt-regexp)))

(ert-deftest py-ert-shell-toggle-1-test ()
  (should (boundp 'py-shell-toggle-1)))

(ert-deftest py-ert-shell-toggle-2-test ()
  (should (boundp 'py-shell-toggle-2)))

(ert-deftest py-ert-smart-indentation-test ()
  (should (boundp 'py-smart-indentation)))

(ert-deftest py-ert-smart-operator-mode-p-test ()
  (should (boundp 'py-smart-operator-mode-p)))

(ert-deftest py-ert-split-window-on-execute-test ()
  (should (boundp 'py-split-window-on-execute)))

(ert-deftest py-ert-split-windows-on-execute-function-test ()
  (should (boundp 'py-split-windows-on-execute-function)))

(ert-deftest py-ert-store-result-p-test ()
  (should (boundp 'py-store-result-p)))

(ert-deftest py-ert-switch-buffers-on-execute-p-test ()
  (should (boundp 'py-switch-buffers-on-execute-p)))

(ert-deftest py-ert-tab-indent-test ()
  (should (boundp 'py-tab-indent)))

(ert-deftest py-ert-tab-indents-region-p-test ()
  (should (boundp 'py-tab-indents-region-p)))

(ert-deftest py-ert-tab-shifts-region-p-test ()
  (should (boundp 'py-tab-shifts-region-p)))

(ert-deftest py-ert-timer-close-completions-p-test ()
  (should (boundp 'py-timer-close-completions-p)))

(ert-deftest py-ert-trailing-whitespace-smart-delete-p-test ()
  (should (boundp 'py-trailing-whitespace-smart-delete-p)))

(ert-deftest py-ert-uncomment-indents-p-test ()
  (should (boundp 'py-uncomment-indents-p)))

(ert-deftest py-ert-update-gud-pdb-history-p-test ()
  (should (boundp 'py-update-gud-pdb-history-p)))

(ert-deftest py-ert-use-current-dir-when-execute-p-test ()
  (should (boundp 'py-use-current-dir-when-execute-p)))

(ert-deftest py-ert-use-font-lock-doc-face-p-test ()
  (should (boundp 'py-use-font-lock-doc-face-p)))

(ert-deftest py-ert-use-local-default-test ()
  (should (boundp 'py-use-local-default)))

(ert-deftest py-ert-verbose-p-test ()
  (should (boundp 'py-verbose-p)))

(ert-deftest py-ert--warn-tmp-files-left-p-test ()
  (should (boundp 'py--warn-tmp-files-left-p)))

(ert-deftest py-ert-already-guessed-indent-offset-test ()
  (should (boundp 'py-already-guessed-indent-offset)))

(ert-deftest py-ert-assignment-re-test ()
  (should (boundp 'py-assignment-re)))

(ert-deftest py-ert--auto-complete-timer-test ()
  (should (boundp 'py--auto-complete-timer)))

(ert-deftest py-ert-auto-completion-buffer-test ()
  (should (boundp 'py-auto-completion-buffer)))

(ert-deftest py-ert-auto-completion-mode-p-test ()
  (should (boundp 'py-auto-completion-mode-p)))

(ert-deftest py-ert-autofill-timer-test ()
  (should (boundp 'py-autofill-timer)))

(ert-deftest py-ert-block-or-clause-re-test ()
  (should (boundp 'py-block-or-clause-re)))

(ert-deftest py-ert-buffer-name-test ()
  (should (boundp 'py-buffer-name)))

(ert-deftest py-ert-builtins-face-test ()
  (should (boundp 'py-builtins-face)))

(ert-deftest py-ert-class-name-face-test ()
  (should (boundp 'py-class-name-face)))

(ert-deftest py-ert-complete-last-modified-test ()
  (should (boundp 'py-complete-last-modified)))

(ert-deftest py-ert-completion-last-window-configuration-test ()
  (should (boundp 'py-last-window-configuration)))

(ert-deftest py-ert-decorators-face-test ()
  (should (boundp 'py-decorators-face)))

(ert-deftest py-ert-default-interpreter-test ()
  (should (boundp 'py-default-interpreter)))

(ert-deftest py-ert-def-class-face-test ()
  (should (boundp 'py-def-class-face)))

(ert-deftest py-ert-delimiter-re-test ()
  (should (boundp 'py-delimiter-re)))

(ert-deftest py-ert-dotted-expression-syntax-table-test ()
  (should (boundp 'py-dotted-expression-syntax-table)))

(ert-deftest py-ert-eldoc-setup-code-test ()
  (should (boundp 'py-eldoc-setup-code)))

(ert-deftest py-ert-encoding-string-re-test ()
  (should (boundp 'py-encoding-string-re)))

(ert-deftest py-ert-error-test ()
  (should (boundp 'py-error)))

(ert-deftest py-ert-ert-test-default-executables-test ()
  (should (boundp 'py-ert-test-default-executables)))

(ert-deftest py-ert-exception-buffer-test ()
  (should (boundp 'py-exception-buffer)))

(ert-deftest py-ert-exception-name-face-test ()
  (should (boundp 'py-exception-name-face)))

(ert-deftest py-ert-exec-command-test ()
  (should (boundp 'py-exec-command)))

(ert-deftest py-ert-expression-re-test ()
  (should (boundp 'py-expression-re)))

(ert-deftest py-ert-expression-skip-chars-test ()
  (should (boundp 'py-expression-skip-chars)))

(ert-deftest py-ert-expression-skip-regexp-test ()
  (should (boundp 'py-expression-skip-regexp)))

(ert-deftest py-ert-fast-filter-re-test ()
  (should (boundp 'py-fast-filter-re)))

(ert-deftest py-ert-ffap-test ()
  (should (boundp 'py-ffap)))

(ert-deftest py-ert-ffap-p-test ()
  (should (boundp 'py-ffap-p)))

(ert-deftest py-ert-ffap-setup-code-test ()
  (should (boundp 'py-ffap-setup-code)))

(ert-deftest py-ert-ffap-string-code-test ()
  (should (boundp 'py-ffap-string-code)))

(ert-deftest py-ert-file-queue-test ()
  (should (boundp 'py-file-queue)))

(ert-deftest py-ert-fill-column-orig-test ()
  (should (boundp 'py-fill-column-orig)))

(ert-deftest py-ert-flake8-history-test ()
  (should (boundp 'py-flake8-history)))

(ert-deftest py-ert-force-local-shell-p-test ()
  (should (boundp 'py-force-local-shell-p)))

(ert-deftest py-ert-import-from-face-test ()
  (should (boundp 'py-import-from-face)))

(ert-deftest py-ert-ipython0.10-completion-command-string-test ()
  (should (boundp 'py-ipython0.10-completion-command-string)))

(ert-deftest py-ert-ipython0.11-completion-command-string-test ()
  (should (boundp 'py-ipython0.11-completion-command-string)))

(ert-deftest py-ert-ipython-completion-command-string-test ()
  (should (boundp 'py-ipython-completion-command-string)))

(ert-deftest py-ert-ipython-completions-test ()
  (should (boundp 'py-ipython-completions)))

(ert-deftest py-ert-ipython-input-prompt-re-test ()
  (should (boundp 'py-ipython-input-prompt-re)))

(ert-deftest py-ert-ipython-module-completion-code-test ()
  (should (boundp 'py-ipython-module-completion-code)))

(ert-deftest py-ert-ipython-module-completion-string-test ()
  (should (boundp 'py-ipython-module-completion-string)))

(ert-deftest py-ert-ipython-output-prompt-re-test ()
  (should (boundp 'py-ipython-output-prompt-re)))

(ert-deftest py-ert-labelled-re-test ()
  (should (boundp 'py-labelled-re)))

(ert-deftest py-ert-line-number-offset-test ()
  (should (boundp 'py-line-number-offset)))

(ert-deftest py-ert-local-command-test ()
  (should (boundp 'py-local-command)))

(ert-deftest py-ert-local-versioned-command-test ()
  (should (boundp 'py-local-versioned-command)))

(ert-deftest py-ert-match-paren-no-use-syntax-pps-test ()
  (should (boundp 'py-match-paren-no-use-syntax-pps)))

(ert-deftest py-ert-mode-output-map-test ()
  (should (boundp 'py-mode-output-map)))

(ert-deftest py-ert-new-session-p-test ()
  (should (boundp 'py-new-session-p)))

(ert-deftest py-ert-not-expression-chars-test ()
  (should (boundp 'py-not-expression-chars)))

(ert-deftest py-ert-not-expression-regexp-test ()
  (should (boundp 'py-not-expression-regexp)))

(ert-deftest py-ert-number-face-test ()
  (should (boundp 'py-number-face)))

(ert-deftest py-ert-object-reference-face-test ()
  (should (boundp 'py-object-reference-face)))

(ert-deftest py-ert-operator-re-test ()
  (should (boundp 'py-operator-re)))

(ert-deftest py-ert-orig-buffer-or-file-test ()
  (should (boundp 'py-orig-buffer-or-file)))

(ert-deftest py-ert-output-buffer-test ()
  (should (boundp 'py-output-buffer)))

(ert-deftest py-ert-partial-expression-backward-chars-test ()
  (should (boundp 'py-partial-expression-backward-chars)))

(ert-deftest py-ert-partial-expression-forward-chars-test ()
  (should (boundp 'py-partial-expression-forward-chars)))

(ert-deftest py-ert-pdbtrack-input-prompt-test ()
  (should (boundp 'py-pdbtrack-input-prompt)))

(ert-deftest py-ert-pep8-history-test ()
  (should (boundp 'py-pep8-history)))

(ert-deftest py-ert-pseudo-keyword-face-test ()
  (should (boundp 'py-pseudo-keyword-face)))

(ert-deftest py-ert-pychecker-history-test ()
  (should (boundp 'py-pychecker-history)))

(ert-deftest py-ert-pydbtrack-input-prompt-test ()
  (should (boundp 'py-pydbtrack-input-prompt)))

(ert-deftest py-ert-pyflakes-history-test ()
  (should (boundp 'py-pyflakes-history)))

(ert-deftest py-ert-pyflakespep8-history-test ()
  (should (boundp 'py-pyflakespep8-history)))

(ert-deftest py-ert-pylint-history-test ()
  (should (boundp 'py-pylint-history)))

(ert-deftest py-ert-python-completions-test ()
  (should (boundp 'py-python-completions)))

(ert-deftest py-ert-result-test ()
  (should (boundp 'py-result)))

(ert-deftest py-ert-return-result-p-test ()
  (should (boundp 'py-return-result-p)))

(ert-deftest py-ert-separator-char-test ()
  (should (boundp 'py-separator-char)))

(ert-deftest py-ert-shebang-regexp-test ()
  (should (boundp 'py-shebang-regexp)))

(ert-deftest py-ert-shell-complete-debug-test ()
  (should (boundp 'py-shell-complete-debug)))

(ert-deftest py-ert-shell-completion-setup-code-test ()
  (should (boundp 'py-shell-completion-setup-code)))

(ert-deftest py-ert-shell-hook-test ()
  (should (boundp 'py-shell-hook)))

(ert-deftest py-ert-shell-module-completion-code-test ()
  (should (boundp 'py-shell-module-completion-code)))

(ert-deftest py-ert-shell-template-test ()
  (should (boundp 'py-shell-template)))

(ert-deftest py-ert-string-delim-re-test ()
  (should (boundp 'py-string-delim-re)))

(ert-deftest py-ert-temp-directory-test ()
  (should (boundp 'py-temp-directory)))

(ert-deftest py-ert-this-abbrevs-changed-test ()
  (should (boundp 'py-this-abbrevs-changed)))

(ert-deftest py-ert-traceback-line-re-test ()
  (should (boundp 'py-traceback-line-re)))

(ert-deftest py-ert-try-if-face-test ()
  (should (boundp 'py-try-if-face)))

(ert-deftest py-ert-underscore-word-syntax-p-test ()
  (should (boundp 'py-underscore-word-syntax-p)))

(ert-deftest py-ert-variable-name-face-test ()
  (should (boundp 'py-variable-name-face)))

(ert-deftest py-ert-which-bufname-test ()
  (should (boundp 'py-which-bufname)))

(ert-deftest py-ert-windows-config-test ()
  (should (boundp 'py-windows-config)))

(ert-deftest py-ert-XXX-tag-face-test ()
  (should (boundp 'py-XXX-tag-face)))

(ert-deftest py-ert-block-closing-keywords-re-test ()
  (should (boundp 'py-block-closing-keywords-re)))

(ert-deftest py-ert-ipython-input-prompt-re-test ()
  (should (boundp 'py-ipython-input-prompt-re)))

(ert-deftest py-ert-imenu-class-regexp-test ()
  (should (boundp 'py-imenu-class-regexp)))

(ert-deftest py-ert-imenu-generic-expression-test ()
  (should (boundp 'py-imenu-generic-expression)))

(ert-deftest py-ert-imenu-generic-parens-test ()
  (should (boundp 'py-imenu-generic-parens)))

(ert-deftest py-ert-imenu-generic-regexp-test ()
  (should (boundp 'py-imenu-generic-regexp)))

(ert-deftest py-ert-imenu-method-arg-parens-test ()
  (should (boundp 'py-imenu-method-arg-parens)))

(ert-deftest py-ert-imenu-method-no-arg-parens-test ()
  (should (boundp 'py-imenu-method-no-arg-parens)))

(ert-deftest py-ert-imenu-method-regexp-test ()
  (should (boundp 'py-imenu-method-regexp)))

