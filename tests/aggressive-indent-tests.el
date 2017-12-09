(byte-compile-file "aggressive-indent.el")
(require 'package)
(setq package-user-dir (expand-file-name "./elpa"))
(package-initialize)
(when (version< emacs-version "24.3")
  (package-install-file (expand-file-name "cl-lib.el")))

(package-install-file (expand-file-name "../names.el"))
(setq byte-compile-error-on-warn t)
(package-install-file (expand-file-name "aggressive-indent.el"))

(defun file-as-list (file)
  (let (out it)
    (with-temp-buffer
      (insert-file-contents-literally file)
      (goto-char (point-min))
      (while (setq it (ignore-errors (read (current-buffer))))
        (push it out))
      out)))

(defvar truncated-emacs-version
  (replace-regexp-in-string "\\(....\\).*" "\\1" emacs-version)
  "")

(ert-deftest compare-autoloads ()
  (let ((should-have (file-as-list (format "elpa/aggressive-indent-autoloads-%s.el" truncated-emacs-version)))
        (do-have (file-as-list "elpa/aggressive-indent-0.1/aggressive-indent-autoloads.el")))
    (should (equal do-have should-have))))



