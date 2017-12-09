;;; test-helper --- Test helper for paradox

;;; Commentary:
;; test helper inspired from https://github.com/tonini/overseer.el/blob/master/test/test-helper.el

;;; Code:

(unless (bound-and-true-p package--initialized)
  (setq
   package-user-dir (expand-file-name
                     (format "../.cask/%s/elpa" emacs-version)
                     (file-name-directory load-file-name)))

  (package-initialize))

(require 'ert)
(require 'undercover)
(undercover "*.el")
(require 'paradox)

;;; test-helper.el ends here
