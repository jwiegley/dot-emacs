;;; nix-mode-tests.el -- test nix-mode

;;; Commentary:

;;; Code:

(require 'ert)
(require 'nix-mode)

(ert-deftest nix-mode-quote-detection ()
  (should (with-temp-buffer
            (nix-mode)
            (insert "'' ")
            (save-excursion (insert " ''"))
            (eq (nix--get-string-type (nix--get-parse-state (point))) ?\'))))

(ert-deftest nix-mode-quote2-detection ()
  (should (with-temp-buffer
            (nix-mode)
            (insert "\"")
            (save-excursion (insert "\""))
            (eq (nix--get-string-type (nix--get-parse-state (point))) ?\"))))

(ert-deftest nix-mode-quote3-detection ()
  (should (with-temp-buffer
            (nix-mode)
            (eq (nix--get-string-type (nix--get-parse-state (point))) nil))))

(provide 'nix-mode-tests)
;;; nix-mode-tests.el ends here
