;;; nix-shell.el -- run nix-shell in Emacs -*- lexical-binding: t -*-

;; Author: Matthew Bauer <mjbauer95@gmail.com>
;; Homepage: https://github.com/matthewbauer/nix-mode
;; Keywords: nix

;; This file is NOT part of GNU Emacs.

;;; Commentary:

;; To use this just run:

;; M-x RET nix-shell RET

;; This will give you some

;;; Code:

;; (require 'nix-mode)
(require 'term)

(defgroup nix-shell nil
  "Customizations for nix-shell"
  :group 'nix)

(defcustom nix-shell-executable "nix-shell"
  "Location of nix-shell executable."
  :group 'nix-shell)

;;;###autoload
(defun nix-shell (path attribute)
  "Run nix-shell in a terminal.

PATH path containing Nix expressions.
ATTRIBUTE attribute name in nixpkgs to use."
  (interactive
   (list (read-from-minibuffer "Nix path: " "<nixpkgs>")
         (read-from-minibuffer "Nix attribute name: ")))
  (set-buffer (make-term "nix-shell" nix-shell-executable nil
                         path "-A" attribute))
  (term-mode)
  (term-char-mode)
  (switch-to-buffer "*nix-shell*"))

(provide 'nix-shell)
;;; nix-shell.el ends here
