;;; nix-shell.el -- support for MMM in nix-mode -*- lexical-binding: t -*-

;; Author: Matthew Bauer <mjbauer95@gmail.com>
;; Homepage: https://github.com/matthewbauer/nix-mode
;; Keywords: nix

;; This file is NOT part of GNU Emacs.

;;; Commentary:

;;; Code:

(require 'mmm-mode)

(mmm-add-group 'nix-sh
               '((sh-command
                  :submode sh-mode
                  :face mmm-output-submode-face
                  :front "[^'a-zA-Z]''[^']"
                  :back "''[^$\\]"
                  :include-front t
                  :front-offset 4
                  :end-not-begin t
                  )))

(setq mmm-global-mode 'maybe)
(mmm-add-mode-ext-class 'nix-mode "\\.nix\\'" 'nix-sh)

(provide 'nix-mode-mmm)
;;; nix-mode-mmm.el ends here
