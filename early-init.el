;;; early-init.el --- Work that must precede init.el -*- lexical-binding: t; -*-

;;; Commentary:

;; Interactive startup loads this file before init.el.  Batch, -q and -Q
;; runs skip it, so init.el requires lisp/user-paths.el again.

;;; Code:

;; Redirect the native-compilation cache, and every other state path,
;; before any library has a chance to use its default.  Load the source
;; file by name: a stale user-paths.elc must never be picked up.
(load (expand-file-name "lisp/user-paths.el" user-emacs-directory) nil t)

;; Packages come from the Nix bundle.  package.el decides whether to
;; activate packages between this file and init.el, so this must be here.
(setq package-enable-at-startup nil)

;;; early-init.el ends here
