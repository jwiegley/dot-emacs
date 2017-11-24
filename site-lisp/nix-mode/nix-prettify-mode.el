;;; nix-prettify.el -- Prettify Nix store file names  -*- lexical-binding: t -*-

;; Copyright © 2014, 2015 Alex Kost <alezost@gmail.com>
;; Modified by Matthew Bauer for use in nix-mode

;; Author: Alex Kost
;; Maintainer: Matthew Bauer <mjbauer95@gmail.com>
;; Homepage: https://github.com/matthewbauer/nix-mode
;; Version: 1.1
;; Keywords: nix

;; This file is NOT part of GNU Emacs.

;;; Commentary:

;; This package provides minor-mode for prettifying Nix store file
;; names — i.e., after enabling `nix-prettify-mode',
;; '/gnu/store/72f54nfp6g1hz873w8z3gfcah0h4nl9p-foo-0.1' names will be
;; replaced with '/gnu/store/…-foo-0.1' in the current buffer.  There is
;; also `global-nix-prettify-mode' for global prettifying.

;; To install, add the following to your Emacs init file:
;;
;;   (add-to-list 'load-path "/path/to/dir-with-nix-prettify")
;;   (autoload 'nix-prettify-mode "nix-prettify" nil t)
;;   (autoload 'global-nix-prettify-mode "nix-prettify" nil t)

;; If you want to enable/disable composition after "M-x font-lock-mode",
;; use the following setting:
;;
;;   (setq font-lock-extra-managed-props
;;         (cons 'composition font-lock-extra-managed-props))

;; Credits:
;;
;; Thanks to Ludovic Courtès for the idea of this package.
;;
;; Thanks to the authors of `prettify-symbols-mode' (part of Emacs 24.4)
;; and "pretty-symbols.el" <http://github.com/drothlis/pretty-symbols>
;; for the code.  It helped to write this package.

;;; Code:

(defgroup nix-prettify nil
  "Prettify Nix store file names."
  :prefix "nix-prettify-"
  :group 'nix
  :group 'font-lock
  :group 'convenience)

(defcustom nix-prettify-char ?…
  "Character used for prettifying."
  :type 'character
  :group 'nix-prettify)

(defcustom nix-prettify-decompose-force nil
  "If non-nil, remove any composition.

By default, after disabling `nix-prettify-mode',
compositions (prettifying names with `nix-prettify-char') are
removed only from strings matching `nix-prettify-regexp', so
that compositions created by other modes are left untouched.

Set this variable to non-nil, if you want to remove any
composition unconditionally (like variable `prettify-symbols-mode' does).
Most likely it will do no harm and will make the process of
disabling `nix-prettify-mode' a little faster."
  :type 'boolean
  :group 'nix-prettify)

(defcustom nix-prettify-regexp
  ;; The following file names / URLs should be abbreviated:

  ;; /gnu/store/…-foo-0.1
  ;; /nix/store/…-foo-0.1
  ;; http://hydra.gnu.org/nar/…-foo-0.1
  ;; http://hydra.gnu.org/log/…-foo-0.1

  (rx "/" (or "store" "nar" "log") "/"
      ;; Hash-parts do not include "e", "o", "u" and "t".  See base32Chars
      ;; at <https://github.com/NixOS/nix/blob/master/src/libutil/hash.cc>
      (group (= 32 (any "0-9" "a-d" "f-n" "p-s" "v-z"))))
  "Regexp matching file names for prettifying.

Disable `nix-prettify-mode' before modifying this variable and
make sure to modify `nix-prettify-regexp-group' if needed.

Example of a \"deeper\" prettifying:

  (setq nix-prettify-regexp \"store/[[:alnum:]]\\\\\\={32\\\\}\"
        nix-prettify-regexp-group 0)

This will transform
'/gnu/store/72f54nfp6g1hz873w8z3gfcah0h4nl9p-foo-0.1' into
'/gnu/…-foo-0.1'"
  :type 'regexp
  :group 'nix-prettify)

(defcustom nix-prettify-regexp-group 1
  "Regexp group in `nix-prettify-regexp' for prettifying."
  :type 'integer
  :group 'nix-prettify)

(defvar nix-prettify-special-modes
  '(nix-info-mode ibuffer-mode)
  "List of special modes that support font-locking.

By default, \\[global-nix-prettify-mode] enables prettifying in
all buffers except the ones where `font-lock-defaults' is
nil (see Info node `(elisp) Font Lock Basics'), because it may
break the existing highlighting.

Modes from this list and all derived modes are exceptions
\(`global-nix-prettify-mode' enables prettifying there).")

(defvar nix-prettify-flush-function
  (cond ((fboundp 'font-lock-flush) #'font-lock-flush)
        ((fboundp 'jit-lock-refontify) #'jit-lock-refontify))
  "Function used to refontify buffer.
This function is called without arguments after
enabling/disabling `nix-prettify-mode'.  If nil, do nothing.")

(defun nix-prettify-compose ()
  "Compose matching region in the current buffer."
  (let ((beg (match-beginning nix-prettify-regexp-group))
        (end (match-end       nix-prettify-regexp-group)))
    (compose-region beg end nix-prettify-char 'decompose-region))
  ;; Return nil because we're not adding any face property.
  nil)

(defun nix-prettify-decompose-buffer ()
  "Remove file names compositions from the current buffer."
  (with-silent-modifications
    (let ((inhibit-read-only t))
      (if nix-prettify-decompose-force
          (remove-text-properties (point-min)
                                  (point-max)
                                  '(composition nil))
        (nix-while-search nix-prettify-regexp
          (remove-text-properties
           (match-beginning nix-prettify-regexp-group)
           (match-end       nix-prettify-regexp-group)
           '(composition nil)))))))

;;;###autoload
(define-minor-mode nix-prettify-mode
  "Toggle Nix Prettify mode.

With a prefix argument ARG, enable Nix Prettify mode if ARG is
positive, and disable it otherwise.  If called from Lisp, enable
the mode if ARG is omitted or nil.

When Nix Prettify mode is enabled, hash-parts of the Nix store
file names (see `nix-prettify-regexp') are prettified,
i.e. displayed as `nix-prettify-char' character.  This mode can
be enabled programmatically using hooks:

  (add-hook 'shell-mode-hook 'nix-prettify-mode)

It is possible to enable the mode in any buffer, however not any
buffer's highlighting may survive after adding new elements to
`font-lock-keywords' (see `nix-prettify-special-modes' for
details).

Also you can use `global-nix-prettify-mode' to enable Nix
Prettify mode for all modes that support font-locking."
  :init-value nil
  :lighter " …"
  (let ((keywords `((,nix-prettify-regexp
                     (,nix-prettify-regexp-group
                      (nix-prettify-compose))))))
    (if nix-prettify-mode
        ;; Turn on.
        (font-lock-add-keywords nil keywords)
      ;; Turn off.
      (font-lock-remove-keywords nil keywords)
      (nix-prettify-decompose-buffer))
    (and nix-prettify-flush-function
         (funcall nix-prettify-flush-function))))

(defun nix-prettify-supported-p ()
  "Return non-nil, if the mode can be harmlessly enabled in current buffer."
  (or font-lock-defaults
      (apply #'derived-mode-p nix-prettify-special-modes)))

(defun nix-prettify-turn-on ()
  "Enable `nix-prettify-mode' in the current buffer if needed.
See `nix-prettify-special-modes' for details."
  (and (not nix-prettify-mode)
       (nix-prettify-supported-p)
       (nix-prettify-mode)))

;;;###autoload
(define-globalized-minor-mode global-nix-prettify-mode
  nix-prettify-mode nix-prettify-turn-on)

;;;###autoload
(defalias 'nix-prettify-global-mode 'global-nix-prettify-mode)

(provide 'nix-prettify-mode)

;;; nix-prettify-mode.el ends here
