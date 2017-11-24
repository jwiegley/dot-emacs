;;; nix-company.el --- Company support for Nix -*- lexical-binding: t -*-

;; This file is NOT part of GNU Emacs.

;;; Commentary:

;;; Code:

(require 'nix-repl)
(require 'cl-lib)

(defun company-nix (command &optional arg &rest _)
  "Company backend for Nix.

COMMAND company command
ARG company argument"
  (interactive '(interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-nix))
    (prefix (and (member major-mode '(nix-mode nix-repl-mode))
                 (nix-grab-attr-path)))
    (candidates
     (nix-get-completions (get-buffer-process (nix--get-company-buffer)) arg))
    (sorted t)))

(defun nix-grab-attr-path ()
  "Get Nix attribute path at point."
  (if (looking-at "[^a-zA-Z0-9'\\-_\\.]")
      (buffer-substring (point) (save-excursion (skip-chars-backward "a-zA-Z0-9'\\-_\\.")
                                                (point)))
    (unless (and (char-after)
                 (string-match "[a-zA-Z0-9'\\-_]" (char-to-string (char-after)))
                 ""))))

(defun nix--get-company-buffer (&optional buffer)
  "Get the Nix repl buffer for company.

BUFFER check for Nix-REPL in current buffer"
  (let* ((buf (or buffer (current-buffer)))
         (repl-buf (get-buffer "*Nix-REPL*")))
    (if (or (equal buf "*Nix-REPL*") (equal buf repl-buf))
        repl-buf
      (nix--get-company-backend-buffer buf))))

(defvar nix-company-backend-buffer-name " *nix-company-backend*")
(defvar nix--company-last-buffer nil)

(defun nix--get-company-backend-buffer (buffer)
  "Get Nix company backend from BUFFER."
  (let* ((buf-file (buffer-file-name buffer))
         (backend-buf (get-buffer-create nix-company-backend-buffer-name))
         (last-buf nix--company-last-buffer)
         (proc (get-buffer-process backend-buf)))
    (with-current-buffer buffer
      (if (and proc
               (process-live-p proc))
          (if (not (string= last-buf (buffer-name)))
              (progn (quit-process proc)
                     (nix--make-repl-in-buffer backend-buf)
                     (nix--send-repl (concat ":l " buf-file "\n")
                                     (get-buffer-process backend-buf) t)
                     (setq nix--company-last-buffer (buffer-name)))
            (nix--send-repl ":r\n" proc t))
        (progn (nix--make-repl-in-buffer backend-buf)
               (nix--send-repl (concat ":l " buf-file "\n")
                               (get-buffer-process backend-buf) t)
               (setq nix--company-last-buffer (buffer-name))))
      backend-buf)))

(add-to-list 'company-backends 'company-nix)

(provide 'nix-company)
;;; nix-company.el ends here
