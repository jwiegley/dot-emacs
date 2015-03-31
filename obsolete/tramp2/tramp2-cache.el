;;; tramp2-cache.el --- TRAMP2 cache management and access

;; Copyright (C) 2001 by Daniel Pittman <daniel@localhost>

;;; Commentary:

;; This module provides remote caching support for tramp2 connections.

;; Each cache is maintained as a buffer-local value in the actual connection
;; buffer. This ensures that the cache is flushed when the connection is
;; destroyed.

;;; Code:
(eval-when-compile
  (require 'tramp2)
  (make-variable-buffer-local 'tramp2-tilde-cache))

(require 'tramp2-compat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tilde expansion caching.
;;
;; Because the user home directory is *very* unlikely to change during a
;; single connection to the remote host, this is a good candidate for caching.
(defun tramp2-tilde-expand (path name)
  "Expand VALUE as a tilde expression for the connection of PATH.
The result is cached and served from there, if possible."
  (unless (char-equal ?~ (elt name 0))
    (tramp2-error "Invalid tilde expression" name))
  (tramp2-with-connection path
    (or (tramp2-tilde-find name)
	(tramp2-tilde-extract path name))))

(defun tramp2-tilde-find (name)
  "Find an entry in the tilde cache for this connection."
  ;; Make sure we have a cache already...
  (if (boundp 'tramp2-tilde-cache)
      (cdr-safe (assoc name tramp2-tilde-cache))
    (set (make-local-variable 'tramp2-tilde-cache) nil)))

(defun tramp2-tilde-extract (path name)
  "Expand a tilde expression on the remote machine and return it.
The value is added to the local cache to avoid the overhead a second
time."
  (unless (= 0 (tramp2-run-command path (format "echo %s" name)))
    (tramp2-error (format "Unable to expand %s" name)))
  (tramp2-tilde-add name
		    (file-name-as-directory (buffer-substring (tramp2-point-at-bol)
							      (tramp2-point-at-eol)))))

(defun tramp2-tilde-add (name value)
  "Add an entry to the tramp2 tilde cache."
  (setq tramp2-tilde-cache (nconc (list (cons name value)) tramp2-tilde-cache))
  value)
  

(provide 'tramp2-cache)

;;; tramp2-cache.el ends here
