;;; anvil-ext.el --- Extensions and fixes for anvil -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Created: 11 Jul 2026
;; Version: 0.1.0
;; Package-Requires: ((emacs "29.1"))
;; Keywords: processes tools

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;;; Commentary:

;; Fixes for the anvil worker pool's socket discovery, which as shipped
;; is coupled to the user's `server-socket-dir':
;;
;; - `anvil-worker--server-file' derives worker socket paths from
;;   `server-socket-dir' at pool-init time, but workers are spawned
;;   with -Q and so bind their sockets in the *default* socket
;;   directory, not the customized one.
;;
;; - `anvil-worker--server-file-stale-p' passes only the socket's
;;   basename to `server-running-p', which re-expands it against the
;;   *current* `server-socket-dir'.  Since init.org customizes
;;   `server-socket-dir' after `anvil-enable' has cached the pool's
;;   paths, the stale check always fails, deletes the socket file of
;;   every healthy worker, and orphans the daemon — leaving the pool
;;   respawning replacements forever and accumulating zombie Emacs
;;   processes.
;;
;; This file decouples the pool from `server-socket-dir' entirely:
;;
;; 1. Worker sockets live in a dedicated directory,
;;    `anvil-ext-worker-socket-dir'.
;; 2. The generated worker init file binds the worker's server socket
;;    there explicitly, so parent and worker always agree.
;; 3. The stale check probes the cached socket path itself instead of
;;    re-deriving a path from global state.
;; 4. A spawn grace period stops the health timer (or an overlapping
;;    second `anvil-enable') from spawning a same-named twin daemon
;;    while a worker is still starting up; twins fight over one socket
;;    path and orphan each other.
;;
;; Load this before `anvil-enable' so the path override is in effect
;; when the pool caches its socket paths.
;;
;; The same bugs are also fixed at the source in the Nix packaging
;; (~/src/nix/overlays/emacs/patches/anvil-worker-pool.patch), which
;; propagates the pool's cached socket directory to workers rather
;; than relocating sockets.  These advices are compatible with the
;; patched build — the dedicated directory simply becomes the cached
;; directory — and keep sessions on unpatched builds safe.  Once every
;; machine runs the patched build, the worker-pool advices can be
;; dropped.  The `anvil-server-dispatch-timeout' setting, dedicated-
;; directory preference, and server-id alias below are independent
;; configuration and remain useful.

;;; Code:

(require 'server)
(require 'cl-lib)
(require 'anvil-server)
(require 'anvil-worker)

(defvar anvil-server-id "anvil")

;; Register every module in one canonical table before `anvil-enable' runs.
;; `init.org' configures the legacy real id `emacs-eval'; clients use the
;; stable virtual id `anvil', which resolves to whichever real id the user has
;; configured.  Do not assign the defcustom here: loading this library must not
;; overwrite a user's Anvil configuration.
(cl-pushnew (cons "anvil" anvil-server-id)
            anvil-server-id-aliases :test #'equal)

(defgroup anvil-ext nil
  "Extensions and fixes for anvil."
  :group 'anvil
  :prefix "anvil-ext-")

(defcustom anvil-ext-worker-socket-dir
  (expand-file-name "anvil-workers" temporary-file-directory)
  "Directory holding anvil worker daemon sockets.
Deliberately independent of `server-socket-dir' so that
customizing the user-facing Emacs server cannot strand the worker
pool.  Keep the path short: Unix socket paths are limited to ~104
bytes on macOS."
  :type 'directory
  :group 'anvil-ext)

(defcustom anvil-ext-worker-spawn-grace 45
  "Seconds after spawning a worker before it may be respawned.
Longer than one `anvil-worker-health-check-interval' so a worker
still loading its init file is not declared dead and doubled by
the next health tick."
  :type 'integer
  :group 'anvil-ext)

(defun anvil-ext--ensure-socket-dir ()
  "Create `anvil-ext-worker-socket-dir' if needed; return its expansion.
The Emacs server refuses sockets in directories that are not owned
and 0700, so enforce that here rather than trusting the umask."
  (let ((dir (expand-file-name anvil-ext-worker-socket-dir)))
    (unless (file-directory-p dir)
      (make-directory dir t))
    (set-file-modes dir #o700)
    dir))

;;; Worker socket paths under the dedicated directory

(defun anvil-ext--worker-server-file (lane index)
  "Return the socket path for worker LANE/INDEX under the dedicated dir."
  (expand-file-name (anvil-worker--name lane index)
                    (anvil-ext--ensure-socket-dir)))

(advice-add 'anvil-worker--server-file
            :override #'anvil-ext--worker-server-file)

;;; Stale check against the cached path itself

(defun anvil-ext--server-file-stale-p (server-file)
  "Return non-nil if no live server is listening at SERVER-FILE.
Probes SERVER-FILE directly; workers always use local sockets
here (the generated init forces `server-use-tcp' nil), so the
original's TCP auth-file branch is unnecessary."
  (condition-case nil
      (progn
        (delete-process
         (make-network-process :name "anvil-ext-stale-check"
                               :family 'local :server nil :noquery t
                               :service server-file))
        nil)
    (file-error t)))

(advice-add 'anvil-worker--server-file-stale-p
            :override #'anvil-ext--server-file-stale-p)

;;; Point spawned workers at the dedicated directory

(defun anvil-ext--worker-init-file (orig &rest args)
  "Add socket-directory setup to the worker init file written by ORIG.
The stock init file leaves a -Q worker binding its socket in the
default socket directory; insert forms directly after the header
line so it binds under `anvil-ext-worker-socket-dir', where the
pool looks for it."
  (let ((init-file (apply orig args))
        (dir (anvil-ext--ensure-socket-dir)))
    (with-temp-buffer
      (insert-file-contents init-file)
      (goto-char (point-min))
      (forward-line 1)
      (insert "\n(require 'server)\n"
              "(setq server-use-tcp nil)\n"
              (format "(setq server-socket-dir %S)\n" dir))
      (let ((coding-system-for-write 'utf-8-unix))
        (write-region (point-min) (point-max) init-file nil 'silent)))
    init-file))

(advice-add 'anvil-worker--generate-init-file
            :around #'anvil-ext--worker-init-file)

;;; Spawn grace period

(defvar anvil-ext--worker-spawn-times (make-hash-table :test #'equal)
  "Worker name → `float-time' of the most recent spawn attempt.
Keyed by name rather than stored in the worker plist so the record
survives `anvil-worker--init-pool' discarding pool state.")

(defun anvil-ext--spawn-with-grace (orig worker)
  "Call ORIG to spawn WORKER unless a recent spawn may still be starting."
  (let* ((name (plist-get worker :name))
         (last (gethash name anvil-ext--worker-spawn-times))
         (elapsed (and last (- (float-time) last))))
    (if (and elapsed (< elapsed anvil-ext-worker-spawn-grace))
        (progn
          (anvil-worker--log
           'spawn-suppressed
           (format "%s spawned %.1fs ago, within %ds grace"
                   name elapsed anvil-ext-worker-spawn-grace))
          nil)
      (puthash name (float-time) anvil-ext--worker-spawn-times)
      (funcall orig worker))))

(advice-add 'anvil-worker--spawn-worker
            :around #'anvil-ext--spawn-with-grace)

;;; Bound synchronous dispatch

;; The stdio bridge gives up on a request after 330 seconds; without a
;; server-side limit the daemon keeps executing the handler with the
;; editor frozen and no one listening for the answer.
(setq anvil-server-dispatch-timeout 270)

(provide 'anvil-ext)
;;; anvil-ext.el ends here
