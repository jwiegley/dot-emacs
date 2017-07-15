;;; esh-client.el --- Communicate with a daemon running ESH  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: faces, tools

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'server) ;; That's Emacs' server

(defconst esh-client--server-name "esh--server")
(defconst esh-client--init-file-name "esh-init.el")

(defconst esh-client--script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst esh-client--script-directory
  (file-name-directory esh-client--script-full-path)
  "Full path to directory of this script.")

(defvar esh-client-use-cask t
  "Whether to start the server with Cask-supplied environment variables.")

(defvar esh-client-pass-Q-to-server t
  "Whether to pass -Q to the server.")

(defvar esh-client-debug-server nil
  "Whether to print backtraces produced by the server.")

(defvar esh-client-debug-client nil
  "Whether to print debugging information on the client side.")

(defvar esh-client--initialized nil
  "Whether the server was (re)initialized.")

;;; Utils

(defun esh-client--debug (&rest args)
  "Call `message' on ARGS if `esh-client-debug-client' is set."
  (when esh-client-debug-client
    (apply #'message args)))

(defun esh-client--server-running-p ()
  "Check if the ESH server is running."
  (let* ((socket-dir (if server-use-tcp server-auth-dir server-socket-dir))
         (socket-fname (expand-file-name esh-client--server-name socket-dir))
         (socket-exists (file-exists-p socket-fname)))
    (esh-client--debug "::server-running-p: %S %s" socket-exists socket-fname)
    (and socket-exists socket-fname)))

(defun esh-client--wait-for-exit (proc)
  "Wait for PROC to exit."
  (while (process-live-p proc)
    (accept-process-output proc 0.010)))

(defun esh-client-stderr (&rest args)
  "Like `message' on ARGS, but don't print a final newline.
Also, don't interact in weird ways with `message' (bug #24157)."
  (princ (apply #'format args) #'external-debugging-output))

(defmacro esh-client--with-progress-msg (msg &rest body)
  "Display MSG before running BODY, then display ‘done.’."
  (declare (indent 1) (debug t))
  `(progn
     (esh-client-stderr "%s:\n" ,msg)
     (prog1 ,@body
       (esh-client-stderr "  done.\n"))))

(defun esh-client--princ (arg)
  "Call `princ' on ARG, if non-nil."
  (when arg (princ arg)))

;;; RPC forms

(defun esh-client--rpc-eval-form (form dest)
  "Construct a form to eval FORM on server.
Output of FORM is saved to DEST.  `esh-server' is required here
instead of when starting the server due to the better error
reporting (see docstring of `esh-client--ensure-server-1');
requiring it here also allows us to set `load-prefer-newer'
first, guaranteeing that we don't get a stale copy of ESH."
  `(progn
     (setq-default load-prefer-newer t)
     (require 'esh-server)
     (esh-server-eval ',form ,dest ,esh-client-debug-server)))

(defun esh-client--rpc-server-init-form (display &optional init-info)
  "Construct a form to initialize the ESH server.
DISPLAY and INIT-INFO are forwarded."
  `(progn
     (esh-server-init ,display ',init-info)))

(defun esh-client--rpc-process-form (in-path out-path in-type out-type)
  "Construct a form to process arguments on server.
IN-PATH, OUT-PATH, IN-TYPE, OUT-TYPE: see `esh-server-process'."
  `(esh-server-process ,in-path ,out-path ',in-type ',out-type))

;;; Running forms on server

(defun esh-client--run-1 (form)
  "Start client process for FORM.
Errors in client's output are signaled."
  (with-temp-buffer
    (let ((proc (start-process "client" (current-buffer)
                               "emacsclient" "-s" esh-client--server-name
                               "--eval" (prin1-to-string form))))
      (esh-client--wait-for-exit proc)
      (esh-client--die-if-rpc-failed))))

(defun esh-client--die-if-rpc-failed ()
  "Check if client response is *ERROR*, and throw if so.
This should only happen for very early errors, such as errors
while loading `esh-server'.  Other errors are captured and
properly returned by the server."
  (goto-char (point-min))
  (when (looking-at-p "\\*ERROR\\*:")
    (error "%s" (buffer-string))))

(defconst esh-client--backtrace-msg
  ">> Run esh2tex again with --debug-on-error to see the full stack trace. <<")

(defun esh-client--read-server-response (fpath)
  "Read server response from FPATH."
  (with-temp-buffer
    (insert-file-contents fpath)
    (pcase (read (buffer-string))
      (`(success ,retv) retv)
      (`(error ,err ,backtrace)
       (setq debug-on-error nil)
       (error "ESH error: %S\n%s" err
              (if esh-client-debug-server backtrace esh-client--backtrace-msg))))))

(defun esh-client--run (form)
  "Run FORM on ESH server.
Result of FORM is printed to a temporary file, and read back by
client, to work around a bug in `emacsclient'."
  (esh-client--ensure-server)
  (let* ((fname (make-temp-name "esh-server-output"))
         (fpath (expand-file-name fname temporary-file-directory)))
    (unwind-protect
        (progn
          (esh-client--run-1 (esh-client--rpc-eval-form form fpath))
          (esh-client--read-server-response fpath))
      (ignore-errors (delete-file fpath)))))

;;; Server management

(defun esh-client--init-file-path ()
  "Find init file for current directory."
  (let* ((parent-dir (locate-dominating-file "." esh-client--init-file-name))
         (init-dir (or parent-dir user-emacs-directory))
         (fpath (expand-file-name esh-client--init-file-name init-dir)))
    (if (file-exists-p fpath)
        fpath
      ;; Fall back to default, guaranteed-to-exist config file
      (expand-file-name esh-client--init-file-name esh-client--script-directory))))

(defun esh-client--truncate-right (str threshold)
  "If STR is longer than THRESHOLD, truncate it from the left."
  (let ((len (length str)))
    (if (<= len threshold) str
      (concat "..." (substring str (- len threshold) len)))))

(defun esh-client--compute-init-info ()
  "Compute an initialization pair for the server.
This is a cons of (INIT-FILE . MTIME)."
  (let* ((init-fpath (esh-client--init-file-path))
         (mtime (when (and init-fpath (file-exists-p init-fpath))
                  (nth 5 (file-attributes init-fpath)))))
    (cons init-fpath mtime)))

(defun esh-client--restart-server-if-stale-init-file (server-init-info expected-init-info)
  "Kill server if init file is stale.
That is, if SERVER-INIT-INFO does not match EXPECTED-INIT-INFO."
  (unless (member server-init-info `(none ,expected-init-info))
    (esh-client-stderr "Stale init file on server (%s); restarting.\n"
             (car server-init-info))
    (esh-client-kill-server)
    (esh-client--ensure-server)))

(defun esh-client--init-server ()
  "Initialize ESH server."
  (setq esh-client--initialized t)
  (let* ((init-info (esh-client--compute-init-info))
         (server-init-info (esh-client--run 'esh-server-init-info)))
    (esh-client--restart-server-if-stale-init-file server-init-info init-info)
    (unless (equal server-init-info init-info)
      (esh-client--with-progress-msg
       (format "Loading %S" (esh-client--truncate-right (car init-info) 40))
       (esh-client--run (esh-client--rpc-server-init-form (getenv "DISPLAY") init-info))))))

(defun esh-client--find-emacs ()
  "Find Emacs binary."
  (or (getenv "EMACS") "emacs"))

(defun esh-client--cask-path (kind)
  "Query Cask to determine value of path KIND."
  (with-temp-buffer
    (unless (eq (call-process "cask" nil (current-buffer) nil kind) 0)
      (error "Failed to run cask %s" kind))
    (replace-regexp-in-string "[\r\n]+" "" (buffer-string) t t)))

(defun esh-client--process-environment ()
  "Compute appropriate process environment for server."
  (let ((env process-environment))
    (when (and esh-client-use-cask (file-exists-p "Cask") (executable-find "cask"))
      (push (concat "PATH=" (esh-client--cask-path "path")) env)
      (push (concat "EMACSLOADPATH=" (esh-client--cask-path "load-path")) env))
    env))

(defun esh-client--ensure-server-1 ()
  "Start server process.
This passes a -L arg to make it possible to load `esh-server',
but it doesn't load it immediately (neither with -l or with
--eval): errors while loading the daemon cause it to never
return.  Instead, the client passes (require 'esh-server) before
each `esh-server-eval' query."
  (when (and (eq system-type 'windows) (< emacs-major-version 25))
    (error "ESH needs Emacs 25 to run on Windows"))
  (let* ((process-environment (esh-client--process-environment))
         (server-name-form `(setq server-name ,esh-client--server-name))
         (emacs-cmdline `(,(esh-client--find-emacs) ,@(when esh-client-pass-Q-to-server '("-Q"))
                          "-L" ,esh-client--script-directory ;; no -l esh-server
                          "--eval" ,(prin1-to-string server-name-form)
                          "--daemon")))
    (esh-client--debug "::ensure-server-1: %S" emacs-cmdline)
    (apply #'start-process "server" nil emacs-cmdline)))

(defun esh-client--ensure-server ()
  "Ensure that an ESH server is running."
  (unless (esh-client--server-running-p)
    (esh-client--with-progress-msg "Starting ESH"
      (if (eq system-type 'windows-nt)
          (progn
            ;; On Windows, --daemon doesn't fork
            (accept-process-output (esh-client--ensure-server-1) 0.010 nil 1)
            (sit-for 0.50 t))
        (esh-client--wait-for-exit (esh-client--ensure-server-1)))))
  (unless esh-client--initialized
    (esh-client--init-server)))

(defun esh-client-kill-server ()
  "Kill the ESH server."
  (interactive)
  (let ((socket-fname (esh-client--server-running-p))
        (delete-by-moving-to-trash nil))
    (when socket-fname
      (unwind-protect
          ;; Use `esh-client--run-1' instead of `server-eval-at', because the latter
          ;; creates a visible frame on Windows while it runs.
          (esh-client--run-1 '(kill-emacs))
        (ignore-errors (delete-file socket-fname))))))

;;; Main entry point

(defun esh-client-process-one (in-path out-path in-type out-type)
  "Call the PROCESS method on the ESH server.
IN-PATH, OUT-PATH, IN-TYPE, OUT-TYPE: see `esh-server-process'.

This function starts an Emacs daemon, and runs the latexification
code on it.  If a daemon is available, it is reused.  Originally,
the only reason a daemon was needed was that it's hard to make
Emacs' initial frame invisible.  Now, it's also used to make
things faster."
  (esh-client--ensure-server) ;; To prevent progress messages from interleaving
  (esh-client--with-progress-msg
      (format "Highlighting %S (writing to %S)" in-path (or out-path 'stdout))
    (setq in-path (expand-file-name in-path))
    (setq out-path (and out-path (expand-file-name out-path)))
    (esh-client--princ (esh-client--run (esh-client--rpc-process-form in-path out-path in-type out-type)))))

;; Local Variables:
;; checkdoc-arguments-in-order-flag: nil
;; End:

(provide 'esh-client)
;;; esh-client.el ends here
