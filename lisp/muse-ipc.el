;;; muse-ipc.el --- publish Muse documents from other processes

;; Copyright (C) 2009, 2010  Free Software Foundation, Inc.

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This file is still in alpha state.  Not for production use!

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Inter-Process Communication
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when-compile (require 'cl))

(require 'muse)
(require 'muse-publish)

(defgroup muse-ipc nil
  "Options controlling the behavior of Muse's IPC module."
  :group 'muse-publish)

(defcustom muse-ipc-timeout 60
  "Maximum time to wait for a client to respond."
  :group 'muse-ipc
  :type 'number)

(defcustom muse-ipc-ignore-done nil
  "If non-nil, ignore any 'done' messages that we get from clients."
  :group 'muse-ipc
  :type 'boolean)

(defvar muse-ipc-server-port nil
  "Port of the Emacs server.")

(defvar muse-ipc-server-process nil
  "Process of the Emacs server.")

(defvar muse-ipc-server-registered nil
  "Whether we have successfully registered our port with the client.")

(defun muse-ipc-init-filter (proc string)
  "Handle data from client while initiating a connection."
  (unless muse-ipc-server-registered
    (when (string-match "\\`ok$" string)
      (setq muse-ipc-server-registered t))))

(defun muse-ipc-delete-client (proc)
  "Delete a client."
  (let ((buffer (process-get proc :buffer)))
    (when (and buffer (buffer-live-p buffer))
      (with-current-buffer buffer
        (set-buffer-modified-p nil))
      (kill-buffer buffer)))
  (when (eq (process-status proc) 'open)
    (delete-process proc)))

(defun* muse-ipc-server-filter (proc string)
  "Handle data from a client after it connects."
  ;; Authenticate
  (unless (process-get proc :authenticated)
    (if (and (string-match "\\`begin \\(.+\\)$" string)
             (equal (match-string 1 string)
                    (process-get proc :shared-secret)))
        (progn
          (setq string (substring string (match-end 0)))
          (process-put proc :authenticated t)
          (process-send-string proc "ok\n"))
      (process-send-string proc "nok\n")
      (delete-process proc))
    (return-from muse-ipc-server-filter))

  ;; Handle case where the client is sending data to be published
  (when (process-get proc :sending-data)
    (with-current-buffer (process-get proc :buffer)
      (insert string)
      (let ((buf-len (1- (point)))
            (expected-len (process-get proc :data-bytes)))
        (cond ((= buf-len expected-len)
               (process-put proc :sending-data nil))
              ((> buf-len expected-len)
               (process-send-string proc "nok\n")
               (muse-ipc-delete-client proc)))))
    (return-from muse-ipc-server-filter))

  ;; Dispatch commands
  (cond
   ((string-match "\\`done$" string)
    ;; done, close the server
    (unless muse-ipc-ignore-done
      (muse-ipc-stop-server)))

   ((string-match "\\`name \\(.+\\)$" string)
    ;; set name
    (process-put proc :file-name (match-string 1 string))
    (process-send-string proc "ok\n"))

   ((string-match "\\`title \\(.+\\)$" string)
    ;; set title
    (process-put proc :title (match-string 1 string))
    (process-send-string proc "ok\n"))

   (t
    ;; unrecognized command
    (process-send-string proc "nok\n"))))

(defun muse-ipc-stop-server ()
  "Stop Muse IPC server and reset connection data."
  (stop-process muse-ipc-server-process)
  (delete-process muse-ipc-server-process)
  (setq muse-ipc-server-port nil)
  (setq muse-ipc-server-process nil))

(defun muse-ipc-start (shared-secret publish-fn client-port &optional server-port)
  "Start an IPC connection and send a response to CLIENT-PORT.
If SERVER-PORT is provided, start the IPC server on that port, otherwise
choose a random port.

SHARED-SECRET is used as a very minimal security measure to
authenticate the Muse IPC server during initialization, and also
any incoming clients once the server is started.

PUBLISH-FN is the function which should be called in buffer of
the received contents.  It should transform the buffer into a
published state.  It must take at least two arguments.  The first
argument is the full path of the file that the contents
correspond with.  The second argument is the title to use when
publishing the file."
  (when (stringp client-port)
    (setq client-port (string-to-number client-port)))
  (when (stringp server-port)
    (setq server-port (string-to-number server-port)))
  (setq muse-ipc-server-process
        (make-network-process
         :name "muse-ipc"
         :buffer nil
         :host 'local :service (or server-port t)
         :server t :noquery t :nowait t
         :plist (list :authenticated nil :shared-secret shared-secret
                      :publish-fn publish-fn)
         :filter 'muse-ipc-server-filter))
  (unless muse-ipc-server-process
    (error "Error: Could not start Muse IPC Server process"))
  (set-process-coding-system muse-ipc-server-process
                             'raw-text-unix 'raw-text-unix)
  (setq muse-ipc-server-port
        (number-to-string
         (cadr (process-contact muse-ipc-server-process))))
  (let ((client-proc
         (make-network-process
          :name "muse-ipc-client"
          :buffer nil
          :host 'local :service client-port
          :noquery t
          :filter 'muse-ipc-init-filter)))
    (setq muse-ipc-server-registered nil)
    (process-send-string client-proc
                         (concat "begin " shared-secret "\n"))
    (accept-process-output client-proc muse-ipc-timeout nil t)
    (unless muse-ipc-server-registered
      (error "Error: Did not register listener"))
    (process-send-string client-proc
                         (concat "port " muse-ipc-server-port "\n"))
    (stop-process client-proc)
    (delete-process client-proc))

  ;; Accept process output until the server dies
  (while muse-ipc-server-process (accept-process-output nil 1)))

(provide 'muse-ipc)

;;; muse-ipc.el ends here
