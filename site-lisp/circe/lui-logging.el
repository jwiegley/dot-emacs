;;; lui-logging.el --- Logging support for lui

;; Copyright (C) 2006  Jorgen Schaefer,
;;               2012  Anthony Martinez

;; Author: Anthony Martinez <pi+circe@pihost.us>

;; This file is part of Lui.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301  USA

;;; Commentary:

;; This lui module enables logging. Lui applications can change the
;; values of `lui-logging-format-arguments' to provide further
;; possibilities of customizing `lui-logging-file-format' for users.

;;; Code:

(require 'lui-format)
(require 'url-util)

(defgroup lui-logging nil
  "Logging support."
  :prefix "lui-logging-"
  :group 'lui)

(defcustom lui-logging-format "[%T] {text}"
  "The format used for log file entries.
This is first passed through `format-time-string' and then through
`lui-format'. The following format strings exist:

  {text} - the text to be logged"
  :type 'string
  :group 'lui-logging)

(defcustom lui-logging-directory "~/.logs"
  "The directory where log files are stored."
  :type 'directory
  :group 'lui-logging)

(defcustom lui-logging-file-format "{buffer}_%Y-%m-%d.txt"
  "The format to be used for the log file name.
This is first passed through `format-time-string', and then
through `lui-format'. Possible lui format strings are:

  {buffer} - the buffer name where the logging happened.

Lui applications can provide further format strings. See
`lui-logging-format-arguments' in the appropriate buffer."
  :type 'string
  :group 'lui-logging)

(defcustom lui-logging-flush-delay 0
  "The number of seconds to delay writing newly-received messages
to disk. This can increase performance/decrease IO-wait at the
cost of a little bit of safety."
  :type 'integer
  :group 'lui-logging)

(defvar lui-logging-format-arguments nil
  "A list of arguments to be passed to `lui-format'.
This can be used to extend the formatting possibilities of the
file name for lui applications.")
(make-variable-buffer-local 'lui-logging-format-arguments)

(defvar lui-logging-file-name-unreserved-chars
  ;; All but '/' is fine actually, but also omit '%' because otherwise there's
  ;; ambiguity between one introduced by encoding and a literal one.
  '(?! ?\" ?# ?$ ?& ?` ?\( ?\) ?* ?+ ?,?: ?\; ?< ?= ?> ?? ?@?\[ ?\\ ?\] ?^ ?`
       ?\{ ?| ?\})
  "A list of characters that should not be percent-encoded by
`url-hexify-string' while generating a logging file name.")

(defvar lui-pending-logs
  (make-hash-table :test 'equal)
  "Storage for log messages awaiting write. It is structured as a
hash table mapping filenames to a list-of-strings, which serves as
a queue.")

(defvar lui-logging-timer nil
  "The timer used to flush lui-logged buffers")

(defun lui-logging-delayed-p ()
  (> lui-logging-flush-delay 0))

(defun enable-lui-logging ()
  "Enable lui logging for this buffer. Also create the log
file's directory, should it not exist."
  (interactive)
  (add-hook 'lui-pre-output-hook 'lui-logging
            nil t))

(defun disable-lui-logging ()
  "Disable lui logging for this buffer, and flush any pending
logs to disk."
  (interactive)
  (remove-hook 'lui-pre-output-hook 'lui-logging t)
  (lui-logging-flush))

(defun enable-lui-logging-globally ()
  "Enable lui logging for all Lui buffers.

This affects current as well as future buffers."
  (interactive)
  (add-hook 'lui-mode-hook 'enable-lui-logging)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when lui-input-marker
        (enable-lui-logging)))))

(defun disable-lui-logging-globally ()
  "Disable logging in all future Lui buffers.

This affects current as well as future buffers."
  (interactive)
  (remove-hook 'lui-mode-hook 'enable-lui-logging)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when lui-input-marker
        (disable-lui-logging)))))

(defun lui-logging-file-name ()
  "Create the name of the log file based on `lui-logging-file-format'."
  (let* ((time-formatted (format-time-string lui-logging-file-format))
         (buffer (let ((url-unreserved-chars
                        (append url-unreserved-chars
                                lui-logging-file-name-unreserved-chars))
                       (downcased (downcase (buffer-name (current-buffer)))))
                   (url-hexify-string downcased)))
         (filename (apply 'lui-format
                          time-formatted
                          :buffer buffer
                          lui-logging-format-arguments)))
    (concat lui-logging-directory "/" filename)))

(defun lui-logging-flush ()
  "Flush out the lui-logging queue, and clear the timer set by
`lui-logging'."
  (maphash #'lui-logging-flush-file lui-pending-logs)
  (clrhash lui-pending-logs)
  (cancel-timer lui-logging-timer)
  (setq lui-logging-timer nil))

(defun lui-logging-write-to-log (file-name content)
  "Actually perform a write to the logfile."
  (let ((coding-system-for-write 'raw-text)
        (dir (file-name-directory file-name)))
    (when (not (file-directory-p dir))
      (make-directory dir t))
    (write-region content nil file-name t 'nomessage)))

(defun lui-logging-flush-file (file-name queue)
  "Consume the logging queue and write the content to the log
file."
  (let ((content (apply #'concat (nreverse queue))))
    (lui-logging-write-to-log file-name content)))

(defun lui-logging-format-string (text)
  "Generate a string to be either directly written or enqueued."
  (substring-no-properties
   (lui-format
    (format-time-string lui-logging-format)
    :text text)))

(defun lui-logging-enqueue (file-name text)
  "Given a filename, push text onto its queue, and tickle the
timer, if necessary."
  (puthash file-name
           (cons text (gethash file-name lui-pending-logs))
           lui-pending-logs)
  (when (null lui-logging-timer)
    (setq lui-logging-timer
          (run-with-timer lui-logging-flush-delay nil
                          #'lui-logging-flush))))

(defun lui-logging ()
  "If output-queueing is enabled, append the to-be-logged string
to the output queue. Otherwise, write directly to the logfile.
This should be added to `lui-pre-output-hook' by way of
`enable-lui-logging'."
  (let ((text (lui-logging-format-string (buffer-string))))
    (if (lui-logging-delayed-p)
        (lui-logging-enqueue (lui-logging-file-name) text)
      (lui-logging-write-to-log (lui-logging-file-name) text))))

(provide 'lui-logging)
;;; lui-logging.el ends here
