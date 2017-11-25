;;; pfuture.el --- a simple wrapper around asynchronous processes -*- lexical-binding: t -*-

;; Copyright (C) 2017 Alexander Miller

;; Author: Alexander Miller <alexanderm@web.de>
;; Homepage: https://github.com/Alexander-Miller/pfuture
;; Package-Requires: ((emacs "24.4"))
;; Version: 1.2.1

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

(require 'cl-lib)

;;;###autoload
(defun pfuture-new (cmd &rest cmd-args)
  "Create a new future process for command CMD and arguments CMD-ARGS.
This will return a process object with one additional 'result property which
can be read via \(process-get process 'result\) or alternatively with
\(pfuture-result process\).

Note that CMD-ARGS must be a *sequence* of strings, such that
this is wrong: (pfuture-new \"git status\")
this is right: (pfuture-new \"git\" \"status\")"
  (let* ((process (apply #'start-process "Process Future" nil cmd cmd-args)))
    (process-put process 'result "")
    (set-process-filter
     process
     (lambda (pr msg)
       (process-put
        pr 'result
        (concat (process-get pr 'result) msg))))
    process))

(cl-defun pfuture-await (process &key (timeout 1) (just-this-one t))
  "Block until PROCESS has produced output and return it.

Will accept the following optional keyword arguments:

TIMEOUT: The timeout in seconds to wait for the process. May be a float to
specify fractional number of seconds. In case of a timeout nil will be returned.

JUST-THIS-ONE: When t only read from the process of FUTURE and no other. For
details see documentation of `accept-process-output'."
  (let (inhibit-quit)
    (accept-process-output
     process timeout nil just-this-one))
  (process-get process 'result))

(defun pfuture-await-to-finish (process)
  "Keep reading the output of PROCESS until it is done.
Same as `pfuture-await', but will keep reading (and blocking) so long as the
process is *alive*.

If the process never quits this method will block forever. Use with caution!"
  (let (inhibit-quit)
    (accept-process-output process nil nil t)
    (while (process-live-p process)
      (accept-process-output process nil nil t)))
  (process-get process 'result))

(defsubst pfuture-result (process)
  "Return the output of PROCESS."
  (process-get process 'result))

(provide 'pfuture)

;;; pfuture.el ends here
