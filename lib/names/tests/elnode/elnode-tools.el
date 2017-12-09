;;; elnode-tools.el --- dev tools for elnode -*- lexical-binding: t -*-

;; Copyright (C) 2014  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Keywords: lisp

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

;; Just some tools to help debug and improve elnode

;;; Code:

(require 'elp)
(require 'elnode)
(require 'dash)
(require 'profiler)
(require 'cl-macs)

(defun process-sentinel-set (proc func)
  (set-process-sentinel proc func)
  proc)

(defvar elnode-elp-do-profiler nil)

(defun elnode-elp-handler (httpcon)
  (let ((elnode-webserver-visit-file t))
    (elnode-docroot-for "~/sources/emacs/etc/"
        :with file
        :on httpcon
        :do (elnode-send-file httpcon file))))

(defun elnode-elp (&optional port)
  (interactive
   (list
    (when current-prefix-arg
      (string-to-number
       (read-from-minibuffer "port to hit: ")))))
  (let ((sock (or port 8001))
        (elnode--do-error-logging :status))
    (unless (kva sock elnode-server-socket)
      (elnode-start 'elnode-elp-handler :port 8001))
    (let ((elnode--do-error-logging :warning))
      (when elnode-elp-do-profiler
        (profiler-stop)
        (profiler-start 'cpu))
      (elp-reset-all)
      (elp-instrument-package "elnode")
      (elp-instrument-package "kv")
      (elp-instrument-package "process")
      (elp-instrument-package "set-process")
      (let (fin)
        (switch-to-buffer
         (process-buffer
          (process-sentinel-set
           (start-process-shell-command
            "elnode-ab" "elnode-ab"
            (format
             (concat
              "ab -r -n 4000 -c 200 -s 20 "
              "http://127.0.0.1:%s/COPYING "
              " > /tmp/elnode-elp-101.txt") sock))
           (lambda (proc status) (setq fin t)))))
        (while (not fin) (sleep-for 20))
        (when elnode-elp-do-profiler
          (profiler-report)
          (profiler-stop))
        (when (get-buffer "elnode-elp-101.txt")
          (with-current-buffer (get-buffer "elnode-elp-101.txt")
            (set-buffer-modified-p nil)))
        (find-file "/tmp/elnode-elp-101.txt")
        (elp-results)
        (elp-reset-all)))))

(defun elnode-check-request-buffers ()
  (interactive)
  (noflet ((request-buffers ()
             (->> (buffer-list)
               (-filter
                (lambda (b) (string-match " \\*elnode.*" (buffer-name b)))))))
    (let ((before (request-buffers)))
      (-each (request-buffers) (lambda (b) (kill-buffer b)))
      (message "request buffers: %d > %d"
               (length before)
               (length (request-buffers))))))


(provide 'elnode-tools)

;;; elnode-tools.el ends here
