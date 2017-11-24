;;; noisy-change.el --- Make changes noisily -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014, 2016, Phillip Lord, Newcastle University

;; This program is free software: you can redistribute it and/or modify
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

;; Make changes noisily. This is useful for developing lentic.

(defvar noisy-change-log nil)
(make-variable-buffer-local 'noisy-change-log)

(defun noisy-change-toggle ()
  (interactive)
  (if noisy-change-log
      (progn (setq noisy-change-log nil)
             (message "Noise-change off"))
    (setq noisy-change-log t)
    (message "noisy-change on")))

(defmacro noisy-change-log (&rest rest)
  "Log REST."
  `(when noisy-change-log
     (with-current-buffer
         (get-buffer-create "*noisy-change-log*")
       (goto-char (point-max))
       (insert
        (concat
         (format ,@rest)
         "\n")))))

(defvar noisy-change-last-bcf nil)

(defun noisy-change-before-function (start stop)
  (setq noisy-change-last-bcf '(start . stop))
  (noisy-change-log "before(%s,%s,%s)" start stop this-command))

(defun noisy-change-after-function (start stop length)
  (when
      (and noisy-change-last-bcf
           (and (< 0 length)
                (not (= start stop))))
    (noisy-change-log "Skew Detected"))
  (noisy-change-log "after(%s,%s,%s,%s)" start stop length
                    this-command))

(add-hook 'before-change-functions
          'noisy-change-before-function)

(add-hook 'after-change-functions
          'noisy-change-after-function)

;; Local Variables:
;; no-update-autoloads: t
;; End:
