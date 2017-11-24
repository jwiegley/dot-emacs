;;; lentic-cookie.el -- Lentic with a magic cookie -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>
;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2016, Phillip Lord, Newcastle University

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


;;; Code:

;; #+begin_src emacs-lisp

(require 'lentic)
(require 'lentic-chunk)

(defclass lentic-cookie-uncommented-configuration
  (lentic-configuration)
  ()
  :documentation "Configuration for a magic cookie containing
  lentic buffer that is not commented.")

(defun lentic-cookie--uncommented-fixup-first-line-1 (buffer first-line-end
                                                             comment)
  "Fixup the first line.

BUFFER is the buffer.
FIRST-LINE-END is the location of the end of the line.

BUFFER is the buffer *with* the comments rather than *without*
despite the name of the function!"
  (m-buffer-nil-marker
   (m-buffer-replace-match
    (m-buffer-match
     buffer
     (rx-to-string
      `(and line-start
            (or
             ;; the line may have been commented during the update
             ,comment
             ;; the line may have the comment from org-mode
             "# ")
            ;; and this is the actual start
            "#!"))
     :end first-line-end)
    "#!")))

(defun lentic-cookie-uncommented-fixup-first-line (conf first-line-end)
  "Fixup the first line.

CONF is the `lentic-configuration' object.
FIRST-LINE-END is the location of the end of the line."
  (lentic-cookie--uncommented-fixup-first-line-1
   (lentic-that conf) first-line-end
   (oref conf :comment)))

(defmethod lentic-clone
  ((conf lentic-cookie-uncommented-configuration)
   &optional start stop length-before
   start-converted stop-converted)
  (let ((clone-return
          (call-next-method conf start stop
                            length-before start-converted stop-converted)))
    (if (lentic-cookie-uncommented-fixup-first-line
         conf
         (cl-cadar
          (m-buffer-match-first-line
           (lentic-this conf)
           :numeric t)))
        nil
      clone-return)))

(defclass lentic-cookie-commented-configuration
  (lentic-configuration)
  ()
  :documentation "Configuration for magic cookie containing lentic file that is
  commented.")

(defun lentic-cookie--commented-fixup-first-line-1 (buffer first-line-end)
  "Fixup the first line.

BUFFER is the buffer.
FIRST-LINE-END is the location of the end of the line.

BUFFER is the buffer *without* the comments rather than *with*
despite the name of the function!"
  (m-buffer-nil-marker
   (m-buffer-replace-match
    (m-buffer-match
     buffer
     (rx
      (and line-start
           (0+ anything)
           "#!"))
     :end first-line-end)
    "# #!")))

(defun lentic-cookie-commented-fixup-first-line (conf first-line-end)
  "Fixup the first line.

CONF is the `lentic-configuration' object.
FIRST-LINE-END is the location of the end of the line."
  (lentic-cookie--commented-fixup-first-line-1
   (lentic-that conf) first-line-end))

(defmethod lentic-clone
  ((conf lentic-cookie-commented-configuration)
   &optional start stop length-before
   start-converted stop-converted)
  (let ((clone-return
          (call-next-method conf start stop
                            length-before start-converted stop-converted)))
    (if
        (or
         ;; next method has done strange things
         (not clone-return)
         ;; calling method is broad
         (not start)
         (not stop)
         (m-buffer-with-markers
             ((first-line
               (m-buffer-match-first-line
                (lentic-this conf))))
           (or
            (m-buffer-in-match-p
             first-line start)
            (m-buffer-in-match-p
             first-line stop))))
        (progn
          (lentic-cookie-commented-fixup-first-line
           conf
           (cl-cadar
            (m-buffer-match-first-line
             (lentic-this conf)
             :numeric t)))
          nil)
      clone-return)))


(defclass lentic-cookie-unmatched-uncommented-chunk-configuration
  (lentic-unmatched-uncommented-chunk-configuration
   lentic-cookie-uncommented-configuration)
  ())

(defmethod lentic-invert
  ((conf lentic-cookie-unmatched-uncommented-chunk-configuration))
  (lentic-cookie-unmatched-commented-chunk-configuration
   "temp4"
   ;; FIXME: Factor this out
   :this-buffer (lentic-that conf)
   :that-buffer (lentic-this conf)
   :comment (oref conf :comment)
   :comment-start (oref conf :comment-start)
   :comment-stop (oref conf :comment-stop)))

(defclass lentic-cookie-unmatched-commented-chunk-configuration
  (lentic-unmatched-commented-chunk-configuration
   lentic-cookie-commented-configuration)
  ())

(defmethod lentic-invert
  ((conf lentic-cookie-unmatched-commented-chunk-configuration))
  (lentic-cookie-unmatched-uncommented-chunk-configuration
   "temp2"
   ;; FIXME: Factor this out
   :this-buffer (lentic-that conf)
   :that-buffer (lentic-this conf)
   :comment (oref conf :comment)
   :comment-start (oref conf :comment-start)
   :comment-stop (oref conf :comment-stop)))

(provide 'lentic-cookie)
;;; lentic-cookie ends here
