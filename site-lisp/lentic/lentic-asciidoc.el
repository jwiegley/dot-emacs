;;; lentic-asciidoc.el --- asciidoc support for lentic -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

;; The contents of this file are subject to the GPL License, Version 3.0.
;;
;; Copyright (C) 2014,2015,2016, Phillip Lord, Newcastle University
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Lentic buffers with asciidoc [source] blocks.

;;; Code:

;; #+begin_src emacs-lisp
(require 'lentic)
(require 'lentic-chunk)
(require 'm-buffer)
(require 'f)

(defun lentic-asciidoc-oset (conf)
  (lentic-m-oset
   conf
   :this-buffer (current-buffer)
   :comment ";; "))

(defun lentic-asciidoc-commented-new ()
  (lentic-asciidoc-oset
   (lentic-commented-asciidoc-configuration
    "lb-commented-clojure asciidoc"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name)) ".adoc"))))

;;;###autoload
(defun lentic-clojure-asciidoc-init ()
  (lentic-asciidoc-commented-new))

(add-to-list 'lentic-init-functions
             'lentic-clojure-asciidoc-init)

(defun lentic-asciidoc-uncommented-new ()
  (lentic-asciidoc-oset
   (lentic-uncommented-asciidoc-configuration
    "lb-uncommented-clojure-asciidoc"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name)) ".clj"))))

;;;###autoload
(defun lentic-asciidoc-clojure-init ()
  (lentic-asciidoc-uncommented-new))

;;;###autoload
(add-to-list 'lentic-init-functions
             'lentic-asciidoc-clojure-init)


;; ** Support Emacs-Lisp
;;;###autoload
(defun lentic-asciidoc-el-init ()
  (lentic-asciidoc-oset
   (lentic-uncommented-asciidoc-configuration
    "temp"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name)) ".el"))))

;;;###autoload
(add-to-list 'lentic-init-functions
             'lentic-asciidoc-el-init)


(defclass lentic-commented-asciidoc-configuration
  (lentic-commented-chunk-configuration)
  ((srctags :initarg :srctags
            :documentation "Language tags in source chunk"
            :initform '("clojure" "lisp")))
  "Lentic buffer config for asciidoc and other code.")

(defclass lentic-uncommented-asciidoc-configuration
  (lentic-uncommented-chunk-configuration)
  ((srctags :initarg :srctags
            :documentation "Language tags in source chunk"
            :initform '("clojure" "lisp")))
  "Lentic buffer config for asciidoc and other code")


(defun lentic-splitter (l)
  "Returns a function which for use as a partition predicate.
The returned function returns the first element of L until it is
passed a value higher than the first element, then it returns the
second element and so on."
  #'(lambda (x)
      (when
          (and l
               (< (car l) x))
        (setq l (-drop 1 l)))
      (car l)))

(defun lentic-partition-after-source (l-source l-dots)
  "Given a set of markers l-source, partition the markers in
l-dots.

The source markers represent [source] markers, so we take the
next matches to \"....\" immediately after a [source] marker.
This should remove other \"....\" matches.
"
  (-partition-by
   (lentic-splitter l-source)
   (-drop-while
    (lambda (x)
      (and l-source
           (< x (car l-source))))
    l-dots)))

(defun lentic-chunk-match-asciidoc
  (conf buffer)
  (let* ((source
          (m-buffer-match-begin
           buffer
           (format ";* *\\[source,%s\\]"
                   (regexp-opt
                    (oref conf :srctags)))))
         ;; this could also be a start of title
         (dots
          (m-buffer-match buffer
                          "^;* *----"))
         (source-start
          (lentic-partition-after-source
           source
           (m-buffer-match-begin
            dots)))
         (source-end
          (lentic-partition-after-source
           source (m-buffer-match-end dots))))
    (when source
      (list
       (-map 'cadr source-start)
       (-map 'car source-end)))))

(defmethod lentic-chunk-match
  ((conf lentic-commented-asciidoc-configuration) buffer)
  (lentic-chunk-match-asciidoc conf buffer))

(defmethod lentic-chunk-match
  ((conf lentic-uncommented-asciidoc-configuration) buffer)
  (lentic-chunk-match-asciidoc conf buffer))

(defmethod lentic-invert
  ((conf lentic-commented-asciidoc-configuration))
  (lentic-m-oset (lentic-asciidoc-uncommented-new)
                 :that-buffer (lentic-this conf)))

(defmethod lentic-invert
  ((conf lentic-uncommented-asciidoc-configuration))
  (lentic-m-oset (lentic-asciidoc-commented-new)
                 :that-buffer (lentic-this conf)))

(provide 'lentic-asciidoc)
;;; lentic-asciidoc.el ends here

;; #+end_src
