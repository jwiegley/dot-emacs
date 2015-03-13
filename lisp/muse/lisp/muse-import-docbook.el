;;; muse-import-docbook.el --- convert Docbook XML into Muse format

;; Copyright (C) 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: Elena Pomohaci <e.pomohaci@gmail.com>

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

;; It works only for article type docbook docs and recognize
;; followings elements: article, sect1, sect2, sect3, title,

;;; Contributors:

;;; Code:

(require 'muse-import-xml)

(defvar muse-import-docbook-prefix "muse-import-docbook-"
  "The name prefix for tag functions")

(defvar muse-import-docbook-para-indent "\n\n"
  "Para elements indentation (0, less than 6 spaces, more than 6 spaces)")

(defun muse-import-docbook-reset-para-indent ()
  (setq muse-import-docbook-para-indent "\n\n"))


;;;###autoload
(defun muse-import-docbook (src dest)
  "Convert the Docbook buffer SRC to Muse, writing output in the DEST buffer."
  (interactive "bDocbook buffer:\nBMuse buffer:")
  (setq muse-import-xml-prefix muse-import-docbook-prefix)
  (setq muse-import-xml-generic-function-name "muse-import-xml-node")
  (muse-import-xml src dest))

;;;###autoload
(defun muse-import-docbook-files (src dest)
  "Convert the Docbook file SRC to Muse, writing output to the DEST file."
  (interactive "fDocbook file:\nFMuse file:")
  (with-temp-file dest
    (muse-import-docbook (find-file-noselect src) (current-buffer))))


;;; element specific functions

(defun muse-import-docbook-get-title (node)
  (let ((tit (car (xml-get-children node 'title))))
    (insert (car (cddr tit)) ?\n ?\n)
    (muse-import-xml-parse-tree (xml-node-children (remove tit node)))))


(defun muse-import-docbook-article (node)
  "Article conversion function"
  (muse-import-xml-node node))

(defun muse-import-docbook-articleinfo (node)
  "Article conversion function"
  (insert "#title ")
  (muse-import-docbook-get-title node)
  (insert ?\n))


(defalias 'muse-import-docbook-appendix 'muse-import-docbook-article)

(defalias 'muse-import-docbook-appendixinfo 'muse-import-docbook-articleinfo)


(defun muse-import-docbook-sect1 (node)
  "Section 1 conversion function"
  (insert ?\n "* ")
  (muse-import-docbook-get-title node))

(defun muse-import-docbook-sect2 (node)
  "Section 2 conversion function"
  (insert ?\n "** ")
  (muse-import-docbook-get-title node))

(defun muse-import-docbook-sect3 (node)
  "Section 3 conversion function"
  (insert ?\n "*** ")
  (muse-import-docbook-get-title node))


(defun muse-import-docbook-graphic (node)
  "Graphic conversion function. Image format is forced to PNG"
  (let ((name (xml-get-attribute node 'fileref)))
  (insert "\n[[img/" name ".png][" name "]]")))

(defun muse-import-docbook-para (node)
  (insert muse-import-docbook-para-indent)
  (muse-import-xml-node node))


(defun muse-import-docbook-emphasis (node)
  (insert "*")
  (muse-import-xml-node node)
  (insert "*"))

(defun muse-import-docbook-quote (node)
  (insert "\"")
  (muse-import-xml-node node)
  (insert "\""))

(defun muse-import-docbook-blockquote (node)
  (setq muse-import-docbook-para-indent "\n\n  ")
  (muse-import-xml-node node)
  (muse-import-docbook-reset-para-indent))

(defun muse-import-docbook-member (node)
  (insert "\n> ")
  (muse-import-xml-node node))

(defun muse-import-docbook-bridgehead (node)
  (insert "\n* ")
  (muse-import-xml-node node))

(provide 'muse-import-docbook)

;;; muse-import-docbook.el ends here
