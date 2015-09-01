;;; muse-import-xml.el --- common to all from-xml converters

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

;;; Contributors:

;;; Code:

(provide 'muse-import-xml)

(require 'xml)
(require 'muse)

(defvar muse-import-xml-prefix ""
  "The name prefix for tag functions")

(defvar muse-import-xml-generic-function-name "muse-import-xml-generic"
  "The generic function name")

(defun muse-import-xml-convert-to-list (buf)
  "Convert xml BUF in a xml-list"
  (with-temp-buffer
    (insert-buffer-substring buf)
    (goto-char (point-min))
    (while (re-search-forward ">[ \n\t]*<" nil t)
      (replace-match "><" nil nil)) ; clean all superfluous blank characters
    (xml-parse-region (point-min)
                      (point-max)
                      (current-buffer))))


(defun muse-import-xml-generic (node)
  "The generic function called when there is no node specific function."
  (let ((name (xml-node-name node)))
    (insert "<" (symbol-name name)  ">")
    (muse-import-xml-node node)
    (insert "</" (symbol-name name) ">")))

(defun muse-import-xml-parse-tree (lst)
  "Parse an xml tree list"
  (mapc #'muse-import-xml-parse-node lst))

(defun muse-import-xml-parse-node (node)
  "Parse a xml tree node"
  (if (stringp node)
      (insert (muse-replace-regexp-in-string "^[ \t]+" "" node))
    (let ((fname (intern-soft (concat muse-import-xml-prefix
                                      (symbol-name (xml-node-name node))))))
      (if (functionp fname)
          (funcall fname node)
        (funcall (intern muse-import-xml-generic-function-name) node)))))


(defun muse-import-xml-node (node)
  "Default node function"
  (muse-import-xml-parse-tree (xml-node-children node)))


(defun muse-import-xml (src dest)
  "Convert the xml SRC buffer in a muse DEST buffer"
  (set-buffer (get-buffer-create dest))
  (when (fboundp 'muse-mode)
    (muse-mode))
  (muse-import-xml-parse-tree (muse-import-xml-convert-to-list src)))

;;; muse-import-xml.el ends here
