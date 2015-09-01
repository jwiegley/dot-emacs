;;; tbx2org.el --- Tinderbox to org-mode conversion

;; Copyright (C) 2014 istib

;; Author: istib
;; URL: https://github.com/istib/tbx2org
;; Version: 0.1
;; Package-Requires: ((dash "2.5.0") (s "1.8.0") (cl-lib "0.4"))
;; Keywords: org-mode

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'cl-lib)
(require 'xml)
(require 'dash)
(require 's)
(require 'org)

;;;###autoload
(defun tbx-import-file (file &optional dest-buffer)
  "imports tinderbox FILE into DEST-BUFFER (or new buffer, if nil)"
  (interactive "f")
  (condition-case nil
      (let* ((dest-buffer (or dest-buffer (generate-new-buffer "*tinderbox import*")))
             (xml-file    (xml-parse-file file))
             (doc-root    (cl-cdddr (cl-cdddar xml-file)))
             (parent-node (car (xml-get-children doc-root 'item)))
             (leaves      (xml-get-children parent-node 'item)))
     (with-current-buffer dest-buffer (org-mode))
     (mapcar (lambda (node)
               (insert-org-node-from-tbx-node node dest-buffer 1))
             leaves))
    (error
     (message "Couldn't parse Tinderbox file"))))

(defun tbx-node-attribute (tbx-node attr)
  "get named 'key attribute' (ATTR) of a tinderbox
node (TBX-NODE). returns NIL if none is found"
  (catch 'found
    (let ((attributes (xml-get-children tbx-node 'attribute)))
      (while attributes
        (let* ((candidate      (car attributes))
               (candidate-name (xml-get-attribute candidate 'name)))
          (if (string= candidate-name attr)
              (throw 'found (cl-caddr candidate)))
        (setq attributes (cdr attributes)))))))

(defun tbx-node-children (tbx-node)
  "returns children of TBX-NODE in document tree, or NIL if node is a leaf"
  (xml-get-children tbx-node 'item))

(defun tbx-node-title (tbx-node)
  "returns NAME property of a tinderbox node"
  (tbx-node-attribute tbx-node "Name"))

(defun tbx-node-text (tbx-node)
  "returns TEXT content of a tinderbox node"
  (cl-caddar (xml-get-children tbx-node 'text)))

(defun tbx-node-defined-attributes (tbx-node)
  "returns all 'key attributes' defined on TBX-NODE"
  (let* ((prop-string (tbx-node-attribute tbx-node "KeyAttributes")))
    (if (not (null prop-string))
      (split-string prop-string ";"))))

(defun tbx-node-named-attributes (tbx-node attrs)
  "returns an alist of property/value pairs of TBX-NODE
given the list of property specified in ATTRS"
  (let* ((values (mapcar (lambda (attr) (tbx-node-attribute tbx-node attr))
                        attrs)))
    (-zip attrs values)))

(defun tbx-node-key-attributes (tbx-node)
  "returns all key attributes defined on TBX-NODE
in the form of property/value pairs, if value is not nil"
  ;; TODO: filter out pairs with no value
  (let ((attr-list (tbx-node-defined-attributes tbx-node)))
    (tbx-node-named-attributes tbx-node attr-list)))

(defun tbx-set-org-property-from-tbx-attribute (attr)
  "set org property at point from attribute/value pair of tinderbox node"
  (let ((prop (car attr))
        (val  (cdr attr)))
    (if (not (null val))
        (org-set-property prop val))))

(defun insert-org-node-from-tbx-node (tbx-node dest-buffer &optional level)
  "write TBX-NODE and descendents into org-mode DEST-BUFFER. Starting at LEVEL"
  (let ((node-title      (tbx-node-title tbx-node))
        (node-properties (tbx-node-key-attributes tbx-node))
        (node-text       (tbx-node-text tbx-node))
        (node-children   (tbx-node-children tbx-node)))

    (with-current-buffer dest-buffer
      ;; heading
      (let* ((org-prefix (s-repeat level "*"))
             (heading    node-title))
        (insert (concat org-prefix " " heading "\n")))
      ;; properties
      (mapc (lambda (pair) (tbx-set-org-property-from-tbx-attribute pair))
            node-properties)
      ;; text
      (if (not (null node-text))
        (insert (concat "\n" node-text "\n"))))
      ;; recur for node children
      (mapcar (lambda (child)
                (insert-org-node-from-tbx-node child
                                               dest-buffer
                                               (1+ level)))
              node-children)))

(provide 'tbx2org)

;;; tbx2org.el ends here
