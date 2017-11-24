;;; lentic-ox.el --- Exporter backend for orgel documentation -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2015, 2016, Phillip Lord, Newcastle University

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

;; An org-mode exporter for lentic.

;;; Code:

;; #+begin_src emacs-lisp
(require 'ox-html)

;; Define an exporter
(org-export-define-derived-backend 'lentic
  'html
  :filters-alist
  '((:filter-parse-tree . lentic-ox-filter-parse-tree)
    (:filter-section . lentic-ox-filter-section)))

;; Main export function
(defun lentic-ox-html-export-to-html ()
  "Export the current buffer to a HTML file."
  (interactive)
  (let* ((extension (concat "." org-html-extension))
         (file (org-export-output-file-name extension))
         (org-export-coding-system org-html-coding-system)
         (org-html-htmlize-output-type 'css)
         (org-html-postamble nil)
         (org-html-use-infojs t)
         (org-html-head
          "<link rel=\"stylesheet\" type=\"text/css\" href=\"http://phillord.github.io/lentic/include/lenticular.css\" />"))
    (org-export-to-file 'lentic file)))


(defvar lentic-ox-no-export-headers '("Header")
  "List of headers to which noexport tags should be added.")

(defun lentic-ox-filter-parse-tree (tree back-end info)
  "Filter preventing the export of specific headers.

TREE is the parse tree. BACK-END is the symbol specifying
back-end used for export. INFO is a plist used as a communication
channel."
  (org-element-map tree 'headline
    (lambda (head)
      (if (-contains?
           lentic-ox-no-export-headers
           (org-element-property
            :raw-value
            head))
          (org-element-put-property
           head :tags
           (cons "noexport"
                 (org-element-property :tags head)))
        head)))
  tree)

(defun lentic-ox-filter-section (section back-end info)
  "Currently does nothing useful."
  section back-end info

  (org-element-property :parent section)
  section
    )

(provide 'lentic-ox)
;;; lentic-ox.el ends here
;; #+end_src
