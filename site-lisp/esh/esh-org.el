;;; esh-org.el --- Utilities for ESH-friendly Org programming  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: faces, tools

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

(require 'org)
(require 'ox-latex)

(defun esh-org--latex-src-block (src-block _contents info)
  "Replace `org-latex-src-block'.
This version is ESH-friendly version and it supports figures.
See `org-latex-src-block' about SRC-BLOCK and INFO."
  (when (org-string-nw-p (org-element-property :value src-block))
    (let* ((attributes (org-export-read-attribute :attr_latex src-block))
           (float (plist-get attributes :float))
           (lang (org-element-property :language src-block))
           (caption (org-element-property :caption src-block))
           (caption-str (org-latex--caption/label-string src-block info))
           (code (org-export-format-code-default src-block info))
           (esh-tag (concat "%% ESH: " lang "\n"))
           (code-block (concat "\\begin{verbatim}\n" code "\\end{verbatim}\n")))
      (if float
          (concat "\\begin{figure}[" (if (string= float "t") "H" float) "]\n"
                  esh-tag code-block
                  (when caption caption-str)
                  "\\end{figure}\n")
        (concat esh-tag code-block)))))

(defun esh-org--latex-inline-src-block (inline-src-block _contents _info)
  "Transcode an INLINE-SRC-BLOCK element from Org to LaTeX.
The format is easy to recognize on the ESH side."
  (let* ((org-lang (org-element-property :language inline-src-block))
         (code (org-element-property :value inline-src-block))
         (separator (org-latex--find-verb-separator code)))
    (format "@%s \\verb%s%s%s" org-lang separator code separator)))

(defun esh-org-activate ()
  "Configure and advise Org primitives to produce ESH-friendly output."
  (setcdr (assoc 'code org-latex-text-markup-alist) 'verb)
  (advice-add 'org-latex-src-block :override #'esh-org--latex-src-block)
  (advice-add 'org-latex-inline-src-block :override #'esh-org--latex-inline-src-block))

(defun esh-org-deactivate ()
  "Unadvise Org primitives advised to produce ESH-friendly output."
  (advice-remove 'org-latex-src-block #'esh-org--latex-src-block)
  (advice-remove 'org-latex-inline-src-block #'esh-org--latex-inline-src-block))

(provide 'esh-org)
;;; esh-org.el ends here

;; Local Variables:
;; checkdoc-arguments-in-order-flag: nil
;; End:
