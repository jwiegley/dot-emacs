;;; muse-markdown.el --- publish to Markdown syntax

;; Copyright (C) 2008 John Wiegley

;; This file is NOT part of Emacs Muse.  It is not part of GNU Emacs.

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

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Markdown Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-when-compile
  (require 'cl))

(require 'muse-publish)
(require 'muse-regexps)
(require 'muse-xml-common)

(defgroup muse-markdown nil
  "Options controlling the behavior of Muse MARKDOWN publishing."
  :group 'muse-publish)

(defcustom muse-markdown-extension ".mmd.txt"
  "Default file extension for publishing MARKDOWN files."
  :type 'string
  :group 'muse-markdown)

(defcustom muse-markdown-header
  "<lisp>
  (mapconcat
    (function
      (lambda (directive)
        (concat (capitalize (car directive)) \": \" (cdr directive))))
      muse-publishing-directives
      \"\\n\")</lisp>\n\n"
  "Header used for publishing MARKDOWN files.  This may be text or a filename."
  :type 'string
  :group 'muse-markdown)

(defcustom muse-markdown-anchor-on-word nil
  "When true, anchors surround the closest word. This allows you
to select them in a browser (i.e. for pasting), but has the
side-effect of marking up headers in multiple colors if your
header style is different from your link style."
  :type 'boolean
  :group 'muse-markdown)

(let ((markup-regex (assoc 2700 muse-publish-markup-regexps)))
  (assert markup-regex)
  (setcdr markup-regex '("^\\(\\W*\\)#ANCHOR#\\(\\S-+\\)\\s-*" 0 anchor)))

(defcustom muse-markdown-markup-functions
  '((footnote . muse-markdown-markup-footnote))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-markdown)

(defcustom muse-markdown-markup-strings
  '((image-with-desc . "![%3%](%1%.%2% \"%3%\")")
    (image           . "![](%s.%s)")
    (image-link      . "!!!IMAGE-LINK!!!")
    (anchor-ref      . "!!!ANCHOR-REF!!!")
    (url             . "[%s](%s)")	; this is reversed
    (link            . "[%1%](%2%)")
    (link-and-anchor . "[%1%](%3%#%2%)")
    (email-addr      . "[%2%](mailto:%1%)")
    (anchor          . "!!!ANCHOR!!!")
    (emdash          . "%s--%s")
    (comment-begin   . "<!-- ")
    (comment-end     . " -->")
    (rule            . "------")
    (fn-sep          . "")
    (no-break-space  . " ")
    (enddots         . "....")
    (dots            . "...")
    (section         . "# ")
    (subsection      . "## ")
    (subsubsection   . "### ")
    (section-other   . "####")
    (begin-underline . "!!!U!!!")
    (end-underline   . "!!!/U!!!!")
    (begin-literal   . "`")
    (end-literal     . "`")
    (begin-cite      . "!!!CITE!!!")
    (begin-cite-author . "!!!CITE-AUTHOR!!!")
    (begin-cite-year . "!!!CITE-YEAR!!!")
    (end-cite        . "!!!END-CITE!!!")
    (begin-emph      . "*")
    (end-emph        . "*")
    (begin-more-emph . "**")
    (end-more-emph   . "**")
    (begin-most-emph . "!!!SEM!!!")
    (end-most-emph   . "!!!/SEM!!!")

    (begin-verse     . "<verse>\n")
    (verse-space     . "  ")
    (end-verse-line  . "")
    (end-last-stanza-line . "")
    (empty-verse-line . "")
    (end-verse       . "</verse>")

    (begin-center    . "!!!CENTER!!!")
    (end-center      . "!!!/CENTER!!!")

    (begin-quote     . "<quote>")		; need to mark quotes with >
    (end-quote       . "</quote>")

    (begin-uli-item  . "* ")
    (begin-oli-item  . "1. ")
    (begin-dl        . "!!!DL!!!")
    (begin-table     . "!!!TABLE!!!"))
  "Strings used for marking up text as MARKDOWN.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-markdown)

(defcustom muse-markdown-encoding-default 'utf-8
  "The default Emacs buffer encoding to use in published files.
This will be used if no special characters are found."
  :type 'symbol
  :group 'muse-markdown)

(defcustom muse-markdown-charset-default "utf-8"
  "The default Markdown meta charset to use if no translation is found in
`muse-html-encoding-map'."
  :type 'string
  :group 'muse-markdown)

(defun muse-markdown-markup-footnote ()
  (cond
   ((get-text-property (match-beginning 0) 'muse-link)
    nil)
   ((= (muse-line-beginning-position) (match-beginning 0))
    (prog1
        (let ((text (match-string 1)))
          (muse-insert-markup (concat "[^" text "]: ")))
      (save-excursion
        (save-match-data
          (let* ((beg (goto-char (match-end 0)))
                 (end (and (search-forward "\n\n" nil t)
                           (prog1
                               (copy-marker (match-beginning 0))
                             (goto-char beg)))))
            (while (re-search-forward (concat "^["
                                              muse-regexp-blank
                                              "]+\\([^\n]\\)")
                                      end t)
              (replace-match "\\1" t)))))
      (replace-match "")))
   (t (let ((text (match-string 1)))
        (muse-insert-markup (concat "[^" text "]")))
      (replace-match ""))))

;; Handling of tags for MARKDOWN

(defun muse-markdown-strip-links (string)
  "Remove all MARKDOWN links from STRING."
  (muse-replace-regexp-in-string "\\(<a .*?>\\|</a>\\)" "" string nil t))

;; Register the Muse MARKDOWN Publisher

(defun muse-markdown-browse-file (file)
  (browse-url (concat "file:" file)))

(defun muse-markdown-encoding ()
  (muse-xml-transform-content-type
   (or (and (boundp 'buffer-file-coding-system)
	    buffer-file-coding-system)
       muse-markdown-encoding-default)
   muse-markdown-charset-default))

(defun muse-markdown-munge-buffer ()
  (goto-char (point-min))
  (while (re-search-forward "<example>\n" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (let ((begin (point))
	  end)
      (re-search-forward "</example>")
      (delete-region (match-beginning 0) (match-end 0))
      (setq end (point-marker))
      (goto-char begin)
      (while (and (not (eobp))
		  (< (point) end))
	(insert "    ")
	(forward-line))))
  (goto-char (point-min))
  (while (re-search-forward "<verse>\n" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (let ((begin (point))
	  end)
      (re-search-forward "</verse>")
      (delete-region (match-beginning 0) (match-end 0))
      (setq end (point-marker))
      (goto-char begin)
      (while (and (not (eobp))
		  (< (point) end))
	(insert "    ")
	(goto-char (line-end-position))
	(insert "  ")
	(forward-char))))
  (goto-char (point-min))
  (while (re-search-forward "</quote>\\(\\s-\\|\n\\)+<quote>" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (insert "\n\n"))
  (goto-char (point-min))
  (while (search-forward "<quote>" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (let ((begin (point))
	  end)
      (search-forward "</quote>")
      (delete-region (match-beginning 0) (match-end 0))
      (setq end (point-marker))
      (goto-char begin)
      (while (and (not (eobp))
		  (< (point) end))
	(insert "> ")
	(forward-line))))
  (goto-char (point-min))
  (while (search-forward "\n\n\n" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (save-excursion
      (insert "\n\n"))))

(defun muse-markdown-finalize-buffer ()
  (when (and (boundp 'buffer-file-coding-system)
             (memq buffer-file-coding-system '(no-conversion undecided-unix)))
    ;; make it agree with the default charset
    (setq buffer-file-coding-system muse-markdown-encoding-default)))

;;; Register the Muse Markdown Publishers

(muse-define-style "markdown"
                   :suffix    'muse-markdown-extension
		   :functions 'muse-markdown-markup-functions
                   :strings   'muse-markdown-markup-strings
		   :before-end 'muse-markdown-munge-buffer
                   :after     'muse-markdown-finalize-buffer
                   :header    'muse-markdown-header
		   :browser   'muse-markdown-browse-file)

(provide 'muse-markdown)

;;; muse-markdown.el ends here
