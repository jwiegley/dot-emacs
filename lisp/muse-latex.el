;;; muse-latex.el --- publish entries in LaTex or PDF format

;; Copyright (C) 2004, 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

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

;; Li Daobing (lidaobing AT gmail DOT com) provided CJK support.

;; Trent Buck (trentbuck AT gmail DOT com) gave valuable advice for
;; how to treat LaTeX specials and the like.

;; Matthias Kegelmann (mathias DOT kegelmann AT sdm DOT de) provided a
;; scenario where we would need to respect the <contents> tag.

;; Jean Magnan de Bornier (jean AT bornier DOT net) provided the
;; markup string for link-and-anchor.

;; Jim Ottaway (j DOT ottaway AT lse DOT ac DOT uk) implemented slides
;; and lecture notes.

;; Karl Berry (karl AT freefriends DOT org) suggested how to escape
;; additional special characters in image filenames.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse LaTeX Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)

(defgroup muse-latex nil
  "Rules for marking up a Muse file as a LaTeX article."
  :group 'muse-publish)

(defcustom muse-latex-extension ".tex"
  "Default file extension for publishing LaTeX files."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-pdf-extension ".pdf"
  "Default file extension for publishing LaTeX files to PDF."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-pdf-browser "open %s"
  "The program to use when browsing a published PDF file.
This should be a format string."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-pdf-program "pdflatex"
  "The program that is called to generate PDF content from LaTeX content."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-pdf-cruft
  '(".aux" ".log" ".nav" ".out" ".snm" ".toc" ".vrb")
  "Extensions of files to remove after generating PDF output successfully."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-header
  "\\documentclass{article}

\\usepackage[english]{babel}
\\usepackage{ucs}
\\usepackage[utf8x]{inputenc}
\\usepackage[T1]{fontenc}
\\usepackage{hyperref}
\\usepackage[pdftex]{graphicx}

\\def\\museincludegraphics{%
  \\begingroup
  \\catcode`\\|=0
  \\catcode`\\\\=12
  \\catcode`\\#=12
  \\includegraphics[width=0.75\\textwidth]
}

\\begin{document}

\\title{<lisp>(muse-publish-escape-specials-in-string
  (muse-publishing-directive \"title\") 'document)</lisp>}
\\author{<lisp>(muse-publishing-directive \"author\")</lisp>}
\\date{<lisp>(muse-publishing-directive \"date\")</lisp>}

\\maketitle

<lisp>(and muse-publish-generate-contents
           (not muse-latex-permit-contents-tag)
           \"\\\\tableofcontents\n\\\\newpage\")</lisp>\n\n"
  "Header used for publishing LaTeX files.  This may be text or a filename."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-footer "<lisp>(muse-latex-bibliography)</lisp>
\\end{document}\n"
  "Footer used for publishing LaTeX files.  This may be text or a filename."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latexcjk-header
  "\\documentclass{article}

\\usepackage{CJK}
\\usepackage{indentfirst}
\\usepackage[CJKbookmarks=true]{hyperref}
\\usepackage[pdftex]{graphicx}

\\begin{document}
\\begin{CJK*}<lisp>(muse-latexcjk-encoding)</lisp>

\\title{<lisp>(muse-publish-escape-specials-in-string
  (muse-publishing-directive \"title\") 'document)</lisp>}
\\author{<lisp>(muse-publishing-directive \"author\")</lisp>}
\\date{<lisp>(muse-publishing-directive \"date\")</lisp>}

\\maketitle

<lisp>(and muse-publish-generate-contents
           (not muse-latex-permit-contents-tag)
           \"\\\\tableofcontents\n\\\\newpage\")</lisp>\n\n"
  "Header used for publishing LaTeX files (CJK).  This may be text or a
filename."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latexcjk-footer
  "\n\\end{CJK*}
\\end{document}\n"
  "Footer used for publishing LaTeX files (CJK).  This may be text or a
filename."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-slides-header
  "\\documentclass[ignorenonframetext]{beamer}

\\usepackage[english]{babel}
\\usepackage{ucs}
\\usepackage[utf8x]{inputenc}
\\usepackage[T1]{fontenc}
\\usepackage{hyperref}

\\def\\museincludegraphics{%
  \\begingroup
  \\catcode`\\|=0
  \\catcode`\\\\=12
  \\catcode`\\#=12
  \\includegraphics[width=0.50\\textwidth]
}

\\title{<lisp>(muse-publish-escape-specials-in-string
  (muse-publishing-directive \"title\") 'document)</lisp>}
\\author{<lisp>(muse-publishing-directive \"author\")</lisp>}
\\date{<lisp>(muse-publishing-directive \"date\")</lisp>}

\\begin{document}

\\frame{\\titlepage}

<lisp>(and muse-publish-generate-contents
           \"\\\\frame{\\\\tableofcontents}\")</lisp>\n\n"
  "Header for publishing of slides using LaTeX.
This may be text or a filename.

You must have the Beamer extension for LaTeX installed for this to work."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-lecture-notes-header
  "\\documentclass{article}
\\usepackage{beamerarticle}

\\usepackage[english]{babel}
\\usepackage{ucs}
\\usepackage[utf8x]{inputenc}
\\usepackage[T1]{fontenc}
\\usepackage{hyperref}
\\usepackage[pdftex]{graphicx}

\\def\\museincludegraphics{%
  \\begingroup
  \\catcode`\\|=0
  \\catcode`\\\\=12
  \\catcode`\\#=12
  \\includegraphics[width=0.50\\textwidth]
}

\\title{<lisp>(muse-publish-escape-specials-in-string
  (muse-publishing-directive \"title\") 'document)</lisp>}
\\author{<lisp>(muse-publishing-directive \"author\")</lisp>}
\\date{<lisp>(muse-publishing-directive \"date\")</lisp>}

\\begin{document}

\\frame{\\titlepage}

<lisp>(and muse-publish-generate-contents
           \"\\\\frame{\\\\tableofcontents}\")</lisp>\n\n"
  "Header for publishing of lecture notes using LaTeX.
This may be text or a filename.

You must have the Beamer extension for LaTeX installed for this to work."
  :type 'string
  :group 'muse-latex)

(defcustom muse-latex-markup-regexps
  `(;; numeric ranges
    (10000 "\\([0-9]+\\)-\\([0-9]+\\)" 0 "\\1--\\2")

    ;; be careful of closing quote pairs
    (10100 "\"'" 0 "\"\\\\-'"))
  "List of markup regexps for identifying regions in a Muse page.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-latex)

(defcustom muse-latex-markup-functions
  '((table . muse-latex-markup-table))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-latex)

(defcustom muse-latex-markup-strings
  '((image-with-desc . "\\begin{figure}[h]
\\centering\\museincludegraphics{%s.%s}|endgroup
\\caption{%s}
\\end{figure}")
    (image           . "\\begin{figure}[h]
\\centering\\museincludegraphics{%s.%s}|endgroup
\\end{figure}")
    (image-link      . "%% %s
\\museincludegraphics{%s.%s}|endgroup")
    (anchor-ref      . "\\ref{%s}")
    (url             . "\\url{%s}")
    (url-and-desc    . "\\href{%s}{%s}\\footnote{%1%}")
    (link            . "\\href{%s}{%s}\\footnote{%1%}")
    (link-and-anchor . "\\href{%1%}{%3%}\\footnote{%1%}")
    (email-addr      . "\\verb|%s|")
    (anchor          . "\\label{%s}")
    (emdash          . "---")
    (comment-begin   . "% ")
    (rule            . "\\vspace{.5cm}\\hrule\\vspace{.5cm}")
    (no-break-space  . "~")
    (line-break      . "\\\\")
    (enddots         . "\\ldots{}")
    (dots            . "\\dots{}")
    (part            . "\\part{")
    (part-end        . "}")
    (chapter         . "\\chapter{")
    (chapter-end     . "}")
    (section         . "\\section{")
    (section-end     . "}")
    (subsection      . "\\subsection{")
    (subsection-end  . "}")
    (subsubsection   . "\\subsubsection{")
    (subsubsection-end . "}")
    (section-other   . "\\paragraph{")
    (section-other-end . "}")
    (footnote        . "\\footnote{")
    (footnote-end    . "}")
    (footnotetext    . "\\footnotetext[%d]{")
    (begin-underline . "\\underline{")
    (end-underline   . "}")
    (begin-literal   . "\\texttt{")
    (end-literal     . "}")
    (begin-emph      . "\\emph{")
    (end-emph        . "}")
    (begin-more-emph . "\\textbf{")
    (end-more-emph   . "}")
    (begin-most-emph . "\\textbf{\\emph{")
    (end-most-emph   . "}}")
    (begin-verse     . "\\begin{verse}\n")
    (end-verse-line  . " \\\\")
    (verse-space     . "~~~~")
    (end-verse       . "\n\\end{verse}")
    (begin-example   . "\\begin{quote}\n\\begin{verbatim}")
    (end-example     . "\\end{verbatim}\n\\end{quote}")
    (begin-center    . "\\begin{center}\n")
    (end-center      . "\n\\end{center}")
    (begin-quote     . "\\begin{quote}\n")
    (end-quote       . "\n\\end{quote}")
    (begin-cite     . "\\cite{")
    (begin-cite-author . "\\citet{")
    (begin-cite-year . "\\citet{")
    (end-cite        . "}")
    (begin-uli       . "\\begin{itemize}\n")
    (end-uli         . "\n\\end{itemize}")
    (begin-uli-item  . "\\item ")
    (begin-oli       . "\\begin{enumerate}\n")
    (end-oli         . "\n\\end{enumerate}")
    (begin-oli-item  . "\\item ")
    (begin-dl        . "\\begin{description}\n")
    (end-dl          . "\n\\end{description}")
    (begin-ddt       . "\\item[")
    (end-ddt         . "] \\mbox{}\n"))
  "Strings used for marking up text.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-latex)

(defcustom muse-latex-slides-markup-tags
  '(("slide" t t nil muse-latex-slide-tag))
 "A list of tag specifications, for specially marking up LaTeX slides."
  :type '(repeat (list (string :tag "Markup tag")
                       (boolean :tag "Expect closing tag" :value t)
                       (boolean :tag "Parse attributes" :value nil)
                       (boolean :tag "Nestable" :value nil)
                       function))
  :group 'muse-latex)

(defcustom muse-latexcjk-encoding-map
  '((utf-8              . "{UTF8}{song}")
    (japanese-iso-8bit  . "[dnp]{JIS}{min}")
    (chinese-big5       . "{Bg5}{bsmi}")
    (mule-utf-8         . "{UTF8}{song}")
    (chinese-iso-8bit   . "{GB}{song}")
    (chinese-gbk        . "{GBK}{song}"))
  "An alist mapping emacs coding systems to appropriate CJK codings.
Use the base name of the coding system (ie, without the -unix)."
  :type '(alist :key-type coding-system :value-type string)
  :group 'muse-latex)

(defcustom muse-latexcjk-encoding-default "{GB}{song}"
  "The default Emacs buffer encoding to use in published files.
This will be used if no special characters are found."
  :type 'string
  :group 'muse-latex)

(defun muse-latexcjk-encoding ()
  (when (boundp 'buffer-file-coding-system)
    (muse-latexcjk-transform-content-type buffer-file-coding-system)))

(defun muse-latexcjk-transform-content-type (content-type)
  "Using `muse-cjklatex-encoding-map', try and resolve an emacs coding
system to an associated CJK coding system."
  (let ((match (and (fboundp 'coding-system-base)
                    (assoc (coding-system-base content-type)
                           muse-latexcjk-encoding-map))))
    (if match
        (cdr match)
      muse-latexcjk-encoding-default)))

(defcustom muse-latex-markup-specials-document
  '((?\\ . "\\textbackslash{}")
    (?\_ . "\\textunderscore{}")
    (?\< . "\\textless{}")
    (?\> . "\\textgreater{}")
    (?^  . "\\^{}")
    (?\~ . "\\~{}")
    (?\@ . "\\@")
    (?\$ . "\\$")
    (?\% . "\\%")
    (?\{ . "\\{")
    (?\} . "\\}")
    (?\& . "\\&")
    (?\# . "\\#"))
  "A table of characters which must be represented specially.
These are applied to the entire document, sans already-escaped
regions."
  :type '(alist :key-type character :value-type string)
  :group 'muse-latex)

(defcustom muse-latex-markup-specials-example
  '()
  "A table of characters which must be represented specially.
These are applied to <example> regions.

With the default interpretation of <example> regions, no specials
need to be escaped."
  :type '(alist :key-type character :value-type string)
  :group 'muse-latex)

(defcustom muse-latex-markup-specials-literal
  '((?\n . "\\\n")
    (?\\ . "\\textbackslash{}")
    (?_  . "\\textunderscore{}")
    (?\< . "\\textless{}")
    (?\> . "\\textgreater{}")
    (?^  . "\\^{}")
    (?\~ . "\\~{}")
    (?\$ . "\\$")
    (?\% . "\\%")
    (?\{ . "\\{")
    (?\} . "\\}")
    (?\& . "\\&")
    (?\# . "\\#"))
  "A table of characters which must be represented specially.
This applies to =monospaced text= and <code> regions."
  :type '(alist :key-type character :value-type string)
  :group 'muse-latex)

(defcustom muse-latex-markup-specials-url
  '((?\\ . "\\textbackslash{}")
    (?\_ . "\\_")
    (?\< . "\\<")
    (?\> . "\\>")
    (?\$ . "\\$")
    (?\% . "\\%")
    (?\{ . "\\{")
    (?\} . "\\}")
    (?\& . "\\&")
    (?\# . "\\#"))
  "A table of characters which must be represented specially.
These are applied to URLs."
  :type '(alist :key-type character :value-type string)
  :group 'muse-latex)

(defcustom muse-latex-markup-specials-image
  '((?\\ . "\\\\")
    (?\< . "\\<")
    (?\> . "\\>")
    (?\$ . "\\$")
    (?\% . "\\%")
    (?\{ . "\\{")
    (?\} . "\\}")
    (?\& . "\\&")
    (?\# . "\\#")
    (?\| . "\\|"))
  "A table of characters which must be represented specially.
These are applied to image filenames."
  :type '(alist :key-type character :value-type string)
  :group 'muse-latex)

(defun muse-latex-decide-specials (context)
  "Determine the specials to escape, depending on CONTEXT."
  (cond ((memq context '(underline emphasis document url-desc verbatim
                                   footnote))
         muse-latex-markup-specials-document)
        ((eq context 'image)
         muse-latex-markup-specials-image)
        ((memq context '(email url))
         muse-latex-markup-specials-url)
        ((eq context 'literal)
         muse-latex-markup-specials-literal)
        ((eq context 'example)
         muse-latex-markup-specials-example)
        (t (error "Invalid context '%s' in muse-latex" context))))

(defcustom muse-latex-permit-contents-tag nil
  "If nil, ignore <contents> tags.  Otherwise, insert table of contents.

Most of the time, it is best to have a table of contents on the
first page, with a new page immediately following.  To make this
work with documents published in both HTML and LaTeX, we need to
ignore the <contents> tag.

If you don't agree with this, then set this option to non-nil,
and it will do what you expect."
  :type 'boolean
  :group 'muse-latex)

(defun muse-latex-markup-table ()
  (let* ((table-info (muse-publish-table-fields (match-beginning 0)
                                                (match-end 0)))
         (row-len (car table-info))
         (field-list (cdr table-info)))
    (when table-info
      (muse-insert-markup "\\begin{tabular}{" (make-string row-len ?l) "}\n")
      (dolist (fields field-list)
        (let ((type (car fields)))
          (setq fields (cdr fields))
          (if (eq type 'hline)
              (muse-insert-markup "\\hline\n")
            (when (= type 3)
              (muse-insert-markup "\\hline\n"))
            (insert (car fields))
            (setq fields (cdr fields))
            (dolist (field fields)
              (muse-insert-markup " & ")
              (insert field))
            (muse-insert-markup " \\\\\n")
            (when (= type 2)
              (muse-insert-markup "\\hline\n")))))
      (muse-insert-markup "\\end{tabular}"))))

;;; Tags for LaTeX

(defun muse-latex-slide-tag (beg end attrs)
  "Publish the <slide> tag in LaTeX.
This is used by the slides and lecture-notes publishing styles."
  (let ((title (cdr (assoc "title" attrs))))
    (goto-char beg)
    (muse-insert-markup "\\begin{frame}[fragile]\n")
    (when title
      (muse-insert-markup "\\frametitle{")
      (insert title)
      (muse-insert-markup "}\n"))
    (save-excursion
      (goto-char end)
      (muse-insert-markup "\n\\end{frame}"))))

;;; Post-publishing functions

(defun muse-latex-fixup-dquotes ()
  "Fixup double quotes."
  (goto-char (point-min))
  (let ((open t))
    (while (search-forward "\"" nil t)
      (unless (get-text-property (match-beginning 0) 'read-only)
        (when (or (bobp)
                  (eq (char-before) ?\n))
          (setq open t))
        (if open
            (progn
              (replace-match "``")
              (setq open nil))
          (replace-match "''")
          (setq open t))))))

(defun muse-latex-fixup-citations ()
  "Replace semicolons in multi-head citations with colons."
  (goto-char (point-min))
  (while (re-search-forward "\\\\cite.?{" nil t)
    (let ((start (point))
          (end (re-search-forward "}")))
      (save-restriction
        (narrow-to-region start end)
        (goto-char (point-min))
        (while (re-search-forward ";" nil t)
          (replace-match ","))))))

(defun muse-latex-fixup-headings ()
  "Remove footnotes in headings, since LaTeX does not permit them to exist.

This can happen if there is a link in a heading, because by
default Muse will add a footnote for each link."
  (goto-char (point-min))
  (while (re-search-forward "^\\\\section.?{" nil t)
    (save-restriction
      (narrow-to-region (match-beginning 0) (muse-line-end-position))
      (goto-char (point-min))
      (while (re-search-forward "\\\\footnote{[^}\n]+}" nil t)
        (replace-match ""))
      (forward-line 1))))

(defun muse-latex-munge-buffer ()
  (muse-latex-fixup-dquotes)
  (muse-latex-fixup-citations)
  (muse-latex-fixup-headings)
  (when (and muse-latex-permit-contents-tag
             muse-publish-generate-contents)
    (goto-char (car muse-publish-generate-contents))
    (muse-insert-markup "\\tableofcontents")))

(defun muse-latex-bibliography ()
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "\\\\cite.?{" nil t)
        (concat
         "\\bibliography{"
         (muse-publishing-directive "bibsource")
         "}\n")
      "")))

(defun muse-latex-pdf-browse-file (file)
  (shell-command (format muse-latex-pdf-browser file)))

(defun muse-latex-pdf-generate (file output-path final-target)
  (apply
   #'muse-publish-transform-output
   file output-path final-target "PDF"
   (function
    (lambda (file output-path)
      (let* ((fnd (file-name-directory output-path))
             (command (format "%s \"%s\""
                              muse-latex-pdf-program
                              (file-relative-name file fnd)))
             (times 0)
             (default-directory fnd)
             result)
        ;; XEmacs can sometimes return a non-number result.  We'll err
        ;; on the side of caution by continuing to attempt to generate
        ;; the PDF if this happens and treat the final result as
        ;; successful.
        (while (and (< times 2)
                    (or (not (numberp result))
                        (not (eq result 0))
                        ;; table of contents takes 2 passes
                        (file-readable-p
                         (muse-replace-regexp-in-string
                          "\\.tex\\'" ".toc" file t t))))
          (setq result (shell-command command)
                times (1+ times)))
        (if (or (not (numberp result))
                (eq result 0))
            t
          nil))))
   muse-latex-pdf-cruft))

;;; Register the Muse LATEX Publishers

(muse-define-style "latex"
                   :suffix    'muse-latex-extension
                   :regexps   'muse-latex-markup-regexps
                   :functions 'muse-latex-markup-functions
                   :strings   'muse-latex-markup-strings
                   :specials  'muse-latex-decide-specials
                   :before-end 'muse-latex-munge-buffer
                   :header    'muse-latex-header
                   :footer    'muse-latex-footer
                   :browser   'find-file)

(muse-derive-style "pdf" "latex"
                   :final   'muse-latex-pdf-generate
                   :browser 'muse-latex-pdf-browse-file
                   :link-suffix 'muse-latex-pdf-extension
                   :osuffix 'muse-latex-pdf-extension)

(muse-derive-style "latexcjk" "latex"
                   :header    'muse-latexcjk-header
                   :footer    'muse-latexcjk-footer)

(muse-derive-style "pdfcjk" "latexcjk"
                   :final   'muse-latex-pdf-generate
                   :browser 'muse-latex-pdf-browse-file
                   :link-suffix 'muse-latex-pdf-extension
                   :osuffix 'muse-latex-pdf-extension)

(muse-derive-style "slides" "latex"
                   :header 'muse-latex-slides-header
                   :tags   'muse-latex-slides-markup-tags)

(muse-derive-style "slides-pdf" "pdf"
                   :header 'muse-latex-slides-header
                   :tags   'muse-latex-slides-markup-tags)

(muse-derive-style "lecture-notes" "slides"
                   :header 'muse-latex-lecture-notes-header)

(muse-derive-style "lecture-notes-pdf" "slides-pdf"
                   :header 'muse-latex-lecture-notes-header)

(provide 'muse-latex)

;;; muse-latex.el ends here
