;;; muse-context.el --- publish entries in ConTeXt or PDF format

;; Copyright (C) 2007, 2008, 2009, 2010  Free Software Foundation, Inc.

;; Author: Jean Magnan de Bornier (jean@bornier.net)
;; Created: 16-Apr-2007

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; This file when loaded allows you to publish .muse files as ConTeXt
;; files or as pdf files, using respectively the "context" and
;; "context-pdf" styles. It is far from being perfect, so any feedback
;; will be welcome and any mistake hopefully fixed.

;;; Author:

;; Jean Magnan de Bornier, who based this file on muse-latex.el and
;; made the context, context-pdf, context-slides, and
;; context-slides-pdf Muse publishing styles.

;; 16 Avril 2007

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse ConTeXt Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-publish)

(defgroup muse-context nil
  "Rules for marking up a Muse file as a ConTeXt article."
  :group 'muse-publish)

(defcustom muse-context-extension ".tex"
  "Default file extension for publishing ConTeXt files."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-pdf-extension ".pdf"
  "Default file extension for publishing ConTeXt files to PDF."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-pdf-program "texexec --pdf"
  "The program that is called to generate PDF content from ConTeXt content."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-pdf-cruft '(".pgf" ".tmp" ".tui" ".tuo" ".toc"  ".log")
  "Extensions of files to remove after generating PDF output successfully."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-header
  "\\setupinteraction [state=start]
\\usemodule[tikz]
\\usemodule[bib]\n
<lisp>(muse-context-setup-bibliography)</lisp>
 \\setuppublications[]\n
\\setuppublicationlist[]\n\\setupcite[]\n
\\starttext
\\startalignment[center]
  \\blank[2*big]
    {\\tfd <lisp>(muse-publishing-directive \"title\")</lisp>}
  \\blank[3*medium]
    {\\tfa <lisp>(muse-publishing-directive \"author\")</lisp>}
  \\blank[2*medium]
    {\\tfa <lisp>(muse-publishing-directive \"date\")</lisp>}
  \\blank[3*medium]
\\stopalignment

<lisp>(and muse-publish-generate-contents
           (not muse-context-permit-contents-tag)
           \"\\\\placecontent\n\\\\page[yes]\")</lisp>\n\n"
  "Header used for publishing ConTeXt files.  This may be text or a filename."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-footer "<lisp>(muse-context-bibliography)</lisp>
\\stoptext\n"
  "Footer used for publishing ConTeXt files.  This may be text or a filename."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-markup-regexps
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
  :group 'muse-context)

(defcustom muse-context-markup-functions
  '((table . muse-context-markup-table))
  "An alist of style types to custom functions for that kind of text.
For more on the structure of this list, see
`muse-publish-markup-functions'."
  :type '(alist :key-type symbol :value-type function)
  :group 'muse-context)

(defcustom muse-context-markup-strings
  '((image-with-desc . "\\placefigure[][]{%3%}{\\externalfigure[%1%.%2%]}")
    (image           . "\\placefigure[][]{}{\\externalfigure[%s.%s]}")
    (image-link      . "\\useURL[aa][%s][][%1%] \\from[aa]")
    (anchor-ref      . "\\goto{%2%}{}[%1%]")
    (url             . "\\useURL[aa][%s][][%s] \\from[aa]")
    (url-and-desc    . "\\useURL[bb][%s][][%s]\\from[bb]\\footnote{%1%}")
    (link            . "\\goto{%2%}[program(%1%)]\\footnote{%1%}")
    (link-and-anchor . "\\useexternaldocument[%4%][%4%][] \\at{%3%, page}{}[%4%::%2%]\\footnote{%1%}")
    (email-addr      . "\\useURL[mail][mailto:%s][][%s]\\from[mail]")
    (anchor          . "\\reference[%s] ")
    (emdash          . "---")
    (comment-begin   . "\\doifmode{comment}{")
    (comment-end     . "}")
    (rule            . "\\blank[medium]\\hrule\\blank[medium]")
    (no-break-space  . "~")
    (enddots         . "\\ldots ")
    (dots            . "\\dots ")
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
    (section-other   . "\\subsubsubject{")
    (section-other-end . "}")
    (footnote        . "\\footnote{")
    (footnote-end    . "}")
    (footnotetext    . "\\footnotetext[%d]{")
    (begin-underline . "\\underbar{")
    (end-underline   . "}")
    (begin-literal   . "\\type{")
    (end-literal     . "}")
    (begin-emph      . "{\\em ")
    (end-emph        . "}")
    (begin-more-emph . "{\\bf ")
    (end-more-emph   . "}")
    (begin-most-emph . "{\\bf {\\em ")
    (end-most-emph   . "}}")
    (begin-example   . "\\starttyping")
    (end-example     . "\\stoptyping")
    (begin-center    . "\\startalignment[center]\n")
    (end-center      . "\n\\stopalignment")
    (begin-quote     . "\\startquotation\n")
    (end-quote       . "\n\\stopquotation")
    (begin-cite     . "\\cite[authoryear][")
    (begin-cite-author . "\\cite[author][")
    (begin-cite-year . "\\cite[year][")
    (end-cite        . "]")
    (begin-uli       . "\\startitemize\n")
    (end-uli         . "\n\\stopitemize")
    (begin-uli-item  . "\\item ")
    (begin-oli       . "\\startitemize[n]\n")
    (end-oli         . "\n\\stopitemize")
    (begin-oli-item  . "\\item ")
    (begin-dl        . "\\startitemize\n")
    (end-dl          . "\n\\stopitemize")
    (begin-ddt       . "\\head ")
    (end-ddt         . "\n")
    (begin-verse     . "\\blank[big]")
    (end-verse-line  . "\\par")
    (verse-space     . "\\fixedspaces ~~")
    (end-verse       . "\\blank[big]"))
  "Strings used for marking up text.
These cover the most basic kinds of markup, the handling of which
differs little between the various styles."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-context)

(defcustom muse-context-slides-header
  "\\usemodule[<lisp>(if (string-equal (muse-publishing-directive \"module\") nil) \"pre-01\" (muse-publishing-directive \"module\"))</lisp>]
\\usemodule[tikz]
\\usemodule[newmat]
\\setupinteraction [state=start]
\\starttext
\\TitlePage { <lisp>(muse-publishing-directive \"title\")</lisp>
\\blank[3*medium]
\\tfa <lisp>(muse-publishing-directive \"author\")</lisp>
 \\blank[2*medium]
  \\tfa <lisp>(muse-publishing-directive \"date\")</lisp>}"
  "Header for publishing a presentation (slides) using ConTeXt.
Any of the predefined modules, which are available in the
tex/context/base directory, can be used by writing a \"module\"
directive at the top of the muse file; if no such directive is
provided, module pre-01 is used.  Alternatively, you can use your
own style (\"mystyle\", in this example) by replacing
\"\\usemodule[]\" with \"\\input mystyle\".

This may be text or a filename."
  :type 'string
  :group 'muse-context)

(defcustom muse-context-slides-markup-strings
   '((section      . "\\Topic {")
     (subsection   . "\\page \n{\\bf ")
     (subsubsection . "{\\em "))
  "Strings used for marking up text in ConTeXt slides."
  :type '(alist :key-type symbol :value-type string)
  :group 'muse-context)

(defcustom muse-context-markup-specials-document
  '((?\\ . "\\textbackslash{}")
    (?\_ . "\\textunderscore{}")
    (?\< . "\\switchtobodyfont[small]")
    (?\> . "\\switchtobodyfont[big]")
    (?^  . "\\^")
    (?\~ . "\\~")
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
  :group 'muse-context)

(defcustom muse-context-markup-specials-example
  '()
  "A table of characters which must be represented specially.
These are applied to <example> regions.

With the default interpretation of <example> regions, no specials
need to be escaped."
  :type '(alist :key-type character :value-type string)
  :group 'muse-context)

(defcustom muse-context-markup-specials-literal
  '()
  "A table of characters which must be represented specially.
This applies to =monospaced text= and <code> regions."
  :type '(alist :key-type character :value-type string)
  :group 'muse-context)

(defcustom muse-context-markup-specials-url
  '((?\\ . "\\textbackslash")
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
  :group 'muse-context)

(defcustom muse-context-markup-specials-image
  '((?\\ . "\\textbackslash")       ; cannot find suitable replacement
    (?\< . "\\<")
    (?\> . "\\>")
    (?\$ . "\\$")
    (?\% . "\\%")
    (?\{ . "\\{")
    (?\} . "\\}")
    (?\& . "\\&")
    (?\# . "\\#")                     ; cannot find suitable replacement
    )
  "A table of characters which must be represented specially.
These are applied to image filenames."
  :type '(alist :key-type character :value-type string)
  :group 'muse-context)

(defun muse-context-decide-specials (context)
  "Determine the specials to escape, depending on the CONTEXT argument."
  (cond ((memq context '(underline emphasis document url-desc verbatim
                                   footnote))
         muse-context-markup-specials-document)
        ((eq context 'image)
         muse-context-markup-specials-image)
        ((memq context '(email url))
         muse-context-markup-specials-url)
        ((eq context 'literal)
         muse-context-markup-specials-literal)
        ((eq context 'example)
         muse-context-markup-specials-example)
        (t (error "Invalid context argument '%s' in muse-context" context))))

(defun muse-context-markup-table ()
  (let* ((table-info (muse-publish-table-fields (match-beginning 0)
                                                (match-end 0)))
         (row-len (car table-info))
         (field-list (cdr table-info)))
    (when table-info
      (muse-insert-markup "\\starttable[|"
                          (mapconcat 'symbol-name (make-vector row-len 'l)
                                     "|") "|]\n \\HL\n \\VL ")
      (dolist (fields field-list)
        (let ((type (car fields)))
          (setq fields (cdr fields))
          (when (= type 3)
            (muse-insert-markup ""))
          (insert (car fields))
          (setq fields (cdr fields))
          (dolist (field fields)
            (muse-insert-markup " \\VL ")
            (insert field))
          (muse-insert-markup "\\VL\\NR\n \\HL\n \\VL ")
          (when (= type 2)
            (muse-insert-markup " "))))
      (muse-insert-markup "\\stoptable\n")
      (while (search-backward "VL \\stoptable" nil t)
        (replace-match "stoptable" nil t)))))

(defun muse-context-fixup-dquotes ()
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

(defcustom muse-context-permit-contents-tag nil
  "If nil, ignore <contents> tags.  Otherwise, insert table of contents.

Most of the time, it is best to have a table of contents on the
first page, with a new page immediately following.  To make this
work with documents published in both HTML and ConTeXt, we need to
ignore the <contents> tag.

If you don't agree with this, then set this option to non-nil,
and it will do what you expect."
  :type 'boolean
  :group 'muse-context)

(defun muse-context-fixup-citations ()
  "Replace semicolons in multi-head citations with colons."
  (goto-char (point-min))
  (while (re-search-forward "\\\\cite.?\\[" nil t)
    (let ((start (point))
          (end (re-search-forward "]")))
      (save-restriction
        (narrow-to-region start end)
        (goto-char (point-min))
        (while (re-search-forward ";" nil t)
          (replace-match ","))))))

(defun muse-context-munge-buffer ()
  (muse-context-fixup-dquotes)
  (muse-context-fixup-citations)
  (when (and muse-context-permit-contents-tag
             muse-publish-generate-contents)
    (goto-char (car muse-publish-generate-contents))
    (muse-insert-markup "\\placecontent")))

(defun muse-context-bibliography ()
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "\\\\cite.?\\[" nil t)
        "\\completepublications[criterium=all]"
      "")))

(defun muse-context-setup-bibliography ()
  (save-excursion
    (goto-char (point-min))
    (if (re-search-forward "\\\\cite.?\\[" nil t)
        (concat
         "\\usemodule[bibltx]\n\\setupbibtex [database="
         (muse-publishing-directive "bibsource") "]")
      "")))

(defun muse-context-pdf-browse-file (file)
  (shell-command (concat "open " file)))

(defun muse-context-pdf-generate (file output-path final-target)
  (apply
   #'muse-publish-transform-output
   file output-path final-target "PDF"
   (function
    (lambda (file output-path)
      (let* ((fnd (file-name-directory output-path))
             (command (format "%s \"%s\""
                              muse-context-pdf-program
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
;;                         (file-readable-p
;;                          (muse-replace-regexp-in-string
;;                           "\\.tex\\'" ".toc" file t t))
                        ))
          (setq result (shell-command command)
                times (1+ times)))
        (if (or (not (numberp result))
                (eq result 0))
            t
          nil))))
   muse-context-pdf-cruft))

(muse-define-style "context"
                   :suffix    'muse-context-extension
                   :regexps   'muse-context-markup-regexps
                   :functions 'muse-context-markup-functions
                   :strings   'muse-context-markup-strings
                   :specials  'muse-context-decide-specials
                   :after     'muse-context-munge-buffer
                   :header    'muse-context-header
                   :footer    'muse-context-footer
                   :browser   'find-file)

(muse-derive-style "context-pdf" "context"
                   :final   'muse-context-pdf-generate
                   :browser 'muse-context-pdf-browse-file
                   :link-suffix 'muse-context-pdf-extension
                   :osuffix 'muse-context-pdf-extension)

(muse-derive-style "context-slides" "context"
                   :header  'muse-context-slides-header
                   :strings 'muse-context-slides-markup-strings)

(muse-derive-style "context-slides-pdf" "context-pdf"
                   :header  'muse-context-slides-header
                   :strings 'muse-context-slides-markup-strings)

(provide 'muse-context)

;;; muse-context.el ends here
