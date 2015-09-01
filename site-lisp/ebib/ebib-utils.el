;;; ebib-utils.el --- Part of Ebib, a BibTeX database manager  -*- lexical-binding: t -*-

;; Copyright (c) 2003-2014 Joost Kremers
;; All rights reserved.

;; Author: Joost Kremers <joostkremers@fastmail.fm>
;; Maintainer: Joost Kremers <joostkremers@fastmail.fm>
;; Created: 2014
;; Version: 2.3
;; Keywords: text bibtex
;; Package-Requires: ((dash "2.5.0") (emacs "24.3"))

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;;
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;; 3. The name of the author may not be used to endorse or promote products
;;    derived from this software without specific prior written permission.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
;; IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
;; OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
;; IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
;; NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES ; LOSS OF USE,
;; DATA, OR PROFITS ; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
;; THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Commentary:

;; This file is part of Ebib, a BibTeX database manager for Emacs. It
;; contains general macros, utilities and variables.

;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'bibtex)

;; Make a bunch of variables obsolete.
(make-obsolete-variable 'ebib-entry-types "The variabale `ebib-entry-types' is obsolete; see the manual for details." "24.4")
(make-obsolete-variable 'ebib-default-entry 'ebib-default-entry-type "24.4")
(make-obsolete-variable 'ebib-additional-fields 'ebib-extra-fields "24.4")
(make-obsolete-variable 'ebib-biblatex-inheritance 'ebib-biblatex-inheritances "24.4")
(make-obsolete-variable 'ebib-standard-url-field 'ebib-url-field "24.4")
(make-obsolete-variable 'ebib-standard-file-field 'ebib-file-field "24.4")
(make-obsolete-variable 'ebib-standard-doi-field 'ebib-doi-field "24.4")

;; Make sure we can call bibtex-generate-autokey
(declare-function bibtex-generate-autokey "bibtex" nil)

;;;;;;;;;;;;;;;;;;;;;;
;; global variables ;;
;;;;;;;;;;;;;;;;;;;;;;

;; user customisation

(defgroup ebib nil "Ebib: a BibTeX database manager" :group 'tex)

(defgroup ebib-windows nil "Ebib window management" :group 'ebib)

(defcustom ebib-bibtex-dialect 'BibTeX
  "The default BibTeX dialect.
A `.bib' file/database without explicit dialect setting is
assumed to use this dialect.  Possible values are those listed in
`bibtex-dialect-list'."
  :group 'ebib
  :type `(choice :tag "BibTeX Dialect"
                 ,@(mapcar (lambda (d) `(const ,d))
                           bibtex-dialect-list)))

(defcustom ebib-default-entry-type "Article"
  "The default entry type.
This is the entry type assigned to newly created entries."
  :group 'ebib
  :type 'string)

(defcustom ebib-preload-bib-files nil
  "List of BibTeX files to load automatically when Ebib starts.
This option allows you to specify which `.bib' file(s) Ebib
should load automatically when it starts up.  Specify one file per
line.  You can complete a partial filename with `M-TAB`."
  :group 'ebib
  :type '(repeat (file :must-match t)))

(defcustom ebib-bib-search-dirs '("~")
  "List of directories to search for BibTeX files.
This is a list of directories Ebib searches for `.bib' files to
be preloaded.  Note that only the directories themselves are
searched, not their subdirectories.  The directories in this list
are also searched when the function `ebib' is passed a file
name (e.g., from an Eshell command line)."
  :group 'ebib
  :type '(repeat :tag "Search directories for BibTeX files" (string :tag "Directory")))

(defcustom ebib-create-backups t
  "Create a backup file.
The first time a BibTeX file is saved, a backup file is created
when it is first saved.  Note that Ebib uses
`make-backup-file-name' to create the name for the backup file."
  :group 'ebib
  :type '(choice (const :tag "Create backups" t)
                 (const :tag "Do not create backups" nil)))

(defcustom ebib-extra-fields '((BibTeX "crossref"
                                       "annote"
                                       "abstract"
                                       "keywords"
                                       "file"
                                       "timestamp"
                                       "url"
                                       "doi")
                               (biblatex "crossref"
                                         "annotation"
                                         "abstract"
                                         "keywords"
                                         "file"
                                         "timestamp"))
  "List of the extra fields for BibTeX entries.
Extra fields are fields that are available for all entry types.
Depending on the bibliography style, the value of these fields
may appear in the bibliography, but you may also define fields
that are just for personal use.

Note, before adding fields to this list, check if the field you
want to add is among the fields that are hidden by default.  See
the option \"Hidden Fields\" (`ebib--hidden-fields') for details."
  :group 'ebib
  :type '(repeat (cons (choice :tag "Choose BibTeX dialect"
                               (const BibTeX)
                               (const biblatex)
                               (symbol :tag "Other"))
                       (repeat :tag "Extra fields" (string :tag "Field")))))

(defcustom ebib-hidden-fields '("addendum" "afterword" "annotator" "bookauthor"
                                "booksubtitle" "booktitleaddon" "chapter" "commentator"
                                "edition" "editora" "editorb" "editorc" "eid" "eprint"
                                "eprintclass" "eprinttype" "eventdate" "eventtitle"
                                "foreword" "holder" "howpublished" "introduction" "isbn"
                                "isrn" "issn" "issue" "issuesubtitle" "issuetitle"
                                "journalsubtitle" "language" "location" "mainsubtitle"
                                "maintitle" "maintitleaddon" "month" "origlanguage"
                                "pagetotal" "part" "remark" "subtitle" "timestamp"
                                "titleaddon" "translator" "urldate" "venue" "version"
                                "volumes")
  "List of fields that are not displayed.
The fields in this list are not displayed by default.  Since
BibLaTeX defines a large number of fields, it is not practical to
display them all in the entry buffer.  You can make these fields
temporarily visible with the command `\\<ebib-index-mode-map>\\[ebib-toggle-hidden]'
or through the menu."
  :group 'ebib
  :type '(repeat (string :tag "Field")))

(defcustom ebib-layout 'full
  "Ebib window layout.
This option defines how Ebib displays the buffers its uses.  By
default, Ebib takes over the entire frame and creates two windows
to display the index and the entry buffer.  Alternatively, Ebib
can use just the right part of the frame (the width can be
specified with the option `ebib-width').  A third option is to
display only the index window upon startup.  The entry buffer will
be displayed when you edit an entry of if you press
\\[ebib-select-and-popup-entry]."
  :group 'ebib-windows
  :type '(choice (const :tag "Use full frame" full)
                 (const :tag "Use right part of the frame" custom)
                 (const :tag "Display only index window" index-only)))

(defcustom ebib-width 80
  "Width of the Ebib windows.
The width can be absolute or relative; if it is absolute, it
specifies the number of columns that the Ebib windows occupies.
If it is relative, the with must be a value between 0 and 1
specifying the width relative to the width of the window that is
selected when Ebib is started.

This option only takes effect if `ebib-layout' is set to `custom'."
  :group 'ebib-windows
  :type '(choice (integer :label "Absolute width:")
                 (float :label "Relative width:" :value 0.3)))

(defcustom ebib-popup-entry-window nil
  "Create a popup window to display the entry window.
If `ebib-layout' is set to `index-only', Ebib will use an
existing window to display the entry buffer when needed.  By
setting this option, however, you can tell Ebib to use the
function `display-buffer-pop-up-window' to show the entry buffer,
which (usually) means that a new window will be created.

Note that setting this option has no effect unless `ebib-layout'
is set to `index-only'."
  :group 'ebib-windows
  :type 'boolean)

(defcustom ebib-window-vertical-split nil
  "Display the index buffer at the left of the frame.
Setting this option makes Ebib display the index buffer at the
left side of the frame rather than at the top.  The width of the
window will be `ebib-index-window-size', which you will probably
have to set to a larger value."
  :group 'ebib-windows
  :type 'boolean)

(defcustom ebib-index-window-size 10
  "The size of the index buffer window.
This is either the height of the window, or, if
`ebib-window-vertical-split' is set, the width of the window.
The rest of the frame is used for the entry buffer, unless
`ebib-layout' is set to `index-only'."
  :group 'ebib-windows
  :type 'integer)

(defcustom ebib-index-mode-line '("%e"
                                  mode-line-front-space
                                  mode-line-modified
                                  mode-line-buffer-identification
                                  (:eval (format "  (%s)" (ebib--get-dialect)))
                                  (:eval (if (and ebib--cur-db (ebib--cur-entry-key)) "     Entry %l" "     No Entries"))
                                  (:eval (if (and ebib--cur-db (ebib-db-get-filter ebib--cur-db)) (format "  |%s|"(ebib--filters-pp-filter (ebib-db-get-filter ebib--cur-db))) "")))
  "The mode line for the index window.
The mode line of the index window shows some Ebib-specific
information.  You can customize this information if you wish, or
disable the Ebib-specific mode line altogether.  Note that the
mode line of the entry buffer is not changed."
  :group 'ebib-windows
  :type '(choice (const :tag "Use standard mode line" nil)
                 (sexp :tag "Customize mode line")))

(defcustom ebib-index-display-fields nil
  "List of the fields to display in the index buffer.
By default, the index buffer only shows the entry key of each
entry.  If this provides too little information, you can have Ebib
add the contents of certain fields to the index buffer."
  :group 'ebib
  :type '(repeat (string :tag "Index Field")))

(defcustom ebib-uniquify-keys nil
  "Create unique keys.
When adding new entries to the database, Ebib does not allow
duplicate keys.  By setting this option, you can tell Ebib to
automatically create a unique key by adding `b', `c', etc. to it.
This applies when Ebib automatically generates keys for new
entries (see `ebib-autogenerate-keys'), when merging `.bib'
files, and when changing a key."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-autogenerate-keys nil
  "Automatically generate keys for new entries.
With this option set, Ebib does not ask for a key when you add a
new entry.  Instead, it gives the entry a temporary key and
assigns a proper key when you finish editing the entry.  This
option uses the function `bibtex-generate-autokey', which has a
number of user-customizable options.  See that function's
documentation for details."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-citation-commands '((any
                                     (("cite" "\\cite%<[%A]%>{%K}")))
                                    (org-mode
                                     (("ebib" "[[ebib:%K][%D]]")))
                                    (markdown-mode
                                     (("text" "@%K%< [%A]%>")
                                      ("paren" "[%(%<%A %>@%K%<, %A%>%; )]")
                                      ("year" "[-@%K%< %A%>]"))))
  "A list of format strings to insert a citation into a buffer.
This option defines the citation commands that you can use when
inserting a citation key into a buffer (with
`ebib--insert-bibtex-key' or `ebib--push-bibtex-key').  The citation
command (which can be any string, it does not have to correspond
to an actual LaTeX macro) can be selected with TAB completion.
You can define a different set of citation commands for each
major mode.  There is a catch-all option `any`, which is chosen
when the major mode from which `ebib--insert-bibtex-key` is not on
the list.  By default, this is used for LaTeX citations, so as to
cover all TeX and LaTeX modes.

The format string that defines the actual citation command
inserted in the buffer is described in the manual/info file in
the section \"Defining Citation Commands\"."
  :group 'ebib
  :type '(repeat (list :tag "Mode" (symbol :tag "Mode name")
                       (repeat (list :tag "Citation command"
                                     (string :tag "Identifier")
                                     (string :tag "Format string"))))))

(defcustom ebib-multiline-major-mode 'text-mode
  "The major mode of the multiline edit buffer."
  :group 'ebib
  :type '(function :tag "Mode function"))

(defcustom ebib-sort-order nil
  "The fields on which the BibTeX entries are to be sorted in the BibTeX file.
This option is described in the manual/info file in the section
\"Sorting the .bib file\"."
  :group 'ebib
  :type '(repeat (repeat :tag "Sort level" (string :tag "Sort field"))))

(defcustom ebib-save-xrefs-first t
  "Save entries with a crossref field first in the BibTeX-file.
For BibTeX's cross-referencing to work, the cross-referencing
entries must appear in the `.bib` file before the
cross-referenced entries.  This option tells Ebib to save all
entries with a `crossref` field first, so that BibTeX's
crossreferencing options work as intended.

Note: this option is not compatible with setting the option
`ebib-sort-order'.  If you want to use the latter, unset this
one."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-use-timestamp nil
  "Add a timestamp to new entries.
If this option is set, Ebib will add a `timestamp` field to every
new entry, recording the date and time it was added to the
database.  See the section \"Timestamps\" in the manual/info file for
details.

Note that the `timestamp' field is normally hidden.  You can make
it visible with \\[ebib--toggle-hidden] in the index buffer or by
customizing the option `ebib--hidden-fields'."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-timestamp-format "%a %b %e %T %Y"
  "Format of the time string used in the timestamp.
This option specifies the format string that is used to create
the timestamp.  The default value produces a timestamp of the form
\"Mon Mar 12 01:03:26 2007\".  This option uses the Emacs function
`format-time-string` to create the timestamp.  See that function's
documentation for details on customizing the format string."
  :group 'ebib
  :type 'string)

(defcustom ebib-url-field "url"
  "Standard field to store URLs in.
In the index buffer, the command \\[ebib--browse-url] can be used to
send a URL to a browser.  This option sets the field from which
this command extracts the URL."
  :group 'ebib
  :type 'string)

(defcustom ebib-url-regexp "\\\\url{\\(.*\\)}\\|https?://[^ ';<>\"\n\t\f]+"
  "Regular expression to extract URLs from a field.
This is the regular expression that Ebib uses to search for URLs
in a field.  With the default value, Ebib considers everything
that is in a LaTeX `\\url{...}' command as a URL, and furthermore
every string of text that starts with `http://' or `https://' and
does not contain whitespace or one of the characters ' \" ; < or >.

Note that the semicolon is added for consistency: it makes it
possible to use the same separator in the `url' field as in the
`file' field."
  :group 'ebib
  :type 'string)

(defcustom ebib-browser-command nil
  "Command to call the browser with.
If this option is unset, Ebib uses the Emacs function
`browse-url' to start a browser.  If you prefer not to use this,
you can set this option to the executable name of your preferred
browser.  For this to work, the browser that you use must be able
to handle a URL on the command line."
  :group 'ebib
  :type '(choice (const :tag "Use standard browser" nil)
                 (string :tag "Specify browser command")))

(defcustom ebib-doi-field "doi"
  "Standard field to store a DOI (digital object identifier) in.
In the index buffer, the command ebib--browse-doi can be used to
send a suitable URL to a browser.  This option sets the field from
which this command extracts the doi."
  :group 'ebib
  :type 'string)

(defcustom ebib-file-field "file"
  "Standard field to store filenames in.
In the index buffer, the command ebib--view-file can be used to
view a file externally.  This option sets the field from which
this command extracts the filename."
  :group 'ebib
  :type 'string)

(defcustom ebib-file-associations '(("pdf" . "xpdf")
                                    ("ps" . "gv"))
  "List of file associations.
Lists file extensions together with external programs to handle
files with those extensions.  The program is searched for in
`exec-path'.

When you open a file for which no external program is defined,
the file is opened in Emacs."
  :group 'ebib
  :type '(repeat (cons :tag "File association"
                       (string :tag "Extension")
                       (choice (const :tag "Open in Emacs" nil)
                               (string :tag "Run external command")))))

(defcustom ebib-filename-separator "; "
  "Separator for filenames in `ebib-file-field'.
The contents of the file field is split up using this separator,
each chunk is assumed to be a filename.

Note that the default value of this option consists of
semicolon-space.  This means you can have semicolons in your file
names, as long as they're not followed by a space."
  :group 'ebib
  :type 'string)

(defcustom ebib-file-search-dirs '("~")
  "List of directories to search when viewing external files.
Note that searching is not recursive: only the files listed here
are searched, not their subdirectories."
  :group 'ebib
  :type '(repeat :tag "Search directories" (string :tag "Directory")))

(defcustom ebib-local-variable-indentation ""
  "Indentation of the local variable block."
  :group 'ebib
  :type '(string :tag "Indentation"))

(defcustom ebib-print-preamble '("\\documentclass{article}")
  "Preamble used for the LaTeX file for printing the database.
This option specifies the preamble that is to be added to the
LaTeX file Ebib creates for printing the database as index cards.
You can set your own `\\usepackage' commands, or anything else
you may need.  See the section \"Printing the Database\" in the
manual/info file for details."
  :group 'ebib
  :type '(repeat (string :tag "Add to preamble")))

(defcustom ebib-print-newpage nil
  "Print each entry on a separate page.
With this option set, Ebib puts every entry on a separate page
when printing index cards.  Otherwise the entries are separated by
a small amount of whitespace only."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-print-multiline nil
  "Include multiline field values when printing the database.
When this options is set, Ebib includes multiline field values
when you print index cards.  Otherwise multiline values are
excluded, which saves space."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-latex-preamble '("\\documentclass{article}" "\\bibliographystyle{plain}")
  "Preamble for the LaTeX file for BibTeXing the database."
  :group 'ebib
  :type '(repeat (string :tag "Add to preamble")))

(defcustom ebib-print-tempfile ""
  "Temporary file for printing the database.
If set, the commands to print the database (`ebib--print-database'
and `ebib--latex-database') write to this file.  Otherwise you are
asked for a file name."
  :group 'ebib
  :type '(file))

(defcustom ebib-allow-identical-fields nil
  "Handle multiple occurrences of a single field gracefully.
Sometimes BibTeX entries from external sources use multiple
identical fields for some reason (e.g., multiple `keyword'
fields).  Normally, only the last value is read by Ebib, but with
this option set, all values are combined into a single field.  See
the section \"Multiple Identical Fields\" in the manual/info
file."
  :group 'ebib
  :type 'boolean)

(defcustom ebib-rc-file "~/.emacs.d/ebibrc"
  "Customization file for Ebib.
This file is read when Ebib is started.  It contains Lisp code,
and can be used to define custom keys or set customization
variables (as an alternative to the customization group), or even
custom commands."
  :group 'ebib
  :type '(file :tag "Customization file:"))

(defcustom ebib-bibtex-extensions '(".bib" ".bibtex")
  "List of possible filename extensions of BibTeX files.
When loading a BibTeX filename without extension, Ebib tries to
find a file by adding these extensions.  When creating a new file,
the first extension is added if the filename provided does not
already have an extension.  If you want to create BibTeX files
without extension, add the empty string \"\" to this list or
unset the option entirely."
  :group 'ebib
  :type '(repeat (string :tag "Extension")))

(defcustom ebib-biblatex-inheritances '(("all"
                                         "all"
                                         (("ids" . none)
                                          ("crossref" . none)
                                          ("xref" . none)
                                          ("entryset" . none)
                                          ("entrysubtype" . none)
                                          ("execute" . none)
                                          ("label" . none)
                                          ("options" . none)
                                          ("presort" . none)
                                          ("related" . none)
                                          ("relatedoptions" . none)
                                          ("relatedstring" . none)
                                          ("relatedtype" . none)
                                          ("shorthand" . none)
                                          ("shorthandintro" . none)
                                          ("sortkey" . none)))

                                        ("inbook, bookinbook, suppbook"
                                         "mvbook, book"
                                         (("author" . "author")
                                          ("bookauthor" . "author")))

                                        ("book, inbook, bookinbook, suppbook"
                                         "mvbook"
                                         (("maintitle" . "title")
                                          ("mainsubtitle" . "subtitle")
                                          ("maintitleaddon" . "titleaddon")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none)))

                                        ("collection, reference, incollection, inreference, suppcollection"
                                         "mvcollection, mvreference"
                                         (("maintitle" . "title")
                                          ("mainsubtitle" . "subtitle")
                                          ("maintitleaddon" . "titleaddon")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none)))

                                        ("proceedings, inproceedings"
                                         "mvproceedings"
                                         (("maintitle" . "title")
                                          ("mainsubtitle" . "subtitle")
                                          ("maintitleaddon" . "titleaddon")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none)))

                                        ("inbook, bookinbook, suppbook"
                                         "book"
                                         (("booktitle" . "title")
                                          ("booksubtitle" . "subtitle")
                                          ("booktitleaddon" . "titleaddon")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none)))

                                        ("incollection, inreference, suppcollection"
                                         "collection, reference"
                                         (("booktitle" . "title")
                                          ("booksubtitle" . "subtitle")
                                          ("booktitleaddon" . "titleaddon")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none)))

                                        ("inproceedings"
                                         "proceedings"
                                         (("booktitle" . "title")
                                          ("booksubtitle" . "subtitle")
                                          ("booktitleaddon" . "titleaddon")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none)))
                                        ("article, suppperiodical"
                                         "periodical"
                                         (("title" . "journaltitle")
                                          ("subtitle" . "journalsubtitle")
                                          ("shorttitle" . none)
                                          ("sorttitle" . none)
                                          ("indextitle" . none)
                                          ("indexsorttitle" . none))))
  "Inheritance scheme for cross-referencing.
This option allows you to define inheritances for BibLaTeX.
Inheritances are specified for pairs of target and source entry
type, where the target is the cross-referencing entry and the
source the cross-referenced entry.  For each pair, specify the
fields that can inherit a value (the targets) and the fields that
they inherit from (the sources).

Inheritances for all entry types can be defined by specifying
`all' as the entry type.  The entry type may also be
a (comma-separated) list of entry types.

If no inheritance rule is set up for a given entry type+field
combination, the field inherits from the same-name field in the
cross-referenced entry.  If no inheritance should take place, set
the source field to \"No inheritance\".

Note that this option is only relevant for BibLaTeX.  If the
BibTeX dialect is set to `BibTeX', this option is ignored."
  :group 'ebib
  :type '(repeat (list (string :tag "Target entry type(s)")
                       (string :tag "Source entry type(s)")
                       (repeat (cons :tag "Inheritance"
                                     (string :tag "Target field")
                                     (choice (string :tag "Source field)")
                                             (const :tag "No inheritance" none)))))))

(defcustom ebib-hide-cursor t
  "Hide the cursor in the Ebib buffers.
Normally, the cursor is hidden in Ebib buffers.  Instead, the
highlight indicates which entry, field or string is active.  By
unsetting this option, you can make the cursor visible.  Note that
changing this option does not take effect until you restart
Ebib (not Emacs)."
  :group 'ebib
  :type '(choice (const :tag "Hide the cursor" t)
                 (const :tag "Show the cursor" nil)))

(defgroup ebib-faces nil "Faces for Ebib" :group 'ebib)

(defface ebib-overlay-face '((t (:inherit highlight)))
  "Face used for the overlays."
  :group 'ebib-faces)

(defface ebib-crossref-face '((t (:inherit font-lock-comment-face)))
  "Face used to indicate values inherited from crossreferenced entries."
  :group 'ebib-faces)

(defface ebib-alias-face '((t (:inherit warning)))
  "Face used to indicate values inherited from crossreferenced entries."
  :group 'ebib-faces)

(defface ebib-marked-face '((t (:inverse-video t)))
  "Face to indicate marked entries."
  :group 'ebib-faces)

(defface ebib-field-face '((t (:inherit font-lock-keyword-face)))
  "Face for field names."
  :group 'ebib-faces)

(defface ebib-nonpermanent-keyword-face '((t (:inherit error)))
  "Face for keywords that have not been made permanent.
Keywords can be made permanent by storing them in
`ebib-keywords-list' or by saving them in a file."
  :group 'ebib-faces)

;; generic for all databases

;; constants and variables that are set only once
(defvar ebib--initialized nil "T if Ebib has been initialized.")

;; Entry type and field aliases defined by BibLaTeX.
(defconst ebib--field-aliases '(("location" . "address")
                                ("annotation" . "annote")
                                ("eprinttype" . "archiveprefix")
                                ("journaltitle" . "journal")
                                ("sortkey" . "key")
                                ("file" . "pdf")
                                ("eprintclass" . "primaryclass")
                                ("institution" . "school"))
  "List of field aliases for BibLaTeX.")

(defconst ebib--type-aliases '(("Conference" . "InProceedings")
                               ("Electronic" . "Online")
                               ("MastersThesis" . "Thesis")
                               ("PhDThesis" . "Thesis")
                               ("TechReport" . "Report")
                               ("WWW" . "Online"))
  "List of entry type aliases for BibLaTeX.")

(defvar ebib--buffer-alist nil "Alist of Ebib buffers.")
(defvar ebib--index-overlay nil "Overlay to mark the current entry.")
(defvar ebib--fields-overlay nil "Overlay to mark the current field.")
(defvar ebib--strings-overlay nil "Overlay to mark the current string.")

;; general bookkeeping
(defvar ebib--field-history nil "Minibuffer field name history.")
(defvar ebib--filters-history nil "Minibuffer history for filters.")
(defvar ebib--cite-command-history nil "Minibuffer history for citation commands.")
(defvar ebib--key-history nil "Minibuffer history for entry keys.")
(defvar ebib--keywords-history nil "Minibuffer history for keywords.")

(defvar ebib--saved-window-config nil "Stores the window configuration when Ebib is called.")
(defvar ebib--window-before nil "The window that was active when Ebib was called.")
(defvar ebib--buffer-before nil "The buffer that was active when Ebib was called.")
(defvar ebib--export-filename nil "Filename to export entries to.")
(defvar ebib--push-buffer nil "Buffer to push entries to.")
(defvar ebib--search-string nil "Stores the last search string.")
(defvar ebib--multiline-buffer-list nil "List of multiline edit buffers.")
(defvar-local ebib--multiline-info nil "Information about the multiline text being edited.")
(defvar ebib--log-error nil "Indicates whether an error was logged.")
(defvar-local ebib--local-bibtex-filenames nil "A list of a buffer's .bib file(s)")
(put 'ebib--local-bibtex-filenames 'safe-local-variable (lambda (v) (null (--remove (stringp it) v))))

;; The databases

;; the master list and the current database
(defvar ebib--databases nil "List of structs containing the databases.")
(defvar ebib--cur-db nil "The database that is currently active.")
(defvar ebib--cur-keys-list nil "Sorted list of entry keys in the current database.")

;; bookkeeping required when editing field values or @STRING definitions

(defvar ebib--hide-hidden-fields t "If set to T, hidden fields are not shown.")

;; the prefix key and the multiline key are stored in a variable so that the
;; user can customise them.
(defvar ebib--prefix-key ?\;)
(defvar ebib--multiline-key ?\|)

;; this is an AucTeX variable, but we want to check its value, so let's
;; keep the compiler from complaining.
(eval-when-compile
  (defvar TeX-master))

;; General functions

(defun ebib--buffer (buffer)
  "Return the buffer object referred to by BUFFER.
BUFFER is a symbol referring to a buffer in
`ebib--buffer-alist'."
  (cdr (assq buffer ebib--buffer-alist)))

(defmacro with-current-ebib-buffer (buffer &rest body)
  "Make BUFFER current and execute BODY.
BUFFER is a symbol referring to a buffer in
`ebib--buffer-alist'."
  (declare (indent defun))
  `(with-current-buffer (cdr (assq ,buffer ebib--buffer-alist))
     ,@body))

(defmacro with-ebib-buffer-writable (&rest body)
  "Make the current buffer writable and execute BODY.
Restore the buffer modified flag after executing BODY."
  (declare (indent defun))
  `(let ((modified (buffer-modified-p)))
     (unwind-protect
         (let ((buffer-read-only nil))
           ,@body)
       (set-buffer-modified-p modified))))

(defmacro with-ebib-window-nondedicated (&rest body)
  "Execute BODY with the current window non-dedicated.
Restore the dedicated status after executing BODY."
  (declare (indent defun))
  `(let ((dedicated (window-dedicated-p)))
     (unwind-protect
         (progn
           (set-window-dedicated-p (selected-window) nil)
           ,@body)
       (if dedicated
           (set-window-dedicated-p (selected-window) t)))))

(defmacro ebib--ifstring (bindvar then &rest else)
  "Bind the string in BINDVAR and execute THEN only if is nonempty.

Format: (ebib--ifstring (var value) then-form [else-forms])

VAR is bound to VALUE, which is evaluated.  If VAR is a nonempty
string, THEN-FORM is executed.  If VAR is either \"\" or nil, the
ELSE-FORMS are executed.  Return the value of THEN or of ELSE."
  (declare (indent 2))
  `(let ,(list bindvar)
     (if (not (or (null ,(car bindvar))
                  (equal ,(car bindvar) "")))
         ,then
       ,@else)))

(eval-and-compile
  (defun ebib--execute-helper (env)
    "Helper function for `ebib--execute-when'."
    (cond
     ((eq env 'entries)
      'ebib--cur-keys-list)
     ((eq env 'marked-entries)
      '(and ebib--cur-db
            (ebib-db-marked-entries-p ebib--cur-db)))
     ((eq env 'database)
      'ebib--cur-db)
     ((eq env 'real-db)
      '(and ebib--cur-db
            (not (ebib-db-get-filter ebib--cur-db))))
     ((eq env 'filtered-db)
      '(and ebib--cur-db
            (ebib-db-get-filter ebib--cur-db)))
     ((eq env 'no-database)
      '(not ebib--cur-db))
     (t t))))

(defmacro ebib--execute-when (&rest forms)
  "Macro to facilitate writing Ebib functions.
This functions essentially like a `cond' clause: the basic format
is (ebib--execute-when FORMS ...), where each FORM is built up
as (ENVIRONMENTS BODY).  ENVIRONMENTS is a list of symbols (not
quoted) that specify under which conditions BODY is to be
executed.  Valid symbols are:

`entries': execute when there are entries in the database,
`marked-entries': execute when there are marked entries in the database,
`database': execute if there is a database,
`no-database': execute if there is no database,
`real-db': execute when there is a database and it is not filtered,
`filtered-db': execute when there is a database and it is filtered,
`default': execute if all else fails.

Just like with `cond', only one form is actually executed, the
first one that matches.  If ENVIRONMENT contains more than one
condition, BODY is executed if they all match (i.e., the
conditions are AND'ed.)"
  (declare (indent defun))
  `(cond
    ,@(mapcar (lambda (form)
                (cons (if (= 1 (length (car form)))
                          (ebib--execute-helper (caar form))
                        `(and ,@(mapcar (lambda (env)
                                          (ebib--execute-helper env))
                                        (car form))))
                      (cdr form)))
              forms)))

(defun ebib--log (type format-string &rest args)
  "Write a message to Ebib's log buffer.
TYPE (a symbol) is the type of message: `log' writes the message
to the log buffer only; `message' writes the message to the log
buffer and outputs it with the function `message'; `warning' logs
the message and sets the variable `ebib--log-error' to 0; finally,
`error' logs the message and sets the variable `ebib--log-error'
to 1. The latter two can be used to signal the user to check the
log for warnings or errors.

FORMAT-STRING and ARGS function as in `format'.  Note that this
function adds a newline to the message being logged."
  (with-current-ebib-buffer 'log
    (cond
     ((eq type 'warning)
      (or ebib--log-error ; If ebib--error-log is already set to 1, we don't want to overwrite it!
          (setq ebib--log-error 0)))
     ((eq type 'error)
      (setq ebib--log-error 1))
     ((eq type 'message)
      (apply #'message format-string args)))
    (insert (apply #'format (concat (if (eq type 'error)
                                        (propertize format-string 'face 'font-lock-warning-face)
                                      format-string)
                                    "\n")
                   args))))

(defun ebib--make-overlay (begin end buffer)
  "Create an overlay from BEGIN to END in BUFFER."
  (let (overlay)
    (setq overlay (make-overlay begin end buffer))
    (overlay-put overlay 'face 'ebib-overlay-face)
    overlay))

(defun ebib--set-index-overlay ()
  "Set the overlay of the index buffer."
  (with-current-ebib-buffer 'index
    (beginning-of-line)
    (let ((beg (point)))
      (if ebib-index-display-fields
          (end-of-line)
        (skip-chars-forward "^ "))
      (move-overlay ebib--index-overlay beg (point) (cdr (assq 'index ebib--buffer-alist)))
      (beginning-of-line))))

(defun ebib--set-fields-overlay ()
  "Set the overlay in the fields buffer."
  (with-current-ebib-buffer 'entry
    (beginning-of-line)
    (save-excursion
      (let ((beg (point)))
        (ebib--looking-at-goto-end "[^ \t\n\f]*")
        (move-overlay ebib--fields-overlay beg (point))))))

(defun ebib--set-strings-overlay ()
  "Set the overlay in the strings buffer."
  (with-current-ebib-buffer 'strings
    (beginning-of-line)
    (save-excursion
      (let ((beg (point)))
        (ebib--looking-at-goto-end "[^ \t\n\f]*")
        (move-overlay ebib--strings-overlay beg (point))))))

(defun ebib--search-key-in-buffer (entry-key)
  "Search ENTRY-KEY in the index buffer.
Point is moved to the first character of the key.  Return value
is the new value of point."
  (goto-char (point-min))
  (re-search-forward (concat "^" entry-key))
  (beginning-of-line)
  (point))

(defvar ebib--info-flag nil "Non-nil means Info was called from Ebib.")

(defadvice Info-exit (after ebib--info-exit activate)
  "Quit info and return to Ebib, if Info was called from there."
  (when ebib--info-flag
    (setq ebib--info-flag nil)
    (ebib)))

(defun ebib--read-file-to-list (filename)
  "Return the contents of FILENAME as a list of lines."
  (if (and filename                               ; protect against 'filename' being 'nil'
           (file-readable-p filename))
      (with-temp-buffer
        (insert-file-contents filename)
        (split-string (buffer-string) "\n" t))))    ; 't' is omit nulls, blank lines in this case

;; We sometimes (often, in fact ;-) need to do something with a string, but
;; take special action (or do nothing) if that string is empty.
;; `ebib--ifstring' makes that easier:

;; we sometimes need to walk through lists.  these functions yield the
;; element directly preceding or following ELEM in LIST. in order to work
;; properly, ELEM must be unique in LIST, obviously. if ELEM is the
;; first/last element of LIST, or if it is not contained in LIST at all,
;; the result is nil.
(defun ebib--next-elem (elem list)
  "Return the element following ELEM in LIST.
If ELEM is the last element, return nil."
  (cadr (member elem list)))

(defun ebib--prev-elem (elem list)
  "Return the element preceding ELEM in LIST.
If ELEM is the first element, return nil."
  (if (or (equal elem (car list))
          (not (member elem list)))
      nil
    (car (last list (1+ (length (member elem list)))))))

(defun ebib--locate-bibfile (file &optional dirs)
  "Locate and/or expand FILE to an absolute filename in DIRS.
First try to locate BibTeX file FILE with `locate-file' and with
`ebib-bibtex-extensions' as possible suffixes.  If this does not
yield a result, expand FILE with `expand-file-name', adding the
first extension in `ebib-bibtex-extensions' if FILE has no
filename suffix."
  (or (locate-file file (or dirs "/") (append '("") ebib-bibtex-extensions))
      (expand-file-name (if (file-name-extension file)
                            file
                          (concat file (car ebib-bibtex-extensions))))))

(defun ebib--ensure-extension (filename ext)
  "Ensure FILENAME has an extension.
Return FILENAME if it alread has an extension, otherwise return
FILENAME appended with EXT.  Note that EXT should start with a
dot."
  (if (file-name-extension filename)
      filename
    (concat filename ext)))

(defun ebib--remove-from-string (string remove)
  "Return a copy of STRING with all the occurrences of REMOVE taken out.
REMOVE can be a regular expression."
  (apply #'concat (split-string string remove)))

(defun ebib--multiline-p (string)
  "Return non-nil if STRING is multiline."
  (if (stringp string)
      (string-match "\n" string)))

(defun ebib--first-line (string)
  "Return the first line of a multiline STRING."
  (if (string-match "\n" string)
      (substring string 0 (match-beginning 0))
    string))

(defun ebib--sort-in-buffer (str limit)
  "Move POINT to the right position to insert STR in the current buffer.
The buffer must contain lines that are sorted A--Z.  LIMIT is the
last line of the buffer.  Note that STR is not actually
inserted."
  (let ((upper limit)
        middle)
    (when (> limit 0)
      (let ((lower 0))
        (goto-char (point-min))
        (while (progn
                 (setq middle (/ (+ lower upper 1) 2))
                 (goto-char (point-min))
                 (forward-line (1- middle)) ; if this turns out to be where we need to be,
                 (beginning-of-line)        ; this puts POINT at the right spot.
                 ;; if upper and lower differ by only 1, we have found the
                 ;; position to insert the entry in.
                 (> (- upper lower) 1))
          (save-excursion
            (let ((beg (point)))
              (end-of-line)
              (if (string< (buffer-substring-no-properties beg (point)) str)
                  (setq lower middle)
                (setq upper middle)))))))))

(defun ebib--match-all-in-string (match-str string)
  "Highlight all the matches of MATCH-STR in STRING.
The return value is a list of two elements: the first is the
modified string, the second either t or nil, indicating whether a
match was found at all."
  (cl-do ((counter 0 (match-end 0)))
      ((not (string-match match-str string counter)) (cl-values string (not (= counter 0))))
    (add-text-properties (match-beginning 0) (match-end 0) '(face highlight) string)))

(defun ebib--looking-at-goto-end (regexp &optional match)
  "Return t if text after point matches REGEXP and move point.
MATCH acts just like the argument to MATCH-END, and defaults to
0."
  (or match (setq match 0))
  (let ((case-fold-search t))
    (if (looking-at regexp)
        (goto-char (match-end match)))))

(defun ebib--special-field-p (field)
  "Return t if FIELD is a special field.
Speciald fields are those whose names start and end with an equal sign."
  (string-match-p "\\`=[[:alpha:]]*=\\'" field))

(defun ebib--local-vars-to-list (str)
  "Convert STR to a list of local variables.
STR must start with \"Local Variables:\" and end with \"End:\".
The return value is a list of lists, where each sublist has the
form (\"<variable>\" \"<value>\"). If STR is not a local variable
block, the return value is nil."
  (let ((vars (split-string str "[\n]+" t "[ \t\r]+")))
    (when (and (string= (car vars) "Local Variables:")
               (string= (-last-item vars) "End:"))
      (--map (split-string it "[: ]" t) (-slice vars 1 -1)))))

(defun ebib--local-vars-add-dialect (vars dialect &optional overwrite)
  "Expand local variable block VARS with DIALECT.
VARS is a list as returned by `ebib--local-vars-to-list'.
DIALECT must be a symbol, possible values are listed in
`bibtex-dialect-list'.  If OVERWRITE is non-nil, overwrite an
existing dialect variable, otherwise do nothing.  The return
value is the (un)modified list."
  (let ((ind (--find-index (string= (car it) "bibtex-dialect") vars)))
    (if ind
        (when overwrite
          (setq vars (-replace-at ind (list "bibtex-dialect" (symbol-name dialect)) vars)))
      (setq vars (push (list "bibtex-dialect" (symbol-name dialect)) vars)))
    vars))

(defun ebib--local-vars-delete-dialect (vars)
  "Delete the dialect definition from VARS.
VARS is a list as returned by `ebib--local-vars-to-list'.  VARS is
not modified, instead the new list is returned."
  (--remove (string= (car it) "bibtex-dialect") vars))

;; The numeric prefix argument is 1 if the user gave no prefix argument at
;; all. The raw prefix argument is not always a number. So we need to do
;; our own conversion.
(defun ebib--prefix (num)
  "Return NUM if it is a number, otherwise return nil.
This can be used to check if the user provided a numeric prefix
argument to a function or not."
  (when (numberp num)
    num))

;; TODO The exporting macros and functions should be rewritten...

(defmacro ebib--export-to-db (num message copy-fn)
  "Export data to another database.
NUM is the number of the database to which the data is to be copied.

MESSAGE is a string displayed in the echo area if the export was
succesful.  It must contain a %d directive, which is used to
display the database number to which the entry was exported.

COPY-FN is the function that actually copies the relevant
data.  It must take as argument the database to which the data is
to be copied.  COPY-FN must return T if the copying was
successful, and NIL otherwise."
  (let ((goal-db (make-symbol "goal-db")))
    `(let ((,goal-db (nth (1- ,num) ebib--databases)))
       (if (not ,goal-db)
           (error "Database %d does not exist" ,num)
         (when (funcall ,copy-fn ,goal-db)
           (ebib--set-modified t ,goal-db)
           (message ,message ,num))))))

(defmacro ebib--export-to-file (prompt-string insert-fn)
  "Export data to a file.
PROMPT-STRING is the string that is used to ask for the filename
to export to.  INSERT-FN must insert the data to be exported into
the current buffer: it is called within a `with-temp-buffer',
whose contents is appended to the file the user enters."
  (let ((filename (make-symbol "filename")))
    `(let ((insert-default-directory (not ebib--export-filename)))
       (ebib--ifstring (,filename (read-file-name
                                   ,prompt-string "~/" nil nil ebib--export-filename))
           (with-temp-buffer
             (funcall ,insert-fn)
             (append-to-file (point-min) (point-max) ,filename)
             (setq ebib--export-filename ,filename))))))

(defun ebib--list-fields (entry-type type dialect)
  "List the fields of ENTRY-TYPE.
TYPE specifies which fields to list.  It is a symbol and can be
one of the following: `required' means to list only required
fields; `optional' means to list optional fields; `extra' means
to list extra fields (i.e., fields defined in `ebib--extra-fields'
and not present in ENTRY-TYPE); finally, `all' means to list all
fields.  DIALECT is the BibTeX dialect; possible values are those
listed in `bibtex-dialect-list' or NIL, in which case the value
of `ebib-bibtex-dialect' is used.

If DIALECT is `biblatex' and ENTRY-TYPE is a type alias as
defined by BibLaTeX, return the fields of the entry type for
which ENTRY-TYPE is an alias."
  (or dialect (setq dialect ebib-bibtex-dialect))
  (if (eq dialect 'biblatex)
      (setq entry-type (or (cdr (assoc-string entry-type ebib--type-aliases 'case-fold))
                           entry-type)))
  (let (required optional extra)
    (when (memq type '(required extra all))
      (setq required (mapcar #'car (append (nth 2 (assoc-string entry-type (bibtex-entry-alist dialect) 'case-fold))
                                           (nth 3 (assoc-string entry-type (bibtex-entry-alist dialect) 'case-fold))))))
    (when (memq type '(optional extra all))
      (setq optional (mapcar #'car (nth 4 (assoc-string entry-type (bibtex-entry-alist dialect) 'case-fold)))))
    (when (memq type '(all extra))
      (setq extra (--remove (member-ignore-case it (append required optional)) (cdr (assq dialect ebib-extra-fields)))))
    (cond
     ((eq type 'required) required)
     ((eq type 'optional) optional)
     ((eq type 'extra) extra)
     ((eq type 'all) (append required optional extra)))))

(defun ebib--list-undefined-fields (entry dialect)
  "Return an alist of fields of ENTRY that are not predefined.
ENTRY is an alist representing a BibTeX entry.  The return value
is an alist of (field . value) pairs of those fields that are not
part of the definition of ENTRY's type and also not part of the
extra fields.

DIALECT is the BibTeX dialect; possible values are those listed
in `bibtex-dialect-list' or NIL, in which case the value of
`ebib-bibtex-dialect' is used."
  (or dialect (setq dialect ebib-bibtex-dialect))
  (let ((fields (ebib--list-fields (cdr (assoc "=type=" entry)) 'all dialect)))
    (--remove (member-ignore-case (car it) (cons "=type=" fields)) entry)))

(defun ebib--list-entry-types (&optional dialect include-aliases)
  "Return a list of entry types.
This list depends on the value of DIALECT, which can have the
values in `bibtex-dialect-list' or NIL, in which case the value
of `ebib-bibtex-dialect' is used.  If INCLUDE-ALIASES is non-NIL,
include entry type aliases as defined by `ebib--type-aliases'."
  (or dialect (setq dialect ebib-bibtex-dialect))
  (append (mapcar #'car (bibtex-entry-alist dialect))
          (if (and include-aliases (eq dialect 'biblatex))
              (mapcar #'car ebib--type-aliases))))

(defvar ebib--unique-field-alist nil
  "Alist of BibTeX dialects and their fields.
This variable is initialized by `ebib--list-field-uniquely'.")

(defun ebib--list-fields-uniquely (dialect)
  "Return a list of all fields of BibTeX DIALECT.
Possible values for DIALECT are those listed in
`bibtex-dialect-list' or NIL, in which case the value of
`ebib-bibtex-dialect' is used."
  (or dialect (setq dialect ebib-bibtex-dialect))
  (or (cdr (assq dialect ebib--unique-field-alist))
      (let (fields)
        (mapc (lambda (entry)
                (setq fields (-union fields (ebib--list-fields (car entry) 'all dialect))))
              (bibtex-entry-alist dialect))
        (add-to-list 'ebib--unique-field-alist (cons dialect fields))
        fields)))

(defun ebib--erase-buffer (buffer)
  "Erase BUFFER, even if it is read-only."
  (with-current-buffer buffer
    (with-ebib-buffer-writable
      (erase-buffer))))

(provide 'ebib-utils)

;;; ebib-utils.el ends here
