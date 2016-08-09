;;; enumitem.el --- AUCTeX style for `enumitem.sty' (v3.5.2)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-20
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for `enumitem.sty' (v3.5.2) from 2011/09/28.
;; `enumitem.sty' is part of TeXLive.

;; Tassilo Horn's `minted.el' was a major source of inspiration for
;; this style, many thanks to him (also for patiently answering my
;; many other questions, incl. the stupid ones.)

;; If things do not work or when in doubt, press `C-c C-n'.  Comments
;; for improvement are welcome.

;;; Code:

;; Needed for compiling `pushnew':
(eval-when-compile (require 'cl))

;; Needed for auto-parsing.
(require 'tex)

(defvar LaTeX-enumitem-key-val-options
  '(;; Vertical Spacing
    ("topsep")
    ("partopsep")
    ("parsep")
    ("itemsep")
    ;; Horizontal Spacing
    ("leftmargin"  ("*" "!"))
    ("itemindent"  ("*" "!"))
    ("labelsep"    ("*" "!"))
    ("labelwidth"  ("*" "!"))
    ("labelindent" ("*" "!"))
    ("labelsep*")
    ("labelindent*")
    ("widest")
    ("widest*")
    ("rightmargin")
    ;; Labels and cross reference format
    ("label")
    ("label*")
    ("ref")
    ("font")
    ("format")
    ("align" ("left" "right" "parleft"))
    ;; Numbering, stopping, resuming
    ("start")
    ("resume")
    ("resume*")
    ;; Series
    ("series")
    ;; Penalties
    ("beginpenalty")
    ("midpenalty")
    ("endpenalty")
    ("before")
    ("before*")
    ("after")
    ("after*")
    ;; Description styles
    ("style" ("standard" "multiline" "nextline" "sameline" "unboxed"))
    ;; Compact lists
    ("noitemsep")
    ("nosep")
    ;; Wide lists
    ("wide")
    ;; Inline lists
    ("itemjoin")
    ("itemjoin*")
    ("afterlabel")
    ("mode" ("boxed" "unboxed")))
  "Key=value options for enumitem macros and environments.")

(defvar LaTeX-enumitem-key-val-options-local nil
  "Buffer-local key=value options for enumitem macros and environments.")
(make-variable-buffer-local 'LaTeX-enumitem-key-val-options-local)

;; Variables needed for \newlist: This command is not hooked into
;; the parser via `TeX-auto-add-type', we mimic that behaviour.

(defvar LaTeX-enumitem-newlist-list nil
  "List of environments defined by command `\\newlist' from
`enumitem' package.")

(defvar LaTeX-enumitem-newlist-list-local nil
  "Local list of all environments definded with `\\newlist'
plus available through `enumitem' package.")
(make-variable-buffer-local 'LaTeX-enumitem-newlist-list-local)

(defvar LaTeX-enumitem-newlist-list-item-arg nil
  "List of description like environments defined by command
`\\newlist' from `enumitem' package.")

(defvar LaTeX-auto-enumitem-newlist nil
  "Temporary for parsing the arguments of `\\newlist' from
`enumitem' package.")

(defvar LaTeX-enumitem-newlist-regexp
  '("\\\\newlist{\\([^}]+\\)}{\\([^}]+\\)}"
    (1 2) LaTeX-auto-enumitem-newlist)
  "Matches the arguments of `\\newlist' from `enumitem'
package.")


;; Setup for \SetEnumitemKey:

(TeX-auto-add-type "enumitem-SetEnumitemKey" "LaTeX")

(defvar LaTeX-enumitem-SetEnumitemKey-regexp
  '("\\\\SetEnumitemKey{\\([^}]+\\)}"
    1 LaTeX-auto-enumitem-SetEnumitemKey)
  "Matches the arguments of `\\SetEnumitemKey' from `enumitem'
package.")


;; Setup for \SetEnumitemValue:

(TeX-auto-add-type "enumitem-SetEnumitemValue" "LaTeX")

;; Upon Tassilo's recommendation, we include also `0' so that we can
;; use the function `LaTeX-enumitem-SetEnumitemValue-list' while we
;; make sure that `TeX-auto-list-information' doesn't remove multiple
;; defined values to a specific key.  For this reason, we also ignore
;; the 3. argument to the `\SetEnumitemValue' macro (i.e., a third
;; {\\([^}]+\\)} in regex) so that we don't pollute the generated
;; `docname.el' with unnecessary (La)TeX code.
(defvar LaTeX-enumitem-SetEnumitemValue-regexp
  '("\\\\SetEnumitemValue{\\([^}]+\\)}{\\([^}]+\\)}"
    (0 1 2) LaTeX-auto-enumitem-SetEnumitemValue)
  "Matches the arguments of `\\SetEnumitemValue' from `enumitem'
package.")

;; Plug them into the machinery.
(defun LaTeX-enumitem-auto-prepare ()
  "Clear various `LaTeX-enumitem-*' before parsing."
  (setq	LaTeX-auto-enumitem-newlist          nil
	LaTeX-enumitem-newlist-list          nil
	LaTeX-enumitem-newlist-list-item-arg nil
	LaTeX-auto-enumitem-SetEnumitemKey   nil
	LaTeX-auto-enumitem-SetEnumitemValue nil))

(defun LaTeX-enumitem-auto-cleanup ()
  "Move parsing results into right places for further usage."
  ;; \newlist{<name>}{<type>}{<max-depth>}
  ;; env=<name>, type=<type>, ignored=<max-depth>
  (dolist (env-type LaTeX-auto-enumitem-newlist)
    (let* ((env  (car env-type))
	   (type (cadr env-type)))
      (add-to-list 'LaTeX-auto-environment
		   (list env 'LaTeX-enumitem-env-with-opts))
      (add-to-list 'LaTeX-enumitem-newlist-list
		   (list env))
      (when (or (string-equal type "description")
		(string-equal type "description*"))
	(add-to-list 'LaTeX-enumitem-newlist-list-item-arg
		     (list env)))))
  ;; Now add the parsed env's to the local list.
  (when LaTeX-enumitem-newlist-list
    (setq LaTeX-enumitem-newlist-list-local
	  (append LaTeX-enumitem-newlist-list
		  LaTeX-enumitem-newlist-list-local)))
  ;; Tell AUCTeX about parsed description like environments.
  (when LaTeX-enumitem-newlist-list-item-arg
    (dolist (env LaTeX-enumitem-newlist-list-item-arg)
      (add-to-list 'LaTeX-item-list `(,(car env) . LaTeX-item-argument)))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-enumitem-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-enumitem-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-enumitem-env-with-opts (env)
  "Update available key-val options, then insert ENV and optional
key-val and the first item."
  (LaTeX-enumitem-update-key-val-options)
  (LaTeX-insert-environment
   env
   (let ((opts (TeX-read-key-val t LaTeX-enumitem-key-val-options-local)))
     (when (and opts (not (string-equal opts "")))
       (format "[%s]" opts))))
  (if (TeX-active-mark)
      (progn
	(LaTeX-find-matching-begin)
	(end-of-line 1))
    (end-of-line 0))
  (delete-char 1)
  (when (looking-at (concat "^[ \t]+$\\|"
			    "^[ \t]*" TeX-comment-start-regexp "+[ \t]*$"))
    (delete-region (point) (line-end-position)))
  (delete-horizontal-space)
  ;; Deactivate the mark here in order to prevent `TeX-parse-macro'
  ;; from swapping point and mark and the \item ending up right after
  ;; \begin{...}.
  (TeX-deactivate-mark)
  (LaTeX-insert-item)
  ;; The inserted \item may have outdented the first line to the
  ;; right.  Fill it, if appropriate.
  (when (and (not (looking-at "$"))
	     (not (assoc environment LaTeX-indent-environment-list))
	     (> (- (line-end-position) (line-beginning-position))
		(current-fill-column)))
    (LaTeX-fill-paragraph nil)))

(defun LaTeX-arg-SetEnumitemKey (optional)
  "Ask for a new key to be defined and add it to
`LaTeX-enumitem-key-val-options-local'."
  (LaTeX-enumitem-update-key-val-options)
  (let ((key     (TeX-read-string "New Key: "))
	(replace (TeX-read-key-val optional
				   LaTeX-enumitem-key-val-options-local "Replacement")))
    (TeX-argument-insert key     optional)
    (TeX-argument-insert replace optional)
    (add-to-list 'LaTeX-enumitem-key-val-options-local (list key))
    (LaTeX-add-enumitem-SetEnumitemKeys key)))

;; In `LaTeX-enumitem-SetEnumitemValue-regexp', we match (0 1 2).
;; When adding a new `key=val', we need something unique for `0'-match
;; until the next `C-c C-n'.  We mimic that regex-match bei concat'ing
;; the elements and pass the result to
;; `LaTeX-add-enumitem-SetEnumitemValues'.  It will vanish upon next
;; invocation of `C-c C-n'.
(defun LaTeX-arg-SetEnumitemValue (optional)
  "Ask for a new value added to an existing key incl. the final
replacement of the value."
  (LaTeX-enumitem-update-key-val-options)
  (let* ((key (TeX-read-key-val optional LaTeX-enumitem-key-val-options-local "Key"))
	 (val (TeX-read-string "String value: "))
	 ;; (key-match (car (assoc key LaTeX-enumitem-key-val-options-local)))
	 (val-match (cdr (assoc key LaTeX-enumitem-key-val-options-local)))
	 (temp (copy-alist LaTeX-enumitem-key-val-options-local))
	 (opts (assq-delete-all (car (assoc key temp)) temp)))
    (if val-match
	(pushnew (list key (delete-dups (apply 'append (list val) val-match)))
		 opts :test #'equal)
      (pushnew (list key (list val)) opts :test #'equal))
    (setq LaTeX-enumitem-key-val-options-local (copy-alist opts))
    (TeX-argument-insert key optional)
    (TeX-argument-insert val optional)
    (LaTeX-add-enumitem-SetEnumitemValues
     (list (concat "\\SetEnumitemValue{" key "}{" val "}")
	   key val))))

(defun LaTeX-enumitem-update-key-val-options ()
  "Update the buffer-local key-val options before offering them
in `enumitem'-completions."
  (dolist (key (LaTeX-enumitem-SetEnumitemKey-list))
    (add-to-list 'LaTeX-enumitem-key-val-options-local key))
  (dolist (keyvals (LaTeX-enumitem-SetEnumitemValue-list))
    (let* ((key (nth 1 keyvals))
	   (val (nth 2 keyvals))
	   ;; (key-match (car (assoc key LaTeX-enumitem-key-val-options-local)))
	   (val-match (cdr (assoc key LaTeX-enumitem-key-val-options-local)))
	   (temp  (copy-alist LaTeX-enumitem-key-val-options-local))
	   (opts (assq-delete-all (car (assoc key temp)) temp)))
      (if val-match
	  (pushnew (list key (delete-dups (apply 'append (list val) val-match)))
		   opts :test #'equal)
	(pushnew (list key (list val)) opts :test #'equal))
      (setq LaTeX-enumitem-key-val-options-local (copy-alist opts)))))


(TeX-add-style-hook
 "enumitem"
 (lambda ()

   ;; Add enumitem to the parser.
   (TeX-auto-add-regexp LaTeX-enumitem-newlist-regexp)
   (TeX-auto-add-regexp LaTeX-enumitem-SetEnumitemKey-regexp)
   (TeX-auto-add-regexp LaTeX-enumitem-SetEnumitemValue-regexp)

   ;; Activate the buffer-local version of key-vals.
   (setq LaTeX-enumitem-key-val-options-local
	 (copy-alist LaTeX-enumitem-key-val-options))

   ;; Set the standard env's to the local list.
   (setq LaTeX-enumitem-newlist-list-local
	 '(("itemize") ("enumerate") ("description")))

   ;; Add the starred versions to the local list.
   (when (LaTeX-provided-package-options-member "enumitem" "inline")
     (setq LaTeX-enumitem-newlist-list-local
	   (append '(("itemize*") ("enumerate*") ("description*"))
		   LaTeX-enumitem-newlist-list-local)))

   ;; Standard env's take key-val as optional argument.
   (LaTeX-add-environments
    '("itemize"      LaTeX-enumitem-env-with-opts)
    '("enumerate"    LaTeX-enumitem-env-with-opts)
    '("description"  LaTeX-enumitem-env-with-opts))

   ;; Make inline env's available with package option "inline"
   (when (LaTeX-provided-package-options-member "enumitem" "inline")
     (LaTeX-add-environments
      '("itemize*"     LaTeX-enumitem-env-with-opts)
      '("enumerate*"   LaTeX-enumitem-env-with-opts)
      '("description*" LaTeX-enumitem-env-with-opts))
     (add-to-list 'LaTeX-item-list '("description*" . LaTeX-item-argument)))

   ;; Cloning lists
   (TeX-add-symbols
    ;; The easy way would be:
    ;; '("newlist"
    ;;   "Name" (TeX-arg-eval
    ;;           completing-read "Type: "
    ;;                 '(("itemize")  ("enumerate")  ("description")
    ;;                   ("itemize*") ("enumerate*") ("description*")))
    ;;  "Max-depth")
    ;; But we go the extra mile to improve the user experience and add
    ;; the arguments directly to appropriate lists.
    ;; \newlist{<name>}{<type>}{<max-depth>}
    '("newlist"
      (TeX-arg-eval
       (lambda ()
	 (let ((name (TeX-read-string "Name: "))
	       (type (completing-read
		      "Type: "
		      '(("itemize")  ("enumerate")  ("description")
			("itemize*") ("enumerate*") ("description*"))))
	       (depth (TeX-read-string "Max-depth: ")))
	   (setq LaTeX-enumitem-newlist-list-local
		 (append `(,(list name)) LaTeX-enumitem-newlist-list-local))
	   (when (or (string-equal type "description")
		     (string-equal type "description*"))
	     (add-to-list 'LaTeX-item-list `(,name . LaTeX-item-argument)))
	   (LaTeX-add-environments `(,name LaTeX-enumitem-env-with-opts))
	   (insert (format "{%s}" name)
		   (format "{%s}" type))
	    (format "%s" depth)))))

    ;; \renewlist{<name>}{<type>}{<max-depth>}
    '("renewlist"
      (TeX-arg-eval completing-read "Name: "
		    LaTeX-enumitem-newlist-list-local)
      (TeX-arg-eval completing-read "Type: "
		    '(("itemize")  ("enumerate")  ("description")
		      ("itemize*") ("enumerate*") ("description*")))
      "Max-depth")

    ;; \setlist[<names,levels>]{<key-vals>}
    '("setlist"
      [TeX-arg-eval mapconcat 'identity
		    (TeX-completing-read-multiple
		     "Environment(s), level(s): "
		     `(,@LaTeX-enumitem-newlist-list-local
		       ("1") ("2") ("3") ("4"))) ","]
      (TeX-arg-eval
       (lambda ()
	 (LaTeX-enumitem-update-key-val-options)
	 (let ((opts (TeX-read-key-val nil LaTeX-enumitem-key-val-options-local)))
	   (format "%s" opts)))))

    ;; \setlist*[<names,levels>]{<key-vals>}
    '("setlist*"
      [TeX-arg-eval mapconcat 'identity
		    (TeX-completing-read-multiple
		     "Environment, level: "
		     `(,@LaTeX-enumitem-newlist-list-local
		       ("1") ("2") ("3") ("4"))) ","]
      (TeX-arg-eval
       (lambda ()
	 (LaTeX-enumitem-update-key-val-options)
	 (let ((opts (TeX-read-key-val nil LaTeX-enumitem-key-val-options-local)))
	   (format "%s" opts))))) )

   ;; General commands:
   (TeX-add-symbols

    ;; Ask for an Integer and insert it.
    '("setlistdepth" "Integer")

    ;; Just add the braces and let the user do the rest.
    '("AddEnumerateCounter" 3)
    '("AddEnumerateCounter*" 3)

    ;; This command only makes sense for enumerate type environments.
    ;; Currently, we offer all defined env's -- to be improved
    ;; sometimes.
    '("restartlist"
      (TeX-arg-eval completing-read "List name: "
		    LaTeX-enumitem-newlist-list-local))

    ;; "Key" will be parsed and added to key-val list.
    '("SetEnumitemKey" LaTeX-arg-SetEnumitemKey)

    ;; "Key" and "Value" are added to our key-val list
    '("SetEnumitemValue" LaTeX-arg-SetEnumitemValue "Replacement"))

   ;; Setting enumerate short label
   (when (LaTeX-provided-package-options-member "enumitem" "shortlabels")
     (TeX-add-symbols
      '("SetEnumerateShortLabel"
	(TeX-arg-eval completing-read "Key: "
		      '(("A") ("a") ("I") ("i") ("1")))
	"Replacement")))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("newlist"             "{{{")
				("renewlist"           "{{{")
				("setlist"             "*[{")
				("AddEnumerateCounter" "*{{{")
				("SetEnumitemKey"      "{{" )
				("SetEnumitemValue"    "{{{"))
			      'function)
     (font-latex-add-keywords '(("restartlist"            "{" )
				("setlistdepth"           "{" )
				("SetEnumerateShortLabel" "{{"))
			      'variable)))
 LaTeX-dialect)

(defvar LaTeX-enumitem-package-options
  '("inline" "ignoredisplayed" "shortlabels" "loadonly")
  "Package options for the enumitem package.")

;;; enumitem.el ends here
