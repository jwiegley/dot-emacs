;; rs-info.el -- Some info related functions
;; $Id: rs-info.el,v 1.29 2008/03/21 21:07:40 ste Exp $

;; Author: Reiner Steib <Reiner.Steib@gmx.de>
;; Keywords: info
;; X-URL: http://theotp1.physik.uni-ulm.de/~ste/comp/emacs/misc/rs-info.el

;;; This program is free software; you can redistribute it and/or modify
;;; it under the terms of the GNU General Public License as published by
;;; the Free Software Foundation; either version 2 of the License, or
;;; (at your option) any later version.
;;;
;;; This program is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.
;;;
;;; You should have received a copy of the GNU General Public License
;;; along with this program; if not, write to the Free Software
;;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:
;; Some functions related to info mode in Emacs.

;;; Installation:

;; Put `rs-info.el' in a directory that's in your `load-path',
;; e.g. ~/lisp:
;;
;; (add-to-list 'load-path "~/lisp")
;;
;; Put the following autoloads in your init file:
;;
;; (autoload 'rs-info-insert-current-node "rs-info"
;;   "Insert reference to current Info node using STYLE in buffer." t nil)
;; (autoload 'rs-info-boxquote "rs-info"
;;   "Yank text (from an info node), box it and use current info node as title."
;;   t nil)
;; (autoload 'rs-info-reload "rs-info" "Reload current info node." t nil)
;; (autoload 'rs-info-insert-node-for-variable "rs-info"
;;   "Insert a custom style info node for the top level form at point." t nil)
;; (defalias 'boxquote-info 'rs-info-boxquote)

;;; History:

;; 2003/11/17 Note on XEmacs.
;;
;; 2003/11/28 Added `rs-info-insert-node-for-variable'.  Use `rs-info' prefix.
;;            Added alias `boxquote-info', suggested by Dave Pearson.

;; See `grep-changelog --text="rs-info.el" ChangeLog' for later changes.

;;; Code:

(autoload 'boxquote-yank "boxquote")

(defgroup rs-info nil
  "Info related functions."
  :group 'info)

(defun rs-info-replace-in-string (string regexp newtext)
  "In STRING, replace all matches for REGEXP with NEWTEXT.
Hack to get a common function for all Emacsen.  Note that Oort Gnus has
`gnus-replace-in-string', but we don't want to load Gnus."
  (cond
   ;; Emacs 21 and later
   ((fboundp 'replace-regexp-in-string)
    (replace-regexp-in-string regexp newtext string))
   ;; Emacs < 21; XEmacs
   (t
    ;; Code duplicated from `subr.el' revision 1.423 of Emacs.  Neither
    ;; `replace-in-string' from XEmacs 21.4.15 nor the Gnus replacement works
    ;; correctly when an empty string is matched.
    (let ((rep newtext)
	  (l (length string))
	  (start 0) ;; (or start 0) in `subr.el'
	  fixedcase literal subexp
	  matches str mb me)
      (save-match-data
	(while (and (< start l) (string-match regexp string start))
	  (setq mb (match-beginning 0)
		me (match-end 0))
	  ;; If we matched the empty string, make sure we advance by one char
	  (when (= me mb) (setq me (min l (1+ mb))))
	  ;; Generate a replacement for the matched substring.
	  ;; Operate only on the substring to minimize string consing.
	  ;; Set up match data for the substring for replacement;
	  ;; presumably this is likely to be faster than munging the
	  ;; match data directly in Lisp.
	  (string-match regexp (setq str (substring string mb me)))
	  (setq matches
		(cons (replace-match (if (stringp rep)
					 rep
				       (funcall rep (match-string 0 str)))
				     fixedcase literal str subexp)
		      (cons (substring string start mb)	; unmatched prefix
			    matches)))
	  (setq start me))
	;; Reconstruct a string from the pieces.
	(setq matches (cons (substring string start l) matches)) ; leftover
	(apply #'concat (nreverse matches)))))))


;;;###autoload
(defcustom rs-info-goto-node-string "info" ;; "Info-goto-node"
  ;; Stefan Monnier suggested to use `info' instead of `Info-goto-node', but
  ;; this doesn't work for XEmacs.  OTOH, I've submitted a patch for XEmacs,
  ;; so "info" should be okay (included in XEmacs >= 21.5.12).
  "String to insert with `rs-info-insert-current-node'."
  :group 'rs-info
  :type 'string)

;;;###autoload
(defcustom rs-info-style-alist
  '((emacs-lisp-mode custom-manual)
    (texinfo-mode    texinfo-ref)
    ;; (message-mode    emacs)
    (t               emacs))
  "Alist of major modes and prefered info styles.
A `t' entry corresponds to the default style used when no matching mode is
found."
  :group 'rs-info
  :type '(repeat (list (symbol :tag "Mode")
		       (symbol :tag "Style"))))

(defcustom rs-info-title-alist
  '(("^de\\.comp\\.text\\.tex" "http://www.dante.de/faq/de-tex-faq/")
    ("^comp\\.text\\.tex"      "http://www.tex.ac.uk/cgi-bin/texfaq2html")
    ("^de\\.comm\\.mozilla"    "http://www.holgermetzger.de/faq.html"))
  "Alist of Gnus groups (regexp) and boxquote titles"
  :group 'rs-info
  :type '(repeat (list (regexp :tag "Groups regexp")
		       (string :tag "Title"))))

;;;###autoload
(defcustom rs-info-buffer-name "*info*"
  "Name of the info buffer"
  :group 'rs-info
  :type '(string :tag "Buffer name"))

;;;###autoload
(defun rs-info-switch-buffer-name (&optional reset)
  "Switch `rs-info-buffer-name'.  If RESET, switch to default value."
  (interactive "P")
  (setq rs-info-buffer-name
	(if current-prefix-arg
	    "*info*"
	  (read-buffer "Buffer: " rs-info-buffer-name t))))

;;;###autoload
(defun rs-info-insert-current-node (style &optional noinsert)
  "Insert reference to current Info node using STYLE in buffer.

If NOINSERT (the prefix), return the string instead.

Possible styles (must be a symbol):
- `emacs' (Emacs style): \(info \"\(file\)node\"\)
- `emacs-press': as `emacs' plus a note about `C-x C-e'
- `emacs-keys-goto' (Emacs key sequence): `C-h i g (file)node RET'
- `emacs-keys-menu' (Emacs menu key sequence): `C-h i d m file RET m node RET'
- `custom-manual': \":link '(custom-manual \"(file)node\")\" for `defcustom'
- `info-link': \":link '(info-link \"(file)node\")\" for `defcustom'
- `texinfo-ref-full': A full \"@ref{...}\" for Texinfo
- `texinfo-ref': \"@ref{...}\" for Texinfo within the same file
- `gnus' (the Gnus home brewed style): <info://foo/bar+baz> (deprecated)
- `gnome' (GNOME style): <info:foo#bar_baz>
- `kde' (KDE style): <info:(foo)bar baz>
- `konqueror' (Konqueror style): <info:/foo/bar baz>

When used interactively, the default is taken from `rs-info-style-alist'.

For `emacs' and `emacs-press' style see the variable
`rs-info-goto-node-string'."
  ;; `rs-info-replace-in-string' may be replaced by `gnus-replace-in-string' or
  ;; `replace-regexp-in-string' (Emacs) or `replace-in-string' (XEmacs).
  (interactive
   (list (let ((default (or (cadr (assq major-mode rs-info-style-alist))
			    (cadr (assq t rs-info-style-alist))) )
	       (completion-ignore-case t))
	   (completing-read
	    "Info URL style: "
	    (mapcar (lambda (method) (list (format "%s" method)))
		    '("emacs"  "emacs-press"
		      "emacs-keys" "emacs-keys-goto" "emacs-keys-menu"
		      "texinfo-ref" "texinfo-ref-full"
		      "gnus"
		      ;; "defcustom" is obsolete
		      "custom-manual" "info-link"
		      "gnome" "kde" "konqueror"))
	    nil t;; PREDICATE REQUIRE-MATCH
	    (if default
		(symbol-name default)
	      ;; no default entry in found `rs-info-style-alist'
	      "")))
	 current-prefix-arg))
  ;; Because of the above use of `completing-read', we also accept strings as
  ;; STYLE (undocumented feature ;-))
  (unless (symbolp style)
    (setq style (intern style)))
  (let ((buffer (buffer-name))
	(ret ""))
    ;; The next lines were orginally borrowed from Karl Pflaesterer's code in
    ;; <m3eli7tgp0.fsf@hamster.pflaesterer.de>.
    (set-buffer rs-info-buffer-name)
    (let* ((node Info-current-node)
	   (node+ (rs-info-replace-in-string node " " "+"))
	   (node_ (rs-info-replace-in-string node " " "_"))
	   (node-SPC (rs-info-replace-in-string node " " " SPC "))
	   (fileurl (file-name-nondirectory Info-current-file))
	   ;; XEmacs doesn't strip extensions in `Info-current-file'.
	   ;; http://thread.gmane.org/gmane.emacs.xemacs.beta/12741
	   (fileurl (rs-info-replace-in-string
		     fileurl "\\(\\.info\\|\\.gz\\'\\)+" "")))
      (setq ret
	    (cond
	     ((or (eq style 'custom-manual)
		  (eq style 'defcustom))
	      (concat ":link '(custom-manual \"(" fileurl ")" node "\")"))
	     ((eq style 'info-link)
	      (concat ":link '(info-link \"(" fileurl ")" node "\")"))
	     ((eq style 'texinfo-ref-full)
	      ;; an approximation:
	      (concat "@ref{" node ", " node ", , " fileurl ", "
		      (capitalize fileurl) " Manual}"))
	     ((eq style 'texinfo-ref)
	      (concat "@ref{" node "}"))
	     ((eq style 'gnome)
	      (concat "<info:" fileurl "#" node_ ">"))
	     ((eq style 'kde)
	      (concat "<info:(" fileurl ")" node ">"))
	     ((eq style 'konqueror)
	      (concat "<info:/" fileurl "/" node ">"))
	     ((eq style 'gnus)
	      (concat "<info://" fileurl "/" node+ ">"))
	     ;; FIXME: Not sure, if this is correct for all nodes.
	     ;;        Gnus should take advantage of `node' here, too.
	     ((eq style 'emacs-keys-menu)
	      (concat "`C-h i d m " fileurl " RET m " node-SPC " RET'"))
	     ;;
	     ((or (eq style 'emacs-keys) (eq style 'emacs-keys-goto))
	      (concat "`C-h i g (" fileurl ")" node-SPC " RET'"))
	     ((or (eq style 'emacs) (eq style 'emacs-press))
	      (concat "(" rs-info-goto-node-string
		      " \"(" fileurl ")" node "\")"
		      (if (eq style 'emacs-press)
			  "; <== Press C-x C-e here!"
			"")))
	     (t
	      (error "Style `%s' is not valid" style))))
      (if noinsert
	  ret
	(set-buffer buffer)
	(if (not (or (eq style 'custom-manual)
		     (eq style 'info-link)
		     (eq style 'defcustom)))
	    (insert ret)
	  (beginning-of-line)
	  (insert ret)
	  (lisp-indent-line)
	  (newline))))))

;;;###autoload
(defun rs-info-insert-node-for-variable ()
  "Insert a custom style info node for the top level form at point.

Limitations: Finding the relevant node is done by looking up the index of the
current info buffer, i.e. you need to choose the appropriate manual before.
It only finds the first match in the index.  You should probably open the info
buffer in another visible frame or buffer to double check the results."
  (interactive)
  ;; FIXME: Don't abuse `eval-defun' to find the name
  (let ((var (eval-defun nil)))
    (save-excursion
      (set-buffer rs-info-buffer-name)
      (Info-index (symbol-name var)))
    (rs-info-insert-current-node 'defcustom)))

;;;###autoload
(defun rs-info-boxquote (&optional use-list)
  "Yank text (from an info node), box it and use current info node as title.
If USE-LIST, the title is taken from `rs-info-title-alist'
depending on the current newsgroup."
  (interactive)
  (boxquote-yank)
  (let ((grp (or (and (boundp 'gnus-newsgroup-name)
		      gnus-newsgroup-name)
		 (and (eq major-mode 'message-mode)
		      (message-fetch-field "Newsgroups"))))
	title)
    (setq title
	  (if current-prefix-arg
	      (dolist (ti rs-info-title-alist)
		(when (string-match (car ti) grp)
		  (cadr ti)))
	    (save-excursion (rs-info-insert-current-node 'emacs 'string))))
    (if title
	(boxquote-title title)
      (message "No title found for group `%s'" grp))))

;;;###autoload
(defalias 'boxquote-info 'rs-info-boxquote)
;; The author of `boxquote.el' (Dave Pearson <davep@davep.org>) suggested to
;; add an alias `boxquote-info' to `rs-info-boxquote'.  He won't use this name
;; in `boxquote.el' so there will be no namespace clash.

;;;###autoload
(defun rs-info-reload ()
  "Reload current info node."
  (interactive)
  (let ((file Info-current-file)
	(node Info-current-node)
	(point (point)))
    ;; Info-revert-find-node from Emacs CVS prevents jumping; use it when
    ;; available.
    (if (fboundp 'Info-revert-find-node)
	(Info-revert-find-node file node)
      (kill-buffer rs-info-buffer-name)
      (Info-find-node file node)
      (goto-char point))))

;;; provide ourself

(provide 'rs-info)

;;; rs-info.el ends here
