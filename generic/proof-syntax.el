;; proof-syntax.el	Functions for dealing with syntax
;;
;; Copyright (C) 1997-2001 LFCS Edinburgh. 
;; Authors:   David Aspinall, Healfdene Goguen, 
;;	      Thomas Kleymann, Dilip Sequiera
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

(require 'font-lock)
(require 'proof-config)			; proof-case-fold-search
(require 'proof-compat)			; proof-buffer-syntactic-context

(defun proof-ids-to-regexp (l)
  "Maps a non-empty list of tokens `l' to a regexp matching any element"
  (concat "\\_<\\(?:" (mapconcat 'identity l "\\|") "\\)\\_>"))

(defun proof-anchor-regexp (e)
  "Anchor (\\`) and group the regexp E."
  (concat "\\`\\(" e "\\)"))

(defconst proof-no-regexp
  "\\'\\`"
  "A regular expression that never matches anything")


(defun proof-regexp-alt (&rest args)
  "Return the regexp which matches any of the regexps ARGS."
  ;; see regexp-optn (NB: but that is for strings, not regexps)
  (let ((res ""))
    (dolist (regexp args)
      (setq res (concat res (if (string-equal res "") "\\(" "\\|\\(")
			regexp "\\)")))
    res))

(defun proof-regexp-region (start end)
  "Return regexp matching START anything over several lines END."
  ;; FIXME: would like to use shy grouping here \\(?: but it seems
  ;; buggy or unimplemented in XEmacs.
  ;; WARNING: this produces nasty regexps that lead to stack
  ;; overflows.  It's better to have a loop that searches over lines,
  ;; see next function.
  (concat "\\(" start "\\)\\(\n\\|.\\)*\\(" end "\\)"))

(defun proof-re-search-forward-region (startre endre)
  "Search for a region delimited by regexps STARTRE and ENDRE.
Return the start position of the match for STARTRE, or
nil if a region cannot be found."
  (if (re-search-forward startre nil t)
      (let ((start (match-beginning 0)))
	(if (re-search-forward endre nil t)
	    start))))

;; Functions for string matching and searching that take into account
;; value of proof-case-fold-search.  Last arg to string-match is not
;; applicable.

(defun proof-search-forward (string &optional bound noerror count)
  "Like search-forward, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (search-forward string bound noerror count)))

(defun proof-replace-regexp-in-string (regexp rep string)
  "Like replace-regexp-in-string, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (replace-regexp-in-string regexp rep string)))

(defun proof-re-search-forward (regexp &optional bound noerror count)
  "Like re-search-forward, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (re-search-forward regexp bound noerror count)))

(defun proof-re-search-backward (regexp &optional bound noerror count)
  "Like re-search-backward, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (re-search-backward regexp bound noerror count)))

(defun proof-string-match (regexp string &optional start)
  "Like string-match, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (string-match regexp string start)))

(defun proof-string-match-safe (regexp string &optional start)
  "Like proof-string-match, but return nil if REGEXP or STRING is nil."
  (if (and regexp string) (proof-string-match regexp string start)))

(defun proof-stringfn-match (regexp-or-fn string)
  "Like proof-string-match if first arg is regexp, otherwise call it."
  (cond ((stringp regexp-or-fn)
	 (proof-string-match regexp-or-fn string))
	((functionp regexp-or-fn)
	 (funcall regexp-or-fn string))))

(defun proof-looking-at (regexp)
  "Like looking-at, but set case-fold-search to proof-case-fold-search."
  (let
      ((case-fold-search proof-case-fold-search))
    (looking-at regexp)))

(defun proof-looking-at-safe (regexp)
  "Like proof-looking-at, but return nil if REGEXP is nil."
  (if regexp (proof-looking-at regexp)))

(defun proof-looking-at-syntactic-context-default ()
  "Default function for `proof-looking-at-syntactic-context'."
  (or
   (proof-buffer-syntactic-context)
   (save-match-data 
     (when (proof-looking-at-safe proof-script-comment-start-regexp) 'comment))
   (save-match-data
     (when (proof-looking-at-safe proof-string-start-regexp) 'string))))

;; Replacing matches

(defsubst proof-replace-string (string to-string)
  "Non-interactive `replace-string', using `proof-case-fold-search'."
  (while (proof-search-forward string nil t)
    (replace-match to-string nil t)))

(defsubst proof-replace-regexp (regexp to-string)
  "Non-interactive `replace-regexp', using `proof-case-fold-search'."
  (while (proof-re-search-forward regexp nil t)
    (replace-match to-string nil nil)))

(defsubst proof-replace-regexp-nocasefold (regexp to-string)
  "Non-interactive `replace-regexp', forcing `case-fold-search' to nil."
  (let ((case-fold-search nil))
    (while (proof-re-search-forward regexp nil t)
      (replace-match to-string nil nil))))

;; Generic font-lock

(defvar proof-id "\\(\\w\\(\\w\\|\\s_\\)*\\)"
  "A regular expression for parsing identifiers.")

;; For font-lock, we treat ,-separated identifiers as one identifier
;; and refontify commata using \{proof-zap-commas}.

(defun proof-ids (proof-id &optional sepregexp)
  "Generate a regular expression for separated lists of identifiers.
Default is comma separated, or SEPREGEXP if set."
  (concat proof-id "\\(\\s-*"   (or sepregexp ",") "\\s-*"
	  proof-id "\\)*"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; A function to unfontify commas in declarations and definitions.
;; Useful for provers which have declarations of the form x,y,z:Ty
;; All that can be said for it is that the previous ways of doing
;; this were even more bogus....

(defun proof-zap-commas (limit)
  "Remove the face of all `,' from point to LIMIT.
Meant to be used from `font-lock-keywords'."
  (while (proof-search-forward "," limit t)
    (if (memq (get-text-property (1- (point)) 'face)
	      '(proof-declaration-name-face
		font-lock-variable-name-face
		font-lock-function-name-face))
	(put-text-property (1- (point)) (point) 'face nil))))

;;
;; Functions for doing something like "format" but with customizable
;; control characters.
;;

;;;###autoload
(defun proof-format (alist string)
  "Format a string by matching regexps in ALIST against STRING.
ALIST contains (REGEXP . REPLACEMENT) pairs where REPLACEMENT
may be a string or sexp evaluated to get a string."
  (while alist
    (let ((idx 0))
      (while (string-match (car (car alist)) string idx)
	(setq string
	      (concat (substring string 0 (match-beginning 0))
		      (cond
		       ((stringp (cdr (car alist)))
			(cdr (car alist)))
		       (t
			(eval (cdr (car alist)))))
		      (substring string (match-end 0))))
	(setq idx (+ (match-beginning 0) (length (cdr (car alist)))))))
    (setq alist (cdr alist)))
  string)

(defun proof-format-filename (string filename)
  "Format STRING by replacing quoted chars by escaped version of FILENAME.

%e uses the canonicalized expanded version of filename (including
directory, using default-directory -- see `expand-file-name').

%r uses the unadjusted (possibly relative) version of FILENAME.

%m ('module') uses the basename of the file, without directory
or extension.

%s means the same as %e.

Using %e can avoid problems with dumb proof assistants who don't
understand ~, for example.

For all these cases, the escapes in `proof-shell-filename-escapes'
are processed.

If STRING is in fact a function, instead invoke it on FILENAME and
return the resulting (string) value."
  (cond
   ((functionp string)
    (funcall string filename))
   (t
    (proof-format
     (list (cons "%s" (proof-format proof-shell-filename-escapes
				    (expand-file-name filename)))
	   (cons "%e" (proof-format proof-shell-filename-escapes
				    (expand-file-name filename)))
	   (cons "%r" (proof-format proof-shell-filename-escapes
				    filename))
	   (cons "%m" (proof-format proof-shell-filename-escapes
				    (file-name-nondirectory
				     (file-name-sans-extension filename)))))
     string))))


;;
;; Functions for inserting text into buffer.
;;

; Taken from Isamode
;
;  %l  - insert the value of isa-logic-name
;  %s  - insert the value returned by isa-current-subgoal

(defun proof-insert (text)
  "Insert TEXT into the current buffer.
TEXT may include these special characters:
  %p  - place the point here after input
Any other %-prefixed character inserts itself."
  ; would be quite nice to have this function:
  ;(isa-delete-pending-input)
  (let ((i 0) pos acc)
    (while (< i (length text))
      (let ((ch (elt text i)))
	(if (not (eq ch ?%))
	    (setq acc (concat acc (char-to-string ch)))
	  (setq i (1+ i))
	  (setq ch (elt text i))
	  (cond ;((eq ch ?l)
		; (setq acc (concat acc isa-logic-name)))
		;((eq ch ?s)
		; (setq acc
		;       (concat acc
		;	       (int-to-string
		;		(if (boundp 'isa-denoted-subgoal)
		;		    isa-denoted-subgoal
		;		  1)))))
		;((eq ch ?n)
		; (if acc (insert acc))
		; (setq acc nil)
		; (scomint-send-input))
		((eq ch ?p)
		 (if acc (insert acc))
		 (setq acc nil)
		 (setq pos (point)))
		(t (setq acc (concat acc (char-to-string ch)))))))
      (setq i (1+ i)))
    (if acc (insert acc))
    (if pos (goto-char pos))))

;;;###autoload
(defun proof-splice-separator (sep strings)
  "Splice SEP into list of STRINGS, ignoring nil entries."
  (let (stringsep)
    (while strings
      (when (car strings) ; suppress nils 
	(setq stringsep (concat stringsep (car strings)))
	(if (and (cdr strings) (cadr strings))
	    (setq stringsep
		  (concat stringsep sep))))
      (setq strings (cdr strings)))
    stringsep))

(provide 'proof-syntax)
