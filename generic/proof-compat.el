;; proof-compat.el   Operating system and Emacs version compatibility
;;
;; Copyright (C) 2000-2002 LFCS Edinburgh. 
;; Author:      David Aspinall <da@dcs.ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;; This file collects together compatibility hacks for different
;; operating systems and Emacs versions.  This is to help keep
;; track of them.
;;
;; The development policy for Proof General is for the main codebase
;; to be written for the latest stable version of XEmacs.  We follow
;; XEmacs advice on removing obsolete function calls.
;;

(require 'proof-site)			; for architecture flags

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Emacs and XEmacs modifications and adjustments
;;;

;; Remove a custom setting.  Needed to support dynamic reconfiguration.
;; (We'd prefer that repeated defcustom calls acted like repeated
;;  "defvar treated as defconst" in XEmacs)
(defun pg-custom-undeclare-variable (symbol)
  "Remove a custom setting SYMBOL.
Done by `makunbound' and removing all properties mentioned by custom library."
  (mapcar (lambda (prop) (remprop symbol prop))
	  '(default 
	     standard-value 
	     force-value 
	     variable-comment
	     saved-variable-comment
	     variable-documentation
	     group-documentation
	     custom-set
	     custom-get
	     custom-options
	     custom-requests
	     custom-group
	     custom-prefix
	     custom-tag
	     custom-links
	     custom-version
	     saved-value
	     theme-value
	     theme-face))
  (makunbound symbol))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; XEmacs compatibility
;;;

;; browse-url function isn't autoloaded in XEmacs 20.4
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

;; executable-find isn't autoloaded in XEmacs 21.4.6
(or (fboundp 'executable-find)
    (autoload 'executable-find "executable" "\
Search for COMMAND in exec-path and return the absolute file name.
Return nil if COMMAND is not found anywhere in `exec-path'." nil nil))


;; Compatibility with XEmacs 20.3/4
(or (boundp 'path-separator)
    (setq path-separator (if proof-running-on-win32 ";" ":")))
(or (fboundp 'split-path)
    (defun split-path (path)
      "Explode a search path into a list of strings.
The path components are separated with the characters specified
with `path-separator'."
      (split-string path (regexp-quote path-separator))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; XEmacs compatibility with GNU Emacs
;;;

(or (fboundp 'display-graphic-p)
    (defun display-graphic-p ()
      "Return non-nil if DISPLAY is a graphic display.
Graphical displays are those which are capable of displaying several
frames and several different fonts at once.  This is true for displays
that use a window system such as X, and false for text-only terminals."
      (or (eq (console-type) 'x)
	  (eq (console-type) 'mswindows))))

(or (fboundp 'subst-char-in-string)
;; Code is taken from Emacs 21.2.1/subr.el 
(defun subst-char-in-string (fromchar tochar string &optional inplace)
  "Replace FROMCHAR with TOCHAR in STRING each time it occurs.
Unless optional argument INPLACE is non-nil, return a new string."
  (let ((i (length string))
	(newstr (if inplace string (copy-sequence string))))
    (while (> i 0)
      (setq i (1- i))
      (if (eq (aref newstr i) fromchar)
	  (aset newstr i tochar)))
    newstr)))

(or (fboundp 'replace-regexp-in-string)
;; Code is taken from Emacs 21.1.1/subr.el 
(defun replace-regexp-in-string (regexp rep string &optional
					fixedcase literal subexp start)
  "Replace all matches for REGEXP with REP in STRING.

Return a new string containing the replacements.

Optional arguments FIXEDCASE, LITERAL and SUBEXP are like the
arguments with the same names of function `replace-match'.  If START
is non-nil, start replacements at that index in STRING.

REP is either a string used as the NEWTEXT arg of `replace-match' or a
function.  If it is a function it is applied to each match to generate
the replacement passed to `replace-match'; the match-data at this
point are such that match 0 is the function's argument.

To replace only the first match (if any), make REGEXP match up to \\'
and replace a sub-expression, e.g.
  (replace-regexp-in-string \"\\(foo\\).*\\'\" \"bar\" \" foo foo\" nil nil 1)
    => \" bar foo\"
"

  ;; To avoid excessive consing from multiple matches in long strings,
  ;; don't just call `replace-match' continually.  Walk down the
  ;; string looking for matches of REGEXP and building up a (reversed)
  ;; list MATCHES.  This comprises segments of STRING which weren't
  ;; matched interspersed with replacements for segments that were.
  ;; [For a `large' number of replacments it's more efficient to
  ;; operate in a temporary buffer; we can't tell from the function's
  ;; args whether to choose the buffer-based implementation, though it
  ;; might be reasonable to do so for long enough STRING.]
  (let ((l (length string))
	(start (or start 0))
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
		    (cons (substring string start mb) ; unmatched prefix
			  matches)))
	(setq start me))
      ;; Reconstruct a string from the pieces.
      (setq matches (cons (substring string start l) matches)) ; leftover
      (apply #'concat (nreverse matches))))))


;; The GNU Emacs implementation of easy-menu-define has a very handy
;; :visible keyword.  To use that when it's available, we set a
;; constant to be :visible or :active

(defconst menuvisiblep (if proof-running-on-Emacs21 :visible :active)
  ":visible (on GNU Emacs) or :active (otherwise). 
The GNU Emacs implementation of easy-menu-define has a very handy
:visible keyword.  To use that when it's available, we use this constant.")

 



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GNU Emacs compatibility
;;;

;; Chars (borrowed from x-symbol-emacs.el compatability file)

(unless (fboundp 'characterp) (defalias 'characterp 'integerp))
(unless (fboundp 'int-to-char) (defalias 'int-to-char 'identity))
(unless (fboundp 'char-to-int) (defalias 'char-to-int 'identity))

;; Missing function, but anyway Emacs has no datatype for events...

(unless (fboundp 'events-to-keys)
  (defalias 'events-to-keys 'identity))

(unless (fboundp 'region-exists-p)
  (defun region-exists-p () mark-active))

;; completion not autoloaded in GNU 20.6.1; we must call 
;; dynamic-completion-mode after loading it.
(or (fboundp 'complete)
    (autoload 'complete "completion"))
(unless proof-running-on-XEmacs
  (eval-after-load "completion"
    '(dynamic-completion-mode)))


;; These days cl is dumped with XEmacs (20.4,21.1) but not GNU Emacs
;; 20.2.  Would rather it was autoloaded but the autoloads are broken
;; in GNU so we load it now.
(require 'cl)				

;; Give a warning,
(or (fboundp 'warn)
(defun warn (str &rest args)
      "Issue a warning STR.  Defined by PG for GNU compatibility."
      (apply 'message str args)
      (sit-for 2)))

;; Modeline redrawing (actually force-mode-line-update is alias on XEmacs)
(or (fboundp 'redraw-modeline)
(defun redraw-modeline (&rest args)
  "Dummy function for Proof General on GNU Emacs."
  (force-mode-line-update)))

;; Interactive flag
(or (fboundp 'noninteractive)
    (defun noninteractive ()
      "Dummy function for Proof General on GNU Emacs."
      noninteractive))

;; Replacing in string (useful function from subr.el in XEmacs 21.1.9)
(or (fboundp 'replace-in-string)
    (if (fboundp 'replace-regexp-in-string)
      (defun replace-in-string (str regexp newtext &optional literal)
        (replace-regexp-in-string regexp newtext str 'fixedcase literal))
(defun replace-in-string (str regexp newtext &optional literal)
  "Replace all matches in STR for REGEXP with NEWTEXT string,
 and returns the new string.
Optional LITERAL non-nil means do a literal replacement.
Otherwise treat \\ in NEWTEXT string as special:
  \\& means substitute original matched text,
  \\N means substitute match for \(...\) number N,
  \\\\ means insert one \\."
  ;; Not present in GNU
  ;; (check-argument-type 'stringp str)
  ;; (check-argument-type 'stringp newtext)
  (let ((rtn-str "")
	(start 0)
	(special)
	match prev-start)
    (while (setq match (string-match regexp str start))
      (setq prev-start start
	    start (match-end 0)
	    rtn-str
	    (concat
	      rtn-str
	      (substring str prev-start match)
	      (cond (literal newtext)
		    (t (mapconcat
			(lambda (c)
			  (if special
			      (progn
				(setq special nil)
				(cond ((eq c ?\\) "\\")
				      ((eq c ?&)
				       (substring str
						  (match-beginning 0)
						  (match-end 0)))
				      ((and (>= c ?0) (<= c ?9))
				       (if (> c (+ ?0 (length
						       (match-data))))
					   ;; Invalid match num
					   (error "Invalid match num: %c" c)
					 (setq c (- c ?0))
					 (substring str
						    (match-beginning c)
						    (match-end c))))
				      (t (char-to-string c))))
			    (if (eq c ?\\) (progn (setq special t) nil)
			      (char-to-string c))))
			 newtext ""))))))
    (concat rtn-str (substring str start))))))

;; An implemenation of buffer-syntactic-context for GNU Emacs
(defun proof-buffer-syntactic-context-emulate (&optional buffer)
  "Return the syntactic context of BUFFER at point.
If BUFFER is nil or omitted, the current buffer is assumed.
The returned value is one of the following symbols:

	nil		; meaning no special interpretation
	string		; meaning point is within a string
	comment		; meaning point is within a line comment"
  (save-excursion
    (if buffer (set-buffer buffer))
    (let ((pp (parse-partial-sexp (point-min) (point))))
      (cond
       ((nth 3 pp) 'string)
       ;; ((nth 7 pp) 'block-comment)
       ;; "Stefan Monnier" <monnier+misc/news@rum.cs.yale.edu> suggests
       ;; distinguishing between block comments and ordinary comments
       ;; is problematic: not what XEmacs claims and different to what
       ;; (nth 7 pp) tells us in GNU Emacs.
       ((nth 4 pp) 'comment)))))


;; In case Emacs is not aware of the function read-shell-command,
;; we duplicate some code adjusted from minibuf.el distributed 
;; with XEmacs 21.1.9
;;
;; This code is still required as of GNU Emacs 20.6.1
;;
;; da: I think bothering with this just to give completion for
;; when proof-prog-name-ask=t is rather a big overkill!
;; Still, now it's here we'll leave it in as a pleasant surprise
;; for GNU Emacs users.
;;	
(or (fboundp 'read-shell-command)
(defvar read-shell-command-map
  (let ((map (make-sparse-keymap 'read-shell-command-map)))
    (if (not (fboundp 'set-keymap-parents))
	(if (fboundp 'set-keymap-parent)
	    ;; GNU Emacs 20.2
	    (set-keymap-parent map minibuffer-local-map)
	  ;; Earlier GNU Emacs
	  (setq map (append minibuffer-local-map map)))
      ;; XEmacs versions without read-shell-command?
      (set-keymap-parents map minibuffer-local-map))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by `shell-command' and related commands."))


(or (fboundp 'read-shell-command)
(defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history 'shell-command-history)))))


;; Emulate a useful builtin from XEmacs.

(or (fboundp 'remassq)
(defun remassq (key alist)
  "Delete any elements of ALIST whose car is `eq' to KEY.
The modified ALIST is returned."
;; The builtin version deletes by side-effect, but don't bother here.
  (let (newalist)
    (while alist
      (unless (eq key (caar alist))
	(setq newalist (cons (car alist) newalist)))
      (setq alist (cdr alist)))
    (nreverse newalist))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; A naughty hack to completion.el 
;;;
;;; At the moment IMO completion too eagerly adds stuff to
;;; its database: the completion-before-command function
;;; makes every suffix be added as a completion!

(eval-after-load "completion"
'(defun completion-before-command ()
  (if (and (symbolp this-command) (get this-command 'completion-function))
	(funcall (get this-command 'completion-function)))))
      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Old Emacs version compatibility
;;;

;; Create a menu from a customize group, for older/non-existent customize

(if (or
     (and (equal emacs-major-version 21) ; or for buggy Emacs 21.2.1
	  (member emacs-minor-version '(2 0)))
     (not (fboundp 'customize-menu-create)))
    (defun customize-menu-create (&rest args)
      "Dummy function for PG; please upgrade your Emacs."
      nil))

(or (fboundp 'process-live-p)
(defun process-live-p (obj)
  "Return t if OBJECT is a process that is alive"
  (and (processp obj)
       (memq (process-status obj) '(open run stop)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; General Emacs version compatibility
;;;


;; These are internal functions of font-lock, autoload policy
;; differs between Emacs versions

;; Beware: font-lock-set-defaults does completely different things
;; in Emacs from what it does in XEmacs.
(or (fboundp 'font-lock-set-defaults)
    (autoload 'font-lock-set-defaults "font-lock"))
(or (fboundp 'font-lock-fontify-region)
    (autoload 'font-lock-fontify-region "font-lock"))
(or (fboundp 'font-lock-append-text-property)
    (autoload 'font-lock-append-text-property "font-lock"))


;; font-lock-preprocessor-face
;; This face is missing from Emacs 21.2's font-lock,
;; but used in Isabelle highlighting, at least.
(eval-after-load "font-lock"
(unless (boundp 'font-lock-preprocessor-face)
  ;; Taken from font-lock.el in XEmacs 21.4.8 (V 1.52)
  (defvar font-lock-preprocessor-face 'font-lock-preprocessor-face
  "This variable should not be set.
The corresponding face should be set using `edit-faces' or the
`set-face-*' functions.")

  (defface font-lock-preprocessor-face
  '((((class color) (background dark)) (:foreground "steelblue1"))
    (((class color) (background light)) (:foreground "blue3"))
    (t (:underline t)))
  "Font Lock Mode face used to highlight preprocessor conditionals."
  :group 'font-lock-faces)))


;; Handle buggy buffer-syntactic-context workaround in XEmacs 21.1,
;; and GNU non-implementation.

(cond
 ((not (fboundp 'buffer-syntactic-context))
  (defalias 'proof-buffer-syntactic-context 
    'proof-buffer-syntactic-context-emulate))
 ((or
   (string-match "21\.1 .*XEmacs" emacs-version)
   (string-match "21\.4 .*XEmacs" emacs-version)) ;; still buggy in 21.4
  (defalias 'proof-buffer-syntactic-context 
    'proof-buffer-syntactic-context-emulate))
 (t
  ;; Rashly assume this version has a good implementation
  (defalias 'proof-buffer-syntactic-context
    'buffer-syntactic-context)))
   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Nasty: Emacs bug/problem fix section
;;;





;; End of proof-compat.el
(provide 'proof-compat)
