;; proof-comapt.el   Operating system and Emacs version compatibility
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
;;; XEmacs compatibility
;;;

;; browse-url function isn't autoloaded in XEmacs 20.4
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

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
;;; GNU Emacs compatibility with XEmacs
;;;

(if proof-running-on-Emacs21
    (defun proof-emacs-imagep (img)
      "See if IMG is an Emacs 21 image descriptor."
      (and (listp img) (eq (car img) 'image)))
  ;; Otherwise, constant nil function
  (defun proof-emacs-imagep (img)
    "See if IMG is an Emacs 21 image descriptor (returns nil since not E21)."
    nil))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GNU Emacs compatibility
;;;

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
      nil)) ;; pretend always interactive.

;; Replacing in string (useful function from subr.el in XEmacs 21.1.9)
(or (fboundp 'replace-in-string)
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
    (concat rtn-str (substring str start)))))

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
    (let ((pp (parse-partial-sexp 1 (point))))
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
	  (setq map (append minibuffer-local-map map))
	  ;; XEmacs versions without read-shell-command?
	  (set-keymap-parents map minibuffer-local-map)))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by shell-command and related commands."))


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

(or (fboundp 'customize-menu-create)
(defun customize-menu-create (&rest args)
  "Dummy function for PG; please upgrade your Emacs."
  nil))

(or (fboundp 'process-live-p)
(defun process-live-p (obj)
  "Return t if OBJECT is a process that is alive"
  (memq (process-status proc) '(open run stop))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; General Emacs version compatibility
;;;


;; These are internal functions of font-lock, autoload policy
;; differs between Emacs versions

(or (fboundp 'font-lock-set-defaults)
    (autoload 'font-lock-set-defaults "font-lock"))
(or (fboundp 'font-lock-fontify-region)
    (autoload 'font-lock-fontify-region "font-lock"))
(or (fboundp 'font-lock-append-text-property)
    (autoload 'font-lock-append-text-property "font-lock"))


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


;; Error in GNU emacs that this is undefined.  I haven't time to
;; investigate why.
(unless proof-running-on-XEmacs
  (defvar font-lock-preprocessor-face nil))



;; End of proof-compat.el
(provide 'proof-compat)