;;; wordnet.el --- A simple wordnet mode

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-04-18>
;; Keywords: wordnet, dictionary, lookup

(defconst wordnet-version "0.3")
(defconst wordnet-homepage
  "http://members.a1.net/t.link/CompEmacsWordnet.html")

 
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA


;;; Commentary:

;; ;---(:excerpt-beg Word-Net :name desc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsWordnet")---
;; 
;; A simple [[http://www.cogsci.princeton.edu/wn/][wordnet]] mode.
;; 
;; Installation: Put (require 'wordnet) (wordnet-install) into your
;; startup/user init file. The default value of `wordnet-command-line'
;; requires w3m to be installed.
;; 
;; 
;; *** Important Commands
;; 
;; wordnet-lookup :: Look up the word at point.
;; 
;; wordnet-lookup-specific :: Look up the word at point in a specific
;; dictionary.
;; 
;; wordnet-lookup-selection :: Look up the primary X selection. Could be
;; used as in: =gnuclient -eval '(wordnet-lookup-selection t)'=
;; 
;; wordnet-run-wn-with-word-at-mouse :: Look up the word the mouse is
;; pointing at.
;; 
;; 
;; *** Important Variables
;; 
;; wordnet-query-word-flag :: Query user before running
;; `wordnet-command-line'.
;; 
;; wordnet-command-line :: The command line used to get wordnet's overview. 
;; %w is replaced with the word you want to lookup.
;; 
;; 
;; *** Default key binding in the Wordnet buffer
;; 
;; q               | `wordnet-bury'
;; Q               | `wordnet-quit'
;; k               | `wordnet-delete-frame'
;; h               | `wordnet-history-show'
;; return          | `wordnet-run-wn-with-word-at-point-anyway'
;; control button1 | `wordnet-run-wn-with-word-at-mouse-anyway'
;; button2         | `wordnet-run-wn-with-word-at-mouse-anyway'
;; button3         | `wordnet-popmenu-at-mouse'
;; control button3 | `wordnet-popmenu-at-mouse-volatile'
;; 
;; ;---(:excerpt-end Word-Net :name desc)---


;;; Change log:

;; ;---(:excerpt-beg Word-Net :name hist)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsWordnet")---
;; 
;; =0.3= :: :nullmatch (see `wordnet-command-line').
;; 
;; =0.2= :: Remember lookup modes; volatile lookups; mode sensible command
;; selection (attempted integration with man, apropos, describe-function,
;; describe-variable); new placeholders in command lines: %l, %{Width};
;; pop-up menu; different ways to run/eval a command line
;; 
;; =0.1= :: Initial release (tested with XEmacs)
;; 
;; ;---(:excerpt-end Word-Net :name hist)---


;;; To do:


;;; Code:

(require 'thingatpt)
(require 'ispell)

(require 'tellib)


(defgroup wordnet nil
  "A simple wordnet mode."
  :link `(url-link :tag "Homepage" ,wordnet-homepage)
  :link '(emacs-commentary-link :tag "Commentary" "wordnet.el")
  :prefix "wordnet-"
  :group 'convenience)

(defcustom wordnet-command-line
  '(
;;; Text
    ("WordNet" "wn \"%w\" -over|fmt -t -w %{Width}"
     (:overview
      (:name "WordNet \"%w\"")
      ;;(:language ("british" "english" "american"))
      ))
    ("Soundslike (aspell)" "echo %w | aspell --language-tag=%l soundslike"
     ((:name "Sounds like \"%w\"")))
;;; Shell mode
    ("Shell Apropos" "apropos \"%w\"|w3m -dump"
     ((:name "Shell Apropos \"%w\"")
      (:mode (sh-mode))))
    ("Shell Manual" "man \"%w\"|w3m -dump"
     (:overview (:name "Shell Manual \"%w\"") (:mode (sh-mode))))
;;; Elisp mode
    ("Elisp Help"
     "(cond ((fboundp '%w) (describe-function '%w))
 ((boundp '%w) (describe-variable '%w)))"
     (:no-output
      (:eval eval)
      (:name "Elisp Describe \"%w\"")
      (:mode (emacs-lisp-mode))))
    ("Elisp Apropos" "(apropos '%w)"
     (:no-output
      (:eval eval)
      (:name "Elisp Apropos \"%w\"")
      (:mode (emacs-lisp-mode))))
    )
  "*A association list with command lines used to get wordnet's overview.
Format: '\(\(NAME COMMAND-LINE \(OPTIONS ...)) ...)

Name:
An identifier string.

Command-Line:
The command line will be executed using `shell-command-to-string'.
Non-wordnet example: \"grep -i \\\"%w\\\" /opt/ding/lib/ger-eng.txt\"

Placeholders in command-lines and :name arguments:
	%w       ... the word at point
	%l       ... `ispell-local-dictionary'
	%{Width} ... `window-width'
	%%       ... %

Options:
:overview ... Run this command when compiling an overview.

:stretch ... Stretch the output for better readability by replacing some
\\n with \\n\\n.

:no-output ... This command yields no interesting output.

:language (LANGUAGES ...) ... Run this command only if one of the
symbols of `wordnet-language-vars' is equal to one of these languages.

:mode (MODES ...) ... Run this command only if one of the symbols of
`wordnet-mode-vars' is equal to one of these modes.

:eval [shell|process|eval] ... How to evaluate the command line.
	shell   ... `shell-command-to-string' (the default)
	process ... `start-process-shell-command' (if 'shell doesn't work)
	eval    ... `eval' (the command line is an Elisp form)

:name STRING ... use STRING as display name (defaults to the command line).

:format FUNCTION ... format result string using this function, which
takes one argumen -- the string.

:nullmatch REGEXP ... If the result matches this string, it is
considered to be null. The REGEXP knows the same expansion strings as
does the command line.
"
  :type `(repeat
	  (list :tag "Command Line" :value ("" "" nil nil)
		(string :tag "Name" :value "")
		(string :tag "Command" :value "")
		(repeat :tag "Options"
			(choice
			 (const :tag "Run on Overview" :value :overview)
			 (const :tag "Strech Output"   :value :stretch)
			 (const :tag "No output"       :value :no-output)
			 (const :tag "Eval as Elisp form" :value :eval)
			 (list :tag "Eval" :value
			       (:eval 'shell)
			       (const :format "" :value :eval)
			       (choice
				(symbol :tag "Shell" :value shell)
				(symbol :tag "Process" :value process)
				(symbol :tag "Eval" :value eval)))
			 (list :tag "Name" :value
			       (:name "")
			       (const :format "" :value :name)
			       (string :tag "String" :value ""))
			 (list :tag "Format" :value
			       (:format)
			       (const :format "" :value :format)
			       (function :tag "Function" :value nil))
			 (list :tag "Mode" :value
			       (:mode)
			       (const :format "" :value :mode)
			       (repeat
				(sexp :tag "Sexp" :value nil)))
			 (list :tag "Null Match" :value
			       (:nullmatch)
			       (const :format "" :value :nullmatch)
			       (string :tag "String" :value ""))
			 (list :tag "Language" :value
			       (:language "english")
			       (const :format "" :value :language)
			       (repeat
				(choice
				 ,@(mapcar
				    (lambda (x)
				      (let ((lang (car x)))
					(if lang
					    `(const :tag ,lang
						    :value ,lang)
					  `(const :tag "None"
						  :value nil))))
				    ispell-dictionary-alist)
				 (string :tag "Other"
					 :value ""))))))))
  :group 'wordnet)

(defcustom wordnet-language-vars
  '(ispell-local-dictionary)
  "*List of functions of variables that contain information about the
buffer's language. The return value has to be a string compatible with
`ispell-dictionary-alist'.

If a symbol is bound as variable and as function, the function takes
precedence."
  :type '(repeat (symbol :tag "Symbol" :value nil))
  :group 'wordnet)

(defcustom wordnet-mode-vars
  '(major-mode)
  "*List of functions of variables that contain information about the
buffer's mode. The return value usually is a symbol.

If a symbol is bound as variable and as function, the function takes
precedence."
  :type '(repeat (symbol :tag "Symbol" :value nil))
  :group 'wordnet)

(defcustom wordnet-query-word-flag t
  "*Non-nil means query user before running `wordnet-command-line'."
  :type 'boolean
  :group 'wordnet)

(defcustom wordnet-buffer-name "*WordNet*"
  "*Wordnet's buffer name."
  :type 'string
  :group 'wordnet)

(defcustom wordnet-mode-hooks nil
  "*Hooks to run upon entry into `wordnet-mode' -- these hooks are only
run once when creating the new wordnet buffer."
  :type 'hook
  :group 'wordnet)

(defcustom wordnet-fill-hooks nil
  "*Hooks to run after filling the wordnet buffer."
  :type 'hook
  :group 'wordnet)

(defcustom wordnet-history-length 50
  "*Wordnet history length."
  :type 'integer
  :group 'wordnet)

(defcustom wordnet-process-timeout 10
  "*Seconds to wait for a command being run/evaluated in process mode to
return a result. As a matter of fact, we don't wait for a result but for
a change of state. We assume that a state change means the program has
finished."
  :type 'integer
  :group 'wordnet)

(defcustom wordnet-volatile-lookup-modes
  '(history)
  "*A list of lookup modes that should not be remembered
by setting `wordnet-lookup-mode'."
  :type '(repeat (choice
		  (symbol :tag "Symbol" :value nil)
		  (string :tag "String" :value "")))
  :group 'wordnet)

(defcustom wordnet-bookmarks-regexp
  '("\\(^=== \\(.*\\) ===$\\|^From \\(.+\\) [Dd]ictionary .*:$\\)"
    2 3)
  "*The regexp used for inserting wordnet bookmarks."
  :type '(cons :tag "Bookmark RegExp"
	       (regexp :tag "RegExp" :value "")
	       (repeat (number :tag "Match numbers" :value 0)))
  :group 'wordnet)



(defvar wordnet-history nil
  "WordNet history.")

(defvar wordnet-bookmarks nil
  "WordNet buffer bookmarks.")
(make-variable-buffer-local 'wordnet-bookmarks)

(defvar wordnet-mode-map
    (let ((map (make-sparse-keymap)))
      (define-key map "q" #'wordnet-bury)
      (define-key map "Q" #'wordnet-quit)
      (define-key map "k" #'wordnet-delete-frame)
      (define-key map "h" #'wordnet-history-show)
      (define-key map [return] #'wordnet-run-wn-with-word-at-point-anyway)
      (define-key map [(control button1)] #'wordnet-run-wn-with-word-at-mouse-anyway)
      (define-key map [(button2)] #'wordnet-run-wn-with-word-at-mouse-anyway)
      (define-key map [(button3)] #'wordnet-popmenu-at-mouse)
      (define-key map [(control button3)] #'wordnet-popmenu-at-mouse-volatile)
      map)
  "Keymap for `wordnet-mode'")

(defvar wordnet-lookup-mode nil
  "Remember or force a specific default lookup mode.
Nil means, compile an overview.")
(make-variable-buffer-local 'wordnet-lookup-mode)



(defun wordnet-get-command-line-option (cmd-line-def key &optional default)
  "Get the option's value for KEY in CMD-LINE-DEF."
  (let ((opts (nth 2 cmd-line-def)))
    (if (member key opts)
	t
      (tellib-alist-get opts key default t))))
;;test: (wordnet-get-command-line-option (car (wordnet-get-command-line)) :language)

(defun wordnet-get-command-line-string (cmd-line-def)
  "Retrieve the command-line string from CMD-LINE-DEF."
  (nth 1 cmd-line-def))

(defun wordnet-get-command-line (&optional mode)
  "Lookup the command-line(s) for MODE in `wordnet-command-line'."
  (if mode
      (let ((rv (assoc mode wordnet-command-line)))
	(when rv
	  (list rv)))
    (tellib-mapcart #'(lambda (this)
			(when (wordnet-get-command-line-option this :overview)
			  this))
		    wordnet-command-line)))
;;test: (wordnet-get-command-line)

(defun wordnet-use-this-def-p (definition)
  "Return non-nil if this command-line DEFINITION should be used
for the current buffer."
  (let ((languages (wordnet-get-command-line-option definition :language))
	(modes     (wordnet-get-command-line-option definition :mode)))
    (or (and (not modes) (not languages))
	(tellib-ormap (lambda (x)
			(tellib-ormap (lambda (y)
					(equal x
					       (if (fboundp y)
						   (funcall y)
						 (eval y))))
				      wordnet-language-vars))
		      languages)
	(tellib-ormap (lambda (x)
			(tellib-ormap (lambda (y)
					(equal x
					       (if (fboundp y)
						   (funcall y)
						 (eval y))))
				      wordnet-mode-vars))
		      modes))))

(defun wordnet-run-wn (word &optional dont-ask mode)
  "Get the wordnet overview for WORD."
  (let ((wd (if (or dont-ask
		    (not wordnet-query-word-flag))
		word
	      (read-from-minibuffer "WordNet: " word))))
    (when wd
      (let* ((rplc `(("w" ,wd)
		     ("{Width}" ,(format "%s" (window-width)))
		     ("l" ,ispell-local-dictionary)))
	    (txt
	     (mapconcat
	      (lambda (def)
		(if (wordnet-use-this-def-p def)
		    (let* ((cl  (tellib-replace-args
				 (wordnet-get-command-line-string def)
				 rplc))
			   (sf  (wordnet-get-command-line-option def :stretch))
			   (no  (wordnet-get-command-line-option def :no-output))
			   (nlm (wordnet-get-command-line-option def :nullmatch))
			   (evl (wordnet-get-command-line-option def :eval))
			   (fmt (or (wordnet-get-command-line-option def :format)
				    #'identity))
			   (nm  (or (let ((s (wordnet-get-command-line-option
					      def :name)))
				      (when s
					(tellib-replace-args s rplc)))
				    cl))
			   (hd  (concat "=== " nm " ==="))
			   (lhd (length hd))
			   (ln  (make-string lhd ?\=))
			   (rv  (case evl
				 ((eval)
				  (format "%s" (eval (car (read-from-string cl)))))
				 ((process)
				  (let ((cl (tellib-split-string-by-char cl ?\ )))
				    (with-temp-buffer
				      (if (catch 'exit
					    (set-process-sentinel
					     (apply #'start-process-shell-command
						    "*WordNet-temp*"
						    (current-buffer)
						    (car cl)
						    (cdr cl))
					     (lambda (x y)
					       (throw 'exit t)))
					    (sleep-for wordnet-process-timeout)
					    nil)
					  (buffer-string)
					""))))
				 (t
				  (shell-command-to-string cl)))))
		      (cond
		       (no
			"")
		       ((and rv
			     (not (string= rv ""))
			     (if nlm
				 (not (string-match (tellib-replace-args nlm rplc)
						    rv))
			       t))
			(concat "\n" ln "\n" hd "\n" ln "\n"
				(let ((rv (funcall fmt rv)))
				(if sf
				    (replace-in-string rv
						       "\\([^\n]\\)\n"
						       "\\1\n\n")
				  rv))))
		       (t
			"")))
		  ""))
	      (wordnet-get-command-line mode)
	      "")))
	(wordnet-history-add wd)
	;;(message "DEBUG: %S" txt)
	(if (string-match "[^]" txt)
	    (concat (or mode "Overview") " for \"" wd "\"\n"
		    (replace-in-string txt "+" "\n\n\n" t))
	  "")))))
	;;	(if (string-match "^*$" txt)
	;;	    (progn (tellib-message 1 'wordnet "Not found: %S" word)
	;;		   "")
	;;	  (concat (or mode "Overview") " for \"" wd "\"\n"
	;;		  (replace-in-string txt "+" "\n\n\n" t)))))))
	

(defun wordnet-run-wn-quiet (word)
  "Get the wordnet overview for WORD, but don't query user."
  (wordnet-run-wn word t))

(defun wordnet-thing-to-lookup ()
  "Return the word or selected text we should lookup."
  (if (region-exists-p)
      (buffer-substring (region-beginning) (region-end))
    (thing-at-point 'word)))

;;;###autoload
(defun wordnet-lookup-word (word &optional dont-ask mode volatile)
  "Look up WORD."
  (interactive "sLookup text: ")
  (let ((mode (cond
	       ((string= mode "Overview")
		nil)
	       (mode
		mode)
	       (t
		wordnet-lookup-mode))))
    ;;(message "DEBUG: %s %s" mode word)
    (wordnet-display-result (wordnet-run-wn word dont-ask mode)
			    mode
			    volatile)))

;;;###autoload
(defun wordnet-lookup-selection (&optional dont-ask mode volatile)
  "Look up the WORD.
Could be used as in:
	gnuclient -eval '\(wordnet-lookup-selection t)'
"
  (interactive)
  (let ((word (get-selection)))
    (wordnet-lookup-word word dont-ask mode volatile)))

;;;###autoload
(defun wordnet-lookup (&optional dont-ask mode volatile)
  "Run `wordnet-command-line' with MODE for the word at point."
  (interactive "P")
  (let ((word (wordnet-thing-to-lookup)))
    (when word
      (wordnet-lookup-word word dont-ask mode volatile))))
(defalias 'wordnet-run-wn-with-word-at-point 'wordnet-lookup)

(defun wordnet-lookup-volatile (&optional dont-ask mode)
  "Perform a volatile lookup."
  (interactive "P")
  (wordnet-lookup dont-ask mode t))

(defun wordnet-run-wn-with-word-at-point-anyway ()
  "Run `wordnet-lookup' regardless of `wordnet-query-word-flag'."
  (interactive)
  (wordnet-run-wn-with-word-at-point t))

(defun wordnet-run-wn-with-word-at-pos (pos &optional dont-ask)
  "Run `wordnet-lookup' regardless of `wordnet-query-word-flag'."
  (save-excursion
    (goto-char pos)
    (wordnet-run-wn-with-word-at-point dont-ask)))

(defun wordnet-lookup-specific (&optional dont-ask)
  "Perform a specific lookup the word at point."
  (interactive "P")
  (let ((mode (completing-read "Mode: " wordnet-command-line nil t
			       (caar wordnet-command-line))))
    (when mode
      (wordnet-lookup dont-ask mode))))

(defun wordnet-run-wn-with-word-at-mouse (event &optional dont-ask)
  "Run `wordnet-command-line' with the word at mouse."
  (interactive "e")
  (let ((wordnet-query-word-flag (not dont-ask)))
    (tellib-call-with-event-pos #'wordnet-run-wn-with-word-at-pos event)))

(defun wordnet-run-wn-with-word-at-mouse-anyway (e)
  "Run `wordnet-lookup' regardless of `wordnet-query-word-flag'."
  (interactive "e")
  (wordnet-run-wn-with-word-at-mouse e t))

(defun wordnet-display-result (string &optional mode volatile)
  "Display wordnet's result STRING in a buffer."
  (if (string= string "")
      (message "wordnet: Null string result")
    (pop-to-buffer (get-buffer-create wordnet-buffer-name))
    (let ((buffer-read-only nil))
      (delete-region (point-min) (point-max))
      (insert string)
      (goto-char 0))
    (wordnet-mode)
    (save-excursion
      (setq wordnet-bookmarks nil)
      (let ((rx (car wordnet-bookmarks-regexp))
	    (mn (cdr wordnet-bookmarks-regexp)))
	(while (tellib-re-search rx t)
	  (add-to-list 'wordnet-bookmarks
		       (list (match-string (car (tellib-ormap #'match-string mn)))
			     (match-beginning 0))
		       t))))
    (let ((buffer-read-only nil))
      (run-hooks 'wordnet-fill-hooks)
      (unless (or volatile
		  (member mode wordnet-volatile-lookup-modes))
	(setq wordnet-lookup-mode mode)))))

(defun wordnet-history-shorten ()
  "Shorten `wordnet-history'."
  (when (> (length wordnet-history) wordnet-history-length)
    (setq wordnet-history (subseq wordnet-history 0 wordnet-history-length))))
  
(defun wordnet-history-add (word)
  "Add word to `wordnet-history'."
  (let ((hist (if (member word wordnet-history)
		  (delete word wordnet-history)
		wordnet-history)))
    (setq wordnet-history
	  (if (equal (car hist) word)
	      hist
	    (cons word hist))))
  (wordnet-history-shorten))

(defun wordnet-history-show ()
  "Show `wordnet-mode' history."
  (interactive)
  (wordnet-display-result
   (concat "WordNet History:\n\n"
	   (let ((count 0))
	     (mapconcat (lambda (x)
			  (setq count (+ count 1))
			  (format "%3d. %s" count x))
			wordnet-history "\n")))
   'history))

(defun wordnet-bury ()
  "Bury WordNet buffer."
  (interactive)
  (when (eq major-mode 'wordnet-mode)
    ;;(delete-window)
    (bury-buffer)
    (if (> (count-windows) 1)
	(delete-window))))

(defun wordnet-quit ()
  "Kill WordNet buffer."
  (interactive)
  (when (eq major-mode 'wordnet-mode)
    (kill-buffer (current-buffer))
    (if (> (count-windows) 1)
	(delete-window))))

(defun wordnet-delete-frame ()
  "Kill the frame."
  (interactive)
  (if (= (length (frame-list)) 1)
      (suspend-or-iconify-emacs)
    (delete-frame)))

(defun wordnet-get-menu (&optional volatile prefix)
  "Return a menu definition of lookup modes (for `add-submenu' or `popup-menu')."
  (let ((prefix (or prefix "")))
    (mapcar (lambda (this)
	      (let ((mode (car this)))
		`[,(concat prefix mode) (wordnet-lookup t ,mode ,volatile)]))
	    wordnet-command-line)))

;;;###autoload
(defun wordnet-popmenu-at-mouse (event &optional volatile)
  "Wordnet pop-up menu."
  (interactive "e")
  (tellib-call-with-event-pos
   (lambda (pos)
     (when pos
       (goto-char pos))
     (popup-menu
      `(,(format "WordNet \"%s\"%s"
		 (wordnet-thing-to-lookup)
		 (if volatile " (volatile)" ""))
	("Bookmarks"
	 ,@(if wordnet-bookmarks
	       (mapcar (lambda (this)
			 `[,(nth 0 this) (goto-char ,(nth 1 this))])
		       wordnet-bookmarks)
	     '(["No Bookmarks" nil]))
	 )
	["New Overview" (wordnet-lookup t "Overview" ,volatile)]
	["History"  (wordnet-history-show)]
	"---"
	,@(wordnet-get-menu volatile))))
   event))

(defun wordnet-popmenu-at-mouse-volatile (event)
  "Wordnet pop-up menu for volatile lookups."
  (interactive "e")
  (wordnet-popmenu-at-mouse event t))

(defun wordnet-mode ()
  "Turn on wordnet-mode.

Keymap:
\\{wordnet-mode-map}"
  (let ((buffer-read-only nil))
    (unless (eq major-mode 'wordnet-mode)
      (kill-all-local-variables)
      ;;(text-mode)
      (use-local-map wordnet-mode-map)
      (setq major-mode 'wordnet-mode)
      (setq mode-name "WordNet")
      (run-hooks 'wordnet-mode-hooks)
      (buffer-disable-undo)))
  (setq buffer-read-only t))

(defun wordnet-install (&optional top-install-flag)
  "Install wordnet hooks."
  (tellib-installer 'tellib 'wordnet top-install-flag))

(defun wordnet-uninstall (&optional top-install-flag)
  "Deinstall wordnet hooks."
  (tellib-uninstaller 'tellib 'wordnet top-install-flag))


(provide 'wordnet)


;;; wordnet.el ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
