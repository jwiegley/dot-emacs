;;; xff.el --- extended find-file

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-03-16>
;; Keywords: files find-file

(defconst xff-version "1.2")
(defconst xff-homepage
  "http://members.a1.net/t.link/CompEmacsXff.html")


;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

;;; Commentary:

;; ;---(:excerpt-beg xff :name desc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsXff")---
;; 
;; This package extends `find-file' with some special syntax of the form:
;; 
;; <example>
;; 	file*keyword1=arg1*keyword2=arg2
;; 	file*keyword1=arg1*keyword2:rest
;; </example>
;; 
;; A split char in the file name has to be escaped with a backslash.
;; 
;; At the moment the following keywords are defined (see `xff-commands'):
;; 
;; line=LINE :: goto line
;; 
;; char=CHAR :: goto char
;; 
;; find=TEXT or rather find:SOME TEXT :: find text
;; 
;; select=BEG-END :: select/mark the region from BEG to END
;; 
;; Installation: Put (require 'xff) (xff-install) into your init file
;; (~/.xemacs/init.el or ~/.emacs.el).
;; 
;; ;---(:excerpt-end xff :name desc)---


;;; Change log:

;; ;---(:excerpt-beg xff :name hist)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsXff")---
;; 
;; =1.2= :: Revised syntax (following a proposal by D. Goel aka deego AT
;; glue umd edu); check if we are dealing with a xff argument first;
;; simplified original syntax (new default mode); works with gnuserv.
;; 
;; =1.1= :: Initial release (tested with XEmacs 21.4.8)
;; 
;; ;---(:excerpt-end xff :name hist)---


;;; Problems:

;; ;---(:excerpt-beg xff :name problems)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsXff")---
;; 
;; - (find-file-noselect "~/.bashrc?select=20-30") selects text in the
;; wrong buffer.
;; 
;; ;---(:excerpt-end xff :name problems)---


;;; To Do:


;;; Code:

(require 'tellib)


;; Customizations

(defgroup xff nil
  "Extended find file syntax."
  :prefix "xff-"
  :group 'find-file)

(defcustom xff-commands
  '(("line" (lambda (string)
	      ;;(raise-frame)
	      (goto-line (string-to-int string))))
    ("char" (lambda (string)
	      ;;(raise-frame)
	      (goto-char (string-to-int string))))
    ("find" (lambda (string)
	      ;;(raise-frame)
	      (goto-char (point-min))
	      (search-forward string)))
    ("select" (lambda (string)
		(let* ((args (mapcar #'string-to-int
				     (tellib-split-string-by-char string ?\-)))
		       (beg  (nth 0 args))
		       (end  (nth 1 args)))
		  ;;(raise-frame)
		  (goto-char end (current-buffer))
		  (push-mark beg nil t (current-buffer)))))
    )
  "*Lists of keywords and a function.
The function takes one string argument. If the function returns nil, the
further evaluation of keywords will be aborted."
  :type
  '(repeat :tag "Definition"
	   (list :tag "List"
		 :value ("" nil)
		 (string :tag "Keyword" :value "")
		 (function :tag "Function" :value nil)
		 (repeat :tag "Flags"
			 (list :tag "Script?" :value (:script nil)
			       (const :format "" :value :script)
			       (boolean :value nil))
			 (list :tag "Save if modified?" :value (:save nil)
			       (const :format "" :value :save)
			       (boolean :value nil))
			 )))
  :group 'xff)
(put 'xff-commands 'risky-local-variable t)

(defcustom xff-handled-functions-list
  nil
  "*IO-Primitives handled by xff -- usually none.
The file name will always be translated."
  :type '(repeat :tag "List"
		 (function :tag "Function"))
  :group 'xff)

(defcustom xff-allow-function-calls-flag nil
  "*Non-nil means, allow the user to call functions via xff."
  :type 'boolean
  :group 'xff)
(put 'xff-allow-function-calls-flag 'risky-local-variable t)

(defcustom xff-allow-set-variables-flag nil
  "*Non-nil means, allow the user to set variables via xff."
  :type 'boolean
  :group 'xff)
(put 'xff-allow-set-variables-flag 'risky-local-variable t)

(defcustom xff-verbosity 1
  "*Verbosity of messages."
  :type 'integer
  :group 'xff)


;(defvar xff-mode 'revised-1
(defvar xff-mode 'simplified
  "Defines the xff syntax to use. A symbol out of: original, revised-1.

Caution: You have to recompile to xff.el for changes to this variable
being effective.

original (see `xff-parse-args-original'):
filename?command1=arg1&command2=arg2&...&commandN:REST

simplified (default mode!; see `xff-parse-args-original'):
filename*command1=arg1*command2=arg2*...*commandN:REST

revised-1 (this doesn't work properly; see `xff-parse-args-revised-1'):
command1=arg1&command2=arg2&...&commandN=argN?filename

arguments: A \"&\" or \"?\" have to be escaped with \"\\\". Thus, an
argument like \"bla&bla?\" would have to be written as \"bla\\&bla\\?\".

A \"\\\" returns always the following character. Consequently, \"\\\\\"
yields \"\\\".")

(defvar xff-original-escaped-filenames-flag t
  "Non-nil means, that \\ is used for escaping special characters in file names.
As in: file\\?name?cmd=arg.")

(defvar xff-file-name-handler-def nil "The xff file name handler definition.")

(defvar xff-strings-split nil "xff original syntax: split string.")
(defvar xff-strings-and   nil "xff original syntax: and string")
(defvar xff-strings-arg   nil "xff original syntax: command-argument separator")
(defvar xff-strings-rest  nil "xff original syntax: rest string")
(defvar xff-strings-esc   nil "xff original syntax: escape string")

(defvar xff-do-nothing nil
  "If non-nil, the argument string won't be parsed or modified.")


;;;original
;;test (string-match (car xff-file-name-handler-def) "test")
;;test (string-match (car xff-file-name-handler-def) "test?x=1")
;;test (string-match (car xff-file-name-handler-def) "test?x:1")

;;;revised-1
;;test (string-match (car xff-file-name-handler-def) "test")
;;test (string-match (car xff-file-name-handler-def) "?test")
;;test (string-match (car xff-file-name-handler-def) "=test")
;;test (string-match (car xff-file-name-handler-def) "&test")
;;test (string-match (car xff-file-name-handler-def) "=&test")
;;test (string-match (car xff-file-name-handler-def) "a=?test")
;;test (string-match (car xff-file-name-handler-def) "a=1?test")
;;test (string-match (car xff-file-name-handler-def) "a=&b=?test")
;;test (string-match (car xff-file-name-handler-def) "a=1&b=1?test")


(defun xff-parse-args-original (string)
  "Parse an extended find-file string in original mode (see `xff-mode').
Original mode syntax: file?keyword=arg&... or file?keyword:rest

In simplified mode, this will become:
	file*keyword=arg*... or file*keyword:rest

Special characters in the filename have to be escaped with \"\\\" -- as
in \"file\\*name*this\\*command=Huh\\*Hah\".

The rest argument may contain any characters.
"
;  (let ((argstring (tellib-split-string-by-char string ?\?)))
;    (if (> (length argstring) 2)
;	(tellib-error 'error "xff: Malformed argument string" string)
  (let* ((argstring (let ((split-pos (string-match
				      (if xff-original-escaped-filenames-flag
					  (format "[^%s]\\(\\%s\\)"
						  xff-strings-esc
						  xff-strings-split)
					(format "\\(\\%s\\)" xff-strings-split))
				      string)))
		      (if split-pos
			  (list (substring string 0 (match-beginning 1))
				(substring string (match-end 1)))
			(list string))))
	 (file  (if xff-original-escaped-filenames-flag
		    (replace-in-string (car argstring)
				       (regexp-quote (concat xff-strings-esc
							     xff-strings-split))
				       xff-strings-split
				       t)
		  (car argstring)))
	 (xargs (cadr argstring))
	 (lxa   (length xargs))
	 (args
	  (when xargs
	    (let ((sstr    (concat "["
				   xff-strings-and
				   xff-strings-arg
				   xff-strings-rest
				   xff-strings-esc
				   "]"))
		  (keyword nil)
		  (arg     nil)
		  (tmp     "")
		  (pos     0)
		  rv)
	      (while (string-match sstr xargs pos)
		(let ((beg  (match-beginning 0))
		      (next (match-end 0))
		      (txt  (match-string 0 xargs)))
		      ;;;(message "%s %s %s %s %s %s %s" pos lxa txt beg next keyword arg)
		  (cond
		   ((string= txt xff-strings-esc)
		    (if (>= next lxa)
			(tellib-error 'error "xff: Bad use of escape character"
				      xargs next)
		      (setq tmp (concat tmp
					(substring xargs pos  beg)
					(substring xargs next (+ next 1)))
			    pos (+ next 1))))
		   ((string= txt xff-strings-rest)
		    (if keyword
			(setq arg (concat tmp arg txt)
			      tmp ""
			      pos next)
		      (setq rv (append rv `((,(concat tmp
						      (substring xargs pos beg))
					     ,(substring xargs next))))
			    tmp ""
			    pos lxa)))
		   ((string= txt xff-strings-arg)
		    (if keyword
			(setq arg (concat tmp arg txt))
		      (setq keyword (concat tmp (substring xargs pos beg))))
		    (setq pos next
			  tmp ""))
		   ((string= txt xff-strings-and)
		    (if keyword
			(setq rv (append rv `((,keyword
					       ,(concat tmp
							arg
							(substring xargs
								   pos beg)))))
			      keyword nil
			      arg     nil
			      tmp     ""
			      pos     next)
		      (tellib-error 'error "xff: Syntax error"))))))
	      (cond
	       (keyword
		(setq rv (append rv `((,keyword
				       ,(concat tmp 
						arg
						(substring xargs pos lxa)))))))
	       ((not (= pos lxa))
		(tellib-error 'error "xff: Missing last argument" xargs pos lxa)))
	      rv))))
    (cons file args)))
;;;original
;;test: (xff-parse-args-original "file")
;;test: (xff-parse-args-original "file?bla=1&blo=2")
;;test: (xff-parse-args-original "file?bla=&blo=")
;;test: (xff-parse-args-original "file?bla:1&1&blo=2")
;;test: (xff-parse-args-original "file?bla=\"1&blo=2")
;;test: (xff-parse-args-original "file?bla=\\&1&blo=2")
;;test: (xff-parse-args-original "file\\?name?bla=\\&1&blo=2")
;;test: (xff-parse-args-original "file\\?name?which-command?=Huh?")
;;test: (xff-parse-args-original "file\\?name?command\\=this\\?=Huh\\&Hah")
;;test: (xff-parse-args-original "file?bla=1&1&blo=2") --> error, ok
;;test: (xff-parse-args-original "file?bla") --> error, ok
;;test: (xff-parse-args-original "file?bla=&blo") --> error, ok
;;test: (xff-parse-args-original "file?bla=1?blo=2") --> error, ok

;;;simplified
;;test: (xff-parse-args-original "file*bla=1*blo=2")
;;test: (xff-parse-args-original "file*bla=*blo=")
;;test: (xff-parse-args-original "file*bla:1*1*blo=2")
;;test: (xff-parse-args-original "file*bla=\"1*blo=2")
;;test: (xff-parse-args-original "file*bla=\\*1*blo=2")
;;test: (xff-parse-args-original "file\\*name*bla=\\*1*blo=2")
;;test: (xff-parse-args-original "file\\*name*which-command\\*=Huh\\*")
;;test: (xff-parse-args-original "file\\*name*command\\=this\\*=Huh\\*Hah")
;;test: (xff-parse-args-original "file*bla=1*1*blo=2") --> error, ok
;;test: (xff-parse-args-original "file*bla") --> error, ok
;;test: (xff-parse-args-original "file*bla=*blo") --> error, ok
;;test: (xff-parse-args-original "file*bla=1\\") --> error, ok

(defun xff-parse-args-revised-1 (argstring)
  "Parse an extended find-file string in original mode (see `xff-mode').

Caution: revised-1 mode has problems when being called via gnuclient
from bash, because the file name is prepended with the current
directory. Thus, \"gnuclient line=10?~/file\" would become \"gnuclient
/home/user/line=10?~/file\", which is almost impossible to parse.

Syntax:
command1=arg1&command2=arg2&...&commandN=argN?filename
?filename-including-a-question-mark?

Arguments: A \"&\" or \"?\" have to be escaped with \"\\\". Thus, an
argument like \"bla&bla?\" would have to be written as \"bla\\&bla\\?\".

A \"\\\" returns always the following character. Consequently, \"\\\\\"
yields \"\\\".
"
  (message argstring)
  (if (string-match "\\?" argstring)
      (let* ((lxa     (length argstring))
	     (keyword nil)
	     (arg     nil)
	     (pos     0)
	     (tmp     "")
	     args
	     (file
	      (catch 'exit
		(while (string-match "[\\=&?]" argstring pos)
		  (let ((beg  (match-beginning 0))
			(next (match-end 0))
			(txt  (match-string 0 argstring)))
		    ;;(message "%s %s %s %s %s %s %s" pos lxa txt beg next keyword arg)
		    (cond
		     ((string= txt "\\")
		      (if (>= next lxa)
			  (tellib-error 'error "xff: Bad use of '\\'"
					argstring next)
			(setq tmp (concat tmp (substring argstring next (+ next 1)))
			      pos (+ next 1))))
		     ((string= txt "=")
		      (if keyword
			  (setq arg (concat tmp arg txt)
				tmp "")
			(setq keyword (concat tmp (substring argstring pos beg))
			      tmp     ""))
		      (setq pos next))
		     (t                 ;;(or (string= txt "&") (string= txt "?"))
		      (let ((last-flag (string= txt "?")))
			(cond
			 (keyword
			  (setq args (append args
					     `((,keyword
						,(concat tmp
							 arg
							 (substring argstring
								    pos beg)))))
				tmp     ""
				keyword nil
				arg     nil
				pos     next))
			 ((or (not last-flag)
			      (not (= beg 0))
			      args keyword arg)
			  (tellib-error 'error "xff: Malformed argument:"
					argstring next keyword args)))
			(when last-flag
			  (throw 'exit (substring argstring next))))))))
		(tellib-error 'error "xff: No file name"))))
	(cons file args))
    (list argstring)))
;;test: (xff-parse-args-revised-1 "file")
;;test: (xff-parse-args-revised-1 "bla=1&blo=2?file")
;;test: (xff-parse-args-revised-1 "bla=&blo=?file")
;;test: (xff-parse-args-revised-1 "bla=\"1&blo=2?file")
;;test: (xff-parse-args-revised-1 "bla=\\&1&blo=2?file")
;;test: (xff-parse-args-revised-1 "?file?")
;;test: (xff-parse-args-revised-1 "file?") --> error, ok
;;test: (xff-parse-args-revised-1 "bla=1&1&blo=2?file") --> error, ok
;;test: (xff-parse-args-revised-1 "bla?file") --> error, ok
;;test: (xff-parse-args-revised-1 "bla=&blo?file") --> error, ok

(defun xff-parse-args (&rest args)
  "Not yet installed."
  (tellib-error 'error "xff: Call `xff-install' first."))

(defun xff-handle-extended-args (arglist)
  "Handle the argument list returned by `xff-parse-args'
according to `xff-commands'."
  (let (rv)
    (mapc #'(lambda (this)
	      (tellib-message 2 'xff "xff handle arg %s" this)
	      (let* ((cmd     (car this))
		     (arg     (cadr this))
		     (sym     (intern-soft cmd))
		     (def     (assoc cmd xff-commands))
		     (flags   (nth 2 def))
		     (save?   (let ((flag (assoc :save flags)))
				(nth 1 flag)))
		     (script? (let ((flag (assoc :script flags)))
				(nth 1 flag))))
		(when script?
		  (add-to-list 'rv :script))
		(when save?
		  (add-to-list 'rv :save))
		(cond
		 ((and def cmd arg)
		  (let* ((fn          (nth 1 def)))
		    ;;(message "DEBUG: %S %S" cmd arg) (sleep-for 3)
		    (funcall fn arg)))
		 ((and sym
		       (fboundp sym)
		       xff-allow-function-calls-flag)
		  (funcall sym arg))
		 ((and sym
		       (boundp sym)
		       xff-allow-set-variables-flag)
		  (set sym arg))
		 ((and cmd arg)
		  (tellib-error 'error "xff: Invalid keyword"
				cmd arg arglist)))
		))
	  arglist)
    rv))
;;test: (xff-handle-extended-args nil)
;;test: (xff-handle-extended-args '(("line" "3")))
;;test: (xff-handle-extended-args '(("unknown" "3")))

;;(defadvice gnuserv-edit-files (around xff-gnuserv-edit-files first activate)
(defadvice gnuserv-edit-files (around xff-gnuserv-edit-files first)
  "Wrap around for dealing with `xff-commands'."
  ;;(gnuserv-edit-files TYPE LIST &rest FLAGS)
  ;;For each (line-number . file) pair in LIST, edit the file at line-number.
  ;;The visited buffers are memorized, so that when C-x # is invoked
  ;;in such a buffer, or when it is killed, or the client's device deleted, the
  ;;client will be invoked that the edit is finished.
  
  ;;TYPE should either be a (tty TTY TERM PID) list, or (x DISPLAY) list.
  ;;If a flag is `quick', just edit the files in Emacs.
  ;;If a flag is `view', view the files read-only.
  (if xff-do-nothing
      ad-do-it
    (let ((list  (ad-get-arg 1))
	  (ms    (car xff-file-name-handler-def)))
      (if list
	  (progn
	    (mapc
	     #'(lambda (this)
		 (let ((line (car this))
		       (file (cdr this)))
		   (if (string-match ms file)
		       (let* ((arglist (xff-parse-args file))
			      (file    (car arglist))
			      (buf     (find-buffer-visiting file))
			      (dirty   (when buf
					 (buffer-modified-p buf)))
			      (xargs   (cdr arglist)))
			 (tellib-message 1 'xff "xff: file=%s xargs=%s"
					 file xargs)
			 (ad-set-arg 1 `((,line . ,file)))
			 ad-do-it
			 (let ((rv     (xff-handle-extended-args xargs))
			       (save?  nil)
			       (close? nil))
			   (mapc
			    #'(lambda (elt)
				(cond
				 ((equal elt :script)
				  (tellib-message 1 'xff
						  "xff: close buffer for %s"
						  file)
				  (setq cbf t))))
			    rv)
			   (when (and save? (not dirty))
			     (save-buffer))
			   (when (and close? (not buf))
			     (kill-buffer (current-buf)))))
		     ad-do-it)))
	     list)
	    nil)
	ad-do-it))))
;;(ad-recover-normality)

;;(defadvice find-file-noselect (around xff-find-file-noselect first activate)
(defadvice find-file-noselect (around xff-find-file-noselect first)
  "Provide an extended syntax for find file. See `xff-parse-args' and 
`xff-commands' for an explanation."
  (if xff-do-nothing
      ad-do-it
    (let ((arg0 (ad-get-arg 0)))
      (if (string-match (car xff-file-name-handler-def) arg0)
	  (let* ((arglist (xff-parse-args arg0))
		 (file    (car arglist))
		 (xargs   (cdr arglist)))
	    (tellib-message 1 'xff "xff: %s file=%s xargs=%s" arg0 file xargs)
	    (ad-set-args 0 (cons file (ad-get-args 1)))
	    (let ((rv ad-do-it))
	      (when rv
		(with-current-buffer rv
		  (xff-handle-extended-args xargs)))
	      rv))
	ad-do-it))))

;;;original
;;test: (find-file-noselect "~/.bashrc?line=10")
;;test: (find-file-noselect "~/.bashrc?line=20")
;;test: (find-file-noselect "~/.bashrc?select=20-30")
;;test: (find-file "~/.bashrc")
;;test: (find-file "~/.bashrc?line=10")
;;test: (find-file "~/.bashrc?char=10")
;;test: (find-file "~/.bashrc?select=10-20")
;;test: (find-file "~/.bashrc?find=TEX")
;;test: (let ((xff-allow-function-calls-flag t))
;;	(find-file "~/.bashrc?search-forward=tex"))
;;(ad-recover-normality)

;;;simplified
;;test: (find-file-noselect "~/.bashrc*line=10")
;;test: (find-file-noselect "~/.bashrc*line=20")
;;test: (find-file-noselect "~/.bashrc*select=20-30")
;;test: (find-file "~/.bashrc")
;;test: (find-file "~/.bashrc*line=10")
;;test: (find-file "~/.bashrc*char=10")
;;test: (find-file "~/.bashrc*select=10-20")
;;test: (find-file "~/.bashrc*find=TEX")
;;test: (let ((xff-allow-function-calls-flag t))
;;	(find-file "~/.bashrc*search-forward=tex"))
;;(ad-recover-normality)

;;;revised-1
;;test: (find-file "~/.bashrc")
;;test: (find-file "line=10?~/.bashrc")
;;test: (find-file "char=10?~/.bashrc")
;;test: (find-file "select=10-20?~/.bashrc")
;;test: (find-file "find=TEX?~/.bashrc")
;;test: (let ((xff-allow-function-calls-flag t))
;;	(find-file "search-forward=tex?~/.bashrc"))


(defun xff-file-name-handler (io-primitive &rest args)
  "Handle extended file names."
  (if xff-do-nothing
      (apply io-primitive args)
    (let* ((arglist (xff-parse-args (nth 0 args)))
	   (file    (car arglist))
	   (xargs   (cdr arglist))
	   (rv      (apply io-primitive (cons file (cdr args)))))
      (message "xff: %S %S %S" io-primitive (cons file (cdr args)) args)
      (when (member io-primitive xff-handled-functions-list)
	(xff-handle-extended-args xargs))
      rv)))


;;;###autoload
(defun xff-install (&optional top-install-flag)
  "Install the xff file name handler."
  (case xff-mode
    ((original)
     (setq xff-file-name-handler-def (cons "\\?.*[:=].*" #'xff-file-name-handler)
	   xff-strings-split "?"
	   xff-strings-and   "&"
	   xff-strings-arg   "="
	   xff-strings-rest  ":"
	   xff-strings-esc   "\\")
     (fset 'xff-parse-args 'xff-parse-args-original))
    ((simplified)
     (setq xff-file-name-handler-def (cons "[^\\]\\*\\(.+[:=].*\\)*$"
					   #'xff-file-name-handler)
	   xff-strings-split "*"
	   xff-strings-and   "*"
	   xff-strings-arg   "="
	   xff-strings-rest  ":"
	   xff-strings-esc   "\\")
     (fset 'xff-parse-args 'xff-parse-args-original))
    ((revised-1)
     (setq xff-file-name-handler-def
	   (cons "^\\(.+?[=].*?&?\\)*\\?" #'xff-file-name-handler))
     (fset 'xff-parse-args 'xff-parse-args-revised-1))
    (t
     (tellib-error 'error "xff: Unknown mode" xff-mode)))
  (tellib-installer 'tellib 'xff top-install-flag)
  (ad-activate-regexp "^xff-")
  (add-to-list 'file-name-handler-alist xff-file-name-handler-def))

(defun xff-uninstall (&optional top-install-flag)
  "Install the xff file name handler."
  ;;(ad-recover-normality)
  (tellib-uninstaller 'tellib 'xff top-install-flag)
  (ad-disable-regexp "^xff-")
  (setq file-name-handler-alist 
	(delete xff-file-name-handler-def file-name-handler-alist)))

;(xff-install)
;(xff-uninstall)

;(setq file-name-handler-alist
;      '(("\\`/\\[.*\\]" . tramp-file-name-handler)
;	("^/[^/:]+:" . remote-path-file-handler-function)))
;;test: (expand-file-name "~/.bashrc?line=10")


(provide 'xff)

;;; xff.el ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
