;;; texi2latex.el --- convert a texi file into a LaTeX file.
;; Copyright (C) 1996, 2004, 2008 Lars Magne Ingebrigtsen

(require 'cl)

(defun latexi-discard-until (string)
  (let ((beg (match-beginning 0)))
    (unless (re-search-forward (concat "^@end +" string "[ \t]*\n") nil t)
      (error "No end: %s" string))
    (delete-region beg (match-end 0))))

(defun latexi-strip-line ()
  (delete-region (progn (beginning-of-line) (point))
		 (progn (forward-line 1) (point))))

(defun latexi-switch-line (command arg)
  (latexi-strip-line)
  (insert (format "\\%s{%s}\n" command arg)))

(defun latexi-index-command (command arg)
  (latexi-strip-line)
  (insert (format "\\gnus%sindex{%s}\n" 
		  (if (equal command "kindex") "k" "")
		  arg)))

(defun latexi-begin-command (command)
  (latexi-strip-line)
  (insert (format "\\begin{%s}\n" command)))

(defun latexi-exchange-command (command arg)
  (delete-region (match-beginning 0) (match-end 0))
  (insert (format "\\%s{%s}" command arg)))

(defun latexi-translate ()
  "Translate."
  (interactive)
  (latexi-translate-file "gnus")
  (latexi-translate-file "gnus-faq")
  (latexi-translate-file "message" t)
  (latexi-translate-file "emacs-mime" t)
  (latexi-translate-file "sieve" t)
  (latexi-translate-file "pgg" t)
  (latexi-translate-file "sasl" t)
  (latexi-translate-file "gnus-news" t))

(defun latexi-translate-file (file &optional as-a-chapter)
  "Translate file a LaTeX file."
  (let ((item-string "")
	(item-stack nil)
	(list-stack nil)
	(latexi-buffer (get-buffer-create "*LaTeXi*"))
	verbatim
	(regexp 
	 (concat 
	    "@\\([^{} \t\n]+\\)"
	    "\\(\\( +\\(.*$\\)\\|[ \t]*$\\)\\|{\\([^}]*\\)}\\)"))
	(cur (find-file-noselect (concat (or (getenv "srcdir") ".") 
					 "/" file ".texi")))
	(times 3)
	(chapter 0)
	command arg)
    (pop-to-buffer latexi-buffer)
    (buffer-disable-undo)
    (erase-buffer)
    (insert-buffer-substring cur)
    (goto-char (point-min))
    (when (search-forward "@copying" nil t)
      (latexi-copying))
    (while (search-forward "@insertcopying" nil t)
      (delete-region (match-beginning 0) (match-end 0))
      (latexi-insertcopying))
    (goto-char (point-min))
    (latexi-strip-line)
    (latexi-translate-string "@'e" "\\'{e}")
    (latexi-translate-string "@`a" "\\`{a}")
    (latexi-translate-string "@,{c}" "\\c{c}")
    (latexi-translate-string "@aa{}" "{\\aa}")
    (latexi-translate-string "@\"{@dotless{i}}" "ï")
    (latexi-translate-string "%@{" "\\gnuspercent{}\\gnusbraceleft{}")
    (latexi-translate-string "%@}" "\\gnuspercent{}\\gnusbraceright{}")
    (latexi-translate-string "%1@{" "\\gnuspercent{}1\\gnusbraceright{}")
    (latexi-translate-string "@*" "\\newline{}")
    (latexi-translate-string "S@{" "S\\gnusbraceleft{}")
    (latexi-translate-string "@code{\\222}" "@code{\\gnusbackslash{}222}")
    (latexi-translate-string "@code{\\264}" "@code{\\gnusbackslash{}264}")
    (latexi-translate-string "@samp{\\Deleted}" "@samp{\\gnusbackslash{}Deleted}")
    (latexi-translate-string "@samp{\\Seen}" "@samp{\\gnusbackslash{}Seen}")
    (latexi-translate-string "@file{c:\\myhome}" "@file{c:\\gnusbackslash{}myhome}")
;    (while (re-search-forward "{\"[^\"]*\\(\\\\\\)[^\"]*\"}\\\\" nil t)
;      (replace-match "\\verb+\\\\+ " t t))
    (while (not (zerop (decf times)))
      (goto-char (point-min))
      (while (re-search-forward regexp nil t)
	(setq command (match-string 1))
	(if (match-beginning 3)
	    (progn
	      (setq arg (or (match-string 4) ""))
	      (save-match-data
		(when (string-match "[ \t]+$" arg)
		  (setq arg (substring arg 0 (match-beginning 0)))))
	      (cond 
	       ((member command '("c" "comment"))
		(if (string-match "@icon" (or arg ""))
		    (progn
		      (beginning-of-line)
		      (delete-region (point) (+ (point) 4))
		      (insert "\\gnus"))
		  (delete-region (match-beginning 0) 
				 (progn (end-of-line) (point))))
		(if (equal arg "@head")
		    (insert "\\gnusinteresting")))
	       ((member command '("setfilename" "set"
				  "synindex" "setchapternewpage"
				  "summarycontents" "bye"
				  "top" "iftex" "cartouche" 
				  "iflatex" "finalout" "vskip"
				  "dircategory" "group" "syncodeindex"
				  "documentencoding"))
		(latexi-strip-line))
	       ((member command '("menu" "tex" "ifinfo" "ignore" 
				  "ifnottex" "direntry"))
		(latexi-discard-until command))
	       ((member command '("subsection" "subsubsection"))
		(if as-a-chapter
		    (latexi-switch-line (format "sub%s" command) arg)
		  (latexi-switch-line command arg)))
	       ((member command '("heading"))
		(if as-a-chapter
		    (latexi-switch-line "subsection*" arg)
		  (latexi-switch-line "section*" arg)))
	       ((member command '("subheading"))
		(if as-a-chapter
		    (latexi-switch-line "subsubsection*" arg)
		  (latexi-switch-line "subsection*" arg)))
	       ((member command '("subsubheading"))
		(if as-a-chapter
		    (latexi-switch-line "subsubsubsection*" arg)
		  (latexi-switch-line "subsubsection*" arg)))
	       ((member command '("chapter"))
		(if (string-match "Index" arg)
		    (latexi-strip-line)
		  (if as-a-chapter
		      (latexi-switch-line "gnussection" arg)
		    (latexi-switch-line 
		     (format 
		      "gnus%s{%s}" command
		      (format "\\epsfig{figure=ps/new-herd-%d,scale=.5}"
			      (if (> (incf chapter) 9) 9 chapter)))
		     arg))))
	       ((member command '("section"))
		(if as-a-chapter
		    (latexi-switch-line "subsection" arg)
		  (latexi-switch-line (format "gnus%s" command) arg)))
	       ((member command '("cindex" "findex" "kindex" "vindex"))
		(latexi-index-command command arg))
	       ((member command '("*"))
		(delete-char -2)
		(insert "\\\\"))
	       ((equal command "sp")
		(replace-match "" t t))
	       ((equal command ":")
		(replace-match "" t t))
	       ((member command '("deffn" "defvar" "defun"))
		(replace-match "" t t))
	       ((equal command "node")
		(latexi-strip-line)
		(unless (string-match "Index" arg)
		  (insert (format "\\label{%s}\n" arg))))
	       ((equal command "contents")
		(latexi-strip-line)
		;;(insert (format "\\tableofcontents\n" arg))
		)
	       ((member command '("titlepage"))
		(latexi-begin-command command))
	       ((member command '("lisp" "example" "smallexample" "display"))
		(latexi-strip-line)
		(insert (format "\\begin{verbatim}\n"))
		(setq verbatim (point)))
	       ((member command '("center"))
		(latexi-strip-line)
		(insert (format "\\begin{%s}%s\\end{%s}\n"
				command arg command)))
	       ((member command '("end"))
		(cond
		 ((member arg '("titlepage"))
		  (latexi-strip-line)
		  (insert (format "\\end{%s}\n" arg)))
		 ((equal arg "quotation")
		  (latexi-strip-line)
		  (insert (format "\\end{verse}\n")))
		 ((member arg '("lisp" "example" "smallexample" "display"))
		  (latexi-strip-line)
		  (save-excursion
		    (save-restriction
		      (narrow-to-region verbatim (point))
		      (goto-char (point-min))
		      (while (search-forward "@{" nil t)
			(replace-match "{" t t))
		      (goto-char (point-min))
		      (while (search-forward "@}" nil t)
			(replace-match "}" t t))))
		  (setq verbatim nil)
		  (insert "\\end{verbatim}\n"))
		 ((member arg '("table"))
		  (setq item-string (pop item-stack))
		  (latexi-strip-line)
		  (insert (format "\\end{%slist}\n" (pop list-stack))))
		 ((member arg '("itemize" "enumerate"))
		  (setq item-string (pop item-stack))
		  (latexi-strip-line)
		  (insert (format "\\end{%s}\n" arg)))
		 ((member arg '("iflatex" "iftex" "cartouche" "group"))
		  (latexi-strip-line))
		 ((member arg '("deffn" "defvar" "defun"))
		  (latexi-strip-line))
		 (t
		  (error "Unknown end arg: %s" arg))))
	       ((member command '("table"))
		(push item-string item-stack)
		(push (substring arg 1) list-stack)
		(setq item-string 
		      (format "[@%s{%%s}]" (car list-stack)))
		(latexi-strip-line)
		(insert (format "\\begin{%slist}\n" (car list-stack))))
	       ((member command '("itemize" "enumerate"))
		(push item-string item-stack)
		(cond 
		 ((member arg '("@bullet"))
		  (setq item-string "[\\gnusbullet]"))
		 (t
		  (setq item-string "")))
		(latexi-strip-line)
		(insert (format "\\begin{%s}\n" command)))
	       ((member command '("item"))
		(latexi-strip-line)
		(insert (format "\\%s%s\n" command (format item-string arg))))
	       ((equal command "itemx")
		(latexi-strip-line)
		(insert (format "\\gnusitemx{%s}\n" (format item-string arg))))
	       ((eq (aref command 0) ?@)
		(goto-char (match-beginning 0))
		(delete-char 2)
		(insert "duppat{}"))
	       ((equal command "settitle")
		(latexi-strip-line)
		(if (not as-a-chapter)
		    (insert 
		     (format "\\newcommand{\\gnustitlename}{%s}\n" arg))))
	       ((equal command "title")
		(latexi-strip-line)
		(insert (format "\\gnustitlename{%s}\n" arg)))
	       ((equal command "author")
		(latexi-strip-line)
		(insert (format "\\gnusauthor{%s}\n" arg)))
	       ((equal command "quotation")
		(latexi-begin-command "verse"))
	       ((equal command "page")
		(latexi-strip-line)
		(insert "\\newpage\n"))
	       ((equal command "'s")
		(goto-char (match-beginning 0))
		(delete-char 1))
	       ((equal command "include")
		(latexi-strip-line)
		(string-match "\\.texi" arg)
		(insert (format "\\input{%s.latexi}\n" 
				(substring arg 0 (match-beginning 0)))))
	       ((equal command "noindent")
		(latexi-strip-line)
		(insert "\\noindent\n"))
	       ((equal command "printindex")
		(latexi-strip-line)
		;;(insert 
		;; (format 
		;;  "\\begin{theindex}\\input{gnus.%s}\\end{theindex}\n" arg))
		)
	       (t
		(error "Unknown command (file %s line %d): %s"
		       file
		       (save-excursion
			 (widen)
			 (1+ (count-lines (point-min) (progn
							(beginning-of-line)
							(point)))))
		       command))))
	  ;; These are commands with {}.
	  (setq arg (match-string 5))
	  (cond 
	   ((member command '("anchor"))
	    (latexi-strip-line))
	   ((member command '("ref" "xref" "pxref"))
	    (latexi-exchange-command (concat "gnus" command) arg))
	   ((member command '("sc" "file" "dfn" "emph" "kbd" "key" "uref"
			      "code" "samp" "var" "strong" "i"
			      "result" "email" "env" "r" "command" "asis"
			      "url"))
	    (goto-char (match-beginning 0))
	    (delete-char 1)
	    (insert "\\gnus"))
	   ((member command '("acronym"))
	    (latexi-exchange-command (concat "gnus" command) (downcase arg)))
	   ((member command '("copyright" "footnote" "TeX"))
	    (goto-char (match-beginning 0))
	    (delete-char 1)
	    (insert "\\"))
	   ((member command '("dots"))
	    (goto-char (match-beginning 0))
	    (delete-region (match-beginning 0) (match-end 0))
	    (insert "..."))
	   ((eq (aref command 0) ?@)
	    (goto-char (match-beginning 0))
	    (delete-char 2)
	    (insert "duppat{}"))
	   (t
	    (error "Unknown command (file %s line %d): %s"
		   file
		   (save-excursion
		     (widen)
		     (1+ (count-lines (point-min) (progn
						    (beginning-of-line)
						    (point)))))
		   command))))))
    (latexi-translate-string "$" "\\gnusdollar{}")
    (latexi-translate-string "&" "\\gnusampersand{}")
    (latexi-translate-string "%" "\\gnuspercent{}")
    (latexi-translate-string "#" "\\gnushash{}")
    (latexi-translate-string "^" "\\gnushat{}")
    (latexi-translate-string "~" "\\gnustilde{}")
    (latexi-translate-string "_" "\\gnusunderline{}")
    (latexi-translate-string "¬" "\\gnusnot{}")
    (goto-char (point-min))
    (while (search-forward "duppat{}" nil t)
      (replace-match "@" t t))
    (latexi-translate-string "@@" "@")
    (latexi-translate-string "<" "\\gnusless{}")
    (latexi-translate-string ">" "\\gnusgreater{}")
    (goto-char (point-min))
    (search-forward "label{Top}" nil t)
    (while (re-search-forward "\\\\[ntr]\\b" nil t)
      (when (save-match-data
	      (or (not (save-excursion
			 (search-backward "begin{verbatim}" nil t)))
		  (> (save-excursion
		       (search-backward "end{verbatim"))
		     (save-excursion
		       (search-backward "begin{verbatim}")))))
	(goto-char (match-beginning 0))
	(delete-char 1)
	(insert "\\gnusbackslash{}")))
    (latexi-translate-string "\\\\" "\\gnusbackslash{}")
    (goto-char (point-min))
    (while (re-search-forward "\\\\[][{}]" nil t)
      (goto-char (match-beginning 0))
      (delete-char 1))
    (latexi-contributors)
    (let ((coding-system-for-write 'iso-8859-1))
      (write-region (point-min) (point-max) (concat file ".latexi")))))

(defun latexi-translate-string (in out)
  (let (yes)
    (goto-char (point-min))
    (search-forward "label{Top}" nil t)
    (while (search-forward in nil t)
      (when (save-match-data
	      (or (not (save-excursion
			 (search-backward "begin{verbatim}" nil t)))
		  (> (save-excursion
		       (re-search-backward "end{verbatim}\\|end{verse}"))
		     (save-excursion
		       (re-search-backward
			"begin{verbatim}\\|begin{verse}")))))
	(replace-match out t t)))))

(defun latexi-contributors ()
  (goto-char (point-min))
  (when (re-search-forward "^Also thanks to the following" nil t)
    (forward-line 2)
    (narrow-to-region
     (point)
     (1- (search-forward "\n\n")))
    (when (re-search-backward "^and" nil t)
      (latexi-strip-line))
    (goto-char (point-min))
    (while (re-search-forward "[.,] *$" nil t)
      (replace-match "" t t))
    (goto-char (point-min))
    (let (names)
      (while (not (eobp))
	(push (buffer-substring (point) (progn (end-of-line) (point)))
	      names)
	(forward-line 1))
      (delete-region (point-min) (point-max))
      (insert "\\begin{tabular}{lll}\n")
      (setq names (nreverse (delete "" names)))
      (while names
	(insert (pop names) " & " (or (pop names) "\\mbox{}") 
		" & " (or (pop names) "\\mbox{}") 
		"\\\\\n"))
      (insert "\\end{tabular}\n")
      (widen))))

(defvar latexi-copying-text ""
  "Text of the copyright notice and copying permissions.")

(defun latexi-copying ()
  "Copy the copyright notice and copying permissions from the Texinfo file,
as indicated by the @copying ... @end copying command;
insert the text with the @insertcopying command."
  (let ((beg (progn (beginning-of-line) (point)))
	(end  (progn (re-search-forward "^@end copying[ \t]*\n") (point))))
    (setq latexi-copying-text
	  (buffer-substring-no-properties
	   (save-excursion (goto-char beg) (forward-line 1) (point))
	   (save-excursion (goto-char end) (forward-line -1) (point))))
    (delete-region beg end)))

(defun latexi-insertcopying ()
  "Insert the copyright notice and copying permissions from the Texinfo file,
which are indicated by the @copying ... @end copying command."
  (insert (concat "\n" latexi-copying-text)))
