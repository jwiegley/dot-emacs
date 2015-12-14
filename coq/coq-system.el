;; coq-system.el --- common part of compilation feature
;; Copyright (C) 2015 LFCS Edinburgh.
;; Authors: Hendrik Tews, Pierre Courtieu
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Pierre.Courtieu<Pierre.Courtieu@cnam.fr>
;;

;;; Commentary:
;;
;; This file holds constants, options and some general functions for
;; setting coq command arguments. Some code is dedicated as a light
;; support for older versions of coq.
;;

(require 'proof)

(eval-when-compile
  (require 'cl)
  (require 'proof-compat)
  (proof-ready-for-assistant 'coq))

(eval-when (compile)
  (defvar coq-prog-args nil)
  (defvar coq-debug nil))

(eval-when (compile)
  (defvar coq-pre-v85 nil))

(defun get-coq-version ()
  (let ((c (shell-command-to-string "coqtop -v")))
    (if (string-match "version \\([^ ]+\\)\\s-" c)
	(match-string 1 c)
      c)))


(defcustom coq-prog-env nil
  "List of environment settings d to pass to Coq process.
On Windows you might need something like:
  (setq coq-prog-env '(\"HOME=C:\\Program Files\\Coq\\\"))"
  :group 'coq)

(defcustom coq-prog-name
  (proof-locate-executable "coqtop" t '("C:/Program Files/Coq/bin"))
   "*Name of program to run as Coq. See `proof-prog-name', set from this.
On Windows with latest Coq package you might need something like:
   C:/Program Files/Coq/bin/coqtop.opt.exe
instead of just \"coqtop\".
This must be a single program name with no arguments; see `coq-prog-args'
to manually adjust the arguments to the Coq process.
See also `coq-prog-env' to adjust the environment."
   :type 'string
   :group 'coq)

(defcustom coq-dependency-analyzer
  (proof-locate-executable "coqdep" t '("C:/Program Files/Coq/bin"))
  "Command to invoke coqdep."
  :type 'string
  :group 'coq)

(defcustom coq-compiler
  (proof-locate-executable "coqc" t '("C:/Program Files/Coq/bin"))
  "Command to invoke the coq compiler."
  :type 'string
  :group 'coq)

(defun get-coq-library-directory ()
  (let ((c (substring (shell-command-to-string (concat coq-prog-name " -where")) 0 -1 )))
    (if (string-match "not found" c)
        "/usr/local/lib/coq"
      c)))

(defconst coq-library-directory (get-coq-library-directory)
  "The coq library directory, as reported by \"coqtop -where\".")

(defcustom coq-tags (concat coq-library-directory "/theories/TAGS")
  "The default TAGS table for the Coq library."
  :type 'string
  :group 'coq)

(defcustom coq-pre-v85 nil
  "Whether to use <= coq-8.4 config (nil by default).
Mainly to deal with command line options that changed between 8.4
and 8.5 (-Q foo bar replace -I foo)."
  :type 'boolean
  :group 'coq)

(defcustom coq-use-makefile nil
  "Whether to look for a Makefile to attempt to guess the command line.
Set to t if you want this feature."
  :type 'string
  :group 'coq)

(defcustom coq-www-home-page "http://coq.inria.fr/"
  "Coq home page URL."
  :type 'string
  :group 'coq)

;;; utility functions for variables

(defun coq-load-path-safep (path)
  "Check if PATH is a safe value for `coq-load-path'."
  (and
   (listp path)
   (every
    (lambda (entry)
      (or (stringp entry)
          (and (listp entry)
               (eq (car entry) 'rec)
               (every 'stringp (cdr entry))
               (equal (length entry) 3))
          (and (listp entry)
               (eq (car entry) 'nonrec)
               (every 'stringp (cdr entry))
               (equal (length entry) 3))
          (and (listp entry)
               (eq (car entry) 'recnoimport)
               (every 'stringp (cdr entry))
               (equal (length entry) 3))
          (and (listp entry)
               (eq (car entry) 'ocamlimport)
               (every 'stringp (cdr entry))
               (equal (length entry) 2))
          (and (listp entry)
               (every 'stringp entry)
               (equal (length entry) 2))))
    path)))

(defcustom coq-load-path nil
  "Non-standard coq library load path.
This list specifies the LoadPath extension for coqdep, coqc and
coqtop. Usually, the elements of this list are strings (for
\"-I\") or lists of two strings (for \"-R\" dir path and
\"-Q\" dir path).

The possible forms of elements of this list correspond to the 4
forms of include options ('-I' '-Q' and '-R'). An element can be

  - A list of the form '(ocamlimport dir)', specifying a
    directory to be added to ocaml path ('-I').
  - A list of the form '(rec dir path)' (where dir and path are
    strings) specifying a directory to be recursively mapped to the
    logical path 'path' ('-R dir path').
  - A list of the form '(recnoimport dir path)' (where dir and
    path are strings) specifying a directory to be recursively
    mapped to the logical path 'path' ('-Q dir path'), but not
    imported (modules accessible for import with qualified names
    only).
  - A list of the form '(norec dir)', specifying a directory
    to be mapped to the empty logical path ('-Q dir \"\"').

For convenience the symbol 'rec' can be omitted and entries of
the form '(dir path)' are interpreted as '(rec dir path)'.

Under normal circumstances this list does not need to
contain the coq standard library or \".\" for the current
directory (see `coq-load-path-include-current').

WARNING: if you use coq <= 8.4, the meaning of these options is
not the same (-I is for coq path).
"
  :type '(repeat (choice (string :tag "simple directory without path (-Q \"\")") ; is this really useful?
                         (list :tag
                               "recursive directory with path (-R ... -as ...)"
                               (const rec)
                               (string :tag "directory")
                               (string :tag "log path"))
			 (list :tag
                               "recursive directory without recursive inport with path (-Q ... ...)"
                               (const recnoimport)
                               (string :tag "directory")
                               (string :tag "log path"))
                         (list :tag
                               "directory with empty logical path (-Q ... "" in coq>=8.5, -I ... in coq<=8.4)"
                               (const nonrec)
                               (string :tag "directory")
                               (string :tag "log path"))
                         (list :tag
                               "ocaml path (-I ...)"
                               (const ocamlimport)
                               (string :tag "directory")
                               (string :tag "log path"))))
  :safe 'coq-load-path-safep
  :group 'coq-auto-compile)

(make-variable-buffer-local 'coq-load-path)

(defcustom coq-load-path-include-current t
  "If `t' let coqdep search the current directory too.
Should be `t' for normal users. If `t' pass -Q dir \"\" to coqdep when
processing files in directory \"dir\" in addition to any entries
in `coq-load-path'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defun coq-option-of-load-path-entry (entry)
  "Translate a single element from `coq-load-path' into options.
See `coq-load-path' for the possible forms of entry and to which
options they are translated."
  (cond
   ((and coq-pre-v85 (stringp entry))
    (list "-I" (expand-file-name entry)))
   ((and (not coq-pre-v85) (stringp entry))
    (list "-Q" (expand-file-name entry) ""))
   ((and coq-pre-v85 (eq (car entry) 'nonrec))
    (list "-I" (expand-file-name (nth 1 entry)) "-as" (nth 2 entry)))
   ((and (not coq-pre-v85) (eq (car entry) 'nonrec)) ;; N/A?
    (list "-Q" (expand-file-name (nth 1 entry)) (nth 2 entry)))
   ((eq (car entry) 'recnoimport) ;; only for >=8.5
    (list "-Q" (expand-file-name (nth 1 entry)) (nth 2 entry)))
   (t
    (if (eq (car entry) 'rec)
        (setq entry (cdr entry)))
    (if coq-pre-v85 ;; -as obsolete in 8.5
	(list "-R" (expand-file-name (car entry)) "-as" (nth 1 entry))
      (list "-R" (expand-file-name (car entry)) (nth 1 entry))))))

(defun coq-include-options (file coq-load-path)
  "Build the list of include options for coqc, coqdep and coqtop.
The options list includes all entries from argument COQ-LOAD-PATH
\(which should be `coq-load-path' of the buffer that invoked the
compilation) prefixed with suitable options and (for coq<8.5), if
`coq-load-path-include-current' is enabled, the directory base of
FILE. The resulting list is fresh for every call, callers can
append more arguments with `nconc'.

FILE should be an absolute file name. It can be nil if
`coq-load-path-include-current' is nil."
  (let ((result nil))
    (unless (coq-load-path-safep coq-load-path)
      (error "Invalid value in coq-load-path"))
    (when coq-load-path
      (setq result (coq-option-of-load-path-entry (car coq-load-path)))
      (dolist (entry (cdr coq-load-path))
        (nconc result (coq-option-of-load-path-entry entry))))
    (if coq-load-path-include-current
        (setq result
              (if coq-pre-v85
		  (cons "-I" (cons (file-name-directory file) result))
		;; from coq-8.5 beta3 cpqdep does not needthis anymore
		;; and actually it can clash with -Q . foo written in
		;; _CoqProject
		;; (cons "-Q" (cons (file-name-directory file) (cons "" result)))
		result)))
    result))



(defun coq-coqdep-prog-args (&optional src-file loadpath)
  (let ((loadpath (or loadpath coq-load-path)))
    (coq-include-options src-file loadpath)))

(defun coq-coqc-prog-args (&optional src-file loadpath)
  ;; coqtop always adds the current directory to the LoadPath, so don't
  ;; include it in the -Q options.
  (let ((coqdep-args
	 (let ((coq-load-path-include-current nil)) ; obsolete >=8.5beta3
	   ;; by the time this function is called, coq-prog-args should be set 
	   (append coq-prog-args
		   (coq-coqdep-prog-args src-file loadpath)))))
    (remove "-emacs" (remove "-emacs-U" coqdep-args))))

;;XXXXXXXXXXXXXX
;; coq-coqtop-prog-args is the user-set list of arguments to pass to
;; Coq process, see 'defpacustom prog-args' in pg-custom.el for
;; documentation.

(defun coq-coqtop-prog-args (&optional src-file loadpath)
  ;; coqtop always adds the current directory to the LoadPath, so don't
  ;; include it in the -Q options. This is not true for coqdep.
  (cons "-emacs" (coq-coqc-prog-args src-file loadpath)))

;; FIXME: we seem to need this function with this exact name,
;; otherwise coqtop command is not generated with the good load-path
;; (??). Is it interfering with defpgcustom's in pg-custom.el?
(defun coq-prog-args () (coq-coqtop-prog-args))



(defcustom coq-use-project-file t
  "If t, when opening a coq file read the dominating _CoqProject.
If t when a coq file is opened, proofgeneral will look for a
project file (see `coq-project-filename') somewhere in the
current directory or its parents directory. If there is one, its
content is read and used to determine the arguments that must be
given to coqtop. In particular it sets the load path (including
the -R lib options) (see `coq-load-path') ."
  :type 'boolean
  :group 'coq)

(defcustom coq-project-filename "_CoqProject"
  "The name of coq project file.
The coq project file of a coq developpement (Cf Coq documentation
on \"makefile generation\") should contain the arguments given to
coq_makefile. In particular it contains the -I and -R
options (one per line). If `coq-use-coqproject' is t (default)
the content of this file will be used by proofgeneral to infer
the `coq-load-path' and the `coq-prog-args' variables that set
the coqtop invocation by proofgeneral. This is now the
recommended way of configuring the coqtop invocation. Local file
variables may still be used to override the coq project file's
configuration. .dir-locals.el files also work and override
project file settings."
  :type 'string
  :group 'coq)


(defun coq-find-project-file ()
  "Return '(buf alreadyopen) where buf is the buffer visiting coq project file.
alreadyopen is t if buffer already existed."
  (let* (
         (projectfiledir (locate-dominating-file buffer-file-name coq-project-filename)))
    (when projectfiledir
      (let* ((projectfile (expand-file-name coq-project-filename projectfiledir))
             ;; we store this intermediate result to know if we have to kill
             ;; the coq project buffer at the end
             (projectbufferalreadyopen (find-buffer-visiting projectfile))
             (projectbuffer (or projectbufferalreadyopen
                                (find-file-noselect projectfile t t))))
        (list projectbuffer projectbufferalreadyopen)))))

;; No "." no "-" in coq module file names, but we do not check
;; TODO: look exactly at what characters are allowed.
(defconst coq-load-path--R-regexp
  "\\_<-R\\s-+\\(?1:[^[:space:]]+\\)\\s-+\\(?2:[^[:space:]]+\\)")

(defconst coq-load-path--Q-regexp
  "\\_<-Q\\s-+\\(?1:[^[:space:]]+\\)\\s-+\\(?2:[^[:space:]]+\\)")

;; second arg of -I is optional (and should become obsolete one day)
(defconst coq-load-path--I-regexp
  "\\_<-I\\s-+\\(?1:[^[:space:]]+\\)\\(?:[:space:]+\\(?2:[^[:space:]]+\\)\\)?")

;(defconst coq-load-path--I-regexp "\\_<-I\\s-+\\(?1:[^[:space:]]+\\)")

;; match-string 1 must contain the string to add to coqtop command line, so we
;; ignore -arg, we use numbered subregexpr.

;; FIXME: if several options are given (within "") in a single -arg line, then
;; they are glued and passed as a single argument to coqtop. this is bad and
;; not conforming to coq_makefile. HOWEVER: this is probably a bad feature of
;; coq_makefile to allow several arguments in a single - arg "xxx yyy".
(defconst coq-prog-args-regexp
  "\\_<\\(?1:-opt\\|-byte\\)\\|-arg[[:space:]]+\\(?:\\(?1:[^\"\t\n#]+\\)\\|\"\\(?1:[^\"]+\\)\"\\)")


(defun coq-read-option-from-project-file (projectbuffer regexp &optional dirprefix)
  "look for occurrences of regexp in buffer projectbuffer and collect subexps.
The returned sub-regexp are the one numbered 1 and 2 (other ones
should be unnumbered). If there is only subexp 1 then it is added
as is to the final list, if there are 1 and 2 then a list
containing both is added to the final list. If optional DIRPREFIX
is non nil, then options ar considered as directory or file names
and will be made absolute from directory named DIRPREFIX. This
allows to call coqtop from a subdirectory of the project."
  (let ((opt nil))
    (when projectbuffer
      (with-current-buffer projectbuffer
        (goto-char (point-min))
        (while (re-search-forward regexp nil t)
          (let* ((firstfname (match-string 1))
                 (second (match-string 2))
                 (first (if (null dirprefix) firstfname
                          (expand-file-name firstfname dirprefix))))
            (if second ; if second arg is "" (two doublequotes), it means empty string
                (let ((sec (if (string-equal second "\"\"") "" second)))
                  (if (string-match coq-load-path--R-regexp (match-string 0))
                      (setq opt (cons (list first sec) opt))
                    (setq opt (cons (list 'recnoimport first sec) opt))))
              (setq opt (cons first opt))))))
      (reverse opt))))

;; Look for -R and -I options in the project buffer
;; add the default "." too
(defun coq-search-load-path (projectbuffer)
  "Read project buffer and retrurn a value for `coq-load-path'."
;;  no automatic insertion of "." here because some people want to do "-R . foo" so
;;  let us avoid conflicts.
  (coq-read-option-from-project-file
   projectbuffer
   (concat coq-load-path--R-regexp "\\|" coq-load-path--Q-regexp "\\|" coq-load-path--I-regexp)
   (file-name-directory (buffer-file-name projectbuffer))))

;; Look for other options (like -opt, -arg foo etc) in the project buffer
;; adds the -emacs option too
(defun coq-search-prog-args (projectbuffer)
  "Read project buffer and retrurn a value for `coq-prog-args'"
  (cons
   "-emacs"
   (coq-read-option-from-project-file projectbuffer coq-prog-args-regexp)))


;; optional args allow to implement the precedence of dir/file local vars
(defun coq-load-project-file-with-avoid (&optional avoidargs avoidpath)
  (let* ((projectbuffer-aux (coq-find-project-file))
         (projectbuffer (and projectbuffer-aux (car projectbuffer-aux)))
         (no-kill (and projectbuffer-aux (car (cdr projectbuffer-aux)))))
    (if (not projectbuffer-aux)
        (message "Coq project file not detected.")
      (unless avoidargs (setq coq-prog-args (coq-search-prog-args projectbuffer)))
      (unless avoidpath (setq coq-load-path (coq-search-load-path projectbuffer)))
      (let ((msg
             (cond
              ((and avoidpath avoidargs) "Coqtop args and load path")
              (avoidpath "Coqtop load path")
              (avoidargs "Coqtop args")
              (t ""))))
        (message
         "Coq project file detected: %s%s." (buffer-file-name projectbuffer)
         (if (or avoidpath avoidargs)
             (concat "\n(" msg " overridden by dir/file local values)")
           "")))
      (when coq-debug
        (message "coq-prog-args: %S" coq-prog-args)
        (message "coq-load-path: %S" coq-load-path))
      (unless no-kill (kill-buffer projectbuffer)))))



(defun coq-load-project-file ()
  "Set `coq-prog-args' and `coq-load-path' according to _CoqProject file.
Obeys `coq-use-project-file'. Note that if a variable is already
set by dir/file local variables, this function will not override
its value.
See `coq-project-filename' to change the name of the
project file, and `coq-use-project-file' to disable this
feature."
  (when coq-use-project-file
    ;; Let us reread dir/file local vars, in case the user mmodified them
    (let* ((oldargs (assoc 'coq-prog-args file-local-variables-alist))
           (oldpath (assoc 'coq-load-path file-local-variables-alist)))
      (coq-load-project-file-with-avoid oldargs oldpath))))


(defun coq-load-project-file-rehack ()
  "Reread file/dir local vars and call `coq-load-project-file'.
Does nothing if `coq-use-project-file' is nil.
Warning: 
"
  (when coq-use-project-file
    ;; Let us reread dir/file local vars, in case the user mmodified them
    (hack-local-variables)
    ;; Useless since coq-load-project-file is in hack-local-variables-hook:
    ;;(coq-load-project-file)
    ))


;; Since coq-project-filename can be set via .dir-locals.el or file variable,
;; we need to call coq-load-coq-project-file only *after* local variables are
;; set. But coq-mode-hook is called BEFORE local variables are read. Therefore
;; coq-load-coq-project-file is added to hack-local-variables-hook instead. To
;; avoid adding for other modes , the setting is performed inside
;; coq-mode-hook. This is described in www.emacswiki.org/emacs/LocalVariables

;; TODO: also read COQBIN somewhere?
;; Note: this does not need to be at a particular place in the hook, but we
;; need to make this hook local.
;; hack-local-variables-hook seems to hack local and dir local vars.
(add-hook 'coq-mode-hook
          '(lambda ()
             (add-hook 'hack-local-variables-hook
                       'coq-load-project-file
                       nil t)))

;; smie's parenthesis blinking is too slow, let us have the default one back
(add-hook 'coq-mode-hook
          '(lambda ()
             (when (and (fboundp 'show-paren--default)
                        (boundp 'show-paren-data-function))
               (setq show-paren-data-function 'show-paren--default))))



(defun coq-toggle-use-project-file ()
  (interactive)
  (setq coq-use-project-file (not coq-use-project-file))
  (when coq-use-project-file (coq-load-project-file-rehack))
  ;; FIXME What should we do when disabling project file? since
  ;; local variables override project file anyway, reading them
  ;; again is useless. Let us do nothing.
  ;;(setq coq-load-path nil)
  ;;(setq coq-prog-args nil)
  )


(provide 'coq-system)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;    To guess the command line options   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; OBSOLETE, should take _CoqProject into account.
(defun coq-guess-command-line (filename)
  "Guess the right command line options to compile FILENAME using `make -n'.
This function is obsolete, the recommended way of setting the
coqtop options is to use a _Coqproject file as described in coq
documentation. ProofGeneral reads this file and sets compilation
options according to its contents. See `coq-project-filename'. Per file configuration may
then be set using local file variables."
  (if (local-variable-p 'coq-prog-name (current-buffer))
      coq-prog-name
    (let* ((dir (or (file-name-directory filename) "."))
           (makedir
           (cond
            ((file-exists-p (concat dir "Makefile")) ".")
            ;; ((file-exists-p (concat dir "../Makefile")) "..")
            ;; ((file-exists-p (concat dir "../../Makefile")) "../..")
            (t nil))))
      (if (and coq-use-makefile makedir)
          (let*
              ;;TODO, add dir name when makefile is in .. or ../..
              ;;
              ;; da: FIXME: this code causes problems if the make
              ;; command fails.  It should not be used by default
              ;; and should be made more robust.
              ;;
              ((compiled-file (concat (substring
                                       filename 0
                                       (string-match ".v$" filename)) ".vo"))
               (command (shell-command-to-string
                         (concat  "cd " dir ";"
                                  "make -n -W " filename " " compiled-file
                                  "| sed s/coqc/coqtop/"))))
            (message command)
            (setq coq-prog-args nil)
            (concat
             (substring command 0 (string-match " [^ ]*$" command))
             "-emacs-U"))
        coq-prog-name))))

;;; coq-compile-common.el ends here
