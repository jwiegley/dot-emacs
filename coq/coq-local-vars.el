;;; coq-local-vars.el --- local variable list tools for coq
;; Copyright (C) 1994 - 1998 LFCS Edinburgh.
;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; $Id$


;;; Commentary:
;; 


;;; History:
;; 

;;; Code:
(defconst coq-local-vars-doc nil
  "Documentation-only variable.
A very convenient way to customize file-specific variables is to use the
File Variables (info:(Emacs)File Variables).  This feature of Emacs allows to
specify the values to use for certain Emacs variables when a file is
loaded.  Those values are written as a list at the end of the file.

We provide the following feature to help you:

\\[coq-ask-insert-coq-prog-name] that builds standard local variable list for a
coq file by asking you some questions.  it is accessible in the menu:

\"coq\"/\"set coq prog *persistently*\".

You should be able to use this feature without reading the rest of this
documentation, which explains how it is used for coq.  For more precision, refer
to the Emacs info manual at ((Emacs)File Variables).

In projects involving multiple directories, it is often useful to set the
variables `proof-prog-name', `proof-prog-args' and `compile-command' for each
file.  Here is an example for Coq users: for the file .../dir/bar/foo.v, if you
want Coq to be started with the path .../dir/theories/ added in the libraries
path (\"-I\" option), you can put at the end of foo.v:

(*
*** Local Variables: ***
*** coq-prog-name: \"coqtop\" ***
*** coq-prog-args: (\"-emacs\" \"-I\" \"../theories\") ***
*** End: ***
*)

That way the good command is called when the scripting starts in foo.v.  Notice
that the command argument \"-I\" \"../theories\" is specific to the file foo.v,
and thus if you set it via the configuration tool, you will need to do it each
time you load this file.  On the contrary with this method, Emacs will do this
operation automatically when loading this file.  Please notice that all the
strings above should never contain spaces see documentation of variables
`proof-prog-name' and <prover>-prog-args (see for example `coq-prog-args').

Extending the previous example, if the makefile for foo.v is located in
directory .../dir/, you can add the right compile command.  And if you want a
non standard coq executable to be used, here is what you should put in
variables:

(*
 Local Variables:
 coq-prog-name: \"../../coqsrc/bin/coqtop\"
 coq-prog-args: \"-emacs\" \"-I\" \"../theories\"
 compile-command: \"make -C .. -k bar/foo.vo\"
 End:
*)

And then the right call to make will be done if you use the \\[compile]
command. Notice that the lines are commented in order to be ignored by the
proof assistant. It is possible to use this mechanism for any other buffer
local variable (info:(Emacs)File Variables)." )


(defun coq-insert-coq-prog-name (progname progargs)
  "Insert or modify the local variables `coq-prog-name' and `coq-prog-args'.
Set them to PROGNAME and PROGARGS respectively.  These variables describe the
coqtop command to be launched on this file."
  (local-vars-list-set 'coq-prog-name progname)
  (local-vars-list-set 'coq-prog-args progargs)
  )


(defun coq-read-directory (prompt &optional maynotmatch initialcontent)
  "Ask for (using PROMPT) and return a directory name."
  (let*
      ;; read-file-name here because it is convenient to see .v files
      ;; when selecting directories to add to the path. Moreover
      ;; read-directory-name does not seem to exist in fsf emacs??
      ((path (read-file-name prompt "" "" (not maynotmatch) initialcontent)))
    path))

;(read-from-minibuffer
;         PROMPT &optional INITIAL-CONTENTS KEYMAP READP HISTORY ABBREV-TABLE DEFAULT)
;(read-directory-name
;         PROMPT &optional DIR DEFAULT MUST-MATCH INITIAL-CONTENTS HISTORY)

(defun coq-extract-directories-from-args (args)
  "Extract directory names from coq option list ARGS."
  (if (not args) ()
    (let ((hd (car args)) (tl (cdr args)))
      (cond
       ((string-equal hd "-I")
	(cond
	 ((not tl) nil)
	 ; if the option following -I starts with '-', forget the -I :
	 ((char-equal ?- (string-to-char (car tl)))
	  (coq-extract-directories-from-args tl))
	 (t (cons (car tl) (coq-extract-directories-from-args (cdr tl))))))
       (t (coq-extract-directories-from-args tl))))))


(defun coq-ask-prog-args (&optional oldvalue)
  "Ask for and return the information to put into variables `coq-prog-args'.
These variable describes the coqtop arguments to be launched on this file.
Optional argument OLDVALUE specifies the previous value of `coq-prog-args', it
will be used to suggest values to the user."
  (let* ((olddirs (coq-extract-directories-from-args oldvalue))
	 (progargs (if coq-utf-safe '("-emacs-U") '("-emacs")))
	 (option))
    ;; first suggest preious directories
    (while olddirs
      (if (y-or-n-p (format "Keep the directory %s? " (car olddirs)))
	  (setq progargs (cons (car olddirs) (cons "-I" progargs))))
      (setq olddirs (cdr olddirs)))
    ;; then ask for more
    (setq option (coq-read-directory "Add directory (tab to complete, empty to stop) :"))
    (while (not (string-equal option ""))
      (setq progargs (cons option (cons "-I" progargs))) ;reversed
      (setq option (coq-read-directory "Add directory (tab to complete, empty to stop) -I :")))
    (reverse progargs)))

(defun coq-ask-prog-name (&optional oldvalue)
  "Ask for and return the local variables `coq-prog-name'.
These variable describes the coqtop command to be launched on this file.
Optional argument OLDVALUE specifies the previous value of `coq-prog-name', it
will be used to suggest a value to the user."
  (let ((cmd (coq-read-directory "coq program name (default coqtop) : " t
			  (or oldvalue "coqtop"))))
    (if (and
         (string-match " " cmd)
         (not (y-or-n-p "The prog name contains spaces, are you sure ? ")))
        (coq-ask-prog-name) ; retry
      cmd)))


(defun coq-ask-insert-coq-prog-name ()
  "Ask for and insert the local variables `coq-prog-name' and `coq-prog-args'.
These variables describe the coqtop command to be launched on this file."
  (interactive)
  (let* ((oldname (local-vars-list-get-safe 'coq-prog-name))
	 (oldargs (local-vars-list-get-safe 'coq-prog-args))
	 (progname (coq-ask-prog-name oldname))
        (progargs (coq-ask-prog-args oldargs)))
    (coq-insert-coq-prog-name progname progargs)
    (setq coq-prog-name progname)
    (setq coq-prog-args progargs)))



(provide 'coq-local-vars)

;;; coq-local-vars.el ends here

;;   Local Variables: ***
;;   fill-column: 79 ***
;;   indent-tabs-mode: nil ***
;;   End: ***
