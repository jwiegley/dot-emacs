;;; coq-local-vars.el --- local variable list tools for coq
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>

;; $Id$ 


;;; Commentary:
;; 


;;; History:
;; 

(defconst coq-local-vars-doc nil
  "A very convenient way to customize file-specific variables is to use the
File Variables ((xemacs)File Variables). This feature of Emacs allows to
specify the values to use for certain Emacs variables when a file is
loaded. Those values are written as a list at the end of the file.

We provide the following feature to help you:

\\[coq-ask-insert-coq-prog-name] that builds standard local variable list for a
coq file by asking you some questions. it is accessible in the menu:

\"coq\"/\"set coq prog name for this file persistently\".

You should be able to use this feature without reading the rest of this
documentation, which explains how it is used for coq. For more precision, refer
to the emacs info manual at ((xemacs)File Variables).

In projects involving multiple directories, it is often useful to set the
variables `proof-prog-name', `proof-prog-args' and `compile-command' for each
file. Here is an example for Coq users: for the file .../dir/bar/foo.v, if you
want Coq to be started with the path .../dir/theories/ added in the libraries
path (\"-I\" option), you can put at the end of foo.v:

(* 
*** Local Variables: ***
*** coq-prog-name: \"coqtop\" ***
*** coq-prog-args: (\"-emacs\" \"-I\" \"../theories\") ***
*** End: ***
*)

That way the good command is called when the scripting starts in foo.v. Notice
that the command argument \"-I\" \"../theories\" is specific to the file foo.v,
and thus if you set it via the configuration tool, you will need to do it each
time you load this file. On the contrary with this method, Emacs will do this
operation automatically when loading this file. Please notice that all the
strings above should never contain spaces see documentation of variables
`proof-prog-name' and `proof-prog-args'.

Extending the previous example, if the makefile for foo.v is located in
directory .../dir/, you can add the right compile command. And if you want a
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
local variable (info:(xemacs)File Variables).
" )


(defun coq-insert-coq-prog-name (progname progargs)
  "Insert or modify (if already existing) the local variables `coq-prog-name'
and `coq-prog-args'.  These variables describe the coqtop command to be
launched on this file."
  (local-vars-list-set 'coq-prog-name progname)
  (local-vars-list-set 'coq-prog-args progargs)
  )


(defun coq-ask-build-addpath-option ()
  "Ask for and return a directory name."
  (let* 
      ;; read-file-name here because it is convenient to see .v files when selecting
      ;; directories to add to the path
      ((path (read-file-name "library path to add (empty to stop) : "
                             "" "" t)))
    (if (and (string-match " " path)
             (not (y-or-n-p "The path contains spaces, are you sure? (y or n) :")))
        (coq-ask-build-addpath-option) ; retry
      path)))

(defun coq-ask-prog-args ()
  "Ask for and return the information to put into variables coq-prog-args.
These variable describes the coqtop arguments to be launched on this file."  
  (let ((progargs '("-emacs"))
        (option (coq-ask-build-addpath-option)))
    (message "progargs = %s" progargs)
    (while (not (string-equal option ""))
      (setq progargs (cons option (cons "-I" progargs))) ;reversed
      (message "progargs = %s" progargs)
      (setq option (coq-ask-build-addpath-option)))
    (message "progargs = %s" progargs)
    (reverse progargs)))

(defun coq-ask-prog-name ()
  "Ask for and return the local variables coq-prog-name.
These variable describes the coqtop command to be launched on this file."  
  (let ((cmd (read-string "coq program name (default coqtop) : " "coqtop")))
    (if (and 
         (string-match " " cmd)
         (not (y-or-n-p "The prog name contains spaces, are you sure? (y or n) :")))
        (coq-ask-prog-name) ; retry
      cmd)))


(defun coq-ask-insert-coq-prog-name ()
  "Ask for and insert the local variables coq-prog-name and coq-prog-args.
These variables describe the coqtop command to be launched on this file."  
  (interactive)
  (let ((progname (coq-ask-prog-name))
        (progargs (coq-ask-prog-args)))
    (coq-insert-coq-prog-name progname progargs)
    (setq coq-prog-name progname)
    (setq coq-prog-args progargs)))

(provide 'coq-local-vars)


;;   Local Variables: ***
;;   fill-column: 79 ***
;;   indent-tabs-mode: nil ***
;;   End: ***

;;; coq.el ends here
