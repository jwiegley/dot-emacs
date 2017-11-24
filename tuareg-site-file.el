;;; tuareg-site-file.el --- Automatically extracted autoloads.
;;; Code:
(add-to-list 'load-path
             (or (file-name-directory load-file-name) (car load-path)))

;;;### (autoloads nil "ocamldebug" "ocamldebug.el" (22960 18385 186574
;;;;;;  216000))
;;; Generated autoloads from ocamldebug.el

(autoload 'ocamldebug "ocamldebug" "\
Run ocamldebug on program FILE in buffer *ocamldebug-FILE*.
The directory containing FILE becomes the initial working directory
and source-file directory for ocamldebug.  If you wish to change this, use
the ocamldebug commands `cd DIR' and `directory'.

\(fn PGM-PATH)" t nil)

(defalias 'camldebug 'ocamldebug)

;;;***

;;;### (autoloads nil "tuareg" "tuareg.el" (23005 3097 903887 888000))
;;; Generated autoloads from tuareg.el
(add-to-list 'auto-mode-alist '("\\.ml[ip]?\\'" . tuareg-mode))
(add-to-list 'auto-mode-alist '("\\.eliomi?\\'" . tuareg-mode))
(dolist (ext '(".cmo" ".cmx" ".cma" ".cmxa" ".cmi"
               ".annot" ".cmt" ".cmti"))
 (add-to-list 'completion-ignored-extensions ext))

(autoload 'tuareg-mode "tuareg" "\
Major mode for editing OCaml code.

Dedicated to Emacs and XEmacs, version 21 and higher.  Provides
automatic indentation and compilation interface.  Performs font/color
highlighting using Font-Lock.  It is designed for OCaml but handles
Caml Light as well.

The Font-Lock minor-mode is used according to your customization
options.

You have better byte-compile tuareg.el.

For customization purposes, you should use `tuareg-mode-hook'
\(run for every file) or `tuareg-load-hook' (run once) and not patch
the mode itself.  You should add to your configuration file something like:
  (add-hook 'tuareg-mode-hook
            (lambda ()
               ... ; your customization code
            ))
For example you can change the indentation of some keywords, the
`electric' flags, Font-Lock colors... Every customizable variable is
documented, use `C-h-v' or look at the mode's source code.

`dot-emacs.el' is a sample customization file for standard changes.
You can append it to your `.emacs' or use it as a tutorial.

`M-x ocamldebug' FILE starts the OCaml debugger ocamldebug on the executable
FILE, with input and output in an Emacs buffer named *ocamldebug-FILE*.

A Tuareg Interactive Mode to evaluate expressions in a REPL (aka toplevel) is
included.  Type `M-x tuareg-run-ocaml' or simply `M-x run-ocaml' or see
special-keys below.

Short cuts for the Tuareg mode:
\\{tuareg-mode-map}

Short cuts for interactions with the REPL:
\\{tuareg-interactive-mode-map}

\(fn)" t nil)

(autoload 'tuareg-run-ocaml "tuareg" "\
Run an OCaml REPL process.  I/O via buffer `*OCaml*'.

\(fn)" t nil)

(defalias 'run-ocaml 'tuareg-run-ocaml)

(add-to-list 'interpreter-mode-alist '("ocamlrun" . tuareg-mode))

(add-to-list 'interpreter-mode-alist '("ocaml" . tuareg-mode))

;;;***

;;;### (autoloads nil "tuareg-jbuild" "tuareg-jbuild.el" (23040 63673
;;;;;;  915101 116000))
;;; Generated autoloads from tuareg-jbuild.el

(autoload 'tuareg-jbuild-mode "tuareg-jbuild" "\
Major mode to edit jbuild files.

\(fn)" t nil)

(add-to-list 'auto-mode-alist '("\\(?:\\`\\|/\\)jbuild\\'" . tuareg-jbuild-mode))

;;;***

;;;### (autoloads nil "tuareg-opam" "tuareg-opam.el" (23040 63783
;;;;;;  815739 961000))
;;; Generated autoloads from tuareg-opam.el

(autoload 'tuareg-opam-mode "tuareg-opam" "\
Major mode to edit opam files.

\(fn)" t nil)

(add-to-list 'auto-mode-alist '("[./]opam_?\\'" . tuareg-opam-mode))

;;;***

;;;### (autoloads nil nil ("dot-emacs.el" "tuareg-light.el" "tuareg-mly.el")
;;;;;;  (22928 42647 125772 673000))

;;;***

