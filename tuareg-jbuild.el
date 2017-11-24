;;; tuareg-jbuild.el --- Mode for editing jbuild files   -*- coding: utf-8 -*-

;; Copyright (C) 2017- Christophe Troestler

;; This file is not part of GNU Emacs.

;; Permission to use, copy, modify, and distribute this software for
;; any purpose with or without fee is hereby granted, provided that
;; the above copyright notice and this permission notice appear in
;; all copies.
;;
;; THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL
;; WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
;; WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE
;; AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR
;; CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
;; LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT,
;; NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
;; CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

(require 'scheme)

(defvar tuareg-jbuild-mode-hook nil
  "Hooks for the `tuareg-jbuild-mode'.")

(defvar tuareg-jbuild-flymake nil
  "If t, check your jbuild file with flymake.")

(defvar tuareg-jbuild-temporary-file-directory
  (expand-file-name "Tuareg-jbuild" temporary-file-directory)
  "Directory where to duplicate the files for flymake.")

(defvar tuareg-jbuild-program
  (expand-file-name "jbuilder-lint" tuareg-jbuild-temporary-file-directory)
  "Script to use to check the jbuild file.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                     Syntax highlighting

(defconst tuareg-jbuild-keywords-regex
  (regexp-opt
   '("jbuild_version" "library" "executable" "executables" "rule"
     "ocamllex" "ocamlyacc" "menhir" "alias" "install" "copy_files")
   'symbols)
  "Keywords in jbuild files.")

(defconst tuareg-jbuild-fields-regex
  (regexp-opt
   '("name" "public_name" "synopsis" "modules" "libraries" "wrapped"
     "preprocess" "preprocessor_deps" "optional" "c_names" "cxx_names"
     "install_c_headers" "modes" "no_dynlink" "kind"
     "ppx_runtime_libraries" "virtual_deps" "js_of_ocaml" "flags"
     "ocamlc_flags" "ocamlopt_flags" "library_flags" "c_flags"
     "cxx_flags" "c_library_flags" "self_build_stubs_archive"
     ;; + for "executable" and "executables":
     "package" "link_flags" "modes" "names" "public_names"
     ;; + for "rule":
     "targets" "action" "deps" "fallback"
     ;; + for "menhir":
     "merge_into"
     ;; + for "install"
     "section" "files" "lib" "libexec" "bin" "sbin" "toplevel" "share"
     "share_root" "etc" "doc" "stublibs" "man" "misc")
   'symbols)
  "Field names allowed in jbuild files.")

(defvar tuareg-jbuild-actions-regex
  (regexp-opt
   '("run" "chdir" "setenv"
     "with-stdout-to" "with-stderr-to" "with-outputs-to"
     "ignore-stdout" "ignore-stderr" "ignore-outputs"
     "progn" "echo" "write-file" "cat" "copy" "copy#" "system" "bash")
   t)
  "Builtin actions in jbuilder")

(defvar tuareg-jbuild-var-kind-regex
  (regexp-opt
   '("path" "path-no-dep" "exe" "bin" "lib" "libexec" "lib-available"
     "version" "read" "read-lines" "read-strings")
   'words)
  "Optional prefix to variable names.")

(defvar tuareg-jbuild-var-regex
      (concat "\\(\\(?:!\\|" tuareg-jbuild-var-kind-regex
              ":\\)?\\)\\([a-zA-Z][a-zA-Z0-9_.]*\\|[<@^]\\)"
              "\\(\\(?::[a-zA-Z][a-zA-Z0-9_.]*\\)?\\)"))

(defvar tuareg-jbuild-font-lock-keywords
  `((,tuareg-jbuild-keywords-regex . font-lock-keyword-face)
    (,tuareg-jbuild-fields-regex . font-lock-constant-face)
    ("\\(true\\|false\\)" 1 font-lock-constant-face)
    (,(concat "(" tuareg-jbuild-actions-regex) 1 font-lock-builtin-face)
    (,(concat "${" tuareg-jbuild-var-regex "}")
     (1 font-lock-builtin-face)
     (3 font-lock-variable-name-face)
     (4 font-lock-variable-name-face))
    (,(concat "$(" tuareg-jbuild-var-regex ")")
     (1 font-lock-builtin-face)
     (3 font-lock-variable-name-face)
     (4 font-lock-variable-name-face))
    ("\\(:[a-zA-Z]+\\)\\b" 1 font-lock-builtin-face)))

(defvar tuareg-jbuild-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\; "< b" table)
    (modify-syntax-entry ?\n "> b" table)
    (modify-syntax-entry ?\( "()" table)
    (modify-syntax-entry ?\) ")(" table)
    (modify-syntax-entry ?\{ "(}" table)
    (modify-syntax-entry ?\} "){" table)
    (modify-syntax-entry ?\[ "(]" table)
    (modify-syntax-entry ?\] ")[" table)
    table)
  "Tuareg-jbuild syntax table.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                             SMIE

(require 'smie)

(defvar tuareg-jbuild-smie-grammar
  (when (fboundp 'smie-prec2->grammar)
    (smie-prec2->grammar
     (smie-bnf->prec2 '()))))

(defun tuareg-jbuild-smie-rules (kind token)
  (cond
   ((eq kind :close-all) '(column . 0))
   ((and (eq kind :after) (equal token ")"))
    (save-excursion
      (goto-char (cadr (smie-indent--parent)))
      (if (looking-at-p tuareg-jbuild-keywords-regex)
          '(column . 0)
        1)))
   ((eq kind :before)
    (if (smie-rule-parent-p "(")
        (save-excursion
          (goto-char (cadr (smie-indent--parent)))
          (cond
           ((looking-at-p tuareg-jbuild-keywords-regex) 1)
           ((looking-at-p tuareg-jbuild-fields-regex)
            (smie-rule-parent 0))
           ((smie-rule-sibling-p) (cons 'column (current-column)))
           (t (cons 'column (current-column)))))
      '(column . 0)))
   (t 1)))

(defun verbose-tuareg-jbuild-smie-rules (kind token)
  (let ((value (tuareg-jbuild-smie-rules kind token)))
    (message
     "%s '%s'; sibling-p:%s parent:%s hanging:%s = %s"
     kind token
     (ignore-errors (smie-rule-sibling-p))
     (ignore-errors smie--parent)
     (ignore-errors (smie-rule-hanging-p))
     value)
    value))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                           Linting

(require 'flymake)

(defun tuareg-jbuild-create-lint-script ()
  "Create the lint script if it does not exist.  This is nedded as long as See https://github.com/janestreet/jbuilder/issues/241 is not fixed."
  (unless (file-exists-p tuareg-jbuild-program)
    (let ((dir (file-name-directory tuareg-jbuild-program))
          (pgm "#!/usr/bin/env ocaml
;;
#load \"unix.cma\";;
#load \"str.cma\";;

open Printf

let filename = Sys.argv.(1)
let root = try Some(Sys.argv.(2)) with _ -> None

let read_all fh =
  let buf = Buffer.create 1024 in
  let b = Bytes.create 1024 in
  let len = ref 0 in
  while len := input fh b 0 1024; !len > 0 do
    Buffer.add_subbytes buf b 0 !len
  done;
  Buffer.contents buf

let errors =
  let root = match root with
    | None | Some \"\" -> \"\"
    | Some r -> \"--root=\" ^ Filename.quote r in
  let cmd = sprintf \"jbuilder external-lib-deps %s %s\" root
              (Filename.quote (Filename.basename filename)) in
  let env = Unix.environment() in
  let (_,_,fh) as p = Unix.open_process_full cmd env in
  let out = read_all fh in
  match Unix.close_process_full p with
  | Unix.WEXITED (0|1) ->
     (* jbuilder will normally exit with 1 as it will not be able to
        perform the requested action. *)
     out
  | Unix.WEXITED 127 -> printf \"jbuilder not found in path.\\n\"; exit 1
  | Unix.WEXITED n -> printf \"jbuilder exited with status %d.\\n\" n; exit 1
  | Unix.WSIGNALED n -> printf \"jbuilder was killed by signal %d.\\n\" n;
                        exit 1
  | Unix.WSTOPPED n -> printf \"jbuilder was stopped by signal %d\\n.\" n;
                       exit 1


let () =
  let re = \"\\\\(:?\\\\)[\\r\\n]+\\\\([a-zA-Z]+\\\\)\" in
  let errors = Str.global_substitute (Str.regexp re)
                 (fun s -> let colon = Str.matched_group 1 s = \":\" in
                           let f = Str.matched_group 2 s in
                           if f = \"File\" then \"\\n File\"
                           else if colon then \": \" ^ f
                           else \", \" ^ f)
                 errors in
  print_string errors"))
      (make-directory dir t)
      (append-to-file pgm nil tuareg-jbuild-program)
      (set-file-modes tuareg-jbuild-program #o777)
      )))

(defun tuareg-jbuild--temp-name (absolute-path)
  "Full path of the copy of the filename in `tuareg-jbuild-temporary-file-directory'."
  (let ((slash-pos (string-match "/" absolute-path)))
    (file-truename (expand-file-name (substring absolute-path (1+ slash-pos))
                                     tuareg-jbuild-temporary-file-directory))))

(defun tuareg-jbuild-flymake-create-temp (filename _prefix)
  ;; based on `flymake-create-temp-with-folder-structure'.
  (unless (stringp filename)
    (error "Invalid filename"))
  (tuareg-jbuild--temp-name filename))

(defun tuareg-jbuild--opam-files (dir)
  "Return all opam files in the directory DIR."
  (let ((files nil))
    (dolist (f (directory-files-and-attributes dir t ".*\\.opam\\'"))
      (when (null (cadr f))
        (push (car f) files)))
    files))

(defun tuareg-jbuild--root (filename)
  "Return the root and copy the necessary context files for jbuilder."
  ;; FIXME: the root depends on jbuild-workspace.  If none is found,
  ;; assume the commands are issued from the dir where opam files are found.
  (let* ((dir (locate-dominating-file (file-name-directory filename)
                                     #'tuareg-jbuild--opam-files)))
    (when dir
      (setq dir (expand-file-name dir)); In case it is ~/...
      (make-directory (tuareg-jbuild--temp-name dir) t)
      (dolist (f (tuareg-jbuild--opam-files dir))
        (copy-file f (tuareg-jbuild--temp-name f) t)))
    dir))

(defun tuareg-jbuild--delete-opam-files (dir)
  "Delete all opam files in the directory DIR."
  (dolist (f (tuareg-jbuild--opam-files dir))
    (flymake-safe-delete-file f)))

(defun tuareg-jbuild-flymake-cleanup ()
  "Attempt to delete temp dir created by `tuareg-jbuild-flymake-create-temp', do not fail on error."
  (let ((dir (file-name-directory flymake-temp-source-file-name))
        (temp-dir (concat (directory-file-name
                           tuareg-jbuild-temporary-file-directory) "/")))
    (flymake-log 3 "Clean up %s" flymake-temp-source-file-name)
    (flymake-safe-delete-file flymake-temp-source-file-name)
    (condition-case nil
        (delete-directory (expand-file-name "_build" dir) t)
      (error nil))
    ;; Also delete parent dirs if empty or only contain opam files
    (while (and (not (string-equal dir temp-dir))
                (> (length dir) 0))
      (condition-case nil
          (progn
            (tuareg-jbuild--delete-opam-files dir)
            (delete-directory dir)
            (setq dir (file-name-directory (directory-file-name dir))))
        (error ; then top the loop
         (setq dir ""))))))

(defun tuareg-jbuild-flymake-init ()
  (tuareg-jbuild-create-lint-script)
  (let ((fname (flymake-init-create-temp-buffer-copy
                'tuareg-jbuild-flymake-create-temp))
        (root (or (tuareg-jbuild--root buffer-file-name) "")))
    (list tuareg-jbuild-program (list fname root))))

(defvar tuareg-jbuild--allowed-file-name-masks
  '("\\(?:\\`\\|/\\)jbuild\\'" tuareg-jbuild-flymake-init
                               tuareg-jbuild-flymake-cleanup)
  "Flymake entry for jbuild files.  See `flymake-allowed-file-name-masks'.")

(defvar tuareg-jbuild--err-line-patterns
  ;; Beware that the path from the root will be reported by jbuilder
  ;; but flymake requires it to match the file name.
  '(("File \"[^\"]*\\(jbuild\\)\", line \\([0-9]+\\), \
characters \\([0-9]+\\)-\\([0-9]+\\): +\\([^\n]*\\)$"
     1 2 3 5))
  "Value of `flymake-err-line-patterns' for jbuild files.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                          Skeletons
;; See Info node "Autotype".

(define-skeleton tuareg-jbuild-insert-version-form
  "Insert the jbuild version."
  nil
  "(jbuild_version 1" _ ")" > ?\n)

(define-skeleton tuareg-jbuild-insert-library-form
  "Insert a library stanza."
  nil
  "(library" > \n
  "((name        " _ ")" > \n
  "(public_name " _ ")" > \n
  "(synopsis  \"" _ "\")" > \n
  "(libraries (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-executable-form
  "Insert an executable stanza."
  nil
  "(executable" > \n
  "((name        " _ ")" > \n
  "(public_name " _ ")" > \n
  "(modules    (" _ "))" > \n
  "(libraries  (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-executables-form
  "Insert an executables stanza."
  nil
  "(executables" > \n
  "((names        (" _ "))" > \n
  "(public_names (" _ "))" > \n
  "(libraries    (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-rule-form
  "Insert a rule stanza."
  nil
  "(rule" > \n
  "((targets (" _ "))" > \n
  "(deps    (" _ "))" > \n
  "(action  (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-ocamllex-form
  "Insert an ocamllex stanza."
  nil
  "(ocamllex (" _ "))" > ?\n)

(define-skeleton tuareg-jbuild-insert-ocamlyacc-form
  "Insert an ocamlyacc stanza."
  nil
  "(ocamlyacc (" _ "))" > ?\n)

(define-skeleton tuareg-jbuild-insert-menhir-form
  "Insert a menhir stanza."
  nil
  "(menhir" > \n
  "((modules (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-alias-form
  "Insert an alias stanza."
  nil
  "(alias" > \n
  "((name " _ ")" > \n
  "(deps (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-install-form
  "Insert an install stanza."
  nil
  "(install" > \n
  "((section " _ ")" > \n
  "(files (" _ "))))" > ?\n)

(define-skeleton tuareg-jbuild-insert-copyfiles-form
  "Insert a copy_files stanza."
  nil
  "(copy_files " _ ")" > ?\n)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar tuareg-jbuild-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c.v" 'tuareg-jbuild-insert-version-form)
    (define-key map "\C-c.l" 'tuareg-jbuild-insert-library-form)
    (define-key map "\C-c.e" 'tuareg-jbuild-insert-executable-form)
    (define-key map "\C-c.x" 'tuareg-jbuild-insert-executables-form)
    (define-key map "\C-c.r" 'tuareg-jbuild-insert-rule-form)
    (define-key map "\C-c.p" 'tuareg-jbuild-insert-ocamllex-form)
    (define-key map "\C-c.y" 'tuareg-jbuild-insert-ocamlyacc-form)
    (define-key map "\C-c.m" 'tuareg-jbuild-insert-menhir-form)
    (define-key map "\C-c.a" 'tuareg-jbuild-insert-alias-form)
    (define-key map "\C-c.i" 'tuareg-jbuild-insert-install-form)
    (define-key map "\C-c.c" 'tuareg-jbuild-insert-copyfiles-form)
    map)
  "Keymap used in Tuareg-jbuild mode.")

(defun tuareg-jbuild-build-menu ()
  (easy-menu-define
    tuareg-jbuild-mode-menu  (list tuareg-jbuild-mode-map)
    "Tuareg-jbuild mode menu."
    '("Jbuild"
      ("Stanzas"
       ["version" tuareg-jbuild-insert-version-form t]
       ["library" tuareg-jbuild-insert-library-form t]
       ["executable" tuareg-jbuild-insert-executable-form t]
       ["executables" tuareg-jbuild-insert-executables-form t]
       ["rule" tuareg-jbuild-insert-rule-form t]
       ["ocamllex" tuareg-jbuild-insert-ocamllex-form t]
       ["ocamlyacc" tuareg-jbuild-insert-ocamlyacc-form t]
       ["menhir" tuareg-jbuild-insert-menhir-form t]
       ["alias" tuareg-jbuild-insert-alias-form t]
       ["install" tuareg-jbuild-insert-install-form t]
       ["copy_files" tuareg-jbuild-insert-copyfiles-form t]
       )))
  (easy-menu-add tuareg-jbuild-mode-menu))


;;;###autoload
(define-derived-mode tuareg-jbuild-mode prog-mode "Tuareg-jbuild"
  "Major mode to edit jbuild files."
  (setq-local font-lock-defaults '(tuareg-jbuild-font-lock-keywords))
  (setq-local comment-start ";")
  (setq-local comment-end "")
  (setq indent-tabs-mode nil)
  (setq-local require-final-newline mode-require-final-newline)
  (push tuareg-jbuild--allowed-file-name-masks flymake-allowed-file-name-masks)
  (smie-setup tuareg-jbuild-smie-grammar #'tuareg-jbuild-smie-rules)
  (setq-local flymake-err-line-patterns tuareg-jbuild--err-line-patterns)
  (when (and tuareg-jbuild-flymake buffer-file-name)
    (flymake-mode t))
  (tuareg-jbuild-build-menu)
  (run-mode-hooks 'tuareg-jbuild-mode-hook))


;;;###autoload
(add-to-list 'auto-mode-alist
             '("\\(?:\\`\\|/\\)jbuild\\'" . tuareg-jbuild-mode))


(provide 'tuareg-jbuild-mode)
