;;; tuareg.el --- OCaml mode for Emacs.  -*- coding: utf-8 -*-

;; Copyright (C) 1997-2006 Albert Cohen, all rights reserved.
;; Copyright (C) 2009-2010 Jane Street Holding, LLC.
;; Licensed under the GNU General Public License.

;; Author: Albert Cohen <Albert.Cohen@inria.fr>
;;      Sam Steingold <sds@gnu.org>
;;      Christophe Troestler <Christophe.Troestler@umons.ac.be>
;;      Till Varoquaux <till@pps.jussieu.fr>
;;      Sean McLaughlin <seanmcl@gmail.com>
;;      Stefan Monnier <monnier@iro.umontreal.ca>
;; Created: 8 Jan 1997
;; Version: 2.1.0
;; Package-Requires: ((caml "3.12.0.1"))
;; Keywords: ocaml languages
;; URL: https://github.com/ocaml/tuareg
;; EmacsWiki: TuaregMode

;;; Commentary:
;; Description:
;; Tuareg helps editing OCaml code, to highlight important parts of
;; the code, to run an OCaml toplevel, and to run the OCaml debugger
;; within Emacs.

;; Installation:
;; If you have permissions to the local `site-lisp' directory, you
;; only have to copy `tuareg.el', `tuareg_indent.el', `ocamldebug.el'
;; and `tuareg-site-file.el'.  Otherwise, copy the previous files
;; to a local directory and add the following line to your `.emacs':
;;
;; (add-to-list 'load-path "DIR")


;;; Usage:
;; Tuareg allows you to run batch OCaml compilations from Emacs (using
;; M-x compile) and browse the errors (C-x `). Typing C-x ` sets the
;; point at the beginning of the erroneous program fragment, and the
;; mark at the end.  Under Emacs, the program fragment is temporarily
;; hilighted.
;;
;; M-x tuareg-run-ocaml (or simply `run-ocaml') starts an OCaml
;; toplevel with input and output in an Emacs buffer named
;; `*ocaml-toplevel*. This gives you the full power of Emacs to edit
;; the input to the OCaml toplevel. This mode is based on comint so
;; you get all the usual comint features, including command history. A
;; hook named `tuareg-interactive-mode-hook' may be used for
;; customization.
;;
;; Typing C-c C-e in a buffer in tuareg mode sends the current phrase
;; (containing the point) to the OCaml toplevel, and evaluates it.  If
;; you type one of these commands before M-x tuareg-run-ocaml, the
;; toplevel will be started automatically.
;;
;; M-x ocamldebug FILE starts the OCaml debugger ocamldebug on the
;; executable FILE, with input and output in an Emacs buffer named
;; *ocamldebug-FILE*.  It is similar to April 1996 version, with minor
;; changes to support XEmacs, Tuareg and OCaml. Furthermore, package
;; `thingatpt' is not required any more.

;; This file is *NOT* part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;;; Code:


(eval-when-compile (require 'cl))
(require 'easymenu)

(defconst tuareg-mode-revision
  (eval-when-compile
    (with-temp-buffer
      (if (file-directory-p ".git")
           (progn
             (insert "git: ")
             (call-process "git" nil t nil "log" "--pretty=%h" "-1")))
      (unless (zerop (buffer-size))
        (buffer-substring-no-properties
         (point-min) (1- (point-max))))))
  "Tuareg revision from the control system used.")

(defconst tuareg-mode-version
  (let ((version "Tuareg Version 2.1.0"))
    (if (null tuareg-mode-revision)
        version
      (concat version " (" tuareg-mode-revision ")")
      ))
  "         Copyright (C) 1997-2006 Albert Cohen, all rights reserved.
         Copyright (C) 2009-2010 Jane Street Holding, LLC.
         Copyright (C) 2011- Stefan Monnier & Christophe Troestler
         Copying is covered by the GNU General Public License.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                      Compatibility functions

(defun tuareg-editing-ls3 ()
  "Tell whether we are editing Lucid Synchrone syntax."
  (string-match "\\.ls\\'" (or buffer-file-name (buffer-name))))

(defun tuareg-editing-ocamllex ()
  "Tell whether we are editing OCamlLex syntax."
  (string-match "\\.mll\\'" (or buffer-file-name (buffer-name))))

(defalias 'tuareg-match-string
  (if (fboundp 'match-string-no-properties)
      'match-string-no-properties
    'match-string))

(or (fboundp 'read-shell-command)
    (defun read-shell-command  (prompt &optional initial-input history)
      "Read a string from the minibuffer, using `shell-command-history'."
      (read-from-minibuffer prompt initial-input nil nil
                            (or history 'shell-command-history))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                    Import types and help features

(defvar tuareg-with-caml-mode-p
  (and (require 'caml-types nil t) (require 'caml-help nil t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                       User customizable variables

(require 'smie nil 'noerror)
(defvar tuareg-use-smie (featurep 'smie)
  "Whether to use SMIE as the indentation engine.")

;; Use the standard `customize' interface or `tuareg-mode-hook' to
;; Configure these variables

(require 'custom)

(defgroup tuareg nil
  "Support for the OCaml language."
  :group 'languages)

;; Indentation defaults

(defcustom tuareg-default-indent 2
  "*Default indentation.

Global indentation variable (large values may lead to indentation overflows).
When no governing keyword is found, this value is used to indent the line
if it has to."
  :group 'tuareg :type 'integer)

(defcustom tuareg-support-camllight nil
  "*If true, handle Caml Light character syntax (incompatible with labels)."
  :group 'tuareg :type 'boolean
  :set (lambda (var val)
         (set-default var val)
         (when (boundp 'tuareg-mode-syntax-table)
           (modify-syntax-entry ?` (if val "\"" ".")
                                tuareg-mode-syntax-table))))

(defcustom tuareg-support-metaocaml nil
  "*If true, handle MetaOCaml syntax."
  :group 'tuareg :type 'boolean
  :set (lambda (var val)
         (set-default var val)
         (ignore-errors
           (tuareg-make-indentation-regexps)
           (dolist (buf (buffer-list))
             (with-current-buffer buf
               (when (derived-mode-p 'tuareg-mode 'tuareg-interactive-mode)
                 (tuareg-install-font-lock)))))))

(defcustom tuareg-in-indent 0 ; tuareg-default-indent
  "*How many spaces to indent from a `in' keyword.
Upstream <http://caml.inria.fr/resources/doc/guides/guidelines.en.html>
recommends 0, and this is what we default to since 2.0.1
instead of the historical `tuareg-default-indent'."
  :group 'tuareg :type 'integer)

(defcustom tuareg-with-indent 0
  "*How many spaces to indent from a `with' keyword.
The examples at <http://caml.inria.fr/resources/doc/guides/guidelines.en.html>
show the '|' is aligned with 'match', thus 0 is the default value."
  :group 'tuareg :type 'integer)

(defcustom tuareg-match-clause-indent 1
  "*How many spaces to indent a clause of match after a pattern `| ... ->'
or `... ->' (pattern without preceding `|' in the first clause of a matching).
To respect <http://caml.inria.fr/resources/doc/guides/guidelines.en.html>
the default is 1.")

(defcustom tuareg-match-when-indent (+ 4 tuareg-match-clause-indent)
  "*How many spaces from `|' to indent `when' in a pattern match
   | patt
        when cond ->
      clause")

;; Automatic indentation
;; Using abbrev-mode and electric keys

(defcustom tuareg-match-patterns-aligned nil
  "Non-nil means that the pipes for multiple patterns of a single case
are aligned instead of being slightly shifted to spot the multiple
patterns better.
         function          v.s.        function
         | A                           | A
           | B -> ...                  | B -> ...
         | C -> ...                    | C -> ... "
  :group 'tuareg :type 'boolean)

(defcustom tuareg-use-abbrev-mode nil
  "*Non-nil means electrically indent lines starting with leading keywords.
Leading keywords are such as `end', `done', `else' etc.
It makes use of `abbrev-mode'.

Many people find electric keywords irritating, so you can disable them by
setting this variable to nil."
  :group 'tuareg :type 'boolean
  :set (lambda (var val)
         (set-default var val)
         (dolist (buf (buffer-list))
           (with-current-buffer buf
             (when (derived-mode-p 'tuareg-mode)
               (abbrev-mode (if val 1 -1)))))))

(defcustom tuareg-electric-indent t
  "*Non-nil means electrically indent lines starting with `|', `)', `]' or `}'.

Many people find electric keys irritating, so you can disable them by
setting this variable to nil."
  :group 'tuareg :type 'boolean)
(when (fboundp 'electric-indent-mode)
  (make-obsolete-variable 'tuareg-electric-indent
                          'electric-indent-mode "Emacs-24.1"))

;; Tuareg-Interactive
;; Configure via `tuareg-mode-hook'

;; Automatic indentation

(defcustom tuareg-electric-close-vector t
  "*Non-nil means electrically insert `|' before a vector-closing `]' or
`>' before an object-closing `}'.

Many people find electric keys irritating, so you can disable them by
setting this variable to nil.  You should probably have this on,
though, if you also have `tuareg-electric-indent' on."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-interactive-scroll-to-bottom-on-output nil
  "*Controls when to scroll to the bottom of the interactive buffer
upon evaluating an expression.

See `comint-scroll-to-bottom-on-output' for details."
  :group 'tuareg :type 'boolean
  :set (lambda (var val)
         (set-default var val)
         (when (boundp 'comint-scroll-to-bottom-on-output)
           (dolist (buf (buffer-list))
             (with-current-buffer buf
               (when (derived-mode-p 'tuareg-interactive-mode)
                 (set (make-local-variable 'comint-scroll-to-bottom-on-output)
                      val)))))))

(defcustom tuareg-skip-after-eval-phrase t
  "*Non-nil means skip to the end of the phrase after evaluation in the
Caml toplevel."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-interactive-read-only-input nil
  "*Non-nil means input sent to the OCaml toplevel is read-only."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-interactive-echo-phrase t
  "*Non-nil means echo phrases in the toplevel buffer when sending
them to the OCaml toplevel."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-interactive-input-font-lock t
  "*Non nil means Font-Lock for toplevel input phrases."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-interactive-output-font-lock t
  "*Non nil means Font-Lock for toplevel output messages."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-interactive-error-font-lock t
  "*Non nil means Font-Lock for toplevel error messages."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-display-buffer-on-eval t
  "*Non nil means pop up the OCaml toplevel when evaluating code."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-manual-url
  "http://caml.inria.fr/pub/docs/manual-ocaml/"
  "*URL to the OCaml reference manual."
  :group 'tuareg :type 'string)

(defcustom tuareg-browser 'browse-url
  "*Name of function that displays the OCaml reference manual.
Valid names are `browse-url', `browse-url-firefox', etc."
  :group 'tuareg)

(defcustom tuareg-library-path "/usr/local/lib/ocaml/"
  "*Path to the OCaml library."
  :group 'tuareg :type 'string)

(defcustom tuareg-definitions-max-items 30
  "*Maximum number of items a definitions menu can contain."
  :group 'tuareg :type 'integer)

(defvar tuareg-options-list
  `(("Automatic indentation of leading keywords" . 'tuareg-use-abbrev-mode)
    ("Automatic indentation of ), ] and }" . 'tuareg-electric-indent)
    ["Prettify symbols" prettify-symbols-mode
      :style toggle :selected prettify-symbols-mode :active t]
    ,@(unless tuareg-use-smie
        '(("Automatic matching of [| and {<" . 'tuareg-electric-close-vector)))
    ,@(unless tuareg-use-smie
        '("---"
          ("Indent body of comments" . 'tuareg-indent-comments)
          ("Indent first line of comments" . 'tuareg-indent-leading-comments)
          ("Leading-`*' comment style" . 'tuareg-support-leading-star-comments)
          )))
  "*List of menu-configurable Tuareg options.")

(defvar tuareg-interactive-options-list
  '(("Skip phrase after evaluation" . 'tuareg-skip-after-eval-phrase)
    ("Echo phrase in interactive buffer" . 'tuareg-interactive-echo-phrase)
    "---"
    ("Font-lock interactive input" . 'tuareg-interactive-input-font-lock)
    ("Font-lock interactive output" . 'tuareg-interactive-output-font-lock)
    ("Font-lock interactive error" . 'tuareg-interactive-error-font-lock)
    "---"
    ("Read only input" . 'tuareg-interactive-read-only-input))
  "*List of menu-configurable Tuareg options.")

(defvar tuareg-interactive-program "ocaml"
  "*Default program name for invoking an OCaml toplevel from Emacs.")
;; Could be interesting to have this variable buffer-local
;;   (e.g., ocaml vs. metaocaml buffers)
;; (make-variable-buffer-local 'tuareg-interactive-program)

(defcustom tuareg-opam-insinuate nil
  "By default, Tuareg will use the environment that Emacs was
launched in.  That environment may not contain an OCaml
compiler (say, because Emacs was launched graphically and the
path is set in ~/.bashrc) and will remain unchanged when one
issue an \"opam switch\" in a shell.  If this variable is set to
t, Tuareg will try to use opam to set the right environment for
`compile', `run-ocaml' and `merlin-mode' based on the current
opam switch at the time the command is run (provided opam is
found).  You may also use `tuareg-opam-update-env' to set the
environment for another compiler from within emacs (without
changing the opam switch)."
  :group 'tuareg :type 'boolean)

(defgroup tuareg-faces nil
  "Special faces for the Tuareg mode."
  :group 'tuareg)

(defconst tuareg-faces-inherit-p
  (and (boundp 'face-attribute-name-alist)
       (assq :inherit face-attribute-name-alist)))

(defface tuareg-font-lock-governing-face
  '((((class color) (type tty)) (:bold t))
    (((background light)) (:foreground "black" :bold t))
    (t (:foreground "wheat" :bold t)))
  "Face description for governing/leading keywords."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-governing-face
  'tuareg-font-lock-governing-face)

(defface tuareg-font-lock-multistage-face
  '((((background light))
     (:foreground "darkblue" :background "lightgray" :bold t))
    (t (:foreground "steelblue" :background "darkgray" :bold t)))
  "Face description for MetaOCaml staging operators."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-multistage-face
  'tuareg-font-lock-multistage-face)

(defface tuareg-font-lock-line-number-face
  '((((background light)) (:foreground "dark gray"))
    (t (:foreground "gray60")))
  "Face description for line numbering directives."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-line-number-face
  'tuareg-font-lock-line-number-face)

(defface tuareg-font-lock-operator-face
  '((((background light)) (:foreground "brown"))
    (t (:foreground "khaki")))
  "Face description for all operators."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-operator-face
  'tuareg-font-lock-operator-face)

(defface tuareg-font-lock-module-face
  '((t (:inherit font-lock-type-face))); backward compatibility
  "Face description for modules and module paths."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-module-face
  'tuareg-font-lock-module-face)

(defface tuareg-font-lock-constructor-face
  '((t (:inherit default)))
  "Face description for constructors of (polymorphic) variants and exceptions."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-constructor-face
  'tuareg-font-lock-constructor-face)

(defface tuareg-font-lock-label-face
  '((t (:inherit font-lock-constant-face keep)))
  "Face description for labels."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-label-face
  'tuareg-font-lock-label-face)

(defface tuareg-font-double-colon-face
  '((t (:foreground "OrangeRed")))
  "Face description for ;; which is not needed in standard code."
  :group 'tuareg-faces)
(defvar tuareg-font-double-colon-face
  'tuareg-font-double-colon-face)

(defface tuareg-font-lock-error-face
  '((t (:foreground "yellow" :background "red" :bold t)))
  "Face description for all errors reported to the source."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-error-face
  'tuareg-font-lock-error-face)

(defface tuareg-font-lock-interactive-output-face
  '((((background light))
     (:foreground "blue4"))
    (t (:foreground "grey")))
  "Face description for all toplevel outputs."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-interactive-output-face
  'tuareg-font-lock-interactive-output-face)

(defface tuareg-font-lock-interactive-error-face
  (if tuareg-faces-inherit-p
      '((t :inherit font-lock-warning-face))
    '((((background light)) (:foreground "red3"))
      (t (:foreground "red2"))))
  "Face description for all toplevel errors."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-interactive-error-face
  'tuareg-font-lock-interactive-error-face)

(defface tuareg-font-lock-attribute-face
  (if tuareg-faces-inherit-p
      '((t :inherit font-lock-preprocessor-face))
    '((((background light)) (:foreground "DodgerBlue2"))
      (t (:foreground "LightSteelBlue"))))
  "Face description for OCaml atribute annotations."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-attribute-face
  'tuareg-font-lock-attribute-face)

(defface tuareg-font-lock-extension-node-face
  (if tuareg-faces-inherit-p
      '((t :inherit font-lock-preprocessor-face))
    '((((background light)) (:foreground "DodgerBlue2"))
      (t (:foreground "LightSteelBlue"))))
  "Face description for OCaml extension nodes."
  :group 'tuareg-faces)
(defvar tuareg-font-lock-extension-node-face
  'tuareg-font-lock-extension-node-face)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Support definitions

;; This function is different from the standard in that it does NOT signal
;; errors at beginning-of-buffer.
(defun tuareg-backward-char (&optional step)
  (if step (goto-char (- (point) step))
    (goto-char (1- (point)))))

(defun tuareg-in-indentation-p ()
  "Return non-nil if all chars between beginning of line and point are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)))

(defun tuareg-in-literal-or-comment-p ()
  "Return non-nil if point is inside an OCaml literal or comment."
  (nth 8 (syntax-ppss)))

(defun tuareg-backward-up-list ()
  ;; FIXME: not clear if moving out of a string/comment should count as 1 or no.
  (condition-case nil
      (backward-up-list)
    (scan-error (goto-char (point-min)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                           Font-lock in Emacs

;; Originally by Stefan Monnier

(defcustom tuareg-font-lock-symbols nil
  "*Display fun and -> and such using symbols in fonts.
This may sound like a neat trick, but note that it can change the
alignment and can thus lead to surprises.  On recent Emacs >= 24.4,
use `prettify-symbols-mode'."
  :group 'tuareg :type 'boolean)

(when (fboundp 'prettify-symbols-mode)
  (make-obsolete-variable 'tuareg-font-lock-symbols
                          'prettify-symbols-mode "Emacs-24.4"))

(defcustom tuareg-prettify-symbols-full nil
  "It f, add fun and -> and such to be prettified with symbols.
This may sound like a neat trick, but note that it can change the
alignment and can thus lead to surprises.  By default, only symbols that
do not perturb in essential ways the alignment are used.  See
`tuareg-prettify-symbols-basic-alist' and
`tuareg-prettify-symbols-extra-alist'."
  :group 'tuareg :type 'boolean)

(defvar tuareg-prettify-symbols-basic-alist
  (cond ((fboundp 'decode-char) ;; use a unicode font.
         `(("sqrt" . ,(decode-char 'ucs 8730))
           ("&&" . ,(decode-char 'ucs 8743)); 'LOGICAL AND' (U+2227)
           ("||" . ,(decode-char 'ucs 8744)); 'LOGICAL OR' (U+2228)
           ("+." . ,(decode-char 'ucs 8724));DOT PLUS (U+2214)
           ("-." . ,(decode-char 'ucs 8760));DOT MINUS (U+2238)
           ;;("*." . ,(decode-char 'ucs 215))
           ("*." . ,(decode-char 'ucs 8729)); BULLET OPERATOR
           ("/." . ,(decode-char 'ucs 247))
           ("<-" . ,(decode-char 'ucs 8592))
           ("<=" . ,(decode-char 'ucs 8804))
           (">=" . ,(decode-char 'ucs 8805))
           ("<>" . ,(decode-char 'ucs 8800))
           ("==" . ,(decode-char 'ucs 8801))
           ("!=" . ,(decode-char 'ucs 8802))
           ("<=>" . ,(decode-char 'ucs 8660))
           ("infinity" . ,(decode-char 'ucs 8734))
           ;; Some greek letters for type parameters.
           ("'a" . ,(decode-char 'ucs 945))
           ("'b" . ,(decode-char 'ucs 946))
           ("'c" . ,(decode-char 'ucs 947))
           ("'d" . ,(decode-char 'ucs 948))
           ("'e" . ,(decode-char 'ucs 949))
           ("'f" . ,(decode-char 'ucs 966))
           ("'i" . ,(decode-char 'ucs 953))
           ("'k" . ,(decode-char 'ucs 954))
           ("'m" . ,(decode-char 'ucs 956))
           ("'n" . ,(decode-char 'ucs 957))
           ("'o" . ,(decode-char 'ucs 969))
           ("'p" . ,(decode-char 'ucs 960))
           ("'r" . ,(decode-char 'ucs 961))
           ("'s" . ,(decode-char 'ucs 963))
           ("'t" . ,(decode-char 'ucs 964))
           ("'x" . ,(decode-char 'ucs 958))))
        ((and (fboundp 'make-char) (fboundp 'charsetp) (charsetp 'symbol))
         `(("sqrt" . ,(make-char 'symbol 214))
           ("&&" . ,(make-char 'symbol 217))
           ("||" . ,(make-char 'symbol 218))
           ("*." . ,(make-char 'symbol 183))
           ("/." . ,(make-char 'symbol 184))
           ("<=" . ,(make-char 'symbol 163))
           ("<-" . ,(make-char 'symbol 172))
           (">=" . ,(make-char 'symbol 179))
           ("<>" . ,(make-char 'symbol 185))
           ("==" . ,(make-char 'symbol 186))
           ("<=>" . ,(make-char 'symbol 219))
           ("=>" . ,(make-char 'symbol 222))
           ("infinity" . ,(make-char 'symbol 165))
           ;; Some greek letters for type parameters.
           ("'a" . ,(make-char 'symbol 97))
           ("'b" . ,(make-char 'symbol 98))
           ("'c" . ,(make-char 'symbol 103)) ; sic! 99 is chi, 103 is gamma
           ("'d" . ,(make-char 'symbol 100))
           ("'e" . ,(make-char 'symbol 101))
           ("'f" . ,(make-char 'symbol 102))
           ("'i" . ,(make-char 'symbol 105))
           ("'k" . ,(make-char 'symbol 107))
           ("'m" . ,(make-char 'symbol 109))
           ("'n" . ,(make-char 'symbol 110))
           ("'o" . ,(make-char 'symbol 111))
           ("'p" . ,(make-char 'symbol 112))
           ("'r" . ,(make-char 'symbol 114))
           ("'s" . ,(make-char 'symbol 115))
           ("'t" . ,(make-char 'symbol 116))
           ("'x" . ,(make-char 'symbol 120))))))

(defvar tuareg-prettify-symbols-extra-alist
  (cond ((fboundp 'decode-char) ;; use a unicode font.
         `(("fun" . ,(decode-char 'ucs 955))
           ("not" . ,(decode-char 'ucs 172))
           ;;("or" . ,(decode-char 'ucs 8744)); should not be used as ||
           ("[|" . ,(decode-char 'ucs 12314)) ;; 〚
           ("|]" . ,(decode-char 'ucs 12315)) ;; 〛
           ("->" . ,(decode-char 'ucs 8594))
           (":=" . ,(decode-char 'ucs 8656))))
         ((and (fboundp 'make-char) (fboundp 'charsetp) (charsetp 'symbol))
          `(("fun" . ,(make-char 'symbol 108))
            ("not" . ,(make-char 'symbol 216))
            ;;("or" . ,(make-char 'symbol 218))
            ("->" . ,(make-char 'symbol 174))
            (":=" . ,(make-char 'symbol 220))))))


(defun tuareg-font-lock-compose-symbol (alist)
  "Compose a sequence of ascii chars into a symbol.
Regexp match data 0 points to the chars."
  ;; Check that the chars should really be composed into a symbol.
  (let* ((mbegin (match-beginning 0))
         (mend (match-end 0))
         (syntax (char-syntax (char-after mbegin))))
    (if (or (eq (char-syntax (or (char-before mbegin) ?\ )) syntax)
            (eq (char-syntax (or (char-after mend) ?\ )) syntax)
            (memq (get-text-property mbegin 'face)
                  '(tuareg-doc-face font-lock-string-face
                    font-lock-comment-face)))
        ;; No composition for you. Let's actually remove any composition
        ;;   we may have added earlier and which is now incorrect.
        (remove-text-properties mbegin mend '(composition))
      ;; That's a symbol alright, so add the composition.
      (compose-region mbegin mend (cdr (assoc (match-string 0) alist)))))
  ;; Return nil because we're not adding any face property.
  nil)

(defun tuareg-font-lock-symbols-keywords ()
  (when (fboundp 'compose-region)
    (let ((alist (if tuareg-prettify-symbols-full
                     (append tuareg-prettify-symbols-basic-alist
                             tuareg-prettify-symbols-extra-alist)
                   tuareg-prettify-symbols-basic-alist)))
      (dolist (x alist)
        (when (and (if (fboundp 'char-displayable-p)
                       (char-displayable-p (cdr x))
                     t)
                   (not (assoc (car x) alist))) ; not yet in alist.
          (push x alist)))
      (when alist
        `((,(regexp-opt (mapcar 'car alist) t)
           (0 (tuareg-font-lock-compose-symbol ',alist))))))))

(defvar tuareg-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?. "'" st)     ;Make qualified names a single symbol.
    (modify-syntax-entry ?# "_" st)     ;Make name#method a single symbol
    (modify-syntax-entry ?? ". p" st)
    (modify-syntax-entry ?~ ". p" st)
    ;; See http://caml.inria.fr/pub/docs/manual-ocaml/lex.html.
    (dolist (c '(?! ?$ ?% ?& ?+ ?- ?/ ?: ?< ?= ?> ?@ ?^ ?|))
      (modify-syntax-entry c "." st))
    (modify-syntax-entry ?' "_" st) ; ' is part of symbols (for primes).
    (modify-syntax-entry
     ;; ` is punctuation or character delimiter (Caml Light compatibility).
     ?` (if tuareg-support-camllight "\"" ".") st)
    (modify-syntax-entry ?\" "\"" st) ; " is a string delimiter
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?*  ". 23" st)
    (condition-case nil
        (progn
          (modify-syntax-entry ?\( "()1n" st)
          (modify-syntax-entry ?\) ")(4n" st))
      (error               ;XEmacs signals an error instead of ignoring `n'.
       (modify-syntax-entry ?\( "()1" st)
       (modify-syntax-entry ?\) ")(4" st)))
    st)
  "Syntax table in use in Tuareg mode buffers.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  Font-Lock

(defvar tuareg-doc-face 'font-lock-doc-face)

(defconst tuareg-font-lock-syntactic-keywords
  ;; Char constants start with ' but ' can also appear in identifiers.
  ;; Beware not to match things like '*)hel' or '"hel' since the first '
  ;; might be inside a string or comment.
  ;; Note: for compatibility with Emacs<23, we use "\\<" rather than "\\_<",
  ;; which depends on tuareg-font-lock-syntax turning all "_" into "w".
  '(("\\<\\('\\)\\([^'\\\n]\\|\\\\.[^\\'\n \")]*\\)\\('\\)"
     (1 '(7)) (3 '(7)))))

(defvar syntax-propertize-function)

(when (eval-when-compile (fboundp 'syntax-propertize-rules))
  (defun tuareg-syntax-propertize (start end)
    (goto-char start)
    (tuareg--syntax-quotation end)
    (funcall
     (syntax-propertize-rules
      ;; When we see a '"', knowing whether it's a literal char (as opposed to
      ;; the end of a string followed by the beginning of a literal char)
      ;; requires checking syntax-ppss as in:
      ;; ("\\_<\\('\"'\\)"
      ;;  (1 (unless (nth 3 (save-excursion (syntax-ppss (match-beginning 0))))
      ;;       (string-to-syntax "\""))))
      ;; Not sure if it's worth the trouble since adding a space between the
      ;; string and the literal char is easy enough and is the usual
      ;; style anyway.
      ;; For all other cases we don't need to check syntax-ppss because, if the
      ;; first quote is within a string (or comment), the whole match is within
      ;; the string (or comment), so the syntax-properties don't hurt.
      ;;
      ;; Note: we can't just use "\\<" here because syntax-propertize is also
      ;; used outside of font-lock.
      ("\\_<\\('\\)\\(?:[^'\\\n]\\|\\\\.[^\\'\n \")]*\\)\\('\\)"
       (1 "\"") (2 "\""))
      ("\\(<\\)\\(?:<\\S.\\|:[[:alpha:]]+<\\)"
       (1 (prog1 "|" (tuareg--syntax-quotation end))))
      ("\\({\\)[a-z_]*|"
       (1 (prog1 "|" (tuareg--syntax-quotation end))))
      )
     (point) end)))

(defun tuareg--syntax-quotation (end)
  (let ((ppss (syntax-ppss)))
    (when (eq t (nth 3 ppss))
      (ecase (char-after (nth 8 ppss))
        (?<
         ;; We're indeed inside a quotation.
         (when (re-search-forward ">>" end 'move)
           (put-text-property (1- (point)) (point)
                              'syntax-table (string-to-syntax "|"))))
        (?\{
         ;; We're inside a quoted string
         ;; http://caml.inria.fr/pub/docs/manual-ocaml/extn.html#sec244
         (let ((id (save-excursion
                     (goto-char (1+ (nth 8 ppss)))
                     (buffer-substring (point)
                                       (progn (skip-chars-forward "a-z_")
                                              (point))))))
	   (when (search-forward (concat "|" id "}") end 'move)
             (put-text-property (1- (point)) (point)
                                'syntax-table (string-to-syntax "|")))))))))

(defun tuareg-font-lock-syntactic-face-function (state)
  (if (nth 3 state)
      (if (and (eq t (nth 3 state)) (eq ?< (char-after (nth 8 state))))
          font-lock-preprocessor-face font-lock-string-face)
    (let ((start (nth 8 state)))
      (if (and (> (point-max) (+ start 2))
               (eq (char-after (+ start 2)) ?*)
               (not (eq (char-after (+ start 3)) ?*)))
          ;; This is a documentation comment
          tuareg-doc-face
        font-lock-comment-face))))

;; Initially empty, set in `tuareg-install-font-lock'
(defvar tuareg-font-lock-keywords ()
  "Font-Lock patterns for Tuareg mode.")

(defconst tuareg-font-lock-syntax
  ;; Note: as a general rule, changing syntax-table during font-lock
  ;; is a potential problem for syntax-ppss.
  `((?_ . "w") (?' . "w"))
  "Syntax changes for Font-Lock.")

(defconst tuareg--whitespace-re
  ;; QUESTION: Why not just "[ \t\n]*"?
  ;; It used to be " *[\t\n]? *" but this is inefficient since it can match
  ;; N spaces in N+1 different ways :-(
  " *\\(?:[\t\n] *\\)?")

(defun tuareg-install-font-lock ()
  (let* ((id "\\<[A-Za-z_][A-Za-z0-9_']*\\>")
         (lid "\\<[a-z_][A-Za-z0-9_']*\\>")
         (uid "\\<[A-Z][A-Za-z0-9_']*\\>")
	 (attr-id1 "\\<[A-Za-z_][A-Za-z0-9_']*\\>")
	 (attr-id (concat attr-id1 "\\(?:\\." attr-id1 "\\)*"))
	 (maybe-infix-attr (concat "\\(?:%" attr-id "\\)?")); at most 1
         ;; Matches braces balanced on max 3 levels.
         (balanced-braces
          (let ((b "\\(?:[^()]\\|(")
                (e ")\\)*"))
            (concat b b b "[^()]*" e e e)))
         (balanced-braces-no-string
          (let ((b "\\(?:[^()\"]\\|(")
                (e ")\\)*"))
            (concat b b b "[^()\"]*" e e e)))
         (balanced-braces-no-end-colon ; non-empty
          (let ((b "\\(?:[^()]\\|(")
                (e ")\\)*"))
            (concat "\\(?:[^():]\\|:+\\(?:[^:()]\\|(" b b "[^()]*" e e ")\\)"
                    "\\|(" b b "[^()]*" e e e)))
	 (balanced-brackets
          (let ((b "\\(?:[^][]\\|\\[")
                (e "\\]\\)*"))
            (concat b b b "[^][]*" e e e)))
	 (maybe-infix-ext
	  (concat "\\(?:\\[@" attr-id balanced-brackets "\\]\\)*"))
	 (maybe-infix-attr+ext
	  (concat maybe-infix-attr maybe-infix-ext))
         (tuple (concat "(" balanced-braces ")")); much more than tuple!
	 ;; FIXME: module paths with functor applications
         (module-path (concat uid "\\(?:\\." uid "\\)*"))
         (typeconstr (concat "\\(?:" module-path "\\.\\)?" lid))
         (constructor (concat "\\(?:\\(?:" module-path "\\.\\)?" uid
                              "\\|`" id "\\)"))
         (extended-module-name
          (concat uid "\\(?: *([ A-Z]" balanced-braces ")\\)*"))
         (extended-module-path
          (concat extended-module-name
                  "\\(?: *\\. *" extended-module-name "\\)*"))
         (modtype-path (concat "\\(?:" extended-module-path "\\.\\)*" id))
         (typevar "'[A-Za-z_][A-Za-z0-9_']*\\>")
         (typeparam (concat "[+-]?" typevar))
         (typeparams (concat "\\(?:" typeparam "\\|( *"
                             typeparam " *\\(?:, *" typeparam " *\\)*)\\)"))
         (typedef (concat "\\(?:" typeparams " *\\)?" lid))
         ;; Define 2 groups: possible path, variables
         (let-ls3 (regexp-opt '("clock" "node" "static"
                                "present" "automaton" "where" "match"
                                "with" "do" "done" "unless" "until"
                                "reset" "every")))
         (let-binding (concat "\\<\\(?:let" maybe-infix-attr+ext
			      "\\(?: +" (if (tuareg-editing-ls3) let-ls3 "rec")
			       "\\)?\\|and\\) +"))
         ;; group of variables
         (gvars (concat "\\(\\(?:" tuareg--whitespace-re
                        "\\(?:" lid "\\|()\\|" tuple ; = any balanced (...)
                        "\\|[~?]\\(?:" lid
                        "\\(?::\\(?:" lid "\\|(" balanced-braces ")\\)\\)?"
                        "\\|(" balanced-braces ")\\)"
                        "\\)\\)+\\)"))
         ;; group for possible class param
         (class-gparams
          (concat "\\<class\\>\\(?: +type\\>\\)?\\(?: +virtual\\>\\)?"
                  "\\( *\\[ *" typevar " *\\(?:, *" typevar " *\\)*\\]\\)?")))
  (setq
   tuareg-font-lock-keywords
   `(("^#[0-9]+ *\\(?:\"[^\"]+\"\\)?" 0 tuareg-font-lock-line-number-face t)
     (";;+" 0 tuareg-font-double-colon-face)
     ;; Attributes (`keep' to highlight except strings & chars)
     (,(concat "\\[@\\(?:@@?\\)?" attr-id balanced-brackets "\\]")
      0 tuareg-font-lock-attribute-face keep)
     ;; Extension nodes
     (,(concat "\\[%%?" attr-id balanced-brackets "\\]")
      0 tuareg-font-lock-extension-node-face keep)
     (,(concat "\\(?:\\<" (regexp-opt '("let" "begin" "module" "val" "val!"
					"fun" "function" "match"))
	       "\\|;\\)\\(" maybe-infix-attr "\\)")
      1 tuareg-font-lock-extension-node-face)
     ;; cppo
     (,(concat "^ *#" (regexp-opt '("define" "undef" "if" "ifdef" "ifndef"
				    "else" "elif" "endif" "include"
				    "warning" "error" "ext" "endext")
				  'words))
      . font-lock-preprocessor-face)
     ("\\<\\(false\\|true\\)\\>" . font-lock-constant-face)
     (,(regexp-opt '("true" "false" "__LOC__" "__FILE__" "__LINE__"
                     "__MODULE__" "__POS__" "__LOC_OF__" "__LINE_OF__"
                     "__POS_OF__") 'words)
      . font-lock-constant-face)
     ;; "type" to introduce a local abstract type considered a keyword
     (,(concat "( *\\(type\\) +\\(" lid "\\) *)")
      (1 font-lock-keyword-face)
      (2 font-lock-type-face))
     ;; First class modules.  In these contexts, "val" and "module"
     ;; are not considered as "governing" (main structure of the code).
     (,(concat "( *\\(module\\) +\\(" module-path "\\) *: +\\("
	       balanced-braces-no-string "\\))")
      (1 font-lock-keyword-face)
      (2 tuareg-font-lock-module-face)
      (3 tuareg-font-lock-module-face))
     (,(concat "( *\\(val\\) +\\(" balanced-braces-no-end-colon "\\) *: +\\("
	       balanced-braces-no-string "\\))")
      (1 font-lock-keyword-face)
      (2 tuareg-font-lock-module-face)
      (3 tuareg-font-lock-module-face))
     ("let +exception" . tuareg-font-lock-governing-face)
     (,(regexp-opt '("module" "include" "sig" "struct" "functor"
                     "type" "constraint" "class" "in" "inherit"
                     "method" "external" "val" "open"
                     "initializer" "let" "rec" "object" "and" "begin" "end")
                   'words)
      . tuareg-font-lock-governing-face)
     ,@(if (tuareg-editing-ls3)
           `((,(concat "\\<\\(let[ \t]+" let-ls3 "\\)\\>")
              . tuareg-font-lock-governing-face)))
     (,(let ((kwd '("as" "do" "done" "downto" "else" "for" "if"
                    "then" "to" "try" "when" "while" "match" "new"
                    "lazy" "assert" "fun" "function" "exception")))
         (if (tuareg-editing-ls3)
             (progn (push "reset" kwd)  (push "merge" kwd)
                    (push "emit" kwd)  (push "period" kwd)))
         (regexp-opt kwd 'words))
      . font-lock-keyword-face)
     ;; with type: "with" treated as a governing keyword
     (,(concat "\\<\\(\\(?:with\\|and\\) +type\\>\\) *\\(" typeconstr "\\)?")
      (1 tuareg-font-lock-governing-face keep)
      (2 font-lock-type-face keep t))
     (,(concat "\\<\\(\\(?:with\\|and\\) +module\\>\\) *\\(?:\\(" module-path
               "\\) *\\)?\\(?:= *\\(" extended-module-path "\\)\\)?")
      (1 tuareg-font-lock-governing-face keep)
      (2 tuareg-font-lock-module-face keep t)
      (3 tuareg-font-lock-module-face keep t))
     ;; "module type of" module-expr (here "of" is a governing keyword)
     ("\\<module +type +of\\>"
      0 tuareg-font-lock-governing-face keep)
     (,(concat "\\<module +type +of +\\(" module-path "\\)?")
      1 tuareg-font-lock-module-face keep t)
     ;; "!", "mutable", "virtual" treated as governing keywords
     (,(concat "\\<\\(\\(?:val" maybe-infix-attr+ext
	       (if (tuareg-editing-ls3) "\\|reset\\|do")
               "\\)!? +\\(?:mutable\\(?: +virtual\\)?\\>"
               "\\|virtual\\(?: +mutable\\)?\\>\\)\\|val!"
	       maybe-infix-attr+ext "\\)\\( *" lid "\\)?")
      (1 tuareg-font-lock-governing-face keep)
      (2 font-lock-variable-name-face nil t))
     ("\\<class\\>\\(?: +type\\>\\)?\\( +virtual\\>\\)?"
      1 tuareg-font-lock-governing-face nil t)
     ;; "private" treated as governing keyword
     (,(concat "\\<method!?\\(?: +\\(private\\(?: +virtual\\)?"
               "\\|virtual\\(?: +private\\)?\\)\\>\\)?")
      1 tuareg-font-lock-governing-face keep t)
     ;; Other uses of "with", "mutable", "private", "virtual"
     (,(regexp-opt '("of" "with" "mutable" "private" "virtual") 'words)
      . font-lock-keyword-face)
     ;;; labels
     (,(concat "\\([?~]" lid "\\)" tuareg--whitespace-re ":[^:>=]")
      1 tuareg-font-lock-label-face keep)
     ;;; label in a type signature
     (,(concat "\\(?:->\\|:[^:>=]\\)" tuareg--whitespace-re
               "\\(" lid "\\)[ \t]*:[^:>=]")
      1 tuareg-font-lock-label-face keep)
     (,(concat "\\<open\\(! +\\|\\> *\\)\\(" module-path "\\)?")
      (1 tuareg-font-lock-governing-face)
      (2 tuareg-font-lock-module-face keep t))
     (,(regexp-opt '("failwith" "failwithf" "exit" "at_exit" "invalid_arg"
                     "parser" "raise" "ref" "ignore"
		     "Match_failure" "Assert_failure" "Invalid_argument"
		     "Failure" "Not_found" "Out_of_memory" "Stack_overflow"
		     "Sys_error" "End_of_file" "Division_by_zero"
		     "Sys_blocked_io" "Undefined_recursive_module") 'words)
      . font-lock-builtin-face)
     ;; module paths A.B.
     (,(concat module-path "\\.") . tuareg-font-lock-module-face)
     (,(concat
         "[][;,()|{}]\\|[-@^!:*=<>&/%+~?#]\\.?\\|\\.\\.\\.*\\|"
         (regexp-opt
          (if (tuareg-editing-ls3)
              '("asr" "asl" "lsr" "lsl" "or" "lor" "and" "land" "lxor"
                "not" "lnot" "mod" "fby" "pre" "last" "at")
            '("asr" "asl" "lsr" "lsl" "or" "lor" "land"
              "lxor" "not" "lnot" "mod"))
          'words))
      . tuareg-font-lock-operator-face)
     ;;; (expr: t) and (expr :> t)
     ;;; If `t' is longer then one word, require a space before.  Not only
     ;;; this is more readable but it also avoids that `~label:expr var`
     ;;; is taken as a type annotation when surrounded by parentheses.
     (,(concat "(" balanced-braces-no-end-colon ":>?\\(['_A-Za-z]+"
               "\\| [ \n'_A-Za-z]" balanced-braces-no-string "\\))")
      1 font-lock-type-face keep)
     ;; (lid: t)
     (,(concat "(" lid " *:\\(['_A-Za-z]" balanced-braces-no-string "\\))")
      1 font-lock-type-face keep)
     (,(concat "\\<external +\\(" lid "\\)")  1 font-lock-function-name-face)
     (,(concat "\\<exception +\\(" uid "\\)") 1 font-lock-variable-name-face)
     (,(concat "\\<module" maybe-infix-attr+ext
	       "\\(?: +type\\)?\\(?: +rec\\)?\\> *\\(" uid "\\)")
      1 tuareg-font-lock-module-face)
     ;; (M: S) -- only color S here (may be "A.T with type t = s")
     (,(concat "( *" uid " *: *\\("
               modtype-path "\\(?: *\\<with\\>" balanced-braces "\\)?\\) *)")
      1 tuareg-font-lock-module-face keep)
     (,(concat "\\<include +\\(" extended-module-path "\\|( *"
               extended-module-path " *: *" balanced-braces " *)\\)")
      1 tuareg-font-lock-module-face keep)
     ;; module type A = B
     (,(concat "\\<module +type +" id " *= *\\(" modtype-path "\\)")
      1 tuareg-font-lock-module-face keep)
     ;; module A(B: _)(C: _) : D = E, including "module A : E"
     (,(concat "\\<module +" uid tuareg--whitespace-re
               "\\(\\(?:( *" uid " *: *"
               modtype-path "\\(?: *\\<with\\>" balanced-braces "\\)?"
               " *)" tuareg--whitespace-re "\\)*\\)\\(?::"
               tuareg--whitespace-re "\\(" modtype-path
               "\\) *\\)?\\(?:=" tuareg--whitespace-re
               "\\(" extended-module-path "\\)\\)?")
      (1 font-lock-variable-name-face keep); functor (module) variable
      (2 tuareg-font-lock-module-face keep t)
      (3 tuareg-font-lock-module-face keep t))
     (,(concat "\\<functor\\> *( *\\(" uid "\\) *: *\\(" modtype-path "\\) *)")
      (1 font-lock-variable-name-face keep); functor (module) variable
      (2 tuareg-font-lock-module-face keep))
     ;;; "type lid" anywhere (e.g. "let f (type t) x =") introduces a new type
     (,(concat "\\<type\\>" tuareg--whitespace-re "\\(" typedef "\\)")
      1 font-lock-type-face keep)
     ;; Constructors
     (,(concat "`" id) . tuareg-font-lock-constructor-face)
     (,(concat "\\(" uid "\\)[^.]")  1 tuareg-font-lock-constructor-face)
     ;;; let-bindings
     (,(concat let-binding "\\(" lid "\\) *\\(?:: *\\([^=]+\\)\\)?= *"
               "fun\\(?:ction\\)?\\>")
      (1 font-lock-function-name-face nil t)
      (2 font-lock-type-face keep t))
     (,(let* ((maybe-constr (concat "\\(?:" constructor " *\\)?"))
              (var (concat maybe-constr "\\(?:" lid "\\|" tuple "\\)"))
              (simple-patt (concat var "\\(?: *, *" var "\\)*")))
         (concat let-binding "\\(" simple-patt
                 "\\) *\\(?:: *\\([^=]+\\)\\)?="))
      ;; module paths, types, constructors already colored by the above
      (1 font-lock-variable-name-face keep)
      (2 font-lock-type-face keep t))
     (,(concat let-binding "\\(" lid "\\)" gvars "?\\(?: +:"
               tuareg--whitespace-re "\\([a-z_]\\|[^ =][^=]*[^ =]\\) *=\\)?")
      (1 font-lock-function-name-face nil t)
      (2 font-lock-variable-name-face keep t)
      (3 font-lock-type-face keep t))
     (,(concat "\\<function\\>" maybe-infix-attr+ext
	       tuareg--whitespace-re "\\(" lid "\\)")
      1 font-lock-variable-name-face)
     (,(concat "\\<fun" maybe-infix-attr+ext " +" gvars " *->")
      1 font-lock-variable-name-face keep nil)
     (,(concat class-gparams " *\\(" lid "\\)")
      (1 font-lock-type-face keep t)
      (2 font-lock-function-name-face))
     (,(concat class-gparams " *" lid gvars "? *=")
      2 font-lock-variable-name-face keep t)
     ;; "method": long match first to capture the method name
     (,(concat "\\<method!? +\\(?:private +\\(?:virtual +\\)?"
               "\\|virtual +\\(?:private +\\)?\\)\\(" lid "\\)")
      1 font-lock-function-name-face keep t); method name
     (,(concat "\\<method!? +\\(" lid "\\)" gvars "?")
      (1 font-lock-function-name-face keep t); method name
      (2 font-lock-variable-name-face keep t))
     (,(concat "\\<object *(\\(" lid "\\) *\\(?:: *\\("
               balanced-braces "\\)\\)?)")
      (1 font-lock-variable-name-face)
      (2 font-lock-type-face keep t))
     (,(concat "\\<object *( *\\(" typevar "\\|_\\) *)")
      1 font-lock-type-face)
     ;; "val" without "!", "mutable" or "virtual"
     (,(concat "\\<val" maybe-infix-attr+ext
	       " +\\(" lid "\\)")
      1 font-lock-function-name-face)
     (,(concat "\\<\\("
               (regexp-opt '("DEFINE" "IFDEF" "IFNDEF" "THEN" "ELSE" "ENDIF"
                             "INCLUDE" "__LOCATION__"))
               "\\)\\>")
      . font-lock-preprocessor-face)
     ,@(and tuareg-support-metaocaml
            '(("\\.<\\|>\\.\\|\\.~\\|\\.!"
               0 tuareg-font-lock-multistage-face nil nil)))
     ,@(and tuareg-font-lock-symbols
            (tuareg-font-lock-symbols-keywords)))))
  (setq font-lock-defaults
        `(tuareg-font-lock-keywords
          nil nil
          ,tuareg-font-lock-syntax nil
          ,@(unless (fboundp 'tuareg-syntax-propertize)
              '((font-lock-syntactic-keywords
                 . tuareg-font-lock-syntactic-keywords)
                (parse-sexp-lookup-properties . t)))
          (font-lock-syntactic-face-function
           . tuareg-font-lock-syntactic-face-function)))
  ;; (if tuareg-use-smie
  ;;     (push 'smie-backward-sexp-command font-lock-extend-region-functions))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                    Keymap

(defvar tuareg-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "|" 'tuareg-electric-pipe)
    (define-key map ")" 'tuareg-electric-rp)
    (define-key map "}" 'tuareg-electric-rc)
    (define-key map "]" 'tuareg-electric-rb)
    (define-key map "\M-q" 'tuareg-indent-phrase)
    (define-key map "\C-c\C-q" 'tuareg-indent-phrase)
    ;; Don't bother: it's the global default anyway.
    ;;(define-key map "\M-\C-\\" 'indent-region)
    (define-key map "\C-c\C-a" 'tuareg-find-alternate-file)
    (define-key map "\C-c\C-c" 'compile)
    (define-key map "\C-c\C-w" 'tuareg-opam-update-env)
    (define-key map "\C-xnd" 'tuareg-narrow-to-phrase)
    (define-key map "\M-\C-x" 'tuareg-eval-phrase)
    (define-key map [remap newline-and-indent] 'tuareg-newline-and-indent)
    (define-key map "\C-x\C-e" 'tuareg-eval-phrase)
    (define-key map "\C-c\C-e" 'tuareg-eval-phrase)
    (define-key map "\C-c\C-r" 'tuareg-eval-region)
    (define-key map "\C-c\C-b" 'tuareg-eval-buffer)
    (define-key map "\C-c\C-s" 'tuareg-run-ocaml)
    (define-key map "\C-c\C-i" 'tuareg-interrupt-ocaml)
    (define-key map "\C-c\C-k" 'tuareg-kill-ocaml)
    (define-key map "\C-c\C-n" 'tuareg-next-phrase)
    (define-key map "\C-c\C-p" 'tuareg-previous-phrase)
    (define-key map [(backspace)] 'backward-delete-char-untabify)
    (define-key map [(control c) (home)]
      'tuareg-move-inside-module-or-class-opening)
    (unless tuareg-use-smie
      (define-key map [(control c) (control down)] 'tuareg-next-phrase)
      (define-key map [(control c) (control up)] 'tuareg-previous-phrase)
      (define-key map [(meta control down)]  'tuareg-next-phrase)
      (define-key map [(meta control up)] 'tuareg-previous-phrase)
      (define-key map [(meta control n)]  'tuareg-next-phrase)
      (define-key map [(meta control p)] 'tuareg-previous-phrase)
      )
    (define-key map [(meta control h)] 'tuareg-mark-phrase)
    (define-key map "\C-c`" 'tuareg-interactive-next-error-source)
    (define-key map "\C-c?" 'tuareg-interactive-next-error-source)
    (define-key map "\C-c.c" 'tuareg-insert-class-form)
    (define-key map "\C-c.b" 'tuareg-insert-begin-form)
    (define-key map "\C-c.f" 'tuareg-insert-for-form)
    (define-key map "\C-c.w" 'tuareg-insert-while-form)
    (define-key map "\C-c.i" 'tuareg-insert-if-form)
    (define-key map "\C-c.l" 'tuareg-insert-let-form)
    (define-key map "\C-c.m" 'tuareg-insert-match-form)
    (define-key map "\C-c.t" 'tuareg-insert-try-form)
    (when tuareg-with-caml-mode-p
      ;; Trigger caml-types
      (define-key map [?\C-c ?\C-t] 'caml-types-show-type)  ; "type"
      (define-key map [?\C-c ?\C-f] 'caml-types-show-call)  ; "function"
      (define-key map [?\C-c ?\C-l] 'caml-types-show-ident) ; "let"
      ;; To prevent misbehavior in case of error during exploration.
      (define-key map [?\C-c mouse-1] 'caml-types-mouse-ignore)
      (define-key map [?\C-c down-mouse-1] 'caml-types-explore)
      ;; Trigger caml-help
      (define-key map [?\C-c ?\C-i] 'ocaml-add-path)
      (define-key map [?\C-c ?\[] 'ocaml-open-module)
      (define-key map [?\C-c ?\]] 'ocaml-close-module)
      (define-key map [?\C-c ?\C-h] 'caml-help)
      (define-key map [?\C-c ?\t] 'tuareg-complete))
    map)
  "Keymap used in Tuareg mode.")

(defvar tuareg-electric-indent-keywords
  '("module" "class" "functor" "object" "type" "val" "inherit"
    "include" "virtual" "constraint" "exception" "external" "open"
    "method" "and" "initializer" "to" "downto" "do" "done" "else"
    "begin" "end" "let" "in" "then" "with"))

(defvar tuareg-mode-abbrev-table ()
  "Abbrev table used for Tuareg mode buffers.")

(if tuareg-mode-abbrev-table ()
  (define-abbrev-table 'tuareg-mode-abbrev-table
    (mapcar (lambda (keyword)
              `(,keyword ,keyword tuareg-abbrev-hook nil t))
            tuareg-electric-indent-keywords)))

(defun tuareg--electric-indent-predicate (char)
  "Check whether we should auto-indent.
For use on `electric-indent-functions'."
  (save-excursion
    (forward-char -1) ;; Go before the inserted char.
    (let ((syntax (char-syntax char)))
      (if (tuareg-in-indentation-p)
          (or (eq char ?|) (eq syntax ?\)))
        (or (case char
              (?\) (char-equal ?* (preceding-char)))
              (?\} (and (char-equal ?> (preceding-char))
                        (progn (tuareg-backward-char)
                               (tuareg-in-indentation-p))))
              (?\] (and (char-equal ?| (preceding-char))
                        (progn (tuareg-backward-char)
                               (tuareg-in-indentation-p)))))
            (and tuareg-use-abbrev-mode  ;; Misnomer, eh?
                 (not (eq syntax ?w))
                 (let ((end (point)))
                   (skip-syntax-backward "w_")
                   (member (buffer-substring (point) end)
                           tuareg-electric-indent-keywords))
                                           (tuareg-in-indentation-p)))))))

(defun tuareg--electric-close-vector ()
  ;; Function for use on post-self-insert-hook.
  (when tuareg-electric-close-vector
    (let ((inners (cdr (assq last-command-event
                             '((?\} ?> "{<") (?\] ?| "\\[|"))))))
      (and inners
           (eq (char-before) last-command-event) ;; Sanity check.
           (not (eq (car inners) (char-before (1- (point)))))
           (not (tuareg-in-literal-or-comment-p))
           (save-excursion
             (when (ignore-errors (backward-sexp 1) t)
               (looking-at (nth 1 inners))))
           (save-excursion
             (goto-char (1- (point)))
             (insert (car inners)))))))

(defun tuareg-electric-pipe ()
  "If inserting a | operator at beginning of line, reindent the line."
  (interactive "*")
  (let ((electric (and tuareg-electric-indent
                       (not (and (boundp 'electric-indent-mode)
                                 electric-indent-mode))
                       (tuareg-in-indentation-p)
                       (not (tuareg-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (and electric
         (not (and (char-equal ?| (preceding-char))
                   (fboundp 'tuareg-find-pipe-match)
                   (fboundp 'tuareg-give-match-pipe-kwop-regexp)
                   (save-excursion
                     (tuareg-backward-char)
                     (tuareg-find-pipe-match)
                     (not (looking-at (tuareg-give-match-pipe-kwop-regexp))))))
         (indent-according-to-mode))))

(defun tuareg-electric-rp ()
  "If inserting a ) operator or a comment-end at beginning of line,
reindent the line."
  (interactive "*")
  (let ((electric (and tuareg-electric-indent
                       (not (and (boundp 'electric-indent-mode)
                                 electric-indent-mode))
                       (if (tuareg-in-indentation-p)
                           (not (tuareg-in-literal-or-comment-p))
                         (and (looking-back "^[ \t]*\\*"
                                            (line-beginning-position))
                              (nth 4 (syntax-ppss)))))))
    (self-insert-command 1)
    (and electric
         (indent-according-to-mode))))

(defun tuareg-electric-rc ()
  "If inserting a } operator at beginning of line, reindent the line.

Reindent also if } is inserted after a > operator at beginning of line.
Also, if the matching { is followed by a < and this } is not preceded
by >, insert one >."
  (interactive "*")
  (let* ((prec (preceding-char))
         (look-bra (and tuareg-electric-close-vector
                        (not (boundp 'post-self-insert-hook))
                        (not (tuareg-in-literal-or-comment-p))
                        (not (char-equal ?> prec))))
         (electric (and tuareg-electric-indent
                        (not (and (boundp 'electric-indent-mode)
                                  electric-indent-mode))
                        (or (tuareg-in-indentation-p)
                            (and (char-equal ?> prec)
                                 (save-excursion (tuareg-backward-char)
                                                 (tuareg-in-indentation-p))))
                        (not (tuareg-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (when look-bra
      (save-excursion
        (let ((inserted-char
               (save-excursion
                 (tuareg-backward-char)
                 (tuareg-backward-up-list)
                 (cond ((looking-at "{<") ">")
                       (t "")))))
          (tuareg-backward-char)
          (insert inserted-char))))
    (when electric (indent-according-to-mode))))

(defun tuareg-electric-rb ()
  "If inserting a ] operator at beginning of line, reindent the line.

Reindent also if ] is inserted after a | operator at beginning of line.
Also, if the matching [ is followed by a | and this ] is not preceded
by |, insert one |."
  (interactive "*")
  (let* ((prec (preceding-char))
         (look-pipe-or-bra (and tuareg-electric-close-vector
                                (not (boundp 'post-self-insert-hook))
                                (not (tuareg-in-literal-or-comment-p))
                                (not (and (char-equal ?| prec)
                                          (not (char-equal
                                                (save-excursion
                                                  (tuareg-backward-char)
                                                  (preceding-char))
                                                ?\[))))))
         (electric (and tuareg-electric-indent
                        (not (and (boundp 'electric-indent-mode)
                                  electric-indent-mode))
                        (or (tuareg-in-indentation-p)
                            (and (char-equal ?| prec)
                                 (save-excursion (tuareg-backward-char)
                                                 (tuareg-in-indentation-p))))
                        (not (tuareg-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (when look-pipe-or-bra
      (save-excursion
        (let ((inserted-char
               (save-excursion
                 (tuareg-backward-char)
                 (tuareg-backward-up-list)
                 (cond ((looking-at "\\[|") "|")
                       (t "")))))
          (tuareg-backward-char)
          (insert inserted-char))))
    (when electric (indent-according-to-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;				 SMIE

;; TODO:
;; - Obey tuareg-*-indent customization variables.
;; - Fix use of tuareg-indent-command in tuareg-auto-fill-insert-leading-star.
;; - Use it by default (when possible).
;; - Move the old indentation code to a separate file.

(defconst tuareg-smie-grammar
  ;; Problems:
  ;; - "let D in E" expression vs "let D" declaration.  This is solved
  ;;   by making the lexer return "d-let" for the second case.
  ;; - FIXME: SMIE assumes that concatenation binds tighter than
  ;;   everything else, whereas OCaml gives tighter precedence to ".".
  ;; - "x : t1; (y : (t2 -> t3)); z : t4" but
  ;;   "when (x1; x2) -> (z1; z2)".  We solve this by distinguishing
  ;;   the two kinds of arrows, using "t->" for the type arrow.
  ;; - The "with" in modules's "with type" has different precedence.
  ;; - Big problem with "if...then": because of SMIE's transitivity of the
  ;;   precedence relation, we can't properly parse both "if A then B; C" and
  ;;   "if A then let x = E in B; C else D" (IOW I think a non-transitive OPG
  ;;   could do it).  We could try and fix the problem in the lexer, but it's
  ;;   far from obvious how (we'd probably end up having to pre-parse the text
  ;;   in the lexer to decide which kind of "if" and "then" we're looking
  ;;   at).  A good solution could be found maybe if SMIE let us disambiguate
  ;;   lexemes late, i.e. at a time where we have access to the relevant parse
  ;;   stack.  Or maybe by allowing smie-grammar to use a non-transitive
  ;;   precedence relation.  But until that happens, we will live with an
  ;;   incorrect parse, and instead we try to patch up the result with ad-hoc
  ;;   hacks in tuareg-smie-rules.
  ;; - The "<module-type> with <mod-constraints>" syntax introduces many
  ;;   conflicts:
  ;;      "... with module M = A with module B = C"
  ;;   vs      "... module M = A with module B = C"
  ;;   In the first, the second "with" should either have the first "with" as
  ;;   sibling, or have some earlier construct as parent, whereas in the second
  ;;   the "with" should have the first "=" (or maybe the first "module", tho
  ;;   that would not correspond to the actual language syntax and would
  ;;   probably break other cases) as parent.  Other problems in this
  ;;   mod-constraints syntax: we need a precedence along the lines of
  ;;   "with" < "and" < "module/type", whereas the rest of the syntax wants
  ;;   "module/type" < "and" < "with", so basically all the keywords involved
  ;;   in mod-constraints need to be handled specially in the lexer :-(
  ;; - and then some...
  (when (fboundp 'smie-prec2->grammar)
    (let ((bnfprec2
           (smie-bnf->prec2
            '((decls (decls "type" decls) (decls "d-let" decls)
                     (decls "and" decls) (decls ";;" decls)
                     (decls "exception" decls)
                     (decls "module" decls)
                     (decls "class" decls)
                     (decls "val" decls) (decls "external" decls)
                     (decls "open" decls) (decls "include" decls)
                     (decls "DEFINE" decls)
                     (exception)
                     (def)
                     ;; Hack: at the top-level, a "let D in E" can appear in
                     ;; decls as well, but the lexer classifies it as "d-let",
                     ;; so we need to make sure that "d-let D in E" doesn't
                     ;; end up matching the "in" with some far away thingy.
                     (def-in-exp))
              (def-in-exp (defs "in" exp))
              (def (var "d=" exp) (id "d=" datatype) (id "d=" module))
              (idtype (id ":" type))
              (var (id) ("m-type" var) ("rec" var) ("private" var) (idtype)
                   ("l-module" var) ("l-class" var))
              (exception (id "of" type))
              (datatype ("{" typefields "}") (typebranches)
                        (typebranches "with" id))
              (typebranches (typebranches "|" typebranches) (id "of" type))
              (typefields (typefields ";" typefields) (idtype))
              (type (type "*…" type) (type "t->" type)
                    ;; ("<" ... ">") ;; FIXME!
                    (type "as" id))
              (id)
              (module ("struct" decls "end")
                      ("sig" decls "end")
                      ("functor" id "->" module)
                      (module "m-with" mod-constraints))
              (simpledef (id "c=" type))
              (mod-constraints (mod-constraints "m-and" mod-constraints)
                               ("w-type" simpledef)
                               ("w-module" simpledef))
              ;; http://caml.inria.fr/pub/docs/manual-ocaml/expr.html
              ;; exp1 is "all exps except for `if exp then'".
              (exp1 ("begin" exp "end")
                    ("(" exp:type ")")
                    ("[|" exp "|]")
                    ("{" fields "}")
                    ("if" exp "then" exp1 "else" exp1)
                    ;; ("if" exp "then" exp)
                    ("while" exp "do" exp "done")
                    ("for" forbounds "do" exp "done")
                    (exp1 ";" exp1)
                    ("match" exp "with" branches)
                    ("function" branches)
                    ("fun" patterns* "->" exp1)
                    ("try" exp "with" branches)
                    ("let" defs "in" exp1)
                    ("let" "exception-let" exception "in" exp1)
                    ("object" class-body "end")
                    ("(" exp:>type ")")
                    ("{<" fields ">}"))
              ;; Like `exp' but additionally allow if-then without else.
              (exp (exp1) ("if" exp "then" exp))
              (forbounds (iddef "to" exp) (iddef "downto" exp))
              (defs (def) (defs "and" defs) ("l-open" id))
              (exp:>type (exp:type ":>" type))
              (exp:type (exp)) ;; (exp ":" type)
              (fields (fields1) (exp "with" fields1))
              (fields1 (fields1 ";" fields1) (iddef))
              (iddef (id "f=" exp1))
              (branches (branches "|" branches) (branch))
              (branch (patterns "->" exp1))
              (patterns* ("-dlpd-" patterns*) (patterns)) ;See use of "-dlpd-".
              (patterns (pattern) (pattern "when" exp1)
                        ;; Since OCaml 4.02, `match' expressions allow
                        ;; `exception' branches.
                        ("exception-case" pattern))
              (pattern (id) (pattern "as" id) (pattern "|-or" pattern)
                       (pattern "," pattern))
              (class-body (class-body "inherit" class-body)
                          (class-body "method" class-body)
                          (class-body "initializer" class-body)
                          (class-body "val" class-body)
                          (class-body "constraint" class-body)
                          (class-field))
              (class-field (exp) ("mutable" idtype)
                           ("virtual" idtype) ("private" idtype))
              ;; We get cyclic dependencies between ; and | because things like
              ;; "branches | branches" implies that "; > |" whereas "exp ; exp"
              ;; implies "| > ;" and while those two do not directly conflict
              ;; because they're constraints on precedences of different sides,
              ;; they do introduce a cycle later on because those operators are
              ;; declared associative, which adds a constraint that both sides
              ;; must be of equal precedence.  So we declare here a dummy rule
              ;; to force a direct conflict, that we can later resolve with
              ;; explicit precedence rules.
              (foo1 (foo1 ";" foo1) (foo1 "|" foo1))
              ;; "mutable x : int ; y : int".
              (foo2 ("mutable" id) (foo2 ";" foo2))
              )
            ;; Type precedence rules.
            ;; http://caml.inria.fr/pub/docs/manual-ocaml/types.html
            '((nonassoc "as") (assoc "t->") (assoc "*…"))
            ;; Pattern precedence rules.
            ;; http://caml.inria.fr/pub/docs/manual-ocaml/patterns.html
            '((nonassoc "as") (assoc "|-or") (assoc ",") (assoc "::"))
            ;; Resolve "{a=(1;b=2)}" vs "{(a=1);(b=2)}".
            '((nonassoc ";") (nonassoc "f="))
            ;; Resolve "(function a -> b) | c -> d".
            '((nonassoc "function") (nonassoc "|"))
            ;; Resolve "when (function a -> b) -> c".
            '((nonassoc "function") (nonassoc "->"))
            ;; Resolve ambiguity "(let d in e2); e3" vs "let d in (e2; e3)".
            '((nonassoc "in" "match" "->" "with") (nonassoc ";"))
            ;; Resolve "(if a then b else c);d" vs "if a then b else (c; d)".
            '((nonassoc ";") (nonassoc "else")) ;; ("else" > ";")
            ;; Resolve "match e1 with a → (match e2 with b → e3 | c → e4)"
            ;;      vs "match e1 with a → (match e2 with b → e3) | c → e4"
            '((nonassoc "with") (nonassoc "|"))
            ;; Resolve "functor A -> (M with MC)".
            '((nonassoc "->") (nonassoc "m-with"))
            ;; Resolve the conflicts caused by "when" and by SMIE's assumption
            ;; that all non-terminals can match the empty string.
            '((nonassoc "with") (nonassoc "->")) ; "when (match a with) -> e"
            '((nonassoc "|") (nonassoc "->")) ; "when (match a with a|b) -> e"
            ;; Fix up conflict between (decls "and" decls) and (defs "in" exp).
            '((nonassoc "in") (nonassoc "and"))
            ;; Resolve the "artificial" conflict introduced by the `foo1' rule.
            '((assoc "|") (assoc ";"))
            ;; Fix up associative declaration keywords.
            '((assoc "type" "d-let" "exception" "module" "val" "open"
                     "external" "include" "class" "DEFINE" ";;")
              (assoc "and"))
            '((assoc "val" "method" "inherit" "constraint" "initializer"))
            ;; Declare associativity of remaining sequence separators.
            '((assoc ";")) '((assoc "|")) '((assoc "m-and")))))
      ;; (dolist (pair '()) ;; ("then" . "|") ("|" . "then")
      ;;   (display-warning 'prec2 (format "%s %s %s"
      ;;                                   (car pair)
      ;;                                   (gethash pair bnfprec2)
      ;;                                   (cdr pair))))
      ;; SMIE takes for granted that all non-terminals can match the empty
      ;; string, which can lead to the addition of unnecessary constraints.
      ;; Let's remove the ones that cause cycles without causing conflicts.
      (progn
        ;; This comes from "exp ; exp" and "function branches", where
        ;; SMIE doesn't realize that `branches' has to have a -> before ;.
        (assert (eq '> (gethash (cons "function" ";") bnfprec2)))
        (remhash (cons "function" ";") bnfprec2))
      (smie-prec2->grammar
       (smie-merge-prec2s
        bnfprec2
        (smie-precs->prec2
         ;; Precedence of operators.
         ;; http://caml.inria.fr/pub/docs/manual-ocaml/expr.html
         (reverse
          '((nonassoc ".")
            ;; function application, constructor application, assert, lazy
            ;; - -. (prefix)    –
            (right "**…" "lsl" "lsr" "asr")
            (nonassoc "*…" "/…" "%…" "mod" "land" "lor" "lxor")
            (left "+…" "-…")
            (assoc "::")
            (right "@…" "^…")
            (left "=…" "<…" ">…" "|…" "&…" "$…")
            (right "&" "&&")
            (right "or" "||")
            (assoc ",")
            (right "<-" ":=")
            (assoc ";")))))))))

(defun tuareg-smie--search-backward (tokens)
  (let (tok)
    (while (progn
             (setq tok (tuareg-smie--backward-token))
             (if (not (zerop (length tok)))
                 (not (member tok tokens))
	       (unless (bobp)
		 (condition-case err
		     (progn (backward-sexp) t)
		   (scan-error
		    (setq tok (buffer-substring (nth 3 err) (1+ (nth 3 err))))
		    nil))))))
    tok))

(defun tuareg-smie--search-forward (tokens)
  (let (tok)
    (while (progn
             (setq tok (tuareg-smie--forward-token))
             (if (not (zerop (length tok)))
                 (not (member tok tokens))
	       (unless (eobp)
		 (condition-case err
		     (progn (forward-sexp) t)
		   (scan-error
		    (setq tok (buffer-substring (nth 2 err) (nth 3 err)))
		    nil))))))
    tok))

(defun tuareg-skip-blank-and-comments ()
  (forward-comment (point-max)))

(defconst tuareg-smie--type-label-leader
  '("->" ":" "=" ""))

(defconst tuareg-smie--exp-operator-leader
  (delq nil (mapcar (lambda (x) (if (numberp (nth 2 x)) (car x)))
                    tuareg-smie-grammar)))

(defconst tuareg-smie--float-re "[0-9]+\\(?:\\.[0-9]*\\)?\\(?:e[-+]?[0-9]+\\)")

(defun tuareg-smie--forward-token ()
  (tuareg-skip-blank-and-comments)
  (buffer-substring-no-properties
   (point)
   (progn (if (zerop (skip-syntax-forward "."))
              (let ((start (point)))
                (skip-syntax-forward "w_'")
                ;; Watch out for floats!
                (and (memq (char-after) '(?- ?+))
                     (eq (char-before) ?e)
                     (save-excursion
                       (goto-char start)
                       (looking-at tuareg-smie--float-re))
                     (goto-char (match-end 0))))
            ;; The "." char is given symbol property so that "M.x" is
            ;; considered as a single symbol, but in reality, it's part of the
            ;; operator chars, since "+." and friends are operators.
            (while (not (and (zerop (skip-chars-forward "."))
                             (zerop (skip-syntax-forward "."))))))
          (point))))

(defun tuareg-smie--backward-token ()
  (forward-comment (- (point)))
  (buffer-substring-no-properties
   (point)
   (progn (if (and (zerop (skip-chars-backward "."))
                   (zerop (skip-syntax-backward ".")))
              (progn
                (skip-syntax-backward "w_'")
                ;; Watch out for floats!
                (and (memq (char-before) '(?- ?+))
                     (memq (char-after) '(?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9 ?0))
                     (save-excursion
                       (forward-char -1) (skip-syntax-backward "w_")
                       (looking-at tuareg-smie--float-re))
                     (>= (match-end 0) (point))
                     (goto-char (match-beginning 0))))
            (cond
             ((memq (char-after) '(?\; ?,)) nil) ; ".;" is not a token.
             ((and (eq (char-after) ?\.)
                   (memq (char-before) '(?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9 ?0)))
              (skip-chars-backward "0-9")) ; A float number!
             (t ;; The "." char is given symbol property so that "M.x" is
              ;; considered as a single symbol, but in reality, it's part of
              ;; the operator chars, since "+." and friends are operators.
              (while (not (and (zerop (skip-chars-backward "."))
                               (zerop (skip-syntax-backward "."))))))))
          (point))))

(defun tuareg-smie-forward-token ()
  "Move point to the end of the next token and return its SMIE name."
  (let ((tok (tuareg-smie--forward-token)))
    (cond
     ((zerop (length tok))
      (if (not (looking-at "{<\\|\\[|"))
          tok
        (goto-char (match-end 0))
        (match-string 0)))
     ((and (equal tok "|") (looking-at "\\]")) (forward-char 1) "|]")
     ((and (equal tok ">") (looking-at "}")) (forward-char 1) ">}")
     ((or (member tok '("let" "=" "->"
                        "module" "class" "open" "type" "with" "and"
                        "exception"))
          ;; http://caml.inria.fr/pub/docs/manual-ocaml/expr.html lists
          ;; the tokens whose precedence is based on their prefix.
          (memq (aref tok 0) '(?* ?/ ?% ?+ ?- ?@ ?^ ?= ?< ?> ?| ?& ?$)))
      ;; When indenting, the movement is mainly backward, so it's OK to make
      ;; the forward tokenizer a bit slower.
      (save-excursion (tuareg-smie-backward-token)))
     ((and (member tok '("~" "?"))
           (looking-at "[[:alpha:]_][[:alnum:]'_]*:"))
      (goto-char (match-end 0))
      "label:")
     ((and (looking-at ":\\(?:[^:]\\|\\'\\)")
           (string-match "\\`[[:alpha:]_]" tok)
           (save-excursion
             (tuareg-smie--backward-token) ;Go back.
             (member (tuareg-smie--backward-token)
                     tuareg-smie--type-label-leader)))
      (forward-char 1)
      "label:")
     ((string-match "\\`[[:alpha:]_].*\\.\\'"  tok)
      (forward-char -1) (substring tok 0 -1))
     (t tok))))

(defconst tuareg-smie--exp-leaders
  ;; (let ((leaders ()))
  ;;   (dolist (cat tuareg-smie-bnf)
  ;;     (dolist (rule (cdr cat))
  ;;       (setq rule (reverse rule))
  ;;       (while (setq rule (cdr (memq 'exp rule)))
  ;;         (push (car rule) leaders))))
  ;;   leaders)
  '("if" "then" "try" "match" "do" "while" "begin" "in" "when"
    "downto" "to" "else"))

(defun tuareg-smie--label-colon-p ()
  (and (not (zerop (skip-chars-backward "[[:alnum:]]_")))
       (or (not (zerop (skip-chars-backward "?~")))
           (save-excursion
             (member (tuareg-smie--backward-token)
                     tuareg-smie--type-label-leader)))))

(defun tuareg-smie--=-disambiguate ()
  "Return which kind of \"=\" we've just found.
Point is not moved and should be right in front of the equality.
Return values can be
  \"f=\" for field definition,
  \"d=\" for a normal definition,
  \"c=\" for a type equality constraint, and
  \"=…\" for an equality test."
  (save-excursion
    (let* ((pos (point))
           (telltale '("type" "let" "module" "class" "and" "external"
                       "val" "method" "DEFINE" "=" ":="
                       "if" "then" "else" "->" ";" ))
           (nearest (tuareg-smie--search-backward telltale)))
      (cond
       ((and (member nearest '("{" ";"))
             (let ((field t))
               (while
                   (let ((x (tuareg-smie--forward-token)))
                     (and (< (point) pos)
                          (cond
                           ((zerop (length x)) (setq field nil))
                           ((memq (char-syntax (aref x 0)) '(?w ?_)))
                           ((member x '("." ";")))
                           (t (setq field nil))))))
               field))
        "f=")
       ((progn
          (while (and (equal nearest "->")
                      (save-excursion
                        (forward-char 2)
                        (equal (tuareg-smie-backward-token) "t->")))
            (setq nearest (tuareg-smie--search-backward telltale)))
          nil))
       ((and (member nearest '("=" ":="))
             (member (tuareg-smie--search-backward telltale)
                     '("type" "module")))
        ;; Second equality in "type t = M.t = C" or after mod-constraint
        "d=")
       ((not (member nearest '("type" "let" "module" "class" "and"
                               "external" "val" "method" "DEFINE")))
        "=…")
       ((and (member nearest '("type" "module"))
             ;; Maybe a module's type equality constraint?
             (or (member (tuareg-smie--backward-token) '("with" "and"))
                 ;; Or maybe an alias as part of a definition?
                 (and (equal nearest "type")
                      (goto-char (1+ pos)) ;"1+" to skip the `=' itself!
                      (let ((tok (tuareg-smie--search-forward
                                  (cons "=" (mapcar #'car
                                                    tuareg-smie-grammar)))))
                        (equal tok "=")))))
        "c=")
       (t "d=")))))

(defun tuareg-smie--:=-disambiguate ()
  "Return which kind of \":=\" we've just found.
Point is not moved and should be right in front of the equality.
Return values can be
  \":=\" for assignment definition,
  \"c=\" for destructive equality constraint."
  (save-excursion
    (let* ((telltale '("type" "let" "module" "class" "and" "external"
                       "val" "method" "DEFINE" "=" ":="
                       "if" "then" "else" "->" ";" ))
           (nearest (tuareg-smie--search-backward telltale)))
      (cond				;Issue #7
       ((and (member nearest '("type" "module"))
             (member (tuareg-smie--backward-token) '("with" "and"))) "c=")
       (t ":=")))))

(defun tuareg-smie--|-or-p ()
  "Return non-nil if we're just in front of an or pattern \"|\"."
  (save-excursion
    (let ((tok (tuareg-smie--search-backward
                ;; Stop at the first | or any token which should
                ;; never appear between a "|" and a "|-or".
                '("|" "[" "->" "with" "function" "=" "of" "in" "then"))))
      (cond
       ((equal tok "(") t)
       ((equal tok "|")
        ;; Maybe we have a "|-or".  Then again maybe not.  We should make sure
        ;; that `tok' is really either a "|-or" or the | of a match (and not
        ;; the | of a datatype definition).
        (while
            (equal "|"
                   (setq tok
                         (tuareg-smie--search-backward
                          '("|" "with" "function" "=" "of" "in" "then")))))
        (cond
         ((equal tok "=")
          (not (equal (tuareg-smie--=-disambiguate) "d=")))
         ((equal tok "of") nil)
         ((member tok '("[" "{" "(")) nil)
         (t t)))))))

(defun tuareg-smie-backward-token ()
  "Move point to the beginning of the next token and return its SMIE name."
  (let ((tok (tuareg-smie--backward-token)))
    (cond
     ;; Distinguish a let expression from a let declaration.
     ((equal tok "let")
      (save-excursion
        (let ((prev (tuareg-smie--backward-token)))
          (if (or (member prev tuareg-smie--exp-leaders)
                  (if (zerop (length prev))
                      (and (not (bobp))
                           (eq 4 (mod (car (syntax-after (1- (point)))) 256)))
                    (and (eq ?. (char-syntax (aref prev 0)))
                         (not (equal prev ";;")))))
              tok
            "d-let"))))
     ;; Handle "let module" and friends.
     ((member tok '("module" "class" "open"))
      (let ((prev (save-excursion (tuareg-smie--backward-token))))
        (cond
         ((equal prev "let") (concat "l-" tok))
         ((and (member prev '("with" "and")) (equal tok "module")) "w-module")
         (t tok))))
     ;; Distinguish a "type ->" from a "case ->".
     ((equal tok "->")
      (save-excursion
        (let (nearest)
          (while (progn
                   (setq nearest (tuareg-smie--search-backward
                                  '("with" "|" "fun" "function" "functor"
				    "type" ":" "of")))
                   (and (equal nearest ":")
                        (tuareg-smie--label-colon-p))))
          (if (member nearest '("with" "|" "fun" "function" "functor"))
              tok "t->"))))
     ;; Handle "module type" and mod-constraint's "with/and type".
     ((equal tok "type")
      (save-excursion
        (let ((prev (tuareg-smie--backward-token)))
          (cond ((equal prev "module") "m-type")
                ((member prev '("and" "with")) "w-type")
                (t tok)))))
     ;; Disambiguate mod-constraint's "and" and "with".
     ((member tok '("with" "and"))
      (save-excursion
        (tuareg-smie--forward-token)
        (if (member (tuareg-smie--forward-token) '("type" "module"))
            (concat "m-" tok) tok)))
     ;; Distinguish a defining = from a comparison-=.
     ((equal tok "=")
      (tuareg-smie--=-disambiguate))
     ((equal tok ":=") (tuareg-smie--:=-disambiguate))
     ((zerop (length tok))
      (if (not (and (memq (char-before) '(?\} ?\]))
                    (save-excursion (forward-char -2)
                                    (looking-at ">}\\||\\]"))))
          tok
        (goto-char (match-beginning 0))
        (match-string 0)))
     ((and (equal tok "|") (eq (char-before) ?\[)) (forward-char -1) "[|")
     ((and (equal tok "<") (eq (char-before) ?\{)) (forward-char -1) "{<")
     ((equal tok "|")
      ;; Check if it's the | of an or-pattern, since it has a slightly
      ;; different precedence (see Issue #71 for an example).
      (if (tuareg-smie--|-or-p) "|-or" "|"))
     ;; Some infix operators get a precedence based on their prefix, so we
     ;; collapse them into a canonical representative.
     ;; See http://caml.inria.fr/pub/docs/manual-ocaml/expr.html.
     ((memq (aref tok 0) '(?* ?/ ?% ?+ ?- ?@ ?^ ?= ?< ?> ?| ?& ?$))
      (cond
       ((member tok '("|" "||" "&" "&&" "<-" "->")) tok)
       ((and (eq (aref tok 0) ?*) (> (length tok) 1) (eq (aref tok 1) ?*))
        "**…")
       (t (string (aref tok 0) ?…))))
     ((equal tok ":")
      (let ((pos (point)))
        (if (tuareg-smie--label-colon-p)
            "label:"
          (goto-char pos)
          tok)))
     ((equal tok "exception")
      (let ((back-tok (save-excursion (tuareg-smie--backward-token))))
	(cond
	 ((member back-tok '("|" "with")) "exception-case")
	 ((equal back-tok "let") "exception-let")
	 (t tok))))
     ((string-match "\\`[[:alpha:]_].*\\.\\'"  tok)
      (forward-char (1- (length tok))) ".")
     (t tok))))

(defun tuareg-smie-rules (kind token)
  ;; FIXME: Handling of "= |", "with |", "function |", and "[ |" is
  ;; problematic.
  (cond
   ;; Special indentation for module fields.
   ((and (eq kind :after) (member token '("." ";"))
         (smie-rule-parent-p "with")
         (tuareg-smie--with-module-fields-rule)))
   ((and (eq kind :after) (equal token ";;"))
    0)
   ;; Special indentation for monadic >>>, >>|, >>=, and >|= operators.
   ((and (eq kind :before) (tuareg-smie--monadic-rule token)))
   ((and (equal token "and") (smie-rule-parent-p "type"))
    0)
   ((member token '(";" "|" "," "and" "m-and"))
    (cond
     ((and (eq kind :before) (member token '("|" ";"))
           (smie-rule-parent-p "then")
           ;; We have misparsed the code: TOKEN is not a child of `then' but
           ;; should have closed the "if E1 then E2" instead!
           (tuareg-smie--if-then-hack token)))
     ;; FIXME: smie-rule-separator doesn't behave correctly when the separator
     ;; is right after the parent (on another line).
     ((and (smie-rule-bolp) (smie-rule-prev-p "d=" "with" "[" "function"))
      (if (and (eq kind :before) (smie-rule-bolp)
               (smie-rule-prev-p "[" "d=" "function"))
          0 tuareg-with-indent))
     ((and (equal token "|") (smie-rule-bolp) (not (smie-rule-prev-p "d="))
           (smie-rule-parent-p "d="))
      ;; FIXME: Need a comment explaining what this tries to do.
      ;; FIXME: Should this only apply when (eq kind :before)?
      ;; FIXME: Don't use smie--parent.
      (goto-char (cadr smie--parent))
      (smie-indent-forward-token)
      (tuareg-skip-blank-and-comments)
      `(column . ,(- (current-column) 2)))
     (t (smie-rule-separator kind))))
   (t
    (case kind
      (:elem (cond
              ((eq token 'basic) tuareg-default-indent)
              ;; The default tends to indent much too deep.
              ((eq token 'empty-line-token) ";")))
      (:list-intro (member token '("fun")))
      (:close-all t)
      (:before
       (cond
        ((equal token "d=") (smie-rule-parent 2))
        ((member token '("fun" "match"))
         (and (not (smie-rule-bolp))
              (cond ((smie-rule-prev-p "d=")
                     (smie-rule-parent tuareg-default-indent))
                    ((smie-rule-prev-p "begin") (smie-rule-parent)))))
        ((equal token "then") (smie-rule-parent))
        ((equal token "if") (if (and (not (smie-rule-bolp))
                                     (smie-rule-prev-p "else"))
                                (smie-rule-parent)))
        ((and (equal token "with") (smie-rule-parent-p "{"))
         (smie-rule-parent))
        ((and (equal token "with") (smie-rule-parent-p "d="))
         (let ((td (smie-backward-sexp "with")))
           (assert (equal (nth 2 td) "d="))
           (goto-char (nth 1 td))
           (setq td (smie-backward-sexp "d="))
           ;; Presumably (equal (nth 1 td) "type").
           (goto-char (nth 1 td))
           `(column . ,(smie-indent-virtual))))
        ;; Align the "with" of "module type A = B \n with ..." w.r.t "module".
        ((and (equal token "m-with") (smie-rule-parent-p "d="))
         (save-excursion
           (smie-backward-sexp token)
           (goto-char (nth 1 (smie-backward-sexp 'halfsexp)))
           (cons 'column (+ 2 (current-column)))))
        ;; Treat purely syntactic block-constructs as being part of their
        ;; parent, when the opening statement is hanging.
        ((member token '("let" "(" "[" "{" "sig" "struct" "begin"))
         (when (and (smie-rule-hanging-p)
                    (apply #'smie-rule-prev-p
                           tuareg-smie--exp-operator-leader))
           (if (let ((openers '("{" "(" "{<" "[" "[|")))
                 (or (apply #'smie-rule-prev-p openers)
                     (not (apply #'smie-rule-parent-p openers))))
               (let ((offset (if (and (member token '("(" "struct" "sig"))
                                      (not (smie-rule-parent-p "let" "d-let")))
                                 0
                               tuareg-default-indent)))
                 (smie-rule-parent offset))
             ;; In "{ a = (", "{" and "a =" are not part of the same
             ;; syntax rule, so "(" is part of "a =" but not of the
             ;; surrounding "{".
             (save-excursion
               (smie-backward-sexp 'halfsexp)
               (cons 'column (smie-indent-virtual))))))
	((and tuareg-match-patterns-aligned
	      (equal token "|-or") (smie-rule-parent-p "|"))
	 (smie-rule-parent))
        ;; If we're looking at the first class-field-spec
        ;; in a "object(type)...end", don't rely on the default behavior which
        ;; will treat (type) as a previous element with which to align.
        ((tuareg-smie--object-hanging-rule token))
        ;; Apparently, people like their `| pattern when test -> body' to have
        ;;  the `when' indented deeper than the body.
        ((equal token "when") (smie-rule-parent tuareg-match-when-indent))))
      (:after
       (cond
        ((equal token "d=")
         (and (smie-rule-parent-p "type")
              (not (smie-rule-next-p "["))
              0))
        ((equal token "->")
         (cond
          ((smie-rule-parent-p "with")
           ;; Align with "with" but only if it's the only branch (often
           ;; the case in try..with), since otherwise subsequent
           ;; branches can't be both indented well and aligned.
           (if (save-excursion
                 (and (not (equal "|" (nth 2 (smie-forward-sexp "|"))))
                      ;; Since we may misparse "if..then.." we need to
                      ;; double check that smie-forward-sexp indeed got us
                      ;; to the right place.
                      (equal (nth 2 (smie-backward-sexp "|")) "with")))
               (smie-rule-parent 2)
             ;; Align with other clauses, even with no preceding "|"
             tuareg-match-clause-indent))
          ((smie-rule-parent-p "function")
           ;; Similar to the previous rule but for "function"
           (if (save-excursion
                 (and (not (equal "|" (nth 2 (smie-forward-sexp "|"))))
                      (equal (nth 2 (smie-backward-sexp "|")) "function")))
               (smie-rule-parent tuareg-default-indent)
             tuareg-match-clause-indent))
          ((smie-rule-parent-p "|") tuareg-match-clause-indent)
          ;; Special case for "CPS style" code.
          ;; https://github.com/ocaml/tuareg/issues/5.
          ((smie-rule-parent-p "fun")
           (save-excursion
             (smie-backward-sexp "->")
             (if (eq ?\( (char-before))
                 (cons 'column
                       (+ tuareg-default-indent
                          (progn
                            (backward-char 1)
                            (smie-indent-virtual))))
               0)))
          (t 0)))
        ((equal token ":")
         (cond
          ((smie-rule-parent-p "val" "external") (smie-rule-parent 2))
          ((smie-rule-parent-p "module") (smie-rule-parent))
          (t 2)))
        ((equal token "in") tuareg-in-indent) ;;(if (smie-rule-hanging-p)
        ((equal token "with")
         (cond
          ;; ((smie-rule-next-p "|") 2)
          ((smie-rule-parent-p "{") nil)
          (t (+ 2 tuareg-with-indent))))
        ((or (member token '("." "t->" "]"))
             (consp (nth 2 (assoc token tuareg-smie-grammar)))) ;; Closer.
         nil)
        ((member token '("{" "("))
         ;; The virtual indent after ( can be higher than the actual one
         ;; because it might be "column + tuareg-default-indent", whereas
         ;; the token only occupies a single column.  So make sure we don't
         ;; get caught in this trap.
         (let ((vi (smie-indent-virtual)))
           (forward-char 1)             ;Skip paren.
           (skip-chars-forward " \t")
           (unless (eolp)
             `(column
               . ,(min (current-column)
                       (+ tuareg-default-indent vi))))))
        (t tuareg-default-indent)))))))

(defun tuareg-smie--with-module-fields-rule ()
  ;; Indentation of fields after "{ E with Module." where the "Module."
  ;; syntactically only applies to the first field, but has
  ;; semantically a higher position since it applies to all fields.
  (save-excursion
    (forward-char 1)
    (smie-backward-sexp 'halfsexp)
    (when (looking-at "\\(?:\\sw\\|\\s_\\)+\\.[ \t]*$")
      (smie-backward-sexp 'halfsexp)
      (cons 'column (current-column)))))

(defconst tuareg-smie--monadic-operators '(">>|" ">>=" ">>>" ">|=")
  "Monadic infix operators")

(defconst tuareg-smie--monadic-op-re
  (regexp-opt tuareg-smie--monadic-operators))

(defun tuareg-smie--monadic-rule (token)
  ;; When trying to indent a >>=, try to look back to find any earlier
  ;; >>= in a sequence of "monadic steps".
  (or (and (equal token ">…") (looking-at tuareg-smie--monadic-op-re)
           (save-excursion
             (tuareg-smie--forward-token)
             (let ((indent nil))
               (while
                   (let ((parent-data (smie-backward-sexp 'halfsexp)))
                     (cond
                      ((car parent-data) (member (nth 2 parent-data) '("->")))
                      ((member (nth 2 parent-data) '(";" "d=")) nil)
                      ((member (nth 2 parent-data) '("fun" "function"))
                       (if (member (tuareg-smie--backward-token)
                                   tuareg-smie--monadic-operators)
                           (progn
                             (setq indent (cons 'column
                                                (smie-indent-virtual)))
                             nil)
                         t)))))
               indent)))
      ;; In "foo >>= fun x -> bar" indent `bar' relative to `foo'.
      (and (member token '("fun" "function")) (not (smie-rule-bolp))
           (save-excursion
             (let ((prev (tuareg-smie-backward-token)))
               ;; FIXME: Should we use the same loop as above?
               (and (equal prev ">…") (looking-at tuareg-smie--monadic-op-re)
                    (progn (smie-backward-sexp prev)
                           (cons 'column (current-column)))))))))

(defun tuareg-smie--object-hanging-rule (token)
  ;; If we're looking at the first class-field-spec
  ;; in a "object(type)...end", don't rely on the default behavior which
  ;; will treat (type) as a previous element with which to align.
  (cond
   ;; An important role of this first condition is to call smie-indent-virtual
   ;; so that we get called back to compute the (virtual) indentation of
   ;; "object", thus making sure we get called back to apply the second rule.
   ((and (member token '("inherit" "val" "method" "constraint"))
         (smie-rule-parent-p "object"))
    (save-excursion
      (forward-word 1)
      (goto-char (nth 1 (smie-backward-sexp 'halfsexp)))
      (let ((col (smie-indent-virtual)))
        `(column . ,(+ tuareg-default-indent col)))))
   ;; For "class foo = object(type)...end", align object...end with class.
   ((and (equal token "object") (smie-rule-parent-p "class"))
    (smie-rule-parent))))

(defun tuareg-smie--if-then-hack (token)
  ;; Getting SMIE's parser to properly parse "if E1 then E2" is difficult, so
  ;; instead we live with a confused parser and try to work around the mess
  ;; here, although it clearly won't help other uses of the parser
  ;; (e.g. navigation).
  (save-excursion
    (let (pd)
      (while (equal (nth 2 (setq pd (smie-backward-sexp token))) "then")
        (let ((pdi (smie-backward-sexp 'halfsexp)))
          (assert (equal (nth 2 pdi) "if"))))
      (cond
       ((equal (nth 2 pd) token)
        (goto-char (nth 1 pd))
        (cons 'column (smie-indent-virtual)))
       ((and (equal token "|") (equal (nth 2 pd) "with")
             (not (smie-rule-bolp)))
        (goto-char (nth 1 pd))
        (cons 'column (+ 3 (current-column))))
       (t (cons 'column (current-column)))))))

(defun tuareg-smie--inside-string ()
  (when (nth 3 (syntax-ppss))
    (save-excursion
      (goto-char (1+ (nth 8 (syntax-ppss))))
      (current-column))))

(defcustom tuareg-indent-align-with-first-arg t
  "Non-nil if indentation should try to align arguments on the first one.
With a non-nil value you get

    let x = List.map (fun x -> 5)
                     my list

whereas with a non value you get

    let x = List.map (fun x -> 5)
              my list"
  :type 'boolean)

(defun tuareg-smie--args ()
  ;; FIXME: This is largely copy&pasted from smie.el.  SMIE should offer a way
  ;; to hook into smie-indent-exps in order to control that behavior.
  (unless (or tuareg-indent-align-with-first-arg
              (nth 8 (syntax-ppss))
              (looking-at comment-start-skip)
              (numberp (nth 1 (save-excursion (smie-indent-forward-token))))
              (numberp (nth 2 (save-excursion (smie-indent-backward-token)))))
    (save-excursion
      (let ((positions nil)
            arg)
        (while (and (null (car (smie-backward-sexp)))
                    (push (point) positions)
                    (not (smie-indent--bolp))))
        (save-excursion
          ;; Figure out if the atom we just skipped is an argument rather
          ;; than a function.
          (setq arg
                (or (null (car (smie-backward-sexp)))
                    (funcall smie-rules-function :list-intro
                             (funcall smie-backward-token-function)))))
        (cond
         ((null positions)
          ;; We're the first expression of the list.  In that case, the
          ;; indentation should be (have been) determined by its context.
          nil)
         (arg
          ;; There's a previous element, and it's not special (it's not
          ;; the function), so let's just align with that one.
          (goto-char (car positions))
          (if (fboundp 'smie-indent--current-column)
              (smie-indent--current-column)
            (current-column)))
         (t
          ;; There's no previous arg at BOL.  Align with the function.
          (goto-char (car positions))
          (+ (smie-indent--offset 'args)
             ;; We used to use (smie-indent-virtual), but that
             ;; doesn't seem right since it might then indent args less than
             ;; the function itself.
             (if (fboundp 'smie-indent--current-column)
                 (smie-indent--current-column)
               (current-column)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                 Phrase movements and indentation

(defun tuareg--skip-double-colon ()
  (when (looking-at ";;[ \t\n]*")
    (goto-char (match-end 0))))

(when tuareg-use-smie
  (defconst tuareg--beginning-of-phrase-syms
    (let* ((prec (cdr (assoc "d-let" tuareg-smie-grammar)))
           (syms (delq nil
                       (mapcar (lambda (x) (if (equal (cdr x) prec) (car x)))
                               tuareg-smie-grammar))))
      (dolist (k '(";;"))
        (setq syms (delete k syms)))
      syms))

  (defun tuareg--beginning-of-phrase ()
    "Move the point to the beginning of the OCaml phrase on which the point is."
    (if (nth 3 (syntax-ppss)); in a string
        (goto-char (nth 8 (syntax-ppss))))
    (while
        (if (save-excursion
              (member (tuareg-smie-backward-token)
                      tuareg--beginning-of-phrase-syms))
            (progn
              (tuareg-smie-backward-token)
              nil)
          (let ((td (smie-backward-sexp 'halfsexp)))
            (cond
             ((member (nth 2 td) tuareg--beginning-of-phrase-syms)
              (goto-char (nth 1 td))
              nil)
             ((and (car td) (not (numberp (car td))))
              (unless (bobp) (goto-char (nth 1 td)) t))
             (t t))))))

  (defun tuareg-discover-phrase ()
    "Return a triplet (BEGIN END END-WITH-COMMENTS)."
    (save-excursion
      (let ((pos (point)))
        (end-of-line)
        (tuareg--beginning-of-phrase)
        (let ((begin (point))
              end
              end-comment)
          (while (progn
                   (smie-forward-sexp 'halfsexp)
                   (setq end (point))
                   (tuareg-skip-blank-and-comments)
                   (< (point) pos))
            ;; Looks like tuareg--beginning-of-phrase went too far back!
            (setq begin (point)))
          (setq end-comment (point))
          (goto-char begin)
          ;; ";;" is not part of the phrase and neither comments
          (tuareg--skip-double-colon)
          (tuareg-skip-blank-and-comments)
          (list (point) end end-comment)))))

  (defun tuareg--string-boundaries ()
    "Assume point is inside a string and return (START . END), the
positions delimiting the string (including its delimiters)."
    (save-excursion
      (let ((start (nth 8 (syntax-ppss)))
            end)
        (goto-char start)
        (smie-forward-sexp)
        (setq end (1- (point)))
        (cons start end))))

  (defun tuareg--fill-string ()
    "Assume the point is inside a string delimited by \" and jusfify it.
This function moves the point."
    (let* ((start-end (tuareg--string-boundaries))
           (start (set-marker (make-marker) (car start-end)))
           (end   (set-marker (make-marker) (cdr start-end)))
           fill-prefix
           (fill-individual-varying-indent t)
           (use-hard-newlines t))
      (indent-region (marker-position start) (marker-position end))
      ;; Delete all backslash protected newlines except those without
      ;; a preceding space that serve to cut a long word.
      (goto-char (marker-position start))
      ;(indent-according-to-mode)
      (setq fill-prefix (make-string (1+ (current-column)) ?\ ))
      (if (looking-at "\"\\\\ *[\n\r] *")
          (replace-match "\""))
      (while (re-search-forward " +\\\\ *[\n\r] *" (marker-position end) t)
        (replace-match " "))
      (set-hard-newline-properties (marker-position start)
                                   (marker-position end))
      ;; Do not include the final \" not to remove space before it:
      (fill-region (marker-position start) (1- (marker-position end)))
      ;; Protect all soft newlines
      (goto-char (marker-position start))
      (end-of-line)
      (while (< (point) (marker-position end))
        (unless (get-char-property (point) 'hard)
          (insert " \\"))
        (forward-char)
        (end-of-line))
      (set-marker start nil)
      (set-marker end nil)))

  (defun tuareg--fill-comment ()
    "Assumes the point is inside a comment and justify it.
This function moves the point."
    (let* ((start (set-marker (make-marker) (nth 8 (syntax-ppss))))
           (end (make-marker))
           fill-prefix
           (use-hard-newlines t))
      (goto-char (marker-position start))
      (indent-according-to-mode)
      (setq fill-prefix (make-string (+ 3 (current-column)) ?\ ))
      (forward-comment 1)
      (set-marker end (point))
      (goto-char (marker-position start))
      (let ((e (marker-position end)))
        (while (re-search-forward "\n\n" e t)
          (put-text-property (match-beginning 0) (match-end 0) 'hard 't)))
      (fill-region start end)
      (remove-text-properties (marker-position start) (marker-position end)
                              '(hard))
      (set-marker start nil)
      (set-marker end nil)))

  (defun tuareg-indent-phrase ()
    "Depending of the context: justify and indent a comment,
or indent all lines in the current phrase."
    (interactive)
    (save-excursion
      (let ((ppss (syntax-ppss)))
        (cond
         ((equal ?\"(nth 3 ppss))
          (tuareg--fill-string))
         ((nth 4 ppss)
          (tuareg--fill-comment))
         (t (let ((phrase (tuareg-discover-phrase)))
              (indent-region (car phrase) (cadr phrase))))))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              The major mode

(defun tuareg--switch-outside-build ()
  "If the current buffer refers to a file under a _build
directory and a corresponding file exists outside the _build
directory, propose the user to switch to it.  Return t if the
switch was made."
  (let ((fpath (buffer-file-name))
	(p nil)
	b)
    (when fpath
      (setq fpath (abbreviate-file-name fpath))
      (while (not (or (null fpath)
		      (string=
		       (setq b (file-name-nondirectory
				(setq fpath (directory-file-name fpath))))
		       "_build")))
	(push b p)
	(let ((parent (file-name-directory fpath)))
	  (setq fpath (if (string= parent fpath) nil parent))))
      (when fpath
	;; Make `fpath' the path without _build.
	(setq fpath (file-name-directory fpath))
	(while p
	  (setq fpath (concat (file-name-as-directory fpath) (pop p))))
	(if (file-exists-p fpath)
	    (when (y-or-n-p "File in _build.  Switch to corresponding \
file outside _build? ")
	      (kill-buffer)
	      (find-file fpath)
	      t)
          (read-only-mode)
	  (message "File under _build.  C-x C-q to edit.")
	  nil)))))

(defmacro tuareg--eval-when-macrop (f form)
  "Execute FORM but only when F is `fboundp' (because it's a macro).
If F is not bound yet, then keep the code un-expanded and perform the
expansion at run-time, if the run-time version of Emacs does know this macro."
  (declare (debug (symbolp body)) (indent 1))
  (if (fboundp f) form                  ;Macro expanded at compile-time.
    `(if (fboundp ',f) (eval ',form)))) ;Macro expanded at run-time.

(defun tuareg--hanging-eolp-advice ()
  "Recognize \"fun ..args.. ->\" at EOL as being hanging."
  (when (looking-at "fun\\_>")
    (smie-indent-forward-token)
    ;; We define a special "-dlpd-" token
    ;; ("-dummy-left-pattern-delimiter-") in the grammar
    ;; specifically so as to be able to make the right
    ;; call to smie-forward-sexp here.
    (if (equal "->" (nth 2 (smie-forward-sexp "-dlpd-")))
        (smie-indent-forward-token))))

(defun tuareg--common-mode-setup ()
  (setq local-abbrev-table tuareg-mode-abbrev-table)
  (when (fboundp 'tuareg-syntax-propertize)
    (set (make-local-variable 'syntax-propertize-function)
         #'tuareg-syntax-propertize))
  (set (make-local-variable 'parse-sexp-ignore-comments)
       ;; Tuareg used to set this to nil (for an unknown reason) but SMIE needs
       ;; it to be set to t.
       tuareg-use-smie)
  (if (and tuareg-smie-grammar tuareg-use-smie)
      (progn
        (smie-setup tuareg-smie-grammar #'tuareg-smie-rules
                    :forward-token #'tuareg-smie-forward-token
                    :backward-token #'tuareg-smie-backward-token)
        (tuareg--eval-when-macrop add-function
          (when (boundp 'smie--hanging-eolp-function)
            ;; FIXME: As its name implies, smie--hanging-eolp-function
            ;; is not to be used by packages like us, but SMIE's maintainer
            ;; hasn't provided any alternative so far :-(
            (add-function :before (local 'smie--hanging-eolp-function)
                          #'tuareg--hanging-eolp-advice)))
        (add-hook 'smie-indent-functions #'tuareg-smie--args nil t)
        (add-hook 'smie-indent-functions #'tuareg-smie--inside-string nil t)
        (set (make-local-variable 'add-log-current-defun-function)
             'tuareg-current-fun-name))
    (set (make-local-variable 'indent-line-function) #'tuareg-indent-command))
  (set (make-local-variable 'prettify-symbols-alist)
       (if tuareg-prettify-symbols-full
           (append tuareg-prettify-symbols-basic-alist
                   tuareg-prettify-symbols-extra-alist)
         tuareg-prettify-symbols-basic-alist))
  (tuareg-install-font-lock)
  (set (make-local-variable 'open-paren-in-column-0-is-defun-start) nil)

  (add-hook 'completion-at-point-functions #'tuareg-completion-at-point nil t)

  (when (fboundp 'electric-indent-mode)
    (add-hook 'electric-indent-functions
              #'tuareg--electric-indent-predicate nil t))
  (when (boundp 'post-self-insert-hook)
    (add-hook 'post-self-insert-hook #'tuareg--electric-close-vector nil t)))

;;;###autoload(add-to-list 'auto-mode-alist '("\\.ml[ip]?\\'" . tuareg-mode))
;;;###autoload(add-to-list 'auto-mode-alist '("\\.eliomi?\\'" . tuareg-mode))
;;;###autoload(dolist (ext '(".cmo" ".cmx" ".cma" ".cmxa" ".cmi"
;;;###autoload                ".annot" ".cmt" ".cmti"))
;;;###autoload  (add-to-list 'completion-ignored-extensions ext))

(defalias 'tuareg--prog-mode
  (if (fboundp 'prog-mode) #'prog-mode #'fundamental-mode))

(defvar compilation-first-column)

(defvar compilation-error-screen-columns)

;;;###autoload
(define-derived-mode tuareg-mode tuareg--prog-mode "Tuareg"
  "Major mode for editing OCaml code.

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

A Tuareg Interactive Mode to evaluate expressions in a toplevel is
included.  Type `M-x tuareg-run-ocaml' or simply `M-x run-ocaml' or see
special-keys below.

Short cuts for the Tuareg mode:
\\{tuareg-mode-map}

Short cuts for interactions with the toplevel:
\\{tuareg-interactive-mode-map}"

  (unless (tuareg--switch-outside-build)
    ;; Initialize the Tuareg menu
    (tuareg-build-menu)

    ;; (unless tuareg-use-smie
    ;; Initialize indentation regexps
    (tuareg-make-indentation-regexps) ;;)

    (set (make-local-variable 'paragraph-start)
	 (concat "^[ \t]*$\\|\\*)$\\|" page-delimiter))
    (set (make-local-variable 'paragraph-separate) paragraph-start)
    (set (make-local-variable 'require-final-newline) t)
    (set (make-local-variable 'comment-start) "(* ")
    (set (make-local-variable 'comment-end) " *)")
    (set (make-local-variable 'comment-start-skip) "(\\*+[ \t]*")
    ;(set (make-local-variable 'comment-column) 40)              ;FIXME: Why?
    ;(set (make-local-variable 'comment-multi-line) t)           ;FIXME: Why?
    ;; `ocamlc' counts columns from 0, contrary to other tools which start at 1.
    (set (make-local-variable 'compilation-first-column) 0)
    (set (make-local-variable 'compilation-error-screen-columns) nil)
    ;; TABs should NOT be used in OCaml files:
    (setq indent-tabs-mode nil)
    (tuareg--common-mode-setup)
    (when (fboundp 'tuareg-auto-fill-function)
      ;; Emacs-21's newcomment.el provides this functionality by default.
      (set (make-local-variable 'normal-auto-fill-function)
	   #'tuareg-auto-fill-function))

    (set (make-local-variable 'imenu-create-index-function)
	 #'tuareg-imenu-create-index)

    (when (and tuareg-use-abbrev-mode
	       (not (and (boundp 'electric-indent-mode) electric-indent-mode)))
      (abbrev-mode 1))
    (run-mode-hooks 'tuareg-load-hook)))

(defconst tuareg-starters-syms
  '("module" "type" "let" "d-let" "and"))

(defun tuareg-find-matching-starter (starters)
  (let (tok)
    (while
        (let ((td (smie-backward-sexp 'halfsexp)))
          (cond
           ((and (car td)
                 (member (nth 2 td) starters))
            (goto-char (nth 1 td)) (setq tok (nth 2 td)) nil)
           ((and (car td) (not (numberp (car td))))
            (unless (bobp) (goto-char (nth 1 td)) t))
           (t t))))
    tok))

(defun tuareg-skip-siblings ()
  (while (and (not (bobp))
              (null (car (smie-backward-sexp))))
    (tuareg-find-matching-starter tuareg-starters-syms))
  (when (looking-at "in")
    ;; Skip over `local...in' and continue.
    (forward-word 1)
    (smie-backward-sexp 'halfsexp)
    (tuareg-skip-siblings)))

(defun tuareg-beginning-of-defun ()
  (when (tuareg-find-matching-starter tuareg-starters-syms)
	(save-excursion (tuareg-smie-forward-token)
                        (tuareg-skip-blank-and-comments)
                        (let ((name (tuareg-smie-forward-token)))
                          (if (not (member name '("rec" "type")))
                              name
                            (tuareg-skip-blank-and-comments)
                        (tuareg-smie-forward-token))))))

(defcustom tuareg-max-name-components 3
  "Maximum number of components to use for the current function name."
  :type 'integer)

(defun tuareg-current-fun-name ()
  (save-excursion
    (let ((count tuareg-max-name-components)
          fullname name)
      (end-of-line)
      (while (and (> count 0)
                  (setq name (tuareg-beginning-of-defun)))
        (decf count)
        (setq fullname (if fullname (concat name "." fullname) name))
        ;; Skip all other declarations that we find at the same level.
        (tuareg-skip-siblings))
      fullname)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Error processing

(require 'compile)

;; In some versions of Emacs, the regexps in
;; compilation-error-regexp-alist do not match the error messages when
;; the language is not English.  Hence we add a regexp.
;; FIXME: We should report those cases to bug-gnu-emacs@gnu.org.

(defconst tuareg-error-regexp
  ;; Errors can take forms like:
  ;;   "File "main.ml", line 1154, characters 30-48:\nError: ..."
  ;;   "Raised at file "pervasives.ml", line 22, characters 22-33"
  ;;   "File "main.ml", line 1018, characters 2-2632:\nWarning 8: ..."
  ;; as well as localized variants depending on locale.
  (concat "^\\(Called from \\)?[[:alpha:]][ [:alpha:]]*[[:alpha:]] "
          "\"\\([^\"\n]+\\)\", "                              ;File name.
          "[[:alpha:]]+ \\([0-9]+\\)\\(?:-\\([0-9]+\\)\\)?, " ;Lines.
          "[[:alpha:]]+ \\([0-9]+\\)-\\([0-9]+\\)"            ;Columns.
          "\\(?::\\(\nWarning\\)?\\|[-,:]\\|$\\)")            ;Warning/error.
  "Regular expression matching the error messages produced by ocamlc.")

(defconst tuareg--error-regexp-newstyle
  (concat "^[ A-\377]+ \"\\([^\"\n]+\\)\", line \\([0-9]+\\), "
          "characters \\([0-9]+\\)-\\([0-9]+\\):")
  "Regular expression matching the error messages produced by ocamlc/ocamlopt.")

(when (boundp 'compilation-error-regexp-alist)
  (or (assoc tuareg-error-regexp
             compilation-error-regexp-alist)
      (setq compilation-error-regexp-alist
            (cons (if (fboundp 'compilation-fake-loc)
                      (list tuareg-error-regexp
                            2 '(3 . 4) '(5 . 6) '(7 . 1))
                    (list tuareg-error-regexp 2 3))
                  ;; Other error format used for unhandled match case.
                  (cons '("^Fatal error: exception [^ \n]*(\"\\([^\"]*\\)\", \\([0-9]+\\), \\([0-9]+\\))"
                          1 2 3)
                        compilation-error-regexp-alist))))
  (unless (assoc tuareg--error-regexp-newstyle
                 compilation-error-regexp-alist)
    (setq compilation-error-regexp-alist
          (cons (list tuareg--error-regexp-newstyle 1 2 '(3 . 4))
                compilation-error-regexp-alist))))

;; A regexp to extract the range info.

;; (defconst tuareg-error-chars-regexp
;;   ".*, .*, [^\0-@]+ \\([0-9]+\\)-\\([0-9]+\\):"
;;   "Regexp matching the char numbers in an error message produced by ocamlc.")

;; Wrapper around next-error.

;; itz 04-21-96 instead of defining a new function, use defadvice
;; that way we get our effect even when we do \C-x` in compilation buffer

;; smclaughlin 07-19-11 defadvice is to be avoided.  It makes debugging
;; much more difficult.  If you really want this behavior, write your
;; own next-error-function.  In particular, it breaks when omake is
;; used.

;; (defadvice next-error (after tuareg-next-error activate)
;;  "Read the extra positional information provided by the OCaml compiler.

;; Puts the point and the mark exactly around the erroneous program
;; fragment. The erroneous fragment is also temporarily highlighted if
;; possible."
;;  (when (eq major-mode 'tuareg-mode)
;;    (let ((beg nil) (end nil))
;;      (with-current-buffer compilation-last-buffer
;;        (save-excursion
;;          (goto-char (window-point (get-buffer-window (current-buffer) t)))
;;          (when (looking-at tuareg-error-chars-regexp)
;;            (setq beg (string-to-number (tuareg-match-string 1))
;;                  end (string-to-number (tuareg-match-string 2))))))
;;      (beginning-of-line)
;;      (when beg
;;        (setq beg (+ (point) beg) end (+ (point) end))
;;        (goto-char beg) (push-mark end t t)))))

(autoload 'ocaml-module-alist "caml-help")
(autoload 'ocaml-visible-modules "caml-help")
(autoload 'ocaml-module-symbols "caml-help")

(defun tuareg-completion-at-point ()
  (let ((beg (save-excursion (skip-syntax-backward "w_") (point)))
        (end (save-excursion (skip-syntax-forward "w_") (point)))
        (table
         (lambda (string pred action)
           (let ((dot (string-match "\\.[^.]*\\'" string))
                 ;; ocaml-module-symbols contains an unexplained call to
                 ;; pop-to-buffer within save-window-excursion.  Let's try and
                 ;; avoid it pops up a stupid frame.
                 (display-buffer-alist
                  (cons '("^\\*caml-help\\*$"
                          (display-buffer-reuse-window
                           display-buffer-pop-up-window)
                          (reusable-frames . nil); only the selected frame
                          (window-height . 0.25))
                        display-buffer-alist)))
             (if (eq (car-safe action) 'boundaries)
                 `(boundaries ,(if dot (1+ dot) 0)
                              ,@(string-match "\\." (cdr action)))
               (if (null dot)
                   (complete-with-action
                    action (apply #'append
                                  (mapcar (lambda (mod) (concat (car mod) "."))
                                          (ocaml-module-alist))
                                  (mapcar #'ocaml-module-symbols
                                          (ocaml-visible-modules)))
                    string pred)
                 (completion-table-with-context
                  (substring string 0 (1+ dot))
                  (ocaml-module-symbols
                   (assoc (substring string 0 dot) (ocaml-module-alist)))
                  (substring string (1+ dot)) pred action)))))))
    (unless (or (eq beg end)
                (not tuareg-with-caml-mode-p))
      (list beg end table))))


(autoload 'caml-complete "caml-help")

(defun tuareg-complete (arg)
  "Completes qualified ocaml identifiers."
  (interactive "p")
  (modify-syntax-entry ?_ "w" tuareg-mode-syntax-table)
  (unwind-protect
      (caml-complete arg)
    (modify-syntax-entry ?_ "_" tuareg-mode-syntax-table)))

(defun tuareg--try-find-alternate-file (mod-name extension &optional no-create)
  "Switch to the file given by MOD-NAME and EXTENSION.
If NO-CREATE is non-nil and the file doesn't exist, don't switch and return nil,
otherwise return non-nil."
  (let* ((filename (concat mod-name extension))
         (buffer (get-file-buffer filename))
         (what (cond
                ((string= extension ".ml") "implementation")
                ((string= extension ".mli") "interface"))))
    (cond
     (buffer (switch-to-buffer buffer))
     ((file-exists-p filename) (find-file filename))
     ((and (not no-create)
           (y-or-n-p
            (format "Create %s file %s " what
                    (file-name-nondirectory filename))))
      (find-file filename)))))

(defun tuareg-find-alternate-file ()
  "Switch Implementation/Interface."
  (interactive)
  (let ((name buffer-file-name))
    (when (string-match "\\`\\(.*\\)\\.ml\\([il]\\)?\\'" name)
      (let ((mod-name (tuareg-match-string 1 name))
            (e (tuareg-match-string 2 name)))
        (cond
         ((string= e "i")
            (tuareg--try-find-alternate-file mod-name ".ml"))
         (t
          (tuareg--try-find-alternate-file mod-name ".mli")))))))

(define-skeleton tuareg-insert-class-form
  "Insert a nicely formatted class-end form, leaving a mark after end."
  nil
  \n "class " @ " = object (self)" > \n
  "inherit " > _ " as super" \n "end;;" > \n)

(define-skeleton tuareg-insert-begin-form
  "Insert a nicely formatted begin-end form, leaving a mark after end."
  nil
  \n "begin" > \n _ \n "end" > \n)

(define-skeleton tuareg-insert-for-form
  "Insert a nicely formatted for-to-done form, leaving a mark after done."
  nil
  \n "for " - " do" > \n _ \n "done" > \n)

(define-skeleton tuareg-insert-while-form
  "Insert a nicely formatted for-to-done form, leaving a mark after done."
  nil
  \n "while " - " do" > \n _ \n "done" > \n)

(define-skeleton tuareg-insert-if-form
  "Insert a nicely formatted if-then-else form, leaving a mark after else."
  nil
  \n "if" > \n _ \n "then" > \n @ \n "else" \n @)

(define-skeleton tuareg-insert-match-form
  "Insert a nicely formatted math-with form, leaving a mark after with."
  nil
  \n "match" > \n _ \n "with" > \n)

(define-skeleton tuareg-insert-let-form
  "Insert a nicely formatted let-in form, leaving a mark after in."
  nil
  \n "let " > _ " in" > \n)

(define-skeleton tuareg-insert-try-form
  "Insert a nicely formatted try-with form, leaving a mark after with."
  nil
  \n "try" > \n _ \n "with" > \n)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               OPAM

(defconst tuareg-opam-compilers
  (when (file-directory-p "~/.opam")
    (let ((c (directory-files "~/.opam" t "[0-9]+\\.[0-9]+\\.[0-9]+")))
      (if (file-directory-p "~/.opam/system")
	  (cons "~/.opam/system" c)
	c)))
  "The list of OPAM directories for the installed compilers.")

(defvar tuareg-opam
  (let ((opam (executable-find "opam")))
    (if opam opam
      (let ((opam (locate-file "bin/opam" tuareg-opam-compilers)))
        (if (and opam (file-executable-p opam)) opam)))) ; or nil
  "The full path of the opam executable or `nil' if opam wasn't found.")

(defun tuareg-shell-command-to-string (command)
  "Similar to shell-command-to-string, but returns nil when the
process return code is not 0 (shell-command-to-string returns the
error message as a string)."
  (let* ((return-value 0)
         (return-string
          (with-output-to-string
	    (with-current-buffer standard-output
	      (setq return-value
		    (process-file shell-file-name nil t nil
                                  shell-command-switch command))))))
    (if (= return-value 0) return-string nil)))

(defun tuareg-opam-config-env (&optional switch)
  "Get the opam environment for the given switch (or the default
switch if none is provied) and return a list of lists of the
form (n v) where n is the name of the environment variable and v
its value (both being strings).  If opam is not found or the
switch is not installed, `nil' is returned."
  (let* ((switch (if switch (concat " --switch " switch)))
	 (get-env (concat tuareg-opam " config env --sexp" switch))
	 (opam-env (tuareg-shell-command-to-string get-env)))
    (if opam-env
	(car (read-from-string opam-env)))))

(defun tuareg-opam-installed-compilers ()
  (let* ((cmd1 (concat tuareg-opam " switch list -i -s"))
         (cmd2 (concat tuareg-opam " switch list -s")); opam2
	 (cpl (or (tuareg-shell-command-to-string cmd1)
                  (tuareg-shell-command-to-string cmd2))))
    (if cpl (split-string cpl "[ \f\t\n\r\v]+" t) '())))

(defun tuareg-opam-current-compiler ()
  (let* ((cmd (concat tuareg-opam " switch show -s"))
	 (cpl (tuareg-shell-command-to-string cmd)))
    (when cpl
      (replace-regexp-in-string "[ \t\n]*" "" cpl))))

(defun tuareg-opam-update-env (switch)
  "Update the environment to follow current OPAM switch configuration."
  (interactive
   (let* ((compl (tuareg-opam-installed-compilers))
	  (current (tuareg-opam-current-compiler))
	  (default (if current current "current"))
	  (prompt (format "opam switch (default: %s): " default)))
     (list (completing-read prompt compl))))
  (let* ((switch (if (string= switch "") nil switch))
	 (env (tuareg-opam-config-env switch)))
    (if env
	(dolist (v env)
	  (setenv (car v) (cadr v))
	  (when (string= (car v) "PATH")
	    (setq exec-path (split-string (cadr v) path-separator))))
      (message "Switch %s does not exist (or opam not found)" switch))))


(when (and tuareg-opam-insinuate tuareg-opam)
  (setq tuareg-interactive-program
        (concat tuareg-opam " config exec -- ocaml"))

  ;; OPAM compilation — one must update to the current compiler
  ;; before launching the compilation.
  (defadvice compile (before tuareg-compile-opam activate)
      "Run opam to update environment variables."
      (let* ((env (tuareg-opam-config-env)))
	(when env
	  (set (make-local-variable 'compilation-environment)
	       (mapcar (lambda(v) (concat (car v) "=" (cadr v)))
		       (tuareg-opam-config-env))))))

  (defvar merlin-command)               ;Silence byte-compiler.
  (setq merlin-command 'opam)
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Tuareg interactive mode

;; Augment Tuareg mode with an OCaml toplevel.

(require 'comint)

(defvar tuareg-interactive-mode-map
  (let ((map (copy-keymap comint-mode-map)))
    (define-key map "|" 'tuareg-electric-pipe)
    (define-key map ")" 'tuareg-electric-rp)
    (define-key map "}" 'tuareg-electric-rc)
    (define-key map "]" 'tuareg-electric-rb)
    (define-key map "\C-c\C-i" 'tuareg-interrupt-ocaml)
    (define-key map "\C-c\C-k" 'tuareg-kill-ocaml)
    (define-key map "\C-c`" 'tuareg-interactive-next-error-toplevel)
    (define-key map "\C-c?" 'tuareg-interactive-next-error-toplevel)
    (define-key map [return] 'tuareg-interactive-send-input)
    (define-key map [M-return] 'tuareg-interactive-send-input-end-of-phrase)
    (define-key map [kp-enter] 'tuareg-interactive-send-input-end-of-phrase)
    map))

(defconst tuareg-interactive-buffer-name "*ocaml-toplevel*")

(defconst tuareg-interactive-error-range-regexp
  "[ \t]*Characters \\([0-9]+\\)-\\([1-9][0-9]*\\):\n"
  "Regexp matching the char numbers in OCaml toplevel's error messages.")

(defconst tuareg-interactive-error-regexp
  "\n\\(Error: [^#]*\\)")

(defconst tuareg-interactive-exception-regexp
  "\\(Exception: [^#]*\\)")

(defvar tuareg-interactive-last-phrase-pos-in-source 0)

(defvar tuareg-interactive-last-phrase-pos-in-toplevel 0)

(defun tuareg-interactive-filter (_text)
  (when (eq major-mode 'tuareg-interactive-mode)
    (save-excursion
      (when (>= comint-last-input-end comint-last-input-start)
        (when tuareg-interactive-read-only-input
          (add-text-properties
           comint-last-input-start comint-last-input-end
           (list 'read-only t)))
        (when (and font-lock-mode tuareg-interactive-input-font-lock)
          (font-lock-fontify-region comint-last-input-start
                                    comint-last-input-end))
        (when tuareg-interactive-output-font-lock
          (save-excursion
            (goto-char (point-max))
            (re-search-backward comint-prompt-regexp
                                comint-last-input-end t)
            (add-text-properties
             comint-last-input-end (point)
             '(font-lock-face tuareg-font-lock-interactive-output-face))))
        (when tuareg-interactive-error-font-lock
          (save-excursion
            (goto-char comint-last-input-end)
            (cond
             ((looking-at tuareg-interactive-error-range-regexp)
              (let ((beg (string-to-number (tuareg-match-string 1)))
                    (end (string-to-number (tuareg-match-string 2))))
                (put-text-property
                 (+ comint-last-input-start beg)
                 (+ comint-last-input-start end)
                 'font-lock-face 'tuareg-font-lock-error-face))
              (goto-char comint-last-input-end)
              (when (re-search-forward tuareg-interactive-error-regexp nil t)
                (let ((errbeg (match-beginning 1))
                      (errend (match-end 1)))
                (put-text-property
                 errbeg errend
                 'font-lock-face 'tuareg-font-lock-interactive-error-face))))
             ((looking-at tuareg-interactive-exception-regexp)
              (let ((errbeg (match-beginning 1))
                    (errend (match-end 1)))
                (put-text-property
                 errbeg errend
                 'font-lock-face 'tuareg-font-lock-interactive-error-face)))
             )))))))

(easy-menu-define
  tuareg-interactive-mode-menu tuareg-interactive-mode-map
  "Tuareg Interactive Mode Menu."
  '("Tuareg"
    ("Interactive Mode"
     ["Run OCaml Toplevel" tuareg-run-ocaml t]
     ["Interrupt OCaml Toplevel" tuareg-interrupt-ocaml
      :active (comint-check-proc tuareg-interactive-buffer-name)]
     ["Kill OCaml Toplevel" tuareg-kill-ocaml
      :active (comint-check-proc tuareg-interactive-buffer-name)]
     ["Evaluate Region" tuareg-eval-region :active (region-active-p)]
     ["Evaluate Phrase" tuareg-eval-phrase t]
     ["Evaluate Buffer" tuareg-eval-buffer t])
    "---"
    ["Customize Tuareg Mode..." (customize-group 'tuareg) t]
    ("Tuareg Options" ["Dummy" nil t])
    ("Tuareg Interactive Options" ["Dummy" nil t])
    "---"
    ["About" tuareg-about t]
    ["Help" tuareg-interactive-help t]))

(define-derived-mode tuareg-interactive-mode comint-mode "Tuareg-Interactive"
  "Major mode for interacting with an OCaml process.
Runs an OCaml toplevel as a subprocess of Emacs, with I/O through an
Emacs buffer. A history of input phrases is maintained. Phrases can
be sent from another buffer in tuareg mode.

Short cuts for interactions with the toplevel:
\\{tuareg-interactive-mode-map}"
  (add-hook 'comint-output-filter-functions 'tuareg-interactive-filter)
  (setq comint-prompt-regexp "^#  *")
  (setq comint-process-echoes nil)
  (setq comint-get-old-input 'tuareg-interactive-get-old-input)
  (setq comint-scroll-to-bottom-on-output
        tuareg-interactive-scroll-to-bottom-on-output)
  (set-syntax-table tuareg-mode-syntax-table)
  (set (make-local-variable 'comment-start) "(* ")
  (set (make-local-variable 'comment-end) " *)")
  (set (make-local-variable 'comment-start-skip) "(\\*+[ \t]*")
  (set (make-local-variable 'comint-prompt-read-only) t)

  (tuareg--common-mode-setup)
  (when (or tuareg-interactive-input-font-lock
            tuareg-interactive-output-font-lock
            tuareg-interactive-error-font-lock)
    (font-lock-mode 1))
  (unless tuareg-use-smie
    (display-warning
     'tuareg "SMIE not enabled, some things may not work as expected."))

  (easy-menu-add tuareg-interactive-mode-menu)
  (tuareg-update-options-menu))

;;;###autoload
(defun tuareg-run-ocaml ()
  "Run an OCaml toplevel process.  I/O via buffer `*ocaml-toplevel*'."
  (interactive)
  (tuareg-run-process-if-needed)
  (display-buffer tuareg-interactive-buffer-name))

;;;###autoload
(defalias 'run-ocaml 'tuareg-run-ocaml)

;;;###autoload
(add-to-list 'interpreter-mode-alist '("ocamlrun" . tuareg-mode))
;;;###autoload
(add-to-list 'interpreter-mode-alist '("ocaml" . tuareg-mode))

(defun tuareg-run-process-if-needed (&optional cmd)
  "Run an OCaml toplevel process if needed, with an optional command name.
I/O via buffer `*ocaml-toplevel*'."
  (if cmd
      (setq tuareg-interactive-program cmd)
    (unless (comint-check-proc tuareg-interactive-buffer-name)
      (setq tuareg-interactive-program
            (read-shell-command "OCaml toplevel to run: "
                                tuareg-interactive-program))))
  (unless (comint-check-proc tuareg-interactive-buffer-name)
    (let ((cmdlist (tuareg--split-args tuareg-interactive-program))
          (process-connection-type nil))
      (set-buffer (apply (function make-comint) "ocaml-toplevel"
                         (car cmdlist) nil (cdr cmdlist)))
      (tuareg-interactive-mode)
      (sleep-for 1))))

(defun tuareg--split-args (args)
  (condition-case nil
      (split-string-and-unquote args)
      (error (progn
               (message "Arguments ‘%s’ ill quoted.  Ignored." args)
               nil))))

(defun tuareg-interactive-get-old-input ()
  (save-excursion
    (let ((end (point)))
      (re-search-backward comint-prompt-regexp (point-min) t)
      (when (looking-at comint-prompt-regexp)
        (re-search-forward comint-prompt-regexp))
      (buffer-substring-no-properties (point) end))))


(defconst tuareg-interactive--send-warning
  "Note: toplevel processing requires a terminating `;;'")

(defun tuareg-interactive--indent-line ()
  (insert "\n")
  (indent-according-to-mode)
  (message tuareg-interactive--send-warning))

(when tuareg-use-smie
  (defun tuareg-interactive-send-input ()
    "Send the current phrase to the OCaml toplevel or insert a newline.
If the point is next to \";;\", the phrase is sent to the toplevel,
otherwise a newline is inserted and the lines are indented."
    (interactive)
    (cond
     ((tuareg-in-literal-or-comment-p) (tuareg-interactive--indent-line))
     ((or (equal ";;" (save-excursion (caddr (smie-backward-sexp))))
          (looking-at "[ \t\n\r]*;;"))
      (comint-send-input))
     (t (tuareg-interactive--indent-line))))

  (defun tuareg-interactive-send-input-end-of-phrase ()
    (interactive)
    (goto-char (point-max))
    (unless (equal ";;" (save-excursion (caddr (smie-backward-sexp))))
      (insert ";;"))
    (comint-send-input))
  )

(defun tuareg-interactive--send-region (start end)
  "Send the region between `start' and `end' to the OCaml toplevel.
It is assumed that the range `start'-`end' delimit valid OCaml phrases."
  (save-excursion (tuareg-run-process-if-needed))
  (comint-preinput-scroll-to-bottom)
  (let* ((phrases (buffer-substring-no-properties start end))
         (phrases-colon (concat phrases ";;")))
    (if (string= phrases "")
        (message "Cannot send empty commands to OCaml toplevel!")
      (with-current-buffer tuareg-interactive-buffer-name
        (goto-char (point-max))
        (setq tuareg-interactive-last-phrase-pos-in-toplevel (point))
        (comint-send-string tuareg-interactive-buffer-name phrases-colon)
        (let ((pos (point)))
          (comint-send-input)
          (when tuareg-interactive-echo-phrase
            (save-excursion
              (goto-char pos)
              (insert phrases-colon)))))))
  (when tuareg-display-buffer-on-eval
    (display-buffer tuareg-interactive-buffer-name)))

(defun tuareg-eval-region (start end)
  "Eval the current region in the OCaml toplevel."
  (interactive "r")
  (setq tuareg-interactive-last-phrase-pos-in-source start)
  (save-excursion
    (goto-char start)
    (setq start (car (tuareg-discover-phrase)))
    (goto-char end)
    (setq end (cadr (tuareg-discover-phrase)))
    (tuareg-interactive--send-region start end)))

(defun tuareg-narrow-to-phrase ()
  "Narrow the editting window to the surrounding OCaml phrase (or block)."
  (interactive)
  (save-excursion
    (let ((pair (tuareg-discover-phrase)))
      (narrow-to-region (nth 0 pair) (nth 1 pair)))))

(defun tuareg-eval-phrase ()
  "Eval the surrounding OCaml phrase (or block) in the Caml toplevel."
  (interactive)
  (let ((end))
    (save-excursion
      (let ((pair (tuareg-discover-phrase)))
        (setq end (nth 2 pair))
        (tuareg-interactive--send-region (nth 0 pair) (nth 1 pair))))
    (when tuareg-skip-after-eval-phrase
      (goto-char end)
      (tuareg--skip-double-colon)
      (tuareg-skip-blank-and-comments))))

(defun tuareg-eval-buffer ()
  "Send the buffer to the Tuareg Interactive process."
  (interactive)
  (tuareg-interactive--send-region (point-min) (point-max)))

(defvar tuareg-interactive-next-error-olv (make-overlay 1 1))

(overlay-put tuareg-interactive-next-error-olv
             'face 'tuareg-font-lock-error-face)

(delete-overlay tuareg-interactive-next-error-olv)

(defun tuareg-interactive-next-error-source ()
  (interactive)
  (let ((error-pos) (beg 0) (end 0))
    (with-current-buffer tuareg-interactive-buffer-name
      (goto-char tuareg-interactive-last-phrase-pos-in-toplevel)
      (setq error-pos
            (re-search-forward tuareg-interactive-error-range-regexp
                               (point-max) t))
      (when error-pos
        (setq beg (string-to-number (tuareg-match-string 1))
              end (string-to-number (tuareg-match-string 2)))))
    (if (not error-pos)
        (message "No syntax or typing error in last phrase.")
      (setq beg (+ tuareg-interactive-last-phrase-pos-in-source beg)
            end (+ tuareg-interactive-last-phrase-pos-in-source end))
      (goto-char beg)
      (move-overlay tuareg-interactive-next-error-olv beg end)
      (unwind-protect
          (sit-for 60 t)
        (delete-overlay tuareg-interactive-next-error-olv))
      )))

(defun tuareg-interactive-next-error-toplevel ()
  (interactive)
  (let ((error-pos) (beg 0) (end 0))
    (save-excursion
      (goto-char tuareg-interactive-last-phrase-pos-in-toplevel)
      (setq error-pos
            (re-search-forward tuareg-interactive-error-range-regexp
                               (point-max) t))
      (when error-pos
        (setq beg (string-to-number (tuareg-match-string 1))
              end (string-to-number (tuareg-match-string 2)))))
    (if (not error-pos)
        (message "No syntax or typing error in last phrase.")
      (setq beg (+ tuareg-interactive-last-phrase-pos-in-toplevel beg)
            end (+ tuareg-interactive-last-phrase-pos-in-toplevel end))
      (move-overlay tuareg-interactive-next-error-olv beg end)
      (unwind-protect
          (sit-for 60 t)
        (delete-overlay tuareg-interactive-next-error-olv))
      (goto-char beg))))

(defun tuareg-interrupt-ocaml ()
  (interactive)
  (when (comint-check-proc tuareg-interactive-buffer-name)
    (with-current-buffer tuareg-interactive-buffer-name
      (comint-interrupt-subjob))))

(defun tuareg-kill-ocaml ()
  (interactive)
  (when (comint-check-proc tuareg-interactive-buffer-name)
    (with-current-buffer tuareg-interactive-buffer-name
      (comint-kill-subjob))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Menu support

(defun tuareg-about ()
  (interactive)
  (describe-variable 'tuareg-mode-version))

(defun tuareg-short-cuts ()
  "Short cuts for the Tuareg mode:
\\{tuareg-mode-map}

Short cuts for interaction within the toplevel:
\\{tuareg-interactive-mode-map}"
  (interactive)
  (describe-function 'tuareg-short-cuts))

(defun tuareg-help ()
  (interactive)
  (describe-function 'tuareg-mode))

(defun tuareg-interactive-help ()
  (interactive)
  (describe-function 'tuareg-interactive-mode))

(defvar tuareg-definitions-menu (list ["Scan..." tuareg-list-definitions t])
  "Initial content of the definitions menu.")
(make-variable-buffer-local 'tuareg-definitions-menu)

(defvar tuareg-definitions-menu-last-buffer nil)

(defvar tuareg-definitions-keymaps nil)

(defun tuareg-build-menu ()
  (easy-menu-define
   tuareg-mode-menu (list tuareg-mode-map)
   "Tuareg Mode Menu."
   '("Tuareg"
     ("Interactive Mode"
      ["Run OCaml Toplevel" tuareg-run-ocaml t]
      ["Interrupt OCaml Toplevel" tuareg-interrupt-ocaml
       :active (comint-check-proc tuareg-interactive-buffer-name)]
      ["Kill OCaml Toplevel" tuareg-kill-ocaml
       :active (comint-check-proc tuareg-interactive-buffer-name)]
      ["Evaluate Region" tuareg-eval-region
       ;; Region-active-p for XEmacs and mark-active for Emacs
       :active mark-active]
      ["Evaluate Phrase" tuareg-eval-phrase t]
      ["Evaluate Buffer" tuareg-eval-buffer t])
     ("OCaml Forms"
      ["try .. with .." tuareg-insert-try-form t]
      ["match .. with .." tuareg-insert-match-form t]
      ["let .. in .." tuareg-insert-let-form t]
      ["if .. then .. else .." tuareg-insert-if-form t]
      ["while .. do .. done" tuareg-insert-while-form t]
      ["for .. do .. done" tuareg-insert-for-form t]
      ["begin .. end" tuareg-insert-begin-form t])
     ["Switch .ml/.mli" tuareg-find-alternate-file t]
     "---"
     ["Compile..." compile t]
     ["Reference Manual..." tuareg-browse-manual t]
     ["OCaml Library..." tuareg-browse-library t]
     ("Definitions"
      ["Scan..." tuareg-list-definitions t])
     "---"
     [ "Show type at point" caml-types-show-type
       tuareg-with-caml-mode-p]
     [ "Show fully qualified ident at point" caml-types-show-ident
       tuareg-with-caml-mode-p]
     [ "Show the kind of call at point" caml-types-show-call
       tuareg-with-caml-mode-p]
     "---"
     [ "Complete identifier" caml-complete
       tuareg-with-caml-mode-p]
     [ "Help for identifier" caml-help
       tuareg-with-caml-mode-p]
     [ "Add path for documentation" ocaml-add-path
       tuareg-with-caml-mode-p]
     [ "Open module for documentation" ocaml-open-module
       tuareg-with-caml-mode-p]
     [ "Close module for documentation" ocaml-close-module
       tuareg-with-caml-mode-p]
     "---"
     ["Customize Tuareg Mode..." (customize-group 'tuareg) t]
     ("Tuareg Options" ["Dummy" nil t])
     ("Tuareg Interactive Options" ["Dummy" nil t])
     "---"
     ["About" tuareg-about t]
     ["Short Cuts" tuareg-short-cuts]
     ["Help" tuareg-help t]))
  (easy-menu-add tuareg-mode-menu)
  (tuareg-update-options-menu))

(defun tuareg-update-definitions-menu ()
  (when (eq major-mode 'tuareg-mode)
    (easy-menu-change
     '("Tuareg") "Definitions"
     tuareg-definitions-menu)))

(defun tuareg-toggle-option (symbol)
  (interactive)
  (set symbol (not (symbol-value symbol)))
  (when (eq 'tuareg-use-abbrev-mode symbol)
    (abbrev-mode tuareg-use-abbrev-mode)) ; toggle abbrev minor mode
  (tuareg-update-options-menu))

(defun tuareg-update-options-menu ()
  (easy-menu-change
   '("Tuareg") "Tuareg Options"
   (mapcar (lambda (pair)
             (if (consp pair)
                 (vector (car pair)
                         (list 'tuareg-toggle-option (cdr pair))
                         ':style 'toggle
                         ':selected (nth 1 (cdr pair))
                         ':active t)
               pair)) tuareg-options-list))
  (easy-menu-change
   '("Tuareg") "Tuareg Interactive Options"
   (mapcar (lambda (pair)
             (if (consp pair)
                 (vector (car pair)
                         (list 'tuareg-toggle-option (cdr pair))
                         ':style 'toggle
                         ':selected (nth 1 (cdr pair))
                         ':active t)
               pair)) tuareg-interactive-options-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Browse Manual

;; From M. Quercia

(defun tuareg-browse-manual ()
  "*Browse OCaml reference manual."
  (interactive)
  (setq tuareg-manual-url (read-from-minibuffer "URL: " tuareg-manual-url))
  (funcall tuareg-browser tuareg-manual-url))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Browse Library

;; From M. Quercia

(defvar tuareg-library-mode-map
  (let ((map (make-keymap)))
    (suppress-keymap map)
    (define-key map [return] 'tuareg-library-find-file)
    (define-key map [mouse-2] 'tuareg-library-mouse-find-file)
    map))

(defun tuareg-browse-library ()
  "Browse the OCaml library."
  (interactive)
  (let ((buf-name "*ocaml-library*") (opoint)
        (dir (read-from-minibuffer "Library path: " tuareg-library-path)))
    (when (and (file-directory-p dir) (file-readable-p dir))
      (setq tuareg-library-path dir)
      ;; List *.ml and *.mli files
      (with-output-to-temp-buffer buf-name
        (buffer-disable-undo standard-output)
        (with-current-buffer buf-name
          (kill-all-local-variables)
          (set (make-local-variable 'tuareg-library-path) dir)
          ;; Help
          (insert "Directory \"" dir "\".\n")
          (insert "Select a file with middle mouse button or RETURN.\n\n")
          (insert "Interface files (.mli):\n\n")
          (insert-directory (concat dir "/*.mli") "-C" t nil)
          (insert "\n\nImplementation files (.ml):\n\n")
          (insert-directory (concat dir "/*.ml") "-C" t nil)
          ;; '.', '-' and '_' are now letters
          (modify-syntax-entry ?. "w")
          (modify-syntax-entry ?_ "w")
          (modify-syntax-entry ?- "w")
          ;; Every file name is now mouse-sensitive
          (goto-char (point-min))
          (while (< (point) (point-max))
            (re-search-forward "\\.ml.?\\>")
            (setq opoint (point))
            (re-search-backward "\\<" (point-min) 1)
            (put-text-property (point) opoint 'mouse-face 'highlight)
            (goto-char (+ 1 opoint)))
          ;; Activate tuareg-library mode
          (setq major-mode 'tuareg-library-mode)
          (setq mode-name "tuareg-library")
          (use-local-map tuareg-library-mode-map)
          (setq buffer-read-only t))))))

(defun tuareg-library-find-file ()
  "Load the file whose name is near point."
  (interactive)
  (when (text-properties-at (point))    ;FIXME: Why??
    (save-excursion
      (let (beg)
        (re-search-backward "\\<") (setq beg (point))
        (re-search-forward "\\>")
        (find-file-read-only (expand-file-name (buffer-substring-no-properties
                                                beg (point))
                                               tuareg-library-path))))))

(defun tuareg-library-mouse-find-file (event)
  "Visit the file name you click on."
  (interactive "e")
  (let ((owindow (selected-window)))
    (mouse-set-point event)
    (tuareg-library-find-file)
    (select-window owindow)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Definitions List

;; Designed from original code by M. Quercia

(defconst tuareg--id-regexp "[[:alpha:]][_'[:alnum:]]*")

(defconst tuareg-definitions-regexp
  (regexp-opt '("and" "val" "type" "module" "class" "exception" "let") 'words)
  "Regexp matching definition phrases.")

(defconst tuareg-definitions-bind-skip-regexp
  (concat (regexp-opt '("rec" "type" "virtual") 'words) "\\|'"
          tuareg--id-regexp "\\|('.*)")
  "Regexp matching stuff to ignore after a binding keyword.")

(defconst tuareg-identifier-regexp (concat "\\<" tuareg--id-regexp "\\>"))

(defmacro tuareg-reset-and-kwop (kwop)
  `(when (and ,kwop (string= ,kwop "and"))
     (setq ,kwop (tuareg-find-and-match)))) ;FIXME: In tuareg_indent.el!

(defun tuareg-imenu-create-index ()
  (let ((cpt (if (fboundp 'make-progress-reporter)
                 (make-progress-reporter "Searching definitions..."
                                         (point-min) (point-max))
               0))
        (kw) (value-list) (type-list) (module-list) (class-list) (misc-list))
    (goto-char (point-min))
    (tuareg-skip-blank-and-comments)
    (while (not (eobp))
      (when (looking-at tuareg-definitions-regexp)
        (setq kw (tuareg-match-string 0))
        (save-match-data (tuareg-reset-and-kwop kw))
        (when (member kw '("exception" "val"))
          (setq kw "let"))
        ;; Skip optional elements
        (goto-char (match-end 0))
        (tuareg-skip-blank-and-comments)
        (when (looking-at tuareg-definitions-bind-skip-regexp)
          (goto-char (match-end 0)))
        (tuareg-skip-blank-and-comments)
        (when (looking-at tuareg-identifier-regexp)
          (let ((ref (cons (tuareg-match-string 0) (point-marker))))
            (if (not (integerp cpt))
                (progress-reporter-update cpt (point))
              (setq cpt (1+ cpt))
              (message "Searching definitions... (%d)" cpt))
            (cond ((string= kw "let")
                   (setq value-list (cons ref value-list)))
                  ((string= kw "type")
                   (setq type-list (cons ref type-list)))
                  ((string= kw "module")
                   (setq module-list (cons ref module-list)))
                  ((string= kw "class")
                   (setq class-list (cons ref class-list)))
                  (t (setq misc-list (cons ref misc-list)))))))
      ;; Skip to next phrase or next top-level `and'
      (goto-char (1+ (point)))          ;Don't signal error at EOB.
      (let ((old-point (point))
            ;; FIXME: tuareg-next-phrase is in tuareg_indent.el!
            (last-and (progn (tuareg-next-phrase t t) (point))))
        (if (< last-and old-point)
            (progn
              (message "¡tuareg-next-phrase moved backward from %S!" old-point)
              (goto-char old-point))
          (save-excursion
            (while (and (re-search-backward "\\<and\\>" old-point t)
                        (not (tuareg-in-literal-or-comment-p))
                        ;; FIXME: Only defined in tuareg_indent.el!
                        (save-excursion (tuareg-find-and-match)
                                        (>= old-point (point))))
              (setq last-and (point))))
          (goto-char last-and))))
    (if (integerp cpt)
        (message "Searching definitions... done")
      (progress-reporter-done cpt))
    (let ((index ()))
      (when module-list (push (cons "Modules" module-list) index))
      (when type-list   (push (cons "Types" type-list) index))
      (when class-list  (push (cons "Classes" class-list) index))
      (when value-list  (push (cons "Values" value-list) index))
      (when misc-list   (push (cons "Miscellaneous" misc-list) index))
      index)))

(defun tuareg-list-definitions ()
  "Parse the buffer and gather toplevel definitions
for a quick jump via the definitions menu."
  ;; FIXME: Why not just use the standard imenu menu?
  (interactive)
  (let ((defs (save-excursion (tuareg-imenu-create-index)))
        menu)
    ;; Sort and build lists
    (dolist (pair defs)
      (let ((entries (mapcar (lambda (elem)
                               (vector (car elem)
                                       (list 'tuareg-goto (cdr elem))
                                       t))
                             (cdr pair))))
        (setq menu
              (append (tuareg-split-long-list
                       (car pair) (tuareg-sort-definitions entries))
                      menu))))
    ;; Update definitions menu
    (setq tuareg-definitions-menu
          (append menu (list "---"
                             ["Rescan..." tuareg-list-definitions t]))))
  (tuareg-update-definitions-menu))

(defun tuareg-goto (pos)
  (goto-char pos)
  (recenter))

(defun tuareg-sort-definitions (list)
  (let* ((last "") (cpt 1)
         (list (sort (nreverse list)    ;FIXME: Why reverse before sorting?
                     (lambda (p q) (string< (elt p 0) (elt q 0)))))
         (tail list))
    (while tail
      (if (string= (elt (car tail) 0) last)
          (progn
            (setq cpt (1+ cpt))
            (aset (car tail) 0 (format "%s (%d)" last cpt)))
        (setq cpt 1)
        (setq last (elt (car tail) 0)))
      (setq tail (cdr tail)))
    list))

;; Split a definition list if it is too long
(defun tuareg-split-long-list (title list)
  (let ((tail (nthcdr tuareg-definitions-max-items list)))
    (if (null (cdr tail))
        ;; List not too long, cons the title
        (list (cons title list))
      ;; List too long, split and add initials to the title
      (let (lists)
        (while list
          (let ((beg (substring (elt (car list) 0) 0 1))
                (end (substring (elt (car (or tail (last list))) 0) 0 1)))
            (push (cons (format "%s %s-%s" title beg end) list)
                  lists)
            (setq list (cdr tail))
	    (when tail
	      (setcdr tail nil)
	      (setq tail (nthcdr tuareg-definitions-max-items list)))))
        (nreverse lists)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Hooks and Exit

(eval-when-compile
  (autoload 'speedbar-add-supported-extension "speedbar"))

(when (require 'speedbar nil t)
  (speedbar-add-supported-extension
   '(".ml" ".mli" ".mll" ".mly" ".mlp" ".ls")))

(provide 'tuareg)

;; Pre-SMIE indentation functions.
;; Load it after providing `tuareg' to avoid circular dependencies.
(if t (require 'tuareg_indent))         ;Don't load during compilation.

;; For compatibility with caml support modes
;; you may also link caml.el to tuareg.el
(provide 'caml)

;;; tuareg.el ends here
