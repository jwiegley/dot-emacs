;;;; -*- emacs-lisp -*-
;;;
;;; Copyright (C) 2003, 2004 Lars Brinkhoff.
;;; Functions for loading and compiling the whole system.
;;; Loading this file also loads the system as a side effect.

(require 'cl)
(require 'byte-compile "bytecomp")

(setq max-lisp-eval-depth 10000)
(setq max-specpdl-size 10000)

;;; Fake IN-PACKAGE and FIND-PACKAGE until they are defined properly
;;; in cl-packages.el.
(defmacro IN-PACKAGE (name) nil)
(defun FIND-PACKAGE (name) nil)

(unless (fboundp 'cl-mapcar-many)
  (fset 'cl-mapcar-many (symbol-function 'cl--mapcar-many)))

(defvar *cl-files*
  '("utils"
    "func"

    "cl-evaluation"
    "cl-flow"
    "cl-numbers"
    "cl-conses"
    "cl-characters"
    "cl-strings"
    "cl-arrays"
    "cl-sequences"
    "cl-structures"
    "cl-iteration"

    "cl-symbols"
    "cl-packages"

    "cl-types"
    "cl-typep"
    "cl-subtypep"

    "cl-hash"
    "cl-streams"
    "cl-reader"
    "cl-printer"
    "cl-environment"
    "cl-filenames"
    "cl-files"
    "interaction"
    "cl-eval"
    "cl-system"

    "cl-loop"
    "cl-format"
    "cl-compile"
    "cl-objects"
    "cl-conditions"

    "populate"))

(defun load-cl ()
  (interactive)
  (let ((load-path (cons (file-name-directory load-file-name) load-path))
	(debug-on-error t)
	(byte-compile-warnings nil))
    (mapc #'load *cl-files*)
    (populate-packages)
    (garbage-collect)))

(defun compile-cl ()
  (interactive)
  (let ((byte-compile-warnings '(not cl-functions)))
    (dolist (file *cl-files*)
      (byte-compile-file (concat file ".el")))))

(when (string-match "^19" emacs-version)
  (dolist (x '(:required :optional-rest :weakness :type :read-only
	       :constituent :whitespace :single-escape
	       :multiple-escape :terminating-macro
	       :non-terminating-macro :eof :special-operator
	       :lexical :special :macro :symbol-macro))
    (set x x)))

(setq *global-environment*
      (vector 'environment
	      ;; Variable information
	      nil nil nil
	      ;; Function information
	      nil nil nil
	      ;; Block and tagbody information
	      nil nil))

(load-cl)
(IN-PACKAGE "CL-USER")
