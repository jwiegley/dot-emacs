;; proof.el  Proof General loader.  All files require this one.
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; Thanks to Rod Burstall, Martin Hofmann,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens
;;   for helpful comments and code.
;;
;; $Id$
;;

(require 'proof-site)			; site config

(require 'proof-config)			; configuration variables

(require 'proof-splash)			; splash screen

;; FIXME da: I think these should all be autoloaded!!
;; (require 'cl)
;; (require 'compile)
;; (require 'comint)
;; (require 'etags)			
;; (require 'easymenu)

;; browse-url function doesn't seem to be autoloaded in
;; XEmacs 20.4, but it is in FSF Emacs 20.2.
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

;;; Autoloads for main code

(autoload 'proof-mode "proof-script"
  "Proof General major mode class for proof scripts.")

(autoload 'proof-shell-mode "proof-shell"
  "Proof General shell mode class for proof assistant processes")

(if (featurep 'toolbar)
    (autoload 'proof-toolbar-setup "proof-toolbar"
      "Initialize Proof General and enable it for the current buffer" t))

;;;
;;; Utilities/macros used in several files  (proof-utils)
;;;

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq-default var value)))

(defun proof-string-to-list (s separator) 
  "Return the list of words in S separated by SEPARATOR."
  (let ((end-of-word-occurence (string-match (concat separator "+") s)))
    (if (not end-of-word-occurence)
        (if (string= s "") 
            nil
          (list s))
      (cons (substring s 0 end-of-word-occurence) 
            (proof-string-to-list 
             (substring s
                        (string-match (concat "[^" separator "]")
                                      s end-of-word-occurence)) separator)))))

(defun proof-define-keys (map kbl)
  "Adds keybindings KBL in MAP.
The argument KBL is a list of tuples (k . f) where `k' is a keybinding
(vector) and `f' the designated function."
  (mapcar
   (lambda (kbl)
     (let ((k (car kbl)) (f (cdr kbl)))
         (define-key map k f)))
   kbl))

;;;
;;; Global variables
;;;

(deflocal proof-buffer-type nil 
  "Symbol indicating the type of this buffer: 'script, 'shell, or 'pbp.")

(defvar proof-shell-busy nil 
  "A lock indicating that the proof shell is processing.
When this is non-nil, proof-shell-ready-prover will give
an error.")

(defvar proof-included-files-list nil 
  "List of files currently included in proof process.
Whenever a new file is being processed, it gets added to the front of
the list. When the prover retracts across file boundaries, this list
is resynchronised. It contains files in canonical truename format")

(defvar proof-script-buffer-list nil
  "Scripting buffers with locked regions.
The first element is current and in scripting minor mode.
The cdr of the list of corresponding file names is a subset of
`proof-included-files-list'.")

(defvar proof-shell-buffer nil
  "Process buffer where the proof assistant is run.")

(defvar proof-pbp-buffer nil
  "The goals buffer (also known as the pbp buffer).")

(defvar proof-response-buffer nil
  "The response buffer.")

(defvar proof-shell-proof-completed nil
  "Flag indicating that a completed proof has just been observed.")

;; FIXME da: remove proof-terminal-string.  At the moment some
;; commands need to have the terminal string, some don't.
;; It's used variously in proof-script and proof-shell.
;; We should assume commands are terminated at the specific level.

(defvar proof-terminal-string nil 
  "End-of-line string for proof process.")




(provide 'proof)
;; proof.el ends here
