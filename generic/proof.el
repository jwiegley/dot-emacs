;; proof.el  Proof General basic functions.  All files require this one.
;;
;; Copyright (C) 1998-2000 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 `(progn
    (defvar ,var nil ,docstring)
    (make-variable-buffer-local (quote ,var))
    (setq-default ,var ,value)))

(require 'proof-site)			; site config

;; cl is dumped with my XEmacs 20.4, but not FSF Emacs 20.2.
;; would rather it was autoloaded but autoloads broken in FSF.
(require 'cl)				

(require 'proof-config)			; configuration variables

(require 'proof-splash)			; display splash screen

;;;
;;; Emacs libraries
;;;

;; browse-url function doesn't seem to be autoloaded in
;; XEmacs 20.4, but it is in FSF Emacs 20.2.
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

;; These are internal functions of font-lock
(autoload 'font-lock-set-defaults "font-lock")
(autoload 'font-lock-fontify-region "font-lock")
(autoload 'font-lock-append-text-property "font-lock")


;;; FIXME: autoloads should be automatic!!

;;;
;;; Autoloads for main code
;;;

(autoload 'proof-mode "proof-script"
  "Proof General major mode class for proof scripts.")

(autoload 'proof-shell-mode "proof-shell"
  "Proof General shell mode class for proof assistant processes")

;; Toolbar defines scripting menu as well as toolbar, so FSF *does*
;; need to load it.  We could consider separating menu code from
;; proof-toolbar, but they are defined using a uniform mechanism.

(autoload 'proof-toolbar-setup "proof-toolbar"
 "Initialize Proof General toolbar and enable it for the current buffer" t)


;;;
;;; More autoloads to help define interface between files
;;;

(autoload 'proof-shell-available-p "proof-shell"
  "Returns non-nil if there is a proof shell active and available.")

(autoload 'proof-shell-invisible-command "proof-shell"
  "Send CMD to the proof process without revealing it to the user.")

(autoload 'proof-x-symbol-toggle "proof-x-symbol"
  "Toggle support for x-symbol.  With optional ARG, force on if ARG<>0."
  t)

(autoload 'proof-x-symbol-decode-region "proof-x-symbol"
  "Call (x-symbol-decode-region START END), if x-symbol support is enabled.")

(autoload 'proof-x-symbol-shell-config "proof-x-symbol"
  "Activate/deactivate x-symbol in Proof General shell, goals, and response buffer.")

(autoload 'proof-x-symbol-mode "proof-x-symbol"
  "Turn on or off x-symbol mode in the current buffer.")

(autoload 'proof-x-symbol-configure "proof-x-symbol"
  "Configure the current buffer for X-Symbol.")


;;;
;;; Global variables
;;;

; rough test for XEmacs on win32
(defconst proof-running-on-win32 (fboundp 'win32-long-file-name)
  "Non-nil if we're running on a win32 system.")

(deflocal proof-buffer-type nil 
  "Symbol indicating the type of this buffer: 'script, 'shell, 'pbp, or 'response.")

(defvar proof-shell-busy nil 
  "A lock indicating that the proof shell is processing.
When this is non-nil, proof-shell-ready-prover will give
an error.")

(defvar proof-included-files-list nil 
  "List of files currently included in proof process.
This list contains files in canonical truename format
(see `file-truename').

Whenever a new file is being processed, it gets added to this list
via the proof-shell-process-file configuration settings.
When the prover retracts a file, this list is resynchronised via the
proof-shell-retract-files-regexp and proof-shell-compute-new-files-list 
configuration settings.

Only files which have been *fully* processed should be included here.
Proof General itself will automatically add the filenames of a script
buffer which has been completely read when scripting is deactivated.
It will automatically remove the filename of a script buffer which
is completely unread when scripting is deactivated.

NB: Currently there is no generic provision for removing files which
are only partly read-in due to an error, so ideally the proof assistant
should only output a processed message when a file has been successfully
read.")


(defvar proof-script-buffer nil
  "The currently active scripting buffer or nil if none.")

(defvar proof-shell-buffer nil
  "Process buffer where the proof assistant is run.")

(defvar proof-goals-buffer nil
  "The goals buffer (also known as the pbp buffer).")

(defvar proof-response-buffer nil
  "The response buffer.")

(defvar proof-shell-error-or-interrupt-seen nil
  "Flag indicating that an error or interrupt has just occurred.
Set to 'error or 'interrupt if one was observed from the proof 
assistant during the last group of commands.")

(defvar proof-shell-proof-completed nil
  "Flag indicating that a completed proof has just been observed.
If non-nil, the value counts the commands from the last command
of the proof (starting from 1).")

;; FIXME da: remove proof-terminal-string.  At the moment some
;; commands need to have the terminal string, some don't.
;; It's used variously in proof-script and proof-shell, which
;; is another mess.  [Shell mode implicitly assumes script mode
;; has been configured].
;; We should assume commands are terminated at the specific level.

(defvar proof-terminal-string nil 
  "End-of-line string for proof process.")


;;;
;;; Compatibility: define some stuff for FSF Emacs
;;;

(or (fboundp 'warn)
    (defun warn (str &rest args)
      "Issue a warning STR.  Defined by PG for XEmacs compatibility."
      (apply 'message str args)
      (sit-for 2)))



;;;
;;; Load other Proof General libraries
;;;

(require 'proof-utils)
(require 'proof-system)


(provide 'proof)
;; proof.el ends here
