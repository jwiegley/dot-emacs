;; proof.el  Proof General loader.  All files require this one.
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq-default var value)))

(require 'proof-site)			; site config

(require 'proof-config)			; configuration variables

(require 'proof-splash)			; splash screen

;;;
;;; Emacs libraries
;;;

;; cl is dumped with my XEmacs 20.4, but not FSF Emacs 20.2.
(require 'cl)				

;; browse-url function doesn't seem to be autoloaded in
;; XEmacs 20.4, but it is in FSF Emacs 20.2.
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

(autoload 'font-lock-fontify-region "font-lock")
(autoload 'font-lock-append-text-property "font-lock")

;;;
;;; Autoloads for main code
;;;

(autoload 'proof-mode "proof-script"
  "Proof General major mode class for proof scripts.")

(autoload 'proof-shell-mode "proof-shell"
  "Proof General shell mode class for proof assistant processes")

(autoload 'proof-toolbar-setup "proof-toolbar"
  "Initialize Proof General toolbar and enable it for the current buffer" t)

;;;
;;; More autoloads to help define interface between files
;;;

(autoload 'proof-shell-available-p "proof-shell"
  "Returns non-nil if there is a proof shell active and available.")

(autoload 'proof-shell-invisible-command "proof-shell"
  "Send CMD to the proof process without revealing it to the user.")

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
Whenever a new file is being processed, it gets added.
When the prover retracts across file boundaries, this list 
is resynchronised. It contains files in canonical truename format")

(defvar proof-script-buffer nil
  "The currently active scripting buffer or nil if none.")

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



;;;
;;; Utilities/macros used in several files  (proof-utils)
;;;

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

;; FIXME: this function should be combined with
;; proof-shell-maybe-erase-response-buffer.  Should allow
;; face of nil for unfontified output.
(defun proof-response-buffer-display (str face)
  "Display STR with FACE in response buffer and return fontified STR."
  (let (start end)
    (with-current-buffer proof-response-buffer
      ;; da: I've moved newline before the string itself, to match
      ;; the other cases when messages are inserted and to cope
      ;; with warnings after delayed output (non newline terminated).
      (goto-char (point-max))
      (newline)				
      (setq start (point))
      (insert str) (setq end (point))
      (save-excursion
	(font-lock-set-defaults)		;required for FSF Emacs 20.2
	(font-lock-fontify-region start end)
	(font-lock-append-text-property start end 'face face))
      (buffer-substring start end))))


(defun proof-display-and-keep-buffer (buffer)
  "Display BUFFER and mark window according to `proof-window-dedicated'.

Also ensures that point is visible."
  (let (window)
    (save-excursion
      (set-buffer buffer)
      (display-buffer buffer)
      (setq window (get-buffer-window buffer 'visible))
      (set-window-dedicated-p window proof-window-dedicated)
      (and window
	   (save-selected-window
	     (select-window window)
	     
	     ;; tms: I don't understand why the point in
	     ;; proof-response-buffer is not at the end anyway.
	     ;; Is there a superfluous save-excursion somewhere?
	     ;; da replies: I think it's because of a *missing*
	     ;; save-excursion above around the font-lock stuff.
	     ;; Adding one has maybe fixed this problem.
	     (goto-char (point-max))

	     (or (pos-visible-in-window-p (point) window)
		 (recenter -1)))))))

(defun proof-clean-buffer (buffer)
  "Erase buffer and hide from display if proof-auto-delete-windows set.
Auto deletion only affects selected frame.  (We assume that the selected
frame is the one showing the script buffer.)"
  (erase-buffer buffer)
  (if proof-auto-delete-windows
      (delete-windows-on buffer t)))

;; utility function
(defun proof-buffers-in-mode (mode &optional buflist)
  "Return a list of the buffers in the buffer list in major-mode MODE.
Restrict to BUFLIST if it's set."
  (let ((bufs-left (or buflist (buffer-list))) 
	bufs-got)
    (dolist (buf bufs-left bufs-got)
      (if (with-current-buffer buf (eq mode major-mode))
	  (setq bufs-got (cons buf bufs-got))))))



(provide 'proof)
;; proof.el ends here
