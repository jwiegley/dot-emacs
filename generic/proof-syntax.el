;; proof-syntax.el Generic font lock expressions
;; Copyright (C) 1997-1998 LFCS Edinburgh. 
;; Author: Healfdene Goguen, Thomas Kleymann and Dilip Sequiera
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;


(require 'font-lock)

;;; FIXME: change this to proof-
(defun ids-to-regexp (l)
  "transforms a non-empty list of identifiers `l' into a regular
  expression matching any of its elements"
  (mapconcat (lambda (s) (concat "\\<" s "\\>")) l "\\|"))

;; Generic font-lock

;; proof-commands-regexp is used for indentation
(defvar proof-commands-regexp ""
  "Subset of keywords and tacticals which are terminated by the
  `proof-terminal-char'") 


(defvar proof-id "\\(\\w\\(\\w\\|\\s_\\)*\\)"
  "A regular expression for parsing identifiers.")

;; For font-lock, we treat ,-separated identifiers as one identifier
;; and refontify commata using \{proof-unfontify-separator}.

(defun proof-ids (proof-id)
  "Function to generate a regular expression for separated lists of
  identifiers."
  (concat proof-id "\\(\\s-*,\\s-*" proof-id "\\)*"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; font lock faces: declarations, errors, tacticals                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; FACES have been moved to proof-config.
;; Old code left here while testing.

;(defun proof-have-color ()
;  "Do we have support for colour?"
;  (or (and (fboundp 'device-class)
;	   (eq (device-class (frame-device)) 'color))
;      (and (fboundp 'x-display-color-p) (x-display-color-p))))

;(defvar font-lock-declaration-name-face 
;(progn 
;  (cond 
;   ((proof-have-color)
;    (copy-face 'bold 'font-lock-declaration-name-face)

;    ;; Emacs 19.28 compiles this down to
;    ;; internal-set-face-1. This is not compatible with XEmacs
;    (set-face-foreground
;     'font-lock-declaration-name-face "chocolate"))
;   (t (copy-face 'bold-italic 'font-lock-declaration-name-face)))))

;;  (if running-emacs19
;;      (setq font-lock-declaration-name-face
;;	    (face-name 'font-lock-declaration-name-face))


;(defvar font-lock-tacticals-name-face
;(if (proof-have-color)
;    (let ((face (make-face 'font-lock-tacticals-name-face)))
;      (dont-compile
;	(set-face-foreground face "MediumOrchid3"))
;      face)
;  (copy-face 'bold 'font-lock-tacticals-name-face)))

;(defvar font-lock-error-face
;  (let ((face (make-face 'font-lock-error-face)))
;    (copy-face 'bold 'font-lock-error-face)
;    (and (proof-have-color) (set-face-background face "salmon1"))
;    face)
;  "*The face for error messages.")

;(defvar font-lock-eager-annotation-face
;  (let ((face (make-face 'font-lock-eager-annotation-face)))
;    (if (proof-have-color)
;	(set-face-background face "lemon chiffon")
;      (copy-face 'italic face))
;    face)
;  "*The face for urgent messages.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A big hack to unfontify commas in declarations and definitions.  ;;
;; Useful for provers which have declarations of the form x,y,z:Ty  ;;
;; All that can be said for it is that the previous way of doing    ;;
;; this was even more bogus.                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Refontify the whole line, 'cos that's what font-lock-after-change
;; does.

(defun proof-zap-commas-region (start end length)
  (save-excursion
    (let 
	((start (progn (goto-char start) (beginning-of-line) (point)))
	 (end (progn (goto-char end) (end-of-line) (point))))
      (goto-char start)
      (while (search-forward "," end t)
	(if (memq (get-char-property (- (point) 1) 'face)
		'(proof-declaration-name-face
		  font-lock-function-name-face))
	    (font-lock-remove-face (- (point) 1) (point))
	    )))))

(defun proof-zap-commas-buffer () 
  (proof-zap-commas-region (point-min) (point-max) 0))

(defun proof-unfontify-separator ()
     (make-local-variable 'after-change-functions)
     (setq after-change-functions
	   (append (delq 'proof-zap-commas-region after-change-functions)
		   '(proof-zap-commas-region))))


(provide 'proof-syntax)
