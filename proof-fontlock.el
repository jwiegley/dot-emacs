;; proof-fontlock.el Generic font lock expressions
;; Copyright (C) 1997 LFCS Edinburgh. 
;; Author: Healfdene Goguen, Thomas Kleymann and Dilip Sequiera
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

;; $Log$
;; Revision 1.3  1997/11/17 17:11:19  djs
;; Added some magic commands: proof-frob-locked-end, proof-try-command,
;; proof-interrupt-process. Added moving nested lemmas above goal for coq.
;; Changed the key mapping for assert-until-point to C-c RET.
;;
;; Revision 1.2  1997/10/13 17:13:50  tms
;; *** empty log message ***
;;
;; Revision 1.1.2.1  1997/10/07 13:34:27  hhg
;; New structure to share as much as possible between LEGO and Coq.
;;
;;

(require 'font-lock)

(defun ids-to-regexp (l)
  "transforms a non-empty list of identifiers `l' into a regular
  expression matching any of its elements"
  (mapconcat (lambda (s) (concat "\\<" s "\\>")) l "\\|"))

;; Generic font-lock
(defvar proof-id "\\(\\w\\(\\w\\|\\s_\\)*\\)"
  "A regular expression for parsing identifiers.")

;; For font-lock, we treat ,-separated identifiers as one identifier
;; and refontify commata using \{proof-unfontify-separator}.

(defun proof-ids (proof-id)
  "Function to generate a regular expression for separated lists of
  identifiers."
  (concat proof-id "\\(\\s *,\\s *" proof-id "\\)*"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; font lock faces: declarations, errors, tacticals                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-have-color ()
 ())

(defvar font-lock-declaration-name-face 
(progn 
  (cond 
   ((proof-have-color)
    (copy-face 'bold 'font-lock-declaration-name-face)

    ;; Emacs 19.28 compiles this down to
    ;; internal-set-face-1. This is not compatible with XEmacs
    (set-face-foreground
     'font-lock-declaration-name-face "chocolate"))
    (t (copy-face 'bold-italic 'font-lock-declaration-name-face)))))

;;  (if running-emacs19
;;      (setq font-lock-declaration-name-face
;;	    (face-name 'font-lock-declaration-name-face))

(defvar font-lock-tacticals-name-face
(if (proof-have-color)
    (let ((face (make-face 'font-lock-tacticals-name-face)))
      (dont-compile
	(set-face-foreground face
			     "MediumOrchid3"))
      face)
  (copy-face 'bold 'font-lock-tacticals-name-face)))

(defvar font-lock-error-face
(if (proof-have-color)
    (let ((face (make-face 'font-lock-error-face)))
      (dont-compile
	(set-face-foreground face
			     "red"))
      face)
  (copy-face 'bold 'font-lock-error-face)))


;;
;; A big hack to unfontify commas in declarations and definitions. All
;; that can be said for it is that the previous way of doing this was
;; even more bogus.
;;

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
		'(font-lock-declaration-name-face
		  font-lock-function-name-face))
	    (font-lock-remove-face (- (point) 1) (point)))))))

(defun proof-zap-commas-buffer () 
  (proof-zap-commas-region (point-min) (point-max) 0))

(defun proof-unfontify-separator ()
     (make-local-variable 'after-change-functions)
     (setq after-change-functions
	   (append (delq 'proof-zap-commas-region after-change-functions)
		   '(proof-zap-commas-region))))


(provide 'proof-fontlock)
