;; proof-syntax.el Generic font lock expressions
;; Copyright (C) 1997-1998 LFCS Edinburgh. 
;; Author: Healfdene Goguen, Thomas Kleymann and Dilip Sequiera
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;


(require 'font-lock)
(require 'proof-config)

;; FIXME da: would regexp-opt be better here?  Or maybe
;;  (concat "\\<" (regexp-opt l) "\\>")
(defun proof-ids-to-regexp (l)
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
;; A big hack to unfontify commas in declarations and definitions.  ;;
;; Useful for provers which have declarations of the form x,y,z:Ty  ;;
;; All that can be said for it is that the previous way of doing    ;;
;; this was even more bogus.                                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Refontify the whole line, 'cos that's what font-lock-after-change
;; does.

;;FIXME: Under FSF Emacs 20.2, when initially fontifying the buffer,
;;       commas are not zapped. 
(defun proof-zap-commas-region (start end &optional length)
  "Remove the face of all `,' within the region (START,END).
The optional argument LENGTH has no effect. It is required so that we
may assign this function to `after-change-function'."
  (save-excursion
    (let 
	((start (progn (goto-char start) (beginning-of-line) (point)))
	 (end (progn (goto-char end) (end-of-line) (point))))
      (goto-char start)
      (while (search-forward "," end t)
	(if (memq (get-char-property (- (point) 1) 'face)
		(list 'proof-declaration-name-face
		  'font-lock-function-name-face))
	    (font-lock-unfontify-region (- (point) 1) (point))
	    )))))

(defun proof-zap-commas-buffer () 
  "Remove the face of all `,' in the current buffer."
  (proof-zap-commas-region (point-min) (point-max)))

(defun proof-unfontify-separator ()
     (make-local-variable 'after-change-functions)
     (setq after-change-functions
	   (append (delq 'proof-zap-commas-region after-change-functions)
		   '(proof-zap-commas-region))))


(provide 'proof-syntax)
