;; pg-assoc.el  Functions for associated buffers
;;
;; Copyright (C) 1994-2002 LFCS Edinburgh. 
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

;; A sub-module of proof-shell; assumes proof-script loaded.
(require 'proof-script)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Defines an empty mode inherited by modes of the associated buffers.
;;

(eval-and-compile
(define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    ;; Doesn't seem to supress TAB, RET
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map 
		       proof-universal-keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Manipulating prover output
;;

(defun pg-assoc-strip-subterm-markup (string)
  "Return STRING with subterm and pbp annotations removed.
Special annotations are characters with codes higher than
'pg-subterm-first-special-char'.
If pg-subterm-first-special-char is unset, return STRING unchanged."
  (if pg-subterm-first-special-char
      (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
	(while (< ip l)
	  (if (>= (aref string ip) pg-subterm-first-special-char)
	      (if (char-equal (aref string ip) pg-subterm-start-char)
		  (progn (incf ip)
			 ;; da: this relies on annotations being
			 ;; characters between \200 and first special
			 ;; char (e.g. \360).  Why not just look for
			 ;; the sep char??
			 (while 
			     (< (aref string ip) 
				pg-subterm-first-special-char)
			   (incf ip))))
	    (aset out op (aref string ip))
	    (incf op))
	  (incf ip))
	(substring out 0 op))
    string))

(defun pg-assoc-strip-subterm-markup-buf (start end)
  "Remove subterm and pbp annotations from region."
  ;; FIXME: create these regexps ahead of time.
  (if pg-subterm-start-char
      (let ((ann-regexp 
	     (concat 
	      (regexp-quote (char-to-string pg-subterm-start-char))
	      "[^" 
	      (regexp-quote (char-to-string pg-subterm-sep-char))
	      "]*"
	      (regexp-quote (char-to-string pg-subterm-sep-char)))))
	(save-restriction
	  (narrow-to-region start end)
	  (goto-char start)
	  (proof-replace-regexp ann-regexp "")
	  (goto-char start)
	  (proof-replace-string (char-to-string pg-subterm-end-char) "")
	  (goto-char start)
	  (if pg-topterm-char
	      (proof-replace-string (char-to-string pg-topterm-char) ""))))))
	  
	 
(defun pg-assoc-strip-subterm-markup-buf-old (start end)
  "Remove subterm and pbp annotations from region."
  (let (c)
    (goto-char start)
    (while (< (point) end)
      ;; FIXME: small OBO here: if char at end is special
      ;; it won't be removed.
      (if (>= (setq c (char-after (point))) 
	      pg-subterm-first-special-char)
	  (progn
	    (delete-char 1)
	    (decf end)
	    (if (char-equal c pg-subterm-start-char)
		(progn 
		  ;; FIXME: could simply replace this by replace
		  ;; match, matching on sep-char??
		  (while (and (< (point) end)
			      (< (char-after (point))
				 pg-subterm-first-special-char))
		    (delete-char 1)
		    (decf end)))))
	(forward-char)))
    end))



(provide 'pg-assoc)
;; pg-assoc.el ends here.
