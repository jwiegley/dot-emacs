;;; junk.el
;;;
;;;  $Id$
;;;
;;; Bits and pieces of code 
;;; removed from main PG (or never added).
;;; Left here in case they're useful later.
;;;

(defun proof-set-toggle (sym value)
  "Try to set a boolean variable <blah>-enable using function <blah>-toggle."
  (save-match-data
    (let* ((nm   (symbol-name sym))
	   (i    (string-match "-enable" nm))
	   (tgfn (if i (intern (concat (substring nm 0 i) "-toggle")))))
      (if (and tgfn (fboundp tgfn))
	  (funcall tgfn (if value 1 0))))))
