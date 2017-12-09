;; $Header: /usr/local/cvsroot/emacs-cl/contrib/gabriel/fread.cl,v 1.1 2004/05/05 05:41:56 lars Exp $
;; $Locker:  $

;;; FREAD -- Benchmark to read from a file.
;;; Pronounced "FRED".  Requires the existance of FPRINT.TST which is created
;;; by FPRINT.

(defun fread ()
  (let ((stream (open "/tmp/fprint.tst" :direction :input)))
    (read stream)
    (close stream)))
	    
(defun testfread ()
  (print (time (fread))))
