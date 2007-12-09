(defun eshell-exec-lisp (printer errprint func-or-form args form-p)
  (let (result)
    (eshell-condition-case err
	(progn
	  (setq result
		(save-current-buffer
		  (if form-p
		      (first (slime-eval
			      `(cl:with-output-to-string
				(str)
				(swank::eval-region ,(prin1-to-string func-or-form))
			      "CL-USER"))
		    (apply func-or-form args))))
	  (and result (funcall printer result))
	  result)
      (error
       (let ((msg (error-message-string err)))
	 (if (and (not form-p)
		  (string-match "^Wrong number of arguments" msg)
		  (fboundp 'eldoc-get-fnsym-args-string))
	     (let ((func-doc (eldoc-get-fnsym-args-string func-or-form)))
	       (setq msg (format "usage: %s" func-doc))))
	 (funcall errprint msg))
       nil))))
