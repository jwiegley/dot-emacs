(defun ml4pg-proof-assert-next-command-interactive3 ()
  (interactive)
  (if (get-buffer "*response*")
  (if (eq ml4pg-save-automatically 0)
      (proof-assert-next-command-interactive)
    (progn (with-current-buffer "*response*"
		    (beginning-of-buffer)
                    (if (zerop (buffer-size))
                      (setf temp nil)
		      (setf temp (search "No" 
				       (format "%s" (read (current-buffer)))))))
		  (if temp
		    (ml4pg-export-previous-lemm)
                    (proof-assert-next-command-interactive)
		      ))
    
  )
  (proof-assert-next-command-interactive)))


(defun ml4pg-export-previous-lemm ()
  (interactive)
  (let ((final (point))
	(result nil)
	(end nil))
    (search-backward "Proof.")
    (proof-goto-point)
    (while (< (point) final) 
      (let* ((semis (save-excursion
		      (skip-chars-backward " \t\n"
					   (proof-queue-or-locked-end))
		      (proof-segment-up-to-using-cache (point))))
	     (comment (caar semis))
	     (cmd (cadar semis))
	     (ts nil))
	(progn (setf ts (ml4pg-get-top-symbol))
	       (setf ng (ml4pg-get-number-of-goals))
	       (proof-assert-next-command-interactive)
	       (setf ng2 (get-number-of-goals))
	       (if cmd 
	       (setf result (cons (append (get-numbers cmd) (list ts) (list ng2)) result))
	       )
		    )
	  
	)	
    )
    (proof-assert-next-command-interactive)
    (setf ml4pg-saved-theorems (append ml4pg-saved-theorems 
				 (list (list (format "%s" (get-name)) 
					     (ml4pg-flat (reverse result))))))
    (search-forward "Qed.")

  ))


(defun ml4pg-get-name ()
  (search-backward "Lemma")
  (read (current-buffer))
  (read (current-buffer)))


(defun ml4pg-list-to-string (list)
  (do ((temp list (cdr temp))
       (temp2 ""))
      ((endp temp) temp2)
      (setf temp2 (concat temp2 (car temp) ", "))))



  



(defun ml4pg-save-numbers ()
  (interactive)
  (progn (beginning-of-buffer)
	 (proof-goto-point)
	 (end-of-buffer)
	 (ml4pg-extract-feature-theorems)
  (let ((d (read-string (concat "Where do you want to store this library (" (ml4pg-list-to-string ml4pg-dirs) "n (create new directory)): ")))
	    (d2 nil))
    (cond ((ml4pg-string-member d ml4pg-dirs)
	       (progn (with-temp-file 
			  (concat ml4pg-home-dir "libs/coq/" d "/"
				  (subseq (buffer-name (current-buffer)) 0 
					  (search "." (buffer-name (current-buffer))))  
				  ".csv") (insert (ml4pg-extract-features-1)))
		      
		      
		      (with-temp-file (concat ml4pg-home-dir "libs/coq/" d "/"
					      (subseq (buffer-name (current-buffer)) 0 
						      (search "." (buffer-name (current-buffer))))  
					      "_names")  (insert (ml4pg-extract-names)))))
	      ((string= d "n")
	       (progn 
		 (setf d2 (read-string (concat "Introduce a name for the directory:")))
		 (shell-command (concat "mkdir " ml4pg-home-dir "libs/coq/" d2))
		 (with-temp-file 
			  (concat ml4pg-home-dir "libs/coq/" d2 "/"
				  (subseq (buffer-name (current-buffer)) 0 
					  (search "." (buffer-name (current-buffer))))  
				  ".csv") (insert (ml4pg-extract-features-1)))
		      (with-temp-file (concat ml4pg-home-dir "libs/coq/" d2 "/"
					      (subseq (buffer-name (current-buffer)) 0 
						      (search "." (buffer-name (current-buffer))))  
					      "_names")  (insert (ml4pg-extract-names)))))
	      (t
	       (progn (with-temp-file 
			  (concat ml4pg-home-dir "libs/coq/" 
				  (subseq (buffer-name (current-buffer)) 0 
					  (search "." (buffer-name (current-buffer))))  
				  ".csv") (insert (ml4pg-extract-features-1)))
		      (with-temp-file (concat ml4pg-home-dir "libs/coq/" 
					      (subseq (buffer-name (current-buffer)) 0 
						      (search "." (buffer-name (current-buffer))))  
					      "_names")  (insert (ml4pg-extract-names))))))
)))