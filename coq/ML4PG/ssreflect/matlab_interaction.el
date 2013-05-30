;; This function starts Matlab

(defun ml4pg-init-clusters ()
  (interactive)
  (ml4pg-my-config-display)
  (require 'comint)  
   (apply 'make-comint "matlab" *matlab-program* nil 
		(list "-nodesktop -r 0")))
  ;(apply 'make-comint "matlab" *matlab-program* nil (list "-nodesktop -r")))
 ; (shell-command "/home/jonathan/Matlab/bin/matlab -nodesktop -r 
  ;              \"load /home/jonathan/Desktop/Research/Matlab/expt1_complete_goals.csv; kmeans_clusters_and_frequencies(expt1_complete_goals,3,1000)\"")
  
(defvar ml4pg-my-buffer "")

(defun ml4pg-my-config-display ()
  (delete-other-windows)
  (switch-to-buffer-other-window "*display*")
  (erase-buffer)
  (other-window -1))

;; This function is in charge of processing the output produced by Matlab
;; The variable signal is used to indicate the function which has called to matlab and to process the result

(defvar ml4pg-signal 0)

(defun ml4pg-my-output-filter (output)
  (setq ml4pg-my-buffer (concat ml4pg-my-buffer output))
  (when (and output (get-buffer "*display*"))
        (with-current-buffer "*display*"
	  (progn (erase-buffer)
		 (cond ((equal ml4pg-signal 0) nil)
		       ((equal ml4pg-signal 1) (ml4pg-print-similarities (ml4pg-split-clusters-aux2 ml4pg-my-buffer nil)))
		       ((equal ml4pg-signal 4) (ml4pg-print-clusters-bis (ml4pg-split-clusters-aux ml4pg-my-buffer nil) (ml4pg-split-frequencies ml4pg-my-buffer nil)))
		       ((equal ml4pg-signal 3) (ml4pg-compute-clusters-and-values (ml4pg-split-clusters-aux (ml4pg-remove-jumps (subseq ml4pg-my-buffer (search "load" ml4pg-my-buffer :from-end t))) nil) 
								      (ml4pg-split-frequencies (ml4pg-remove-jumps  (subseq ml4pg-my-buffer (search "load" ml4pg-my-buffer :from-end t))) nil)))
		       (t nil)))))
  output)

(add-hook 'comint-preoutput-filter-functions 'ml4pg-my-output-filter)


(defun ml4pg-split-clusters-aux2 (str res)
 (let ((init (search "ans =" str)))
 (if init
     (list (ml4pg-cluster-string-to-list (ml4pg-remove-jumps (subseq str (+ 5 init) (search ">>" str :from-end t)))))
   nil)))

(defun ml4pg-split-clusters-aux (str res)
 (let ((init (search "ans =" str)))
 (if init
	(let ((end (search "[" str :start2 (1+ init))))
	  (ml4pg-split-clusters-aux (subseq str (1+ end))
			     (cons (ml4pg-cluster-string-to-list (ml4pg-remove-jumps (subseq str (+ 5 init) end))) res)))
     res)))


(defun ml4pg-split-frequencies (str res)
(let ((init (search "[" str)))
  (if init
      (let ((end (search "]" str :start2 (1+ init))))
	  (if (not (search "char" (subseq str init end)))
	      (ml4pg-split-frequencies (subseq str (1+ end))
				 (cons (string-to-number (ml4pg-remove-jumps (subseq str (1+ init) end))) res))
	    (ml4pg-split-frequencies (subseq str (1+ (search "[" str :start2 (1+ end))))  res)
	    ))
    res)))




(defun ml4pg-search-cluster (res n)
  (do ((temp res (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (member (format "%s" n) (car temp))
	  (append temp2 (list (car temp))))))
	  


(defun ml4pg-cluster-string-to-list (cluster)
  (do ((temp cluster)
       (temp2 nil))
      ((not (search "," temp)) (append temp2 (list temp)))
      (progn (setf temp2 (append temp2 (list (subseq temp 0 (search "," temp)))))
	     (setf temp (subseq temp (1+ (search "," temp)))))))

      
  


(defun ml4pg-remove-occurrence (list n)
  (do ((temp list (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (if (not (equal (format "%s" n) (car temp)))
	  (setf temp2 (append temp2 (list (car temp)))))))


(defvar ml4pg-granularity-level-temp 1)

(defun ml4pg-print-similarities (res)
  (interactive)
  (cond ((not (caar res)) (insert (format "Searching similarities...\n")))
	((search "None" (caar res))
	 (if (not ml4pg-iterative)
	     (insert (format "Sorry, but we have not found any similarity using granularity %s\n" ml4pg-granularity-level))
	   (if (eq ml4pg-granularity-level-temp 5)
		      (format "Sorry, but we have not found any similarity at any ganularity level\n")
	     (progn (setf ml4pg-granularity-level-temp (1+ ml4pg-granularity-level-temp))
		    (ml4pg-show-clusters-of-theorem-iterative)))))
	(t (progn (insert (format "Similarities:\n"))
		  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
		  (insert (format "This lemma is similar to the lemmas: \n"))
		  (do ((temp2 (ml4pg-remove-occurrence (car res) (1+ (length ml4pg-saved-theorems))) (cdr temp2)))
			  ((endp temp2) )
			  (if (<= (string-to-number (car temp2)) (length ml4pg-saved-theorems))
			      (progn  (insert (format "- "))
				     (ml4pg-insert-button-lemma (ml4pg-remove_last_colon(car (nth (- (string-to-number (car temp2)) 1) ml4pg-saved-theorems)))))
			    (progn (shell-command (concat "cat "(expand-file-name "names_temp.txt") " | sed -n '" 
							  (format "%s" (- (string-to-number (car temp2)) (length ml4pg-saved-theorems)))
							  "p'")) 
				   (with-current-buffer "*Shell Command Output*"
				     (beginning-of-buffer)
				     (read (current-buffer))
				     (setf temp-res (ml4pg-remove_last_colon (format "%s"  (read (current-buffer))))))
				   (insert (format "- "))
				   (ml4pg-insert-button-lemma temp-res)))))
		  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
		  (if ml4pg-iterative (insert (format "Similarities found using granularity level %s\n" ml4pg-granularity-level-temp)))
		  )))



;
(defun ml4pg-print-similarities-matlab ()
  (with-current-buffer "*display*"
    (while (string= "0" (car (ml4pg-read-lines (expand-file-name "available.txt"))))
      
      (progn (erase-buffer)
	     (insert (format "Searching clusters...\n"))
	     (sleep-for 1))
      )
    (erase-buffer)
    (let* ((clu (car (ml4pg-read-lines (expand-file-name "matlab_res.txt")))))
      (cond 
	((search "None" clu)
	 (if (not ml4pg-iterative)
	     (insert (format "Sorry, but we have not found any similarity using granularity %s\n" ml4pg-granularity-level))
	   (if (eq ml4pg-granularity-level-temp 5)
		      (format "Sorry, but we have not found any similarity at any ganularity level\n")
	     (progn (setf ml4pg-granularity-level-temp (1+ granularity-level-temp))
		    (ml4pg-show-clusters-of-theorem-iterative)))))
	(t (progn (insert (format "Similarities:\n"))
		  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
		  (insert (format "This lemma is similar to the lemmas:\n "))
		  (do ((temp2 (ml4pg-remove-occurrence (ml4pg-cluster-string-to-list clu) (1+ (length ml4pg-saved-theorems))) (cdr temp2)))
			  ((endp temp2) )
			  (if (<= (string-to-number (car temp2)) (length ml4pg-saved-theorems))
			      (progn (insert (format "- "))
				     (ml4pg-insert-button-lemma (ml4pg-remove_last_colon(car (nth (- (string-to-number (car temp2)) 1) ml4pg-saved-theorems)))))
			    (progn (shell-command (concat "cat "(expand-file-name "names_temp.txt") " | sed -n '" 
							  (format "%s" (- (string-to-number (car temp2)) (length ml4pg-saved-theorems)))
							  "p'")) 
				   (with-current-buffer "*Shell Command Output*"
				     (beginning-of-buffer)
				     (read (current-buffer))
				     (setf temp-res (ml4pg-remove_last_colon (format "%s"  (read (current-buffer))))))
				   (insert (format "- "))
				   (ml4pg-insert-button-lemma temp-res)))))
		  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
		  (if ml4pg-iterative (insert (format "Similarities found using granularity level %s\n" ml4pg-granularity-level-temp)))
		  ))
)))





(defun ml4pg-print-similarities-weka (n)
  (let ((clusters (ml4pg-extract-clusters-from-file n)))
    (with-current-buffer "*display*"
      (erase-buffer)
      (insert (format "Similarities:\n"))
      (insert (format "-----------------------------------------------------------------------------------\n"))
      (insert (format "This lemma is similar to the lemmas:\n"))
      (do ((temp2 (ml4pg-remove-occurrence (ml4pg-clusters-of-n clusters (nth (1- (length ml4pg-saved-theorems)) clusters)) (1+ (length ml4pg-saved-theorems))) (cdr temp2)))
	  ((endp temp2) )
	  (if (<= (car temp2) (length ml4pg-saved-theorems))
	      (progn (insert (format "- "))
		     (ml4pg-insert-button-lemma (ml4pg-remove_last_colon(car (nth (- (car temp2)  1) ml4pg-saved-theorems)))))
	    (progn (shell-command (concat "cat "(expand-file-name "names_temp.txt") " | sed -n '" 
					  (format "%s" (- (car temp2) (length ml4pg-saved-theorems)))
					  "p'")) 
		   (with-current-buffer "*Shell Command Output*"
		     (beginning-of-buffer)
		     (read (current-buffer))
		     (setf temp-res (ml4pg-remove_last_colon (format "%s"  (read (current-buffer))))))
		   (insert (format "- "))
		   (ml4pg-insert-button-lemma temp-res)
		   )))
      (insert (format "-----------------------------------------------------------------------------------\n") )
      )
    ))



(defun ml4pg-insert-button-lemma (lemma)
  (progn (insert-button lemma 'action (ml4pg-insert-button-lemma-macro lemma)
			'face (list 'link)
			'follow-link t)
	 (insert (format "\n"))))



(defun ml4pg-insert-button-lemma-macro (test)
  (list 'lambda '(x)
    (list 'progn
      (list 'proof-shell-invisible-cmd-get-result (list 'format '"Unset Printing All."))
      (list 'if (list 'get-buffer '"*display2*") (list 'with-current-buffer '"*display2*" (list 'delete-window)))
      (list 'with-current-buffer '"*display*" (list 'split-window-vertically))
      (list 'switch-to-buffer-other-window '"*display2*")
      (list 'with-current-buffer '"*display2*" (list 'erase-buffer))
      (list 'with-current-buffer '"*display2*"
        (list 'insert (list 'proof-shell-invisible-cmd-get-result
          (list 'format '"Print %s." test))))
    )))





			  
(defvar ml4pg-times 0)

(defun ml4pg-print-clusters (res freq)
  (interactive)
  (setf ml4pg-times (1+ ml4pg-times))
  (if (not (caar res))
      (insert (format "Searching clusters...\n"))
  (let* ((temp0 (ml4pg-unzip (ml4pg-quicksort-pair (ml4pg-zip res freq))))
	 (res1 (car temp0))
	 (freq1 (cadr  temp0)))
  (insert (format "We have found the following clusters:\n" ))
  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
  (do ((temp res1 (cdr temp))
       (temp-freq freq1 (cdr temp-freq))
       (i 1 (1+ i)))
      ((endp temp) (insert (format "------------------------------------------------------------------------------------------------------------\n")) )
    (progn (insert (format "Cluster %s with frequency %s%%\n" i (car temp-freq))) 
    (do ((temp2 (car temp) (cdr temp2)))
	((endp temp2) (insert (format "\n")))
      (progn (insert (format "Lemma "))
	     (ml4pg-insert-button-lemma 
	      (ml4pg-remove_last_colon
                 (car (nth (string-to-number (car temp2)) ml4pg-saved-theorems)))))))))))


(defun ml4pg-print-clusters-bis (res freq)
  (interactive)
  (setf ml4pg-times (1+ ml4pg-times))
  (if (not (caar res))
      (insert (format "Searching clusters...\n"))
  (let* ((temp0 (ml4pg-unzip (ml4pg-quicksort-pair (ml4pg-zip res freq))))
	 (res1 (car temp0))
	 (freq1 (cadr  temp0)))
  (insert (format "We have found the following clusters:\n" ))
  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
  (do ((temp res1 (cdr temp))
       (temp-freq freq1 (cdr temp-freq))
       (i 1 (1+ i)))
      ((endp temp) (insert (format "------------------------------------------------------------------------------------------------------------\n")) )
    (progn (insert (format "Cluster %s with frequency %s%%\n" i (car temp-freq))) 
    (do ((temp2 (car temp) (cdr temp2)))
	((endp temp2) (insert (format "\n")))
	(if (< (string-to-number (car temp2)) (length ml4pg-saved-theorems))
	    (progn (insert (format "Lemma "))
		   (ml4pg-insert-button-lemma (ml4pg-remove_last_colon
			     (car (nth (string-to-number (car temp2)) ml4pg-saved-theorems)))))
	  (progn (shell-command (concat "cat "(expand-file-name "names_temp.txt") " | sed -n '" 
						  (format "%s" (- (string-to-number (car temp2)) (length ml4pg-saved-theorems)))
						  "p'")) 
		 (with-current-buffer "*Shell Command Output*"
		   (beginning-of-buffer)
		   (read (current-buffer))
		   (setf temp-res (format "%s"  (read (current-buffer)))))
		 (insert (format "Lemma " ))
		 (ml4pg-insert-button-lemma temp-res))
	  )))))))


(defun ml4pg-extract_clusters_freq (list)
  (do ((temp list (cdr temp))
       (clusters nil)
       (freq nil))
      ((endp temp) (list clusters freq))
      (if (not (string= (subseq (car temp) 0 1) "["))
	  (setf clusters (append clusters (list (car temp))))
	(setf freq (append freq (list (string-to-number (subseq (car temp) 1 (search "]" (car temp))))))))))






(defun ml4pg-print-clusters-matlab ()
  (with-current-buffer "*display*"
    (while (string= "0" (car (read-lines (expand-file-name "available.txt"))))
      
      (progn (erase-buffer)
	     (insert (format "Searching clusters...\n"))
	     (sleep-for 1))
      )
    (erase-buffer)
    (let* ((clu-freq (ml4pg-extract_clusters_freq (read-lines (expand-file-name "matlab_res.txt"))))
	  (clu (car clu-freq))
	  (freq (cadr clu-freq))
	  (temp0 (ml4pg-unzip (ml4pg-quicksort-pair (ml4pg-zip clu freq))))
	  (res1 (car temp0))
	  (freq1 (cadr  temp0))) 
    (insert (format "We have found the following clusters:\n" ))
    (insert (format "------------------------------------------------------------------------------------------------------------\n"))
    (do ((temp res1 (cdr temp))
       (temp-freq freq1 (cdr temp-freq))
       (i 1 (1+ i)))
      ((endp temp) (insert (format "------------------------------------------------------------------------------------------------------------\n")) )
    (progn (insert (format "Cluster %s with frequency %s%%\n" i (car temp-freq))) 
    (do ((temp2 (ml4pg-cluster-string-to-list (car temp)) (cdr temp2)))
	((endp temp2) (insert (format "\n")))
	(if (< (string-to-number (car temp2)) (length ml4pg-saved-theorems))
	    (progn (insert (format "Lemma "))
		   (ml4pg-insert-button-lemma (ml4pg-remove_last_colon
			     (car (nth (string-to-number (car temp2)) ml4pg-saved-theorems)))))
	  (progn (shell-command (concat "cat "(expand-file-name "names_temp.txt") " | sed -n '" 
						  (format "%s" (- (string-to-number (car temp2)) (length ml4pg-saved-theorems)))
						  "p'")) 
		 (with-current-buffer "*Shell Command Output*"
		   (beginning-of-buffer)
		   (read (current-buffer))
		   (setf temp-res (format "%s"  (read (current-buffer)))))
		 (insert (format "Lemma " ))
		 (ml4pg-insert-button-lemma temp-res))
	  ))))
    )))




(defun ml4pg-print-clusters-weka (gra)
  (let* ((clusters (ml4pg-extract-clusters-from-file gra))
	 (res1 (ml4pg-remove-alone (cdr (ml4pg-form-clusters clusters gra)))))
    (with-current-buffer "*display*"
      (erase-buffer)
      (insert (format "We have found the following clusters:\n" ))
      (insert (format "-------------------------------------------------------------------------------------\n"))
  
      (do ((temp res1 (cdr temp))
	   (i 1 (1+ i)))
	  ((endp temp) (insert (format "-------------------------------------------------------------------------------------\n")) )
	  (progn (insert (format "Cluster %s\n" i )) 
		 (do ((temp2 (car temp) (cdr temp2)))
		     ((endp temp2) (insert (format "\n")))
		     (if (< (car temp2) (length ml4pg-saved-theorems))
			 (progn (insert (format "Lemma "))
				(ml4pg-insert-button-lemma (ml4pg-remove_last_colon
						      (car (nth (car temp2) ml4pg-saved-theorems)))))
		       (progn (shell-command (concat "cat "(expand-file-name "names_temp.txt") " | sed -n '" 
						     (format "%s" (- (car temp2) (length ml4pg-saved-theorems)))
						  "p'")) 
			      (with-current-buffer "*Shell Command Output*"
				(beginning-of-buffer)
				(read (current-buffer))
				(setf temp-res (format "%s"  (read (current-buffer)))))
		 (insert (format "Lemma " ))
		 (if (not (search "home" temp-res) )(ml4pg-insert-button-lemma temp-res)))
		       ))))
      
		   
		   

      )))



  



(defun ml4pg-remove_last_colon (str)
  (if (string= (subseq str (1- (length str))) ":")
      (subseq str 0 (1- (length str)))
    str))

      
;; This functions shows the cluster of a theorem


(defun ml4pg-show-clusters-of-theorem-iterative ()
  (interactive)
  (let* ((alg (cond ((string= "g" ml4pg-algorithm) "find_cluster_with_gaussian") (t "find_cluster_with_kmeans")))
	 (gra (if (not ml4pg-iterative)
		  (cond  ((eq 2 ml4pg-granularity-level) 5)
			 ((eq 3 ml4pg-granularity-level) 10)
			 ((eq 4 ml4pg-granularity-level) 15)
			 ((eq 5 ml4pg-granularity-level) 20)
			 (t 3))
		(cond  ((eq 2 ml4pg-granularity-level-temp) 5)
			 ((eq 3 ml4pg-granularity-level-temp) 10)
			 ((eq 4 ml4pg-granularity-level-temp) 15)
			 ((eq 5 ml4pg-granularity-level-temp) 20)
			 (t 3)))))
  (progn (setf signal 1)
	 (shell-command  (concat "echo 0 > " (expand-file-name "available.txt")))
	 (require 'comint)
	 (comint-send-string (get-buffer-process "*matlab*") 
			     (concat "load " (expand-file-name "temp.csv")
				     (format "; %s(temp,%s,%s,'%s'); csvwrite('%s',1)\n" alg gra (1+ (length ml4pg-saved-theorems))
					     (expand-file-name "matlab_res.txt") (expand-file-name "available.txt"))))
	 (ml4pg-print-similarities-matlab)
		  )))

(defun ml4pg-show-clusters-of-theorem ()
  (interactive)
  (let* ((alg (cond ((string= "g" ml4pg-algorithm) "find_cluster_with_gaussian") (t "find_cluster_with_kmeans")))
	 (gra (if (not ml4pg-iterative)
		  (cond  ((eq 2 ml4pg-granularity-level) 8)
			 ((eq 3 ml4pg-granularity-level) 15)
			 ((eq 4 ml4pg-granularity-level) 25)
			 ((eq 5 ml4pg-granularity-level) 50)
			 (t 5))
		(cond  ((eq 2 ml4pg-granularity-level-temp) 8)
			 ((eq 3 ml4pg-granularity-level-temp) 15)
			 ((eq 4 ml4pg-granularity-level-temp) 25)
			 ((eq 5 ml4pg-granularity-level-temp) 50)
			 (t 5)))))
  (progn 
    (setq ml4pg-my-buffer "")
    (setf res (ml4pg-extract-info-up-to-here))
    (with-temp-file (expand-file-name "temp.csv") (cond ((string= ml4pg-level "g") (insert (ml4pg-extract-features-1-bis res)))
							((string= ml4pg-level "t") (insert (ml4pg-extract-features-2-bis ml4pg-tactic-temp ml4pg-tactic-level)))
							((string= ml4pg-level "p") (insert (ml4pg-extract-features-2-bis ml4pg-proof-tree-temp ml4pg-proof-tree-level)))))
    (if ml4pg-libs-menus
	(progn (ml4pg-add-libraries-temp)
	       (ml4pg-add-names)))
    (switch-to-buffer-other-window "*display*")
    (cond ((string= ml4pg-ml-system "m") 
	   (progn (setf ml4pg-signal 1)
		  (shell-command  (concat "echo 0 > " (expand-file-name "available.txt")))
		  (require 'comint)
		  (comint-send-string (get-buffer-process "*matlab*") 
				      (concat "load " (expand-file-name "temp.csv")
					      (format "; %s(temp,%s,%s,'%s'); csvwrite('%s',1)\n" alg gra (1+ (length ml4pg-saved-theorems))
						      (expand-file-name "matlab_res.txt") (expand-file-name "available.txt"))))
		  (ml4pg-print-similarities-matlab)
		  ))

	  ((string= ml4pg-ml-system "w") 
	   (progn (setf ml4pg-signal 5) 
		  (ml4pg-weka gra)
		  (sleep-for 1)
		  (ml4pg-print-similarities-weka gra))
	   )
	  )))
  (proof-shell-invisible-cmd-get-result (format "Unset Printing All")))

;; The following function shows all the clusters which have been obtained from all the theorems exported up to now

(defun ml4pg-show-clusters ()
  (interactive)
  (let* ((alg (cond ((string= "g" ml4pg-algorithm) "gaussian_clusters") (t "kmeans_clusters_and_frequencies")))
	 (gra (cond  ((eq 2 ml4pg-granularity-level) 5)
		     ((eq 3 ml4pg-granularity-level) 10)
		     ((eq 4 ml4pg-granularity-level) 15)
		     ((eq 5 ml4pg-granularity-level) 20)
		     (t 3)))
	 (freq (cond  ((eq 2 ml4pg-frequency-precision) 500)
		      ((eq 3 ml4pg-frequency-precision) 1000)
		      (t 100))))
    
  (progn 
    (setf ml4pg-signal 2)
    (setf ml4pg-my-buffer "")
    (progn (with-temp-file (expand-file-name "temp1.csv") (insert (ml4pg-extract-features-1)))
		  (switch-to-buffer-other-window "*display*")
		  (require 'comint)
		  (comint-send-string (get-buffer-process "*matlab*") 
				      (concat "load " (expand-file-name "temp1.csv") (format "; %s(temp1,%s,%s)\n" alg gra freq))))
    )))



(defun ml4pg-show-clusters-bis ()
  (interactive)
  (let* ((alg (cond ((string= "g" ml4pg-algorithm) "gaussian_clusters") (t "kmeans_clusters_and_frequencies")))
	 (gra (cond  ((eq 2 ml4pg-granularity-level) 5)
		     ((eq 3 ml4pg-granularity-level) 10)
		     ((eq 4 ml4pg-granularity-level) 15)
		     ((eq 5 ml4pg-granularity-level) 20)
		     (t 3)))
	 (freq (cond  ((eq 2 ml4pg-frequency-precision) 500)
		      ((eq 3 ml4pg-frequency-precision) 1000)
		      (t 100))))
    
  (progn 
    (setf ml4pg-signal 4)
    (setf ml4pg-my-buffer "")
    (if ml4pg-libs-menus
	(progn (with-temp-file (expand-file-name "temp.csv")  (cond ((string= ml4pg-level "g") (insert (ml4pg-extract-features-1)))
								     ((string= ml4pg-level "t") (insert (ml4pg-extract-features-2 ml4pg-tactic-level)))
								     ((string= ml4pg-level "p") (insert (ml4pg-extract-features-2 ml4pg-proof-tree-level)))))
	       (ml4pg-add-libraries-temp)
	       (ml4pg-add-names))
      (with-temp-file (expand-file-name "temp.csv") (insert (ml4pg-extract-features-1))))
    (switch-to-buffer-other-window "*display*")
    (cond ((string= ml4pg-ml-system "m") 
	   (progn
	     (shell-command  (concat "echo 0 > " (expand-file-name "available.txt")))
	     (require 'comint)
	     (comint-send-string (get-buffer-process "*matlab*") 
				 (concat "load " (expand-file-name "temp.csv") (format "; %s(temp,%s,%s,'%s'); csvwrite('%s',1)\n" alg gra freq
											     (expand-file-name "matlab_res.txt") (expand-file-name "available.txt"))))
		  (ml4pg-print-clusters-matlab)))
	  ((string= ml4pg-ml-system "w") 
	   (progn (setf ml4pg-signal 5) 
		  (ml4pg-weka gra)
		  (sleep-for 1)
		  (ml4pg-print-clusters-weka gra))
	   )
      
    )))
  (proof-shell-invisible-cmd-get-result (format "Unset Printing All"))
)




(defun ml4pg-add-libraries ()
  (do ((temp ml4pg-libs-menus (cdr temp)))
      ((endp temp) nil)
      (cond ((string= ml4pg-level "g") (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) ".csv >> " (expand-file-name "temp1.csv"))))
	    ((string= ml4pg-level "t") (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) "_tactics.csv >> " (expand-file-name "temp1.csv"))))
	    ((string= ml4pg-level "p") (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) "_tree.csv >> " (expand-file-name "temp1.csv")))))))

(defun ml4pg-add-libraries-temp ()
  (do ((temp ml4pg-libs-menus (cdr temp)))
      ((endp temp) nil)
      (cond ((string= ml4pg-level "g") (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) ".csv >> " (expand-file-name "temp.csv"))))
	    ((string= ml4pg-level "t") (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) "_tactics.csv >> " (expand-file-name "temp.csv"))))
	    ((string= ml4pg-level "p") (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) "_tree.csv >> " (expand-file-name "temp.csv")))))))

(defun ml4pg-add-names ()
  (shell-command (concat "rm " (expand-file-name "names_temp.txt")))
  (shell-command (concat "touch " (expand-file-name "names_temp.txt")))
  (do ((temp ml4pg-libs-menus (cdr temp)))
      ((endp temp) nil)
      (shell-command  (concat "cat " ml4pg-home-dir "libs/ssreflect/" (car temp) "_names >> " (expand-file-name "names_temp.txt")))))







(defvar ml4pg-names-values nil)

(defun ml4pg-print-clusters2 (res freq)
  (interactive)
  (let* ((temp0 (ml4pg-unzip (ml4pg-quicksort-pair (ml4pg-zip res freq))))
	 (res1 (car temp0))
	 (freq1 (cadr  temp0)))
  (insert (format "We have found the following clusters:\n"))
  (insert (format "------------------------------------------------------------------------------------------------------------\n"))
  (do ((temp res1 (cdr temp))
       (temp-freq freq1 (cdr temp-freq))
       (i 1 (1+ i)))
      ((endp temp) (insert (format "------------------------------------------------------------------------------------------------------------\n")))
    (progn (insert (format "Cluster %s with frequency %s%%\n" i (car temp-freq))) 
    (do ((temp2 (car temp) (cdr temp2)))
	((endp temp2) (insert (format "\n")))
      (insert (format "Lemma %s\n"
	      (ml4pg-remove_last_colon
                 (car (nth (- (string-to-number (car temp2)) 1) ml4pg-saved-theorems2))))))))))


(defun ml4pg-compute-clusters-and-values (list fr)
  (if (not (ml4pg-left-strings ml4pg-saved-theorems2))
      (ml4pg-print-clusters2 list fr)
    (progn (setf ml4pg-names-values (ml4pg-extract-names-dynamic))
    (do ((temp list (cdr temp))
	 (n 200 (+ n 5)))
	((endp temp) (progn (setf ml4pg-names-values (ml4pg-complete-names-values ml4pg-names-values n))
			    (setf ml4pg-saved-theorems2 (ml4pg-recompute-saved-theorems ml4pg-saved-theorems2))
			    (setf ml4pg-my-buffer "")
			    (ml4pg-show-clusters-dynamic-b)
			    )
nil
)
      (ml4pg-assign-values (car temp) n))
    )))

(defvar ml4pg-granularity-dynamic 0)

(defun ml4pg-show-clusters-dynamic ()
  (interactive)
  (setf ml4pg-granularity-dynamic (read-string "Introduce the granularity level (values from 1 to 5): "))
  (progn 
    (setf ml4pg-signal 3)
    (setf ml4pg-my-buffer "")
    (with-temp-file (expand-file-name "temp.csv") (insert (ml4pg-extract-features-dynamic)))
    (switch-to-buffer-other-window "*display*")
    (require 'comint)
    (cond ((string= "1" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,3,100)\n")))
	  ((string= "2" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,5,100)\n")))
	  ((string= "3" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,10,100)\n")))
	  ((string= "4" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,15,100)\n")))
	  ((string= "5" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,20,100)\n")))
	  (t (ml4pg-show-clusters-dynamic)))
    
  ))

(defun ml4pg-show-clusters-dynamic-b ()
  (interactive)
  (progn 
    (setf ml4pg-signal 3)
    (setf ml4pg-my-buffer "")
    (with-temp-file (expand-file-name "temp.csv") (insert (ml4pg-extract-features-dynamic)))
    (require 'comint)
    (cond ((string= "1" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,3,100)\n")))
	  ((string= "2" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,5,100)\n")))
	  ((string= "3" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,10,100)\n")))
	  ((string= "4" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,15,100)\n")))
	  ((string= "5" ml4pg-granularity-dynamic)
	   (comint-send-string (get-buffer-process "*matlab*") (concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp,20,100)\n")))
	  (t (ml4pg-show-clusters-dynamic)))
    ;(comint-send-string (get-buffer-process "*matlab*")
;			(concat "load " (expand-file-name "temp.csv") "; kmeans_clusters_and_frequencies(temp," 
;				(format "%s" (floor (length (extract-list-without-strings saved-theorems2)) 5) ) ",100)\n"))   
  ))