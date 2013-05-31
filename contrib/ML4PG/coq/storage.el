(defun ml4pg-save-lemma-aux (string)
  (append-to-file string nil (concat ml4pg-home-dir "lemmas.txt"))  
)

(defun ml4pg-save-lemma (name value)
  (ml4pg-save-lemma-aux (format "%s&%s$" name value)))


(defun ml4pg-save-view-aux (string)
  (append-to-file string nil (concat ml4pg-home-dir "views.txt"))  
)

(defun ml4pg-save-view (name value)
  (sml4pg-ave-view-aux (format "%s&%s$" name value)))


(defun ml4pg-read-lemmas ()
  (if (file-exists-p (concat ml4pg-home-dir "coq/lemmas.txt"))
      (with-temp-buffer
	(insert-file-contents (concat ml4pg-home-dir "coq/lemmas.txt"))
	(let ((temp (format "%s" (read (current-buffer)))))
	  (setf ml4pg-theorems_id (ml4pg-extract-info-from-files temp))
	  ))))

(defun ml4pg-read-views ()
  (if (file-exists-p (concat ml4pg-home-dir "coq/views.txt"))
      (with-temp-buffer
	(insert-file-contents (concat ml4pg-home-dir "coq/views.txt"))
	(let ((temp (format "%s" (read (current-buffer)))))
	  (setf ml4pg-views_id (ml4pg-extract-info-from-files temp))
	  ))))

(defun ml4pg-extract-info-from-files (string)
  (do ((temp string)
       (temp2 nil))
      ((not (search "$" temp)) temp2)
      (let ((dollar (search "$" temp))
	    (amper (search "&" temp)))
	(progn 
	  (setf temp2 (append temp2 (list (cons (subseq temp 0 amper)
					 (string-to-number (subseq temp (1+ amper) dollar))))))
	       (setf temp (subseq temp (1+ dollar)))))))









