;;; The menu interaction

(easy-menu-define ml4pg-menu global-map "Statistics"
  '("Statistics" 
    ("Configuration" 
     ("Algorithm"
       ["K-means" (ml4pg-change-algorithm "k")
	:selected (string= ml4pg-algorithm "k")
	:style toggle
	:help "Use k-means algorithm"]
       ["Gaussian" (ml4pg-change-algorithm "g")
	:selected (string= ml4pg-algorithm "g")
	:style toggle
	:active (string= ml4pg-ml-system "m")
	:help "Use Gaussian algorithm"]
       ["EM" (ml4pg-change-algorithm "e")
	:selected (string= ml4pg-algorithm "e")
	:style toggle
	:active (string= ml4pg-ml-system "w")
	:help "Use Simple EM algorithm"]
       ["FarthestFirst" (ml4pg-change-algorithm "f")
	:selected (string= ml4pg-algorithm "f")
	:style toggle
	:active (string= ml4pg-ml-system "w")
	:help "Use FarhestFirst algorithm"])
      ("Granularity"
       ["1"  (ml4pg-change-granularity 1)
	:selected (eq ml4pg-granularity-level 1)
	:style toggle
	:help "We will use 3 clusters"]
       ["2"  (ml4pg-change-granularity 2)
	:selected (eq ml4pg-granularity-level 2)
	:style toggle
	:help "We will use 5 clusters"]
       ["3"  (ml4pg-change-granularity 3)
	:selected (eq ml4pg-granularity-level 3)
	:style toggle
	:help "We will use 10 clusters"]
       ["4"  (ml4pg-change-granularity 4)
	:selected (eq ml4pg-granularity-level 4)
	:style toggle
	:help "We will use 15 clusters"]
       ["5"  (ml4pg-change-granularity 5)
	:selected (eq ml4pg-granularity-level 5)
	:style toggle
	:help "We will use 20 clusters"])
      ("Frequencies"
       ["1" (ml4pg-change-frequency 1)
	:selected (eq ml4pg-frequency-precision 1)
	:style toggle
	:help "The experiments will be run 100 times"]
       ["2" (ml4pg-change-frequency 2)
	:selected (eq ml4pg-frequency-precision 2)
	:style toggle
	:help "The experiments will be run 500 times"]
       ["3" (ml4pg-change-frequency 3)
	:selected (eq ml4pg-frequency-precision 3)
	:style toggle
	:help "The experiments will be run 1000 times"]))
    ["Extract info up to point" (ml4pg-extract-feature-theorems)
     :keys "C-c SPC"]
    ["Show clusters" (ml4pg-show-clusters-bis)
     :keys "C-c c"]
    ["Show similar theorems" (ml4pg-show-clusters-of-theorem)
     :keys "C-c m"]
    ["Export library" (ml4pg-save-numbers)
     :keys "C-c n"]
    ["Show cluster libraries" (ml4pg-exported-libraries)]
    ["Activate Icons" (ml4pg-activate-icons)]
))

(easy-menu-remove-item global-map '("menu-bar") "Statistics")

(easy-menu-add-item nil nil ml4pg-menu "help-menu") 

(defun ml4pg-activate-icons ()
  (interactive)
  (progn 
    (easy-menu-remove-item nil '("Statistics") "Activate Icons")
    (define-key coq-mode-map [tool-bar statistical-hint]
      (list 'menu-item "Statistical Hint" 'ml4pg-show-clusters-of-theorem
		  :help "Statistical Hint"
		  :image (list 'image :type 'xpm 
				:file (concat ml4pg-home-dir "icons/sh-hint.xpm"))))
    (define-key coq-mode-map [tool-bar clustering]
      (list 'menu-item "Clustering" 'ml4pg-show-clusters-bis
		  :help "Clustering"
		  :image (list 'image :type 'xpm 
				:file (concat ml4pg-home-dir "icons/clustering.xpm"))))))


(defvar ml4pg-ml-system "w")
(defvar ml4pg-algorithm "k")
(defvar ml4pg-granularity-level 3)
(defvar ml4pg-frequency-precision 1)
(defvar ml4pg-iterative nil)
(defvar ml4pg-save-automatically nil)
(defvar ml4pg-level "g")


(defun ml4pg-change-level (n)
  (setq ml4pg-level n))

(defun ml4pg-change-algorithm (s)
  (setq ml4pg-algorithm s))

(defun ml4pg-change-ml-system (s)
  (setq ml4pg-ml-system s)
  (setq ml4pg-algorithm "k")
  (cond ((string= s "w")
	 (setq ml4pg-iterative nil)
	 ))
  )
  
(defun ml4pg-change-granularity (n)
  (setq ml4pg-granularity-level n))

(defun ml4pg-change-frequency (n)
  (setq ml4pg-frequency-precision n))

(defun ml4pg-change-iterative-search ()
  (setq ml4pg-iterative (not ml4pg-iterative)))

(defun ml4pg-change-save ()
  (setq ml4pg-save-automatically (not ml4pg-save-automatically)))

      
;(easy-menu-add-item nil '("Statistics") statistics-menu "help-menu") 

(defun ml4pg-change-algorithm-interactive ()
  (interactive)
  (let ((alg (read-string 
	      "What algorithm do you want to use (k-means -> k, Gaussian -> g): ")))
    (setf ml4pg-algorithm (cond ((string= "g" alg) "g") 
			  ((string= "k" alg) "k")
			  (t ml4pg-algorithm)))))

(defun ml4pg-change-granularity-interactive ()
  (interactive)
  (let ((alg (read-string 
	      "Introduce the granularity level (values from 1 to 5): ")))
    (setf ml4pg-granularity-level (cond ((string= "1" alg) 1) 
				  ((string= "2" alg) 2)
				  ((string= "3" alg) 3)
				  ((string= "4" alg) 4)
				  ((string= "5" alg) 5)
				  (t granularity-level)))))

(defun ml4pg-change-frequency-interactive ()
  (interactive)
  (let ((alg (read-string 
 "Introduce the precision of the frequencies that you want to obtain (values from 1 to 3): ")))
    (setf ml4pg-frequency-precision (cond ((string= "1" alg) 1) 
				  ((string= "2" alg) 2)
				  ((string= "3" alg) 3)
				  (t ml4pg-frequency-precision)))))

(defun change-iterative-interactive ()
  (interactive)
  (let ((alg (read-string 
 "Do you want to perform iterative search? (yes -> y, no -> n): ")))
    (setf ml4pg-iterative (cond ((string= "y" alg) 1) 
			  ((string= "n" alg) 2)
			  (t ml4pg-iterative)))))



(defun ml4pg-exported-libraries ()
  (interactive)
  (easy-menu-remove-item nil '("Statistics") "Show cluster libraries")
  (easy-menu-add-item nil '("Statistics") 
		      (cons "Available libraries for clustering:"
			   (cons ["Current" nil
			    :selected t
			    :style toggle
			    :help "Use the current library for clustering"]
			   (ml4pg-select-libraries)))))


(defun ml4pg-select-libraries ()
  (ml4pg-available-libraries)
  (ml4pg-available-dirs)
  (append (ml4pg-select-libraries-aux ml4pg-libs nil) (ml4pg-libraries-dirs)))


(defun ml4pg-select-libraries-aux (temp temp2)
  (if (endp temp)
      temp2
    (ml4pg-select-libraries-aux (cdr temp) (append temp2 (list (ml4pg-menu-library (car temp)))))))




(defvar ml4pg-libs nil)

(defun ml4pg-available-libraries ()
  (shell-command  (concat "ls " ml4pg-home-dir "libs/ssreflect | grep .csv | wc -l"))
  (let ((n nil)
	(i 0))
  (with-current-buffer "*Shell Command Output*"
    (beginning-of-buffer)
    (setq n (string-to-number (format "%s"  (read (current-buffer))))))
  (shell-command  (concat "ls " ml4pg-home-dir "libs/ssreflect | grep .csv"))
  (with-current-buffer "*Shell Command Output*"
    (progn (beginning-of-buffer)
	   (while (< i n)
	     (let ((r (format "%s" (read (current-buffer)))))
	       (progn (setq i (1+ i))
		      (setq ml4pg-libs (append ml4pg-libs (list (subseq r 0 (search "." r))))))))))))



(defvar ml4pg-dirs nil)

(defun ml4pg-available-dirs ()
  (shell-command  (concat "ls -d " ml4pg-home-dir "libs/ssreflect/*/ | wc -l"))
  (let ((n nil)
	(i 0))
  (with-current-buffer "*Shell Command Output*"
    (beginning-of-buffer)
    (setq n (string-to-number (format "%s"  (read (current-buffer))))))
  (shell-command  (concat "ls -d " ml4pg-home-dir "libs/ssreflect/*/"))
  (with-current-buffer "*Shell Command Output*"
    (progn (beginning-of-buffer)
	   (while (< i n)
	     (let ((r (format "%s" (read (current-buffer)))))
	       (progn (setq i (1+ i))
		      (setq ml4pg-dirs (append ml4pg-dirs (list (subseq r (length (concat ml4pg-home-dir "libs/ssreflect/")) (1- (length r)))))))))))
  ))




(defun ml4pg-libraries-dirs ()
  (do ((temp ml4pg-dirs (cdr temp))
       (temp2 nil))
      ((endp temp) temp2)
      (setf temp2 (append temp2 (list (append (list (car temp)) (ml4pg-libraries-dir (car temp))))))))
      


(defun ml4pg-libraries-dir (dir)
  (shell-command  (concat "ls " ml4pg-home-dir "libs/ssreflect/" dir "/ | grep _names | wc -l"))
  (let ((n nil)
	(i 0)
	(temp nil))
  (with-current-buffer "*Shell Command Output*"
    (beginning-of-buffer)
    (setq n (string-to-number (format "%s"  (read (current-buffer))))))
  (shell-command  (concat "ls " ml4pg-home-dir "libs/ssreflect/" dir "/ | grep _names"))
  (with-current-buffer "*Shell Command Output*"
    (progn (beginning-of-buffer)
	   (while (< i n)
	     (let* ((r1 (format "%s" (read (current-buffer))))
		    (r (subseq r1 0 (search "_names" r1))))
	       (progn (setq i (1+ i))
		      (setq temp (append temp (list (ml4pg-menu-library-dir (subseq r 0 (search "." r)) dir)))))))
))
  temp))



(defun ml4pg-menu-library-dir (item dir)
  (vector item (list 'ml4pg-change-library (concat dir "/" item)) 
    :selected (list 'ml4pg-string-member (concat dir "/" item) 'ml4pg-libs-menus)
    :style 'toggle
    :help (format "Use the %s library for clustering" item)))

(defun ml4pg-menu-library (item)
  (vector item (list 'change-library item) 
    :selected (list 'ml4pg-string-member item 'ml4pg-libs-menus)
    :style 'toggle
    :help (format "Use the %s library for clustering" item)))



(defvar ml4pg-libs-menus nil)

(defun ml4pg-string-member (string list)
  (do ((temp list (cdr temp))
       (is nil))
      ((or (endp temp) is) is)
      (if (string= string (car temp))
	  (setf is t))))


(defun ml4pg-change-library (string)
  (if (ml4pg-string-member string ml4pg-libs-menus)
      (ml4pg-remove-from-menus string)
    (setq ml4pg-libs-menus (append ml4pg-libs-menus (list string)))))


(defun ml4pg-remove-from-menus (string)
  (do ((temp ml4pg-libs-menus (cdr temp))
       (temp2 nil))
      ((endp temp) (setf ml4pg-libs-menus temp2))
      (if (not (string= string (car temp)))
	  (setf temp2 (append temp2 (list (car temp)))))))




  


	  


