;; $State$ $Date$ $Revision$ 
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; the proof by rules popup menu part
;;
;; Note : program extraction is still experimental This file is very
;; dependant of the actual state of our developments
;;--------------------------------------------------------------------------;;

;;--------------------------------------------------------------------------;;
;; Syntactic functions
;;--------------------------------------------------------------------------;;
(setq
 pg-pbrpm-start-goal-regexp "^goal \\([0-9]+\\)/[0-9]+\\( (new)\\)?$"
 pg-pbrpm-start-goal-regexp-par-num 1
 pg-pbrpm-end-goal-regexp "^$"
 pg-pbrpm-start-hyp-regexp "^\\([A-Za-z0-9_.']+\\) := "
 pg-pbrpm-start-hyp-regexp-par-num 1
 pg-pbrpm-start-concl-regexp "^ *|- "
 pg-pbrpm-auto-select-regexp "\\(\\(['a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)\\(_+\\(['a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)\\)*\\)\\|\\(\\?[0-9]+\\)"
)


; TODO : deal with future invisible parentheses (french guillemots)
(defun phox-pbrpm-left-paren-p (char)
"Retrun t if the character is a left parenthesis : '(' or a french guillemot '<<'"
   (or
   (char-equal char (int-char 40))
   (char-equal char (int-char 171)))
)

(defun phox-pbrpm-right-paren-p (char)
"Retrun t if the character is a right parenthesis ')' or a french guillemot '>>'"
   (or
   (char-equal char (int-char 41))
   (char-equal char (int-char 187)))
)

;;--------------------------------------------------------------------------;;
;; Testing Menu
;;--------------------------------------------------------------------------;;

(defun phox-pbrpm-exists (f l0)
  (if (null l0) nil
    (or (funcall f (car l0)) (phox-pbrpm-exists f (cdr l0)))))

(defun phox-pbrpm-eliminate-id (acc l)
  (if (null l) (reverse acc)
    (message "call")
    (message (nth 0 (car l)))
    (message (nth 1 (car l)))
    (if 
	(phox-pbrpm-exists (lambda (x) 
			     (progn 
			       (message "=")
			       (message (nth 0 x))
			       (message (nth 0 (car l)))
			       (string= (nth 0 x) (nth 0 (car l))))) acc)
	(phox-pbrpm-eliminate-id acc (cdr l))
      (phox-pbrpm-eliminate-id (cons (car l) acc) (cdr l)))))

(defun phox-pbrpm-menu-from-string (str)
  "build a menu from a string send by phox"
  (if (string= str "") nil
    (phox-pbrpm-eliminate-id nil (mapcar 
				  (lambda (s) (progn (message s) (split-string s "\\\\-"))) 
				  (split-string str "\\\\\\\\")))))

(defun phox-pbrpm-generate-menu (click-infos region-infos)
; This FAKE function will be replace by a real 'generate-menu' once the code will be judged stable

"Use informations to build a list of (name , rule)"
   ;click-infos = (goal-number, "whole"/hyp-name/"none", expression, depth-tree-list)
   ;region-infos = idem if in the goal buffer, (0, "none", expression, nil ) if in another buffer, do not display if no region available.

   (let
     ((pbrpm-rules-list nil)
      (goal-prefix
       (if (= (nth 0 click-infos) 1) "" 
	 (concat "["
		 (int-to-string (nth 0 click-infos))
		 "] "))))
 

   ; the first goal is the selected one by default, so we prefer not to display it.

   ; if clicking in a conclusion => select.intro
     (if (and (string= (nth 1 click-infos) "none") (not region-infos))
	 (setq pbrpm-rules-list
	       (append pbrpm-rules-list
		       (list
			(list 10 "Trivial ?" (concat goal-prefix "trivial."))
			(list 4 "Par l'absurde" (concat goal-prefix "by_absurd;; elim False.")))
			(mapcar (lambda (l) (cons 0 l)) (phox-pbrpm-menu-from-string 
			 (proof-shell-invisible-cmd-get-result 
			  (concat "menu_intro "
				  (int-to-string (nth 0 click-infos))
				  "."))))
		       ); end append
	       );end setq
       );end if

					; if clicking in an hypothesis => select.elim
     (if (and
	  (not (or (string= (nth 1 click-infos) "none")
		   (string= (nth 1 click-infos) "whole")))
	  (not region-infos))
	 (progn 
	   (setq pbrpm-rules-list
		 (append pbrpm-rules-list
			 (list (list 3 (concat
				      "Déduit la conclusion de "
				      (nth 1 click-infos)
				      " (génère éventuellement de nouveaux buts) ?")
				     (concat goal-prefix
					     "elim "
					     (nth 1 click-infos)
					     ". "))
			       (list 3 (concat
				      "Rentre les négations (loi de De Morgan) de "
				      (nth 1 click-infos) " ?")
				     (concat goal-prefix "rewrite_hyp "
					     (nth 1 click-infos)
					     " demorganl."))
			       (list 4 (concat
				      "Conclustion égale à "
				      (nth 1 click-infos) " ?")
				     (concat goal-prefix
					     "axiom "
					     (nth 1 click-infos)
					     ". ")))))))
     
					; if clicking in an hypothesis => select.left
     (if (and
	  (not (or (string= (nth 1 click-infos) "none")
            (string= (nth 1 click-infos) "whole")))
         (not region-infos))
	 (progn
	   (if (char= ?t (string-to-char (proof-shell-invisible-cmd-get-result 
					  (concat "is_equation "
						  (int-to-string (nth 0 click-infos))
						  " \""
						  (nth 1 click-infos)
						  "\"."))))
	       (setq pbrpm-rules-list
		     (append pbrpm-rules-list
			     (list (list 2 
				    (concat "Récrit la conclusion avec "
					    (nth 1 click-infos)
					    " ?")
				     (concat goal-prefix 
					     "rewrite "
					     (nth 1 click-infos)
					     ". "))))))
	   (setq pbrpm-rules-list
		 (append pbrpm-rules-list			
			 (mapcar (lambda (l) (cons 0 l)) (phox-pbrpm-menu-from-string 
			  (proof-shell-invisible-cmd-get-result 
			   (concat "menu_left "
				  (int-to-string (nth 0 click-infos))
				  (nth 1 click-infos)
				  "."))))))))

   ; if region is an hypothesis (ie in the goals buffer) and clicking in that hyp's goal =>
;   (if (and
;	region-infos
;	(string= (nth 1 click-infos) "none")
;	(not (or (string= (nth 1 region-infos) "none")
;		 (string= (nth 1 region-infos) "whole")))
;	(equal (nth 0 click-infos) (nth 0 region-infos))
;	(string-to-char (proof-shell-invisible-cmd-get-result 
;			 (concat "is_equation "
;				 (int-to-string (nth 0 region-infos))
;				 " \""
;				 (nth 1 region-infos)
;				 "\"."))))
;      (setq pbrpm-rules-list
;         (append pbrpm-rules-list
;            (list (list (concat "Récrit la conclusion avec " (nth 1 region-infos))
;			(concat goal-prefix "rewrite " (nth 1 region-infos) ". "))))))

   (if (not (string= (nth 2 click-infos) ""))
       (let ((r (proof-shell-invisible-cmd-get-result (concat "is_definition "
							      (int-to-string (nth 0 click-infos))
							      " \""
							      (nth 2 click-infos)
							      "\"."))))
	 (if (char= (string-to-char r) ?t)
	     (setq pbrpm-rules-list
		   (append pbrpm-rules-list
			   (list (list 1 (concat 
					"Ouvre la définition: "
					(nth 2 click-infos))
				       (concat 
					goal-prefix
					(if (or (string= (nth 1 click-infos) "none") 
						(string= (nth 1 click-infos) "whole"))
					    "unfold " 
					  (concat "unfold_hyp " (nth 1 click-infos) " "))
					(nth 2 click-infos)
					". ")))))
	 (if (and (char= (string-to-char (nth 2 click-infos)) ??)
		  region-infos)
	     (setq pbrpm-rules-list
		   (append pbrpm-rules-list
			   (list (list 0 (concat 
					"Instancie "
					(nth 2 click-infos)
					" avec "
					(nth 2 region-infos))
				       (concat 
					goal-prefix
					"instance "
					(nth 2 click-infos) 
					" "
					(nth 2 region-infos)
					". ")))))))))   
   (if (and         
	(not (or (string= (nth 1 click-infos) "none")
		 (string= (nth 1 click-infos) "whole")))
	(nth 2 region-infos))
       (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list (list 4 (concat "Applique "
				(nth 1 click-infos)
				 " à l'expression "
				 (nth 2 region-infos) " ?") 
			(concat goal-prefix 
				"apply "
				(nth 1 click-infos)
				" with "
				(nth 2 region-infos)
				". "))))))

   ; if region is an hypothesis (ie in the goals buffer) and clicking in an (other) hyp', both in the same goal => 
   (if (and region-infos
         (not (or (string= (nth 1 click-infos) "none")
            (string= (nth 1 click-infos) "whole")))
         (not (or (string= (nth 1 region-infos) "none")
            (string= (nth 1 region-infos) "whole")))
         (equal (nth 0 click-infos) (nth 0 region-infos))
         (not (string= (nth 1 click-infos) (nth 1 region-infos)))
      )
      (progn 
	(if (char= ?t (string-to-char (proof-shell-invisible-cmd-get-result 
			     (concat "is_equation "
				     (int-to-string (nth 0 click-infos))
				     " \""
				     (nth 1 click-infos)
				  "\"."))))
	(setq pbrpm-rules-list
	      (append pbrpm-rules-list
		      (list 
		       (list 4 (concat 
			      "Récrit " (nth 1 region-infos) 
			      " avec l'équation " (nth 1 click-infos) " ?")
				 (concat goal-prefix
					 "rewrite_hyp "
					 (nth 1 region-infos)
					 " "
					 (nth 1 click-infos)
					 ". "))))))
	 (setq pbrpm-rules-list
	       (append pbrpm-rules-list
		       (list
			(list 4 (concat 
			       "Applique " (nth 1 click-infos) 
			       " avec l'hypothèse " (nth 1 region-infos) " ?")
			      (concat goal-prefix 
				      "apply "
				      (nth 1 click-infos)
				      " with "
				      (nth 1 region-infos)
				      ". ")))))))

   pbrpm-rules-list
))

;;--------------------------------------------------------------------------;;
;; Selections Buffer management -- unused for now
;;--------------------------------------------------------------------------;;
;initialize the selections buffer for the PBRPM mode
;1 buffer for every selections
;(display-buffer (generate-new-buffer (generate-new-buffer-name "phox-selections")))

;copy the current region in the selections buffer
(defun pg-pbrpm-add-selection ()
"Append the selection of the current buffer to
the phox-selections buffer used with PBRPM."
  (interactive)
  ;TODO : check wether the selected region is a well formed expression
  ;copy at the end of the selections buffer before switching to it
  ; else we'll loose mark & point
  (switch-to-buffer (get-buffer "phox-selections"))
  (goto-char (point-max))
  (insert-string (get-selection))
  ; if the selected region already ends with a \n, don't insert a second one
  (if (not (bolp))
      (insert-string "\n"))
  (insert-string "\n")
  ;buffer is ready to receive a new selection
)

;clean the phox-selections buffer
(defun pg-pbrpm-clean-selections-buffer ()
"Clean the phox-selections buffer used with PBRPM."
  (interactive)
  (erase-buffer (get-buffer "phox-selections"))
)

;selections management menu
(defvar phox-pbrpm-menu
"Phox menu for dealing with Selections."
   '("Selections"
   ["Add Selection" pg-pbrpm-add-selection ]
   ["Clean Selections buffer" pg-pbrpm-clean-selections-buffer ]
   )
) ;see phox.el > menu-entries


;;--------------------------------------------------------------------------;;
;; phox specific functions
;;--------------------------------------------------------------------------;;

(defalias 'proof-pbrpm-generate-menu 'phox-pbrpm-generate-menu)
(defalias 'proof-pbrpm-left-paren-p 'phox-pbrpm-left-paren-p)
(defalias 'proof-pbrpm-right-paren-p 'phox-pbrpm-right-paren-p)

;;--------------------------------------------------------------------------;;
(require 'pg-pbrpm)
(provide 'phox-pbrpm)
;; phox-pbrpm ends here