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
 pg-pbrpm-auto-select-regexp "\\(\\(\\(['a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)\\)\\(_+\\(\\(['a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)\\)\\)*\\)\\|\\(\\?[0-9]+\\)"
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


(defun phox-pbrpm-menu-from-string (order str)
  "build a menu from a string send by phox"
  (setq str (proof-shell-invisible-cmd-get-result str))
  (if (string= str "") nil
    (mapcar 
     (lambda (s) (progn (cons order (split-string s "\\\\-"))))
     (split-string str "\\\\\\\\"))))

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

   ; if clicking in a conclusion with no selection
     (if (and (string= (nth 1 click-infos) "none") (not region-infos))
	 (setq pbrpm-rules-list
	       (append pbrpm-rules-list
		       (list
			(list 10 "Trivial ?" (concat goal-prefix "trivial."))
			(list 4 "Par l'absurde" (concat goal-prefix "by_absurd;; elim False.")))
		       (phox-pbrpm-menu-from-string 0
						    (concat "menu_intro "
							    (int-to-string (nth 0 click-infos))
							    "."))
		       (phox-pbrpm-menu-from-string 0
						    (concat "menu_evaluate "
							    (int-to-string (nth 0 click-infos))
							    "."))
		       ); end append
	       );end setq
       );end if

   ; if clicking a conclusion with a selection
   (if (and (string= (nth 1 click-infos) "none") region-infos)
       (setq pbrpm-rules-list
         (append pbrpm-rules-list
		 (phox-pbrpm-menu-from-string 1
		       (concat "menu_rewrite "
			       (int-to-string (nth 0 click-infos)) " "
			       (let ((tmp ""))
				 (mapc (lambda (region-info)
					 (setq tmp 
					       (concat tmp " " (nth 1 region-info))))
				       region-infos)
				 tmp)
			       ".")))))

    ; if clicking in an hypothesis with no selection
     (if (and
	  (not (or (string= (nth 1 click-infos) "none")
		   (string= (nth 1 click-infos) "whole")))
	  (not region-infos))
	 (progn 
	   (setq pbrpm-rules-list
		 (append pbrpm-rules-list
			 (list
			  (list 9 (concat "Supprimer l'hypothèse " (nth 1 click-infos) " devenue inutile.") (concat "rmh " (nth 1 click-infos) ".")))
			 (phox-pbrpm-menu-from-string 1
						      (concat "menu_elim "
							      (int-to-string (nth 0 click-infos)) " "
							      (nth 1 click-infos)
							      "."))
			 (phox-pbrpm-menu-from-string 1
						      (concat "menu_evaluate_hyp "
							      (int-to-string (nth 0 click-infos)) " "
							      (nth 1 click-infos)
							      "."))
			 (phox-pbrpm-menu-from-string 0
						       (concat "menu_left "
							       (int-to-string (nth 0 click-infos))
							       " "
							       (nth 1 click-infos)
							       "."))))))

   ; if clicking on an hypothesis with a selection
   (if (and         
	(not (or (string= (nth 1 click-infos) "none")
		 (string= (nth 1 click-infos) "whole")))
	region-infos)
       (setq pbrpm-rules-list
         (append pbrpm-rules-list
		 (phox-pbrpm-menu-from-string 1
		       (concat "menu_apply "
			       (int-to-string (nth 0 click-infos)) " "
			       (nth 1 click-infos)
			       (let ((tmp ""))
				 (mapc (lambda (region-info)
					 (setq tmp 
					       (concat tmp " \"" (nth 2 region-info) "\"")))
				       region-infos)
				 tmp)
			       "."))
		 (phox-pbrpm-menu-from-string 1
		       (concat "menu_rewrite_hyp "
			       (int-to-string (nth 0 click-infos)) " "
			       (nth 1 click-infos)
			       (let ((tmp ""))
				 (mapc (lambda (region-info)
					 (setq tmp 
					       (concat tmp " " (nth 1 region-info))))
				       region-infos)
				 tmp)
			       ".")))))

   ; is clicking on a token
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
	   (message (nth 2 click-infos))
	   (if (and (char= (string-to-char (nth 2 click-infos)) ??)
		    region-infos (not (cdr region-infos)))
	       (setq pbrpm-rules-list
		     (append pbrpm-rules-list
			     (list (list 0 (concat 
					    "Instancie "
					    (nth 2 click-infos)
					    " avec "
					    (nth 2 (car region-infos)))
					 (concat 
					  goal-prefix
					  "instance "
					  (nth 2 click-infos) 
					  " "
					  (nth 2 (car region-infos))
					  ". ")))))))))

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