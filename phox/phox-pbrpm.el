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
(defun phox-pbrpm-regexps ()
  (setq
    goal-backward-regexp "^goal [0-9]+/[0-9]+$"
    goal-number-regexp "[0-9]+"
    hyp-backward-regexp "[^A-Za-z0-9_.']\\([A-Za-z0-9_.']+\\) :="
    ccl-backward-regexp "|-")
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

(defun phox-pbrpm-generate-menu (click-infos region-infos)
; This FAKE function will be replace by a real 'generate-menu' once the code will be judged stable

"Use informations to build a list of (name , rule)"
   ;click-infos = (goal-number, "whole"/hyp-name/"none", expression, depth-tree-list)
   ;region-infos = idem if in the goal buffer, (0, "none", expression, nil ) if in another buffer, do not display if no region available.

   (setq pbrpm-rules-list (list))

   ; the first goal is the selected one by default, so we prefer not to display it.

   ; if clicking in a conclusion => select.intro
   (if (and (string= (nth 1 click-infos) "none") (not region-infos))
      (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list
	     (list "Décompose"
               (if (= (nth 0 click-infos) 1)
                  (identity "intro. ")
                  (concat "select " (int-to-string (nth 0 click-infos)) ". intro. ")))
	     (list "Décompose plusieurs"
               (if (= (nth 0 click-infos) 1)
                  (identity "intros. ")
                  (concat "select " (int-to-string (nth 0 click-infos)) ". intros. ")))
		  );end list's
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
		     (list (list "Produit la conclusion"
               (if (= (nth 0 click-infos) 1)
                  (concat "elim "
                     (nth 1 click-infos)
                     ". ")
                  (concat "select "
                     (int-to-string (nth 0 click-infos))
                     ". elim "
                     (nth 1 click-infos)
                     ". "))))))
      (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list (list "QED"
               (if (= (nth 0 click-infos) 1)
                  (concat "axiom "
                     (nth 1 click-infos)
                     ". ")
                  (concat "select "
                     (int-to-string (nth 0 click-infos))
                     ". axiom "
                     (nth 1 click-infos)
                     ". "))))))))

   ; if clicking in an hypothesis => select.left
   (if (and
         (not (or (string= (nth 1 click-infos) "none")
            (string= (nth 1 click-infos) "whole")))
         (not region-infos))
      (setq pbrpm-rules-list
      (append pbrpm-rules-list
         (list (list "Décompose"
            (if (= (nth 0 click-infos) 1)
		(concat "left "
			(nth 1 click-infos)
                     ". ")
               (concat "select "
		       (int-to-string (nth 0 click-infos))
		       ". left"
		  (nth 1 click-infos)
                     ". ")
 		  ))
	       (list "Décompose plusieurs"
            (if (= (nth 0 click-infos) 1)
		(concat "lefts "
			(nth 1 click-infos)
                     ". ")
               (concat "select "
		       (int-to-string (nth 0 click-infos))
		       ". lefts"
		  (nth 1 click-infos)
                     ". ")
 		  ))))))


   ; if region is an hypothesis (ie in the goals buffer) and clicking in that hyp's goal =>
   (if region-infos
   (if (and
         (not (or (string= (nth 1 region-infos) "none")
            (string= (nth 1 region-infos) "whole")))
         (equal (nth 0 click-infos) (nth 0 region-infos))
      )
      (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list (list "Réécrit la conclusion"
               (if (= (nth 0 click-infos) 1)
                  (concat "rewrite "
                     (nth 1 region-infos)
                     ". ")
                  (concat "select "
                     (int-to-string (nth 0 click-infos))
                     ". rewrite "
                     (nth 1 region-infos)
                     ". ")))))))
   )

   (if (and         
	(not (or (string= (nth 1 click-infos) "none")
		 (string= (nth 1 click-infos) "whole")))
	(not (string= (nth 2 region-infos) ""))
	)
       (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list (list "Applique l'hypothèse à une expression"
               (if (= (nth 0 click-infos) 1)
               (concat "apply "
                  (nth 1 click-infos)
                  " with "
                  (nth 2 region-infos)
                  ". ")
               (concat "select "
                  (int-to-string (nth 0 click-infos))
                  ". select "
                  (nth 1 click-infos)
                  " with "
                  (nth 2 region-infos)
                  ". ")))))))

   ; if region is an hypothesis (ie in the goals buffer) and clicking in an (other) hyp', both in the same goal => 
   (if region-infos
   (if (and
         (not (or (string= (nth 1 click-infos) "none")
            (string= (nth 1 click-infos) "whole")))
         (not (or (string= (nth 1 region-infos) "none")
            (string= (nth 1 region-infos) "whole")))
         (equal (nth 0 click-infos) (nth 0 region-infos))
         (not (string= (nth 1 click-infos) (nth 1 region-infos)))
      )
      (progn 
         (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list (list "Réécrit l'hypothèse"
               (if (= (nth 0 click-infos) 1)
               (concat "rewrite_hyp "
                  (nth 1 click-infos)
                  " "
                  (nth 1 region-infos)
                  ". ")
               (concat "select "
                  (int-to-string (nth 0 click-infos))
                  ". rewrite_hyp "
                  (nth 1 click-infos)
                  " "
                  (nth 1 region-infos)
                  ". "))))))
       (setq pbrpm-rules-list
         (append pbrpm-rules-list
            (list (list "Applique l'hypothèse à une autre hypothèse"
               (if (= (nth 0 click-infos) 1)
               (concat "apply "
                  (nth 1 click-infos)
                  " with "
                  (nth 1 region-infos)
                  ". ")
               (concat "select "
                  (int-to-string (nth 0 click-infos))
                  ". select "
                  (nth 1 click-infos)
                  " with "
                  (nth 1 region-infos)
                  ". "))))))))

  )

   (identity pbrpm-rules-list)
)


;;--------------------------------------------------------------------------;;
;; Selections Buffer management -- unused for now
;;--------------------------------------------------------------------------;;
;initialize the selections buffer for the PBRPM mode
;1 buffer for every selections
(display-buffer (generate-new-buffer (generate-new-buffer-name "phox-selections")))

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
(defalias 'proof-pbrpm-regexps 'phox-pbrpm-regexps)

;;--------------------------------------------------------------------------;;
(require 'pg-pbrpm)
(provide 'phox-pbrpm)
;; phox-pbrpm ends here