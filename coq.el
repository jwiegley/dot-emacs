;; coq.el Major mode for Coq proof assistant
;; Copyright (C) 1994, 1995, 1996, 1997 LFCS Edinburgh. 
;; Author: Healfdene Goguen and Thomas Kleymann

;; $Log$
;; Revision 1.21  1998/05/12 14:51:27  hhg
;; Added hook `coq-shell-init-hook', for `proof-shell-insert-hook'.
;; This initializes undo limit and changes directory to that associated
;; with buffer.
;; This is because Coq has a command line option to run with emacs mode.
;;
;; Revision 1.20  1998/05/08 17:08:31  hhg
;; Made separated indentation more elegant.
;; 	Fixed bug with Inductive.
;; 	Added CoInductive.
;;
;; Revision 1.19  1998/05/08 15:42:42  hhg
;; Merged indentation code for LEGO and Coq into proof.el.
;;
;; Revision 1.18  1998/05/06 16:39:10  hhg
;; Removed default instantiation of undo limit to 100.
;;
;; Revision 1.17  1998/05/06 15:29:11  hhg
;; Added coq-info-dir so that script-management.info can be hard-coded.
;;
;; Revision 1.16  1998/05/05 14:21:48  hhg
;; Made updates to fix problem with Definition, which couldn't be
;; used with proof scripts.
;; Removed some useless declarations.
;; Removed Abort from menu.
;; Now Reset's if user undoes to beginning of proof.
;; Added command to increase undo limit for Coq, and set default to 100.
;;
;; Revision 1.15  1998/03/25 17:30:35  tms
;; added support for etags at generic proof level
;;
;; Revision 1.14  1998/01/15 13:30:18  hhg
;; Added coq-shell-cd
;; Some new fontlocks
;;
;; Revision 1.13  1997/11/26 17:23:51  hhg
;; Added C-c C-s to run "Search" in Coq.
;; Moved coq-goal-with-hole-regexp etc to coq-fontlock.
;; Removed various superfluous definitions for COQPATH etc.
;;
;; Revision 1.12  1997/11/24 19:15:08  djs
;; Added proof-execute-minibuffer-cmd and scripting minor mode.
;;
;; Revision 1.11  1997/11/20 13:03:08  hhg
;; Added coq-global-p for global declarations and definitions.  These now
;; get lifted in the same way as lemmas.
;; Changed [meta (control i)] to [meta tab] in key definition.
;; Changed menu, and made help in menu refer to info mode.
;;
;; Revision 1.10  1997/11/17 17:11:15  djs
;; Added some magic commands: proof-frob-locked-end, proof-try-command,
;; proof-interrupt-process. Added moving nested lemmas above goal for coq.
;; Changed the key mapping for assert-until-point to C-c RET.
;;
;; Revision 1.9  1997/11/12 15:56:15  hhg
;; Changed pbp-change-goal so that it only "Show"s the goal pointed at.
;;
;; Revision 1.8  1997/11/06 16:55:49  hhg
;; Assign new variable proof-goal-hyp-fn to coq-goal-hyp, which advances
;; over coq-goal-regexp to pick up goal for pbp
;;
;; Revision 1.7  1997/10/30 15:58:31  hhg
;; Updates for coq, including:
;; 	* pbp-goal-command and pbp-hyp-command use proof-terminal-string
;; 	* updates to keywords
;; 	* fix for goal regexp
;;
;; Revision 1.6  1997/10/24 14:51:09  hhg
;; Fixed coq-count-undos for comments
;;
;; Revision 1.5  1997/10/17 14:51:48  hhg
;; Fixed coq-shell-prompt-pattern to reflect proof-id
;; Changed ";" to "." in coq-save-with-hole-regexp
;; New modifications to syntax table to reflect actual use of symbols in Coq
;;
;; Revision 1.4  1997/10/16 13:14:32  djs
;; Merged Coq changes with main branch.
;;
;; Revision 1.2  1997/10/13 17:12:48  tms
;; *** empty log message ***
;;
;; Revision 1.1.2.3  1997/10/10 19:19:58  djs
;; Added multiple file support, changed the way comments work, fixed a
;; few minor bugs, and merged in coq support by hhg.
;;
;; Revision 1.1.2.2  1997/10/08 08:22:30  hhg
;; Updated undo, fixed bugs, more modularization
;;
;; Revision 1.1.2.1  1997/10/07 13:34:16  hhg
;; New structure to share as much as possible between LEGO and Coq.
;;

;; *** Add indentation in scripts!

(require 'easymenu)
(require 'coq-fontlock)
(require 'outline)
(require 'proof)
(require 'info)

; Configuration

(defconst coq-mode-version-string
  "Coq-MODE. ALPHA Version 1.11 (June 1996) LEGO Team <lego@dcs.ed.ac.uk>")

(defvar coq-tags "/obj/local/coq/V6.2/theories/TAGS"
  "the default TAGS table for the Coq library")

(defconst coq-info-dir "/usr/local/share/info")

(defconst coq-process-config nil
  "Command to configure pretty printing of the Coq process for emacs.")

(defconst coq-interrupt-regexp "Interrupted"
  "Regexp corresponding to an interrupt")

(defvar coq-save-query t
  "*If non-nil, ask user for permission to save the current buffer before
  processing a module.")

(defvar coq-default-undo-limit 100
  "Maximum number of Undo's possible when doing a proof.")

;; ----- web documentation

(defvar coq-www-home-page "http://pauillac.inria.fr/coq/")

;; ----- coq-shell configuration options

(defvar coq-prog-name "/obj/local/coq/V6.2/bin/sun4/coqtop -image /obj/local/coq/V6.2/bin/sun4/coq.out -emacs"
  "*Name of program to run as Coq.")

(defvar coq-shell-working-dir ""
  "The working directory of the coq shell")

(defvar coq-shell-prompt-pattern (concat "^" proof-id " < ")
  "*The prompt pattern for the inferior shell running coq.")

(defvar coq-shell-cd nil ; "Cd \"%s\"."
  "*Command of the inferior process to change the directory.") 

(defvar coq-shell-abort-goal-regexp "Current goal aborted"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar coq-shell-proof-completed-regexp "Subtree proved!"
  "*Regular expression indicating that the proof has been completed.")

(defvar coq-goal-regexp
  "\\(============================\\)\\|\\(subgoal [0-9]+ is:\\)\n")

;; ----- outline

(defvar coq-outline-regexp
  (ids-to-regexp 
	   '("Section" "Chapter" "Goal" "Lemma" "Theorem" "Fact"
	   "Remark" "Record" "Inductive" "Definition")))

(defvar coq-outline-heading-end-regexp "\.\\|\\*)")

(defvar coq-shell-outline-regexp coq-goal-regexp)
(defvar coq-shell-outline-heading-end-regexp coq-goal-regexp)

(defconst coq-kill-goal-command "Abort.")
(defconst coq-forget-id-command "Reset ")

(defconst coq-undoable-commands-regexp (ids-to-regexp coq-tactics))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode coq-shell-mode proof-shell-mode
   "coq-shell" "Inferior shell mode for coq shell"
   (coq-shell-mode-config))

(define-derived-mode coq-mode proof-mode
   "coq" "Coq Mode"
   (coq-mode-config))

(define-derived-mode coq-pbp-mode pbp-mode
  "pbp" "Proof-by-pointing support for Coq"
  (coq-pbp-mode-config))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Popup and Pulldown Menu ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar coq-shared-menu
  (append '(
            ["Display context" coq-ctxt
	      :active (proof-shell-live-buffer)]
            ["Display proof state" coq-prf
	      :active (proof-shell-live-buffer)]
	    ["Exit Coq" coq-exit :active (proof-shell-live-buffer)]
	    "----"
	    ["Find definition/declaration" find-tag-other-window t]
	    ("Help"
	     ["The Coq Proof-assistant (WWW)"
	      (w3-fetch coq-www-home-page)  t]
	     ["Help on Emacs Coq-mode" coq-info-mode t]
	     ))))

(defvar coq-menu  
  (append '("Coq Commands"
            ["Toggle active terminator" proof-active-terminator-minor-mode
	     :active t
	     :style toggle
             :selected proof-active-terminator-minor-mode]
            "----")
          (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
		    "--:doubleLine" "----"))
          coq-shared-menu
          )
  "*The menu for Coq.")

(defvar coq-shell-menu coq-shared-menu
  "The menu for the Coq shell")

(easy-menu-define coq-shell-menu
		  coq-shell-mode-map
		  "Menu used in the coq shell."
		  (cons "Coq" (cdr coq-shell-menu)))

(easy-menu-define coq-mode-menu  
		  coq-mode-map
		  "Menu used coq mode."
		  (cons "Coq" (cdr coq-menu)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's coq specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-shell-init-hook ()
  (insert (format "Set Undo %s." coq-default-undo-limit))
  (insert (format "Cd \"%s\"." default-directory))
  (remove-hook 'proof-shell-insert-hook 'coq-shell-init-hook))

(defun coq-set-undo-limit (undos)
  (proof-invisible-command (format "Set Undo %s." undos)))

(defun coq-count-undos (sext)
  (let ((ct 0) str i)
    (if (and sext (prev-span sext 'type)
	     (not (eq (span-property (prev-span sext 'type) 'type) 'comment))
	     (coq-goal-command-p (span-property (prev-span sext 'type) 'cmd)))
	(concat "Restart" proof-terminal-string)
      (while sext
	(setq str (span-property sext 'cmd))
	(cond ((eq (span-property sext 'type) 'vanilla)
	       (if (string-match coq-undoable-commands-regexp str)
		   (setq ct (+ 1 ct))))
	      ((eq (span-property sext 'type) 'pbp)
	       (cond ((string-match coq-undoable-commands-regexp str)
		      (setq i 0)
		      (while (< i (length str))
			(if (= (aref str i) proof-terminal-char)
			    (setq ct (+ 1 ct)))
			(setq i (+ 1 i))))
		     (t nil))))
	(setq sext (next-span sext 'type)))
      (concat "Undo " (int-to-string ct) proof-terminal-string))))

(defconst coq-keywords-decl-defn-regexp
  (ids-to-regexp (append coq-keywords-decl coq-keywords-defn))
  "Declaration and definition regexp.")

;; Decide whether this is a goal or not
(defun coq-goal-command-p (str)
  (and (string-match coq-goal-command-regexp str)
       (not (string-match "Definition.*:=" str))))

(defun coq-find-and-forget (sext)
  (let (str ans)
    (while (and sext (not ans))
      (setq str (span-property sext 'cmd))
      (cond

       ((eq (span-property sext 'type) 'comment))       

       ((eq (span-property sext 'type) 'goalsave)
	(setq ans (concat coq-forget-id-command
			  (span-property sext 'name) proof-terminal-string)))

       ;; I'm not sure match-string 2 is correct with proof-id
       ;; Furthermore, decl's can have proof-ids rather than proof-id
       ((string-match (concat "\\`\\(" coq-keywords-decl-defn-regexp
			      "\\)\\s-*\\(" proof-id "\\)\\s-*:") str)
	(setq ans (concat coq-forget-id-command
			  (match-string 2 str) proof-terminal-string)))

       ;; If it's not a goal but it contains "Definition" then it's a
       ;; declaration
       ((and (not (coq-goal-command-p str))
	     (string-match
	      (concat "Definition\\s-+\\(" proof-id "\\)\\s-*:") str))
	(setq ans (concat coq-forget-id-command
			  (match-string 2 str) proof-terminal-string))))

      (setq sext (next-span sext 'type)))

      (or ans "COMMENT")))

(defvar coq-current-goal 1
  "Last goal that emacs looked at.")

(defun coq-goal-hyp ()
  (cond 
   ((looking-at "============================\n")
    (goto-char (match-end 0))
    (cons 'goal (int-to-string coq-current-goal)))
   ((looking-at "subgoal \\([0-9]+\\) is:\n")
    (goto-char (match-end 0))
    (cons 'goal (match-string 1))
    (setq coq-current-goal (string-to-int (match-string 1))))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))

(defun coq-state-preserving-p (cmd)
  (not (string-match coq-undoable-commands-regexp cmd)))

(defun coq-global-p (cmd)
  (or (string-match coq-keywords-decl-defn-regexp cmd)
      (and (string-match
	    (concat "Definition\\s-+\\(" coq-id "\\)\\s-*:") cmd)
	   (string-match ":=" cmd))))

(defun coq-retract-target (target delete-region)
  (let ((end (proof-locked-end))
	(start (span-start target))
	(ext (proof-last-goal-or-goalsave))
	actions)
    
    (if (and ext (not (eq (span-property ext 'type) 'goalsave)))
	(if (< (span-end ext) (span-end target))
	    (progn
	      (setq ext target)
	      (while (and ext (eq (span-property ext 'type) 'comment))
		(setq ext (next-span ext 'type)))
	      (setq actions (proof-setup-retract-action
			     start end 
			     (if (null ext) "COMMENT" (coq-count-undos ext))
			     delete-region)
		    end start))
	  
	  (setq actions (proof-setup-retract-action (span-start ext) end
						    proof-kill-goal-command
						    delete-region)
		end (span-start ext))))
    
    (if (> end start) 
	(setq actions
	      (nconc actions (proof-setup-retract-action 
			      start end
			      (coq-find-and-forget target)
			      delete-region))))
      
    (proof-start-queue (min start end) (proof-locked-end) actions)))

(defun coq-shell-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x )) c ext)
      (while (< ip l)	
	(if (< (setq c (aref string ip)) 128) (progn (aset out op c)
						     (incf op)))
	(incf ip))
      (display-buffer (set-buffer proof-pbp-buffer))
      (erase-buffer)
      (insert (substring out 0 op))

      (setq ip 0
	    op 1)
      (while (< ip l)
	(setq c (aref string ip))
	(cond
	 ((= c proof-shell-goal-char)
	  (setq topl (cons op topl))
	  (setq ap 0))
	 ((= c proof-shell-start-char)
	  (setq ap (- ap (- (aref string (incf ip)) 128)))
	  (incf ip)
	  (while (not (= (setq c (aref string ip)) proof-shell-end-char))
	    (aset ann ap (- c 128))
	    (incf ap)
	    (incf ip))
	  (setq stack (cons op (cons (substring ann 0 ap) stack))))
	 ((= c proof-shell-field-char)
	  (setq ext (make-span (car stack) op))
	  (set-span-property ext 'mouse-face 'highlight)
	  (set-span-property ext 'proof (car (cdr stack)))
					; Pop annotation off stack
	  (setq ap 0)
	  (while (< ap (length (cadr stack)))
	    (aset ann ap (aref (cadr stack) ap))
	    (incf ap))
					; Finish popping annotations
	  (setq stack (cdr (cdr stack))))
	 (t (incf op)))
	(incf ip))
      (setq topl (reverse (cons (point-max) topl)))
      (setq coq-current-goal 1)
      (while (setq ip (car topl) 
		   topl (cdr topl))
	(pbp-make-top-span ip (car topl))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to coq                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-info-mode ()
  "Info mode on Coq."
  (interactive)
  (info "script-management"))

(defun coq-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-invisible-command "Help."))

(defun coq-prf ()
  "List proof state."
  (interactive)
  (proof-invisible-command "Show."))

(defun coq-exit ()
  "Exit Coq."
  (interactive)
  (proof-restart-script))

(defun coq-ctxt ()
  "List context."
  (interactive) 
  (proof-invisible-command "Show."))

(defun coq-Intros () 
  "List proof state." 
  (interactive) 
  (insert "Intros "))

(defun coq-Apply () 
  "List proof state."  
  (interactive) 
  (insert "Apply "))

(defun coq-Search ()
  "Search for type in goals."
  (interactive)
  (let (cmd)
    (proof-check-process-available)
    (setq cmd (read-string "Search Type: " nil 'proof-minibuffer-history))
    (proof-invisible-command (concat "Search " cmd proof-terminal-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Indentation                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-stack-to-indent (stack)
  (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (let ((col (save-excursion
		   (goto-char (nth 1 (car stack)))
		   (current-column))))
	(cond
	 ((eq (car (car stack)) ?c)
	  (save-excursion (move-to-column (current-indentation))
			  (cond 
			   ((eq (char-after (point)) ?|) (+ col 3))
			   ((looking-at "end") col)
			   (t (+ col 5)))))	  
	 ((eq (car (car stack)) ?I)
	  (+ col (if (eq ?| (save-excursion 
			      (move-to-column (current-indentation))
			      (char-after (point)))) 8 10)))
	 (t (1+ col)))))))

(defun coq-parse-indent (c stack)
  (cond
   ((and (eq c ?c) (looking-at "case"))
    (cons (list c (point)) stack))
   ((and (eq c ?e) (looking-at "end") (eq (car (car stack)) ?c))
    (cdr stack))
   
   ((and (eq c ?I) (looking-at "Inductive"))
    (forward-char (length "Inductive"))
    (cons (list c (- (point) (length "Inductive"))) stack))
   ((and (eq c ?C) (looking-at "CoInductive"))
    (forward-char (length "CoInductive"))
    (cons (list c (- (point) (length "CoInductive"))) stack))

   ((and (eq c ?.) (or (eq (car (car stack)) ?I) (eq (car (car stack)) ?C)))
    (cdr stack))

   (t stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Coq shell startup and exit hooks                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-pre-shell-start ()
  (setq proof-prog-name coq-prog-name)
  (setq proof-mode-for-shell 'coq-shell-mode)
  (setq proof-mode-for-pbp 'coq-pbp-mode)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-mode-config ()

  (setq proof-terminal-char ?\.)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")

  (setq proof-goal-command-p 'coq-goal-command-p
	proof-retract-target-fn 'coq-retract-target
        proof-goal-hyp-fn 'coq-goal-hyp
	proof-state-preserving-p 'coq-state-preserving-p
	proof-global-p 'coq-global-p
	proof-parse-indent 'coq-parse-indent
	proof-stack-to-indent 'coq-stack-to-indent)

  (setq proof-save-command-regexp coq-save-command-regexp
	proof-save-with-hole-regexp coq-save-with-hole-regexp
	proof-goal-with-hole-regexp coq-goal-with-hole-regexp
	proof-kill-goal-command coq-kill-goal-command)

  (modify-syntax-entry ?\$ ".")
  (modify-syntax-entry ?\/ ".")
  (modify-syntax-entry ?\\ ".")
  (modify-syntax-entry ?+  ".")
  (modify-syntax-entry ?-  ".")
  (modify-syntax-entry ?=  ".")
  (modify-syntax-entry ?%  ".")
  (modify-syntax-entry ?<  ".")
  (modify-syntax-entry ?>  ".")
  (modify-syntax-entry ?\& ".")
  (modify-syntax-entry ?_  "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")

;; font-lock

  (setq font-lock-keywords coq-font-lock-keywords-1)

  (proof-config-done)

  (define-key (current-local-map) [(control c) (control p)] 'coq-prf)
  (define-key (current-local-map) [(control c) c] 'coq-ctxt)
  (define-key (current-local-map) [(control c) h] 'coq-help)
  (define-key (current-local-map) [(control c) I] 'coq-Intros)
  (define-key (current-local-map) [(control c) a] 'coq-Apply)
  (define-key (current-local-map) [(control c) (control s)] 'coq-Search)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp coq-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp coq-outline-heading-end-regexp)

;; tags
  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.v$" . coq-tags)
		       ("coq"  . coq-tags))
		     tag-table-alist)))

;; Info
  (if (not (memq coq-info-dir Info-directory-list))
      (setq Info-directory-list	(cons coq-info-dir Info-directory-list)))

;; keymaps and menus
  (easy-menu-add coq-mode-menu coq-mode-map)

  (setq blink-matching-paren-dont-ignore-comments t)

;; hooks and callbacks

  (add-hook 'proof-shell-exit-hook 'coq-zap-line-width nil t)
  (add-hook 'proof-pre-shell-start-hook 'coq-pre-shell-start nil t))

;; insert standard header and footer in fresh buffers	       

(defun coq-shell-mode-config ()
  (setq proof-shell-prompt-pattern coq-shell-prompt-pattern
        proof-shell-cd coq-shell-cd
        proof-shell-abort-goal-regexp coq-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp coq-shell-proof-completed-regexp
        proof-shell-error-regexp coq-error-regexp
	proof-shell-interrupt-regexp coq-interrupt-regexp
        proof-shell-noise-regexp ""
        proof-shell-assumption-regexp coq-id
        proof-shell-goal-regexp coq-goal-regexp
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?\371 ; done: prompt
        ; The next three represent path annotation information
	proof-shell-start-char ?\372 ; not done
        proof-shell-end-char ?\373 ; not done
        proof-shell-field-char ?\374 ; not done
        proof-shell-goal-char ?\375 ; done
	proof-shell-eager-annotation-start "\376" ; done
	proof-shell-eager-annotation-end "\377" ; done
        proof-shell-annotated-prompt-regexp
	(concat proof-shell-prompt-pattern
		(char-to-string proof-shell-wakeup-char)) ; done
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "[0-9]+ subgoals?"
        proof-shell-end-goals-regexp proof-shell-annotated-prompt-regexp
        proof-shell-init-cmd nil
	proof-shell-analyse-structure 'coq-shell-analyse-structure)

  ;; The following hook is removed once it's called.
  (add-hook 'proof-shell-insert-hook 'coq-shell-init-hook nil t)

  (proof-shell-config-done)
)

(defun coq-pbp-mode-config ()
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp coq-error-regexp))

(provide 'coq)
