;; lego.el Major mode for LEGO proof assistants
;; Copyright (C) 1994, 1995, 1996, 1997 LFCS Edinburgh. 
;; Author: Thomas Schreiber and Dilip Sequeira
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>


;; $Log$
;; Revision 1.25  1997/10/16 08:46:16  tms
;; o merged script management (1.20.2.11) on the main branch
;; o fixed a bug in lego-find-and-forget due to new treatment of comments
;;
;; Revision 1.20.2.11  1997/10/14 17:30:12  djs
;; Fixed a bunch of bugs to do with comments, moved annotations out-of-band
;; to exploit a feature which will exist in XEmacs 20.
;;
;; Revision 1.20.2.10  1997/10/10 19:24:29  djs
;; Attempt to create a fresh branch because of Attic-Attack.
;;
;; Revision 1.20.2.9  1997/10/10 19:20:00  djs
;; Added multiple file support, changed the way comments work, fixed a
;; few minor bugs, and merged in coq support by hhg.
;;
;; Revision 1.20.2.7  1997/10/08 08:22:33  hhg
;; Updated undo, fixed bugs, more modularization
;;
;; Revision 1.20.2.6  1997/10/07 13:26:05  hhg
;; New structure sharing as much as possible between LEGO and Coq.
;;
;; Revision 1.20.2.5  1997/07/08 11:52:17  tms
;; Made dependency on proof explicit
;;

(require 'easymenu)
(require 'lego-fontlock)
(require 'outline)
(require 'proof)

; Configuration                                  

(defconst lego-mode-version-string
  "LEGO-MODE. ALPHA Version 1.11 (June 1996) LEGO Team <lego@dcs.ed.ac.uk>")

(defvar lego-tags "/usr/local/share/lego/lib-alpha/lib_all/TAGS"
  "the default TAGS table for the LEGO library")

(defconst lego-process-config "Configure PrettyOn; Configure AnnotateOn;"
  "Command to enable pretty printing of the LEGO process.")

(defconst lego-pretty-set-width "Configure PrettyWidth %s; "
  "Command to adjust the linewidth for pretty printing of the LEGO
  process.") 

(defvar lego-test-all-name "test_all"
  "The name of the LEGO module which inherits all other modules of the
  library.")

;; Could be set to "Load". To cite Mark, "Although this may sound
;; strange at first side, the Make command is much, much slower for my
;; files then the load command. That is because .o files do not save
;; Equiv's. So a Make of a .o file needs to find the proper
;; conversions itself, and hence will be much slower in some
;; cases. Especially when doing larger examples."

(defvar lego-make-command "Make")

(defvar lego-path-name "LEGOPATH"
  "The name of the environmental variable to search for modules. This
  is used by \\{legogrep} to find the files corresponding to a
  search.")

(defvar lego-path-separator ":"
  "A character indicating how the items in the \\{lego-path-name} are
  separated.") 

(defvar lego-save-query t
  "*If non-nil, ask user for permission to save the current buffer before
  processing a module.")


;; ----- web documentation

(defvar lego-www-home-page "http://www.dcs.ed.ac.uk/home/lego/")

(defvar lego-www-refcard (concat (w3-remove-file-name lego-www-home-page)
				 "refcard.dvi.gz"))

;; `lego-www-refcard' ought to be set to
;; "ftp://ftp.dcs.ed.ac.uk/pub/lego/refcard.dvi.gz", but  
;;    a) w3 fails to decode the image before invoking xdvi
;;    b) ange-ftp and efs cannot handle Solaris ftp servers


(defvar lego-library-www-page
  (concat (w3-remove-file-name lego-www-home-page)
          "html/library/newlib.html"))

(defvar lego-www-customisation-page
  (concat (w3-remove-file-name lego-www-home-page)
          "html/emacs-customisation.html"))

;; ----- legostat and legogrep, courtesy of Mark Ruys

(defvar legogrep-command (concat "legogrep -n \"\" " lego-test-all-name)
  "Last legogrep command used in \\{legogrep}; default for next legogrep.")

(defvar legostat-command "legostat -t")

(defvar legogrep-regexp-alist
  '(("^\\([^:( \t\n]+\\)[:( \t]+\\([0-9]+\\)[:) \t]" 1 2 nil ("%s.l")))
  "Regexp used to match legogrep hits.  See `compilation-error-regexp-alist'.")

;; ----- lego-shell configuration options

(defvar lego-prog-name "legoML"
  "*Name of program to run as lego.")

(defvar lego-shell-working-dir ""
  "The working directory of the lego shell")

(defvar lego-shell-prompt-pattern "^\\(Lego>[ \201]*\\)+"
  "*The prompt pattern for the inferior shell running lego.")

(defvar lego-shell-abort-goal-regexp "KillRef: ok, not in proof state"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar lego-shell-proof-completed-regexp "\\*\\*\\* QED \\*\\*\\*"
  "*Regular expression indicating that the proof has been completed.")

(defvar lego-save-command-regexp
  (concat "^" (ids-to-regexp lego-keywords-save)))
(defvar lego-save-with-hole-regexp
  (concat "\\(" (ids-to-regexp lego-keywords-save) "\\)\\s-+\\([^;]+\\)"))
(defvar lego-goal-command-regexp
  (concat "^" (ids-to-regexp lego-keywords-goal)))
(defvar lego-goal-with-hole-regexp
  (concat "\\(" (ids-to-regexp lego-keywords-goal) "\\)\\s-+\\([^:]+\\)"))

(defvar lego-kill-goal-command "KillRef;")
(defvar lego-forget-id-command "Forget ")

(defvar lego-undoable-commands-regexp
  (ids-to-regexp '("Refine" "Intros" "intros" "Next" "Qrepl" "Claim"
		   "For" "Repeat" "Succeed" "Fail" "Try" "Assumption" "UTac"
		   "Qnify" "AndE" "AndI" "exE" "exI" "orIL" "orIR" "orE"
		   "ImpI" "impE" "notI" "notE" "allI" "allE" "Expand"
		   "Induction" "Immed"))
  "Undoable list")

;; ----- outline

(defvar lego-goal-regexp "\\?\\([0-9]+\\)")

(defvar lego-outline-regexp
  (concat "[[*]\\|"
	  (ids-to-regexp 
	   '("Discharge" "DischargeKeep" "Freeze" "$?Goal" "Module" "Record" "Inductive"
     "Unfreeze"))))

(defvar lego-outline-heading-end-regexp ";\\|\\*)")

(defvar lego-shell-outline-regexp lego-goal-regexp)
(defvar lego-shell-outline-heading-end-regexp lego-goal-regexp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode lego-shell-mode proof-shell-mode
   "lego-shell" "Inferior shell mode for lego shell"
   (lego-shell-mode-config))

(define-derived-mode lego-mode proof-mode
   "lego" "Lego Mode"
   (lego-mode-config))

(define-derived-mode lego-pbp-mode pbp-mode
  "pbp" "Proof-by-pointing support for LEGO"
  (lego-pbp-mode-config))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Popup and Pulldown Menu ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shared-menu
  (append '(
            ["Display context" lego-ctxt
	      :active (proof-shell-live-buffer)]
            ["Display proof state" lego-prf
	      :active (proof-shell-live-buffer)]
           ["Kill the current refinement proof"
            lego-killref  :active (proof-shell-live-buffer)]
           ["Exit LEGO" proof-shell-exit
	     :active (proof-shell-live-buffer)]
           "----"
           ["Find definition/declaration" find-tag-other-window t]
           ("Help"
            ["The LEGO Reference Card" (w3-fetch lego-www-refcard) t]
            ["The LEGO library (WWW)"
             (w3-fetch lego-library-www-page)  t]
            ["The LEGO Proof-assistant (WWW)"
             (w3-fetch lego-www-home-page)  t]
            ["Help on Emacs LEGO-mode" describe-mode  t]
            ["Customisation" (w3-fetch lego-www-customisation-page)
	      t]
            ))))

(defvar lego-menu  
  (append '("LEGO Commands"
            ["Toggle active ;" proof-active-terminator-minor-mode
	     :active t
	     :style toggle
             :selected proof-active-terminator-minor-mode]
            "----")
          (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
		    "--:doubleLine" "----"))
          lego-shared-menu
          )
  "*The menu for LEGO.")

(defvar lego-shell-menu lego-shared-menu
  "The menu for the LEGO shell")

(easy-menu-define lego-shell-menu
		  lego-shell-mode-map
		  "Menu used in the lego shell."
		  (cons "LEGO" (cdr lego-shell-menu)))

(easy-menu-define lego-mode-menu  
		  lego-mode-map
		  "Menu used lego mode."
		  (cons "LEGO" (cdr lego-menu)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's lego specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Martin Steffen <mnsteffe@informatik.uni-erlangen.de> has pointed
;; out that calling lego-get-path has to deal with a user who hasn't
;; set the environmental variable LEGOPATH. It is probably best if
;; lego is installed as a shell script which sets a sensible default
;; for LEGOPATH if the user hasn't done so before. See the
;; documentation of the library for further details.

(defun lego-get-path ()
  (let ((path-name (getenv lego-path-name)))
    (cond ((not path-name)
           (message "Warning: LEGOPATH has not been set!")
           (setq path-name ".")))       
    (string-to-list path-name lego-path-separator)))

(defun lego-count-undos (sext)
  (let ((ct 0) str i)
    (while sext
      (setq str (span-property sext 'cmd))
      (cond ((eq (span-property sext 'type) 'vanilla)
	     (if (or (string-match lego-undoable-commands-regexp str)
		(and (string-match "Equiv" str)
		     (not (string-match "Equiv\\s +[TV]Reg" str))))
	    (setq ct (+ 1 ct))))
	    ((eq (span-property sext 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str)) 
	       (if (= (aref str i) proof-terminal-char) (setq ct (+ 1 ct)))
	       (setq i (+ 1 i)))))
      (setq sext (next-span sext 'type)))
  (concat "Undo " (int-to-string ct) proof-terminal-string)))

(defun lego-find-and-forget (sext) 
  (let (str ans)
    (while (and sext (not ans))
      (setq str (span-property sext 'cmd))
      
      (cond
       
       ((eq (span-property sext 'type) 'comment))

       ((eq (span-property sext 'type) 'goalsave)
	(setq ans (concat "Forget " 
			  (span-property sext 'name) proof-terminal-string)))

       ((string-match (concat "\\`" (lego-decl-defn-regexp "[:|=]")) str)
	(let ((ids (match-string 1 str))) ; returns "a,b"
	  (string-match proof-id ids)	; matches "a"
	  (setq ans (concat "Forget " (match-string 1 ids)
			    proof-terminal-string))))
	   
       ((string-match "\\`\\(Inductive\\|\\Record\\)\\s-*\\[\\s-*\\w+\\s-*:[^;]+\\`Parameters\\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans (concat "Forget " 
			  (match-string 2 str) proof-terminal-string)))

       ((string-match 
	 "\\`\\(Inductive\\|Record\\)\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans 
	      (concat "Forget " (match-string 2 str) proof-terminal-string)))
       
       ((string-match "\\`\\s-*Module\\s-+\\(\\S-+\\)\\W" str)
	(setq ans (concat "ForgetMark " (match-string 1 str) 
			  proof-terminal-string))))
      
      (setq sext (next-span sext 'type)))
  (or ans
      "COMMENT")))
  

(defun lego-retract-target (target delete-region)
  (let ((end (proof-end-of-locked))
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
			     (if (null ext) "COMMENT" (lego-count-undos ext))
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
			      (lego-find-and-forget target)
			      delete-region))))
      
    (proof-start-queue (min start end) (proof-end-of-locked) actions)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to lego                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-invisible-command "Help;"))

(defun lego-prf ()
  "List proof state."
  (interactive)
  (proof-invisible-command "Prf;"))

(defun lego-ctxt ()
  "List context."
  (interactive) 
  (proof-invisible-command "Ctxt;"))

(defun lego-intros ()
  "intros."
  (interactive)
  (insert "intros "))

(defun lego-Intros () 
  "List proof state." 
  (interactive) 
  (insert "Intros "))

(defun lego-Refine () 
  "List proof state."  
  (interactive) 
  (insert "Refine "))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Lego shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shell-current-line-width nil
  "Current line width of the LEGO process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; NEED TO MAKE THE CODE BELOW CONSISTENT WITH THE VARIABLE ABOVE
;; BEING BUFFER LOCAL TO THE SHELL BUFFER - djs 5/2/97

;; The line width needs to be adjusted if the LEGO process is
;; running and is out of sync with the screen width

(defun lego-shell-adjust-line-width ()
  "Uses LEGO's pretty printing facilities to adjust the line width of
  the output."
  (if (proof-shell-live-buffer)
      (let ((current-width
	     (window-width (get-buffer-window proof-shell-buffer))))
	 (if (equal current-width lego-shell-current-line-width)
	     ""
	   (setq lego-shell-current-line-width current-width)
	   (format lego-pretty-set-width (- current-width 1))))
    ""))

(defun lego-pre-shell-start ()
  (setq proof-prog-name lego-prog-name)
  (setq proof-mode-for-shell 'lego-shell-mode)
  (setq proof-mode-for-pbp 'lego-pbp-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-mode-config ()

  (setq proof-terminal-char ?\;)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")

  (setq proof-retract-target-fn 'lego-retract-target)

  (setq	proof-save-command-regexp lego-save-command-regexp
	proof-save-with-hole-regexp lego-save-with-hole-regexp
	proof-goal-command-regexp lego-goal-command-regexp
	proof-goal-with-hole-regexp lego-goal-with-hole-regexp
	proof-kill-goal-command lego-kill-goal-command)

  (modify-syntax-entry ?_ "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")

  (proof-config-done)

  (define-key (current-local-map) "\M-\C-i"
    (if (fboundp 'complete-tag)
	'complete-tag		; Emacs 19.31 (superior etags)
      'tag-complete-symbol))	;XEmacs 19.13 (inferior etags)
  (define-key (current-local-map) "\C-c\C-p" 'lego-prf)
  (define-key (current-local-map) "\C-cc"    'lego-ctxt)
  (define-key (current-local-map) "\C-ch"    'lego-help)
  (define-key (current-local-map) "\C-ci"    'lego-intros)
  (define-key (current-local-map) "\C-cI"    'lego-Intros)
  (define-key (current-local-map) "\C-cr"    'lego-Refine)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp lego-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp lego-outline-heading-end-regexp)

;; tags
  (cond ((boundp 'tags-table-list)
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons lego-tags tags-table-list))))

  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.l$" . lego-tags)
		       ("lego"  . lego-tags))
		     tag-table-alist)))

  (setq font-lock-keywords lego-font-lock-keywords-1)

;; where to find files

  (setq compilation-search-path (cons nil (lego-get-path)))

;; keymaps and menus

  (easy-menu-add lego-mode-menu lego-mode-map)

  (setq blink-matching-paren-dont-ignore-comments t)
;; font-lock

;; if we don't have the following, zap-commas fails to work.

  (setq font-lock-always-fontify-immediately t)

;; hooks and callbacks

  (add-hook 'proof-shell-exit-hook 'lego-zap-line-width nil t)
  (add-hook 'proof-pre-shell-start-hook 'lego-pre-shell-start nil t))

;; insert standard header and footer in fresh buffers	       

(defun lego-shell-mode-config ()
  (setq proof-shell-prompt-pattern lego-shell-prompt-pattern
        proof-shell-abort-goal-regexp lego-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp lego-shell-proof-completed-regexp
        proof-shell-error-regexp lego-error-regexp
        proof-shell-noise-regexp "Discharge\\.\\. "
        proof-shell-assumption-regexp lego-id
        proof-shell-goal-regexp lego-goal-regexp
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?\371
        proof-shell-start-char ?\372
        proof-shell-end-char ?\373
        proof-shell-field-char ?\374
        proof-shell-goal-char ?\375
	proof-shell-eager-annotation-start "\376"
	proof-shell-eager-annotation-end "\377"
        proof-shell-annotated-prompt-regexp "Lego> \371"
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "\372 Start of Goals \373"
        proof-shell-end-goals-regexp "\372 End of Goals \373"
        proof-shell-init-cmd lego-process-config
        proof-shell-config 'lego-shell-adjust-line-width
        lego-shell-current-line-width nil)
  (proof-shell-config-done)
)

(defun lego-pbp-mode-config ()
  (setq pbp-change-goal "Next %s;")
  (setq pbp-error-regexp lego-error-regexp))

(provide 'lego)
