;; coq.el Major mode for Coq proof assistant
;; Copyright (C) 1994, 1995, 1996, 1997 LFCS Edinburgh. 
;; Author: Healfdene Goguen and Thomas Kleymann

;; $Log$
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

; Configuration                                  

(defconst coq-mode-version-string
  "Coq-MODE. ALPHA Version 1.11 (June 1996) LEGO Team <lego@dcs.ed.ac.uk>")

(defvar coq-tags "/usr/local/share/coq/lib-alpha/lib_all/TAGS"
  "the default TAGS table for the Coq library")

(defconst coq-process-config nil
  "Command to configure pretty printing of the Coq process for emacs.")

;; This doesn't exist at the moment
(defconst coq-pretty-set-width ""
  "Command to adjust the linewidth for pretty printing of the Coq
  process.") 

;; This doesn't exist at the moment
(defvar coq-test-all-name "test_all"
  "The name of the Coq module which inherits all other modules of the
  library.")

;; Could be set to "Load". To cite Mark, "Although this may sound
;; strange at first side, the Make command is much, much slower for my
;; files then the load command. That is because .o files do not save
;; Equiv's. So a Make of a .o file needs to find the proper
;; conversions itself, and hence will be much slower in some
;; cases. Especially when doing larger examples."

(defvar coq-make-command "Make")

(defvar coq-path-name "COQPATH"
  "The name of the environmental variable to search for modules. This
  is used by \\{coqgrep} to find the files corresponding to a
  search.")

(defvar coq-path-separator ":"
  "A character indicating how the items in the \\{coq-path-name} are
  separated.") 

(defvar coq-save-query t
  "*If non-nil, ask user for permission to save the current buffer before
  processing a module.")


;; ----- web documentation

(defvar coq-www-home-page "http://www.dcs.ed.ac.uk/home/lego/")

(defvar coq-www-refcard (concat (w3-remove-file-name coq-www-home-page)
				 "refcard.dvi.gz"))

;; `coq-www-refcard' ought to be set to
;; "ftp://ftp.dcs.ed.ac.uk/pub/coq/refcard.dvi.gz", but  
;;    a) w3 fails to decode the image before invoking xdvi
;;    b) ange-ftp and efs cannot handle Solaris ftp servers


(defvar coq-library-www-page
  (concat (w3-remove-file-name coq-www-home-page)
          "html/library/newlib.html"))

(defvar coq-www-customisation-page
  (concat (w3-remove-file-name coq-www-home-page)
          "html/emacs-customisation.html"))

;; ----- coqstat and coqgrep, courtesy of Mark Ruys

(defvar coqgrep-command (concat "coqgrep -n \"\" " coq-test-all-name)
  "Last coqgrep command used in \\{coqgrep}; default for next coqgrep.")

(defvar coqstat-command "coqstat -t")

(defvar coqgrep-regexp-alist
  '(("^\\([^:( \t\n]+\\)[:( \t]+\\([0-9]+\\)[:) \t]" 1 2 nil ("%s.l")))
  "Regexp used to match coqgrep hits.  See `compilation-error-regexp-alist'.")

;; ----- coq-shell configuration options

(defvar coq-prog-name "/obj/local/coq/V6.1.beta/bin/sun4/coqtop -bindir /obj/local/coq/V6.1.beta/bin/sun4"
  "*Name of program to run as Coq.")

(defvar coq-shell-working-dir ""
  "The working directory of the coq shell")

(defvar coq-shell-prompt-pattern "^\\w+ < "
  "*The prompt pattern for the inferior shell running coq.")

(defvar coq-shell-abort-goal-regexp "Current goal aborted"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar coq-shell-proof-completed-regexp "Subtree proved!"
  "*Regular expression indicating that the proof has been completed.")

;; ----- outline

(defvar coq-goal-regexp "============================\n")

(defvar coq-outline-regexp
  (concat "[[*]\\|"
	  (ids-to-regexp 
	   '("Discharge" "DischargeKeep" "Freeze" "$?Goal" "Module" "Record" "Inductive"
     "Unfreeze"))))

(defvar coq-outline-heading-end-regexp ";\\|\\*)")

(defvar coq-shell-outline-regexp coq-goal-regexp)
(defvar coq-shell-outline-heading-end-regexp coq-goal-regexp)

(defvar coq-save-command-regexp
  (concat "^" (ids-to-regexp coq-keywords-save)))
; The semicolon is incorrect here!
(defvar coq-save-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-save) "\\)\\s-+\\([^;]+\\)"))
(defvar coq-goal-command-regexp
  (concat "^" (ids-to-regexp coq-keywords-goal)))
(defvar coq-goal-with-hole-regexp
  (concat "\\(" (ids-to-regexp coq-keywords-goal) "\\)\\s-+\\([^:]+\\)"))

(defvar coq-kill-goal-command "Abort.")
(defvar coq-forget-id-command "Reset ")

(defvar coq-undoable-commands-regexp (ids-to-regexp coq-tactics))

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
           ["Kill the current refinement proof"
            coq-killref  :active (proof-shell-live-buffer)]
           ["Exit Coq" proof-shell-exit
	     :active (proof-shell-live-buffer)]
           "----"
           ["Find definition/declaration" find-tag-other-window t]
           ("Help"
            ["The Coq Reference Card" (w3-fetch coq-www-refcard) t]
            ["The Coq library (WWW)"
             (w3-fetch coq-library-www-page)  t]
            ["The Coq Proof-assistant (WWW)"
             (w3-fetch coq-www-home-page)  t]
            ["Help on Emacs Coq-mode" describe-mode  t]
            ["Customisation" (w3-fetch coq-www-customisation-page)
	      t]
            ))))

(defvar coq-menu  
  (append '("Coq Commands"
            ["Toggle active ;" proof-active-terminator-minor-mode
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

;(easy-menu-define coq-shell-menu
;		  coq-shell-mode-map
;		  "Menu used in the coq shell."
;		  (cons "Coq" (cdr coq-shell-menu)))

;(easy-menu-define coq-mode-menu  
;		  coq-mode-map
;		  "Menu used coq mode."
;		  (cons "Coq" (cdr coq-menu)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's coq specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Martin Steffen <mnsteffe@informatik.uni-erlangen.de> has pointed
;; out that calling coq-get-path has to deal with a user who hasn't
;; set the environmental variable COQPATH. It is probably best if
;; coq is installed as a shell script which sets a sensible default
;; for COQPATH if the user hasn't done so before. See the
;; documentation of the library for further details.

(defun coq-get-path ()
  (let ((path-name (getenv coq-path-name)))
    (cond ((not path-name)
           (message "Warning: COQPATH has not been set!")
           (setq path-name ".")))       
    (string-to-list path-name coq-path-separator)))

(defun coq-count-undos (sext)
  (let ((ct 0) str)
    (while sext
      (setq str (extent-property sext 'cmd))
      (if (string-match coq-undoable-commands-regexp str)
	  (setq ct (+ 1 ct)))
      (setq sext (extent-at (extent-end-position sext) nil 'type nil 'after)))
  (concat "Undo " (int-to-string ct) proof-terminal-string)))

(defconst coq-keywords-decl-defn-regexp
  (ids-to-regexp (append coq-keywords-decl coq-keywords-defn))
  "Declaration and definition regexp.")


(defun coq-find-and-forget (sext)
  (let (str ans)
    (while sext
      (if (eq (extent-property sext 'type) 'goalsave)
	  (setq ans (concat coq-forget-id-command
			    (extent-property sext 'name) proof-terminal-string)
		sext nil)
	(setq str (extent-property sext 'cmd))
	(cond

	 ((string-match (concat "\\`\\(" coq-keywords-decl-defn-regexp
				"\\)\\s-*\\(\\w+\\)\\s-*:") str)
	  (setq ans (concat coq-forget-id-command
			    (match-string 2 str) proof-terminal-string)
		sext nil))

	 (t 
	  (setq sext 
		(extent-at (extent-end-position sext) nil 'type nil 
			   'after))))))
; I don't know what the equivalent of "echo" is in Coq -- hhg
    (or ans
	(concat "echo \"Nothing more to Forget.\"" proof-terminal-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to coq                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun coq-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-invisible-command "Help."))

(defun coq-prf ()
  "List proof state."
  (interactive)
  (proof-invisible-command "Show."))

(defun coq-ctxt ()
  "List context."
  (interactive) 
  (proof-invisible-command "Show Context."))

(defun coq-Intros () 
  "List proof state." 
  (interactive) 
  (insert "Intros "))

(defun coq-Apply () 
  "List proof state."  
  (interactive) 
  (insert "Apply "))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Lego shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar coq-shell-current-line-width nil
  "Current line width of the Coq process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; NEED TO MAKE THE CODE BELOW CONSISTENT WITH THE VARIABLE ABOVE
;; BEING BUFFER LOCAL TO THE SHELL BUFFER - djs 5/2/97

;; The line width needs to be adjusted if the Coq process is
;; running and is out of sync with the screen width

(defun coq-shell-adjust-line-width ()
  "Uses Coq's pretty printing facilities to adjust the line width of
  the output."
  (if (proof-shell-live-buffer)
      (let ((current-width
	     (window-width (get-buffer-window proof-shell-buffer))))
	 (if (equal current-width coq-shell-current-line-width)
	     ""
	   (setq coq-shell-current-line-width current-width)
	   (format coq-pretty-set-width (- current-width 1))))
    ""))

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

  (setq proof-undo-target-fn 'coq-count-undos)
  (setq proof-forget-target-fn 'coq-find-and-forget)

  (setq proof-save-command-regexp coq-save-command-regexp
	proof-save-with-hole-regexp coq-save-with-hole-regexp
	proof-goal-command-regexp coq-goal-command-regexp
	proof-goal-with-hole-regexp coq-goal-with-hole-regexp
	proof-kill-goal-command coq-kill-goal-command)

  (modify-syntax-entry ?_ "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")

;; font-lock

  (setq font-lock-keywords coq-font-lock-keywords-1)

  (proof-config-done)

  (define-key (current-local-map) "\M-\C-i"
    (if (fboundp 'complete-tag)
	'complete-tag		; Emacs 19.31 (superior etags)
      'tag-complete-symbol))	;XEmacs 19.13 (inferior etags)
  (define-key (current-local-map) "\C-c\C-p" 'coq-prf)
  (define-key (current-local-map) "\C-cc"    'coq-ctxt)
  (define-key (current-local-map) "\C-ch"    'coq-help)
  (define-key (current-local-map) "\C-cI"    'coq-Intros)
  (define-key (current-local-map) "\C-ca"    'coq-Apply)

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp coq-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp coq-outline-heading-end-regexp)

;; tags
  (cond ((boundp 'tags-table-list)
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons coq-tags tags-table-list))))

  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.l$" . coq-tags)
		       ("coq"  . coq-tags))
		     tag-table-alist)))

;; where to find files

  (setq compilation-search-path (cons nil (coq-get-path)))

;; keymaps and menus

;; The following doesn't work:
;;  (easy-menu-add coq-mode-menu coq-mode-map)

  (setq blink-matching-paren-dont-ignore-comments t)

;; hooks and callbacks

  (add-hook 'proof-shell-exit-hook 'coq-zap-line-width nil t)
  (add-hook 'proof-pre-shell-start-hook 'coq-pre-shell-start nil t))

;; insert standard header and footer in fresh buffers	       

(defun coq-shell-mode-config ()
  (setq proof-shell-prompt-pattern coq-shell-prompt-pattern
        proof-shell-abort-goal-regexp coq-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp coq-shell-proof-completed-regexp
        proof-shell-error-regexp coq-error-regexp
        proof-shell-noise-regexp ""
        proof-shell-assumption-regexp coq-id
        proof-shell-goal-regexp coq-goal-regexp
        proof-shell-first-special-char ?\360
        proof-shell-wakeup-char ?\371 ; done: prompt
        proof-shell-start-char ?\372 ; not done
        proof-shell-end-char ?\373 ; not done
        proof-shell-field-char ?\374
        proof-shell-goal-char ?\375
	proof-shell-eager-annotation-start "\376" ; done
	proof-shell-eager-annotation-end "\377" ; done
        proof-shell-annotated-prompt-regexp
	(concat proof-shell-prompt-pattern
		(char-to-string proof-shell-wakeup-char)) ; done
        proof-shell-result-start "\372 Pbp result \373"
        proof-shell-result-end "\372 End Pbp result \373"
        proof-shell-start-goals-regexp "[0-9]+ subgoal[s]"
        proof-shell-end-goals-regexp proof-shell-annotated-prompt-regexp
        proof-shell-init-cmd coq-process-config
        proof-shell-config 'coq-shell-adjust-line-width
        coq-shell-current-line-width nil)
  (proof-shell-config-done)
)

(defun coq-pbp-mode-config ()
  (setq pbp-change-goal "Focus %s.")
  (setq pbp-error-regexp coq-error-regexp))

(provide 'coq)
