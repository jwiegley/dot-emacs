;; lego.el Major mode for LEGO proof assistants
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Author: Thomas Kleymann and Dilip Sequeira
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>


;; $Log$
;; Revision 1.52  1998/07/27 15:39:56  tms
;; Supports official LEGO release 1.3
;;
;; Revision 1.51  1998/06/10 11:43:38  hhg
;; Added lego-init-syntax-table as function to initialize syntax entries
;; particular to LEGO, and call it from lego-shell-mode-config.
;;
;; Revision 1.50  1998/06/03 18:03:02  hhg
;; Added '?'s before single characters in define-keys for emacs19, at
;; Pascal Brisset's suggestion.
;;
;; Revision 1.49  1998/06/02 15:34:58  hhg
;; Generalized proof-retract-target, now parameterized by
;; proof-count-undos and proof-find-and-forget.
;; Generalized proof-shell-analyse-structure, introduced variable
;; proof-analyse-using-stack.
;; Generalized proof menu plus ancillary functions.
;; Generalized proof-mode-version-string.
;; Moved various comments into documentation string.
;;
;; Revision 1.48  1998/05/29 09:49:47  tms
;; o outsourced indentation to proof-indent
;; o support indentation of commands
;; o replaced test of Emacs version with availability test of specific
;;   features
;; o C-c C-c, C-c C-v and M-tab is now available in all buffers
;;
;; Revision 1.47  1998/05/23 12:50:42  tms
;; improved support for Info
;;   o employed `Info-default-directory-list' rather than
;;     `Info-directory-list' so that code also works for Emacs 19.34
;;   o setting of `Info-default-directory-list' now at proof level
;;
;; Revision 1.46  1998/05/16 14:52:07  tms
;; implementation of `lego-shell-adjust-line-width' can now be called as
;; part of a hook. This change has been caused by replacing
;; `proof-shell-config' with `proof-shell-insert-hook'
;;
;; Revision 1.45  1998/05/15 16:17:41  hhg
;; Changed variable names [s]ext to span.
;;
;; Revision 1.44  1998/05/12 14:52:50  hhg
;; Added hook `proof-shell-insert-hook', which is initalized to
;; lego-shell-adjust-line-width.
;; This replaces `lego-shell-config'.
;;
;; Revision 1.43  1998/05/08 17:09:13  hhg
;; Made separated indentation more elegant.
;; 	Separated consideration of {}'s so it only happens for LEGO.
;;
;; Revision 1.42  1998/05/08 15:36:41  hhg
;; Merged indentation code for LEGO and Coq into proof.el.
;;
;; Revision 1.41  1998/05/06 15:54:50  hhg
;; Changed lego-undoable-commands-regexp to have "andI" and "andE"
;; instead of "AndI" and "AndE".
;;
;; Revision 1.40  1998/05/06 15:29:30  hhg
;; Added lego-info-dir so that location of script-management.info can be
;; hard-coded.
;;
;; Revision 1.39  1998/05/05 14:22:48  hhg
;; Added lego-goal-command-p to fix Coq's problem with "Definition".
;; Removed lego-killref from menu.
;;
;; Revision 1.38  1998/04/27 16:25:33  tms
;; removed explicit reference to a binary in ctm's home directory
;;
;; Revision 1.37  1998/03/25 17:30:41  tms
;; added support for etags at generic proof level
;;
;; Revision 1.36  1998/02/10 14:12:56  tms
;; added Dnf to lego-undoable-commands-regexp
;;
;; Revision 1.35  1998/01/16 15:40:23  djs
;; Commented the code of proof.el and lego.el a bit. Made a minor change
;; to the way errors are handled, so that any delayed output is inserted
;; in the buffer before the error message is printed.
;;
;; Revision 1.34  1998/01/15 12:23:59  hhg
;; Updated method of defining proof-shell-cd to be consistent with other
;; proof-assistant-dependent variables.
;; Added ctrl-button1 to copy selected region to end of locked region
;;
;; Revision 1.33  1998/01/05 14:59:03  tms
;; fixed a bug in the indenting functions
;;
;; Revision 1.32  1997/11/26 14:15:21  tms
;; o simplified code:
;;     lego-goal-with-hole-regexp and lego-save-with-hole-regexp is now
;;     used for lego-font-lock-keywords-1 as well
;; o improved lego-find-and-forget
;;
;; Revision 1.31  1997/11/24 19:15:11  djs
;; Added proof-execute-minibuffer-cmd and scripting minor mode.
;;
;; Revision 1.30  1997/11/20 13:04:59  hhg
;; Added lego-global-p as always false, but for consistency with Coq mode.
;; Changed [meta (control i)] to [meta tab] in key definition.
;;
;; Revision 1.29  1997/11/18 19:24:55  djs
;; Added indentation for lego-mode.
;;
;; Revision 1.28  1997/11/17 17:11:17  djs
;; Added some magic commands: proof-frob-locked-end, proof-try-command,
;; proof-interrupt-process. Added moving nested lemmas above goal for coq.
;; Changed the key mapping for assert-until-point to C-c RET.
;;
;; Revision 1.27  1997/11/06 16:56:26  hhg
;; Assign new variable proof-goal-hyp-fn to lego-goal-hyp, which is
;; simply old code for picking up goal or hypothesis for pbp
;;
;; Revision 1.26  1997/10/24 14:51:11  hhg
;; New indentation for lego-count-undos (smile)
;;
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

(require 'lego-fontlock)
(require 'outline)
(require 'proof)

; Configuration

(defvar lego-assistant "LEGO"
  "Name of proof assistant")

(defvar lego-tags "/home/tms/lib/lib_Type/TAGS"
  "the default TAGS table for the LEGO library")

(defconst lego-process-config "Configure PrettyOn; Configure AnnotateOn;"
  "Command to enable pretty printing of the LEGO process.")

(defconst lego-pretty-set-width "Configure PrettyWidth %s; "
  "Command to adjust the linewidth for pretty printing of the LEGO
  process.") 

(defconst lego-interrupt-regexp "Interrupt.."
  "Regexp corresponding to an interrupt")

(defvar lego-indent 2 "Indentation")

(defvar lego-test-all-name "test_all"
  "The name of the LEGO module which inherits all other modules of the
  library.")

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
;;    b) ftp.dcs.ed.ac.uk is set up in a too non-standard way 


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

(defvar lego-prog-name "lego"
  "*Name of program to run as lego.")

(defvar lego-shell-working-dir ""
  "The working directory of the lego shell")

(defvar lego-shell-prompt-pattern "^\\(Lego>[ \201]*\\)+"
  "*The prompt pattern for the inferior shell running lego.")

(defvar lego-shell-cd "Cd \"%s\";"
  "*Command of the inferior process to change the directory.") 

(defvar lego-shell-abort-goal-regexp "KillRef: ok, not in proof state"
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar lego-shell-proof-completed-regexp "\\*\\*\\* QED \\*\\*\\*"
  "*Regular expression indicating that the proof has been completed.")

(defvar lego-save-command-regexp
  (concat "^" (ids-to-regexp lego-keywords-save)))
(defvar lego-goal-command-regexp
  (concat "^" (ids-to-regexp lego-keywords-goal)))

(defvar lego-kill-goal-command "KillRef;")
(defvar lego-forget-id-command "Forget ")

(defvar lego-undoable-commands-regexp
  (ids-to-regexp '("Dnf" "Refine" "Intros" "intros" "Next" "Normal"
  "Qrepl" "Claim" "For" "Repeat" "Succeed" "Fail" "Try" "Assumption"
  "UTac" "Qnify" "qnify" "andE" "andI" "exE" "exI" "orIL" "orIR" "orE" "ImpI"
  "impE" "notI" "notE" "allI" "allE" "Expand" "Induction" "Immed"
  "Invert")) "Undoable list")

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
    (proof-string-to-list path-name lego-path-separator)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   This is how to work out what the undo commands are, given the  ;;
;;   first span which needs to be undone                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; needs to handle Normal as well
;; it should ignore Normal TReg Normal VReg and (Normal ...)
(defun lego-count-undos (span)
  (let ((ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (if (or (string-match lego-undoable-commands-regexp str)
		     (and (string-match "Equiv" str)
			  (not (string-match "Equiv\\s +[TV]Reg" str))))
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str)) 
	       (if (= (aref str i) proof-terminal-char) (setq ct (+ 1 ct)))
	       (setq i (+ 1 i)))))
      (setq span (next-span span 'type)))
    (concat "Undo " (int-to-string ct) proof-terminal-string)))

(defun lego-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (string-match lego-goal-command-regexp str))

(defun lego-find-and-forget (span) 
  (let (str ans)
    (while (and span (not ans))
      (setq str (span-property span 'cmd))
      
      (cond
       
       ((eq (span-property span 'type) 'comment))

       ((eq (span-property span 'type) 'goalsave)
	(setq ans (concat "Forget " 
			  (span-property span 'name) proof-terminal-string)))

       ((string-match (concat "\\`\\$?" (lego-decl-defn-regexp "[:|=]")) str)
	(let ((ids (match-string 1 str))) ; returns "a,b"
	  (string-match proof-id ids)	; matches "a"
	  (setq ans (concat "Forget " (match-string 1 ids)
			    proof-terminal-string))))
	   
       ((string-match "\\`\\(Inductive\\|\\Record\\)\\s-*\\[\\s-*\\w+\\s-*:[^;]+\\`Parameters\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans (concat "Forget " 
			  (match-string 2 str) proof-terminal-string)))

       ((string-match 
	 "\\`\\(Inductive\\|Record\\)\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans 
	      (concat "Forget " (match-string 2 str) proof-terminal-string)))
       
       ((string-match "\\`\\s-*Module\\s-+\\(\\S-+\\)\\W" str)
	(setq ans (concat "ForgetMark " (match-string 1 str) 
			  proof-terminal-string))))
      
      (setq span (next-span span 'type)))
  (or ans
      "COMMENT")))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Other stuff which is required to customise script management   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-goal-hyp ()
  (cond 
   ((looking-at proof-shell-goal-regexp)
    (cons 'goal (match-string 1)))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))


(defun lego-state-preserving-p (cmd)
  (not (string-match lego-undoable-commands-regexp cmd)))

(defun lego-global-p (cmd)
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to lego                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
;;   Lego Indentation                                               ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-stack-to-indent (stack)
  (cond
   ((null stack) 0)
   ((null (car (car stack)))
    (nth 1 (car stack)))
   (t (save-excursion
	(goto-char (nth 1 (car stack)))
	(+ lego-indent (current-column))))))

(defun lego-parse-indent (c stack)
  (cond
   ((eq c ?\{) (cons (list c (point)) stack))
   ((eq c ?\}) (cdr stack))
   (t stack)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Lego shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shell-current-line-width nil
  "Current line width of the LEGO process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; The line width needs to be adjusted if the LEGO process is
;; running and is out of sync with the screen width

(defun lego-shell-adjust-line-width ()
  "Uses LEGO's pretty printing facilities to adjust the line width of
  the output."
  (save-excursion 
    (set-buffer proof-shell-buffer)
    (and (proof-shell-live-buffer)
	 (let ((current-width
		(window-width (get-buffer-window proof-shell-buffer))))
	   (if (equal current-width lego-shell-current-line-width) ()
	     ; else
	     (setq lego-shell-current-line-width current-width)
	     (insert (format lego-pretty-set-width (- current-width 1)))
	     )))))

(defun lego-pre-shell-start ()
  (setq proof-prog-name lego-prog-name)
  (setq proof-mode-for-shell 'lego-shell-mode)
  (setq proof-mode-for-pbp 'lego-pbp-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."

  (modify-syntax-entry ?_ "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))

(defun lego-mode-config ()

  (setq proof-terminal-char ?\;)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")

  (setq proof-assistant lego-assistant
	proof-www-home-page lego-www-home-page)

  (setq proof-prf-string "Prf"
	proof-ctxt-string "Ctxt"
	proof-help-string "Help")

  (setq proof-goal-command-p 'lego-goal-command-p
	proof-count-undos-fn 'lego-count-undos
	proof-find-and-forget-fn 'lego-find-and-forget
        proof-goal-hyp-fn 'lego-goal-hyp
	proof-state-preserving-p 'lego-state-preserving-p
	proof-global-p 'lego-global-p
	proof-parse-indent 'lego-parse-indent
	proof-stack-to-indent 'lego-stack-to-indent)

  (setq	proof-save-command-regexp lego-save-command-regexp
	proof-save-with-hole-regexp lego-save-with-hole-regexp
	proof-goal-with-hole-regexp lego-goal-with-hole-regexp
	proof-kill-goal-command lego-kill-goal-command
	proof-commands-regexp (ids-to-regexp lego-commands))

  (lego-init-syntax-table)

  (proof-config-done)

  (define-key (current-local-map) [(control c) ?i] 'lego-intros)
  (define-key (current-local-map) [(control c) ?I] 'lego-Intros)
  (define-key (current-local-map) [(control c) ?r] 'lego-Refine)

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

  (setq blink-matching-paren-dont-ignore-comments t)

;; font-lock

;; if we don't have the following in xemacs, zap-commas fails to work.

  (and (boundp 'font-lock-always-fontify-immediately)
       (setq font-lock-always-fontify-immediately t))

;; hooks and callbacks

  (add-hook 'proof-shell-exit-hook 'lego-zap-line-width nil t)
  (add-hook 'proof-pre-shell-start-hook 'lego-pre-shell-start nil t)
  (add-hook 'proof-shell-insert-hook 'lego-shell-adjust-line-width))

;; insert standard header and footer in fresh buffers	       

(defun lego-shell-mode-config ()
  (setq proof-shell-prompt-pattern lego-shell-prompt-pattern
        proof-shell-cd lego-shell-cd
        proof-shell-abort-goal-regexp lego-shell-abort-goal-regexp
        proof-shell-proof-completed-regexp lego-shell-proof-completed-regexp
        proof-shell-error-regexp lego-error-regexp
	proof-shell-interrupt-regexp lego-interrupt-regexp
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
	proof-analyse-using-stack nil
        lego-shell-current-line-width nil)

  (lego-init-syntax-table)

  (proof-shell-config-done))

(defun lego-pbp-mode-config ()
  (setq pbp-change-goal "Next %s;")
  (setq pbp-error-regexp lego-error-regexp))

(provide 'lego)
