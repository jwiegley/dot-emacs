;; lego.el Major mode for LEGO proof assistants
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Author:      Thomas Kleymann and Dilip Sequeira
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>

;;
;; $Id$
;;

(require 'lego-syntax)
(require 'outline)
(require 'proof)

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Configuration ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgroup lego-settings nil
  "Customization of Lego specifics for Proof General."
  :group 'proof-general)

;; I believe this is standard for Linux under RedHat -tms
(defcustom lego-tags "/usr/lib/lego/lib_Type/"
  "*the default TAGS table for the LEGO library"
  :type 'file
  :group 'lego-settings)

(defcustom lego-indent 2
  "*Indentation"
  :type 'number
  :group 'lego-settings)

(defcustom lego-test-all-name "test_all"
  "*The name of the LEGO module which inherits all other modules of the
  library."
  :type 'string
  :group 'lego-settings)

(defcustom lego-help-menu-list
  '(["The LEGO Reference Card" (w3-fetch lego-www-refcard) t]
    ["The LEGO library (WWW)" (w3-fetch lego-library-www-page)  t])
  "List of menu items, as defined in `easy-menu-define' for LEGO
  specific help."
  :type '(repeat sexp)
  :group 'lego-settings)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Configuration of Generic Proof Package ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Users should not need to change this. 

(defvar lego-shell-process-output
  '((lambda (cmd string) (string-match "^Module" cmd)) .
    (lambda (cmd string)
      (setq proof-shell-delayed-output
	    (cons 'insert "Imports done!"))))
  "Acknowledge end of processing import declarations.")

(defvar lego-assistant "LEGO"
  "Name of proof assistant")

(defconst lego-process-config "Configure PrettyOn; Configure AnnotateOn;"
  "Command to enable pretty printing of the LEGO process.")

(defconst lego-pretty-set-width "Configure PrettyWidth %s; "
  "Command to adjust the linewidth for pretty printing of the LEGO
  process.") 

(defconst lego-interrupt-regexp "Interrupt.."
  "Regexp corresponding to an interrupt")

(defvar lego-path-name "LEGOPATH"
  "The name of the environmental variable to search for modules. This
  is used by \\{legogrep} to find the files corresponding to a
  search.")

(defvar lego-path-separator ":"
  "A character indicating how the items in the \\{lego-path-name} are
  separated.") 


;; ----- web documentation

(defcustom lego-www-home-page "http://www.dcs.ed.ac.uk/home/lego/"
  "Lego home page URL."
  :type 'string
  :group 'lego-settings)

;; FIXME da: this doesn't belong here, it's only used by lego.
;; (and it shouldn't be called w3-* !!)
(defun w3-remove-file-name (address)
  "Remove the file name in a World Wide Web address"
  (string-match "://[^/]+/" address)
  (concat (substring address 0 (match-end 0))
          (file-name-directory (substring address (match-end 0)))))

(defcustom lego-www-latest-release
  (concat (w3-remove-file-name lego-www-home-page)
  "html/release-1.3/")
  "The WWW address for the latest LEGO release."
  :type 'string
  :group 'lego-settings)
	  
(defcustom lego-www-refcard
  (concat lego-www-latest-release "refcard.ps.gz")
  "URL for the Lego reference card."
  :type 'string
  :group 'lego-settings)

(defcustom lego-library-www-page
  (concat lego-www-latest-release "library/library.html")
  "The HTML documentation of the LEGO library."
  :type 'string
  :group 'lego-settings)


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
   "lego-shell"
   ;; With nil argument for docstring, Emacs makes up a nice one.
   nil
   (lego-shell-mode-config))

(define-derived-mode lego-mode proof-mode
   "lego" nil
   (lego-mode-config)
   (easy-menu-change (list proof-mode-name) (car proof-help-menu)
		     (append (cdr proof-help-menu) lego-help-menu-list)))

(define-derived-mode lego-pbp-mode pbp-mode
  "pbp" nil
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
	(setq ans (concat lego-forget-id-command
			  (span-property span 'name) proof-terminal-string)))

       ;; alternative definitions
       ((string-match lego-definiendum-alternative-regexp str)
	(setq ans (concat lego-forget-id-command (match-string 1 str)
			  proof-terminal-string)))
       ;; declarations
       ((string-match (concat "\\`\\$?" (lego-decl-defn-regexp "[:|=]")) str)
	(let ((ids (match-string 1 str))) ; returns "a,b"
	  (string-match proof-id ids)	; matches "a"
	  (setq ans (concat lego-forget-id-command(match-string 1 ids)
			    proof-terminal-string))))
	   
       ((string-match "\\`\\(Inductive\\|\\Record\\)\\s-*\\[\\s-*\\w+\\s-*:[^;]+\\`Parameters\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans (concat lego-forget-id-command
			  (match-string 2 str) proof-terminal-string)))

       ((string-match 
	 "\\`\\(Inductive\\|Record\\)\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans 
	      (concat lego-forget-id-command (match-string 2 str)
		      proof-terminal-string)))
       
       ((string-match "\\`\\s-*Module\\s-+\\(\\S-+\\)\\W" str)
	(setq ans (concat "ForgetMark " (match-string 1 str) 
			  proof-terminal-string))))
      
      (setq span (next-span span 'type)))
  (or ans proof-no-command)))
  
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

;; where to find files

  (setq compilation-search-path (cons nil (lego-get-path)))

  (setq blink-matching-paren-dont-ignore-comments t)

;; font-lock

  (setq font-lock-keywords lego-font-lock-keywords-1)

;; if we don't have the following in xemacs, zap-commas fails to work.

  (and (boundp 'font-lock-always-fontify-immediately)
       (setq font-lock-always-fontify-immediately t))

;; hooks and callbacks

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
	proof-shell-process-output-system-specific lego-shell-process-output
        lego-shell-current-line-width nil

	;;FIXME: we ought to set up separate font-lock instructions for
	;;the shell, the goal buffer and the script
	font-lock-keywords lego-font-lock-keywords-1)

  (lego-init-syntax-table)

  (proof-shell-config-done))

(defun lego-pbp-mode-config ()
  (setq pbp-change-goal "Next %s;")
  (setq pbp-error-regexp lego-error-regexp))

(provide 'lego)
