;; proof.el Major mode for proof assistants Copyright (C) 1994,
;; 1995, 1996 LFCS Edinburgh. This version by Dilip Sequeira, by
;; rearranging Thomas Schreiber's code.

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Time-stamp: <17 Oct 96 djs /home/lego/emacs/lego.el>
;; Thanks to David Aspinall, Robert Boyer, Rod Burstall,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens  

(require 'proof)

; Configuration                                  

(defconst lego-mode-version-string
  "LEGO-MODE. ALPHA Version 1.11 (June 1996) LEGO Team <lego@dcs.ed.ac.uk>")

(defvar lego-tags "/usr/local/share/lego/lib-alpha/lib_all/TAGS"
  "the default TAGS table for the LEGO library")

(defvar lego-pretty-p t
  "In the latest version of LEGO, pretty printing using Oppen's
  algorithm can be switched on, but is disabled. The Emacs interface
  is primarily concerned to make life easier. There it will enable
  pretty printing")

(defconst lego-pretty-on "Configure PrettyOn;"
  "Command to enable pretty printing of the LEGO process.")

(defconst lego-pretty-set-width "Configure PrettyWidth %s;"
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

(defvar lego-shell-process-name "lego"
  "*The name of the lego-process")

(defvar lego-shell-prog-name "lego"
  "*Name of program to run as lego.")

(defvar lego-shell-working-dir ""
  "The working directory of the lego shell")

(defvar lego-shell-prompt-pattern "^\\(Lego> *\\)+"
  "*The prompt pattern for the inferion shell running lego.")

;; ----- outline

(defvar lego-goal-regexp "?[0-9]+  : ")

(defvar lego-outline-regexp 
  (ids-to-regexp 
   '("*" "Discharge" "Freeze" "Goal" "Module" "[" "Record" "Inductive" 
     "Unfreeze")))

(defvar lego-outline-heading-end-regexp ";\\|\\*)")

(defvar lego-shell-outline-regexp lego-goal-regexp)
(defvar lego-shell-outline-heading-end-regexp lego-goal-regexp)

;; ----- keywords for font-lock. If you want to hack deeper, you'd better
;; ----- be fluent in regexps - it's in the YUK section.

(defvar lego-keywords 
  '("andI" "Claim" "Constructors" "Cut" "Discharge" "DischargeKeep"
    "Double" "echo" "ElimOver" "Expand" "ExpAll" "ExportState" "Equiv"
    "Fields" "Freeze" "From" "$?Goal" "Hnf" "Immed" "Import" "Induction"
    "Inductive" "Inversion" "Init" "intros" "Intros" "Module" "Next"
    "NoReductions" "Normal" "Parameters" "Qnify" "Qrepl" "Record"
    "Refine" "Relation" "$?Save" "$?SaveFrozen" "$?SaveUnfrozen"
    "Theorems" "Unfreeze"))

(defvar lego-shell-keywords 
  '("Cd" "Ctxt" "Decls" "Forget" "ForgetMark" "Help" "KillRef" "Load"
    "Make" "Prf" "Pwd" "Help" "KillRef" "Load" "Make" "Prf" "Pwd"
    "Reload" "Undo"))

(defvar lego-tacticals '("Then" "Else" "Try" "Repeat" "For"))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode lego-shell-mode comint-mode
   "lego-shell" "Inferior shell mode for lego shell"
   (lego-shell-mode-config))

(define-derived-mode lego-mode proof-mode
   "lego" "Lego Mode"
   (lego-mode-config))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Popup and Pulldown Menu ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shared-menu
  (append '(
            ["Display context" lego-ctxt
	      :active (proof-shell-buffer)]
            ["Display proof state" lego-prf
	      :active (proof-shell-buffer)]
            ["Restart the proof" lego-restart-goal
	      :active (proof-shell-buffer)]
           ["Kill the current refinement proof"
            lego-killref  :active (proof-shell-buffer)]
           ["Undo last proof step" lego-undo-1
             :active (proof-shell-buffer)]
           ["Exit LEGO" proof-shell-exit
	     :active (proof-shell-buffer)]
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

(defvar lego-process-menu
  '("Process LEGO code"
    ["Process buffer"  lego-make-buffer  t]
    ["Process buffer until point" lego-make-buffer-until-point
      t]
    ["Process command" proof-send-command  t]
    ["Process line"    proof-send-line     t]
    ["Process region"  proof-send-region   t])
  "*Interaction between the proof script and the LEGO process.")

(defvar lego-menu  
  (append '("LEGO Commands"
            ["Start LEGO" lego-shell
             :active (not (comint-check-proc (and proof-shell-process-name
						  (proof-shell-buffer))))]
            ["Toggle active ;" proof-active-terminator-minor-mode
	     :active t
	     :style toggle
             :selected proof-active-terminator-minor-mode]
            "----")
          (list lego-process-menu)
          '("----")
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  *   *  *    *  *    *    ;;
;;   * *   *    *  *   *     ;;
;;    *    *    *  ****      ;;
;;    *    *    *  *  *      ;;
;;    *    *    *  *   *     ;;
;;    *     ****   *    *    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-decl-defn-regexp (char)
  (concat "\\[ *\\([^][" char " ]+\\) *\\(\\[[^]]*\\]\\)* *" char))

(defvar lego-font-lock-keywords-1
   (list

     (cons (ids-to-regexp lego-keywords) 'font-lock-keyword-face)
     (cons (ids-to-regexp lego-tacticals) 'font-lock-tacticals-name-face)

     (list (lego-decl-defn-regexp ":") 1 'font-lock-declaration-name-face)
     (list (lego-decl-defn-regexp "|") 1 'font-lock-declaration-name-face)
     (list (lego-decl-defn-regexp "=") 1 'font-lock-function-name-face)
     (list "[{<]\\([^:|]+\\)" 1 'font-lock-declaration-name-face)

     (list "\\<$?Goal\\>[ \t]+\\(\\<[^ \t\n\):]+\\) *:"
             1 'font-lock-function-name-face)
     (list "\\<$?Save\\>[ \t]+\\([^ \t\n\):]+\\) *;" 1
	   'font-lock-function-name-face)
     ;; Kinds

     '("\\<Prop\\>\\|\\<Type *\\(([^)]+)\\)?" . font-lock-type-face)))

(defvar lego-shell-font-lock-keywords-1
  (append lego-font-lock-keywords-1
	  (list
	   (cons (ids-to-regexp lego-shell-keywords) 
		 'font-lock-keywords-name-face)
	   '("\\<defn\\>  \\([^ \t\n\)]+\\) =" 1 font-lock-function-name-face)
	  '("^\\(value of\\|type  of\\) \\([^ \t\n\)]+\\) =" 2 
	    font-lock-function-name-face)
	  '("^  \\([^ \t\n\)]+\\) = ... :" 1 font-lock-function-name-face)

	  '("^  \\([^ \t\n\)]+\\) : " 1 font-lock-declaration-name-face)
	  '("\\<decl\\>  \\([^:]+\\) :" 1 font-lock-declaration-name-face)
	  '("\\<decl\\>  \\(.+\\) |" 1 font-lock-declaration-name-face)
	  '("^value = \\([^ \t\n\)]+\\)" 1 font-lock-declaration-name-face)

	  ;; Error Messages (only required in the process buffer)

	  '("attempt to apply\\|with domain type\\|^to " .font-lock-error-face)
	  '("^Error.*\n" .font-lock-error-face))))

;;
;; A big hack to unfontify commas in declarations.  All that can be
;; said for it is that the previous way of doing this was even more
;; bogus.
;;

;; Refontify the whole line, 'cos that's what font-lock-after-change
;; does.

(defun lego-zap-commas-region (start end length)
  (save-excursion
    (let 
	((start (progn (goto-char start) (beginning-of-line) (point)))
	 (end (progn (goto-char end) (end-of-line) (point))))
      (goto-char start)
      (while (search-forward "," end t)
	(if (eq (get-char-property (- (point) 1) 'face)
		'font-lock-declaration-name-face)
	    (font-lock-remove-face (- (point) 1) (point)))))))

(defun lego-zap-commas-buffer () 
  (lego-zap-commas-region (point-min) (point-max) 0))

(defun lego-fixup-change ()
     (make-local-variable 'after-change-functions)
     (setq after-change-functions
	   (append (delq 'lego-zap-commas-region after-change-functions)
		   '(lego-zap-commas-region))))

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

(defun lego-add-common-bindings (map)
  "*adds keybindings used in both lego-mode and lego-shell."
  (define-key map "\M-\C-i"
    (if (fboundp 'complete-tag)
	'complete-tag		; Emacs 19.31 (superior etags)
      'tag-complete-symbol))	;XEmacs 19.13 (inferior etags)
  (define-key map "\C-c\C-s" 'legogrep)
  (define-key map "\C-c\C-p" 'lego-prf)
  (define-key map "\C-ci"    'lego-intros)
  (define-key map "\C-cI"    'lego-Intros)
  (define-key map "\C-cr"    'lego-Refine)
  (define-key map "\C-c\C-k" 'lego-killref)
  (define-key map "\C-c\C-u" 'lego-undo-1)
  (define-key map "\C-c\C-t" 'lego-restart-goal)
  (define-key map "\C-c\C-c" 'proof-interrupt-subjob)
  map)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to lego                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-restart-goal ()
  "Restart the current proof."
  (interactive)
  (proof-command "Undo 9999"))          ;hopefully 9999 is large
                                        ;enough!
(defun lego-killref ()
  "Kill the current refinement proof."
  (interactive)
  (proof-command "KillRef"))

(defun lego-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-command "Help"))

(defun lego-undo-1 ()
  "Undo the last step in a proof."
  (interactive)
  (proof-command "Undo 1"))

(defun lego-prf ()
  "List proof state."
  (interactive)
  (proof-command "Prf"))

(defun lego-ctxt ()
  "List context."
  (interactive) 
  (proof-command "Ctxt"))

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

(defun lego-shell ()
  "Start a lego shell"
  (interactive) 
  (proof-start-shell))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Line width auto-adjust                                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shell-current-line-width nil
  "Current line width of the LEGO process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; The line width needs to be adjusted if the LEGO process is
;; running and is out of sync with the screen width

(defun lego-adjust-line-width ()
  "Uses LEGO's pretty printing facilities to adjust the line width of
  the output."
  (and (comint-check-proc (and proof-shell-process-name (proof-shell-buffer)))
       (let ((current-width
	      (window-width (get-buffer-window proof-shell-buffer-name t))))
	 (and (not (equal current-width
			  lego-shell-current-line-width))
	      (progn 
		(setq lego-shell-current-line-width current-width)
		(comint-simple-send lego-shell-process-name
				    (format lego-pretty-set-width
					    (- current-width 1))))))))

(defun lego-shell-zap-line-width () 	     
  (setq lego-shell-current-line-width nil))
      
(defun lego-shell-init-lego ()
  (setq compilation-search-path (cons nil (lego-get-path)))
  (cond (lego-pretty-p
	 (setq lego-shell-current-line-width nil)
	 (accept-process-output (get-process proof-shell-process-name))
	 (proof-simple-send lego-pretty-on t))))

;;;;;;;;;;;;;;;;;;;;;;;
;;   Make support    ;;
;;;;;;;;;;;;;;;;;;;;;;;

(defun possibly-save-current-buffer ()
  "If the buffer has been modified, the user will be asked if it
should be saved and appropriate action will be taken. This code was
nicked from AUCTeX's tex-buffer.el"
  (and (buffer-modified-p)
       (or (not lego-save-query)
           (y-or-n-p (concat "Save file "
                             (buffer-file-name)
                             "? ")))
       (save-buffer)))  

(defun lego-module-name (file)
  "Extract the name of the module from a file."
  (substring (file-name-nondirectory file) 0 -2))

(defun lego-make-buffer ()
  "Save file then execute a Make command on it."
  (interactive)
  (possibly-save-current-buffer)
  (let ((module-name (lego-module-name buffer-file-name)))
    (proof-simple-send (concat lego-make-command " " module-name ";") t)))

(defun lego-make-buffer-until-point ()
  "Comment out anything after point, then save file and run a Make"
  (interactive)
  (let ((current-buffer (current-buffer))
        (temp-buffer (generate-new-buffer "*LEGO TMP*")))
    (save-excursion
      (set-buffer temp-buffer)
      (insert-buffer current-buffer))
    (let ((current-point (point)))
      (insert proof-comment-start)
      (goto-char (point-max))
      (insert proof-comment-end)
      (lego-make-buffer)
      (erase-buffer)
      (insert-buffer temp-buffer)
      (goto-char current-point))
    (kill-buffer temp-buffer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof mode and setting up various utilities        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-shell-mode-config ()

  (lego-add-common-bindings lego-shell-mode-map)
  (easy-menu-add lego-shell-menu lego-shell-mode-map)
  (define-key lego-shell-mode-map
      (if running-xemacs [(meta button1)] [S-down-mouse-1]) 
        'lego-x-mouse-refine-point))

      ;; in XEmacs 19.11 [S-down-mouse-1] is bound to
      ;; `mouse-track-adjust'
      ;; in Emacs 19.28 [(meta button1)] is bound to
      ;; `mouse-drag-secondary' 


(defun lego-mode-config ()

;; ----- things before proof-mode-child-config-done are mandatory.

  (setq proof-terminal-char ?\;)
  (setq proof-comment-start "(*")
  (setq proof-comment-end "*)")
  (modify-syntax-entry ?_ "w" lego-mode-syntax-table)
  (modify-syntax-entry ?\* ". 23" lego-mode-syntax-table)
  (modify-syntax-entry ?\( "()1" lego-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" lego-mode-syntax-table)

;; These should really be defvaralias, since if the user changes them
;; interactively proof mode won't see the alterations. Unfortunately
;; emacs can't cope with aliases to buffer local variables

  (setq proof-shell-prog-name lego-shell-prog-name)
  (setq proof-shell-process-name lego-shell-process-name)
  (setq proof-shell-prompt-pattern lego-shell-prompt-pattern)
  (setq proof-shell-working-dir lego-shell-working-dir)
  (setq proof-shell-mode-is 'lego-shell-mode)

  (proof-mode-child-config-done)

;; ---------- Everything below here is strictly optional - it's mostly
;; ---------- just support for minor modes


;; where to find files

  (setq compilation-search-path (cons nil (lego-get-path)))

;; hooks to support automatic line-width adjustment

  (add-hook 'proof-shell-safe-send-hook 'lego-adjust-line-width)
  (add-hook 'proof-shell-exit-hook 'lego-shell-zap-line-width)
  (add-hook 'proof-shell-pre-display-hook 'lego-shell-init-lego)

;; keymaps and menus

  (lego-add-common-bindings lego-mode-map)
  (define-key lego-mode-map ";"        'proof-active-terminator)
  (define-key lego-mode-map [(control c) (control b)] 'lego-make-buffer)
  (define-key lego-mode-map [(control c) (control h)] 
    'lego-make-buffer-until-point)
  (define-key lego-mode-map "\C-c;"    'proof-active-terminator-minor-mode)
  (define-key lego-mode-map [(control c) (control j)] 'proof-send-line)
  (define-key lego-mode-map [(control c) (control r)] 'proof-send-region)

  (easy-menu-add lego-mode-menu lego-mode-map)

;; etags support for Emacs 19.31

  (cond ((boundp 'tags-table-list)
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons lego-tags tags-table-list))
	 (setq tag-table-alist
	       (append '(("\\.l$" . lego-tags)
			 ("lego"  . lego-tags))
		       tag-table-alist))))

;; outline
  
  (make-local-variable 'outline-regexp)
  (setq outline-regexp lego-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp lego-outline-heading-end-regexp)

;; hooks for font locks

(cond (running-xemacs
       (put 'lego-mode 'font-lock-keywords 'lego-font-lock-keywords-1)
       (put 'lego-shell 'font-lock-keywords
	    'lego-shell-font-lock-keywords-1))

      (running-emacs19
       (add-hook 'lego-mode-hook
		 '(lambda () (setq font-lock-keywords
				   lego-font-lock-keywords-1)))
       
       (add-hook 'lego-shell-post-display-hook
		 '(lambda () (setq font-lock-keywords
				   lego-shell-font-lock-keywords-1)))))

(remove-hook 'font-lock-after-fontify-buffer-hook  'lego-zap-commas-buffer t)
(add-hook 'font-lock-after-fontify-buffer-hook  'lego-zap-commas-buffer nil t)

(remove-hook 'font-lock-mode-hook 'lego-fixup-change t)
(add-hook 'font-lock-mode-hook 'lego-fixup-change nil t)

;; if we don't have the following, zap-commas fails to work.

(setq font-lock-always-fontify-immediately t)

;; insert standard header and footer in fresh buffers

  (and (equal (buffer-size) 0)
       buffer-file-name
       (or (file-exists-p buffer-file-name)
	   (prog2
	       (insert-before-markers
		(format "Module %s;" (lego-module-name buffer-file-name)))
	       )))
  )

(provide 'lego)
