;; proof-menu.el  Menu and keymaps for Proof General
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;; Authors:  David Aspinall
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Key bindings
;;;

;;;###autoload
(defun proof-menu-define-keys (map)
(define-key map [(control c) (control a)] (proof-assistant-keymap))
;; FIXME: C-c C-a and C-c C-e are lost.
;; Consider adding new submap for movement in proof script.
;; (define-key map [(control c) (control e)] 'proof-goto-command-end)
; (define-key map [(control c) (control a)] 'proof-goto-command-start)
(define-key map [(control c) (control b)] 'proof-process-buffer)
; C-c C-c is proof-interrupt-process in universal-keys
(define-key map [(control c) (control n)] 'proof-assert-next-command-interactive)
(define-key map [(control c) (control p)] 'proof-prf)
(define-key map [(control c) (control r)] 'proof-retract-buffer)
(define-key map [(control c) (control s)] 'proof-toggle-active-scripting)
(define-key map [(control c) (control t)] 'proof-ctxt)
(define-key map [(control c) (control u)] 'proof-undo-last-successful-command)
(define-key map [(control c) (control backspace)] 'proof-undo-and-delete-last-successful-command)
; C-c C-v is proof-minibuffer-cmd in universal-keys
(define-key map [(control c) (control z)] 'proof-frob-locked-end)
(define-key map [(control c) (control ?.)] 'proof-goto-end-of-locked)
(define-key map [(control c) (control return)] 'proof-goto-point)
(cond ((string-match "XEmacs" emacs-version)
(define-key map [(control button3)]	  'proof-mouse-goto-point)
(define-key map [(control button1)]	  'proof-mouse-track-insert)) ; no FSF
      (t 
(define-key map [mouse-3]		  'proof-mouse-goto-point))) ; FSF
;; NB: next binding overwrites comint-find-source-code.  
(define-key map [(control c) (control f)] 'proof-find-theorems)
(define-key map [(control c) (control h)] 'proof-help)
;; FIXME: not implemented yet 
;; (define-key map [(meta p)]		  'proof-previous-matching-command)
;; (define-key map [(meta n)]		  'proof-next-matching-command)
;; Deprecated bindings
;(define-key map [(control c) return] 'proof-assert-next-command)
;(define-key map [(control c) ?u] 'proof-retract-until-point-interactive)
;; Add the universal keys bound in all PG buffers.
(proof-define-keys map proof-universal-keys))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Functions to define the menus
;;;

;; The main Proof-General generic menu

;;;###autoload
(defun proof-menu-define-main ()
  (easy-menu-define 
   proof-mode-menu  
   proof-mode-map
   "The main Proof General menu"
   (cons proof-general-name
	 (append
	  proof-toolbar-scripting-menu
	  proof-menu
	  (list "----")
	  (append
	   (list (customize-menu-create 'proof-general))
	   (list (customize-menu-create 'proof-general-internals 
					"Internals")))
	  proof-bug-report-menu))))


;; The proof assistant specific menu

;;;###autoload
(defun proof-menu-define-specific ()
  (easy-menu-define 
   proof-assistant-menu 
   proof-mode-map
   (concat "The menu for " proof-assistant)
   (cons proof-assistant
	 (append
	  (proof-ass menu-entries)
	  '("----")
	  (proof-ass favourites)
	  '(["Add favourite" 
	     (call-interactively 'proof-add-favourite) t])
	  '("----")
	  (list
	   (cons "Help"
		 (append 
		  `(;; FIXME: should only put these two on the
		    ;; menu if the settings are non-nil.
		    [,(concat proof-assistant " information")
		     (proof-help) t]
		    [,(concat proof-assistant " web page")
		     (browse-url proof-assistant-home-page) t])
		  (proof-ass help-menu-entries))))))))
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Contents of the generic menus
;;;

(defvar proof-help-menu
  '("Help"
    ["Proof General home page"
     (browse-url proof-general-home-page) t]
    ["Proof General Info"
     (info "ProofGeneral") t])
  "Proof General help menu.")

(defvar proof-buffer-menu
  '("Buffers"
    ["Active scripting"
     (proof-switch-to-buffer proof-script-buffer)
     :active (buffer-live-p proof-script-buffer)]
    ["Goals"
     (proof-switch-to-buffer proof-goals-buffer t)
     :active (buffer-live-p proof-goals-buffer)]
    ["Response"
     (proof-switch-to-buffer proof-response-buffer t)
     :active (buffer-live-p proof-response-buffer)]
    ["Shell"
     (proof-switch-to-buffer proof-shell-buffer)
     :active (buffer-live-p proof-shell-buffer)])
  "Proof General buffer menu.")

;; Make the togglers used in options menu below

(proof-deftoggle proof-dont-switch-windows)
(proof-deftoggle proof-delete-empty-windows)
(proof-deftoggle proof-multiple-frames-enable proof-multiple-frames-toggle)
(proof-deftoggle proof-output-fontify-enable proof-output-fontify-toggle)
(proof-deftoggle proof-x-symbol-enable proof-x-symbol-toggle)

(defvar proof-quick-opts-menu
  `("Options"
    ["Don't switch windows" proof-dont-switch-windows-toggle
     :style toggle
     :selected proof-dont-switch-windows]
    ["Delete empty windows" proof-delete-empty-windows-toggle
     :style toggle
     :selected proof-delete-empty-windows]
    ["Multiple frames" proof-multiple-frames-toggle
     :style toggle
     :selected proof-multiple-frames-enable]
    ["Output highlighting" proof-output-fontify-toggle
     :active t
     :style toggle
     :selected proof-output-fontify-enable]
    ["Toolbar" proof-toolbar-toggle
     :active (and (featurep 'toolbar) 
		  (boundp 'proof-buffer-type)
		  (eq proof-buffer-type 'script))
     :style toggle
     :selected proof-toolbar-enable]
    ["X-Symbol" proof-x-symbol-toggle
     :active (proof-x-symbol-support-maybe-available)
     :style toggle
     :selected proof-x-symbol-enable]
    ("Follow mode" 
     ["Follow locked region" 
      (customize-set-variable 'proof-follow-mode 'locked)
     :style radio
     :selected (eq proof-follow-mode 'locked)]
     ["Keep locked region displayed" 
      (customize-set-variable 'proof-follow-mode 'follow)
     :style radio
     :selected (eq proof-follow-mode 'follow)]
     ["Never move" 
      (customize-set-variable 'proof-follow-mode 'ignore)
     :style radio
     :selected (eq proof-follow-mode 'ignore)]))
  "Proof General quick options.")

(defvar proof-shared-menu
  (append
   ;; FIXME: should we move the start and stop items to 
   ;; the specific menu?  
   ;; (They only seem specific because they mention the PA).
    (list
     (vector
      (concat "Start " proof-assistant)
      'proof-shell-start
      ':active '(not (proof-shell-live-buffer)))
     (vector
      (concat "Exit " proof-assistant)
      'proof-shell-exit
      ':active '(proof-shell-live-buffer)))
    (list proof-buffer-menu)
    (list proof-quick-opts-menu)
    (list proof-help-menu))
  "Proof General menu for various modes.")

(defvar proof-bug-report-menu
  (list "----"
   ["About Proof General" proof-splash-display-screen t]
   ["Submit bug report"   proof-submit-bug-report t])
  "Proof General menu for submitting bug report (one item plus separator).")

(defvar proof-menu  
  (append '("----"
	    ["Scripting active" proof-toggle-active-scripting
	     :style toggle
	     :selected (eq proof-script-buffer (current-buffer))]
	    ["Electric terminator" proof-electric-terminator-toggle
	     :style toggle
             :selected proof-electric-terminator-enable]
	    ["Function menu" function-menu
	     :active (fboundp 'function-menu)]
	    "----")
          proof-shared-menu)
  "The Proof General generic menu.")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Favourites mechanism for specific menu
;;;


(defmacro proof-defshortcut (fn string &optional key)
  "Define shortcut function FN to insert STRING, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is inserted using `proof-insert', which see.
KEY is added onto proof-assistant map."
  (if key
      (eval
       `(define-key (proof-ass keymap) ,key (quote ,fn))))
  `(defun ,fn ()
     (concat "Shortcut command to insert " ,string " into the current buffer.")
     (interactive)
     (proof-insert ,string)))

(defmacro proof-definvisible (fn string &optional key)
  "Define function FN to send STRING to proof assistant, optional keydef KEY.
This is intended for defining proof assistant specific functions.
STRING is sent using proof-shell-invisible-command, which see.
KEY is added onto proof-assistant map."
  (if key
      (eval
       `(define-key (proof-ass keymap) ,key (quote ,fn))))
  `(defun ,fn ()
     (concat "Command to send " ,string " to the proof assistant.")
     (interactive)
     (proof-shell-invisible-command ,string)))


;;; Code for adding "favourites" to the proof-assistant specific menu

(defvar proof-make-favourite-cmd-history nil
  "History for proof-make-favourite.")

(defun proof-add-favourite (command inscript menuname &optional key)
  "Define and add a \"favourite\" proof-assisant function to the menu bar.
The favourite function will issue COMMAND to the proof assistant.  
COMMAND is inserted into script (not sent immediately) if INSCRIPT non-nil.
MENUNAME is the name of the function for the menu.
KEY is the optional key binding
This function defines a function and returns a menu entry 
suitable for adding to the proof assistant menu."
  (interactive 
   (let* 
       ((cmd (read-string 
	      (concat "Command to send to " proof-assistant ": ") nil 
	      proof-make-favourite-cmd-history))
	(ins (y-or-n-p "Should command be recorded in script? "))
	(men (read-string "Name of command on menu: " cmd))
	(key (if (y-or-n-p "Set a keybinding for this command? : ")
		 (read-key-sequence 
		  "Type the key to use (I recommend C-c C-a <key>): " nil t))))
     (list cmd ins men key)))
  (let* ((menunames	(split-string (downcase menuname)))
	 (menuname-sym  (proof-sym (proof-splice-separator "-" menunames)))
	 (menu-fn	menuname-sym) (i 1))
    (while (fboundp menu-fn)
      (setq menu-fn (intern (concat (symbol-name menuname-sym)
				    "-" (int-to-string i))))
      (incf i))
    (if inscript
	(eval `(proof-defshortcut ,menu-fn ,command ,key))
      (eval `(proof-definvisible ,menu-fn ,command ,key)))
    (let ((menu-entry (vector menuname menu-fn t)))
      (customize-save-variable (proof-ass-sym menu-entries)
			       (append (proof-ass menu-entries)
				       (list menu-entry)))
      ;; Unfortunately, (easy-menu-add-item proof-assistant-menu nil ..)
      ;; seems buggy, it adds to main menu. But with "Coq" argument 
      ;; for path it adds a submenu!   The item argument seems to be
      ;; something special, but no way to make an item for adding
      ;; an ordinary item?!
      (easy-menu-add-item proof-assistant-menu 
			  '("Favourites")
			  menu-entry 
			  "Add favourite"))
    (warn 
     "PG: favourites mechanism is work-in-progress, not fully working yet!")))



(provide 'proof-menu)
;; proof-menu.el ends here.
