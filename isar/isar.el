;; isar.el Major mode for Isabelle/Isar proof assistant
;; Copyright (C) 1994-1998 LFCS Edinburgh.
;;
;; Author:              David Aspinall <da@dcs.ed.ac.uk>
;; Author / Maintainer: Markus Wenzel <wenzelm@in.tum.de>
;;
;; $Id$
;;


;; Add Isabelle image onto splash screen
(customize-set-variable
 'proof-splash-extensions
 '(list
   nil
   (proof-splash-display-image "isabelle_transparent" t)))

;; In case Isar mode was invoked directly or by -*- isar -*- at
;; the start of the file, ensure that Isar mode is used from now
;; on for .thy files.
;; FIXME: be less messy with auto-mode-alist here (remove dups)
(setq auto-mode-alist
      (cons '("\\.thy$" . isar-mode) auto-mode-alist))

(require 'proof)
(require 'isar-syntax)

;; Completion table for Isabelle/Isar identifiers
(defpgdefault completion-table isar-keywords-major)

;; Add generic code for Isabelle and Isabelle/Isar
(setq load-path (cons (concat proof-home-directory "isa/") load-path))
(require 'isabelle-system)
(require 'x-symbol-isabelle)

(defcustom isar-web-page
  "http://isabelle.in.tum.de/Isar/"
  "URL of web page for Isabelle/Isar."
  :type 'string
  :group 'isabelle-isar)

;; Adjust toolbar entries (must be done before proof-toolbar is loaded).

(if proof-running-on-XEmacs
    (setq isar-toolbar-entries
	  (remassoc 'qed (remassoc 'goal isar-toolbar-entries))))


;;;
;;; theory header
;;;

(defun isar-detect-header ()
  "Detect new-style theory header in current buffer"
  (let ((header-regexp (isar-ids-to-regexp '("header" "theory")))
        (white-space-regexp "\\(\\s-\\|\n\\)+")
        (cmt-end-regexp (regexp-quote proof-comment-end))
        (cmt-start-regexp (regexp-quote proof-comment-start))
        (found-header nil) forward-amount
        (end (point-max)) (cont t) (cmt-level 0))
    (save-excursion
      (goto-char (point-min))
      (while (and cont (< (point) end))
        (setq forward-amount 1)
        (cond
         ;; comments
         ((proof-looking-at cmt-start-regexp)
          (setq forward-amount (length (match-string 0)))
          (incf cmt-level))
         ((proof-looking-at cmt-end-regexp)
          (setq forward-amount (length (match-string 0)))
          (decf cmt-level))
         ((> cmt-level 0))
         ;; white space
         ((proof-looking-at white-space-regexp)
          (setq forward-amount (length (match-string 0))))
         ;; theory header
         ((proof-looking-at header-regexp)
          (setq found-header t)
          (setq cont nil))
         ;; bad stuff
         (t
          (setq cont nil)))
        (and cont (forward-char forward-amount)))
      found-header)))


(defun isar-strip-terminators ()
  "Remove explicit Isabelle/Isar command terminators `;' from the buffer."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (search-forward ";" (point-max) t)
      (if (not (proof-buffer-syntactic-context))
          (delete-backward-char 1)))))


(defun isar-markup-ml (string)
  "Return marked up version of ML command STRING for Isar."
  (format "ML_command {* %s *};" string))


(defun isar-mode-config-set-variables ()
  "Configure generic proof scripting mode variables for Isabelle/Isar."
  (setq
   proof-assistant-home-page    isar-web-page
   proof-mode-for-script        'isar-mode
   ;; proof script syntax
   proof-terminal-char          ?\;     ; forcibly ends a command
   proof-script-command-start-regexp (proof-regexp-alt
                                      isar-any-command-regexp
                                      (regexp-quote ";"))
   proof-script-integral-proofs t
   proof-comment-start          isar-comment-start
   proof-comment-end            isar-comment-end
   proof-comment-start-regexp   isar-comment-start-regexp
   proof-comment-end-regexp     isar-comment-end-regexp
   proof-string-start-regexp    isar-string-start-regexp
   proof-string-end-regexp      isar-string-end-regexp

   ;; Next few used for func-menu and recognizing goal..save regions in
   ;; script buffer.
   proof-save-command-regexp    isar-save-command-regexp
   proof-goal-command-regexp    isar-goal-command-regexp
   proof-goal-with-hole-regexp  isar-named-entity-regexp ; da
   proof-save-with-hole-regexp  nil
   proof-script-next-entity-regexps isar-next-entity-regexps

   proof-indent-enclose-offset  (- proof-indent)
   proof-indent-open-offset     0
   proof-indent-close-offset    0
   proof-indent-any-regexp      isar-indent-any-regexp
;   proof-indent-inner-regexp    isar-indent-inner-regexp
   proof-indent-enclose-regexp  isar-indent-enclose-regexp
   proof-indent-open-regexp     isar-indent-open-regexp
   proof-indent-close-regexp    isar-indent-close-regexp

   ;; proof engine commands
   proof-showproof-command      "pr"
   proof-goal-command           "lemma \"%s\""
   proof-save-command           "qed"
   proof-context-command        "print_context"
   proof-info-command           "welcome"
   proof-kill-goal-command      "ProofGeneral.kill_proof"
   proof-find-theorems-command  "thms_containing %s"
   proof-shell-start-silent-cmd "disable_pr"
   proof-shell-stop-silent-cmd  "enable_pr"
   ;; command hooks
   proof-goal-command-p         'isar-goal-command-p
   proof-really-save-command-p  'isar-global-save-command-p
   proof-count-undos-fn         'isar-count-undos
   proof-find-and-forget-fn     'isar-find-and-forget
   ;; da: for pbp.
   ;; proof-goal-hyp-fn         'isar-goal-hyp
   proof-state-preserving-p     'isar-state-preserving-p
   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list))

(defun isar-shell-mode-config-set-variables ()
  "Configure generic proof shell mode variables for Isabelle/Isar."
  (setq
   proof-shell-first-special-char       ?\350

   proof-shell-wakeup-char              ?\372
   proof-shell-annotated-prompt-regexp  "^\\w*[>#] \372"

   ;; This pattern is just for comint.
   proof-shell-prompt-pattern           "^\\w*[>#] "

   ;; for issuing command, not used to track cwd in any way.
   proof-shell-cd-cmd                   (isar-markup-ml "ThyLoad.add_path \"%s\"")

   ;; Escapes for filenames inside ML strings.
   ;; We also make a hack for a bug in Isabelle, by switching from
   ;; backslashes to forward slashes if it looks like we're running
   ;; on Windows.
   proof-shell-filename-escapes
   (if (fboundp 'win32-long-filename)   ; rough test for XEmacs on win32
       ;; Patterns to unixfy names.
       ;; Jacques Fleuriot's patch in ML does this too: ("^[a-zA-Z]:" . "")
       ;; But I'll risk leaving drive names in, not sure how to replace them.
       '(("\\\\" . "/") ("\"" . "\\\""))
     ;; Normal case: quotation for backslash, quote mark.
     '(("\\\\" . "\\\\") ("\""   . "\\\"")))

   proof-shell-proof-completed-regexp   nil     ; n.a.
   proof-shell-interrupt-regexp         "\364\\*\\*\\* Interrupt\\|\360Interrupt"
   proof-shell-error-regexp             "\364\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
   proof-shell-abort-goal-regexp        nil     ; n.a.

   ;; matches names of assumptions
   proof-shell-assumption-regexp        isar-id
   ;; matches subgoal name
   ;; da: not used at the moment, maybe after 3.0 used for
   ;; proof-generic-goal-hyp-fn to get pbp-like features.
   ;; proof-shell-goal-regexp           "\370[ \t]*\\([0-9]+\\)\\."

   proof-shell-start-goals-regexp       "\366\n"
   proof-shell-end-goals-regexp         "\367"
   proof-shell-goal-char                ?\370

   proof-assistant-setting-format       'isar-markup-ml
   proof-shell-init-cmd                 (proof-assistant-settings-cmd)
   proof-shell-restart-cmd              "ProofGeneral.restart"
   proof-shell-quit-cmd                 "quit();"

   proof-shell-eager-annotation-start-length 1
   proof-shell-eager-annotation-start   "\360\\|\362"
   proof-shell-eager-annotation-end     "\361\\|\363"
   proof-shell-spill-output-regexp      "\375"

   ;; Some messages delimited by eager annotations
   proof-shell-clear-response-regexp    "Proof General, please clear the response buffer."
   proof-shell-clear-goals-regexp       "Proof General, please clear the goals buffer."

   ;; Dirty hack to allow font-locking for output based on hidden
   ;; annotations, see isar-output-font-lock-keywords-1
   proof-shell-leave-annotations-in-output t

   ;; === ANNOTATIONS  === ones below here are broken
   proof-shell-result-start             "\372 Pbp result \373"
   proof-shell-result-end               "\372 End Pbp result \373"
   proof-analyse-using-stack            t
   proof-shell-start-char               ?\372
   proof-shell-end-char                 ?\373
   proof-shell-field-char               ?\374

   proof-shell-process-file
   (cons
    ;; Theory loader output
    "Proof General, this file is loaded: \"\\(.*\\)\""
    (lambda (str)
      (match-string 1 str)))
   proof-shell-retract-files-regexp
   "Proof General, you can unlock the file \"\\(.*\\)\""
   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list
   proof-shell-inform-file-processed-cmd "ProofGeneral.inform_file_processed \"%s\""
   proof-shell-inform-file-retracted-cmd "ProofGeneral.inform_file_retracted \"%s\"")
  (add-hook 'proof-activate-scripting-hook 'isar-activate-scripting))


;;;
;;; Theory loader operations
;;;

(defun isar-remove-file (name files cmp-base)
  (if (not files) nil
    (let*
        ((file (car files))
         (rest (cdr files))
         (same (if cmp-base (string= name (file-name-nondirectory file))
                 (string= name file))))
      (if same (isar-remove-file name rest cmp-base)
        (cons file (isar-remove-file name rest cmp-base))))))

(defun isar-shell-compute-new-files-list (str)
  "Compute the new list of files read by the proof assistant.
This is called when Proof General spots output matching
proof-shell-retract-files-regexp."
  (let*
      ((name (match-string 1 str))
       (base-name (file-name-nondirectory name)))
    (if (string= name base-name)
        (isar-remove-file name proof-included-files-list t)
      (isar-remove-file (file-truename name) proof-included-files-list nil))))

(defun isar-activate-scripting ()
  "Make sure the Isabelle/Isar toplevel is in a sane state."
  (proof-cd-sync))


;;
;;   Define the derived modes
;;
(eval-and-compile
(define-derived-mode isar-shell-mode proof-shell-mode
   "Isabelle/Isar shell" nil
   (isar-shell-mode-config)))

(eval-and-compile
(define-derived-mode isar-response-mode proof-response-mode
  "Isabelle/Isar response" nil
  (isar-response-mode-config)))

(eval-and-compile                       ; to define vars for byte comp.
(define-derived-mode isar-goals-mode proof-goals-mode
  "Isabelle/Isar proofstate" nil
  (isar-goals-mode-config)))

(eval-and-compile                       ; to define vars for byte comp.
(define-derived-mode isar-mode proof-mode
    "Isabelle/Isar script" nil
    (isar-mode-config)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's Isabelle/Isar specific                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; help menu  
;;;

;;; da: how about a `C-c C-a h ?' for listing available keys?

;;; NB: definvisible must come after derived modes because uses
;;; isar-mode-map
(proof-definvisible isar-help-antiquotations "print_antiquotations" [h A])
(proof-definvisible isar-help-attributes "print_attributes" [h a])
(proof-definvisible isar-help-cases "print_cases" [h c])
(proof-definvisible isar-help-claset "print_claset" [h C])
(proof-definvisible isar-help-commands "print_commands" [h o])
(proof-definvisible isar-help-facts "print_facts" [h f])
(proof-definvisible isar-help-syntax "print_syntax" [h i])
(proof-definvisible isar-help-induct-rules "print_induct_rules" [h I])
(proof-definvisible isar-help-methods "print_methods" [h m])
(proof-definvisible isar-help-simpset "print_simpset" [h S])
(proof-definvisible isar-help-binds "print_binds" [h b])
(proof-definvisible isar-help-theorems "print_theorems" [h t])
(proof-definvisible isar-help-trans-rules "print_trans_rules" [h T])

(defpgdefault help-menu-entries
  (append
   isabelle-docs-menu
   (list
    (cons "Show me ..."
          (list
           ["antiquotations"     isar-help-antiquotations t]
           ["attributes"         isar-help-attributes     t]
           ["cases"              isar-help-cases          t]
           ["classical rules"    isar-help-claset         t]
           ["commands"           isar-help-commands       t]
           ["facts"              isar-help-facts          t]
           ["inner syntax"       isar-help-syntax         t]
           ["induct/cases rules" isar-help-induct-rules   t]
           ["methods"            isar-help-methods        t]
           ["simplifier rules"   isar-help-simpset        t]
           ["term bindings"      isar-help-binds          t]
           ["theorems"           isar-help-theorems       t]
           ["transitivity rules" isar-help-trans-rules    t])))))

;; undo proof commands
(defun isar-count-undos (span)
  "Count number of undos in a span, return the command needed to undo that far."
  (let
      ((case-fold-search nil)       ;FIXME ??
       (ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
             (or (proof-string-match isar-undo-skip-regexp str)
                 (setq ct (+ 1 ct))))
            ((eq (span-property span 'type) 'pbp)
             ;; this case probably redundant for Isabelle, unless
             ;; we think of some nice ways of matching non-undoable
             ;; commands.
             (cond ((not (proof-string-match isar-undo-skip-regexp str))
                    (setq i 0)
                    (while (< i (length str))
                      (if (= (aref str i) proof-terminal-char)
                          (setq ct (+ 1 ct)))
                      (setq i (+ 1 i))))
                   (t nil))))
      (setq span (next-span span 'type)))
    (isar-undos ct)))

;; undo theory commands
(defun isar-find-and-forget (span)
  "Return commands to be used to forget SPAN."
  (let (str ans answers)
    (while span
      (setq str (span-property span 'cmd))
      (setq ans nil)
      (cond
       ;; comment or diagnostic command: skip
       ((or (eq (span-property span 'type) 'comment)
            (proof-string-match isar-undo-skip-regexp str)))
       ;; finished goal: undo
       ((eq (span-property span 'type) 'goalsave)
        (setq ans isar-undo))
       ;; open goal: skip and exit
       ((proof-string-match isar-goal-command-regexp str)
        (setq span nil))
       ;; not undoable: fail and exit
       ((proof-string-match isar-undo-fail-regexp str)
        (setq answers nil)
        (setq ans (isar-cannot-undo str))
        (setq span nil))
       ;; theory: remove and exit
       ((proof-string-match isar-undo-remove-regexp str)
        (setq ans (isar-remove (match-string 2 str)))
        (setq span nil))
       ;; context switch: kill
       ((proof-string-match isar-undo-kill-regexp str)
        (setq ans isar-kill))
       ;; else: undo
       (t
        (setq ans isar-undo)))
      (if ans (setq answers (cons ans answers)))
      (if span (setq span (next-span span 'type))))
    (if (null answers) proof-no-command (apply 'concat answers))))



(defun isar-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match isar-goal-command-regexp str))

(defun isar-global-save-command-p (span str)
  "Decide whether argument really is a global save command"
  (or
   (proof-string-match isar-global-save-command-regexp str)
   (let ((ans nil) (lev 0) cmd)
     (while (and (not ans) span (setq span (prev-span span 'type)))
       (setq cmd (span-property span 'cmd))
       (cond
        ;; comment: skip
        ((eq (span-property span 'type) 'comment))
        ;; local qed: enter block
        ((proof-string-match isar-save-command-regexp cmd)
         (setq lev (+ lev 1)))
        ;; local goal: leave block, or done
        ((proof-string-match isar-local-goal-command-regexp cmd)
         (if (> lev 0) (setq lev (- lev 1)) (setq ans 'no)))
        ;; global goal: done
        ((proof-string-match isar-goal-command-regexp cmd)
         (setq ans 'yes))))
     (eq ans 'yes))))

(defvar isar-current-goal 1
  "Last goal that emacs looked at.")

(defun isar-state-preserving-p (cmd)
  "Non-nil if command preserves the proofstate."
  (proof-string-match isar-undo-skip-regexp cmd))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to isar                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(proof-defshortcut isar-bold "\\<^bold>" [(control b)])
(proof-defshortcut isar-super "\\<^sup>" [(control u)])
(proof-defshortcut isar-sub "\\<^sub>"   [(control l)])



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Isar shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;borrowed from plastic.el
(defvar isar-shell-current-line-width nil
  "Current line width of the Isabelle process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;borrowed from plastic.el
(defun isar-shell-adjust-line-width ()
  "Use Isabelle's pretty printing facilities to adjust output line width.
   Checks the width in the `proof-goals-buffer'"
  (let ((ans ""))
    (and (buffer-live-p proof-goals-buffer)
         (proof-shell-live-buffer)
         (save-excursion
           (set-buffer proof-goals-buffer)
           (let ((current-width
                  ;; Actually, one might sometimes
                  ;; want to get the width of the proof-response-buffer
                  ;; instead. Never mind.
                  (max 20 (window-width (get-buffer-window proof-goals-buffer)))))

             (if (equal current-width isar-shell-current-line-width) ()
               (setq isar-shell-current-line-width current-width)
               (set-buffer proof-shell-buffer)
               (setq ans (format "pretty_setmargin %d;" (- current-width 4)))))))
    ans))

(defun isar-pre-shell-start ()
  (setq proof-prog-name         (isabelle-command-line))
  (setq proof-mode-for-shell    'isar-shell-mode)
  (setq proof-mode-for-goals    'isar-goals-mode)
  (setq proof-mode-for-response 'isar-response-mode))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof and pbp mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun isar-preprocessing ()  ;dynamic scoping of `string'
  "Insert sync markers - acts on variable STRING by dynamic scoping"
  (if (proof-string-match isabelle-verbatim-regexp string)
      (setq string (match-string 1 string))
    (unless (proof-string-match ";[ \t]*\\'" string)
      (setq string (concat string ";")))
    (setq string (concat
                  "\\<^sync>"
                  (isar-shell-adjust-line-width)
                  ;; da: this was an attempted hack to deal with ML files,
                  ;; unfortunately Isar complains about not seeing a theory
                  ;; command first: ML_setup illegal at first line
                  ;; Another failure is that: (* comment *) foo;
                  ;; ignores foo.  This could be fixed by scanning for
                  ;; comment end in proof-script.el's function
                  ;; proof-segment-upto-cmdstart (which becomes even more
                  ;; Isar specific, then...)
                  ;; (if (proof-string-match "\\.ML$" (buffer-name proof-script-buffer))
                  ;;    (format "ML_command {* %s *};" string)
                  ;;    string)
                  string
                  " \\<^sync>;"))))

(defun isar-mode-config ()
  (isar-mode-config-set-variables)
  (isar-init-syntax-table)
  (setq font-lock-keywords isar-font-lock-keywords-1)
  (proof-config-done)
  (set (make-local-variable 'outline-regexp) isar-outline-regexp)
  (set (make-local-variable 'outline-heading-end-regexp) isar-outline-heading-end-regexp)
  (setq blink-matching-paren-dont-ignore-comments t)
  (add-hook 'proof-pre-shell-start-hook 'isar-pre-shell-start nil t)
  (add-hook 'proof-shell-insert-hook 'isar-preprocessing))

(defun isar-shell-mode-config ()
  "Configure Proof General proof shell for Isabelle/Isar."
  (isar-init-output-syntax-table)
  (setq font-lock-keywords  ;FIXME handle x-symbol stuff by generic code!?
	(append isar-output-font-lock-keywords-1 x-symbol-isabelle-font-lock-keywords))
  (isar-shell-mode-config-set-variables)
  (proof-shell-config-done))

(defun isar-response-mode-config ()
  (setq font-lock-keywords  ;FIXME handle x-symbol stuff by generic code!?
	(append isar-output-font-lock-keywords-1 x-symbol-isabelle-font-lock-keywords))
  (isar-init-output-syntax-table)
  (proof-response-config-done))

(defun isar-goals-mode-config ()
  ;; FIXME: next two broken, of course, as is PBP everywhere except LEGO.
  (setq pbp-change-goal "Show %s.")
  (setq pbp-error-regexp proof-shell-error-regexp)
  (isar-init-output-syntax-table)
  (setq font-lock-keywords  ;FIXME handle x-symbol stuff by generic code!?
	(append isar-goals-font-lock-keywords x-symbol-isabelle-font-lock-keywords))
  (proof-goals-config-done))


;;
;; x-symbol support
;;
;; The following settings configure the generic PG package; the main
;; part is in isa/x-symbol-isabelle.el
;;

(setq
 proof-xsym-activate-command
 (isar-markup-ml "print_mode := ([\"xsymbols\",\"symbols\"] @ ! print_mode)")
 proof-xsym-deactivate-command
 (isar-markup-ml "print_mode := (Library.gen_rems (op =) (! print_mode, [\"xsymbols\",\"symbols\"]))"))


(provide 'isar)
