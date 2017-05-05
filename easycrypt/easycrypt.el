;; --------------------------------------------------------------------
;; Copyright (c) - 2012--2016 - IMDEA Software Institute
;; Copyright (c) - 2012--2016 - Inria
;;
;; Distributed under the terms of the GPL-v3 license
;; --------------------------------------------------------------------

(require 'proof)
(require 'easycrypt-syntax)
(require 'easycrypt-hooks)
(require 'easycrypt-abbrev)

(add-to-list 'hs-special-modes-alist
  '(easycrypt-mode "{" "}" "/[*/]" nil nil))

;; --------------------------------------------------------------------
(defun easycrypt-load-path-safep (path)
  (and
   (listp path)
   (every (lambda (entry) (stringp entry)) path)))

;; --------------------------------------------------------------------
(defcustom easycrypt-prog-name "easycrypt"
  "*Name of program to run EasyCrypt."
  :type  'file
  :group 'easycrypt)

(defcustom easycrypt-load-path nil
  "Non-standard EasyCrypt library load path.
This list specifies the include path for EasyCrypt. The elements of
this list are strings."
  :type  '(repeat (string :tag "simple directory (-I)"))
  :safe  'easycrypt-load-path-safep
  :group 'easycrypt)

(defcustom easycrypt-web-page
  "http://www.easycrypt.info/"
  "URL of web page for EasyCrypt."
  :type  'string
  :group 'easycrypt-config)

;; --------------------------------------------------------------------
(defun easycrypt-option-of-load-path-entry (entry)
  (list "-I" (expand-file-name entry)))

;; --------------------------------------------------------------------
(defun easycrypt-include-options ()
  (let ((result nil))
    (when easycrypt-load-path
      (dolist (entry easycrypt-load-path)
        (setq result (append result (easycrypt-option-of-load-path-entry entry)))))
    result))

;; --------------------------------------------------------------------
(defun easycrypt-build-prog-args ()
  (delete "-emacs" easycrypt-prog-args)
  (push "-emacs" easycrypt-prog-args))

(easycrypt-build-prog-args)

;; --------------------------------------------------------------------
(defun easycrypt-prog-args ()
  (append easycrypt-prog-args (easycrypt-include-options)))

;; --------------------------------------------------------------------
;; Generic mode

(defun easycrypt-config ()
  "Configure Proof General scripting for EasyCrypt."
  (easycrypt-init-output-syntax-table)
  
  (setq  proof-terminal-string                 easycrypt-terminal-string)
  (setq  proof-script-command-end-regexp       easycrypt-command-end-regexp)

  (setq  proof-script-comment-start            "(*"
         proof-script-comment-end              "*)")
  
  ;; For undo
  (setq  proof-find-and-forget-fn              'easycrypt-find-and-forget
         proof-completed-proof-behaviour       nil
         proof-non-undoables-regexp            easycrypt-non-undoables-regexp
         proof-shell-restart-cmd               "pragma restart. ")

  (set (make-local-variable 'comment-quote-nested) nil)

  ;; For func-menu and finding goal...save regions
  (setq  proof-save-command-regexp             easycrypt-proof-save-regexp
         proof-really-save-command-p           'easycrypt-save-command-p
         proof-save-with-hole-regexp           nil
         proof-goal-command-p                  'easycrypt-goal-command-p
         proof-goal-with-hole-regexp           easycrypt-goal-command-regexp
         proof-goal-with-hole-result           1)

  (setq  proof-goal-command                    "lemma %s: ."
         proof-save-command                    "qed.")
  
  (setq  proof-prog-name                       easycrypt-prog-name
         proof-assistant-home-page             easycrypt-web-page)

  ; Options
  (setq  proof-three-window-enable             t
         proof-three-window-mode-policy        (quote hybrid)
         proof-auto-multiple-files             t)

  ; Setting indents 
  (set   (make-local-variable 'indent-tabs-mode) nil)
  (setq  proof-indent-enclose-offset   (- proof-indent)
         proof-indent-open-offset     0
         proof-indent-close-offset    0
         proof-indent-any-regexp      easycrypt-indent-any-regexp
         proof-indent-enclose-regexp  easycrypt-indent-enclose-regexp
         proof-indent-open-regexp     easycrypt-indent-open-regexp
         proof-indent-close-regexp    easycrypt-indent-close-regexp)

  ; Silent/verbose mode for batch processing
  (setq proof-shell-start-silent-cmd "pragma silent. "
        proof-shell-stop-silent-cmd  "pragma verbose. ")

  ; Ask for the current goal
  (setq proof-showproof-command "pragma noop. ")

  (easycrypt-init-syntax-table)
  ;; we can cope with nested comments
  (set (make-local-variable 'comment-quote-nested) nil)

  (setq  proof-script-font-lock-keywords
         easycrypt-font-lock-keywords))

(defun easycrypt-shell-config ()
  "Configure Proof General shell for EasyCrypt."
  (easycrypt-init-output-syntax-table)
  (setq  proof-shell-auto-terminate-commands    easycrypt-terminal-string)
  (setq  proof-shell-eager-annotation-start
     (concat "\\(?:^\\[W\\] *\\)\\|\\(?:" easycrypt-shell-proof-completed-regexp "\\)"))
  (setq  proof-shell-strip-crs-from-input       nil)
  (setq  proof-shell-annotated-prompt-regexp    "^\\[[0-9]+|\\sw+\\]>")
  (setq  proof-shell-clear-goals-regexp         easycrypt-shell-proof-completed-regexp)
  (setq  proof-shell-proof-completed-regexp     easycrypt-shell-proof-completed-regexp)
  (setq  proof-shell-error-regexp               easycrypt-error-regexp)
  (setq  proof-shell-truncate-before-error      nil)
  (setq  proof-shell-start-goals-regexp         "^Current")
  (setq  proof-shell-end-goals-regexp           nil)  ; up to next prompt
  (setq  proof-shell-font-lock-keywords         easycrypt-font-lock-keywords))

;; --------------------------------------------------------------------
;; Derived modes

(define-derived-mode easycrypt-mode proof-mode
  "EasyCrypt script" nil
  (easycrypt-config)
  (proof-config-done))

(define-derived-mode easycrypt-shell-mode proof-shell-mode
  "EasyCrypt shell" nil
  (easycrypt-shell-config)
  (proof-shell-config-done))

(define-derived-mode easycrypt-response-mode proof-response-mode
  "EasyCrypt response" nil
  (easycrypt-init-output-syntax-table)
  (setq  proof-response-font-lock-keywords 
         easycrypt-font-lock-keywords)
  (proof-response-config-done))

(define-derived-mode easycrypt-goals-mode proof-goals-mode
  "EasyCrypt goals" nil
  (easycrypt-init-output-syntax-table)
  (setq  proof-goals-font-lock-keywords 
         easycrypt-font-lock-keywords)
  (proof-goals-config-done))

(defun easycrypt-get-last-error-location () 
  "Remove [error] in the error message and extract the position
  and length of the error "
  (proof-with-current-buffer-if-exists proof-response-buffer

     (goto-char (point-max))
     (when (re-search-backward "\\[error-\\([0-9]+\\)-\\([0-9]+\\)\\]" nil t)
        (let* ((inhibit-read-only t)
               (pos1 (string-to-number (match-string 1)))
               (pos2 (string-to-number (match-string 2)))
               (len (- pos2 pos1)))

              (delete-region (match-beginning 0) (match-end 0))
              (list pos1 len)))))

(defun easycrypt-advance-until-command ()
   (while (proof-looking-at "\\s-") (forward-char 1)))

(defun easycrypt-highlight-error ()
  "Use 'easycrypt-get-last-error-location' to know the position
  of the error and then highlight in the script buffer"
  (proof-with-current-buffer-if-exists proof-script-buffer
    (let ((mtch (easycrypt-get-last-error-location)))
        (when mtch
          (let ((pos (car mtch))
                  (lgth (cadr mtch)))
          (if (eq (proof-unprocessed-begin) (point-min))
                (goto-char (proof-unprocessed-begin))
                (goto-char (+ (proof-unprocessed-begin) 1)))
            (easycrypt-advance-until-command)
             (goto-char (+ (point) pos))
             (span-make-self-removing-span
               (point) (+ (point) lgth)
               'face 'proof-script-highlight-error-face))))))

(defun easycrypt-highlight-error-hook ()
  (easycrypt-highlight-error))

(defun easycrypt-redisplay-hook ()
  (easycrypt-redisplay))

(add-hook 'proof-shell-handle-error-or-interrupt-hook
          'easycrypt-highlight-error-hook t)

;; --------------------------------------------------------------------
;; Check mode related commands
(defun easycrypt-cmode-check ()
  "Set EasyCrypt in check mode."
  (interactive)
  (proof-shell-invisible-command "pragma Proofs:check."))

(defun easycrypt-cmode-weak-check ()
  "Set EasyCrypt in weak-check mode."
  (interactive)
  (proof-shell-invisible-command "pragma Proofs:weak."))

;; --------------------------------------------------------------------
(defun easycrypt-ask-do (do)
  (let* ((cmd))
    (setq cmd (read-string (format "Term for `%s': " do)))
    (proof-shell-ready-prover)
    (proof-shell-invisible-command (format " %s %s . " do cmd))))

;; --------------------------------------------------------------------
(defun easycrypt-Print ()
  "Ask for a term and print its type."
  (interactive)
  (easycrypt-ask-do "print"))

;; --------------------------------------------------------------------
(defun easycrypt-Check ()
  (easycrypt-Print))

;; --------------------------------------------------------------------
;; Key bindings

(define-key easycrypt-keymap "\C-p" 'easycrypt-Print)
(define-key easycrypt-goals-mode-map "\C-c\C-a\C-p" 'easycrypt-Print)
(define-key easycrypt-response-mode-map "\C-c\C-a\C-p" 'easycrypt-Print)

(define-key easycrypt-keymap "\C-c" 'easycrypt-Check)
(define-key easycrypt-goals-mode-map "\C-c\C-a\C-c" 'easycrypt-Check)
(define-key easycrypt-response-mode-map "\C-c\C-a\C-c" 'easycrypt-Check)

;; --------------------------------------------------------------------
;; 3-window pane layout hack
(add-hook
  'proof-activate-scripting-hook
  '(lambda () (when proof-three-window-enable (proof-layout-windows))))

;; --------------------------------------------------------------------
(provide 'easycrypt)
