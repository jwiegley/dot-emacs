;; isar-syntax.el Syntax expressions for Isabelle/Isar
;; Copyright (C) 1994-1998 LFCS Edinburgh. 
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Markus Wenzel <wenzelm@in.tum.de>
;;
;; $Id$
;;

(require 'proof-syntax)
(require 'isar-keywords)

;;; Proof mode customization: how should it work?
;;;   Presently we have a bunch of variables in proof.el which are
;;;   set from a bunch of similarly named variables in <engine>-syntax.el.
;;;
;;;   Seems a bit daft: why not just have the customization in
;;;   one place, and settings hardwired in <engine>-syntax.el.
;;;
;;;   That way we can see which settings are part of instantiation of
;;;   proof.el, and which are part of cusomization for <engine>.

;; ------ customize groups

;(defgroup isar-scripting nil
;  "Customization of Isabelle/Isar script management"
;  :group 'external
;  :group 'languages)

;(defgroup isar-syntax nil
;  "Customization of Isabelle/Isar's syntax recognition"
;  :group 'isar-scripting)


;; ----- character syntax

(defun isar-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
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
  (modify-syntax-entry ?.  "w")
  (modify-syntax-entry ?_  "w")
  (modify-syntax-entry ?\' "w")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4")
  (modify-syntax-entry ?\{ "(}1")
  (modify-syntax-entry ?\} "){4"))

(defun isar-init-output-syntax-table ()
  "Set appropriate values for syntax table for Isabelle output."
  (isar-init-syntax-table)
  ;; ignore strings so font-locking works
  ;; inside them
  (modify-syntax-entry ?\" " "))


;; ----- syntax for font-lock and other features

(defconst isar-keywords-theory-enclose
  (append isar-keywords-theory-begin
	  isar-keywords-theory-switch
	  isar-keywords-theory-end))

(defconst isar-keywords-theory
  (append isar-keywords-theory-heading
	  isar-keywords-theory-decl
	  isar-keywords-theory-goal))

(defconst isar-keywords-save
  (append isar-keywords-qed
	  isar-keywords-qed-block
	  isar-keywords-qed-global))

(defconst isar-keywords-proof-enclose
  (append isar-keywords-proof-block
	  isar-keywords-qed-block))

(defconst isar-keywords-proof
  (append isar-keywords-proof-goal
	  isar-keywords-proof-chain
	  isar-keywords-proof-decl
	  isar-keywords-qed))

(defconst isar-keywords-proof-context
  (append isar-keywords-proof-asm
	  isar-keywords-proof-asm-goal))

(defconst isar-keywords-local-goal
  (append isar-keywords-proof-goal
	  isar-keywords-proof-asm-goal))

(defconst isar-keywords-proof-improper
  (append isar-keywords-proof-script
	  isar-keywords-qed-global))

(defconst isar-keywords-outline
  (append isar-keywords-theory-begin
	  isar-keywords-theory-heading
	  isar-keywords-theory-goal))

(defconst isar-keywords-indent
  (append isar-keywords-theory-heading
	  isar-keywords-theory-decl
	  isar-keywords-proof-block
	  isar-keywords-proof-decl
	  isar-keywords-proof-asm
	  isar-keywords-proof-script))

(defconst isar-keywords-indent-open
  (append isar-keywords-theory-goal
	  isar-keywords-proof-goal
	  isar-keywords-proof-asm-goal))

(defconst isar-keywords-indent-close
  (append isar-keywords-save))

(defconst isar-keywords-indent-enclose
  (append isar-keywords-proof-block
	  isar-keywords-qed-block))

(defconst isar-keywords-indent-reset
  (append isar-keywords-theory-begin
	  isar-keywords-theory-switch
	  isar-keywords-theory-end
	  isar-keywords-theory-heading
	  isar-keywords-theory-decl
	  isar-keywords-qed-global))


;; ----- regular expressions

;; tuned version of proof-ids-to-regexp --- admit single non-word char
;; as well (e.g. { })

(defun isar-ids-to-regexp (l)
  "Maps a non-empty list of tokens `l' to a regexp matching any element"
  (mapconcat
   (lambda (s) (if (string-match "^\\W$" s) s (concat "\\<" s "\\>")))
   l "\\|"))

(defconst isar-id "\\([A-Za-z][A-Za-z0-9'_]*\\)")
(defconst isar-idx (concat isar-id "\\(\\.[0-9]+\\)?"))

(defconst isar-string "\"\\(\\([^\\\"]\\|\\\\\"\\)*\\)\"")

(defconst isar-name-regexp
  (concat "\\s-*\\(" isar-string "\\|" isar-id "\\)\\s-*")
  "Regexp matching Isabelle/Isar names, with contents grouped.")

(defconst isar-tac-regexp
  "\\<[A-Za-z][A-Za-z0-9'_]*_tac\\>"
  "Regexp matching old-style tactic names")

(defconst isar-save-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-save)))

(defconst isar-global-save-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-qed-global)))

(defconst isar-save-with-hole-regexp "$^") ; n.a.

(defconst isar-goal-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-goal)))

(defconst isar-local-goal-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-local-goal)))

(defconst isar-goal-with-hole-regexp
  (concat "\\(" (isar-ids-to-regexp isar-keywords-theory-goal) "\\)" isar-name-regexp ":")
  "Regexp matching goal commands in Isabelle/Isar which name a theorem")

(defconst isar-verbatim-regexp "^\^VERBATIM: \\(\\(.\\|\n\\)*\\)$"
  "Regexp matching internal marker for verbatim command output")

(defun isar-verbatim (str)
  "Mark internal command for verbatim output"
  (concat "\^VERBATIM: " str))


;; ----- Isabelle inner syntax hilite

(defface isabelle-class-name-face
  '((((type x) (class color) (background light))   
     (:foreground "red"))
    (((type x) (class color) (background dark))   
     (:foreground "red3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-tfree-name-face
  '((((type x) (class color) (background light))   
     (:foreground "purple"))
    (((type x) (class color) (background dark))   
     (:foreground "purple3"))
    (t
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-tvar-name-face
  '((((type x) (class color) (background light))   
     (:foreground "purple"))
    (((type x) (class color) (background dark))   
     (:foreground "purple3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-free-name-face
  '((((type x) (class color) (background light))   
     (:foreground "blue"))
    (((type x) (class color) (background dark))   
     (:foreground "blue3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-bound-name-face
  '((((type x) (class color) (background light))   
     (:foreground "green4"))
    (((type x) (class color) (background dark))   
     (:foreground "green"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defface isabelle-var-name-face
  '((((type x) (class color) (background light))   
     (:foreground "darkblue"))
    (((type x) (class color) (background dark))   
     (:foreground "blue3"))
    (t				
     (bold t)))
  "*Face for Isabelle term / type hiliting"
  :group 'proof-faces)

(defconst isabelle-class-name-face 'isabelle-class-name-face)
(defconst isabelle-tfree-name-face 'isabelle-tfree-name-face)
(defconst isabelle-tvar-name-face 'isabelle-tvar-name-face)
(defconst isabelle-free-name-face 'isabelle-free-name-face)
(defconst isabelle-bound-name-face 'isabelle-bound-name-face)
(defconst isabelle-var-name-face 'isabelle-var-name-face)


(defvar isar-font-lock-keywords-1
  (list
   (cons (isar-ids-to-regexp isar-keywords-minor)          'font-lock-type-face)
   (cons (isar-ids-to-regexp isar-keywords-control)        'proof-error-face)
   (cons (isar-ids-to-regexp isar-keywords-diag)           'proof-tacticals-name-face)
   (cons (isar-ids-to-regexp isar-keywords-theory-enclose) 'font-lock-preprocessor-face)
   (cons (isar-ids-to-regexp isar-keywords-theory)         'font-lock-keyword-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-enclose)  'font-lock-preprocessor-face)
   (cons (isar-ids-to-regexp isar-keywords-proof)          'font-lock-keyword-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-context)  'proof-declaration-name-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-improper) 'font-lock-reference-face)
   (cons isar-tac-regexp 'font-lock-reference-face)))

(defvar isar-output-font-lock-keywords-1
  (list
   (cons (concat "\351" isar-id "\350") 'isabelle-class-name-face)
   (cons (concat "\352'" isar-id "\350") 'isabelle-tfree-name-face)
   (cons (concat "\353\\?'" isar-idx "\350") 'isabelle-tvar-name-face)
   (cons (concat "\354" isar-id "\350") 'isabelle-free-name-face)
   (cons (concat "\355" isar-id "\350") 'isabelle-bound-name-face)
   (cons (concat "\356\\?" isar-idx "\350") 'isabelle-var-name-face)
   (cons (concat "\357" isar-id "\350") 'proof-declaration-name-face)
   (cons (concat "\357\\?" isar-idx "\350") 'proof-declaration-name-face)
   )
  "*Font-lock table for Isabelle terms.")


;; ----- variations on undo

(defconst isar-undo "undo;")
(defconst isar-kill "kill;")

(defun isar-remove (name)
  (concat "init_toplevel; kill_thy \"" name "\";"))

(defun isar-undos (i)
  (if (> i 0) (concat "undos_proof " (int-to-string i) ";")
    proof-no-command))

(defun isar-cannot-undo (cmd)
  (concat "cannot_undo \"" cmd "\";"))


(defconst isar-undo-fail-regexp
  (proof-anchor-regexp
   (isar-ids-to-regexp (append isar-keywords-control isar-keywords-theory-end))))

(defconst isar-undo-skip-regexp
  (proof-anchor-regexp (concat ";\\|" (isar-ids-to-regexp isar-keywords-diag))))

(defconst isar-undo-remove-regexp
  (concat
   (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-begin))
   isar-name-regexp))

(defconst isar-undo-kill-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-switch)))


;; ----- indentation

(defconst isar-indent-regexp (isar-ids-to-regexp isar-keywords-indent))
(defconst isar-indent-open-regexp (isar-ids-to-regexp isar-keywords-indent-open))
(defconst isar-indent-close-regexp (isar-ids-to-regexp isar-keywords-indent-close))
(defconst isar-indent-enclose-regexp (isar-ids-to-regexp isar-keywords-indent-enclose))
(defconst isar-indent-reset-regexp (isar-ids-to-regexp isar-keywords-indent-reset))


(provide 'isar-syntax)
