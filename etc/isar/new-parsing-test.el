;; 
;; Temporary test for new code in proof-done-advancing, following
;; Markus's suggestions in proof-config  
;; [see doc of proof-really-save-command-p]
;; 
;; Not integrated yet for fear of destruction of finely tuned 
;; PG/Isar instance.
;; 
;;  -da  June 02.
;; 
;; FIXME: the handling of nesting depth counter doesn't yet work
;; smoothly in the generic code, especially across undos/forget.
;; Need to fix when nesting depth is changed, how it is changed,
;; and choice of kill_proof vs undos for Isar.
;;
;; Testing: evaluate this buffer, reload script file 
;; (to re-execute isar-mode).

(setq proof-nested-goals-p t)
(setq proof-goal-command-regexp 
      (concat isar-goal-command-regexp "\\|" isar-local-goal-command-regexp))

(defun isar-goal-command-p (str)
  "Decide whether argument is a goal or not"
  (proof-string-match proof-goal-command-regexp str))

;; Reset this to default value
(setq proof-really-save-command-p (lambda (span cmd) t))

;; Use the new parser, but have to hack the keywords setting
;; to fix prob with "{"  
;; [do we??  that was probably buffer-syntactic context/symtab problem]
(setq proof-script-use-old-parser nil)
(setq isar-any-command-regexp
      (isar-ids-to-regexp isar-keywords-major))
;      (cons "{[^\\*]"  ;; FIXME:
;	    (isar-ids-to-regexp 
;	     (remove "{" isar-keywords-major))))
