;;
;; $Id$
;; 

(customize-set-variable
 'isabelle-isar-prog-name
 (concat (getenv "ISABELLE") " " (getenv "PROOFGENERAL_LOGIC")))

(let ((xsym (getenv "PROOFGENERAL_XSYMBOL")))
  (cond
   ((equal xsym "true")
    (customize-set-variable 'proof-x-symbol-enable t))
   ((equal xsym "false")
    (customize-set-variable 'proof-x-symbol-enable nil))))
