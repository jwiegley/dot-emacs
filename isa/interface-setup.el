;;
;; $Id$
;;

(let ((xsymbol (getenv "PROOFGENERAL_XSYMBOL")))
  (if (and xsymbol (not (equal xsymbol "")))
      (customize-set-variable
       (if (equal (getenv "PROOFGENERAL_ASSISTANTS") "isa")
           'isa-x-symbol-enable
         'isar-x-symbol-enable)
       (equal xsymbol "true"))))
