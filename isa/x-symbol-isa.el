;; Canonical file for token language file for PG/isar.

(require 'x-symbol-isabelle)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; x-symbol support for Isabelle PG, provided by David von Oheimb.
;;
;; The following settings configure the generic PG package.
;; The token language "Isabelle Symbols" is in file x-symbol-isabelle.el
;;

(setq proof-xsym-extra-modes '(thy-mode)
      proof-xsym-activate-command
      "print_mode := ([\"xsymbols\", \"symbols\"] @ ! print_mode);"
      proof-xsym-deactivate-command
      "print_mode := (! print_mode \\\\ [\"xsymbols\", \"symbols\"]);")



(provide 'x-symbol-isa)
