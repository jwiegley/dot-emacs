;; x-symbol-isa.el   token language "Isabelle Symbols" for package x-symbol
;;
;; Author:      David von Oheimb
;; Copyright    1998 Technische Universitaet Muenchen
;; Maintainer:  ??
;;
;; $Id$
;;

(provide 'x-symbol-isa)
(defvar x-symbol-isa-required-fonts nil)

;(defvar x-symbol-isa-name "Isabelle Symbol")
(defvar x-symbol-isa-modeline-name "isa")
(defvar x-symbol-isa-header-groups-alist nil)
;'(("Operator" bigop operator)
;    ("Relation" relation)
;    ("Arrow, Punctuation" arrow triangle shape
;     white line dots punctuation quote parenthesis)
;    ("Symbol" symbol currency mathletter setsymbol)
;    ("Greek Letter" greek greek1)
;    ("Acute, Grave" acute grave))
;  "*If non-nil, used in isasym specific grid/menu.

(defvar x-symbol-isa-class-alist
  '((VALID "Isabelle Symbol" (x-symbol-info-face))
    (INVALID "no Isabelle Symbol" (red x-symbol-info-face))))
(defvar x-symbol-isa-class-face-alist nil)
(defvar x-symbol-isa-electric-ignore nil)

(defvar x-symbol-isa-font-lock-keywords nil)
(defvar x-symbol-isa-master-directory  'ignore)
(defvar x-symbol-isa-image-searchpath '("./"))
(defvar x-symbol-isa-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-isa-image-file-truename-alist nil)
(defvar x-symbol-isa-image-keywords nil)

(defvar x-symbol-isa-case-insensitive nil)
;(defvar x-symbol-isa-token-shape '(?\\ "\\\\\\<[A-Za-z][A-Za-z0-9_']*>\\a'" . "[A-Za-z]"))
(defvar x-symbol-isa-token-shape nil)

(defvar x-symbol-isa-exec-specs '(nil ("\\`\\\\<[A-Za-z][A-Za-z0-9_']*>\\'" . 
				          "\\\\<[A-Za-z][A-Za-z0-9_']*>")))

(defvar x-symbol-isa-input-token-ignore nil)
(defun x-symbol-isa-default-token-list (tokens) tokens)


(defvar x-symbol-isa-token-list 'x-symbol-isa-default-token-list)

(defvar x-symbol-isa-symbol-table '(;;symbols (isabelle14 font)
    (visiblespace () "\\\\<space2>")
    (Gamma () "\\\\<Gamma>")
    (Delta () "\\\\<Delta>")
    (Theta () "\\\\<Theta>")
    (Lambda () "\\\\<Lambda>")
    (Pi () "\\\\<Pi>")
    (Sigma () "\\\\<Sigma>")
    (Phi () "\\\\<Phi>")
    (Psi () "\\\\<Psi>")
    (Omega () "\\\\<Omega>")
    (alpha () "\\\\<alpha>")
    (beta () "\\\\<beta>")
    (gamma () "\\\\<gamma>")
    (delta () "\\\\<delta>")
    (epsilon1 () "\\\\<epsilon>")
    (zeta () "\\\\<zeta>")
    (eta () "\\\\<eta>")
    (theta1 () "\\\\<theta>")
    (kappa1 () "\\\\<kappa>")
    (lambda () "\\\\<lambda>")
    (mu () "\\\\<mu>")
    (nu () "\\\\<nu>")
    (xi () "\\\\<xi>")
    (pi () "\\\\<pi>")
    (rho () "\\\\<rho>")
    (sigma () "\\\\<sigma>")
    (tau () "\\\\<tau>")
    (phi1 () "\\\\<phi>")
    (chi () "\\\\<chi>")
    (psi () "\\\\<psi>")
    (omega () "\\\\<omega>")
    (notsign () "\\\\<not>")
    (logicaland () "\\\\<and>")
    (logicalor () "\\\\<or>")
    (universal1 () "\\\\<forall>")
    (existential1 () "\\\\<exists>")
    (biglogicaland () "\\\\<And>")
    (ceilingleft () "\\\\<lceil>")
    (ceilingright () "\\\\<rceil>")
    (floorleft () "\\\\<lfloor>")
    (floorright () "\\\\<rfloor>")
    (bardash () "\\\\<turnstile>")
    (bardashdbl () "\\\\<Turnstile>")
    (braceleft2 () "\\\\<lbrakk>") ;##missing symbol
    (braceright2 () "\\\\<rbrakk>") ;##missing symbol
    (periodcentered () "\\\\<cdot>")
    (element () "\\\\<in>")
    (reflexsubset () "\\\\<subseteq>")
    (intersection () "\\\\<inter>")
    (union () "\\\\<union>")
    (bigintersection () "\\\\<Inter>")
    (bigunion () "\\\\<Union>")
    (sqintersection () "\\\\<sqinter>")
    (squnion () "\\\\<squnion>")
;   (??????? () "\\\\<Sqinter>") ;##missing symbol
    (bigsqunion () "\\\\<Squnion>")
    (perpendicular1 () "\\\\<bottom>")
    (dotequal () "\\\\<doteq>")
    (equivalence () "\\\\<equiv>")
    (notequal () "\\\\<noteq>")
    (propersqsubset () "\\\\<sqsubset>")
    (reflexsqsubset () "\\\\<sqsubseteq>")
    (properprec () "\\\\<prec>")
    (reflexprec () "\\\\<preceq>")
    (propersucc () "\\\\<succ>")
    (approxequal () "\\\\<approx>")
    (similar () "\\\\<sim>")
    (simequal () "\\\\<simeq>")
    (lessequal () "\\\\<le>")
    (therefore1 () "\\\\<Colon>") ;##missing symbol
    (arrowleft () "\\\\<leftarrow>")
    (endash () "\\\\<midarrow>")
    (arrowright () "\\\\<rightarrow>")
    (arrowdblleft () "\\\\<Leftarrow>")
    (rightleftharpoons () "\\\\<Midarrow>") ;##missing symbol (unnecessary)
    (arrowdblright () "\\\\<Rightarrow>")
    (frown () "\\\\<bow>")
    (mapsto () "\\\\<mapsto>")
    (leadsto () "\\\\<leadsto>")
    (arrowup () "\\\\<up>")
    (arrowdown () "\\\\<down>")
    (notelement () "\\\\<notin>")
    (multiply () "\\\\<times>")
    (circleplus () "\\\\<oplus>")
    (circleminus () "\\\\<ominus>")
    (circlemultiply () "\\\\<otimes>")
    (circleslash () "\\\\<oslash>")
    (propersubset () "\\\\<subset>")
    (infinity () "\\\\<infinity>")
    (box () "\\\\<box>") ;##too big
    (smllozenge () "\\\\<diamond>") ;##too small
    (circ () "\\\\<circ>")
    (bullet () "\\\\<bullet>")
    (bardbl () "\\\\<parallel>")
    (radical () "\\\\<surd>")
    (copyright () "\\\\<copyright>")
  ))
(defvar x-symbol-isa-xsymbol-table '(;;xsymbols
    (longarrowright () "\\\\<longrightarrow>")
    (longarrowleft  () "\\\\<longleftarrow>")
    (longarrowboth  () "\\\\<longleftrightarrow>")
    (longarrowdblright () "\\\\<Longrightarrow>")
    (longarrowdblleft  () "\\\\<Longleftarrow>")
    (longarrowdblboth  () "\\\\<Longleftrightarrow>")
  ))
(defvar x-symbol-isa-user-table nil)
(defvar x-symbol-isa-table
  (append x-symbol-isa-user-table 
	  (append x-symbol-isa-symbol-table x-symbol-isa-xsymbol-table)))

;;;===========================================================================
;;;  Internal
;;;===========================================================================

(defvar x-symbol-isa-menu-alist nil
  "Internal.  Alist used for Isasym specific menu.")
(defvar x-symbol-isa-grid-alist nil
  "Internal.  Alist used for Isasym specific grid.")

(defvar x-symbol-isa-decode-atree nil
  "Internal.  Atree used by `x-symbol-token-input'.")
(defvar x-symbol-isa-decode-alist nil
  "Internal.  Alist used for decoding of Isasym macros.")
(defvar x-symbol-isa-encode-alist nil
  "Internal.  Alist used for encoding to Isasym macros.")

(defvar x-symbol-isa-nomule-decode-exec nil
  "Internal.  File name of Isasym decode executable.")
(defvar x-symbol-isa-nomule-encode-exec nil
  "Internal.  File name of Isasym encode executable.")





