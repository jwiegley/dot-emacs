;;  ID:         $Id$
;;  Author:     David von Oheimb
;;  Copyright   1998 Technische Universitaet Muenchen
;;; token language "Isabelle Symbols" for package x-symbol

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
    (visiblespace () "\\\\<spacespace>")
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
    (semanticsleft () "\\\\<lbrakk>")
    (semanticsright () "\\\\<rbrakk>")
    (periodcentered () "\\\\<cdot>")
    (element () "\\\\<in>")
    (reflexsubset () "\\\\<subseteq>")
    (intersection () "\\\\<inter>")
    (union () "\\\\<union>")
    (bigintersection () "\\\\<Inter>")
    (bigunion () "\\\\<Union>")
    (sqintersection () "\\\\<sqinter>")
    (squnion () "\\\\<squnion>")
    (bigsqintersection () "\\\\<Sqinter>")
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
    (coloncolon () "\\\\<Colon>")
    (arrowleft () "\\\\<leftarrow>")
    (endash () "\\\\<midarrow>")
    (arrowright () "\\\\<rightarrow>")
    (arrowdblleft () "\\\\<Leftarrow>")
;   (rightleftharpoons () "\\\\<Midarrow>") ;missing symbol (but not necessary)
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
    (box () "\\\\<box>")
    (lozenge1 () "\\\\<diamond>")
    (circ () "\\\\<circ>")
    (bullet () "\\\\<bullet>")
    (bardbl () "\\\\<parallel>")
    (radical () "\\\\<surd>")
    (copyright () "\\\\<copyright>")
  ))
(defvar x-symbol-isa-xsymbol-table '(;;xsymbols
    (plusminus () "\\\\<plusminus>")
    (division () "\\\\<div>")
    (longarrowright () "\\\\<longrightarrow>")
    (longarrowleft  () "\\\\<longleftarrow>")
    (longarrowboth  () "\\\\<longleftrightarrow>")
    (longarrowdblright () "\\\\<Longrightarrow>")
    (longarrowdblleft  () "\\\\<Longleftarrow>")
    (longarrowdblboth  () "\\\\<Longleftrightarrow>")
    (brokenbar () "\\\\<brokenbar>")
    (hyphen () "\\\\<hyphen>")
    (macron () "\\\\<macron>")
    (exclamdown () "\\\\<exclamdown>")
    (questiondown () "\\\\<questiondown>")
    (guillemotleft () "\\\\<guillemotleft>")
    (guillemotright () "\\\\<guillemotright>")
    (degree () "\\\\<degree>")
    (onesuperior () "\\\\<onesuperior>")
    (onequarter () "\\\\<onequarter>")
    (twosuperior () "\\\\<twosuperior>")
    (onehalf () "\\\\<onehalf>")
    (threesuperior () "\\\\<threesuperior>")
    (threequarters () "\\\\<threequarters>")
    (paragraph () "\\\\<paragraph>")
    (registered () "\\\\<registered>")
    (ordfeminine () "\\\\<ordfeminine>")
    (ordmasculine () "\\\\<ordmasculine>")
    (section () "\\\\<section>")
    (pounds () "\\\\<pounds>")
    (yen () "\\\\<yen>")
    (cent () "\\\\<cent>")
    (currency () "\\\\<currency>")
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



;;;===========================================================================
;;;  useful key bindings
;;;===========================================================================

(global-set-key [(meta l)] 'x-symbol-INSERT-lambda)

(global-set-key [(meta n)] 'x-symbol-INSERT-notsign)
(global-set-key [(meta a)] 'x-symbol-INSERT-logicaland)
(global-set-key [(meta o)] 'x-symbol-INSERT-logicalor)
(global-set-key [(meta f)] 'x-symbol-INSERT-universal1)
(global-set-key [(meta t)] 'x-symbol-INSERT-existential1)

(global-set-key [(meta A)] 'x-symbol-INSERT-biglogicaland)
(global-set-key [(meta e)] 'x-symbol-INSERT-equivalence)
(global-set-key [(meta u)] 'x-symbol-INSERT-notequal)
(global-set-key [(meta m)] 'x-symbol-INSERT-arrowdblright)
(global-set-key [(meta x)] 'x-symbol-INSERT-multiply)

(global-set-key [(meta i)] 'x-symbol-INSERT-longarrowright)
