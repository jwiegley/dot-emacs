;;  ID:         $Id$
;;  Author:     David von Oheimb
;;  Copyright   1998 Technische Universitaet Muenchen
;;  token language "Isabelle Symbols" for package x-symbol
;;
;; NB: Part of Proof General distribution.
;;

(defvar x-symbol-isabelle-required-fonts nil)

;; FIXME da: these next two are also set in proof-x-symbol.el, but
;; it's handy to use this file away from PG.  In future could
;; fix things so just (require 'proof-x-symbol) would be enough
;; here.
(defvar x-symbol-isabelle-name "Isabelle Symbol")
(defvar x-symbol-isabelle-modeline-name "isa")

(defvar x-symbol-isabelle-header-groups-alist nil)
;'(("Operator" bigop operator)
;    ("Relation" relation)
;    ("Arrow, Punctuation" arrow triangle shape
;     white line dots punctuation quote parenthesis)
;    ("Symbol" symbol currency mathletter setsymbol)
;    ("Greek Letter" greek greek1)
;    ("Acute, Grave" acute grave))
;  "*If non-nil, used in isasym specific grid/menu."

(defvar x-symbol-isabelle-class-alist
  '((VALID "Isabelle Symbol" (x-symbol-info-face))
    (INVALID "no Isabelle Symbol" (red x-symbol-info-face))))
(defvar x-symbol-isabelle-class-face-alist nil)
(defvar x-symbol-isabelle-electric-ignore "[:'][A-Za-z]\\|<=\\|\\[\\[\\|\\]\\]\\|~=")


;;  Bold, super- and subscripts

(defun x-symbol-isabelle-make-ctrl-regexp (s)
  (concat "\\(\\\\?\\\\<\\^" s ">\\)\\(\\\\?\\\\<[A-Za-z][A-Za-z0-9_']*>\\|[^\\]\\)"))

(defconst x-symbol-isabelle-font-lock-bold-regexp
  (x-symbol-isabelle-make-ctrl-regexp "bold")
  "Regexp matching bold marker in Isabelle.")

(defconst x-symbol-isabelle-font-lock-scripts-regexp
  (x-symbol-isabelle-make-ctrl-regexp "su[bp]")
  "Regexp matching super- and subscript markers in Isabelle.")

(defun x-symbol-isabelle-match-bold (limit)
  ;; checkdoc-params: (limit)
  "Match and skip over bold face.
Return nil if `x-symbol-mode' is nil.
Uses `x-symbol-isabelle-font-lock-bold-regexp'."
  (and (proof-ass x-symbol-enable)
       (or (proof-looking-at x-symbol-isabelle-font-lock-bold-regexp)
	   (proof-re-search-forward x-symbol-isabelle-font-lock-bold-regexp limit t))))

(defun x-symbol-isabelle-match-scripts (limit)
  ;; checkdoc-params: (limit)
  "Match and skip over super- and subscripts.
Return nil if `x-symbol-mode' is nil.
Uses `x-symbol-isabelle-font-lock-scripts-regexp'."
  (and (proof-ass x-symbol-enable)
       (or (proof-looking-at x-symbol-isabelle-font-lock-scripts-regexp)
	   (proof-re-search-forward x-symbol-isabelle-font-lock-scripts-regexp limit t))))

(defvar x-symbol-isabelle-font-lock-keywords
  '((x-symbol-isabelle-match-bold
     (1 x-symbol-invisible-face t)
     (2	'underline prepend))
    (x-symbol-isabelle-match-scripts
     (1 x-symbol-invisible-face t)
     (2	(if (or (eq (char-after (+ 5 (match-beginning 1))) ?b)
		(eq (char-after (+ 6 (match-beginning 1))) ?b))
	    'x-symbol-sub-face 'x-symbol-sup-face) prepend)))
  "Isabelle font-lock keywords for bold, super- and subscripts.")


(defvar x-symbol-isabelle-master-directory  'ignore)
(defvar x-symbol-isabelle-image-searchpath '("./"))
(defvar x-symbol-isabelle-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-isabelle-image-file-truename-alist nil)
(defvar x-symbol-isabelle-image-keywords nil)

(defvar x-symbol-isabelle-case-insensitive nil)
;(defvar x-symbol-isabelle-token-shape '(?\\ "\\\\\\<[A-Za-z][A-Za-z0-9_']*>\\a'" . "[A-Za-z]"))
(defvar x-symbol-isabelle-token-shape nil)

(defvar x-symbol-isabelle-exec-specs '(nil ("\\`\\\\<[A-Za-z][A-Za-z0-9_']*>\\'" .
                                          "\\\\<[A-Za-z][A-Za-z0-9_']*>")))

(defvar x-symbol-isabelle-input-token-ignore nil)
(defun x-symbol-isabelle-default-token-list (tokens) tokens)


(defvar x-symbol-isabelle-token-list 'x-symbol-isabelle-default-token-list)

(defvar x-symbol-isabelle-symbol-table      ; symbols (isabelle font)
  '((visiblespace "\\<spacespace>")
    (Gamma "\\<Gamma>")
    (Delta "\\<Delta>")
    (Theta "\\<Theta>")
    (Lambda "\\<Lambda>")
    (Pi "\\<Pi>")
    (Sigma "\\<Sigma>")
    (Phi "\\<Phi>")
    (Psi "\\<Psi>")
    (Omega "\\<Omega>")
    (alpha "\\<alpha>")
    (beta "\\<beta>")
    (gamma "\\<gamma>")
    (delta "\\<delta>")
    (epsilon1 "\\<epsilon>")
    (zeta "\\<zeta>")
    (eta "\\<eta>")
    (theta "\\<theta>")
    (kappa1 "\\<kappa>")
    (lambda "\\<lambda>")
    (mu "\\<mu>")
    (nu "\\<nu>")
    (xi "\\<xi>")
    (pi "\\<pi>")
    (rho1 "\\<rho>")
    (sigma "\\<sigma>")
    (tau "\\<tau>")
    (phi1 "\\<phi>")
    (chi "\\<chi>")
    (psi "\\<psi>")
    (omega "\\<omega>")
    (notsign "\\<not>")
    (logicaland "\\<and>")
    (logicalor "\\<or>")
    (universal1 "\\<forall>")
    (existential1 "\\<exists>")
    (biglogicaland "\\<And>")
    (ceilingleft "\\<lceil>")
    (ceilingright "\\<rceil>")
    (floorleft "\\<lfloor>")
    (floorright "\\<rfloor>")
    (bardash "\\<turnstile>")
    (bardashdbl "\\<Turnstile>")
    (semanticsleft "\\<lbrakk>")
    (semanticsright "\\<rbrakk>")
    (periodcentered "\\<cdot>")
    (element "\\<in>")
    (reflexsubset "\\<subseteq>")
    (intersection "\\<inter>")
    (union "\\<union>")
    (bigintersection "\\<Inter>")
    (bigunion "\\<Union>")
    (sqintersection "\\<sqinter>")
    (squnion "\\<squnion>")
    (bigsqintersection "\\<Sqinter>")
    (bigsqunion "\\<Squnion>")
    (perpendicular "\\<bottom>")
    (dotequal "\\<doteq>")
    (wrong "\\<wrong>")
    (equivalence "\\<equiv>")
    (notequal "\\<noteq>")
    (propersqsubset "\\<sqsubset>")
    (reflexsqsubset "\\<sqsubseteq>")
    (properprec "\\<prec>")
    (reflexprec "\\<preceq>")
    (propersucc "\\<succ>")
    (approxequal "\\<approx>")
    (similar "\\<sim>")
    (simequal "\\<simeq>")
    (lessequal "\\<le>")
    (coloncolon "\\<Colon>")
    (arrowleft "\\<leftarrow>")
    (endash "\\<midarrow>")
    (arrowright "\\<rightarrow>")
    (arrowdblleft "\\<Leftarrow>")
;   (nil "\\<Midarrow>")
    (arrowdblright "\\<Rightarrow>")
    (frown "\\<frown>")
    (mapsto "\\<mapsto>")
    (leadsto "\\<leadsto>")
    (arrowup "\\<up>")
    (arrowdown "\\<down>")
    (notelement "\\<notin>")
    (multiply "\\<times>")
    (circleplus "\\<oplus>")
    (circleminus "\\<ominus>")
    (circlemultiply "\\<otimes>")
    (circleslash "\\<oslash>")
    (propersubset "\\<subset>")
    (infinity "\\<infinity>")
    (box "\\<box>")
    (lozenge1 "\\<diamond>")
    (circ "\\<circ>")
    (bullet "\\<bullet>")
    (bardbl "\\<parallel>")
    (radical "\\<surd>")
    (copyright "\\<copyright>")))

(defvar x-symbol-isabelle-xsymbol-table    ; xsymbols
  '((Xi "\\<Xi>")
    (Upsilon1 "\\<Upsilon>")
    (iota "\\<iota>")
    (upsilon "\\<upsilon>")
    (plusminus "\\<plusminus>")
    (division "\\<div>")
    (longarrowright "\\<longrightarrow>")
    (longarrowleft "\\<longleftarrow>")
    (longarrowboth "\\<longleftrightarrow>")
    (longarrowdblright "\\<Longrightarrow>")
    (longarrowdblleft "\\<Longleftarrow>")
    (longarrowdblboth "\\<Longleftrightarrow>")
    (brokenbar "\\<bar>")
    (hyphen "\\<hyphen>")
    (macron "\\<inverse>")
    (exclamdown "\\<exclamdown>")
    (questiondown "\\<questiondown>")
    (guillemotleft "\\<guillemotleft>")
    (guillemotright "\\<guillemotright>")
    (degree "\\<degree>")
    (onesuperior "\\<onesuperior>")
    (onequarter "\\<onequarter>")
    (twosuperior "\\<twosuperior>")
    (onehalf "\\<onehalf>")
    (threesuperior "\\<threesuperior>")
    (threequarters "\\<threequarters>")
    (paragraph "\\<paragraph>")
    (registered "\\<registered>")
    (ordfeminine "\\<ordfeminine>")
    (masculine "\\<ordmasculine>")
    (section "\\<section>")
    (sterling "\\<pounds>")
    (yen "\\<yen>")
    (cent "\\<cent>")
    (currency "\\<currency>")
    (braceleft2 "\\<lbrace>")
    (braceright2 "\\<rbrace>")
    (top "\\<top>")
    (congruent "\\<cong>")
    (club "\\<clubsuit>")
    (diamond "\\<diamondsuit>")
    (heart "\\<heartsuit>")
    (spade "\\<spadesuit>")
    (arrowboth "\\<leftrightarrow>")
    (greaterequal "\\<ge>")
    (proportional "\\<propto>")
    (partialdiff "\\<partial>")
    (ellipsis "\\<dots>")
    (aleph "\\<aleph>")
    (Ifraktur "\\<Im>")
    (Rfraktur "\\<Re>")
    (weierstrass "\\<wp>")
    (emptyset "\\<emptyset>")
    (angle "\\<angle>")
    (gradient "\\<nabla>")
    (product "\\<Prod>")
    (arrowdblboth "\\<Leftrightarrow>")
    (arrowdblup "\\<Up>")
    (arrowdbldown "\\<Down>")
    (angleleft "\\<langle>")
    (angleright "\\<rangle>")
    (summation "\\<Sum>")
    (integral "\\<integral>")
    (circleintegral "\\<ointegral>")
    (dagger "\\<dagger>")
    (sharp "\\<sharp>")
    (star "\\<star>")
    (smltriangleright "\\<triangleright>")
    (triangleleft "\\<lhd>")
    (triangle "\\<triangle>")
    (triangleright "\\<rhd>")
    (trianglelefteq "\\<unlhd>")
    (trianglerighteq "\\<unrhd>")
    (smltriangleleft "\\<triangleleft>")
    (natural "\\<natural>")
    (flat "\\<flat>")
    (amalg "\\<amalg>")
    (Mho "\\<mho>")
    (arrowupdown "\\<updown>")
    (longmapsto "\\<longmapsto>")
    (arrowdblupdown "\\<Updown>")
    (hookleftarrow "\\<hookleftarrow>")
    (hookrightarrow "\\<hookrightarrow>")
    (rightleftharpoons "\\<rightleftharpoons>")
    (leftharpoondown "\\<leftharpoondown>")
    (rightharpoondown "\\<rightharpoondown>")
    (leftharpoonup "\\<leftharpoonup>")
    (rightharpoonup "\\<rightharpoonup>")
    (asym "\\<asymp>")
    (minusplus "\\<minusplus>")
    (bowtie "\\<bowtie>")
    (centraldots "\\<cdots>")
    (circledot "\\<odot>")
    (propersuperset "\\<supset>")
    (reflexsuperset "\\<supseteq>")
    (propersqsuperset "\\<sqsupset>")
    (reflexsqsuperset "\\<sqsupseteq>")
    (lessless "\\<lless>")
    (greatergreater "\\<ggreater>")
    (unionplus "\\<uplus>")
    (smile "\\<smile>")
    (reflexsucc "\\<succeq>")
    (dashbar "\\<stileturn>")
    (biglogicalor "\\<Or>")
    (bigunionplus "\\<Uplus>")
    (daggerdbl "\\<ddagger>")
    (bigbowtie "\\<Join>")
    (booleans "\\<bool>")
    (complexnums "\\<complex>")
    (natnums "\\<nat>")
    (rationalnums "\\<rat>")
    (realnums "\\<real>")
    (integers "\\<int>")
    (lesssim "\\<lesssim>")
    (greatersim "\\<greatersim>")
    (lessapprox "\\<lessapprox>")
    (greaterapprox "\\<greaterapprox>")
    (definedas "\\<triangleq>")
    (cataleft "\\<lparr>")
    (cataright "\\<rparr>")
    (bigcircledot "\\<Odot>")
    (bigcirclemultiply "\\<Otimes>")
    (bigcircleplus "\\<Oplus>")
    (coproduct "\\<Coprod>")
    (cedilla "\\<cedilla>")
    (diaeresis "\\<dieresis>")
    (acute "\\<acute>")
    (hungarumlaut "\\<hungarumlaut>")
    (lozenge "\\<lozenge>")
    (smllozenge "\\<struct>")
    (dotlessi "\\<index>")
    (euro "\\<euro>")
    (zero1 "\\<zero>")
    (one1 "\\<one>")
    (two1 "\\<two>")
    (three1 "\\<three>")
    (four1 "\\<four>")
    (five1 "\\<five>")
    (six1 "\\<six>")
    (seven1 "\\<seven>")
    (eight1 "\\<eight>")
    (nine1 "\\<nine>")
    ))

(defun x-symbol-isabelle-prepare-table (table)
  (let*
      ((is-isar (eq proof-assistant-symbol 'isar))
       (prfx1 (if is-isar "" "\\"))
       (prfx2 (if is-isar "\\" "")))
    (mapcar (lambda (entry)
              (list (car entry) '() (concat prfx1 (cadr entry)) (concat prfx2 (cadr entry))))
            table)))

(defvar x-symbol-isabelle-table
  (x-symbol-isabelle-prepare-table
   (append
    (if (boundp 'x-symbol-isabelle-user-table) x-symbol-isabelle-user-table nil)
    x-symbol-isabelle-symbol-table
    x-symbol-isabelle-xsymbol-table)))

(defvar x-symbol-user-table
  (append
   (if (boundp 'x-symbol-user-table) x-symbol-user-table nil)
   '((bardash 180 (arrow) (direction east . perpendicular) nil (t "|-"))
     (bardashdbl 182 (arrow) (direction east) nil (t "|=")))))


;;;===========================================================================
;;;  Internal
;;;===========================================================================

(defvar x-symbol-isabelle-menu-alist nil
  "Internal.  Alist used for Isasym specific menu.")
(defvar x-symbol-isabelle-grid-alist nil
  "Internal.  Alist used for Isasym specific grid.")

(defvar x-symbol-isabelle-decode-atree nil
  "Internal.  Atree used by `x-symbol-token-input'.")
(defvar x-symbol-isabelle-decode-alist nil
  "Internal.  Alist used for decoding of Isasym macros.")
(defvar x-symbol-isabelle-encode-alist nil
  "Internal.  Alist used for encoding to Isasym macros.")

(defvar x-symbol-isabelle-nomule-decode-exec nil
  "Internal.  File name of Isasym decode executable.")
(defvar x-symbol-isabelle-nomule-encode-exec nil
  "Internal.  File name of Isasym encode executable.")



;;;===========================================================================
;;;  useful key bindings
;;;===========================================================================


;; FIXME: these break some standard bindings, and should only be set
;; for proof shell, script (or minibuffer) modes.

;(global-set-key [(meta l)] 'x-symbol-INSERT-lambda)

;(global-set-key [(meta n)] 'x-symbol-INSERT-notsign)
;(global-set-key [(meta a)] 'x-symbol-INSERT-logicaland)
;(global-set-key [(meta o)] 'x-symbol-INSERT-logicalor)
;(global-set-key [(meta f)] 'x-symbol-INSERT-universal1)
;(global-set-key [(meta t)] 'x-symbol-INSERT-existential1)

;(global-set-key [(meta A)] 'x-symbol-INSERT-biglogicaland)
;(global-set-key [(meta e)] 'x-symbol-INSERT-equivalence)
;(global-set-key [(meta u)] 'x-symbol-INSERT-notequal)
;(global-set-key [(meta m)] 'x-symbol-INSERT-arrowdblright)

;(global-set-key [(meta i)] 'x-symbol-INSERT-longarrowright)

(provide 'x-symbol-isabelle)
