;; new-x-symbol-coq.el   

;;	directly inspired from x-symbol-isabelle.el of ProofGeneral by
;;	Markus Wenzel, Christoph Wedler, David Aspinall.

;; Token language "Coq Symbols" for package x-symbol
;;
;;  License     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;
;; NB: Part of Proof General distribution.
;;

; ?? (defvar x-symbol-coq-required-fonts nil)

;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

;; NB da: these next two are also set in proof-x-symbol.el, but
;; it would be handy to be able to use this file away from PG.  
;; FIXME: In future could fix things so just 
;; (require 'proof-x-symbol) would be enough here.
(defvar x-symbol-coq-name "Coq Symbol")
(defvar x-symbol-coq-modeline-name "coq")

(defcustom x-symbol-coq-header-groups-alist nil
   "*If non-nil, used in coqsym specific grid/menu.
See `x-symbol-header-groups-alist'."
  :group 'x-symbol-coq
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-coq-electric-ignore 
  nil
  "*Additional Coq version of `x-symbol-electric-ignore'."
  :group 'x-symbol-coq
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)


(defvar x-symbol-coq-required-fonts nil
  "List of features providing fonts for language `coq'.")

(defvar x-symbol-coq-extra-menu-items nil
  "Extra menu entries for language `coq'.")


;;three following are from x-symbol-phox.el
(defvar x-symbol-coq-token-grammar
  ;; CW: for X-Symbol-4.4.3:
  ;; '(x-symbol-make-grammar ...)
  (if (fboundp 'x-symbol-make-grammar) ;; x-symbol >=4.3 versions
      (x-symbol-make-grammar
       :encode-spec '(((id . "[_'a-zA-Z0-9]") (op . "[]><=\\/~&+-*-%!{}:|]")) .
                    ((id . "[_'a-zA-Z0-9]") (op . "[]><=\\/~&+-*-%!{}:|]")))
       :decode-spec nil
       :decode-regexp "\\([_'a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:|-]+\\)"
       :token-list #'x-symbol-coq-default-token-list
		 :input-spec nil)))

(defvar x-symbol-coq-input-token-grammar
  '("\\([_'a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*-%!{}:|]+\\)"
     ((id . "[A-Za-z_0-9]") (op . "[-<>!+*/|&]"))
     (id . "[A-Za-z_0-9]") (op . "[-<>!+*/|&]"))
  "Grammar of input method Token for language `coq'.")

(defun x-symbol-coq-default-token-list (tokens)
  (mapcar 
   (lambda (x)
     (cons x 
	   (cond
	    ;; CW: where are the shapes `id' and `op' used?
	    ((string-match "\\`[A-Za-z_][A-Za-z_0-9]+\\'" x)
	     'id)
	    ((string-match "\\`[-<>!+*/|&]+\\'" x) 
	     'op))))
   tokens))


;(defvar x-symbol-coq-token-grammar
;  '(x-symbol-make-grammar
;    :encode-spec (((t . "\\\\")))
;    :decode-regexp "\\\\[A-Za-z]+"
;    :input-spec nil
;    :token-list x-symbol-coq-token-list))

;(defun x-symbol-coq-token-list (tokens)
;  (mapcar (lambda (x) (cons x t)) tokens))

(defvar x-symbol-coq-user-table nil
  "User table defining Coq commands, used in `x-symbol-coq-table'.")

(defvar x-symbol-coq-generated-data nil
  "Internal.")


;;;===========================================================================
;;;  No image support
;;;===========================================================================

(defvar x-symbol-coq-master-directory  'ignore)
(defvar x-symbol-coq-image-searchpath '("./"))
(defvar x-symbol-coq-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-coq-image-file-truename-alist nil)
(defvar x-symbol-coq-image-keywords nil)


;;;===========================================================================
;;  super- and subscripts
;;;===========================================================================
;not implemeted yet

(defvar x-symbol-coq-font-lock-keywords nil)

(defvar x-symbol-coq-font-lock-allowed-faces t)

;;;===========================================================================
;;;  Charsym Info
;;;===========================================================================

(defcustom x-symbol-coq-class-alist
  '((VALID "Coq Symbol" (x-symbol-info-face))
    (INVALID "no Coq Symbol" (red x-symbol-info-face)))
  "Alist for Coq's token classes displayed by info in echo area.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-texi
  :group 'x-symbol-info-strings
;;  :set 'x-symbol-set-cache-variable   [causes compile error]
  :type 'x-symbol-class-info)


(defcustom x-symbol-coq-class-face-alist nil
  "Alist for Coq's color scheme in TeXinfo's grid and info.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-coq
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
;;  :set 'x-symbol-set-cache-variable   [causes compile error]
  :type 'x-symbol-class-faces)



;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defvar x-symbol-coq-case-insensitive nil)
(defvar x-symbol-coq-token-shape nil)
(defvar x-symbol-coq-input-token-ignore nil)
(defvar x-symbol-coq-token-list 'identity)

(defvar x-symbol-coq-symbol-table      ; symbols (coq font)
  '((visiblespace "spacespace")
    (Gamma "Gamma")
    (Delta "Delta")
    (Theta "Theta")
    (Lambda "Lambda")
    (Pi "Pi")
    (Sigma "Sigma")
    (Phi "Phi")
    (Psi "Psi")
    (Omega "Omega")
    (alpha "alpha")
    (beta "beta")
    (gamma "gamma")
    (delta "delta")
    (epsilon1 "epsilon")
    (zeta "zeta")
    (eta "eta")
    (theta "theta")
    (kappa1 "kappa")
    (lambda "lambda")
    (mu "mu")
    (nu "nu")
    (xi "xi")
    (pi "pi")
    (rho1 "rho")
    (sigma "sigma")
    (tau "tau")
    (phi1 "phi")
    (chi "chi")
    (psi "psi")
    (omega "omega")

    (notsign "~")
    (logicaland "/\\")
    (logicalor "\\/")
    (universal1 "forall")
;    (existential1 "ex")
    (biglogicaland "And")
    (ceilingleft "lceil")
    (ceilingright "rceil")
    (floorleft "lfloor")
    (floorright "rfloor")
    (bardash "|-")
    (bardashdbl "Turnstile")
    (semanticsleft "lbrakk")
    (semanticsright "rbrakk")
    (periodcentered "cdot")
;    (element "in") ; coq keyword
    (element "In") 
    (reflexsubset "subseteq")
    (intersection "inter")
    (union "union")
    (bigintersection "Inter")
    (bigunion "Union")
    (sqintersection "sqinter")
    (squnion "squnion")
    (bigsqintersection "Sqinter")
    (bigsqunion "Squnion")
    (perpendicular "False")
    (dotequal "doteq")
    (wrong "wrong")
    (equivalence "<->")
    (notequal "noteq")
    (propersqsubset "sqsubset")
    (reflexsqsubset "sqsubseteq")
    (properprec "prec")
    (reflexprec "preceq")
;    (propersucc "succ")
    (approxequal "approx")
    (similar "sim")
    (simequal "simeq")
    (lessequal "<=")
    (coloncolon "Colon")
;    (arrowleft "leftarrow")
    (arrowleft "<-")
    (endash "midarrow")
;    (arrowright "rightarrow") ; only ->
    (arrowright "->")
;    (arrowdblleft "Leftarrow")
;   (nil "Midarrow")
;    (arrowdblright "Rightarrow") ; only => 
    (arrowdblright "=>")
    (frown "frown")
    (mapsto "mapsto")
    (leadsto "leadsto")
    (arrowup "up")
    (arrowdown "down")
    (notelement "notin")
    (multiply "times")
    (circleplus "oplus")
    (circleminus "ominus")
    (circlemultiply "otimes")
    (circleslash "oslash")
    (propersubset "subset")
    (infinity "infinity")
    (box "box")
    (lozenge1 "diamond")
    (circ "circ")
    (bullet "bullet")
    (bardbl "parallel")
    (radical "surd")
    (copyright "copyright")))

(defvar x-symbol-coq-xsymbol-table    ; xsymbols
  '((Xi "Xi")
    (Upsilon1 "Upsilon")
    (iota "iota")
    (upsilon "upsilon")
    (plusminus "plusminus")
    (division "div")
    (longarrowright "longrightarrow")
    (longarrowleft "longleftarrow")
    (longarrowboth "longleftrightarrow")
    (longarrowdblright "Longrightarrow")
    (longarrowdblleft "Longleftarrow")
    (longarrowdblboth "Longleftrightarrow")
    (brokenbar "bar")
    (hyphen "hyphen")
    (macron "inverse")
    (exclamdown "exclamdown")
    (questiondown "questiondown")
    (guillemotleft "guillemotleft")
    (guillemotright "guillemotright")
    (degree "degree")
    (onesuperior "onesuperior")
    (onequarter "onequarter")
    (twosuperior "twosuperior")
    (onehalf "onehalf")
    (threesuperior "threesuperior")
    (threequarters "threequarters")
    (paragraph "paragraph")
    (registered "registered")
    (ordfeminine "ordfeminine")
    (masculine "ordmasculine")
    (section "section")
    (sterling "pounds")
    (yen "yen")
    (cent "cent")
    (currency "currency")
    (braceleft2 "lbrace")
    (braceright2 "rbrace")
    (top "True")
    (congruent "cong")
    (club "clubsuit")
    (diamond "diamondsuit")
    (heart "heartsuit")
    (spade "spadesuit")
    (arrowboth "leftrightarrow")
    (greaterequal ">=")
    (proportional "propto")
    (partialdiff "partial")
    (ellipsis "dots")
    (aleph "aleph")
    (Ifraktur "Im")
    (Rfraktur "Re")
    (weierstrass "wp")
    (emptyset "emptyset")
    (angle "angle")
    (gradient "nabla")
    (product "Prod")
    (arrowdblboth "Leftrightarrow")
    (arrowdblup "Up")
    (arrowdbldown "Down")
    (angleleft "langle")
    (angleright "rangle")
    (summation "Sum")
    (integral "integral")
    (circleintegral "ointegral")
    (dagger "dagger")
    (sharp "sharp")
    (star "star")
    (smltriangleright "triangleright")
    (triangleleft "lhd")
    (triangle "triangle")
    (triangleright "rhd")
    (trianglelefteq "unlhd")
    (trianglerighteq "unrhd")
    (smltriangleleft "triangleleft")
    (natural "natural")
    (flat "flat")
    (amalg "amalg")
    (Mho "mho")
    (arrowupdown "updown")
    (longmapsto "longmapsto")
    (arrowdblupdown "Updown")
    (hookleftarrow "hookleftarrow")
    (hookrightarrow "hookrightarrow")
    (rightleftharpoons "rightleftharpoons")
    (leftharpoondown "leftharpoondown")
    (rightharpoondown "rightharpoondown")
    (leftharpoonup "leftharpoonup")
    (rightharpoonup "rightharpoonup")
    (asym "asymp")
    (minusplus "minusplus")
    (bowtie "bowtie")
    (centraldots "cdots")
    (circledot "odot")
    (propersuperset "supset")
    (reflexsuperset "supseteq")
    (propersqsuperset "sqsupset")
    (reflexsqsuperset "sqsupseteq")
    (lessless "lless")
    (greatergreater "ggreater")
    (unionplus "uplus")
    (smile "smile")
    (reflexsucc "succeq")
    (dashbar "stileturn")
    (biglogicalor "Or")
    (bigunionplus "Uplus")
    (daggerdbl "ddagger")
    (bigbowtie "Join")
    (booleans "bool")
    (complexnums "complex")
    (natnums "nat")
    (rationalnums "rat")
    (realnums "real")
    (integers "int")
    (lesssim "lesssim")
    (greatersim "greatersim")
    (lessapprox "lessapprox")
    (greaterapprox "greaterapprox")
    (definedas "triangleq")
    (cataleft "lparr")
    (cataright "rparr")
    (bigcircledot "Odot")
    (bigcirclemultiply "Otimes")
    (bigcircleplus "Oplus")
    (coproduct "Coprod")
    (cedilla "cedilla")
    (diaeresis "dieresis")
    (acute "acute")
    (hungarumlaut "hungarumlaut")
    (lozenge "lozenge")
;    (smllozenge "struct") ;coq keyword
    (dotlessi "index")
    (euro "euro")
    (zero1 "zero")
    (one1 "one")
    (two1 "two")
    (three1 "three")
    (four1 "four")
    (five1 "five")
    (six1 "six")
    (seven1 "seven")
    (eight1 "eight")
    (nine1 "nine")
    ))


(defun x-symbol-coq-prepare-table (table)
  "Builds the x-symbol coq table from `x-symbol-coq-user-table', ` x-symbol-coq-symbol-table' and `x-symbol-coq-xsymbol-table'."
  (let*
      ((is-isar t) ;; simplified from isabelle, is_isar is bad name...
       (prfx1 (if is-isar "" "\\"))
       ;(prfx2 (if is-isar "\\" ""))
		 )
    (mapcar (lambda (entry)
              (list (car entry) nil
		    (concat prfx1 (cadr entry)) 
		    ;;(concat prfx1 (cadr entry))
			 ))
            table)))

(defvar x-symbol-coq-table
  (x-symbol-coq-prepare-table
   (append
    x-symbol-coq-user-table
    x-symbol-coq-symbol-table
    x-symbol-coq-xsymbol-table)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; User-level settings for X-Symbol 
;;
;; this is MODE-ON CODING 8BITS UNIQUE SUBSCRIPTS IMAGE
(defcustom x-symbol-coq-auto-style
  '((proof-ass x-symbol-enable)	 ; MODE-ON: whether to turn on interactively
    nil   ;; x-symbol-coding
    'null ;; x-symbol-8bits	   [NEVER want it; null disables search]
    nil   ;; x-symbol-unique
    nil     ;; x-symbol-subscripts
    nil)  ;; x-symbol-image
  "Variable used to document a language access.
See documentation of `x-symbol-auto-style'."
  :group 'x-symbol-coq
  :group 'x-symbol-mode
  :type 'x-symbol-auto-style)

;; FIXME da: is this needed?
(defcustom x-symbol-coq-auto-coding-alist nil
  "*Alist used to determine the file coding of COQ buffers.
Used in the default value of `x-symbol-auto-mode-alist'.  See
variable `x-symbol-auto-coding-alist' for details."
  :group 'x-symbol-coq
  :group 'x-symbol-mode
  :type 'x-symbol-auto-coding)


     
;; from x-symbol-isa.el

;(setq proof-xsym-extra-modes '(coq-mode)
;      proof-xsym-activate-command
;      "print_mode := ([\"xsymbols\", \"symbols\"] @ ! print_mode);"
;      proof-xsym-deactivate-command
;      "print_mode := (! print_mode \\\\ [\"xsymbols\", \"symbols\"]);")

(provide 'x-symbol-coq)
