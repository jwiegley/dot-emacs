;; x-symbol-coq.el
;;
;; David Aspinall, adapted from file supplied by David von Obheimb
;;
;; $Id$
;;

(defvar x-symbol-coq-symbol-table 
  '((arrowup () "\\+"  "\\<uparrow>")
    (arrowdown () "\\-"  "\\<downarrow>")
    (perpendicular  () "False"  "\\<bottom>")
    (top            () "True"   "\\<top>")
    (notsign       () "~"       "\\<not>")
    (longarrowright () "->"  "\\<longrightarrow>")
    (logicaland     () "/\\" "\\<and>")
    (logicalor      () "\\/" "\\<or>")
    (equivalence    () "<->" "\\<equiv>")
    (existential1   () "EX"  "\\<exists>")
    ;; some naughty ones, but probably what you'd like
    ;; (a mess in words like "searching" !!)
    (Gamma  () "Gamma" "\\<Gamma>")
    (Delta  () "Delta" "\\<Delta>")
    (Theta  () "Theta" "\\<Theta>")
    (Lambda () "Lambda" "\\<Lambda>")
    (Pi     () "Pi" "\\<Pi>")
    (Sigma  () "Sigma" "\\<Sigma>")
    (Phi    () "Phi" "\\<Phi>")
    (Psi    () "Psi" "\\<Psi>")
    (Omega  () "Omega" "\\<Omega>")
    (alpha  () "alpha" "\\<alpha>")
    (beta   () "beta" "\\<beta>")
    (gamma  () "gamma" "\\<gamma>")
    (delta  () "delta" "\\<delta>")
    (epsilon1 () "epsilon" "\\<epsilon>")
    (zeta   () "zeta" "\\<zeta>")
    (eta    () "eta" "\\<eta>")
    (theta1 () "theta" "\\<theta>")
    (kappa1 () "kappa" "\\<kappa>")
    (lambda () "lambda" "\\<lambda>")
;    (mu     () "mu" "\\<mu>")
;    (nu     () "nu" "\\<nu>")
;    (xi     () "xi" "\\<xi>")
;    (pi     () "pi" "\\<pi>")
    (rho    () "rho" "\\<rho>")
    (sigma  () "sigma" "\\<sigma>")
    (tau    () "tau" "\\<tau>")
    (phi1   () "phi" "\\<phi>")
;    (chi    () "chi" "\\<chi>")
    (psi    () "psi" "\\<psi>")
    (omega  () "omega" "\\<omega>")))

;; All the stuff X-Symbol complains about
(defvar x-symbol-coq-master-directory 'ignore)
(defvar x-symbol-coq-image-searchpath '("./"))
(defvar x-symbol-coq-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-coq-image-keywords nil)
(defvar x-symbol-coq-font-lock-keywords nil)
(defvar x-symbol-coq-header-groups-alist nil)
(defvar x-symbol-coq-class-alist 
  '((VALID "Coq Symbol" (x-symbol-info-face))
    (INVALID "no Coq Symbol" (red x-symbol-info-face))))
(defvar x-symbol-coq-class-face-alist nil)
(defvar x-symbol-coq-electric-ignore nil)
(defvar x-symbol-coq-required-fonts nil)
(defvar x-symbol-coq-case-insensitive nil)

;Pierre: let's try this, phi1 will be encoded, but not phia or
;philosophy. problem: blaphi will be encoded,
; other problem: false1 sholud not be encoded

(defvar x-symbol-coq-token-shape '(?_ "[A-Za-z]+" . "[A-Za-z_]"))

;(defvar x-symbol-coq-token-shape nil)

(defvar x-symbol-coq-table x-symbol-coq-symbol-table)
(defun x-symbol-coq-default-token-list (tokens) tokens)
(defvar x-symbol-coq-token-list 'x-symbol-coq-default-token-list)
(defvar x-symbol-coq-input-token-ignore nil)

;; internal stuff 
(defvar x-symbol-coq-exec-specs nil)
(defvar x-symbol-coq-menu-alist nil)
(defvar x-symbol-coq-grid-alist nil)
(defvar x-symbol-coq-decode-atree nil)
(defvar x-symbol-coq-decode-alist nil)
(defvar x-symbol-coq-encode-alist nil)
(defvar x-symbol-coq-nomule-decode-exec nil)
(defvar x-symbol-coq-nomule-encode-exec nil)

(warn "Coq support for X-Symbol is highly incomplete!  Please help improve it!
Send improvements to x-symbol-coq.el to proofgen@dcs.ed.ac.uk")


(provide 'x-symbol-coq)
