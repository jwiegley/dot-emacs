;; x-symbol-hol98.el
;;
;; David Aspinall, adapted from file supplied by David von Obheimb
;;
;; $Id$
;;

(defvar x-symbol-hol98-symbol-table 
  '((longarrowright () "->"  "\\<longrightarrow>")
    (longarrowdblright () "==>" "\\<Longrightarrow>")
    (logicaland     () "/\\" "\\<and>")
    (logicalor      () "\\/" "\\<or>")
    (equivalence    () "<->" "\\<equiv>")
    (existential1   () "EX"  "\\<exists>")
    (universal1     () "ALL"  "\\<forall>")
    ;; some naughty ones, but probably what you'd like
    ;; (a mess in words like "searching" "philosophy" etc!!)
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
(defvar x-symbol-hol98-master-directory 'ignore)
(defvar x-symbol-hol98-image-searchpath '("./"))
(defvar x-symbol-hol98-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-hol98-image-keywords nil)
(defvar x-symbol-hol98-font-lock-keywords nil)
(defvar x-symbol-hol98-header-groups-alist nil)
(defvar x-symbol-hol98-class-alist 
  '((VALID "Hol98 Symbol" (x-symbol-info-face))
    (INVALID "no Hol98 Symbol" (red x-symbol-info-face))))
(defvar x-symbol-hol98-class-face-alist nil)
(defvar x-symbol-hol98-electric-ignore nil)
(defvar x-symbol-hol98-required-fonts nil)
(defvar x-symbol-hol98-case-insensitive nil)
(defvar x-symbol-hol98-token-shape nil)
(defvar x-symbol-hol98-table x-symbol-hol98-symbol-table)
(defun x-symbol-hol98-default-token-list (tokens) tokens)
(defvar x-symbol-hol98-token-list 'x-symbol-hol98-default-token-list)
(defvar x-symbol-hol98-input-token-ignore nil)

;; internal stuff 
(defvar x-symbol-hol98-exec-specs nil)
(defvar x-symbol-hol98-menu-alist nil)
(defvar x-symbol-hol98-grid-alist nil)
(defvar x-symbol-hol98-decode-atree nil)
(defvar x-symbol-hol98-decode-alist nil)
(defvar x-symbol-hol98-encode-alist nil)
(defvar x-symbol-hol98-nomule-decode-exec nil)
(defvar x-symbol-hol98-nomule-encode-exec nil)

(warn "Hol98 support for X-Symbol is highly incomplete!  Please help improve it!
Send improvements to x-symbol-hol98.el to proofgen@dcs.ed.ac.uk")


(provide 'x-symbol-hol98)
