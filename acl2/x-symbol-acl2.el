;; x-symbol-acl2.el
;;
;; David Aspinall, adapted from file supplied by David von Obheimb
;;
;; $Id$
;;

(defvar x-symbol-acl2-symbol-table 
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
(defvar x-symbol-acl2-master-directory 'ignore)
(defvar x-symbol-acl2-image-searchpath '("./"))
(defvar x-symbol-acl2-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-acl2-image-keywords nil)
(defvar x-symbol-acl2-font-lock-keywords nil)
(defvar x-symbol-acl2-header-groups-alist nil)
(defvar x-symbol-acl2-class-alist 
  '((VALID "Acl2 Symbol" (x-symbol-info-face))
    (INVALID "no Acl2 Symbol" (red x-symbol-info-face))))
(defvar x-symbol-acl2-class-face-alist nil)
(defvar x-symbol-acl2-electric-ignore nil)
(defvar x-symbol-acl2-required-fonts nil)
(defvar x-symbol-acl2-case-insensitive nil)
;; Setting token shape prevents "philosophy" example, but still
;; problems, e.g. delphi, false1.  (Pierre)
(defvar x-symbol-acl2-token-shape '(?_ "[A-Za-z]+" . "[A-Za-z_]"))
(defvar x-symbol-acl2-table x-symbol-acl2-symbol-table)
(defun x-symbol-acl2-default-token-list (tokens) tokens)
(defvar x-symbol-acl2-token-list 'x-symbol-acl2-default-token-list)
(defvar x-symbol-acl2-input-token-ignore nil)

;; internal stuff 
(defvar x-symbol-acl2-exec-specs nil)
(defvar x-symbol-acl2-menu-alist nil)
(defvar x-symbol-acl2-grid-alist nil)
(defvar x-symbol-acl2-decode-atree nil)
(defvar x-symbol-acl2-decode-alist nil)
(defvar x-symbol-acl2-encode-alist nil)
(defvar x-symbol-acl2-nomule-decode-exec nil)
(defvar x-symbol-acl2-nomule-encode-exec nil)

(warn "Acl2 support for X-Symbol is highly incomplete!  Please help improve it!
Send improvements to x-symbol-acl2.el to proofgen@proofeneral.org")


(provide 'x-symbol-acl2)
