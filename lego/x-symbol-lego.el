;; x-symbol-coq.el
;;
;; David Aspinall, adapted from file supplied by David von Obheimb
;;
;; $Id$
;;

(defvar x-symbol-lego-symbol-table 
  '((longarrowright () "->"  "\\<longrightarrow>")
    (logicaland     () "/\\" "\\<and>")
    (logicalor      () "\\/" "\\<or>")
    ;; Some naughty ones, but probably what you'd like.
    ;; FIXME: can we set context to prevent accidental use,
    ;; e.g. sear<chi>ng ?
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
 ;  (mu     () "mu" "\\<mu>")
 ;  (nu     () "nu" "\\<nu>")
 ;  (xi     () "xi" "\\<xi>")
 ;  (pi     () "pi" "\\<pi>")
    (rho    () "rho" "\\<rho>")
    (sigma  () "sigma" "\\<sigma>")
    (tau    () "tau" "\\<tau>")
    (phi1   () "phi" "\\<phi>")
 ;  (chi    () "chi" "\\<chi>")
    (psi    () "psi" "\\<psi>")
    (omega  () "omega" "\\<omega>")))

;; All the stuff X-Symbol complains about
(defvar x-symbol-lego-master-directory 'ignore)
(defvar x-symbol-lego-image-searchpath '("./"))
(defvar x-symbol-lego-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-lego-image-keywords nil)
(defvar x-symbol-lego-font-lock-keywords nil)
(defvar x-symbol-lego-header-groups-alist nil)
(defvar x-symbol-lego-class-alist 
  '((VALID "Lego Symbol" (x-symbol-info-face))
    (INVALID "no Lego Symbol" (red x-symbol-info-face))))
(defvar x-symbol-lego-class-face-alist nil)
(defvar x-symbol-lego-electric-ignore nil)
(defvar x-symbol-lego-required-fonts nil)
(defvar x-symbol-lego-case-insensitive nil)
(defvar x-symbol-lego-token-shape nil)
(defvar x-symbol-lego-table x-symbol-lego-symbol-table)
(defun x-symbol-lego-default-token-list (tokens) tokens)
(defvar x-symbol-lego-token-list 'x-symbol-lego-default-token-list)
(defvar x-symbol-lego-input-token-ignore nil)

;; internal stuff 
(defvar x-symbol-lego-exec-specs nil)
(defvar x-symbol-lego-menu-alist nil)
(defvar x-symbol-lego-grid-alist nil)
(defvar x-symbol-lego-decode-atree nil)
(defvar x-symbol-lego-decode-alist nil)
(defvar x-symbol-lego-encode-alist nil)
(defvar x-symbol-lego-nomule-decode-exec nil)
(defvar x-symbol-lego-nomule-encode-exec nil)

(warn "LEGO support for X-Symbol is highly incomplete!  Please help improve it!
Send improvements to x-symbol-lego.el to proofgen@dcs.ed.ac.uk")


(provide 'x-symbol-lego)
