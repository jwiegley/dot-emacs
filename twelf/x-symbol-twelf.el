;; x-symbol-twelf.el
;;
;; David Aspinall, adapted from file supplied by David von Obheimb
;;
;; $Id$
;;

(defvar x-symbol-twelf-symbol-table 
  '((arrowright () "->"  "\\<rightarrow>")
    (longarrowright () "0->"  "\\<longrightarrow>")
    (longarrowdblright () "==>" "\\<Longrightarrow>")
    (logicaland     () "/\\" "\\<and>")
    (logicalor      () "\\/" "\\<or>")
    (equivalence    () "<->" "\\<equiv>")
    (existential1   () "EX"  "\\<exists>")
    (universal1     () "ALL"  "\\<forall>")
    (bardash	    () "|-" "\\<turnstile>")
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
(defvar x-symbol-twelf-master-directory 'ignore)
(defvar x-symbol-twelf-image-searchpath '("./"))
(defvar x-symbol-twelf-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-twelf-image-keywords nil)
(defvar x-symbol-twelf-font-lock-keywords nil)
(defvar x-symbol-twelf-header-groups-alist nil)
(defvar x-symbol-twelf-class-alist 
  '((VALID "Twelf Symbol" (x-symbol-info-face))
    (INVALID "no Twelf Symbol" (red x-symbol-info-face))))
(defvar x-symbol-twelf-class-face-alist nil)
(defvar x-symbol-twelf-electric-ignore nil)
(defvar x-symbol-twelf-required-fonts nil)
(defvar x-symbol-twelf-case-insensitive nil)
;; Setting token shape prevents "philosophy" example, but still
;; problems, e.g. delphi, false1.  (Pierre)
(defvar x-symbol-twelf-token-shape '(?_ "[A-Za-z]+" . "[A-Za-z_]"))
(defvar x-symbol-twelf-table x-symbol-twelf-symbol-table)
(defun x-symbol-twelf-default-token-list (tokens) tokens)
(defvar x-symbol-twelf-token-list 'x-symbol-twelf-default-token-list)
(defvar x-symbol-twelf-input-token-ignore nil)

;; internal stuff 
(defvar x-symbol-twelf-exec-specs nil)
(defvar x-symbol-twelf-menu-alist nil)
(defvar x-symbol-twelf-grid-alist nil)
(defvar x-symbol-twelf-decode-atree nil)
(defvar x-symbol-twelf-decode-alist nil)
(defvar x-symbol-twelf-encode-alist nil)
(defvar x-symbol-twelf-nomule-decode-exec nil)
(defvar x-symbol-twelf-nomule-encode-exec nil)

(warn "Twelf support for X-Symbol is highly incomplete!  Please help improve it!
Send improvements to x-symbol-twelf.el to proofgen@dcs.ed.ac.uk")


(provide 'x-symbol-twelf)
