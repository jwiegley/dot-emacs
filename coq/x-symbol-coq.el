(defvar x-symbol-coq-symbol-table 
  '((longarrowright () "->"  "\\<longrightarrow>")
    (logicaland     () "/\\" "\\<and>")
    (logicalor      () "\\/" "\\<or>")
    (notsign	    () "~"   "\\<not>")
    (equivalence    () "<->" "\\<equiv>")
    (existential1   () "EX"  "\\<exists>")))

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
(defvar x-symbol-coq-token-shape nil)
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

(message "Coq support for X-Symbol is highly incomplete!  Please help improve it!")


(provide 'x-symbol-coq)
