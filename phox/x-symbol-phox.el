
  
(defvar x-symbol-phox-name "PhoX")
(defvar phox-xsym-extra-modes '('phox-response-mode 'phox-goals-mode))
(x-symbol-register-language 'phox 'x-symbol-phox '(phox-mode phox-shell-mode))


(defvar x-symbol-phox-required-fonts nil)
(defvar x-symbol-phox-modeline-name "phox")
(defvar x-symbol-phox-class-alist
  '((VALID "PhoX Symbol" (x-symbol-info-face))
    (INVALID "no PhoX Symbol" (red x-symbol-info-face))))
(defvar x-symbol-phox-font-lock-keywords nil)
(defvar x-symbol-phox-image-keywords nil)

(defvar x-symbol-phox-token-shape nil)
(defvar x-symbol-phox-exec-specs nil)
(defvar x-symbol-phox-decoding-regexp "\\([_'a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)")
(defvar x-symbol-phox-surrounding-regexp "[ \n\t\r]")

(defvar x-symbol-phox-input-token-ignore nil)
(defvar x-symbol-phox-header-groups-alist nil)
(defvar x-symbol-phox-class-face-alist nil)
(defvar x-symbol-phox-electric-ignore nil)
(defvar x-symbol-phox-case-insensitive nil)

(defvar x-symbol-phox-menu-alist nil
  "Internal.  Alist used for Isasym specific menu.")
(defvar x-symbol-phox-grid-alist nil
  "Internal.  Alist used for Isasym specific grid.")
(defvar x-symbol-phox-decode-atree nil
  "Internal.  Atree used by `x-symbol-token-input'.")
(defvar x-symbol-phox-decode-ahash nil
  "Internal.  Ahash.")
(defvar x-symbol-phox-decode-alist nil
  "Internal.  Alist used for decoding of Isasym macros.")
(defvar x-symbol-phox-encode-alist nil
  "Internal.  Alist used for encoding to Isasym macros.")

(defvar x-symbol-phox-nomule-decode-exec nil
  "Internal.  File name of Isasym decode executable.")
(defvar x-symbol-phox-nomule-encode-exec nil
  "Internal.  File name of Isasym encode executable.")



(defvar x-symbol-phox-master-directory  'ignore)
(defvar x-symbol-phox-image-searchpath '("./"))
(defvar x-symbol-phox-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-phox-image-file-truename-alist nil)
(defvar x-symbol-phox-image-keywords nil)

  
(defun x-symbol-phox-default-token-list (tokens) tokens)

(defvar x-symbol-phox-token-list 'x-symbol-phox-default-token-list)
(defvar x-symbol-phox-user-table nil)
(defvar x-symbol-phox-xsymb0-table
  '((greaterequal () ">=")
    (lessequal () "<=")
    (notequal () "!=")
    (element () "in")
    (notelement () "notin")
    (propersubset () "<<")
    (intersection () "inter")
    (union () "union")
    (backslash3 () "minus")
    (universal1 () "/\\")
    (existential1 () "\\/")
    (logicalor () "or")
    (logicaland () "&")
    (arrowboth () "<->")
    (arrowright () "->")
    (arrowdblright () "=>")
    (notsign () "~")
    (lambda () "\\")
))

(defvar x-symbol-phox-table
  (append x-symbol-phox-user-table x-symbol-phox-xsymb0-table))

(provide 'x-symbol-phox)