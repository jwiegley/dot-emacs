;; x-symbol-phox.el   
;;	Token language "PhoX Symbols" for package x-symbol
;;
;;  ID:         $Id$
;;  Author:     C. Raffalli
;;              Updates by Markus Wenzel, Christoph Wedler, David Aspinall.
;;  Copyright   1998 Technische Universitaet Muenchen
;;  License     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;  Adapted from x-symbol-isabelle.el
;; NB: Part of Proof General distribution.
;;

;; CW: this sexpr can be deleted with X-Symbol 4.4.3
(eval-when-compile
  ;; Next lines should allow this file to work standalone 
  ;; without proof-x-symbol.el.  See comments further below too.
  (require 'cl)
  (ignore-errors (require 'x-symbol-vars)))

(defvar x-symbol-phox-required-fonts nil)
  
;;;===========================================================================
;;;  General language accesses, see `x-symbol-language-access-alist'
;;;===========================================================================

;; NB da: these next two are also set in proof-x-symbol.el, but
;; it would be handy to be able to use this file away from PG.  
;; FIXME: In future could fix things so just 
;; (require 'proof-x-symbol) would be enough here.
(defvar x-symbol-phox-name "PhoX Symbol")
(defvar x-symbol-phox-modeline-name "phox")

(defcustom x-symbol-phox-header-groups-alist nil
   "*If non-nil, used in isasym specific grid/menu.
See `x-symbol-header-groups-alist'."
  :group 'x-symbol-phox
  :group 'x-symbol-input-init
  :type 'x-symbol-headers)

(defcustom x-symbol-phox-electric-ignore nil
;;  "[:'][A-Za-z]\\|<=\\|\\[\\[\\|\\]\\]\\|~="
  "*Additional Phox version of `x-symbol-electric-ignore'."
  :group 'x-symbol-phox
  :group 'x-symbol-input-control
  :type 'x-symbol-function-or-regexp)

(defvar x-symbol-phox-required-fonts nil
  "List of features providing fonts for language `phox'.")

(defvar x-symbol-phox-extra-menu-items nil
  "Extra menu entries for language `phox'.")


(defvar x-symbol-phox-token-grammar
  ;; CW: for X-Symbol-4.4.3:
  ;; '(x-symbol-make-grammar ...)
  (if (fboundp 'x-symbol-make-grammar) ;; x-symbol >=4.3 versions
      (x-symbol-make-grammar
       :encode-spec '(((id . "[_'a-zA-Z0-9]") (op . "[]><=\\/~&+-*%!{}:-]")) .
                    ((id . "[_'a-zA-Z0-9]") (op . "[]><=\\/~&+-*%!{}:-]")))
       :decode-spec nil
       :decode-regexp "\\([_'a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)"
       :token-list #'x-symbol-phox-default-token-list)))

(defvar x-symbol-phox-input-token-grammar
  '("\\([_'a-zA-Z0-9]+\\)\\|\\([]><=\\/~&+-*%!{}:-]+\\)"
     ((id . "[A-Za-z_0-9]") (op . "[<>!+-*/|&]"))
     (id . "[A-Za-z_0-9]") (op . "[<>!+-*/|&]"))
  "Grammar of input method Token for language `phox'.")

(defun x-symbol-phox-default-token-list (tokens)
  (mapcar 
   (lambda (x)
     (cons x 
	   (cond
	    ;; CW: where are the shapes `id' and `op' used?
	    ((string-match "\\`[A-Za-z_][A-Za-z_0-9]+\\'" x)
	     'id)
	    ((string-match "\\`[<>!+-*/|&]+\\'" x) 
	     'op))))
   tokens))

(defvar x-symbol-phox-user-table nil
  "User table defining Phox commands, used in `x-symbol-phox-table'.")

(defvar x-symbol-phox-generated-data nil
  "Internal.")


;;;===========================================================================
;;;  No image support
;;;===========================================================================

(defvar x-symbol-phox-master-directory  'ignore)
(defvar x-symbol-phox-image-searchpath '("./"))
(defvar x-symbol-phox-image-cached-dirs '("images/" "pictures/"))
(defvar x-symbol-phox-image-file-truename-alist nil)
(defvar x-symbol-phox-image-keywords nil)

;;;===========================================================================
;;;  Charsym Info
;;;===========================================================================

(defcustom x-symbol-phox-class-alist
  '((VALID "Phox Symbol" (x-symbol-info-face))
    (INVALID "no Phox Symbol" (red x-symbol-info-face)))
  "Alist for Phox's token classes displayed by info in echo area.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-texi
  :group 'x-symbol-info-strings
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-class-info)


(defcustom x-symbol-phox-class-face-alist nil
  "Alist for Phox's color scheme in TeXinfo's grid and info.
See `x-symbol-language-access-alist' for details."
  :group 'x-symbol-phox
  :group 'x-symbol-input-init
  :group 'x-symbol-info-general
  :set 'x-symbol-set-cache-variable
  :type 'x-symbol-class-faces)


(defvar x-symbol-phox-font-lock-keywords x-symbol-nomule-font-lock-keywords)
(defvar x-symbol-phox-font-lock-allowed-faces t)

;;;===========================================================================
;;;  The tables
;;;===========================================================================

(defvar x-symbol-phox-case-insensitive nil)
(defvar x-symbol-phox-token-shape nil)
(defvar x-symbol-phox-input-token-ignore nil)

;; FIXME: next one not needed in X-Symbol 4, kept for back compat.
;;(defvar x-symbol-phox-exec-specs 
;;  '(nil ("\\`\\\\<[A-Za-z][A-Za-z0-9_']*>\\'" .
;;	 "\\\\<[A-Za-z][A-Za-z0-9_']*>")))

(defvar x-symbol-phox-token-list 'identity)

(defvar x-symbol-phox-xsymb0-table      ; symbols 
  '((greaterequal ">=")
    (lessequal "<=")
    (notequal "!=")
    (element "in")
    (notelement "notin")
    (propersubset "<<")
    (intersection "inter")
    (union "union")
    (backslash3 "minus")
    (universal1 "/\\")
    (existential1 "\\/")
    (logicalor "or")
    (logicaland "&")
    (arrowboth "<->")
    (arrowright "->")
    (arrowdblright "=>")
    (notsign "~")
    (lambda "\\")
))

(defun x-symbol-phox-prepare-table (table)
  "Prepar the table."
    (mapcar (lambda (entry)
              (list (car entry) nil
		    (cadr entry)))
            table))

(defvar x-symbol-phox-table
  (x-symbol-phox-prepare-table
    (append x-symbol-phox-user-table x-symbol-phox-xsymb0-table)))

(provide 'x-symbol-phox)

;;;===========================================================================
;;;  Internal
;;;===========================================================================
;; CW: all are not needed in X-Symbol >= v4.3

(defvar x-symbol-phox-menu-alist nil
  "Internal.  Alist used for Isasym specific menu.")
(defvar x-symbol-phox-grid-alist nil
  "Internal.  Alist used for Isasym specific grid.")

(defvar x-symbol-phox-decode-atree nil
  "Internal.  Atree used by `x-symbol-token-input'.")
(defvar x-symbol-phox-decode-alist nil
  "Internal.  Alist used for decoding of Isasym macros.")
(defvar x-symbol-phox-encode-alist nil
  "Internal.  Alist used for encoding to Isasym macros.")

;; FIXME: next two not needed for newer X-Symbol versions.
(defvar x-symbol-phox-nomule-decode-exec nil
  "Internal.  File name of Isasym decode executable.")
(defvar x-symbol-phox-nomule-encode-exec nil
  "Internal.  File name of Isasym encode executable.")

(provide 'x-symbol-phox)

