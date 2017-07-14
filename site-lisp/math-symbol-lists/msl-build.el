;; functions to build symbol lists

(require 'cl)

;; IMPORT UTILITIES
;; 
;; Utilities for reading LUCR list from [1] and optionally PRINT. LUCR list is a
;; super-set of unicode-math list [2]. FILE is a local file from [3].
;; 
;;  [1] http://milde.users.sourceforge.net/LUCR/Math/
;;  [2] https://github.com/wspr/unicode-math/blob/master/unicode-math-table.tex
;;  [3] http://milde.users.sourceforge.net/LUCR/Math/data/unimathsymbols.txt

(defun msl--LUCR-parse-alias (str)
  ;; (msl--LUCR-parse-alias "= \\Theta (-slantedGreek)")
  ;; (msl--LUCR-parse-alias "= \\mathrm{\\Theta}")
  (when (and str (msl--no-{}-p str))
    (if (string-match " ?= ?\\(\\\\[^() ]+\\) *$" str)
        (cons (match-string 1 str) "latex")
      (if (string-match " ?= ?\\(\\\\[^() ]+\\) *(\\(.+\\)) *$" str)
          (cons (match-string 1 str) (match-string 2 str))))))

(defun msl--LUCR-parse-line (line)
  (let* ((words (split-string line "\\^"))
         (comment (nth 7 words))
         (aliases (when comment
                    (delq nil
                          (mapcar #'msl--LUCR-parse-alias 
                                  (split-string comment ", *")))))
         (packages (when (> (length (nth 6 words)) 0)
                     (split-string (nth 6 words) " +")))
         (usymb (nth 1 words)))
    (when (> (length usymb) 0)
      (list (nth 0 words) 			;; 0: HEX Code
            (when (> (length usymb) 0)
              (substring usymb -1)) ;; 1: Unicode Symbol
            (nth 2 words)           ;; 2: La(TeX) command
            (nth 3 words)           ;; 3: unicode-math package command
            (nth 4 words)           ;; 4: Class
            (nth 5 words)           ;; 5: category
            packages    			;; 6: packages (prefixed with _ are conflicts)
            aliases)))) 			;; 7: aliases (conses of (alias . package))

(defun msl--no-{}-p (str)
  (not (string-match "[{}]" str)))

(defun msl--LUCR-read-file (file)
  (let ((lines (with-temp-buffer
                 (insert-file-contents file)
                 (split-string (buffer-string) "\n" t))))
    (delq nil
          (cl-loop for l in lines
                   unless (string-match-p "^#" l)
                   collect (msl--LUCR-parse-line l)))))

(defun msl--LUCR-to-msl (lucr &optional latex alias no-parse)
  "Convert LUCR list to this package conventions.
If LATEX is non-nil, give package and latex command instead of
unicode-math command. If ALIAS is non-nil give package and latex
command from alias field. "
  (flet ((code (el) (if no-parse (car el) (string-to-number (car el) 16))))
    (let ((sl (delq nil
                    (cond
                     (latex (mapcan (lambda (el)
                                      (and (> (length (nth 2 el)) 0)
                                           (> (length (nth 6 el)) 0)
                                           (msl--no-{}-p (nth 2 el))
                                           (mapcar (lambda (pkg)
                                                     (list pkg (nth 5 el) (nth 2 el) (code el) (nth 1 el)))
                                                   (nth 6 el))))
                                    lucr))
                     (alias (mapcan (lambda (el)
                                      (mapcan (lambda (pkg)
                                                (and (> (length (car pkg)) 0)
                                                     (msl--no-{}-p (car pkg))
                                                     (mapcar (lambda (pkg2)
                                                               (list pkg2 (nth 5 el) (car pkg) (code el) (nth 1 el)))
                                                             (split-string (cdr pkg) " +"))))
                                              (nth 7 el)))
                                    lucr))
                     (t (mapcar (lambda (el)
                                  (and (string-match-p "\\\\" (nth 3 el))
                                       (list (nth 5 el) (nth 3 el) (code el) (nth 1 el))))
                                lucr))))))
      (when (or latex alias)
        (setq sl (mapcar (lambda (el)
                           (if (not (string-match-p "^-" (car el)))
                               el
                             (append (list (substring (car el) 1)) (cdr el) (list t))))
                         sl)))
      (cl-sort sl (lambda (a b) (string-lessp (concat (car a) (cadr a)) (concat (car b) (cadr b))))))))

(defun msl--LUCR-filter-LaTeX-aliases (list)
  (delq nil
        (mapcar (lambda (el)
                  (when (cl-some (lambda (al) 
                                   (and (string= "latex" (cdr al))
                                        (msl--no-{}-p (car al))))
                                 (nth 7 el))
                    el))
                list)))

;; this is how you build those 
(setq tt (msl--LUCR-read-file "./data/unimathsymbols.txt"))

;; extra aliases for basic symbols
(setq tt2 (msl--LUCR-filter-LaTeX-aliases tt))
(msl--LUCR-to-msl tt2 nil t)

;; extended
(msl--LUCR-to-msl tt)
;; packages
(msl--LUCR-to-msl tt t)
;; aliases
(msl--LUCR-to-msl tt nil t)


;; SUBSCRIPTS and SUPERSCRIPTS

(defvar subscripts )
(defvar superscripts "ⱽª²³¹ºʰʱʲʳʴʵʶʷʸˠˡˢˣᴬᴭᴮᴯᴰᴱᴲᴳᴴᴵᴶᴷᴸᴹᴺᴻᴼᴽᴾᴿᵀᵁᵂᵃᵄᵅᵆᵇᵈᵉᵊᵋᵌᵍᵎᵏᵐᵑᵒᵓᵔᵕᵖᵗᵘᵙᵚᵛᵜᵝᵞᵟᵠᵡᵸᶛᶜᶝᶞᶟᶠᶡᶢᶣᶤᶥᶦᶧᶨᶩᶪᶫᶬᶭᶮᶯᶰᶱᶲᶳᶴᶵᶶᶷᶸᶹᶺᶻᶼᶽᶾᶿ⁰ⁱ⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿ")

;; taken from https://github.com/tpapp/company-unicode-subsuper/blob/master/company-unicode-subsuper.el
(defconst unicode-name-table
  '((?β . "beta")
    (?γ . "gamma")
    (?δ . "delta")
    (?θ . "theta")
    (?ɩ . "iota")
    (?φ . "varphi")                     ; varphi instead of phi, as in LaTeX
    (?χ . "chi")
    (?ρ . "rho")
    (?− . "-"))                         ; replace #x2212 with minus sign
  "table for entering characters outside the ASCII range. Follows conventions of LaTeX for Greek letters, but without the \\ prefix.")

(defun gen-scirpted-alist (char-str type prefix)
  (mapcar (lambda (c)
            (let* ((dec (cdr (get-char-code-property c 'decomposition)))
                   (plain (or (cdr (assoc (car dec) unicode-name-table)) dec)))
              (list type (concat prefix plain) c (char-to-string c))))
          char-str))

(gen-scirpted-alist "₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓᵦᵧᵨᵩᵪ" "subscript" "_")
(gen-scirpted-alist "⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁⱽᵂᵝᵞᵟᶿᶥᵠᵡ" "superscripts" "^")

