;;; dr-racket-like-unicode.el --- DrRacket-style unicode input -*- lexical-binding: t; -*-

;; Copyright (C) 2016 David Christiansen

;; Author: David Christiansen <david@davidchristiansen.dk>
;; Keywords: i18n tools
;; Package-Requires: ((emacs "24.1"))
;; Version: 1.1

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is an implementation of DrRacket-style Unicode input.  The
;; difference between this and an Emacs input method is that an Emacs
;; input method attempts to transform text as it is typed, while this
;; minor mode simply provides a command that turns the current
;; TeX-syntax symbol into its Unicode equivalent.

;;; Code:

(defgroup dr-racket-like-unicode
  '()
  "Input Unicode characters as is done in DrRacket."
  :group 'editing)

(defcustom dr-racket-like-unicode-table
  '(("\\to"              . "→")
    ("\\rightarrow"      . "→")
    ("\\Rightarrow"      . "⇒")
    ("\\leftarrow"       . "←")
    ("\\Leftarrow"       . "⇐")
    ("\\Downarrow"       . "⇓")
    ("\\nwarrow"         . "↖")
    ("\\downarrow"       . "↓")
    ("\\mapsto"          . "↦")
    ("\\searrow"         . "↘")
    ("\\swarrow"         . "↙")
    ("\\uparrow"         . "↑")
    ("\\longrightarrow"  . "−")
    ("\\Uparrow"         . "⇑")
    ("\\Leftrightarrow"  . "⇔")
    ("\\updownarrow"     . "↕")
    ("\\leftrightarrow"  . "↔")
    ("\\nearrow"         . "↗")
    ("\\Updownarrow"     . "⇕")
    ("\\aleph"           . "א")
    ("\\emptyset"        . "∅")
    ("\\nabla"           . "∇")
    ("\\diamondsuit"     . "♦")
    ("\\spadesuit"       . "♠")
    ("\\clubsuit"        . "♣")
    ("\\heartsuit"       . "♥")
    ("\\sharp"           . "♯")
    ("\\flat"            . "♭")
    ("\\natural"         . "♮")
    ("\\surd"            . "√")
    ("\\neg"             . "¬")
    ("\\triangle"        . "△")
    ("\\forall"          . "∀")
    ("\\exists"          . "∃")
    ("\\infty"           . "∞")
    ("\\pm"              . "±")
    ("\\cap"             . "∩")
    ("\\diamond"         . "◇")
    ("\\oplus"           . "⊕")
    ("\\mp"              . "∓")
    ("\\cup"             . "∪")
    ("\\bigtriangleup"   . "△")
    ("\\ominus"          . "⊖")
    ("\\times"           . "×")
    ("\\uplus"           . "⊎")
    ("\\bigtriangledown" . "▽")
    ("\\otimes"          . "⊗")
    ("\\div"             . "÷")
    ("\\sqcap"           . "⊓")
    ("\\triangleright"   . "▹")
    ("\\oslash"          . "⊘")
    ("\\ast"             . "∗")
    ("\\sqcup"           . "⊔")
    ("\\vee"             . "∨")
    ("\\wedge"           . "∧")
    ("\\triangleleft"    . "◃")
    ("\\odot"            . "⊙")
    ("\\star"            . "★")
    ("\\dagger"          . "†")
    ("\\bullet"          . "•")
    ("\\ddagger"         . "‡")
    ("\\wr"              . "≀")
    ("\\amalg"           . "⨿")
    ("\\leq"             . "≤")
    ("\\geq"             . "≥")
    ("\\equiv"           . "≡")
    ("\\models"          . "⊨")
    ("\\prec"            . "≺")
    ("\\succ"            . "≻")
    ("\\precdot"         . "⋖")
    ("\\succdot"         . "⋗")
    ("\\sim"             . "∼")
    ("\\perp"            . "⊥")
    ("\\bot"             . "⊥")
    ("\\top"             . "⊤")
    ("\\preceq"          . "≼")
    ("\\succeq"          . "≽")
    ("\\simeq"           . "≃")
    ("\\ll"              . "≪")
    ("\\gg"              . "≫")
    ("\\asymp"           . "≍")
    ("\\parallel"        . "∥")
    ("\\subset"          . "⊂")
    ("\\supset"          . "⊃")
    ("\\approx"          . "≈")
    ("\\bowtie"          . "⋈")
    ("\\subseteq"        . "⊆")
    ("\\supseteq"        . "⊇")
    ("\\cong"            . "≌")
    ("\\sqsubsetb"       . "⊏")
    ("\\sqsupsetb"       . "⊐")
    ("\\neq"             . "≠")
    ("\\smile"           . "⌣")
    ("\\sqsubseteq"      . "⊑")
    ("\\sqsupseteq"      . "⊒")
    ("\\doteq"           . "≐")
    ("\\frown"           . "⌢")
    ("\\in"              . "∈")
    ("\\ni"              . "∋")
    ("\\notin"           . "∉")
    ("\\propto"          . "∝")
    ("\\vdash"           . "⊢")
    ("\\dashv"           . "⊣")
    ("\\Vdash"           . "⊩")
    ("\\forces"          . "⊩")
    ("\\sum"             . "∑")
    ("\\prod"            . "∏")
    ("\\coprod"          . "∐")
    ("\\int"             . "∫")
    ("\\oint"            . "∮")
    ("\\sqrt"            . "√")
    ("\\skull"           . "☠")
    ("\\smiley"          . "☺")
    ("\\blacksmiley"     . "☻")
    ("\\frownie"         . "☹")
    ("\\S"               . "§")
    ("\\l"               . "ł")
    ("\\newpage"         . "")
    ("\\vdots"           . "⋮")
    ("\\ddots"           . "⋱")
    ("\\cdots"           . "⋯")
    ("\\hdots"           . "⋯")
    ("\\langle"          . "⟨")
    ("\\rangle"          . "⟩")
    ("\\llbracket"       . "〚")
    ("\\rrbracket"       . "〛")
    ("\\cdot"            . "·")
    ("\\circ"            . "∘")
    ("\\prime"           . "′")
    ("\\alpha"           . "α")
    ("\\beta"            . "β")
    ("\\gamma"           . "γ")
    ("\\delta"           . "δ")
    ("\\epsilon"         . "ε")
    ("\\varepsilon"      . "ε")
    ("\\zeta"            . "ζ")
    ("\\eta"             . "η")
    ("\\theta"           . "θ")
    ("\\vartheta"        . "ϑ")
    ("\\iota"            . "ι")
    ("\\kappa"           . "κ")
    ("\\lambda"          . "λ")
    ("\\mu"              . "μ")
    ("\\nu"              . "ν")
    ("\\xi"              . "ξ")
    ("\\omicron"         . "ο")
    ("\\pi"              . "π")
    ("\\rho"             . "ρ")
    ("\\varrho"          . "ϱ")
    ("\\sigma"           . "σ")
    ("\\varsigma"        . "ς")
    ("\\tau"             . "τ")
    ("\\upsilon"         . "υ")
    ("\\phi"             . "φ")
    ("\\chi"             . "χ")
    ("\\psi"             . "ψ")
    ("\\omega"           . "ω")
    ("\\Alpha"           . "Α")
    ("\\Beta"            . "Β")
    ("\\Gamma"           . "Γ")
    ("\\Delta"           . "Δ")
    ("\\Epsilon"         . "Ε")
    ("\\Zeta"            . "Ζ")
    ("\\Eta"             . "Η")
    ("\\Theta"           . "Θ")
    ("\\Iota"            . "Ι")
    ("\\Kappa"           . "Κ")
    ("\\Lambda"          . "Λ")
    ("\\Mu"              . "Μ")
    ("\\Nu"              . "Ν")
    ("\\Xi"              . "Ξ")
    ("\\Omicron"         . "Ο")
    ("\\Pi"              . "Π")
    ("\\Rho"             . "Ρ")
    ("\\Sigma"           . "Σ")
    ("\\Tau"             . "Τ")
    ("\\Upsilon"         . "Υ")
    ("\\Phi"             . "Φ")
    ("\\Chi"             . "Χ")
    ("\\Psi"             . "Ψ")
    ("\\Omega"           . "Ω")
    ("\\o"               . "ø")
    ("\\O"               . "Ø")
    ("\\ae"              . "æ")
    ("\\AE"              . "Æ")
    ("\\aa"              . "å")
    ("\\AA"              . "Å")
    ("\\\"a"             . "ä")
    ("\\\"o"             . "ö")
    ("\\\"u"             . "ü")
    ("\\\"y"             . "ÿ")
    ("\\\"i"             . "ï")
    ("\\\"e"             . "ë"))
  "The table of operators for `dr-racket-like-unicode-char'."
  :type 'alist
  :group 'dr-racket-like-unicode)

(defun dr-racket-like-unicode--replace-region (start end new-str)
  "Replace the contents of the current buffer between position START and END with NEW-STR."
  (delete-region start end)
  (goto-char start)
  (insert new-str))

;;;###autoload
(defun dr-racket-like-unicode-char ()
  "Transform the TeX-style code immediately prior to point into Unicode.

Customize `dr-racket-like-unicode-table' to change the collection of unicode symbols."
  (interactive)
  (let ((ok-p (looking-back "\\\\\"?[a-zA-Z]+" (max 0 (- (point) 50)))))
    (if (not ok-p)
        (error "No character code immediately before point")
      (let ((code (match-string 0))
            (start (match-beginning 0))
            (end (match-end 0)))
        (let ((unicode-options (cl-remove-if-not (lambda (code-and-str)
                                                   (string-prefix-p code (car code-and-str)))
                                                 dr-racket-like-unicode-table)))
          (pcase unicode-options
            ('()
             (error "Did't understand `%s' as a Unicode abbreviation" code))
            (`((,_code . ,str))
             (dr-racket-like-unicode--replace-region start end str))
            (more
             (let* ((chosen-code (completing-read (concat "Ambiguous code `" code "': ")
                                                  more
                                                  nil
                                                  t
                                                  nil nil code))
                    (unicode (assoc chosen-code
                                    dr-racket-like-unicode-table)))
               (if unicode
                   (dr-racket-like-unicode--replace-region
                    start
                    end
                    (cdr unicode))
                 (error "Did't understand `%s' as a Unicode abbreviation" chosen-code))))))))))


(defvar dr-racket-like-unicode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c \\") 'dr-racket-like-unicode-char)
    map))

;;;###autoload
(define-minor-mode dr-racket-like-unicode-mode
  "A minor mode for writing Unicode as in DrDr-Racket.

This minor mode binds one command: `dr-racket-like-unicode-char'.

\\{dr-racket-like-unicode-map}"
  nil
  " Dr\\"
  dr-racket-like-unicode-map)

(provide 'dr-racket-like-unicode)
;;; dr-racket-like-unicode.el ends here
