(require 'cc-mode)
(require 'yasnippet)

(add-to-list 'c-style-alist
             '("edg"
               (indent-tabs-mode . nil)
               (c-basic-offset . 2)
               (c-comment-only-line-offset . (0 . 0))
               (c-hanging-braces-alist
                . ((substatement-open before after)
                   (arglist-cont-nonempty)))
               (c-offsets-alist
                . ((statement-block-intro . +)
                   (knr-argdecl-intro . 5)
                   (substatement-open . 0)
                   (substatement-label . 0)
                   (label . 0)
                   (case-label . +)
                   (statement-case-open . 0)
                   (statement-cont . +)
                   (arglist-intro . +)
                   (arglist-close . +)
                   (inline-open . 0)
                   (brace-list-open . 0)
                   (topmost-intro-cont
                    . (first c-lineup-topmost-intro-cont
                             c-lineup-gnu-DEFUN-intro-cont))))
               (c-special-indent-hook . c-gnu-impose-minimum)
               (c-block-comment-prefix . "")))

(define-minor-mode edg-mode
  "Minor mode for editing EDG code.")

(yas/define-snippets
 'cc-mode
 '(("if" "if ($0) {\n}  /* if */" "if" edg-mode)

   ("ife" "if ($0) {\n} else {\n}  /* if */" "ife" edg-mode)

   ("switch"
    "switch ($0) {\ncase :\nbreak;\ndefault:\nbreak;\n}  /* switch */"
    "switch" edg-mode)

   ("for" "for ($0; ; ) {\n}  /* for */" "for" edg-mode)

   ("while" "while ($0) {\n}  /* while */" "while" edg-mode)

   ("defun" "void $1($0) {\n}  /* $1 */" "defun" edg-mode)
   ))

(provide 'edg)
