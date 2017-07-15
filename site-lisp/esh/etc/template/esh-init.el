(load-theme 'tango t)

;; Register “\cverb” as an inline macro highlighted as C code
;; This allows us to use \cverb|int main()|, for example.
(esh-latex-add-inline-verb "\\cverb" 'c-mode)
