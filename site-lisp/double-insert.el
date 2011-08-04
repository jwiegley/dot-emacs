 (defmacro rgb-insert-if-double (otherwise)
   "Insert OTHERWISE when the key mapped to this fcn is pressed twice.
  For example typing && can result in &amp; appearing in place of &&.
  Use C-u <count> <key> to insert <key> more than once without replace."
   `(lambda (cnt raw)
      (interactive "p\nP")
      (if (and (equal (preceding-char) last-command-char)
               (not raw))
          (progn
              (backward-delete-char 1)
              (insert ,otherwise))
          (self-insert-command cnt))))
 
(add-hook 'html-mode-hook
 (lambda ()
   (define-key html-mode-map [(<)]  (rgb-insert-if-double "&lt;"))
   (define-key html-mode-map [(>)]  (rgb-insert-if-double "&gt;"))
   (define-key html-mode-map [(&)]  (rgb-insert-if-double "&amp;"))
   (define-key html-mode-map [(\")] (rgb-insert-if-double "&quot;"))))
