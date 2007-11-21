(require 'info-look)

(info-lookup-add-help :mode 'lisp-mode
		      :regexp "[^][()'\" \t\n]+"
		      :ignore-case t
		      :doc-spec '(("(ansicl)Symbol Index" nil nil nil)))

(eval-after-load "lisp-mode"
  '(progn
     (define-key lisp-mode-map [(control ?h) ?f] 'info-lookup-symbol)))

(defadvice Info-exit (after remove-info-window activate)
  "When info mode is quit, remove the window."
  (if (> (length (window-list)) 1)
      (delete-window)))
