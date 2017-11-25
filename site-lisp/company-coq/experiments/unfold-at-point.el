(defun company-coq-unfold-clicked (e)
  (interactive "e")
  (company-coq--with-point-at-click e
    (-when-let* ((symbol (company-coq-symbol-at-point)))
      (company-coq-with-current-buffer-maybe proof-script-buffer
        (proof-goto-end-of-locked)
        (company-coq-on-blank-line "\n" ""
          (insert (format "unfold %s in *." symbol)))
        (proof-goto-point)))))

(define-key coq-goals-mode-map (kbd "<mouse-2>") #'company-coq-unfold-clicked)
(define-key coq-goals-mode-map (kbd "<mouse-3>") #'company-coq-unfold-clicked)
