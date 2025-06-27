(defun manipulate-list (lst mutations)
  (let ((current lst))
    (dolist (op mutations current)
      (pcase op
        (`(:append . ,items) (setq current (append current items)))
        (`(:nconc . ,items) (nconc current items))
        (`(:add ,item) (setq current (add-to-list 'current item)))
        (`(:delete ,item) (setq current (delete item current)))
        (`(:remove-if ,pred) (setq current (cl-remove-if pred current)))
        (`(:reverse) (setq current (reverse current)))
        (`(:sort ,lessp) (setq current (sort current lessp)))
        (_ (error "Unknown operation: %S" op))))))

(manipulate-list '(1 2 3) '((:add 3)))
