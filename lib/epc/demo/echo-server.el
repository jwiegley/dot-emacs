(require 'epcs)

(defun echo-server-init (mngr)
  (epc:define-method mngr 'echo #'identity))

(when noninteractive
  (setq epcs (epcs:server-start #'echo-server-init))
  ;; Start "event loop".
  (while t
    (sleep-for 0.1)))
