;; Ensure that non-compiled versions of everything is loaded
(setq load-path
      (append
       '("../generic/" "../isa/" "../lego/" "../coq/") load-path))
(load "proof-site.el")
(load "proof-config.el")
(load "proof.el")
(load "isa.el")
(load "thy-mode.el")
(load "coq.el")
(load "lego.el")

(load "texi-docstring-magic.el")