;; doc/docstring-magic.el  -- hack for using texi-docstring-magic.
;;
;; Copyright (C) 1998 LFCS Edinburgh. 
;; Author: David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; Ensure that non-compiled versions of everything are loaded.
;;
;; $Id$
;;
(setq load-path
      (append
       '("../generic/" "../isa/" "../lego/" "../coq/" "../isar" "../plastic/") load-path))
(load "proof-site.el")
(load "proof-config.el")
(load "proof.el")
(load "proof-toolbar.el")
;; New ones first incase they duplicate variable names
;; accidently. 
(load "isar.el")
(load "plastic.el")
(load "isa.el")
(load "thy-mode.el")
(load "coq.el")
(load "lego.el")
;; A couple of comint symbols are mentioned in the docs
(load "comint.el)

;; Set some symbols to make markup happen
(setq sml-mode 'markup-hack)
(setq func-menu 'markup-hack)

(load "texi-docstring-magic.el")