;; proof.el  Proof General loader.
;;
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; Thanks to Rod Burstall, Martin Hofmann,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens
;;   for helpful comments and code.
;;
;; $Id$
;;

(require 'proof-site)			; site config

(require 'proof-config)			; variables

(require 'proof-splash)			; splash screen

;; FIXME da: I think these ones should be autoloaded!!
(require 'cl)
(require 'compile)
(require 'comint)
(require 'etags)			
(require 'easymenu)


;; Spans are our abstraction of extents/overlays.
(cond ((fboundp 'make-extent) (require 'span-extent))
      ((fboundp 'make-overlay) (require 'span-overlay))
      (t nil))

(require 'proof-syntax)
(require 'proof-indent)


;; browse-url function doesn't seem to be autoloaded in
;; XEmacs 20.4, but it is in FSF Emacs 20.2.
(or (fboundp 'browse-url)
    (autoload 'browse-url "browse-url"
      "Ask a WWW browser to load URL." t))

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq-default var value)))


;; Load toolbar code if toolbars available.
(if (featurep 'toolbar)
    (require 'proof-toolbar))

;; Main code is in these files
(require 'proof-script)
(require 'proof-shell)


(provide 'proof)
;; proof.el ends here
