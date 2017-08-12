;;; proof-maths-menu.el --- Support for maths menu mode package

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>

;; License:   GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; With thanks to Dave Love for the original maths menu code,
;; provided at http://www.loveshack.ukfsn.org/emacs/
;; 
;; Note: maths menu is bundled with Proof General in lib/, and PG will select
;; it's own version before any other version on the Emacs load path.
;; If you want to override this, simply load your version before
;; starting Emacs, with (require 'maths-menu).
;;

;;; Code:

(eval-when-compile
  (require 'cl))

(eval-when-compile
  (require 'proof-auxmodes)	  ; loaded by proof.el
  (require 'maths-menu))	  ; loaded dynamically in proof-auxmodes


;;;###autoload
(defun proof-maths-menu-set-global (flag)
  "Set global status of maths-menu mode for PG buffers to be FLAG.
Turn on/off menu in all script buffers and ensure new buffers follow suit."
  (let ((hook (proof-ass-sym mode-hook)))
    (if flag
	(add-hook hook 'maths-menu-mode)
      (remove-hook hook 'maths-menu-mode))
    (proof-map-buffers
      (proof-buffers-in-mode proof-mode-for-script)
      (maths-menu-mode (if flag 1 0)))))



;;;###autoload
(defun proof-maths-menu-enable ()
  "Turn on or off maths-menu mode in Proof General script buffer.
This invokes `maths-menu-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have maths menu mode turn itself on automatically
in future if we have just activated it for this buffer."
  (interactive)
  (require 'maths-menu)
  (if (proof-maths-menu-support-available)
      (proof-maths-menu-set-global (not maths-menu-mode))))


(provide 'proof-maths-menu)

;;; proof-maths-menu.el ends here
