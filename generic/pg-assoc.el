;;; pg-assoc.el --- Functions for associated buffers

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira

;; License:   GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Defines an empty mode inherited by modes of the associated buffers.
;; 

;;; Code:

(require 'proof-utils)

(define-derived-mode proof-universal-keys-only-mode fundamental-mode
  proof-general-name "Universal keymaps only"
  ;; Doesn't seem to supress TAB, RET
  (suppress-keymap proof-universal-keys-only-mode-map 'all)
  (proof-define-keys proof-universal-keys-only-mode-map
                     proof-universal-keys))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Return a list of associated buffers
;;

;;;###autoload
(defun proof-associated-buffers ()
  "Return a list of the associated buffers.
Some may be dead/nil."
  (list proof-goals-buffer
	proof-response-buffer
	proof-trace-buffer
	proof-thms-buffer))


;;;###autoload
(defun proof-associated-windows (&optional all-frames)
  "Return a list of the associated buffers windows.
Dead or nil buffers are not represented in the list. Optional
argument ALL-FRAMES has the same meaning than for
`get-buffer-window'."
  (let ((bufs (proof-associated-buffers))
	buf wins)
    (while bufs
      (setq buf (car bufs))
      (if (and buf (get-buffer-window-list buf nil all-frames))
	  (setq wins (append (get-buffer-window-list buf nil all-frames) wins)))
      (setq bufs (cdr bufs)))
    wins))


(defun proof-associated-buffer-p (b) (member b (proof-associated-buffers)))


(defun proof-filter-associated-windows (lw)
  "Remove windows of LW not displaying at least one associated buffer."
  (remove-if-not (lambda (w) (proof-associated-buffer-p (window-buffer w))) lw))


;;;###autoload
(defun proof-associated-frames ()
  "Return the list of frames displaying at least one associated buffer."
  (remove-if-not (lambda (f) (proof-filter-associated-windows (window-list f)))
		 (frame-list)))

(provide 'pg-assoc)
;;; pg-assoc.el ends here
