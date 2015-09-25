;;; pg-assoc.el --- Functions for associated buffers
;;
;; Copyright (C) 1994-2008, 2010 LFCS Edinburgh.
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;; Commentary:
;;
;; Defines an empty mode inherited by modes of the associated buffers.
;; 

;;; Code:

(require 'proof-utils)

(eval-and-compile ; defines proof-universal-keys-only-mode-map at compile time
  (define-derived-mode proof-universal-keys-only-mode fundamental-mode
    proof-general-name "Universal keymaps only"
    ;; Doesn't seem to supress TAB, RET
    (suppress-keymap proof-universal-keys-only-mode-map 'all)
    (proof-define-keys proof-universal-keys-only-mode-map
		       proof-universal-keys)))

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
(defun proof-associated-windows ()
  "Return a list of the associated buffers windows.
Dead or nil buffers are not represented in the list."
  (let ((bufs (proof-associated-buffers))
	buf wins)
    (while bufs
      (setq buf (car bufs))
      (if (and buf (get-buffer-window buf))
	  (setq wins (cons (get-buffer-window buf) wins)))
      (setq bufs (cdr bufs)))
    wins))


(defun proof-associated-buffer-p (b) (member b (proof-associated-buffers)))


(defun proof-filter-associated-windows (lw)
  "Remove windows of LW not displaying at least one associated buffer."
  (remove-if-not (lambda (w) (proof-associated-buffer-p (window-buffer w))) lw))

(defun proof-find-all-associated-windows ()
  "Return the list of windows displaying an associated buffer."
  (proof-filter-associated-windows (window-list-1 nil nil t)))

(defun proof-find-all-associated-frames ()
  "Return the list of frames displaying at least one associated buffer."
  (remove-if-not (lambda (f) (proof-filter-associated-windows (window-list f)))
		 (frame-list)))

(provide 'pg-assoc)
;;; pg-assoc.el ends here
