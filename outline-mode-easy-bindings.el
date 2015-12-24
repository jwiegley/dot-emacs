;; [OBSOLETE FOR OUTSHINE.EL, BECAUSE ALL FUNCTIONS AND KEYBINDINGS FROM THIS
;; LIBRARY HAVE BEEN MERGED INTO OUTSHINE.EL]

;; outline-mode-easy-bindings.el (2010-08-15)
;;
;; Outlines can be managed entirely with Meta + <arrow key>.
;;
;; Installation: Store this file as outline-mode-easy-bindings.el
;; somewhere in your load-path and create hooks for outline modes to
;; load this automatically, for example:

;;     (add-hook 'outline-mode-hook 'my-outline-easy-bindings)
;;     (add-hook 'outline-minor-mode-hook 'my-outline-easy-bindings)
;;
;;     (defun my-outline-easy-bindings ()
;;       (require 'outline-mode-easy-bindings nil t))

;; Copied from: http://emacswiki.org/emacs/OutlineMinorMode

(defun outline-body-p ()
  (save-excursion
    (outline-back-to-heading)
    (outline-end-of-heading)
    (and (not (eobp))
         (progn (forward-char 1)
                (not (outline-on-heading-p))))))

(defun outline-body-visible-p ()
  (save-excursion
    (outline-back-to-heading)
    (outline-end-of-heading)
    (not (outline-invisible-p))))

(defun outline-subheadings-p ()
  (save-excursion
    (outline-back-to-heading)
    (let ((level (funcall outline-level)))
      (outline-next-heading)
      (and (not (eobp))
           (< level (funcall outline-level))))))

(defun outline-subheadings-visible-p ()
  (interactive)
  (save-excursion
    (outline-next-heading)
    (not (outline-invisible-p))))

(defun outline-hide-more ()
  (interactive)
  (when (outline-on-heading-p)
    (cond ((and (outline-body-p)
                (outline-body-visible-p))
           (hide-entry)
           (hide-leaves))
          (t
           (hide-subtree)))))

(defun outline-show-more ()
  (interactive)
  (when (outline-on-heading-p)
    (cond ((and (outline-subheadings-p)
                (not (outline-subheadings-visible-p)))
           (show-children))
          ((and (not (outline-subheadings-p))
                (not (outline-body-visible-p)))
           (show-subtree))
          ((and (outline-body-p)
                (not (outline-body-visible-p)))
           (show-entry))
          (t
           (show-subtree)))))

(let ((map outline-mode-map))
  (define-key map (kbd "M-<left>") 'outline-hide-more)
  (define-key map (kbd "M-<right>") 'outline-show-more)
  (define-key map (kbd "M-<up>") 'outline-previous-visible-heading)
  (define-key map (kbd "M-<down>") 'outline-next-visible-heading)
  (define-key map (kbd "C-c J") 'outline-hide-more)
  (define-key map (kbd "C-c L") 'outline-show-more)
  (define-key map (kbd "C-c I") 'outline-previous-visible-heading)
  (define-key map (kbd "C-c K") 'outline-next-visible-heading))

(let ((map outline-minor-mode-map)) 
  (define-key map (kbd "M-<left>") 'outline-hide-more)
  (define-key map (kbd "M-<right>") 'outline-show-more)
  (define-key map (kbd "M-<up>") 'outline-previous-visible-heading)
  (define-key map (kbd "M-<down>") 'outline-next-visible-heading)
  (define-key map (kbd "C-c J") 'outline-hide-more)
  (define-key map (kbd "C-c L") 'outline-show-more)
  (define-key map (kbd "C-c I") 'outline-previous-visible-heading)
  (define-key map (kbd "C-c K") 'outline-next-visible-heading))

(provide 'outline-mode-easy-bindings)
