(require 'lusty-explorer)
(require 'ido)

(ido-mode t)

(defun shk-init-lusty-display ()
  (let ((lusty--active-mode :buffer-explorer))
    (lusty-setup-completion-window)
    (lusty-update-completion-buffer)))

(defun shk-lusty-on-make-buffer-list ()
  (when (minibufferp)
    (let ((lusty--active-mode :buffer-explorer))
      (lusty-update-completion-buffer))))

(defadvice ido-exhibit (after shk-lusty-ido-post-command-hook activate)
  (when (minibufferp)
    (let ((lusty--active-mode :buffer-explorer)
          (lusty--wrapping-ido-p t))
      (lusty-update-completion-buffer))))

(add-hook 'ido-minibuffer-setup-hook 'shk-init-lusty-display)
(add-hook 'ido-make-buffer-list-hook 'shk-lusty-on-make-buffer-list)

;(remove-hook 'ido-minibuffer-setup-hook 'shk-init-lusty-display)
;(remove-hook 'ido-make-buffer-list-hook 'shk-lusty-on-make-buffer-list)
;(ad-deactivate 'ido-exhibit)

