;;; selected.el --- Keymap for when region is active

;; Copyright (C) 2016--2017 Erik Sjöstrand
;; MIT License

;; Author: Erik Sjöstrand
;; URL: http://github.com/Kungsgeten/selected.el
;; Version: 1.01
;; Keywords: convenience
;; Package-Requires: ()

;;; Commentary:

;; When `selected-minor-mode' is active, the keybindings in `selected-keymap'
;; will be enabled when the region is active.  This is useful for commands that
;; operates on the region, which you only want keybound when the region is
;; active.
;;
;; `selected-keymap' has no default bindings.  Bind it yourself:
;;
;; (define-key selected-keymap (kbd "u") #'upcase-region)
;;
;; You can also bind keys specific to a major mode, by creating a keymap named
;; selected-<major-mode-name>-map:
;;
;; (setq selected-org-mode-map (make-sparse-keymap))
;; (define-key selected-org-mode-map (kbd "t") #'org-table-convert-region)
;;
;; There's also a global minor mode available: `selected-global-mode' if you
;; want selected-minor-mode in all buffers.

;;; Code:
(defvar selected-keymap (make-sparse-keymap)
  "Keymap for `selected-minor-mode'.  Add keys here that should be active when region is active.")

(defvar selected-minor-mode-override nil
  "Put keys in `selected-keymap' into `minor-mode-overriding-map-alist'?")

(define-minor-mode selected-region-active-mode
  "Meant to activate when region becomes active.  Not intended for the user.  Use `selected-minor-mode'."
  :keymap selected-keymap
  (if selected-region-active-mode
      (let* ((major-selected-map
              (eval (intern-soft (concat "selected-" (symbol-name major-mode) "-map"))))
             (map
              (if major-selected-map
                  (progn
                    (set-keymap-parent major-selected-map selected-keymap)
                    major-selected-map)
                selected-keymap)))
        (if selected-minor-mode-override
            (push `(selected-region-active-mode . ,map) minor-mode-overriding-map-alist)
          (setf (cdr (assoc 'selected-region-active-mode minor-mode-map-alist))
                map)))
    (setq minor-mode-overriding-map-alist
          (assq-delete-all 'selected-region-active-mode minor-mode-overriding-map-alist))))

(defun selected--on ()
  (selected-region-active-mode 1))

(defun selected-off ()
  "Disable bindings in `selected-keymap' temporarily."
  (interactive)
  (selected-region-active-mode -1))

;;;###autoload
(define-minor-mode selected-minor-mode
  "If enabled activates the `selected-keymap' when the region is active."
  :lighter " sel"
  (if selected-minor-mode
      (progn
        (add-hook 'activate-mark-hook #'selected--on)
        (add-hook 'deactivate-mark-hook #'selected-off))
    (remove-hook 'activate-mark-hook #'selected--on)
    (remove-hook 'deactivate-mark-hook #'selected-off)
    (selected-off)))

(defun selected--global-on-p ()
  "If `selected-global-mode' should activate in a new buffer."
  (unless (minibufferp)
    (selected-minor-mode 1)))

;;;###autoload
(define-globalized-minor-mode selected-global-mode
  selected-minor-mode
  selected--global-on-p)

(provide 'selected)
;;; selected.el ends here
