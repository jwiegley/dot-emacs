;; cmake-font-lock-screenshot-setup.el --- prepare Emacs for screenshot.

;; Usage:
;;
;;   emacs -q -l cmake-font-lock-screenshot-setup.el
;;
;;   Take screenshot. OS X: Cmd-Shift-4 SPC click on window.

(setq inhibit-startup-screen t)

(blink-cursor-mode -1)

(defvar cmake-font-lock-screenshot-setup-file-name
  (or load-file-name
      (buffer-file-name)))

(let ((dir (file-name-directory cmake-font-lock-screenshot-setup-file-name)))
  (load (concat dir "../cmake-font-lock.el"))
  (cmake-font-lock-set-signature "my_get_dirs" '(:var))
  ;; Note: Needs cmake-mode.
  (load (concat dir "../../../lisp/cmake-mode.el"))
  (find-file (concat dir "Example.cmake")))

(cmake-mode)
(cmake-font-lock-activate)

(set-frame-size (selected-frame) 80 30)

(goto-char (point-max))

(message "")

;; cmake-font-lock-screenshot-setup.el ends here
