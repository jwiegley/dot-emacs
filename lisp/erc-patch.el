;; This file make erc-scrolltobottom work again in Emacs 24.

(defun erc-display-line-1 (string buffer)
  "Display STRING in `erc-mode' BUFFER.
Auxiliary function used in `erc-display-line'.  The line gets filtered to
interpret the control characters.  Then, `erc-insert-pre-hook' gets called.
If `erc-insert-this' is still t, STRING gets inserted into the buffer.
Afterwards, `erc-insert-modify' and `erc-insert-post-hook' get called.
If STRING is nil, the function does nothing."
  (when string
    (with-current-buffer (or buffer (process-buffer erc-server-process))
      (let ((insert-position (or (marker-position erc-insert-marker)
                                 (point-max))))
        (let ((string string) ;; FIXME! Can this be removed?
              (buffer-undo-list t)
              (inhibit-read-only t))
          (unless (string-match "\n$" string)
            (setq string (concat string "\n"))
            (when (erc-string-invisible-p string)
              (erc-put-text-properties 0 (length string)
                                       '(invisible intangible) string)))
          (erc-log (concat "erc-display-line: " string
                           (format "(%S)" string) " in buffer "
                           (format "%s" buffer)))
          (setq erc-insert-this t)
          (run-hook-with-args 'erc-insert-pre-hook string)
          (if (null erc-insert-this)
              ;; Leave erc-insert-this set to t as much as possible.  Fran
              ;; Litterio <franl> has seen erc-insert-this set to nil while
              ;; erc-send-pre-hook is running, which should never happen.  This
              ;; may cure it.
              (setq erc-insert-this t)
            (save-excursion ;; to restore point in the new buffer
              (save-restriction
                (widen)
                (goto-char insert-position)
                (insert-before-markers string)
                ;; run insertion hook, with point at restored location
                (save-restriction
                  (narrow-to-region insert-position (point))
                  (run-hooks 'erc-insert-modify-hook)
                  (run-hooks 'erc-insert-post-hook)
                  (when erc-remove-parsed-property
                    (remove-text-properties (point-min) (point-max)
                                            '(erc-parsed nil))))))))
        (erc-update-undo-list (- (or (marker-position erc-insert-marker)
                                     (point-max))
                                 insert-position)))
       ;;; this line and only this line was added --v
      (run-hooks 'erc-display-post-hook))))

(defvar erc-display-post-hook nil
  "New hook!")

(defun damd-erc-display-post-hook ()
  (let ((windows (get-buffer-window-list (current-buffer) nil 'visible)))
    (dolist (w windows)
      (when (>= (point) erc-input-marker)
        (with-selected-window w
          (recenter -1))))))
(add-hook 'erc-display-post-hook 'damd-erc-display-post-hook)

(defun damd-erc-send-post-hook ()
  (when (>= (point) erc-input-marker)
    (goto-char (point-max))
    (widen)
    (recenter -1)))
(add-hook 'erc-send-post-hook 'damd-erc-send-post-hook)

(defun damd-window-configuration-change-hook ()
  (when (and (eq major-mode 'erc-mode)
             (>= (point) erc-input-marker))
    (recenter -1)))

(add-hook 'window-configuration-change-hook
          'damd-window-configuration-change-hook)

(provide 'erc-patch)
