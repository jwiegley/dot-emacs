(require 'comint)
(require 'notify)

(defcustom yesod-devel-directory
  nil
  "Default directory to prompt for for yesod devel'ing.")

(defcustom yesod-devel-command
  "yesod devel"
  "Default command to run for yesod devel'ing.")

(defun yesod-devel-mode ()
  "Yesod devel mode."
  (interactive)
  (setq major-mode 'yesod-devel-mode
        mode-name "yesod devel"
        mode-line-process '(":%s"))
  (set (make-local-variable 'comint-output-filter-functions)
       '(ansi-color-process-output
         comint-postoutput-scroll-to-bottom
         comint-truncate-buffer
         yesod-devel-filter)))

(defun yesod-devel-filter (input)
  (when (string-match "Devel application launched: " input)
    (message "yesod-devel: Restarted.")
    (notify "yesod devel" "Restarted."))
  (when (string-match "Stopping development server..." input)
    (message "yesod-devel: Recompiling…")
    (notify "yesod devel" "Recompiling…")))

(defun run-yesod-devel ()
  (interactive)
  (let ((path (read-from-minibuffer "Directory: " (if yesod-devel-directory
                                                      yesod-devel-directory
                                                    default-directory)))
        (command (read-from-minibuffer "Command: " yesod-devel-command)))
    (shell (get-buffer-create "*yesod-devel*"))
    (with-current-buffer "*yesod-devel*"
      (yesod-devel-mode)
      (insert "cd " path)
      (comint-send-input nil t)
      (insert command)
      (comint-send-input nil t)
      (erase-buffer))))

(provide 'yesod-devel-mode)
