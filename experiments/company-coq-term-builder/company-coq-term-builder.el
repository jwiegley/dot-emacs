(require 'dash)

(defun company-coq--cleanup-program (program)
  "Cleanup PROGRAM for display as partial extraction."
  (replace-regexp-in-string (regexp-quote "failwith \"AXIOM TO BE REALIZED\"")
                            "??" program t))

(defun company-coq-ask-prover-throw-errors (command)
  "Run COMMAND, and fail if it returns an error.
If UNDO-STATE is non-nil, go back to that Coq state before throwing."
  (let ((result (company-coq-ask-prover command)))
    (when (company-coq-error-message-p result)
      (error "Running %S failed with message %S" command result))
    result))

(defvar company-coq--extraction-busy nil
  "Whether the extraction view is currently busy.")

(defconst company-coq--extraction-command "Show Proof."
  "Command to show the current proof term.")

(defun company-coq--ask-prover-then-rewind (&rest cmds)
  "Run CMDS, then rewind to state before running them."
  (unless proof-shell-busy
    (-when-let* ((statenum (car (coq-last-prompt-info-safe))))
      (unwind-protect
          (let* ((proof-shell-eager-annotation-start nil)
                 (retval nil)) ;; Disable capture of urgent messages
            (dolist (cmd cmds retval)
              (setq retval (company-coq-ask-prover-throw-errors cmd))))
        (company-coq-ask-prover (format "BackTo %d." statenum))))))

(defun company-coq--extract-partial ()
  "Extract the current proof, plugging holes with _UNFINISHED_GOAL."
  (interactive)
  (unless company-coq--extraction-busy
    (setq company-coq--extraction-busy t)
    (unwind-protect
        (let* ((response (company-coq--ask-prover-then-rewind company-coq--extraction-command))
               (program (company-coq--cleanup-program response)))
          (company-coq--display-extraction program))
      (setq company-coq--extraction-busy nil))))

(defvar company-coq--extraction-buffer-name "*Proof term*")

(defun company-coq--display-extraction (extraction)
  "Display EXTRACTION in its own window."
  (with-current-buffer (get-buffer-create company-coq--extraction-buffer-name)
    (erase-buffer)
    (insert extraction)
    ;; (coq-mode) ; too slow
    (when proof-script-buffer
      (company-coq--fontify-buffer-with proof-script-buffer))
    (company-coq--setup-doc-buffer)
    (unless (get-buffer-window (current-buffer))
      (-when-let* ((script-buf proof-script-buffer)
                   (script-win (get-buffer-window script-buf)))
        (set-window-buffer (split-window-vertically) (current-buffer))))))

(defun company-coq-features/live-extraction--cleanup ()
  "Close the live extraction window and kill its buffer."
  (-when-let* ((win (get-buffer-window company-coq--extraction-buffer-name)))
    (delete-window win)))

(defun company-coq--extract-partial-in-bg ()
  "Update extraction buffer, ignoring errors if any."
  (condition-case err
      (company-coq--extract-partial)
    (error (company-coq-features/live-extraction--cleanup))))

(defun company-coq--extraction-hook-fn ()
  "Hook function to update extraction display."
  (unless (memq 'no-goals-display proof-shell-delayed-output-flags)
    (run-with-timer 0 nil #'company-coq--extract-partial-in-bg)))

(define-minor-mode company-coq-TermBuilder
  "Show terms as they are built in tactics mode."
  :lighter " 🐤—TB"
  (if company-coq-TermBuilder
      (progn
        (add-hook 'proof-shell-handle-delayed-output-hook #'company-coq--extraction-hook-fn))
    (company-coq-features/live-extraction--cleanup)
    (remove-hook 'proof-shell-handle-delayed-output-hook #'company-coq--extraction-hook-fn)))

(company-coq-TermBuilder)

(provide 'company-coq-term-builder)
