;;; lsp-haskell.el --- Haskell support for lsp-mode

;; Version: 1.0
;; Package-Requires: ((lsp-mode "3.0") (haskell-mode "1.0"))
;; Keywords: haskell
;; URL: https://github.com/emacs-lsp/lsp-haskell

(require 'haskell)
(require 'lsp-mode)

;; ---------------------------------------------------------------------
;; HaRe functions

(defun lsp-demote ()
  "Demote a function to the level it is used"
  (interactive)
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:demote"
   (vector `(:file ,(concat "file://" buffer-file-name)
             :pos  ,(lsp-point-to-position (point))))))

(defun lsp-duplicate-definition (newname)
  "Duplicate a definition"
  (interactive "sNew definition name: ")
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:dupdef"
   (vector `(:file ,(concat "file://" buffer-file-name)
             :pos  ,(lsp-point-to-position (point))
             :text ,newname))))

(defun lsp-if-to-case ()
  "Convert an if statement to a case statement"
  (interactive)
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:iftocase"
   (vector `(:file      ,(concat "file://" buffer-file-name)
             :start_pos ,(lsp-get-start-position)
             :end_pos   ,(lsp-get-end-position)))))

(defun lsp-lift-level ()
  "Lift a function to the top level"
  (interactive)
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:liftonelevel"
   (vector `(:file ,(concat "file://" buffer-file-name)
             :pos  ,(lsp-point-to-position (point))))))

(defun lsp-lift-to-top ()
  "Lift a function to the top level"
  (interactive)
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:lifttotoplevel"
   (vector `(:file ,(concat "file://" buffer-file-name)
             :pos  ,(lsp-point-to-position (point))))))

(defun lsp-delete-definition ()
  "Delete a definition"
  (interactive)
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:deletedef"
   (vector `(:file ,(concat "file://" buffer-file-name)
             :pos  ,(lsp-point-to-position (point))))))

(defun lsp-generalise-applicative ()
  "Generalise a monadic function to use applicative"
  (interactive)
  (lsp--cur-workspace-check)
  (lsp--send-execute-command
   "hare:genapplicative"
   (vector `(:file ,(concat "file://" buffer-file-name)
             :pos  ,(lsp-point-to-position (point))))))

;; ---------------------------------------------------------------------

(defun lsp-haskell--session-cabal-dir ()
  "Get the session cabal-dir."
  (let* ((cabal-file (haskell-cabal-find-file))
         (cabal-dir (if cabal-file
                        (file-name-directory cabal-file)
                      "." ;; no cabal file, use directory only
                      )))
    (progn
      (message "cabal-dir: %s" cabal-dir)
      cabal-dir)))

(defun lsp-haskell--get-root ()
  "TODO: use projectile directory"
  (let ((dir (lsp-haskell--session-cabal-dir)))
    (if (string= dir "/")
        (user-error (concat "Couldn't find cabal file, using:" dir))
      dir)))

;; ---------------------------------------------------------------------

;;----------------------------------------------------------------------
;; AZ: Not sure where this section should go, putting it here for now

;; AZ: This section based on/inspired by the intero 'intero-apply-suggestions' code, at
;; https://github.com/commercialhaskell/intero/blob/master/elisp/intero.el

(defun lsp-apply-commands ()
  "Prompt and apply any codeAction commands."
  (interactive)
  (if (null lsp-code-actions)
      (message "No actions to apply")
    (let ((to-apply
           (lsp--intero-multiswitch
            (format "There are %d suggestions to apply:" (length lsp-code-actions))
            (cl-remove-if-not
             #'identity
             (mapcar
              (lambda (suggestion)
                ;; (pcase (plist-get suggestion :type)
                ;;   (add-extension
                ;;    (list :key suggestion
                ;;          :title (concat "Add {-# LANGUAGE "
                ;;                         (plist-get suggestion :extension)
                ;;                         " #-}")
                ;;          :default t))
                ;;   (redundant-constraint
                ;;    (list :key suggestion
                ;;          :title (concat
                ;;                  "Remove redundant constraints: "
                ;;                  (string-join (plist-get suggestion :redundancies)
                ;;                               ", ")
                ;;                  "\n    from the "
                ;;                  (plist-get suggestion :signature))
                ;;          :default nil)))
                ;; (message "lsp-apply-command:suggestion command=%s"    (gethash "command" suggestion))
                ;; (message "lsp-apply-command:suggestion ommand=args%s" (gethash "arguments" suggestion))
                (list :key   (gethash "title" suggestion)
                      :title (gethash "title" suggestion)
                      :type  "codeAction"
                      :default t
                      :command suggestion)
                )
              lsp-code-actions)))))
      (if (null to-apply)
          (message "No changes selected to apply.")
        (let ((sorted (sort to-apply
                            (lambda (lt gt)
                              (let ((lt-line   (or (plist-get lt :line)   0))
                                    (lt-column (or (plist-get lt :column) 0))
                                    (gt-line   (or (plist-get gt :line)   0))
                                    (gt-column (or (plist-get gt :column) 0)))
                                (or (> lt-line gt-line)
                                    (and (= lt-line gt-line)
                                         (> lt-column gt-column))))))))
          ;; # Changes unrelated to the buffer
          (cl-loop
           for suggestion in sorted
           do ;; (message "lsp-apply-commands:suggestion=%s" suggestion)
              (pcase (plist-get suggestion :type)
                (otherwise
                 (lsp--execute-lsp-server-command suggestion))))
          ;; # Changes that do not increase/decrease line numbers
          ;;
          ;; Update in-place suggestions

          ;; # Changes that do increase/decrease line numbers
          ;;

          ;; Add extensions to the top of the file
          )))))

;; The following is copied directly from intero. I suspect it would be better to
;; have it in a dependency somewhere

(defun lsp--intero-multiswitch (title options)
  "Displaying TITLE, read multiple flags from a list of OPTIONS.
Each option is a plist of (:key :default :title) wherein:

  :key should be something comparable with EQUAL
  :title should be a string
  :default (boolean) specifies the default checkedness"
  (let ((available-width (window-total-width)))
    (save-window-excursion
      (lsp--intero-with-temp-buffer
        (rename-buffer (generate-new-buffer-name "multiswitch"))
        (widget-insert (concat title "\n\n"))
        (widget-insert (propertize "Hit " 'face 'font-lock-comment-face))
        (widget-create 'push-button :notify
                       (lambda (&rest ignore)
                         (exit-recursive-edit))
                       "C-c C-c")
        (widget-insert (propertize " to apply these choices.\n\n" 'face 'font-lock-comment-face))
        (let* ((me (current-buffer))
               (choices (mapcar (lambda (option)
                                  (append option (list :value (plist-get option :default))))
                                options)))
          (cl-loop for option in choices
                   do (widget-create
                       'toggle
                       :notify (lambda (widget &rest ignore)
                                 (setq choices
                                       (mapcar (lambda (choice)
                                                 (if (equal (plist-get choice :key)
                                                            (plist-get (cdr widget) :key))
                                                     (plist-put choice :value (plist-get (cdr widget) :value))
                                                   choice))
                                               choices)))
                       :on (concat "[x] " (plist-get option :title))
                       :off (concat "[ ] " (plist-get option :title))
                       :value (plist-get option :default)
                       :key (plist-get option :key)
                       :command (plist-get option :command)))
          (let ((lines (line-number-at-pos)))
            (select-window (split-window-below))
            (switch-to-buffer me)
            (goto-char (point-min)))
          (use-local-map
           (let ((map (copy-keymap widget-keymap)))
             (define-key map (kbd "C-c C-c") 'exit-recursive-edit)
             (define-key map (kbd "C-g") 'abort-recursive-edit)
             map))
          (widget-setup)
          (recursive-edit)
          (kill-buffer me)
          (mapcar (lambda (choice)
                    (plist-get choice :command))
                  (cl-remove-if-not (lambda (choice)
                                      (plist-get choice :value))
                                    choices)))))))

;; The following is copied directly from intero. I suspect it would be better to
;; have it in a dependency somewhere
(defmacro lsp--intero-with-temp-buffer (&rest body)
  "Run BODY in `with-temp-buffer', but inherit certain local variables from the current buffer first."
  (declare (indent 0) (debug t))
  `(let ((initial-buffer (current-buffer)))
     (with-temp-buffer
       (lsp--intero-inherit-local-variables initial-buffer)
       ,@body)))

;; The following is copied directly from intero. I suspect it would be better to
;; have it in a dependency somewhere
(defun lsp--intero-inherit-local-variables (buffer)
  "Make the current buffer inherit values of certain local variables from BUFFER."
  (let ((variables '(
                     ;; TODO: shouldn’t more of the above be here?
                     )))
    (cl-loop for v in variables do
             (set (make-local-variable v) (buffer-local-value v buffer)))))
;; ---------------------------------------------------------------------

(lsp-define-stdio-client lsp-haskell "haskell" #'lsp-haskell--get-root
			 '("hie" "--lsp" "-d" "-l" "/tmp/hie.log"))
        ;; '("lsp-hello"))

(provide 'lsp-haskell)
;;; lsp-haskell.el ends here
