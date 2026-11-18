;;; guards.el --- Keep a sandboxed init away from shared resources -*- lexical-binding: t; -*-

;;; Commentary:

;; xdg/audit/run.sh loads this file before init.el.  The init is the real
;; one, so it would start a server, look up passwords and open network
;; connections.  sandbox-exec already denies the network and any write to
;; the real home directory; these stubs turn the remaining attempts into
;; logged no-ops, so that the init can finish.

;;; Code:

(let ((scratch (getenv "XDG_AUDIT_SCRATCH")))
  (unless (and scratch
               (string-prefix-p scratch (expand-file-name "~"))
               (string-prefix-p scratch
                                (expand-file-name user-emacs-directory)))
    (message "guards: HOME and the init directory must be inside %s" scratch)
    (kill-emacs 99)))

;; Servers and listeners.
(dolist (function '(server-start edit-server-start atomic-chrome-start-server
                    httpd-start))
  (advice-add function :override
              (lambda (&rest _)
                (message "guards: suppressed %s" function)
                nil)
              `((name . ,(intern (format "xdg-audit-%s" function))))))

;; The init makes the directory of its server socket when that is missing,
;; as it is while no Emacs runs.  run.sh denies every write there, so the
;; attempt is skipped as well.
(defconst xdg-audit-server-directory
  (format "/tmp/%s-emacs" (user-login-name))
  "Directory of the live server socket, which the sandbox denies.")

(dolist (function '(make-directory set-file-modes))
  (advice-add function :around
              (lambda (original file &rest arguments)
                (if (equal (directory-file-name (expand-file-name file))
                           xdg-audit-server-directory)
                    (progn (message "guards: left %s alone" file) nil)
                  (apply original file arguments)))
              `((name . ,(intern (format "xdg-audit-%s" function))))))

;; Network.
(define-advice make-network-process (:override (&rest args) xdg-audit)
  (signal 'file-error
          (list "guards: network disabled" (plist-get args :name))))
(define-advice url-retrieve (:override (url &rest _) xdg-audit)
  (message "guards: refused url-retrieve %s" url)
  nil)
(define-advice url-retrieve-synchronously (:override (url &rest _) xdg-audit)
  (message "guards: refused url-retrieve-synchronously %s" url)
  nil)

;; Long-lived subprocesses.
(define-advice make-process (:override (&rest args) xdg-audit)
  (signal 'file-error
          (list "guards: subprocesses disabled" (plist-get args :command))))

;; emacsclient could reach the live session.
(define-advice call-process (:around (original program &rest args) xdg-audit)
  (if (and (stringp program)
           (string-match-p "emacsclient" (file-name-nondirectory program)))
      1
    (apply original program args)))

;; The init looks passwords up while it loads.
(define-advice lookup-password (:override (&rest _) xdg-audit)
  "not-a-real-password")

;; This reads a file from ~/org, which the scratch home does not have.
(advice-add 'org-ext-update-team :around
            (lambda (original &rest args)
              (condition-case err
                  (apply original args)
                (error (message "guards: org-ext-update-team: %S" err) nil)))
            '((name . xdg-audit-org-ext-update-team)))

;; No prompt may block a batch run.
(setq use-dialog-box nil)
(define-advice yes-or-no-p (:override (&rest _) xdg-audit) nil)
(define-advice y-or-n-p (:override (&rest _) xdg-audit) nil)

(provide 'guards)

;;; guards.el ends here
