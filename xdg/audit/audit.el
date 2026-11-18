;;; audit.el --- Find variables that still point into the init directory -*- lexical-binding: t; -*-

;;; Commentary:

;; xdg/audit/run.sh loads this file in a batch Emacs whose home directory
;; is a scratch copy.  It loads early-init.el and init.el the way an
;; interactive start would, loads every feature a `use-package' form names,
;; and then looks at every variable.  A variable whose value names a path
;; inside the init directory is an offender unless it is on the lists below.
;;
;; Each offender is printed as "OFFENDER<TAB>variable<TAB>library<TAB>paths".
;; The exit status is 1 if there is an offender or a form of init.el failed.
;;
;; The scan cannot see a path that is a symbol or a function resolved on
;; use, a relative path, or a value inside a vector, hash table or closure.

;;; Code:

(require 'cl-lib)

(defconst xdg-audit-allowed-paths
  '("lisp" "snippets" "prompts" "certs" "auctex/style"
    "abbrevs.el" "settings.el" "runshell" "init.el" "early-init.el" "init.org"
    "eshell/alias" "eshell/login" "eshell/profile"
    "nix-packages" "nix-packages.el")
  "Configuration that Emacs reads, relative to the init directory.
A path is allowed if it equals an entry or lies beneath one.")

(defconst xdg-audit-allowed-variables
  '(;; Emacs's own record of where the configuration is.
    user-emacs-directory user-init-file early-init-file default-directory
    command-line-default-directory custom-file custom-theme-directory
    user-lisp-directory startup--xdg-config-default
    startup--xdg-config-home-emacs startup--original-eln-load-path
    ;; Bookkeeping, not settings.
    load-path load-history load-file-name current-load-list
    custom-current-group-alist command-line-args command-line-args-left
    ;; Configuration read from the checkout.
    eshell-directory-name aya-persist-snippets-dir
    dired-ext-directory-groups magit-user-githook-file
    ;; Written only by an explicit command, as settings a person chose.
    calc-settings-file diary-file purpose-default-layout-file
    purpose-layout-dirs TeX-style-private TeX-style-path
    ;; An obsolete constant; `treemacs-last-error-persist-file' replaced it.
    treemacs--last-error-persist-file)
  "Variables that may point into the init directory.")

(defconst xdg-audit-history-regexp
  (rx (or (seq (or "-history" "-ring") string-end)
          (seq string-start
               (or "recentf-list" "save-place-alist" "dired-buffers"
                   "project--list" "projectile-known-projects"
                   "projectile-known-projects-on-file")
               string-end)))
  "Variables that only remember paths a session has visited.")

(defun xdg-audit--prefixes (root)
  "Return the spellings under which a path counts as inside ROOT."
  (let* ((absolute (file-name-as-directory (expand-file-name root)))
         (home (file-name-as-directory (expand-file-name "~")))
         (prefixes (list absolute)))
    (cond ((string-prefix-p "/private/" absolute)
           (push (substring absolute (length "/private")) prefixes))
          ((string-match-p "\\`/\\(tmp\\|var\\)/" absolute)
           (push (concat "/private" absolute) prefixes)))
    (dolist (prefix (copy-sequence prefixes))
      (when (string-prefix-p home prefix)
        (push (concat "~/" (substring prefix (length home))) prefixes)))
    prefixes))

(defun xdg-audit--inside-p (value prefixes)
  "Return non-nil if VALUE is a path at or below one of PREFIXES."
  (and (stringp value)
       (< (length value) 4096)
       (cl-some (lambda (prefix)
                  (or (string-prefix-p prefix value)
                      (string= value (substring prefix 0 -1))))
                prefixes)))

(defun xdg-audit--paths (value prefixes)
  "Return the paths in VALUE that lie inside PREFIXES.
VALUE may be a string, a list of strings, or an alist with strings as
keys or values.  Nothing deeper is examined."
  (cond
   ((xdg-audit--inside-p value prefixes) (list value))
   ((and (consp value) (proper-list-p value))
    (let (found)
      (dolist (element (take 2000 value))
        (dolist (candidate (if (consp element)
                               (list (car element) (cdr element)
                                     (car-safe (cdr element)))
                             (list element)))
          (when (xdg-audit--inside-p candidate prefixes)
            (push candidate found))))
      (nreverse found)))
   ((consp value)
    (cl-remove-if-not (lambda (candidate)
                        (xdg-audit--inside-p candidate prefixes))
                      (list (car value) (cdr value))))))

(defun xdg-audit--relative (path prefixes)
  "Return PATH relative to the init directory named by PREFIXES."
  (or (cl-some (lambda (prefix)
                 (cond ((string-prefix-p prefix path)
                        (substring path (length prefix)))
                       ((string= path (substring prefix 0 -1)) "")))
               prefixes)
      path))

(defun xdg-audit--allowed-path-p (path prefixes)
  "Return non-nil if PATH is configuration on `xdg-audit-allowed-paths'."
  (let ((relative (xdg-audit--relative path prefixes)))
    (cl-some (lambda (allowed)
               (or (string= relative allowed)
                   (string-prefix-p (concat allowed "/") relative)))
             xdg-audit-allowed-paths)))

(defun xdg-audit-offenders (root)
  "Return (VARIABLE LIBRARY PATHS) for each offender under ROOT."
  (let ((prefixes (xdg-audit--prefixes root))
        offenders)
    (mapatoms
     (lambda (symbol)
       (when (and (not (keywordp symbol))
                  (default-boundp symbol)
                  (not (memq symbol xdg-audit-allowed-variables))
                  (not (string-match-p xdg-audit-history-regexp
                                       (symbol-name symbol))))
         (let ((paths (cl-remove-if
                       (lambda (path)
                         (xdg-audit--allowed-path-p path prefixes))
                       (xdg-audit--paths (default-value symbol) prefixes))))
           (when paths
             (push (list symbol
                         (let ((file (symbol-file symbol 'defvar)))
                           (if file (file-name-nondirectory file) "-"))
                         (mapcar (lambda (path)
                                   (concat "<init>/"
                                           (xdg-audit--relative path prefixes)))
                                 (take 6 paths)))
                   offenders))))))
    (sort offenders (lambda (a b) (string< (car a) (car b))))))

(defun xdg-audit--forms (file)
  "Return the top-level forms of FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (let (forms)
      (condition-case nil
          (while t
            (push (read (current-buffer)) forms))
        (end-of-file nil))
      (nreverse forms))))

(defun xdg-audit-load (file)
  "Evaluate FILE one form at a time; return (FORMS . FAILED) as counts.
One failing form therefore cannot hide the forms after it."
  (let ((load-file-name file)
        (load-true-file-name file)
        (load-in-progress t)
        (forms (xdg-audit--forms file))
        (failed 0))
    (dolist (form forms)
      (condition-case err
          (eval form t)
        (error
         (setq failed (1+ failed))
         (message "audit: FAILED %s: %S"
                  (truncate-string-to-width (format "%S" form) 70)
                  err))))
    (cons (length forms) failed)))

(defun xdg-audit--features (file)
  "Return the feature named by each `use-package' form in FILE."
  (let (names)
    (cl-labels ((walk (form)
                  (when (and (consp form) (proper-list-p form))
                    (when (and (eq (car form) 'use-package)
                               (symbolp (cadr form))
                               (not (plist-get (cddr form) :disabled)))
                      (push (cadr form) names))
                    (mapc #'walk form))))
      (mapc #'walk (xdg-audit--forms file)))
    (nreverse names)))

(defun xdg-audit--run-hook (hook)
  "Run the functions on HOOK one at a time, logging errors."
  (dolist (function (let ((value (and (boundp hook) (symbol-value hook))))
                      (if (functionp value) (list value) value)))
    (unless (eq function t)
      (condition-case err
          (funcall function)
        (error (message "audit: %s: %S" hook err)))))
  (set hook nil))

(defvar xdg-audit-selftest-file nil
  "A path inside the init directory, set only by the self-test.")

(defun xdg-audit--selftest ()
  "Plant a stray variable and a stray file for the audit to find."
  (setq xdg-audit-selftest-file
        (expand-file-name "selftest-state" user-emacs-directory))
  (write-region "" nil xdg-audit-selftest-file nil 'silent))

(defun xdg-audit-main ()
  "Load the init, force every package to load, and report offenders."
  (let ((early (expand-file-name "early-init.el" user-emacs-directory))
        (init (expand-file-name "init.el" user-emacs-directory))
        (guards (expand-file-name "guards.el"
                                  (file-name-directory load-file-name)))
        (forms 0)
        (failed 0)
        (loaded 0)
        (refused 0))
    ;; An interactive start loads early-init.el before anything else.
    (when (file-exists-p early)
      (load early nil t))
    (load guards nil t)
    ;; Forms that test `noninteractive' or `window-system' (savehist,
    ;; persistent-scratch, the server) must take their interactive branch.
    (let ((noninteractive nil)
          (window-system 'ns))
      (setq user-init-file init)
      (let ((counts (xdg-audit-load init)))
        (setq forms (car counts)
              failed (cdr counts)))
      (mapc #'xdg-audit--run-hook
            '(after-init-hook emacs-startup-hook window-setup-hook))
      (dolist (feature (xdg-audit--features init))
        (unless (featurep feature)
          (condition-case nil
              (with-timeout (30 (setq refused (1+ refused)))
                (let ((inhibit-message t))
                  (require feature))
                (setq loaded (1+ loaded)))
            (error (setq refused (1+ refused)))))))
    (when (equal (getenv "XDG_AUDIT_SELFTEST") "1")
      (xdg-audit--selftest))
    (message "audit: %d forms, %d failed; %d more features loaded, %d would not; %d features in all"
             forms failed loaded refused (length features))
    (let ((offenders (xdg-audit-offenders user-emacs-directory)))
      (dolist (offender offenders)
        (princ (format "OFFENDER\t%s\t%s\t%S\n"
                       (nth 0 offender) (nth 1 offender) (nth 2 offender))))
      (princ (format "audit: %d offenders, %d failed forms\n"
                     (length offenders) failed))
      ;; Leave through `kill-emacs', so that exit hooks write their files.
      (kill-emacs (if (or offenders (> failed 0)) 1 0)))))

(when noninteractive
  (xdg-audit-main))

;;; audit.el ends here
