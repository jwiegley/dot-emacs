;; from shell: emacs --batch -l ./build.el -- repository-name package-file-name...

(defvar repository '(("marmalade"        . "http://marmalade-repo.org/packages/")
                     ("melpa"            . "http://melpa.milkbox.net/packages/")
                     ("melpa-stable"     . "http://melpa-stable.milkbox.net/packages/"))
  "List of repository to install org-trello's dependency from.")

(require 'package)
(package-initialize)

(setq package-user-dir (concat (file-name-directory (or (buffer-file-name) load-file-name default-directory)) ".elpa"))

(let* ((cli           (reverse command-line-args))
       (package-name  (car cli))
       (repo          (cadr cli))
       (package-file  (format "./%s" package-name))
       (repo-ref      (assoc repo repository)))
  (message "Installing '%s' using standard repository + '%s'" package-file repo)
  ;; install the repo asked for
  (add-to-list 'package-archives repo-ref)
  ;; refresh the list according to the repository installed
  (package-refresh-contents)
  ;; workaround
  (dolist (p '(elnode)) (package-install p))
  ;; install the file in the context
  (package-install-file package-file))

;; End
