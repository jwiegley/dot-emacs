;; emacs -Q --batch -nw -l ./install.el -- <repo>

(defvar repository '(("marmalade"        . "http://marmalade-repo.org/packages/")
                     ("melpa"            . "http://melpa.milkbox.net/packages/")
                     ("melpa-stable"     . "http://melpa-stable.milkbox.net/packages/"))
  "List of repository to install org-trello's dependency from.")

(require 'package)
(package-initialize)

(let* ((cli           (reverse command-line-args))
       (repo          (car cli))
       (repo-ref      (assoc repo repository)))
  (message "Installing 'org-trello' using standard repository + '%s'" repo)
  (add-to-list 'package-archives repo-ref)
  (package-refresh-contents)
  ;; install needed deps (not required or problematic)
  (mapc (lambda (p) (package-install p)) '(org elnode org-trello)))

;; end
