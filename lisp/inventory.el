(defun sort-package-declarations ()
  (interactive)
  (cl-flet ((next-use-package
             () (if (re-search-forward "^(use-package " nil t)
                    (goto-char (match-beginning 0))
                  (goto-char (point-max)))))
    (sort-subr
     nil
     #'next-use-package
     #'(lambda ()
         (goto-char (line-end-position))
         (next-use-package))
     #'(lambda ()
         (re-search-forward "(use-package \\([A-Za-z0-9_+-]+\\)")
         (match-string 1)))))

(defmacro on (f g) `(lambda (x y) (,f (,g x) (,g y))))

(defun sort-on (seq predicate accessor)
  "Sort SEQ using PREDICATE applied to values returned by ACCESSOR.
This implements the so-called Schwartzian transform, which has
the performance advantage of applying ACCESSOR at most once per
element in the list, as opposed to using `sort' with a PREDICATE
that applies the ACCESSOR.
Note: this function is only a win over `sort' if ACCESSOR is
compute-intensive; otherwise, it uses more intermediate cons
cells than regular `sort', and so represents a memory for CPU
tradeoff."
  (mapcar #'cdr (sort (mapcar #'(lambda (x) (cons (funcall accessor x) x)) seq)
                      #'(lambda (x y) (funcall predicate (car x) (car y))))))

(defun sort-on* (seq predicate accessor)
  "Sort SEQ using PREDICATE applied to values returned by ACCESSOR.
This is a destructive version of `sort-on', which attempts to
reuse storage as much as possible."
  (let ((seq2 seq))
    (while seq2
      (setcar seq2 (cons (funcall accessor (car seq2)) (car seq2)))
      (setq seq2 (cdr seq2))))
  (setq seq (sort* seq #'(lambda (x y) (funcall predicate (car x) (car y)))))
  (let ((seq2 seq))
    (while seq2
      (setcar seq2 (cdar seq2))
      (setq seq2 (cdr seq2)))
    seq))

(defun package-inventory (&optional conversions builtin ignored)
  (interactive)
  (let ((pkgs (make-hash-table :test #'equal))
        (feature-names (make-hash-table :test #'equal)))
    (cl-macrolet
        ((with-package
          (name &rest forms)
          `(let* ((pkg-name (gethash ,name feature-names ,name))
                  (pkg (gethash pkg-name pkgs (list pkg-name nil nil))))
             (let ((result (progn ,@forms)))
               (if result
                   (puthash pkg-name
                            (list (nth 0 pkg)
                                  (nth 1 pkg)
                                  (cons result (nth 2 pkg))) pkgs)
                 (remhash pkg-name pkgs))))))

      (dolist (conv conversions)
        (dolist (name (cdr conv))
          (puthash name (car conv) feature-names)))

      (dolist (dir '("lib" "site-lisp" "override" "lisp"))
        (dolist (file (directory-files-recursively
                       (expand-file-name dir user-emacs-directory)
                       "\\.el\\'" nil))
          (pcase (dired-make-relative file user-emacs-directory)
            ((and (pred (string-match "\\`\\([a-z-]+/\\([^/]+?\\)\\)\\.el")) file)
             (puthash (match-string 2 file)
                      (list (match-string 1 file) t '(:installed)) pkgs))
            ((and (pred (string-match "\\`\\([a-z-]+/\\([^/]+?\\)\\)/")) file)
             (puthash (match-string 2 file)
                      (list (match-string 1 file) nil '(:installed)) pkgs)))))

      (dolist (pkg builtin) (with-package pkg :installed))

      (dolist (file
               (list (expand-file-name "init.el" user-emacs-directory)
                     (expand-file-name "dot-gnus.el" user-emacs-directory)
                     (expand-file-name "dot-org.el" user-emacs-directory)))
        (with-temp-buffer
          (insert-file-contents file)
          (goto-char (point-min))
          (while (re-search-forward "(use-package \\([A-Za-z0-9_+-]+\\)" nil t)
            (with-package (match-string 1) :referenced))))

      (with-temp-buffer
        (let ((default-directory user-emacs-directory))
          (call-process "git" nil (current-buffer) nil "remote"))
        (goto-char (point-min))
        (while (re-search-forward "^ext/\\(.+\\)" nil t)
          (with-package (match-string 1) :external)))

      (dolist (pkg ignored) (with-package pkg))

      (with-current-buffer (get-buffer-create "*inventory*")
        (cd user-emacs-directory)
        (delete-region (point-min) (point-max))
        (let (alist)
          (maphash #'(lambda (key value)
                       (setq alist (cons (cons key value) alist))) pkgs)
          (pcase-dolist (`(,key . ,value)
                         (sort-on alist #'string-lessp #'car))
            (let ((keys (nth 2 value)))
              (if (memq :installed keys)
                  (if (memq :referenced keys)
                      ;; (unless (memq :external keys)
                      ;;   (insert ";; no external: " key ?\n ?\n))
                      t
                    (insert "(use-package " key ?\n
                            "  ;; " "(shell-command \""
                            (if (nth 1 value)
                                (concat "rm -f " (nth 0 value) ".el*")
                              (concat "rm -fr " (nth 0 value)))
                            "\")" ?\n)
                    (when (memq :external keys)
                      (insert "  ;; (shell-command \"git remote rm ext/"
                              key "\")" ?\n))
                    (insert "  :disabled t")
                    (unless (nth 1 value)
                      (insert ?\n "  :load-path \"" (nth 0 value) "\""))
                    (insert ")" ?\n ?\n))
                (when (memq :referenced keys)
                  (insert ";; referenced: " key ?\n ?\n))
                (when (memq :external keys)
                  (insert ";; (shell-command \"git remote rm ext/" key "\")"
                          ?\n ?\n))))))
        (emacs-lisp-mode)
        (display-buffer (current-buffer))))))

(defun inventory ()
  (interactive)
  (package-inventory
   '(
     ("ProofGeneral" "proof-site" "coq" "pg-user")
     ("agda" "agda-input" "agda2-mode")
     ("auctex" "tex-site" "latex" "texinfo" "preview")
     ("bbdb" "bbdb-com")
     ("bookmark-plus" "bookmark+")
     ("company-mode" "company")
     ("dash-el" "dash")
     ("debbugs" "debbugs-gnu")
     ("diffview-mode" "diffview")
     ("dircmp-mode" "dircmp")
     ("docker-el" "docker" "docker-images")
     ("emacs-async" "async")
     ("emacs-calfw" "calfw" "calfw-cal" "calfw-org")
     ("emacs-ctable" "ctable")
     ("emacs-deferred" "deferred")
     ("emacs-epc" "epc")
     ("emacs-git-messenger" "git-messenger")
     ("emacs-request" "request")
     ("emacs-web" "web")
     ("expand-region-el" "expand-region")
     ("f-el" "f")
     ("flx" "flx-ido")
     ("fold-this-el" "fold-this")
     ("fuzzy-el" "fuzzy")
     ("gh-el" "gh")
     ("git-annex-el" "git-annex")
     ("git-wip" "git-wip-mode")
     ("github-issues-el" "github-issues")
     ("haskell-config" "haskell-edit")
     ("haskell-mode" "haskell-mode-autoloads")
     ("helm" "helm-config" "helm-buffers" "helm-files" "helm-grep" "helm-match-plugin" "helm-mode" "helm-multi-match")
     ("ht-el" "ht")
     ("ipa-el" "ipa")
     ("liquid-types-el" "liquid-types")
     ("lusty-emacs" "lusty-explorer")
     ("magit" "magit" "magit-commit")
     ("multifiles-el" "multifiles")
     ("multiple-cursors-el" "multiple-cursors")
     ("navi" "navi-mode")
     ("popup-el" "popup")
     ("popwin-el" "popwin")
     ("projectile" "projectile" "helm-projectile")
     ("s-el" "s")
     ("slime" "slime" "hyperspec")
     ("smart-forward-el" "smart-forward")
     ("smartparens" "smartparens" "smartparens-config")
     ("tramp" "tramp-sh")
     ("yari-with-buttons" "yari")
     )
   '("align" "abbrev" "allout" "browse-url" "cc-mode" "compile"
     "cus-edit" "diff-mode" "dired" "dired-x" "edebug" "ediff"
     "edit-server" "eldoc" "elint" "em-unix" "epa" "erc" "ert"
     "eshell" "etags" "eww" "flyspell" "grep" "gud" "hippie-exp"
     "ibuffer" "ido" "ielm" "image-file" "info" "isearch"
     "lisp-mode" "message" "midnight" "mule" "outline" "paren"
     "ps-print" "recentf" "smerge-mode" "whitespace" "autorevert"
     "bookmark" "ispell" "nroff-mode" "nxml-mode" "sh-script"
     "testcover" "winner" "hi-lock" "hilit-chg" "hl-line"
     "info-look"

     "gnus-demon"
     "gnus-dired"
     "gnus-group"
     "gnus-sum"
     "mml"
     "nnir"
     "smedl-mode"
     )
   '("use-package"
     "dot-gnus" "dot-org"
     "ledger-mode"
     "sage"
     "browse-kill-ring")))

(provide' inventory)
