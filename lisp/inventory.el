(eval-when-compile
  (require 'cl))
(require 'anaphora)

(defsubst sort-on (seq predicate accessor)
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

(defun sort-package-declarations ()
  (interactive)
  (save-excursion
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
           (match-string 1))))))

(defsubst modhash (key table f)
  (let ((value (gethash key table)))
    (puthash key (funcall f value) table)))

(defun alist-put (alist &rest pairs)
  (dolist (pair pairs)
    (when pair
      (let* ((key (car pair))
             (value (cdr pair))
             (entry (assq key alist)))
        (if entry
            (unless (equal (cdr entry) value)
              (display-warning
               'inventory
               (format "%s: overwriting %s with %s" key (cdr entry) value)
               :error))
          (setq alist (cons (cons key value) alist))))))
  alist)

(defun inventory-alist ()
  (let ((pkgs (make-hash-table :test #'equal)))
    ;; 1. git remotes
    ;; (with-temp-buffer
    ;;   (shell-command "git remote" (current-buffer))
    ;;   (goto-char (point-min))
    ;;   (while (re-search-forward "^ext/\\(.+\\)" nil t)
    ;;     (let* ((pkg (match-string 1))
    ;;            (name (concat "ext/" pkg))
    ;;            (url (substring
    ;;                  (shell-command-to-string
    ;;                   (format "git remote get-url %s" name)) 0 -1)))
    ;;       (puthash pkg
    ;;                (alist-put nil
    ;;                           (cons 'remote url)
    ;;                           (cons 'remote-name name)) pkgs))))

    ;; 2. subdirectories
    (dolist (topdir '("lisp"))
      (let ((path (expand-file-name topdir user-emacs-directory)))
        (dolist (entry (directory-files path t nil t))
          (let ((base (file-name-nondirectory entry)))
            (unless (string-match
                     "\\(\\`\\.\\.?\\|\\.\\(elc\\|org\\)\\)\\'" base)
              (modhash
               (replace-regexp-in-string "\\.el\\'" "" base) pkgs
               (lambda (value)
                 (alist-put value
                            (cons 'path
                                  (concat topdir "/" base))))))))))

    ;; 3. MANIFEST.csv
    ;; (with-temp-buffer
    ;;   (insert-file-contents-literally
    ;;    (expand-file-name "MANIFEST.csv" user-emacs-directory))
    ;;   (goto-char (point-min))
    ;;   (while (re-search-forward
    ;;           "^\\(.*?\\),\\(.*?\\),\\(.*?\\),\\(.*?\\),\\(.*?\\)$" nil t)
    ;;     (let* ((name (match-string 1))
    ;;            (dir (match-string 2))
    ;;            (type (match-string 3))
    ;;            (origin (match-string 4))
    ;;            (options (match-string 5))
    ;;            (path (concat dir "/" name))
    ;;            (update
    ;;             (pcase type
    ;;               ("subtree" (format "git pulltree %s/%s" dir name))
    ;;               ("file" (format "curl -s -S -o %s/%s %s" dir name origin))
    ;;               ("submodule"
    ;;                (format "git --git-dir=%s/%s fetch --no-tags"
    ;;                        dir name)))))
    ;;       (modhash
    ;;        (replace-regexp-in-string "\\.el\\'" "" name) pkgs
    ;;        (lambda (value)
    ;;          (alist-put value
    ;;                     (cons 'manifest-path path)
    ;;                     (cons 'manifest-type type)
    ;;                     (cons 'manifest-origin origin)
    ;;                     (cons 'manifest-options options)
    ;;                     (and update
    ;;                          (cons 'manifest-update update))))))))

    ;; 4. use-package declarations
    (dolist (file '("init.el" "dot-org.el" "dot-gnus.el"))
      (with-temp-buffer
        (insert-file-contents
         (expand-file-name file user-emacs-directory))
        (goto-char (point-min))
        (while (re-search-forward "^(use-package \\([A-Za-z0-9_+-]+\\)" nil t)
          (let* ((beg (match-beginning 0))
                 (local-end (match-end 0))
                 (name (match-string 1))
                 (entry (and (goto-char beg)
                             (read (current-buffer))))
                 (end (progn
                        (goto-char beg)
                        (forward-sexp)
                        (point)))
                 (load-paths (plist-get entry :load-path))
                 (path (cond
                        ((and load-paths
                              (listp load-paths)
                              (cl-every #'stringp load-paths))
                         (car load-paths))
                        ((stringp load-paths)
                         load-paths)))
                 (load-path-re "\\`\\(site-lisp\\|lisp\\|lib\\)/\\([^/]+\\)")
                 (key (if (and path (string-match load-path-re path))
                          (let* ((key (match-string 2 path))
                                 (entry (gethash key pkgs))
                                 (pkg-name (alist-get 'use-package-name entry)))
                            (if (or (null entry)
                                    (null pkg-name)
                                    (string= name pkg-name))
                                key
                              name))
                        name)))
            (unless (aif (locate-library name)
                         (and (string-match "/share/emacs/[0-9.]+/lisp" it)
                              (not (string-match "/site-lisp/elpa/" it))))
              (modhash key pkgs
                       (lambda (value)
                         (alist-put value
                                    (cons 'use-package-name name)
                                    (and load-paths
                                         (cons 'use-package-load-path
                                               load-paths))))))
            (goto-char local-end)))))
    ;; 5. overrides.nix
    (dolist (file '("~/src/nix/config/emacs.nix"))
      (with-temp-buffer
        (insert-file-contents file)
        (goto-char (point-min))
        (forward-line 2)
        (while (not (looking-at "^\\s-*\\]"))
          (when (looking-at
                 "^\\s-+\\([a-zA-Z0-9_-]+\\)\\(?: +# +\\(.+?\\)\\)?$")
            (let* ((aliases (aif (match-string 2)
                                 (split-string it "\\s-+")))
                   (names (or aliases (list (match-string 1)))))
              (dolist (name names)
                (modhash name pkgs
                         (lambda (value)
                           (alist-put value (cons 'nixpkgs-name name)))))))
          (forward-line))))

    (with-temp-buffer
      (insert "(\n")
      (maphash
       (lambda (key value)
         (let ((internal
                (let ((opts (alist-get 'manifest-options value))
                      (origin (alist-get 'manifest-origin value))
                      (type (alist-get 'manifest-type value))
                      (path (alist-get 'path value)))
                  (or (and opts (string-match "mirror-only" opts))
                      (and origin (string-match "unknown" origin))
                      (member type '("part" "internal" "personal"))
                      path)))
               errs)
           (cl-flet ((report (err) (setq errs (cons err errs))))
             (let ((fields (if internal
                               '(;; manifest-path
                                 ;; manifest-type
                                 ;; manifest-origin
                                 ;; remote
                                 ;; remote-name
                                 )
                             '(use-package-name
                               nixpkgs-name
                               ;; manifest-path
                               ;; manifest-type
                               ;; manifest-origin
                               ;; path
                               ;; remote
                               ;; remote-name
                               ))))
               (when (or internal
                         (string= key "use-package")
                         (and (alist-get 'manifest-type value)
                              (string= (alist-get 'manifest-type value) "file")))
                 (setq fields (delq 'remote (delq 'remote-name fields))))
               (when (and (alist-get 'path value)
                          (string-match "\\`lisp/" (alist-get 'path value)))
                 (setq fields (delq 'use-package-name fields)))
               (dolist (field fields)
                 (unless (assq field value)
                   (report (list 'missing field)))))
             (cl-flet ((clean-url
                        (url)
                        (and url
                             (replace-regexp-in-string
                              "\\.git\\'" ""
                              (replace-regexp-in-string
                               "git@github\\.com:"
                               "git://github.com/" url)))))
               (let ((url1 (alist-get 'manifest-origin value))
                     (url2 (alist-get 'remote value)))
                 (if (and url1 url2
                          (not (string= (clean-url url1)
                                        (clean-url url2)))
                          (not (aif (alist-get 'manifest-options value)
                                    (string-match "custom-remote" it))))
                     (report 'remote-mismatch))))
             (let ((paths
                    (let ((load-path
                           (alist-get 'use-package-load-path value)))
                      (delete nil
                              (append (list (alist-get 'manifest-path value)
                                            (alist-get 'path value))
                                      (if (stringp load-path)
                                          (list load-path)
                                        load-path))))))
               (when (and (not internal)
                          paths
                          (> (length paths) 1)
                          (not (equal (alist-get 'use-package-load-path value) "lib"))
                          (not (aif (alist-get 'manifest-options value)
                                    (string-match "custom-path" it)))
                          (cl-every #'stringp paths)
                          (not (= 1 (length (cl-remove-duplicates
                                             paths :test #'string=)))))
                 (report 'path-inconsistency))))
           (insert (pp-to-string
                    (cons key
                          (if errs
                              (cons (cons 'errors errs) value)
                            value))) ?\n)))
       pkgs)
      (insert ")\n")
      (goto-char (point-min))
      (read (current-buffer)))))

(defun inventory (&optional show-all)
  (interactive "P")
  (let ((pkgs (sort* (inventory-alist) #'string-lessp :key #'car)))
    (display-buffer
     (with-current-buffer (get-buffer-create "*Inventory*")
       (erase-buffer)
       (insert (format ";; %s packages\n(\n" (length pkgs)))
       (mapc
        (lambda (elem)
          (let* ((here (point))
                 (key (car elem))
                 (value (cdr elem))
                 (errs (alist-get 'errors value))
                 (internal
                  (let ((opts (alist-get 'manifest-options value))
                        (type (alist-get 'manifest-type value)))
                    (or (and opts (string-match "mirror-only" opts))
                        (member type '("part" "internal" "personal"))))))
            (unless internal
              (when (member '(missing path) errs)
                (insert (format ";; %s: need to install\n" key)))
              (when (member '(missing remote) errs)
                (insert (format ";; %s: need to mirror as Git remote\n" key)))
              (when (member '(missing use-package-name) errs)
                (insert (format ";; %s: need to configure with use-package\n" key))))
            (when (member '(missing manifest-path) errs)
              (insert (format ";; %s: need to record in manifest\n" key)))
            (if (or show-all errs)
                (insert (pp-to-string elem) ?\n)))) pkgs)
       (insert ")\n")
       (current-buffer)))))

(provide' inventory)
