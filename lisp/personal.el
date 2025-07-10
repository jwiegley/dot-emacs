;;; -*- lexical-binding: t -*-

(defun my-set-custom-variable ()
  (interactive)
  (save-excursion
    (custom-set-variables (read (current-buffer)))
    (message "Variable has been set")))

(defcustom user-initials nil
  "*Initials of this user."
  :set
  #'(lambda (symbol value)
      (if (fboundp 'font-lock-add-keywords)
          (mapc
           #'(lambda (mode)
               (font-lock-add-keywords
                mode (list (list (concat "\\<\\(" value " [^:\n]+\\):")
                                 1 font-lock-warning-face t))))
           '(c-mode c++-mode emacs-lisp-mode lisp-mode
                    python-mode perl-mode java-mode groovy-mode
                    haskell-mode literate-haskell-mode)))
      (set symbol value))
  :type 'string
  :group 'mail)

(defun insert-user-timestamp ()
  "Insert a quick timestamp using the value of `user-initials'."
  (interactive)
  (insert (format "%s (%s): " user-initials
                  (format-time-string "%Y-%m-%d" (current-time)))))

(defadvice async-shell-command (before uniqify-running-shell-command activate)
  (let ((buf (get-buffer "*Async Shell Command*")))
    (if buf
        (let ((proc (get-buffer-process buf)))
          (if (and proc (eq 'run (process-status proc)))
              (with-current-buffer buf
                (rename-uniquely)))))))

(defun mark-line (&optional arg)
  (interactive "p")
  (beginning-of-line)
  (let ((here (point)))
    (dotimes (i arg)
      (or (zerop i) (forward-line))
      (end-of-line))
    (set-mark (point))
    (goto-char here)))

(defun mark-sentence (&optional arg)
  (interactive "P")
  (backward-sentence)
  (mark-end-of-sentence arg))

(defun delete-indentation-forward ()
  (interactive)
  (delete-indentation t))

(defun rename-current-buffer-file ()
  "Renames the current buffer and the file it is visiting."
  (interactive)
  (let ((name (buffer-name))
        (filename (buffer-file-name)))
    (if (not (and filename (file-exists-p filename)))
        (error "Buffer '%s' is not visiting a file!" name)
      (let ((new-name (read-file-name "New name: " filename)))
        (if (get-buffer new-name)
            (error "A buffer named '%s' already exists!" new-name)
          (rename-file filename new-name 1)
          (rename-buffer new-name)
          (set-visited-file-name new-name)
          (set-buffer-modified-p nil)
          (message "File '%s' successfully renamed to '%s'"
                   name (file-name-nondirectory new-name)))))))

(defun delete-current-buffer-file ()
  "Delete the current buffer and the file connected with it"
  (interactive)
  (let ((filename (buffer-file-name))
        (buffer (current-buffer))
        (name (buffer-name)))
    (if (not (and filename (file-exists-p filename)))
        (kill-buffer buffer)
      (when (yes-or-no-p "Are you sure this file should be removed? ")
        (delete-file filename)
        (kill-buffer buffer)
        (message "File '%s' successfully removed" filename)))))

(defun duplicate-line (arg)
  "Duplicate the line containing point."
  (interactive "p")
  (save-excursion
    (let (line-text)
      (goto-char (line-beginning-position))
      (let ((beg (point)))
        (goto-char (line-end-position))
        (setq line-text (buffer-substring beg (point))))
      (if (eobp)
          (insert ?\n)
        (forward-line))
      (open-line 1)
      (if arg
          (dotimes (i arg)
            (unless (= i 0)
              (insert ?\n))
            (insert line-text))
        (insert line-text)))))

(defun find-alternate-file-with-sudo ()
  (interactive)
  (find-alternate-file (concat "/sudo::" (buffer-file-name))))

(defun refill-paragraph (arg)
  (interactive "*P")
  (let ((fun (if (memq major-mode '(c-mode c++-mode))
                 'c-fill-paragraph
               (or fill-paragraph-function
                   'fill-paragraph)))
        (width (if (numberp arg) arg))
        prefix beg end)
    (forward-paragraph 1)
    (setq end (copy-marker (- (point) 2)))
    (forward-line -1)
    (let ((b (point)))
      (skip-chars-forward "^A-Za-z0-9`'\"(")
      (setq prefix (buffer-substring-no-properties b (point))))
    (backward-paragraph 1)
    (if (eolp)
        (forward-char))
    (setq beg (point-marker))
    (delete-horizontal-space)
    (while (< (point) end)
      (delete-indentation 1)
      (end-of-line))
    (let ((fill-column (or width fill-column))
          (fill-prefix prefix))
      (if prefix
          (setq fill-column
                (- fill-column (* 2 (length prefix)))))
      (funcall fun nil)
      (goto-char beg)
      (insert prefix)
      (funcall fun nil))
    (goto-char (+ end 2))))

(defun recursive-edit-preserving-window-config ()
  (interactive)
  (save-window-excursion
    (unless (one-window-p 'ignore-minibuffer)
      (delete-other-windows))
    (recursive-edit)))

(defun recursive-edit-preserving-window-config-pop ()
  (interactive)
  (exit-recursive-edit))

(defun delete-current-line (&optional arg)
  (interactive "p")
  (let ((here (point)))
    (beginning-of-line)
    (kill-line arg)
    (goto-char here)))

(defun do-eval-buffer ()
  (interactive)
  (call-interactively 'eval-buffer)
  (message "Buffer has been evaluated"))

(defun do-eval-region ()
  (interactive)
  (call-interactively 'eval-region)
  (message "Region has been evaluated"))

(defun view-clipboard ()
  (interactive)
  (delete-other-windows)
  (switch-to-buffer "*Clipboard*")
  (let ((inhibit-read-only t))
    (erase-buffer)
    (clipboard-yank)
    (goto-char (point-min))))

(defun delete-to-end-of-buffer ()
  (interactive)
  (kill-region (point) (point-max)))

(defun copy-current-buffer-name (&optional arg)
  (interactive "P")
  (let ((name (buffer-file-name)))
    (unless arg
      (setq name (file-name-nondirectory name)))
    (when name
      (kill-new name)
      (message name))))

(defun unfill-paragraph ()
  (interactive)
  (let ((fill-column (point-max)))
    (fill-paragraph nil t)))

(defun unfill-region (beg end)
  (interactive "r")
  (setq end (copy-marker end))
  (save-excursion
    (goto-char beg)
    (while (< (point) end)
      (unfill-paragraph)
      (forward-paragraph))))

(defun close-all-parentheses* (indent-fn arg)
  ;; http://acidwords.com/posts/2017-10-19-closing-all-parentheses-at-once.html
  (let* ((closing nil)
         ;; by default rely on (newline-and-indent)
         (local-indent-fn (lambda (token)
                            (newline-and-indent)
                            (insert token)))
         (indent-fn (if indent-fn
                        indent-fn
                      local-indent-fn)))
    (save-excursion
      (while
          (condition-case nil
              (progn
                (backward-up-list)
                (let ((syntax (syntax-after (point))))
                  (pcase (car syntax)
                    (`(4) (setq closing
                                (cons (cdr syntax) closing)))
                    (`(7 8) (setq closing
                                  (cons (char-after (point)) closing)))))
                t)
            ((scan-error) nil))))
    (dolist (token (nreverse closing))
      (if arg
          (funcall indent-fn token)
        (insert token)))))

(defun close-all-parentheses (arg)
  (interactive "P")
  (let ((my-format-fn
         (lambda (token)
           ;; 125 is codepoint for '}'
           (if (and (= token 125)
                    ;; C, C++ and Java
                    (member major-mode '(c-mode c++-mode java-mode)))
               (let ((last-command-event ?}))
                 (newline)
                 (if (fboundp 'c-electric-brace)
                     (funcall #'c-electric-brace nil)))
             (insert token)))))
    (close-all-parentheses* my-format-fn arg)))

(defun check-papers ()
  (interactive)
  ;; From https://www.gnu.org/prep/maintain/html_node/Copyright-Papers.html
  (find-file-other-window "/fencepost.gnu.org:/gd/gnuorg/copyright.list"))

(defun scratch (&optional name)
  (interactive)
  (switch-to-buffer-other-window
   (get-buffer-create (or name "*scratch*")))
  (goto-char (point-min))
  (when (looking-at ";")
    (forward-line 4)
    (delete-region (point-min) (point)))
  (goto-char (point-max))
  (text-mode))

(defun find-all-macros ()
  (interactive)
  (while (re-search-forward "(\\([A-Za-z-]+\\)\\s-+" nil t)
    (let ((sym (intern-soft (match-string 1))))
      (if (and sym (macrop sym)
               (not (memq sym
                          '(declare
                            declare-function
                            defcustom
                            defgroup
                            defmacro
                            defsubst
                            defun
                            eval-and-compile
                            lambda
                            when
                            unless
                            with-current-buffer
                            push))))
          (with-current-buffer (get-buffer-create "*macros*")
            (goto-char (point-max))
            (insert (symbol-name sym) ?\n)))))
  (display-buffer (get-buffer-create "*macros*")))

(defun transform-by-lines (f)
  (goto-char (point-min))
  (while (not (eobp))
    (let* ((line-beg (line-beginning-position))
           (line-end (line-end-position))
           (line (buffer-substring line-beg line-end)))
      (delete-region line-beg line-end)
      (let ((result (funcall f line)))
        (if (stringp result)
            (progn
              (insert result)
              (forward-line))
          (delete-char 1))))))

(defun kill-ring-save-no-newlines (beg end)
  (interactive "r")
  (let ((substring (buffer-substring beg end)))
    (with-temp-buffer
      (insert substring)
      (delete-indentation nil (point-min) (point-max))
      (kill-new (buffer-string)))
    (deactivate-mark)))

(defun traverse (f x)
  "Visit all nodes within the sexp X, apply F to its leaves."
  (cond ((consp x)
         (cons (traverse f (car x))
               (traverse f (cdr x))))
        ((listp x)
         (mapcar (apply-partially #'traverse f) x))
        ((hash-table-p x)
         (maphash #'(lambda (key value)
                      (puthash key (traverse f value) x)) x))
        (t (funcall f x))))

(defun comment-and-copy (beg end)
  (interactive "r")
  (insert (buffer-substring beg end))
  (comment-region beg end))

(defun profile-hook (hook)
  (eval
   (macroexp-progn
    (mapcan #'(lambda (f)
                (use-package-with-elapsed-timer (format "%s" f)
                  `((funcall ',f))))
            hook))))

(defun filter (f args)
  (let (result)
    (dolist (arg args)
      (when (funcall f arg)
        (setq result (cons arg result))))
    (nreverse result)))

(defmacro atomic-modify-buffer (&rest body)
  `(let ((buf (current-buffer)))
     (save-window-excursion
       (with-temp-buffer
         (insert-buffer buf)
         ,@body
         (let ((temp-buf (current-buffer))
               (inhibit-redisplay t))
           (with-current-buffer buf
             (let ((here (point)))
               (save-excursion
                 (delete-region (point-min) (point-max))
                 (insert-buffer temp-buf))
               (goto-char here))))))))

(defun sort-on (seq predicate accessor)
  "Sort by comparing results of ACCESSOR applied to each element.
This function has the performance advantage of evaluating
ACCESSOR only once for each element in the input list. This is
called the \"decorate-sort-undecorate\" paradigm, or Schwartzian
transform."
  (mapcar #'car
          (sort (mapcar #'(lambda (x) (cons x (funcall accessor x))) seq)
                :lessp #'(lambda (x y) (funcall predicate (cdr x) (cdr y))))))

(defmacro save-bound-variable (var &rest body)
  `(let ((,var ,var))
     ,@body))

(defmacro save-bound-list (var &rest body)
  `(let ((,var (cl-copy-list ,var)))
     ,@body))

(defmacro save-lexical-variable (var &rest body)
  (let ((save-var (intern (concat "--save-" (symbol-name var)))))
    `(let ((,save-var ,var))
       (unwind-protect
           (progn ,@body)
         (setq ,var ,save-var)))))

(defmacro save-lexical-list (var &rest body)
  (let ((save-var (intern (concat "--save-" (symbol-name var)))))
    `(let ((,save-var (cl-copy-list ,var)))
       (unwind-protect
           (progn ,@body)
         (setq ,var ,save-var)))))

;;; These are obviated by the `let-alist' package.

;; (defmacro with (alist &rest body)
;;   "Use an alist as a set of scoped symbol definitions.
;; This can be used alone, or in conjunction with `capture'. Example:

;;   (defun bar (scope)
;;     (with scope
;;       (message \"x = %s, y = %s, z = %s\" x y z)))

;;   (defun foo ()
;;     (let ((x 100)
;;           (y 200)
;;           (z 300))
;;       (bar (capture x y z))))"
;;   (declare (indent defun))
;;   `(cl-progv (mapcar #'car ,alist) (mapcar #'cdr ,alist) ,@body))

;; (defmacro capture (&rest syms)
;;   `(mapcar #'(lambda (sym) (cons (quote sym) sym)) (quote ,syms)))

(defun buffer-locals ()
  (interactive)
  (let ((vars (buffer-local-variables)))
    (with-current-buffer (get-buffer "*scratch*")
      (insert (pp-to-string vars)))))

(defmacro compose (&rest args)
  `(lambda (x) (thread-last x ,@args)))

(defconst emacs-nix-name-re
  (rx
   (seq bol "  "
        (opt (zero-or-more " "))
        (opt (group "(exclude "))
        (or (seq "epkgs.\"" (group (+? nonl)) "\"")
            (group (one-or-more (any "-" "+" alnum))))
        (opt ")"))))

(defun sort-emacs-nix-names ()
  (interactive)
  (let ((re emacs-nix-name-re)
        (counter 10000))
    (cl-flet ((nextrecfun ()
                (if (< (setq counter (1- counter)) 0)
                    (error "Counter tripped"))
                (if (looking-at re)
                    (point)
                  (if (re-search-forward re nil t)
                      (goto-char (match-beginning 0))
                    (goto-char (point-max)))))
              (endrecfun ()
                (goto-char (line-end-position)))
              (startkeyfun ()
                (and (looking-at re)
                     (or (match-string 2)
                         (match-string 3)))))
      (sort-subr nil #'nextrecfun #'endrecfun #'startkeyfun))))

(defun sort-emacs-nix-file ()
  (interactive)
  (when (string= (buffer-file-name)
                 "/Users/johnw/src/nix/config/emacs.nix")
    (save-excursion
      (goto-char 75)
      (sort-emacs-nix-names))))

(cl-defun comm (list1 list2 &key
                      (key #'identity)
                      (compare #'string<)
                      (test #'string=)
                      (merge #'vector))
  (sort-on
   (nconc
    (mapcar (lambda (x)
              (if-let* ((y (cl-member (funcall key x) list2
                                      :test test :key key)))
                  (if (equal x (car y))
                      (cons x :both)
                    (let ((merged (funcall merge (cdr x) (cdar y))))
                      (if merged
                          (cons (cons (car x) merged) :both)
                        (cons x :both))))
                (cons x :left)))
            list1)
    (seq-keep (lambda (x)
                (unless (cl-member (funcall key x) list1
                                   :test test :key key)
                  (cons x :right)))
              list2))
   compare
   (lambda (x) (funcall key (car x)))))

(defun org-within-commented-block ()
  (save-excursion
    (catch 'found
      (while (ignore-errors (prog1 t (org-up-element)))
        (if (string-match-p "COMMENT" (org-get-heading))
            (throw 'found t))))))

(defun emacs-nix-packages ()
  (let (results)
    (while (re-search-forward emacs-nix-name-re nil t)
      (let ((commented (match-string-no-properties 1))
            (name (or (match-string-no-properties 2)
                      (match-string-no-properties 3))))
        (setq results
              (cons (cons name (and commented (list :commented)))
                    results))))
    results))

(defun init-org-packages ()
  (let (results)
    (while (re-search-forward
            (rx (seq bol
                     "*" (one-or-more "*") " "
                     (group (opt (group "COMMENT "))
                            (group (one-or-more (any "+-" alnum))))
                     eol))
            nil t)
      (let* ((heading (match-string-no-properties 1))
             (name (match-string-no-properties 3))
             (commented (or (match-string-no-properties 2)
                            (org-within-commented-block)))
             (end (save-excursion
                    (org-next-visible-heading 1)
                    (point))))
        (when (save-excursion
                (re-search-forward "use-package [[:alnum:]+-]+" end t))
          (let* ((no-require
                  (save-excursion (search-forward ":no-require t" end t)))
                 (from-load-path
                  (save-excursion (re-search-forward "^  :load-path" end t)))
                 (nix-name
                  (save-excursion
                    (and (re-search-forward ":nix \\([[:alnum:]+-]+\\))?$" end t)
                         (match-string-no-properties 1))))
                 (no-nix (and nix-name (string= nix-name "nil"))))
            (setq results
                  (cons (cons (if no-nix name (or nix-name name))
                              (append
                               (and commented (list :commented))
                               (and no-require (list :no-require))
                               (and from-load-path (list :from-load-path))
                               (and no-nix (list :no-nix))))
                        results))))))
    (nreverse results)))

(defun parse-packages (path func)
  (with-current-buffer (find-file-noselect path)
    (save-excursion
      (goto-char (point-min))
      (funcall func))))

(defconst excluded-keywords '(:no-require :from-load-path :no-nix))

(defun active-init-org-attrs (attrs)
  (or (equal attrs '(:commented))
      (not (seq-every-p
            (lambda (x)
              (or (null x)
                  (memq x excluded-keywords)))
            (seq-remove (lambda (x) (eq x :commented)) attrs)))))

(defun review-emacs-nix-file (&optional arg)
  (interactive "P")
  (with-current-buffer (get-buffer-create "*packages*")
    (erase-buffer)
    (let ((combined
           (comm
            (parse-packages "~/org/init.org" #'init-org-packages)
            (parse-packages "~/src/nix/config/emacs.nix" #'emacs-nix-packages)
            :key #'car
            :compare #'string<
            :test #'string=
            :merge (lambda (x y)
                     (let ((x-prime (seq-remove (lambda (i) (memq i excluded-keywords)) x))
                           (y-prime (seq-remove (lambda (i) (memq i excluded-keywords)) y)))
                       (unless (equal x-prime y-prime)
                         (vector x-prime y-prime)))))))
      (dolist (item combined)
        (when (or arg
                  (cl-case (cdr item)
                    (:both (and (vectorp (cdar item))
                                (active-init-org-attrs (cdar item))))
                    (:left (active-init-org-attrs (cdar item)))
                    (t t)))
          (let ((both-mismatch (and (eq (cdr item) :both)
                                    (vectorp (cdar item)))))
            (cond ((eq (cdr item) :left)
                   (insert "<< "))
                  ((eq (cdr item) :right)
                   (insert ">> "))
                  (both-mismatch
                   (insert "!! "))
                  (t
                   (insert "== ")))
            (if both-mismatch
                (insert "     ")
              (insert
               (format "%-5s"
                       (with-temp-buffer
                         (dolist (item (cdar item))
                           (cl-case item
                             (:commented
                              (insert ";"))
                             (:no-require
                              (insert "r"))
                             (:from-load-path
                              (insert "l"))
                             (:no-nix
                              (insert "n"))))
                         (buffer-string)))))
            (insert (caar item))
            (when both-mismatch
              (insert (format " %S" (cdar item)))))
          (insert ?\n))))
    (goto-char (point-min))
    (pop-to-buffer (current-buffer))))

(provide 'personal)

;;; personal.el ends here
