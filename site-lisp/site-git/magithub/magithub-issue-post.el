(require 'magithub-core)
(require 'magithub-issue)
(require 'magithub-label)

(require 'widget)
(eval-and-compile
  (require 'wid-edit))

(declare-function magithub-issue-view "magithub-issue-view.el" (issue))

(define-derived-mode magithub-issue-post-mode nil
  "Magithub Issue Post"
  "Major mode for posting GitHub issues and pull requests.")

(defvar-local magithub-issue--extra-data nil)
(defvar-local magithub-issue--widgets nil
  "Alist of symbols to widgets.")
(defun magithub-issue--widget-get (key)
  (alist-get key magithub-issue--widgets))
(defun magithub-issue--widget-value (key)
  (widget-value (magithub-issue--widget-get key)))

(setq magithub-issue-post-mode-map
      (let ((m (copy-keymap widget-keymap)))
        (define-key m (kbd "C-c RET") #'magithub-issue-wsubmit)
        (define-key m (kbd "C-c C-k") #'magithub-issue-wcancel)
        (define-key m "b" #'magithub-issue-w-jump-to-body)
        m))

(add-hook 'magithub-issue-post-mode-hook
          #'magithub-bug-reference-mode-on)

(defun magithub-issue-w-beginning-of-buffer-dwim ()
  (interactive)
  (let ((start-of-body (magithub-issue--w-start-of-body)))
    (goto-char
     (if (= (point) start-of-body)
         (point-min)
       start-of-body))))
(defun magithub-issue-w-end-of-buffer-dwim ()
  (interactive)
  (let ((end-of-body (magithub-issue--w-end-of-body)))
    (goto-char
     (if (= (point) end-of-body)
         (point-max)
       end-of-body))))
(defun magithub-issue-w-jump-to-body ()
  (interactive)
  (if (or (not (widget-at))
          (eq 'checkbox (widget-type (widget-at))))
      (goto-char (magithub-issue--w-start-of-body))
    (call-interactively #'self-insert-command)))

(defun magithub-issue--w-start-of-body ()
  (save-excursion
    (goto-char (widget-get (magithub-issue--widget-get 'body) :from))
    (forward-line)
    (point)))
(defun magithub-issue--w-end-of-body ()
  (save-excursion
    (goto-char (widget-get (magithub-issue--widget-get 'body) :to))
    (backward-char 3)
    (point)))
(defun magithub-issue-w-next-widget-dwim ()
  (interactive)
  (ignore-errors
    (let ((start (magithub-issue--w-start-of-body))
          (end   (magithub-issue--w-end-of-body))
          (keys  (kbd (substitute-command-keys
                       "\\[magithub-issue-w-next-widget-dwim]"))))
      (if (or (<= (point) start) (<= end (point)))
          (call-interactively #'widget-forward)
        (when-let ((func (with-temp-buffer
                           (key-binding keys))))
          (call-interactively func))))))

(define-widget 'magithub-issue-title 'editable-field
  "Issue / pull-request title entry"
  :tag "Title"
  :format "%t: %v \n\n")
(define-widget 'magithub-issue-labels 'checklist
  "Tag entry"
  :greedy t
  :tag "Labels"
  :format "%t:\n%v \n\n")
(define-widget 'magithub-issue-text 'text
  "Issue / pull-request body entry"
  :tag "Body"
  :format "%t:\n%v\n\n"
  :inline nil)

(defun magithub-issue--new-form (repo issue
                                      buffer-name
                                      header
                                      show-labels-p
                                      submit-caption
                                      submit-function
                                      cancel-caption
                                      cancel-function)
  "Opens a new widget-based form for issue/PR submission.

REPO should be a full repository object.

ISSUE should be an issue object.  The `title' and `labels'
properties are respected and prepopulate the form."
  (let-alist `((repo . ,repo) (issue . ,issue))
    (with-current-buffer (generate-new-buffer buffer-name)
      (magithub-issue-post-mode)
      (setq header-line-format
            (substitute-command-keys
             (s-join " | " (list header
                                 "submit: \\[magithub-issue-wsubmit]"
                                 "cancel: \\[magithub-issue-wcancel]"))))
      (push
       (cons 'title (widget-create 'magithub-issue-title
                                   :size 76
                                   .issue.title))
       magithub-issue--widgets)

      (when show-labels-p
        (push (cons 'labels
                    (let ((w (apply #'widget-create 'magithub-issue-labels
                                    (mapcar (lambda (label) `(item ,(alist-get 'name label)))
                                            (magithub-label-list)))))
                      (widget-value-set w (ghubp-get-in-all '(name) .issue.labels))
                      w))
              magithub-issue--widgets))

      (push (cons 'body (widget-create 'magithub-issue-text))
            magithub-issue--widgets)

      (widget-insert "\n")
      (widget-create 'push-button :notify submit-function submit-caption)
      (widget-insert "  ")
      (widget-create 'push-button :notify cancel-function cancel-caption)
      (widget-insert "\n")
      (widget-setup)
      (magithub-issue-w-jump-to-body)
      ;; GFM-mode doesn't handle line breaks just yet
      (visual-line-mode 1)
      (current-buffer))))

(defun magithub-issue-new (repo title labels)
  (interactive
   (let-alist (setq repo (magithub-repo))
     (list repo
           (read-string (format "Issue title (%s): " .full_name))
           (when .permissions.push
             (magithub-label-read-labels "Labels: ")))))

  (let-alist repo
    (with-current-buffer
        (magithub-issue--new-form
         repo `((title . ,title) (labels . ,labels))
         "*magithub-issue*"
         (format "Creating an issue for %s" .full_name)
         .permissions.push
         "Create new issue"
         #'magithub-issue-wsubmit-issue
         "Cancel"
         #'magithub-issue-wcancel)
      (setq magithub-issue--extra-data '((kind . issue)))
      (magithub-issue--template-insert "ISSUE_TEMPLATE")
      (switch-to-buffer-other-window (current-buffer)))))

(defun magithub-issue--template-insert (filename)
  "Inserts template FILENAME into the issue body"
  (save-excursion
    (magithub-issue-w-jump-to-body)
    (when-let ((template (magithub-issue--template-find filename)))
      (insert-file-contents template))))

(defun magithub-issue--template-find (filename)
  "Find an appropriate template called FILENAME and returns its absolute path.

See also URL
`https://github.com/blog/2111-issue-and-pull-request-templates'"
  (let ((default-directory (magit-toplevel))
        combinations)
    (dolist (tryname (list filename (concat filename ".md")))
      (dolist (trydir (list default-directory (expand-file-name ".github/")))
        (push (expand-file-name tryname trydir) combinations)))
    (-find #'file-readable-p combinations)))

(defun magithub-remote-branches (remote)
  "Return a list of branches on REMOTE."
  (let ((regexp (concat (regexp-quote remote) (rx "/" (group (* any))))))
    (--map (and (string-match regexp it)
                (match-string 1 it))
           (magit-list-remote-branch-names remote))))

(defun magithub-remote-branches-choose (prompt remote &optional default)
  "Using PROMPT, choose a branch on REMOTE."
  (magit-completing-read
   (format "[%s] %s"
           (magithub-repo-name (magithub-repo-from-remote remote))
           prompt)
   (magithub-remote-branches remote)
   nil t nil nil default))

(defun magithub-pull-request-new-arguments ()
  (let* ((this-repo   (magithub-read-repo "Fork's remote (this is you!)"))
         (this-repo-owner (let-alist this-repo .owner.login))
         (parent-repo (or (alist-get 'parent this-repo) this-repo))
         (this-remote (car (magithub-repo-remotes-for-repo this-repo)))
         (on-this-remote (string= (magit-get-push-remote) this-remote))
         (base-remote (car (magithub-repo-remotes-for-repo parent-repo)))
         (head        (magithub-remote-branches-choose
                       "Head branch" this-remote
                       (when on-this-remote
                         (magit-get-current-branch))))
         (base        (magithub-remote-branches-choose
                       "Base branch" base-remote
                       (when on-this-remote
                         (magit-get-upstream-branch head)))))
    (let-alist parent-repo
      (list parent-repo
            base
            (if (string= this-remote base-remote)
                head
              (format "%s:%s" this-repo-owner head))
            (read-string (format "Pull request title (%s/%s): "
                                 .owner.login .name))))))

(defun magithub-pull-request-new (repo base head title)
  "Create a new pull request."
  (interactive (magithub-pull-request-new-arguments))
  (let-alist repo
    (with-current-buffer
        (magithub-issue--new-form
         repo `((title . ,title))
         "*magithub-pull-request*"
         (format "PR %s/%s (%s->%s)" .owner.login .name head base)
         nil
         "Submit new pull request"
         #'magithub-issue-wsubmit-pull-request
         "Cancel"
         #'magithub-issue-wcancel)
      (setq magithub-issue--extra-data
            `((base . ,base) (head . ,head)
              (kind . pull-request)))
      (magithub-issue--template-insert "PULL_REQUEST_TEMPLATE")
      (switch-to-buffer-other-window (current-buffer)))))

(defun magithub-issue-wsubmit ()
  (interactive)
  (call-interactively
   (pcase (alist-get 'kind magithub-issue--extra-data)
     ('pull-request #'magithub-issue-wsubmit-pull-request)
     ('issue #'magithub-issue-wsubmit-issue))))

(defun magithub-issue-wsubmit-issue (&rest _)
  (interactive)
  (let ((issue `((title  . ,(s-trim (magithub-issue--widget-value 'title)))
                 (body   . ,(s-trim (magithub-issue--widget-value 'body)))
                 ,@(when-let ((vlabels (ignore-errors (magithub-issue--widget-value 'labels))))
                     `((labels . ,vlabels))))))
    (when (s-blank-p (alist-get 'title issue))
      (user-error "Title is required"))
    (when (yes-or-no-p "Are you sure you want to submit this issue? ")
      (magithub-issue-view
       (ghubp-post-repos-owner-repo-issues (magithub-repo) issue))
      (kill-buffer-and-window))))
(defun magithub-issue-wsubmit-pull-request (&rest _)
  (interactive)
  (let ((pull-request `((title  . ,(s-trim (magithub-issue--widget-value 'title)))
                        (body   . ,(s-trim (magithub-issue--widget-value 'body)))
                        (base   . ,(alist-get 'base magithub-issue--extra-data))
                        (head   . ,(alist-get 'head magithub-issue--extra-data)))))
    (when (s-blank-p (alist-get 'title pull-request))
      (user-error "Title is required"))
    (when (yes-or-no-p "Are you sure you want to submit this pull request? ")
      (when (y-or-n-p "Allow maintainers to modify this pull request? ")
        (push (cons 'maintainer_can_modify t) pull-request))
      (magithub-issue-view
       (ghubp-post-repos-owner-repo-pulls (magithub-repo) pull-request))
      (kill-buffer-and-window))))

(defun magithub-issue-wcancel (&rest _)
  (interactive)
  ;; It'd be nice to have a sort of kill ring for cancelled issues
  (when (yes-or-no-p "You will lose this buffer completely; are you sure? ")
    (kill-buffer-and-window)))

(provide 'magithub-issue-post)
