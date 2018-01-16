(require 'ghub+)
(require 'magithub-core)

(defvar magit-magithub-label-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magithub-map)
    (define-key m [remap magit-visit-thing]  #'magithub-label-visit)
    (define-key m [remap magit-delete-thing] #'magithub-label-remove)
    (define-key m [remap magit-section-toggle] (lambda () (interactive)))
    (define-key m [remap magithub-browse-thing] #'magithub-label-browse)
    (define-key m [remap magithub-add-thing] #'magithub-label-add)
    m)
  "Keymap for label sections.")

(defun magithub-label-list ()
  "Return a list of issue and pull-request labels."
  (magithub-cache :label
    `(magithub-request
      (ghubp-get-repos-owner-repo-labels
       (magithub-repo)))
    :message
    "Loading labels..."))

(defun magithub-label-read-labels (prompt &optional default)
  "Read some issue labels and return a list of strings.
Available issues are provided by `magithub-label-list'.

DEFAULT is a list of pre-selected labels.  These labels are not
prompted for again."
  (let ((remaining-labels
         (cl-set-difference (magithub-label-list) default
                            :test (lambda (a b)
                                    (= (alist-get 'name a)
                                       (alist-get 'name b))))))
    (magithub--completing-read-multiple
     prompt remaining-labels
     (lambda (l) (alist-get 'name l)))))

(defalias 'magithub-label-visit #'magithub-label-browse)
(defun magithub-label-browse (label)
  "Visit LABEL with `browse-url'.
In the future, this will likely be replaced with a search on
issues and pull requests with the label LABEL."
  (interactive (list (magithub-thing-at-point 'label)))
  (unless label
    (user-error "No label found at point to browse"))
  (unless (string= (ghubp-host) ghub-default-host)
    (user-error "Label browsing not yet supported on Github Enterprise; pull requests welcome!"))
  (let-alist (magithub-repo)
    (browse-url (format "%s/%s/%s/labels/%s"
                        (ghubp-base-html-url)
                        .owner.login .name (alist-get 'name label)))))

(defcustom magithub-label-color-replacement-alist nil
  "Make certain label colors easier to see.
In your theme, you may find that certain colors are very
difficult to see.  Customize this list to map Github's label
colors to their Emacs replacements."
  :group 'magithub
  :type '(alist :key-type color :value-type color))

(defun magithub-label--get-display-color (label)
  "Gets the display color for LABEL.
Respects `magithub-label-color-replacement-alist'."
  (let ((original (concat "#" (alist-get 'color label))))
    (if-let ((color (assoc-string original magithub-label-color-replacement-alist t)))
        (cdr color)
      original)))

(defun magithub-label-propertize (label)
  "Propertize LABEL according to its color.
The face used is dynamically calculated, but it always inherits
from `magithub-label'.  Customize that to affect all labels."
  (propertize (alist-get 'name label)
              'face (list :foreground (magithub-label--get-display-color label)
                          :inherit 'magithub-label)))

(defun magithub-label-color-replace (label new-color)
  "For LABEL, define a NEW-COLOR to use in the buffer."
  (interactive
   (list (magithub-thing-at-point 'label)
         (magithub-core-color-completing-read "Replace label color: ")))
  (let ((label-color (concat "#" (alist-get 'color label))))
    (if-let ((cell (assoc-string label-color magithub-label-color-replacement-alist)))
        (setcdr cell new-color)
      (push (cons label-color new-color)
            magithub-label-color-replacement-alist)))
  (when (y-or-n-p "Save customization? ")
    (customize-save-variable 'magithub-label-color-replacement-alist
                             magithub-label-color-replacement-alist
                             "Auto-saved by `magithub-label-color-replace'"))
  (when (derived-mode-p 'magit-status-mode)
    (magit-refresh)))

(defun magithub-label--verify-manage ()
  (or (magithub-repo-push-p)
      (user-error "You don't have permission to manage labels in this repository")))

(defun magithub-label-remove (issue label)
  "From ISSUE, remove LABEL."
  (interactive (and (magithub-label--verify-manage)
                    (list (magithub-thing-at-point 'issue)
                          (magithub-thing-at-point 'label))))
  (unless issue
    (user-error "No issue here"))
  (unless label
    (user-error "No label here"))
  (let-alist label
    (if (yes-or-no-p (format "Remove label %S from this issue? " .name))
        (prog1 (magithub-request
                (ghubp-delete-repos-owner-repo-issues-number-labels-name
                 (magithub-issue-repo issue) issue label))
          (magithub-cache-without-cache :issues
            (magit-refresh-buffer)))
      (user-error "Aborted"))))

(defun magithub-label-add (issue labels)
  "To ISSUE, add LABELS."
  (interactive (list (magithub-thing-at-point 'issue)
                     (magithub-label-read-labels "Add labels: ")))
  (if (not (and issue labels))
      (user-error "No issue/labels")
    (if (yes-or-no-p (format "Add {%s} to %s#%s? "
                             (s-join "," (ghubp-get-in-all '(name) labels))
                             (magithub-repo-name (magithub-issue-repo issue))
                             (alist-get 'number issue)))
        (prog1 (magithub-request
                (ghubp-post-repos-owner-repo-issues-number-labels
                 (magithub-issue-repo issue) issue labels))
          (magithub-cache-without-cache :issues
            (magit-refresh)))
      (user-error "Aborted"))))

(defun magithub-label-insert (label)
  "Insert LABEL into the buffer.
If you need to insert many labels, use
`magithub-label-insert-list'."
  (magit-insert-section (magithub-label label)
    (insert (magithub-label-propertize label))))

(defun magithub-label-insert-list (label-list)
  "Insert LABEL-LIST intro the buffer."
  (if (null label-list)
      (magit-insert-section (magithub-label)
        (insert (propertize "none" 'face 'magit-dimmed)))
    (while label-list
      (magithub-label-insert (pop label-list))
      (when label-list
        (insert " ")))))

(provide 'magithub-label)
