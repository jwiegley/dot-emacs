(require 'org)
(require 'org-extra)
(require 'org-ql)
(require 'org-ql-find)

(org-ql-defpred keyword (&rest keywords)
  "Search for entries about any of NAMES."
  :body (cl-loop
         for kw in keywords
         thereis (member kw (split-string
                             (or (org-entry-get (point) "KEYWORDS") "")))))

(org-ql-defpred shown ()
  "Whether this entry is not marked as HIDE."
  :body (not (org-entry-get (point) "HIDE")))

(org-ql-defpred about (&rest keywords)
  "Whether this entry is \"about\" the given keyword.
   This means checking if it's in the tags or CATEGORY."
  :body (cl-loop
         for kw in keywords
         thereis (or (member kw (org-get-tags (point)))
                     (string= kw (org-get-category (point))))))

(org-ql-defpred tasks-for (&rest who)
  "True if this task is assigned to, or related to, anyone in WHO."
  :body (and (apply #'org-ql--predicate-about who)
             (org-ql--predicate-todo)
             (org-ql--predicate-shown)))

(org-ql-defpred refile-target ()
  "Return non-nil if entry is a refile target."
  :body (org-extra-refile-heading-p))

(org-ql-defpred property-ts (property &key from to _on regexp _with-time args)
  "Match timestamps in property value."
  :normalizers ((`(,predicate-names ,property . ,rest)
                 `(property-ts ,property
                               ,@(org-ql--normalize-from-to-on
                                   `(:from ,from :to ,to)))))
  :body (when-let ((value (org-entry-get (point) property))
                   (ts (ignore-errors
                         (ts-parse-org value))))
          (cond ((not (or from to)) ts)
                ((and from to) (ts-in from to ts))
                (from (ts<= from ts))
                (to (ts<= ts to)))))

(defvar org-ql-extra-heading-to-id (make-hash-table :test 'equal))

(defun org-ql-extra-completions-at-point ()
  "Function to be used as `completion-at-point' in Org mode."
  (when (looking-back "@\\(\\(?:\\sw\\|\\s_\\|\\s-\\|\\s-:\\)+\\)" nil)
    (let* ((start (match-beginning 1))
           (end (point))
           (input (match-string-no-properties 1))
           (candidates
            (org-ql-select
              (org-agenda-files)
              (org-ql--query-string-to-sexp input)
              :action (lambda ()
                        (let* ((heading (org-get-heading t))
                               (id (org-id-get (point))))
                          ;; Avoid having to look up the ID again since we
                          ;; are visiting all the locations with org-ql
                          ;; anyway
                          (puthash heading id org-ql-extra-heading-to-id)
                          heading))))
           (exit-function
            (lambda (heading status)
              (when (eq status 'finished)
                ;; The +1 removes the @ symbol
                (delete-char (- (+ (length heading) 1)))
                (insert
                 (format "[[id:%s][%s]]"
                         (gethash heading org-ql-extra-heading-to-id)
                         heading))))))
      (list start end candidates :exit-function exit-function))))

(defun org-ql-extra-completion-hook ()
  "Configure org-mode for completion at point for org-agenda headlines."
  (add-to-list 'completion-at-point-functions
               'org-ql-extra-completions-at-point))

(defun org-ql-extra-find-refile-targets ()
  (interactive)
  (let ((query-prefix "refile-target: ")
        current-prefix-arg)
    (cond
     ((eq major-mode 'dired-mode)
      (let ((org-ql-search-directories-files-recursive t))
        (org-ql-find (org-ql-search-directories-files
                      :directories (list org-directory))
                     :query-prefix query-prefix)))
     ((eq major-mode 'org-mode)
      (org-ql-find (org-ql-find--buffers)))
     (t
      (org-ql-find (org-agenda-files)
                   :query-prefix query-prefix)))))

(provide 'org-ql-extra)
