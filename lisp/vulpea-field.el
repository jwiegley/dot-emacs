(require 'vulpea)

;;;###autoload
(defsubst vulpea-field-query (table-name note)
  (eval
   `(org-roam-db-query
     [:select [field] :from ,table-name
              :where (= note-id $s1)]
     (vulpea-note-id note))))

;;;###autoload
(defun vulpea-field-setup (table-name predicate accessor processor)
  (vulpea-db-define-table
   ;; name
   table-name
   ;; version
   1
   ;; schema
   '([(note-id :unique :primary-key)
      field]
     ;; useful to automatically cleanup your table whenever a note/node/file is removed
     (:foreign-key [note-id] :references nodes [id] :on-delete :cascade))
   ;; index
   '((field-id-index [note-id])))

  (add-hook 'vulpea-db-insert-note-functions
            (apply-partially #'vulpea-field--insert
                             table-name predicate accessor processor)))

(defun vulpea-field--insert (table-name predicate accessor processor note)
  (when (funcall predicate note)
    (eval
     `(org-roam-db-query
       [:delete :from ,table-name
                :where (= note-id $s1)]
       (vulpea-note-id note)))
    (vulpea-utils-with-note note
      (when-let ((datum (funcall accessor note)))
        (eval
         `(org-roam-db-query!
           (lambda (err)
             (lwarn 'org-roam :warning "%s for field '%s' in %s (%s) %s"
                    (error-message-string err)
                    datum
                    (vulpea-note-title note)
                    (vulpea-note-id note)
                    (vulpea-note-path note)))
           [:insert :into ,table-name
                    :values $v1]
           (vector (vulpea-note-id note)
                   (funcall processor note datum))))))))

(provide 'vulpea-field)
