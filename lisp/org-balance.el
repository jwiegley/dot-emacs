(defun org-todo-score (&optional ignore)
  "Compute the score of an Org-mode task.
Age gradually decreases the value given to a task.  After 28
days, its score is zero.
Effort should act as a multiplier on the value."
  1)

(defvar org-categories-pending-hashmap nil)
(defvar org-categories-completed-hashmap nil)

(defun org-compute-category-totals ()
  (interactive)
  (setq org-categories-pending-hashmap (make-hash-table :test 'equal)
        org-categories-completed-hashmap (make-hash-table :test 'equal))
  (dolist (file '("todo.txt" "archive.txt"))
    (with-current-buffer
        (find-file-noselect (expand-file-name file "~/Documents"))
      (save-excursion
        (goto-char (point-min))
        (while (not (eobp))
          (outline-next-heading)
          (let* ((state (org-get-todo-state))
                 (category
                  (or (org-entry-get (point) "ARCHIVE_CATEGORY" t)
                      (org-entry-get (point) "CATEGORY" t)))
                 (hashmap
                  (cond
                   ((string= state "TODO") org-categories-pending-hashmap)
                   ((string= state "DONE") org-categories-completed-hashmap)))
                 (value (and hashmap (gethash category hashmap 0))))
            (if hashmap
                (puthash category (+ value (org-todo-score)) hashmap))))))))

(defun org-category-total (category)
  ;; A category's final score is the sum of all open tasks (which raises the
  ;; value), subtracted by the sum of all closed tasks.  Thus, a category with
  ;; a higher score deserves more attention (it has been neglected or has not
  ;; seen much activity), while a category with a low score deserves less.
  ;;
  ;; Note that this score is affected by several heuristics.  See
  ;; `org-todo-score'.
  (unless org-categories-pending-hashmap
    (org-compute-category-totals))
  (- (gethash category org-categories-pending-hashmap 0)
     (gethash category org-categories-completed-hashmap 0)))

(defun org-cmp-category-totals (a b)
  (let ((cat-a (get-text-property 1 'org-category a))
        (cat-b (get-text-property 1 'org-category b)))
    (if (> (org-category-total cat-a)
           (org-category-total cat-b))
        1
      -1)))

;; (setq org-agenda-cmp-user-defined 'org-cmp-category-totals)
