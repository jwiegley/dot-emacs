


;;; Code;
(defvar org-roam-gt-node-display-template #'org-roam-gt-default-format
  "Default template to use when displaying a node.

If it is a string and it will be used as described in org-roam
 (see org-roam-node-display-template)

If it is a function, it will be called to format a node.
Its result is expected to be a string (potentially with
embedded properties)."
  )

;; add a BOA constructor to org-roam-node.
;;
;; the constructor with named parameters is much slower than the boa one
;;
;; This code replaces the one found in org-roam
(cl-defstruct (org-roam-node (:constructor org-roam-node-create)
                             (:constructor org-roam-node-create-from-db
                                           (title aliases                    ; 2
                                                  id file file-title level todo     ; 5
                                                  point priority scheduled deadline properties ;;5
                                                  olp file-atime file-mtime tags refs)) ;;5
                             (:copier nil))
  "A heading or top level file with an assigned ID property."
  file file-title file-hash file-atime file-mtime ;5 
  id level point todo priority ; 5
  scheduled deadline title properties olp ;5
  tags aliases refs)


;; This is a rewrite of org-roam-node-list. It returns the same values
;;
;; It has a simplified logic for processing the nodes and uses the BAO constructor
;; instead of the one with named parameters

(defvar org-roam-gt--retrieve-nodes-query "
SELECT
  title,
  aliases,

  id,
  file,
  filetitle,
  \"level\",
  todo,

  pos,
  priority ,
  scheduled ,
  deadline ,
  properties ,

  olp,
  atime,
  mtime,
  '(' || group_concat(tags, ' ') || ')' as tags,
  refs
FROM
  (
  SELECT
    id,
    file,
    filetitle,
    \"level\",
    todo,
    pos,
    priority ,
    scheduled ,
    deadline ,
    title,
    properties ,
    olp,
    atime,
    mtime,
    tags,
    '(' || group_concat(aliases, ' ') || ')' as aliases,
    refs
  FROM
    (
    SELECT
      nodes.id as id,
      nodes.file as file,
      nodes.\"level\" as \"level\",
      nodes.todo as todo,
      nodes.pos as pos,
      nodes.priority as priority,
      nodes.scheduled as scheduled,
      nodes.deadline as deadline,
      nodes.title as title,
      nodes.properties as properties,
      nodes.olp as olp,
      files.atime as atime,
      files.mtime as mtime,
      files.title as filetitle,
      tags.tag as tags,
      aliases.alias as aliases,
      '(' || group_concat(RTRIM (refs.\"type\", '\"') || ':' || LTRIM(refs.ref, '\"'), ' ') || ')' as refs
    FROM nodes
    LEFT JOIN files ON files.file = nodes.file
    LEFT JOIN tags ON tags.node_id = nodes.id
    LEFT JOIN aliases ON aliases.node_id = nodes.id
    LEFT JOIN refs ON refs.node_id = nodes.id
    GROUP BY nodes.id, tags.tag, aliases.alias )
  GROUP BY id, tags )
GROUP BY id
"
  "SQLite Query to use for retrieving all the nodes from the database."
  )


(defun org-roam-gt-node-list (sort-by-mtime)
  "Return all nodes stored in the database as a list of org-roam-node's.

If SORT-BY-MTIME then order by mtime in descending order.
"
  (let* (
         (order-by (if sort-by-mtime
                       "order by mtime desc"
                     ""))
         (rows (org-roam-db-query
                (format "%s\n%s" 
                        org-roam-gt--retrieve-nodes-query
                        order-by))))
   (mapcan
     (lambda (row)
       (let (
              (all-titles (cons (car row) (nth 1 row)))
              )
         (mapcar (lambda (temp-title)
                   (apply 'org-roam-node-create-from-db (cons temp-title (cdr row))))
                 all-titles)
       ))
     rows)
     ))


;; rewrite org-roam-node-read--completions

;; 1. Uses org-roam-gt-node-list instead of org-roam-node-list
;; 2. If org-roam-gt-node-display-template is a string process as in org-roam
;;    if it is a function, call it instead
;; 3. Simplified the code a bit, reducing memory consumption

(defun org-roam-gt--format-nodes-using-template (nodes)
  "Formats NODES using org-roam template features.
Uses org-roam-gt-node-display-template."
  (let  (
      (wTemplate (org-roam-node--process-display-format org-roam-gt-node-display-template))
      )
    (mapcar (lambda (node)
              (org-roam-node-read--to-candidate node wTemplate)) nodes))
  )

(defun org-roam-gt--format-nodes-using-function (nodes)
  "Formats NODES using the function org-roam-gt-node-display-template."
  (mapcar org-roam-gt-node-display-template nodes )
  )

(defun org-roam-gt-node-read--completions (&optional filter-fn sort-fn)
  "Return an alist for node completion.
The car is the displayed title or alias for the node, and the cdr
is the `org-roam-node'.
FILTER-FN is a function to filter out nodes: it takes an `org-roam-node',
and when nil is returned the node will be filtered out.
SORT-FN is a function to sort nodes. See `org-roam-node-read-sort-by-file-mtime'
for an example sort function.
The displayed title is formatted according to `org-roam-node-display-template'."
  (let* (
         ;; if the sorting is by file-mtime, then do it in the database
         (sort-by-mtime (and (not sort-fn)
                         (eq org-roam-node-default-sort 'file-mtime)))
         (nodes (org-roam-gt-node-list sort-by-mtime))
         (nodes (if filter-fn
                    (cl-remove-if-not
                     (lambda (n) (funcall filter-fn n))
                     nodes)
                  nodes))
         (nodes (if (functionp org-roam-gt-node-display-template)
                    (org-roam-gt--format-nodes-using-function nodes)
                   (org-roam-gt--format-nodes-using-template nodes)))

         ;; do we sort, and if so, by what?
         (sort-fn (or sort-fn
                      ;; only do it if it not by file-mtime
                      (when (and (not sort-by-mtime) org-roam-node-default-sort)
                        (intern (concat "org-roam-node-read-sort-by-"
                                        (symbol-name org-roam-node-default-sort))))))
         (nodes (if sort-fn (seq-sort sort-fn nodes)
                  nodes)))
    nodes))


;; org-roam-gt-default-format-template
;

;; support functions

(defun org-roam-gt--to-string (st)
  "Make sure we have ST is a string. if it is a list, concatenate it."
  (cond
   ((stringp st) st)
   ((listp st) (mapconcat 'identity st " "))
   (t "")))
      

(defun org-roam-gt--truncate (st width)
  "Return ST as a string of length WIDTH. Using spaces for padding"
  (truncate-string-to-width (org-roam-gt--to-string st) width nil ? ))

(defun org-roam-gt--format-todo (st width)
  "Return ST as a todo item (prefixed with t:) of width WIDTH."
  (org-roam-gt--truncate
   (concat  (if st "t:" "") st) width))


(defun org-roam-gt--format-tags (tags width)
  "Return TAGS as a string of width WIDTH.
Prefixes every tag with #."
  (org-roam-gt--truncate 
   (mapconcat (lambda (tag) (concat "#" tag)) tags " ")
   width))
  
(defun org-roam-gt--format-file (file)
  "Simply remove org-roam-directory from the path in FILE."
  (substring file (length org-roam-directory))
  )


(defun org-roam-gt-default-format (node)
  "Sample function to format a NODE.
This function is equivalent to the following template

    (setq org-roam-node-display-template
              (concat 
                (propertize \"${todo:10} \" 'face 'org-todo)
                \"${todo:10} \"
                (propertize \"${tags:30} \" 'face 'org-tag)
                \"${title:40} \"
                \"${file}\"
                ))"
  (let (
        (formatted-node     (concat
                             (org-roam-gt--format-todo (org-roam-node-todo node) 10 )
                             " "
                             (propertize
                              (org-roam-gt--format-tags (org-roam-node-tags node) 30))
                             " "
                             (org-roam-gt--truncate (org-roam-node-title node) 40)
                             " "
                             (org-roam-gt--format-file
                              (org-roam-node-file node))))
        )
    (cons
     (propertize formatted-node 'node node)
     node)))

;; define a minor mode to enable/disable the changes

(defun org-roam-gt-mode-enable ()
"Callback when org-roam-mode is enabled."  
(advice-add 'org-roam-node-read--completions :override #'org-roam-gt-node-read--completions)
  )

(defun org-roam-gt-mode-disable ()
  "Callback when org-roam-mode is disabled."  
  (message "disabling")
  (advice-remove 'org-roam-node-read--completions #'org-roam-gt-node-read--completions)
  )

(define-minor-mode org-roam-gt-mode
  "Minor mode that enables improvements in speed in org-roam.

Specifically it improves the speed of the retrieval and
and formatting of nodes from the database."

  :global t
  :lighter   " _o-r-gt_"    ; lighter
  :keymap nil
  (if org-roam-gt-mode
      (org-roam-gt-mode-enable)
    (org-roam-gt-mode-disable)
    )
  )

(provide 'org-roam-gt)
