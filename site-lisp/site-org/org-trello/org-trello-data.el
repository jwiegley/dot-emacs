;;; org-trello-data.el --- org-trello data access functions

;; Copyright (C) 2015-2017  Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>

;; Author: Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>
;; Keywords:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;; Code:

(require 'org-trello-setup)
(require 'org-trello-log)
(require 'org-trello-hash)
(require 's)
(require 'json)
(require 'dash-functional)

(defun orgtrello-data-merge-2-lists-without-duplicates (a-list b-list)
  "Merge the 2 lists A-LIST and B-LIST together without duplicates."
  (-> a-list
      (append b-list)
      delete-dups))

(defun orgtrello-data--entity-with-level-p (entity level)
  "Is the ENTITY with level LEVEL?"
  (-> entity orgtrello-data-entity-level (eq level)))

(defun orgtrello-data-entity-card-p (entity)
  "Is the ENTITY a card?"
  (orgtrello-data--entity-with-level-p entity org-trello--card-level))

(defun orgtrello-data-entity-checklist-p (entity)
  "Is the ENTITY a checklist?"
  (orgtrello-data--entity-with-level-p entity org-trello--checklist-level))

(defun orgtrello-data-entity-item-p (entity)
  "Is the ENTITY an item?"
  (orgtrello-data--entity-with-level-p entity org-trello--item-level))

(defun orgtrello-data-entity-id (entity)
  "Retrieve the id from the ENTITY."
  (let ((id (orgtrello-data-entity-id-or-marker entity)))
    (when (orgtrello-data-id-p id)
      id)))

(defun orgtrello-data-entity-keyword (entity &optional default-value)
  "Retrieve the keyword from the ENTITY.
If the keyword is nil, return the optional DEFAULT-VALUE."
  (orgtrello-hash-gethash-data :keyword entity default-value))

(defun orgtrello-data-entity-name         (entity)     "Retrieve the ENTITY's NAME."             (orgtrello-hash-gethash-data :name         entity))
(defun orgtrello-data-entity-memberships  (entity)     "Retrieve the ENTITY's MEMBERSHIPS."      (orgtrello-hash-gethash-data :memberships  entity))
(defun orgtrello-data-entity-member       (entity)     "Retrieve the ENTITY's MEMBER."           (orgtrello-hash-gethash-data :member       entity))
(defun orgtrello-data-entity-username     (entity)     "Retrieve the ENTITY's USERNAME."         (orgtrello-hash-gethash-data :username     entity))
(defun orgtrello-data-entity-action       (entity)     "Retrieve the ENTITY's ACTION."           (orgtrello-hash-gethash-data :action       entity))
(defun orgtrello-data-entity-board-id     (entity)     "Retrieve the ENTITY's BOARD-id."         (orgtrello-hash-gethash-data :board-id     entity))
(defun orgtrello-data-entity-card-id      (entity)     "Retrieve the ENTITY's CARD-id."          (orgtrello-hash-gethash-data :card-id      entity))
(defun orgtrello-data-entity-list-id      (entity)     "Retrieve the ENTITY's LIST-id."          (orgtrello-hash-gethash-data :list-id      entity))
(defun orgtrello-data-entity-member-ids   (entity)     "Retrieve the ENTITY's MEMBER-ids."       (orgtrello-hash-gethash-data :member-ids   entity))
(defun orgtrello-data-entity-description  (entity)     "Retrieve the ENTITY's DESCRIPTION."      (orgtrello-hash-gethash-data :desc         entity))
(defun orgtrello-data-entity-checklists   (entity)     "Retrieve the ENTITY's CHECKLISTS."       (orgtrello-hash-gethash-data :checklists   entity))
(defun orgtrello-data-entity-items        (entity)     "Retrieve the ENTITY's ITEMS."            (orgtrello-hash-gethash-data :items        entity))
(defun orgtrello-data-entity-position     (entity)     "Retrieve the ENTITY's POSITION."         (orgtrello-hash-gethash-data :position     entity))
(defun orgtrello-data-entity-buffername   (entity)     "Retrieve the ENTITY's BUFFERNAME."       (orgtrello-hash-gethash-data :buffername   entity))
(defun orgtrello-data-entity-checked      (entity)     "Retrieve the ENTITY's CHECKED."          (orgtrello-hash-gethash-data :checked      entity))
(defun orgtrello-data-entity-due          (entity)     "Retrieve the ENTITY's DUE."              (orgtrello-hash-gethash-data :due          entity))
(defun orgtrello-data-entity-id-or-marker (entity)     "Retrieve the ENTITY's ID-or-marker."     (orgtrello-hash-gethash-data :id           entity))
(defun orgtrello-data-entity-level        (entity)     "Retrieve the ENTITY's LEVEL."            (orgtrello-hash-gethash-data :level        entity))
(defun orgtrello-data-entity-closed       (entity)     "Retrieve the ENTITY's CLOSED."           (orgtrello-hash-gethash-data :closed       entity))
(defun orgtrello-data-entity-comments     (entity)     "Retrieve the ENTITY's COMMENTS."         (orgtrello-hash-gethash-data :comments     entity))
(defun orgtrello-data-entity-labels       (entity)     "Retrieve the ENTITY's LABELS."           (orgtrello-hash-gethash-data :labels       entity))
(defun orgtrello-data-entity-tags         (entity)     "Retrieve the ENTITY's TAGS."             (orgtrello-hash-gethash-data :tags         entity))
(defun orgtrello-data-entity-comment-id   (entity)     "Retrieve the ENTITY's COMMENT-ID."       (orgtrello-hash-gethash-data :comment-id   entity))
(defun orgtrello-data-entity-comment-text (entity)     "Retrieve the ENTITY's COMMENT-TEXT."     (orgtrello-hash-gethash-data :comment-text entity))
(defun orgtrello-data-entity-comment-date (entity)     "Retrieve the ENTITY's COMMENT-DATE."     (orgtrello-hash-gethash-data :comment-date entity))
(defun orgtrello-data-entity-comment-user (entity)     "Retrieve the ENTITY's COMMENT-USER."     (orgtrello-hash-gethash-data :comment-user entity))
(defun orgtrello-data-entity-color        (entity)     "Retrieve the ENTITY's COLOR."            (orgtrello-hash-gethash-data :color        entity))
(defun orgtrello-data-entity-lists        (entity)     "Retrieve the ENTITY's LISTS."            (orgtrello-hash-gethash-data :lists        entity))
(defun orgtrello-data-entity-unknown-properties (entity) "Retrieve the ENTITY's UNKNOWN-PROPERTIES." (orgtrello-hash-gethash-data :unknown-properties entity))
(defun orgtrello-data-entity-method       (query-map)  "Retrieve the QUERY-MAP's METHOD."        (orgtrello-hash-gethash-data :method query-map))
(defun orgtrello-data-entity-uri          (query-map)  "Retrieve the QUERY-MAP's URI."           (orgtrello-hash-gethash-data :uri    query-map))
(defun orgtrello-data-entity-sync         (query-map)  "Retrieve the QUERY-MAP's SYNC."          (orgtrello-hash-gethash-data :sync   query-map))
(defun orgtrello-data-entity-params       (query-map)  "Retrieve the QUERY-MAP's PARAMS."        (orgtrello-hash-gethash-data :params query-map))
(defun orgtrello-data-current             (entry-meta) "Retrieve the ENTRY-META's current."      (orgtrello-hash-gethash-data :current     entry-meta))
(defun orgtrello-data-parent              (entry-meta) "Retrieve the ENTRY-META's parent."       (orgtrello-hash-gethash-data :parent      entry-meta))
(defun orgtrello-data-grandparent         (entry-meta) "Retrieve the ENTRY-META's grand-parent." (orgtrello-hash-gethash-data :grandparent entry-meta))

(defun orgtrello-data-put-entity-name         (value entity)     "Update the name with VALUE in ENTITY map."                  (orgtrello-hash-puthash-data :name         value entity))
(defun orgtrello-data-put-entity-memberships  (value entity)     "Update the memberships with VALUE in ENTITY map."           (orgtrello-hash-puthash-data :memberships  value entity))
(defun orgtrello-data-put-entity-member       (value entity)     "Update the member with VALUE in ENTITY map."                (orgtrello-hash-puthash-data :member       value entity))
(defun orgtrello-data-put-entity-username     (value entity)     "Update the username with VALUE in ENTITY map."              (orgtrello-hash-puthash-data :username     value entity))
(defun orgtrello-data-put-entity-action       (value entity)     "Update the action with VALUE in ENTITY map."                (orgtrello-hash-puthash-data :action       value entity))
(defun orgtrello-data-put-entity-board-id     (value entity)     "Update the board-id with VALUE in ENTITY map."              (orgtrello-hash-puthash-data :board-id     value entity))
(defun orgtrello-data-put-entity-card-id      (value entity)     "Update the card-id with VALUE in ENTITY map."               (orgtrello-hash-puthash-data :card-id      value entity))
(defun orgtrello-data-put-entity-list-id      (value entity)     "Update the list-id with VALUE in ENTITY map."               (orgtrello-hash-puthash-data :list-id      value entity))
(defun orgtrello-data-put-entity-member-ids   (value entity)     "Update the member-ids with VALUE in ENTITY map."            (orgtrello-hash-puthash-data :member-ids   value entity))
(defun orgtrello-data-put-entity-description  (value entity)     "Update the description with VALUE in ENTITY map."           (orgtrello-hash-puthash-data :desc         value entity))
(defun orgtrello-data-put-entity-checklists   (value entity)     "Update the checklists with VALUE in ENTITY map."            (orgtrello-hash-puthash-data :checklists   value entity))
(defun orgtrello-data-put-entity-items        (value entity)     "Update the items with VALUE in ENTITY map."                 (orgtrello-hash-puthash-data :items        value entity))
(defun orgtrello-data-put-entity-position     (value entity)     "Update the position with VALUE in ENTITY map."              (orgtrello-hash-puthash-data :position     value entity))
(defun orgtrello-data-put-entity-buffername   (value entity)     "Update the buffername with VALUE in ENTITY map."            (orgtrello-hash-puthash-data :buffername   value entity))
(defun orgtrello-data-put-entity-checked      (value entity)     "Update the checked with VALUE in ENTITY map."               (orgtrello-hash-puthash-data :checked      value entity))
(defun orgtrello-data-put-entity-due          (value entity)     "Update the due with VALUE in ENTITY map."                   (orgtrello-hash-puthash-data :due          value entity))
(defun orgtrello-data-put-entity-id           (value entity)     "Update the id with VALUE in ENTITY map."                    (orgtrello-hash-puthash-data :id           value entity))
(defun orgtrello-data-put-entity-level        (value entity)     "Update the level with VALUE in ENTITY map."                 (orgtrello-hash-puthash-data :level        value entity))
(defun orgtrello-data-put-entity-closed       (value entity)     "Update the closed with VALUE in ENTITY map."                (orgtrello-hash-puthash-data :closed       value entity))
(defun orgtrello-data-put-entity-comments     (value entity)     "Update the comments with VALUE in ENTITY map."              (orgtrello-hash-puthash-data :comments     value entity))
(defun orgtrello-data-put-entity-labels       (value entity)     "Update the labels with VALUE in ENTITY map."                (orgtrello-hash-puthash-data :labels       value entity))
(defun orgtrello-data-put-entity-tags         (value entity)     "Update the tags with VALUE in ENTITY map."                  (orgtrello-hash-puthash-data :tags         value entity))
(defun orgtrello-data-put-entity-unknown-properties (value entity) "Update the tags with VALUE in ENTITY map."                (orgtrello-hash-puthash-data :unknown-properties value entity))
(defun orgtrello-data-put-entity-keyword      (value entity)     "Update the keyword with VALUE in ENTITY map."               (orgtrello-hash-puthash-data :keyword      value entity))
(defun orgtrello-data-put-entity-comment-id   (value entity)     "Update the comment-id with VALUE in ENTITY map."            (orgtrello-hash-puthash-data :comment-id   value entity))
(defun orgtrello-data-put-entity-comment-text (value entity)     "Update the comment-text with VALUE in ENTITY map."          (orgtrello-hash-puthash-data :comment-text value entity))
(defun orgtrello-data-put-entity-comment-date (value entity)     "Update the comment-date with VALUE in ENTITY map."          (orgtrello-hash-puthash-data :comment-date value entity))
(defun orgtrello-data-put-entity-comment-user (value entity)     "Update the comment-user with VALUE in ENTITY map."          (orgtrello-hash-puthash-data :comment-user value entity))
(defun orgtrello-data-put-entity-method       (value query-map)  "Update the method with VALUE in QUERY-MAP."                 (orgtrello-hash-puthash-data :method       value query-map))
(defun orgtrello-data-put-entity-uri          (value query-map)  "Update the uri with VALUE in QUERY-MAP."                    (orgtrello-hash-puthash-data :uri          value query-map))
(defun orgtrello-data-put-entity-sync         (value query-map)  "Update the sync with VALUE in QUERY-MAP."                   (orgtrello-hash-puthash-data :sync         value query-map))
(defun orgtrello-data-put-entity-params       (value query-map)  "Update the params with VALUE in QUERY-MAP."                 (orgtrello-hash-puthash-data :params       value query-map))
(defun orgtrello-data-put-current             (value entry-meta) "Update the current entry with VALUE in ENTRY-META map."     (orgtrello-hash-puthash-data :current      value entry-meta))
(defun orgtrello-data-put-parent              (value entry-meta) "Update the parent entry with VALUE in ENTRY-META map."      (orgtrello-hash-puthash-data :parent       value entry-meta))
(defun orgtrello-data-put-grandparent         (value entry-meta) "Update the grandparent entry with VALUE in ENTRY-META map." (orgtrello-hash-puthash-data :grandparent  value entry-meta))

(defun orgtrello-data--compute-level (entity-map)
  "Given an ENTITY-MAP, compute the entity level."
  (cond ((orgtrello-data-entity-list-id entity-map) org-trello--card-level)
        ((orgtrello-data-entity-card-id entity-map) org-trello--checklist-level)
        ((orgtrello-data-entity-checked entity-map) org-trello--item-level)
        (t nil)))

(defun orgtrello-data-make-hash-org (member-ids level keyword name id due position buffer-name desc tags unknown-properties)
  "Compute the hash-map from MEMBER-IDS LEVEL KEYWORD NAME ID DUE POSITION BUFFER-NAME DESC TAGS UNKNOWN-PROPERTIES."
  (->> (orgtrello-hash-empty-hash)
       (orgtrello-data-put-entity-buffername         buffer-name)
       (orgtrello-data-put-entity-position           position)
       (orgtrello-data-put-entity-level              level)
       (orgtrello-data-put-entity-keyword            keyword)
       (orgtrello-data-put-entity-name               name)
       (orgtrello-data-put-entity-id                 id)
       (orgtrello-data-put-entity-due                due)
       (orgtrello-data-put-entity-member-ids         member-ids)
       (orgtrello-data-put-entity-description        desc)
       (orgtrello-data-put-entity-tags               tags)
       (orgtrello-data-put-entity-unknown-properties unknown-properties)))

(defun orgtrello-data-make-hierarchy (current &optional parent grandparent)
  "Build an org-trello hierarchy using CURRENT, PARENT and GRANDPARENT maps."
  (->> (orgtrello-hash-empty-hash)
       (orgtrello-data-put-current current)
       (orgtrello-data-put-parent parent)
       (orgtrello-data-put-grandparent grandparent)))

(defvar orgtrello-controller--data-map-keywords
  (orgtrello-hash-make-properties `((url            . :url)
                                    (id             . :id)
                                    (name           . :name)
                                    (idMembers      . :member-ids)
                                    (idList         . :list-id)
                                    (checklists     . :checklists) ;; for full data
                                    (idChecklists   . :checklists) ;; for checklist ids (those 2 keywords are mutually exclusive and are dealt at request level)
                                    (idBoard        . :board-id)
                                    (due            . :due)
                                    (desc           . :desc)
                                    (closed         . :closed)
                                    (idCard         . :card-id)
                                    (checkItems     . :items)
                                    (state          . :checked)
                                    (status         . :status)
                                    (pos            . :position)
                                    (keyword        . :keyword)
                                    (member-ids     . :member-ids)
                                    (member         . :member)
                                    (memberships    . :memberships)
                                    (username       . :username)
                                    (fullName       . :full-name)
                                    (actions        . :comments)
                                    (labelNames     . :labels)
                                    (lists          . :lists)
                                    (labels         . :labels)
                                    (color          . :color))))

(defun orgtrello-data--deal-with-key (key)
  "Return KEY as is if it's a keyword or return its orgtrello representation."
  (cond ((keywordp key) key)
        (t             (gethash key orgtrello-controller--data-map-keywords))))

(defun orgtrello-data--dispatch-parse-data-fn (key)
  "Compute the parsing function depending on the KEY."
  (cond ((eq :comments key) 'orgtrello-data--parse-actions)
        (t                  'orgtrello-data-parse-data)))

(defun orgtrello-data--parse-actions (data &optional size)
  "Given an association list DATA, filter and return only the 'comment' actions.
SIZE is a useless parameter, only here to satisfy an implementation detail."
  (--map (->> (orgtrello-hash-empty-hash)
              (orgtrello-data-put-entity-comment-id   (assoc-default 'id it))
              (orgtrello-data-put-entity-comment-text (->> it (assoc-default 'data) (assoc-default 'text)))
              (orgtrello-data-put-entity-comment-date (assoc-default 'date it))
              (orgtrello-data-put-entity-comment-user (->> it (assoc-default 'memberCreator) (assoc-default 'username))))
         data))

(defun orgtrello-data-parse-data (entities)
  "Parse the data in ENTITIES to an org-trello format."
  (cond ((eq :json-false entities)                                           nil)
        ((--any? (funcall it entities) '(stringp symbolp numberp functionp)) entities)
        ((arrayp entities)                                                   (mapcar 'orgtrello-data-parse-data entities))
        (t
         (let ((hmap (--reduce-from (let ((key (car it))
                                          (val (cdr it)))
                                      (-when-let (new-key (orgtrello-data--deal-with-key key))
                                        (orgtrello-hash-puthash-data new-key (funcall (orgtrello-data--dispatch-parse-data-fn new-key) val) acc))
                                      acc)
                                    (orgtrello-hash-empty-hash)
                                    entities)))
           (-when-let (level (orgtrello-data--compute-level hmap)) (orgtrello-data-put-entity-level level hmap))
           hmap))))

(defun orgtrello-data-format-labels (labels)
  "Given an assoc list of LABELS, serialize it."
  (->> labels
       (-map (-partial #'s-join ": "))
       (s-join "\n\n")))

(defun orgtrello-data-id-p (id)
  "Is the string ID a trello identifier?"
  (and id (not (string-match-p (format "^%s-" org-trello--label-key-marker) id))))

(defun orgtrello-data--merge-item (trello-item org-item)
  "Merge TRELLO-ITEM and ORG-ITEM together.
If TRELLO-ITEM is nil, return the ORG-ITEM."
  (if trello-item
      (->> (orgtrello-hash-init-map-from org-item)
        (orgtrello-data-put-entity-level   (orgtrello-data-entity-level trello-item))
        (orgtrello-data-put-entity-id      (orgtrello-data-entity-id trello-item))
        (orgtrello-data-put-entity-name    (orgtrello-data-entity-name trello-item))
        (orgtrello-data-put-entity-keyword (orgtrello-data-entity-keyword trello-item)))
    org-item))

(defun orgtrello-data--compute-state-item-checkbox (state)
  "Compute the STATE of the item checkbox."
  (orgtrello-data--compute-state-generic state '("[X]" "[ ]")))

(defun orgtrello-data--compute-state-item (state)
  "Compute the STATE of the checkbox."
  (orgtrello-data--compute-state-generic state `(,org-trello--done ,org-trello--todo)))

(defun orgtrello-data--merge-checklist (trello-checklist org-checklist)
  "Merge TRELLO-CHECKLIST and ORG-CHECKLIST together.
If TRELLO-CHECKLIST is nil, return ORG-CHECKLIST."
  (if trello-checklist
      (->> (orgtrello-hash-init-map-from org-checklist)
        (orgtrello-data-put-entity-level (orgtrello-data-entity-level trello-checklist))
        (orgtrello-data-put-entity-name  (orgtrello-data-entity-name trello-checklist))
        (orgtrello-data-put-entity-id    (orgtrello-data-entity-id trello-checklist)))
    org-checklist))

(defun orgtrello-data-entity-member-ids-as-list (entity)
  "Retrieve the users assigned to the ENTITY."
  (-> entity
    orgtrello-data-entity-member-ids
    orgtrello-data--users-from))

(defun orgtrello-data--merge-member-ids (trello-card org-card)
  "Merge users assigned from TRELLO-CARD and ORG-CARD."
  (--> trello-card
       (orgtrello-data-entity-member-ids-as-list it)
       (orgtrello-data-merge-2-lists-without-duplicates it (orgtrello-data-entity-member-ids-as-list org-card))
       (-map (lambda (member-id) (gethash member-id (orgtrello-setup-users))) it)
       (orgtrello-data--users-to it)))

(defun orgtrello-data--labels-to-tags (labels)
  "Given a list of tags (LABELS), return a joined string with : as separator."
  (when labels
    (-when-let (tags (s-join ":" labels))
      (concat ":" tags ":"))))

(defun orgtrello-data--labels-hash-to-tags (labels)
  "Given a hash map with LABELS entry, return a tag string joined by : separator."
  (when labels
    (orgtrello-data--labels-to-tags
     (mapcar (lambda (label) (-if-let (l (orgtrello-data-entity-color label))
                            l
                          "grey")) labels))))

(defun orgtrello-data--from-tags-to-list (tags)
  "Given TAGS, a : string separated string, return a list of non empty string."
  (->> tags
       (s-split ":")
       (-filter (-compose #'not (-partial #'string= "")))))

(defun orgtrello-data--merge-labels-as-tags (trello-labels org-tags)
  "Given TRELLO-LABELS and ORG-TAGS, merge both of them."
  (if org-tags
      (let ((org-tags-as-list (orgtrello-data--from-tags-to-list org-tags))
            (trello-tags-as-list (orgtrello-data--from-tags-to-list trello-labels)))
        (orgtrello-data--labels-to-tags (orgtrello-data-merge-2-lists-without-duplicates org-tags-as-list trello-tags-as-list)))
    trello-labels))

(defun orgtrello-data--merge-card (trello-card org-card)
  "Merge TRELLO-CARD and ORG-CARD together.
If TRELLO-CARD is nil, return ORG-CARD."
  (if trello-card
      (->> (orgtrello-hash-init-map-from org-card)
           (orgtrello-data-put-entity-tags         (orgtrello-data--merge-labels-as-tags
                                                    (orgtrello-data-entity-tags trello-card)
                                                    (orgtrello-data-entity-tags org-card)))
           (orgtrello-data-put-entity-comments    (orgtrello-data-entity-comments trello-card))
           (orgtrello-data-put-entity-level       (orgtrello-data-entity-level trello-card))
           (orgtrello-data-put-entity-id          (orgtrello-data-entity-id trello-card))
           (orgtrello-data-put-entity-name        (orgtrello-data-entity-name trello-card))
           (orgtrello-data-put-entity-keyword     (orgtrello-data-entity-keyword trello-card))
           (orgtrello-data-put-entity-member-ids  (orgtrello-data--merge-member-ids trello-card org-card))
           (orgtrello-data-put-entity-description (orgtrello-data-entity-description trello-card))
           (orgtrello-data-put-entity-due         (orgtrello-data-entity-due trello-card)))
    org-card))

(defun orgtrello-data--dispatch-merge-fn (entity)
  "Dispatch the function fn to merge the ENTITY."
  (cond ((orgtrello-data-entity-card-p entity)      'orgtrello-data--merge-card)
        ((orgtrello-data-entity-checklist-p entity) 'orgtrello-data--merge-checklist)
        ((orgtrello-data-entity-item-p entity)      'orgtrello-data--merge-item)))

(defun orgtrello-data-merge-entities-trello-and-org (trello-data org-data)
  "Merge to TRELLO-DATA the ORG-DATA, (org-entity entities inside the trello-entities)."
  (let ((trello-entities  (car trello-data))
        (trello-adjacency (cadr trello-data))
        (org-entities     (car org-data))
        (org-adjacency    (cadr org-data)))

    (maphash (lambda (id trello-entity)
               (orgtrello-hash-puthash-data id
                                            (funcall (orgtrello-data--dispatch-merge-fn trello-entity)
                                                     trello-entity
                                                     (orgtrello-data--get-entity id org-entities))
                                            trello-entities) ;; updating entity to trello
               (orgtrello-hash-puthash-data id
                                            (orgtrello-data-merge-2-lists-without-duplicates (gethash id trello-adjacency) (gethash id org-adjacency))
                                            trello-adjacency)) ;; update entity adjacency to trello
             trello-entities)

    ;; copy the entities only present on org files to the trello entities.
    (maphash (lambda (id org-entity)
               (unless (gethash id trello-entities)
                 (orgtrello-hash-puthash-data id org-entity trello-entities)
                 (orgtrello-hash-puthash-data id (gethash id org-adjacency) trello-adjacency)))
             org-entities)

    (list trello-entities trello-adjacency)))

(defun orgtrello-data--compute-card-status (card-id-list)
  "Given a CARD-ID-LIST, compute its status."
  (gethash card-id-list org-trello--hmap-list-orgkeyword-id-name))

(defun orgtrello-data--get-entity (id entities-hash)
  "Retrieve the entity with ID in ENTITIES-HASH."
  (gethash id entities-hash))

(defun orgtrello-data--compute-state-generic (state list-state)
  "Depending on the STATE and a generic LIST-STATE, compute the state.
If state is \"complete\" or \"DONE\", the first element is returned, otherwise the second."
  (if (or (string= "complete" state)
          (string= org-trello--done state))
      (car list-state)
    (cadr list-state)))

(defun orgtrello-data--users-from (string-users)
  "Compute the users name from the comma separated values STRING-USERS."
  (when string-users
    (s-split "," string-users t)))

(defun orgtrello-data--users-to (users)
  "Given a list of USERS, compute the comma separated string of users."
  (if users
      (s-join "," users)
    ""))

(defun orgtrello-data-get-children (entity entities-adjacencies)
  "Given ENTITY and ENTITIES-ADJACENCIES, return the children of the entity."
  (-let (((_ adjacencies) entities-adjacencies))
    (-> entity
        orgtrello-data-entity-id-or-marker
        (orgtrello-data--get-entity adjacencies))))

(defun orgtrello-data-get-entity (entity-id entities-adjacencies)
  "Given ENTITY-ID, return the complete entity.
ENTITIES-ADJACENCIES provides needed information."
  (-let (((entities _) entities-adjacencies))
    (orgtrello-data--get-entity entity-id entities)))

(defun orgtrello-data-to-org-trello-card (trello-card)
  "Map a TRELLO-CARD to an org-trello one."
  (->> trello-card
       (orgtrello-data-put-entity-tags (orgtrello-data--labels-hash-to-tags (orgtrello-data-entity-labels trello-card)))
       (orgtrello-data-put-entity-labels nil)
       (orgtrello-data-put-entity-level org-trello--card-level)
       (orgtrello-data-put-entity-keyword (-> trello-card orgtrello-data-entity-list-id orgtrello-data--compute-card-status))
       (orgtrello-data-put-entity-list-id nil)
       (orgtrello-data-put-entity-member-ids (->> trello-card orgtrello-data-entity-member-ids orgtrello-data--users-to))
       (orgtrello-data-put-entity-comments (-> trello-card orgtrello-data-entity-comments))
       (orgtrello-data-put-entity-checklists (->> trello-card orgtrello-data-entity-checklists (mapcar #'orgtrello-data-to-org-trello-checklist)))))

(defun orgtrello-data-to-org-trello-checklist (trello-checklist)
  "Map a TRELLO-CHECKLIST to an org-trello one."
  (->> trello-checklist
    (orgtrello-data-put-entity-level org-trello--checklist-level)
    (orgtrello-data-put-entity-items (->> trello-checklist orgtrello-data-entity-items (mapcar #'orgtrello-data-to-org-trello-item)))))

(defun orgtrello-data-to-org-trello-item (trello-item)
  "Map a TRELLO-ITEM to an org-trello one."
  (->> trello-item
    (orgtrello-data-put-entity-level org-trello--item-level)
    (orgtrello-data-put-entity-keyword (-> trello-item orgtrello-data-entity-checked orgtrello-data--compute-state-item))
    (orgtrello-data-put-entity-checked nil)))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-data loaded!")

(provide 'org-trello-data)
;;; org-trello-data.el ends here
