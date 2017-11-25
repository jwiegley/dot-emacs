;;; org-trello-buffer.el --- Manipulation functions of org-trello buffer

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
(require 'org-trello-utils)
(require 'org-trello-log)
(require 'org-trello-hash)
(require 'org-trello-data)
(require 'org-trello-query)
(require 'org-trello-entity)
(require 'org-trello-cbx)
(require 'org-trello-backend)
(require 'org-trello-date)
(require 'dash-functional)

(defun orgtrello-buffer-global-properties-region ()
  "Compute the global properties from the buffer.
Expects the :PROPERTIES: to start the buffer.
:: () -> (Int, Int)"
  (save-excursion
    (goto-char (point-min))
    (let ((point-min-start (save-excursion
                             (search-forward ":PROPERTIES:" nil t)
                             (point-at-bol))))
      point-min-start
      (when (eq point-min-start 1) ;; only when :PROPERTIES: as first position!
        (list point-min-start (save-excursion
                                (search-forward ":END:" nil t)))))))

(defun orgtrello-buffer-org-delete-property (property)
  "Delete the PROPERTY at point."
  (funcall (if (orgtrello-entity-org-checkbox-p)
               'orgtrello-cbx-org-delete-property
             'org-delete-property) property))

(defun orgtrello-buffer-org-entry-put (point property value)
  "Put at POINT the PROPERTY with VALUE.
If the VALUE is nil or empty, remove such PROPERTY."
  (if (or (null value) (string= "" value))
      (orgtrello-buffer-delete-property-from-entry property)
    (org-entry-put point property value)))

(defun orgtrello-buffer--extract-card-description-at-point ()
  "Given the current position, extract the text content of current card."
  (let* ((start (orgtrello-entity-card-description-start-point))
         (end   (orgtrello-entity-card-metadata-end-point)))
    (if (< start end)
        (->> (buffer-substring-no-properties start end)
             s-lines
             (--map (if (s-equals? "" it)
                        it
                      (substring it org-trello-buffer--indent-description)))
             (s-join "\n"))
      "")))

(defun orgtrello-buffer--extract-comment-description-at-point ()
  "Given the current position, extract the text content of current card."
  (apply 'buffer-substring-no-properties
         (orgtrello-entity-comment-description-region)))

(defun orgtrello-buffer-get-local-checksum ()
  "Retrieve local checksum."
  (funcall (if (orgtrello-entity-org-checkbox-p)
               'orgtrello-buffer-get-checkbox-local-checksum
             'orgtrello-buffer-get-card-local-checksum)))

(defun orgtrello-buffer-get-card-local-checksum ()
  "Retrieve the card's current local checksum."
  (orgtrello-buffer-card-entry-get (point) org-trello--label-key-local-checksum))

(defun orgtrello-buffer-get-checkbox-local-checksum ()
  "Retrieve the checkbox's current local checksum."
  (orgtrello-buffer-org-entry-get (point) org-trello--label-key-local-checksum))

(defalias 'orgtrello-buffer-org-get-property 'assoc-default
  "Retrieve the PROPERTY-KEY in PROPERTIES.")

(defun orgtrello-buffer-org-file-get-property (property-key)
  "Return the PROPERTY-KEY present in the org buffer."
  (orgtrello-buffer-org-get-property property-key
                                     (orgtrello-buffer-org-file-properties)))

(defun orgtrello-buffer-board-name ()
  "Compute the board's name."
  (orgtrello-buffer-org-file-get-property org-trello--property-board-name))

(defun orgtrello-buffer-board-id ()
  "Compute the board's id."
  (orgtrello-buffer-org-file-get-property org-trello--property-board-id))

(defun orgtrello-buffer-me ()
  "Compute the board's current user."
  (orgtrello-buffer-org-file-get-property org-trello--property-user-me))

(defun orgtrello-buffer-colors ()
  "Compute the list of colors."
  (-map (-partial 'format "%s")
        (orgtrello-hash-values orgtrello-setup-data-color-keywords)))

(defun orgtrello-buffer-labels ()
  "Compute the board's current labels and return it as an association list."
  (-map (-juxt #'identity #'orgtrello-buffer-org-file-get-property)
        (orgtrello-buffer-colors)))

(defun orgtrello-buffer-pop-up-with-content (title body-content)
  "Buffer `org-trello--title-buffer-information' with TITLE & BODY-CONTENT."
  (with-current-buffer-window
   org-trello--title-buffer-information nil nil
   (temp-buffer-resize-mode 1)
   (insert (format "%s:\n\n%s" title body-content))))

(defun orgtrello-buffer-trim-input-comment (comment)
  "Trim the COMMENT."
  (let ((trim-comment comment))
    (while (string-match "\\`# .*\n[ \t\n]*" trim-comment) ;; remove # comments
      (setq trim-comment (replace-match "" t t trim-comment)))
    (->> trim-comment
         (s-split "\n")
         nreverse
         (--drop-while (string= "" it))
         nreverse
         (s-join "\n"))))

(defun orgtrello-buffer-write-item (item-id entities)
  "Write the ITEM-ID to the org buffer.
ENTITIES are the complete map of entities in the org-buffer."
  (->> entities
       (gethash item-id)
       (orgtrello-buffer-write-entity item-id))
  (save-excursion ;; item writing does insert a new line
    (forward-line -1)
    (orgtrello-buffer-write-properties-at-pt item-id)))

(defalias 'orgtrello-buffer-write-checklist-header 'orgtrello-buffer-write-entity)

(defun orgtrello-buffer-write-checklist (checklist-id entities adjacency)
  "Write the CHECKLIST-ID and its structure inside the org buffer.
ENTITIES is the map of entities in the org-buffer.
ADJACENCY is map of entity-id, children of the entity.
At the end of it all, the cursor is moved after the new written text."
  (orgtrello-buffer-write-checklist-header
   checklist-id
   (gethash checklist-id entities)) ;; beware this writes a new line
  (let* ((item-ids             (gethash checklist-id adjacency))
         (nb-lines-to-get-back
          (1+ (if item-ids (length item-ids) 0)))) ;; +1 because of the injected
    ;; line by headers
    (mapc (lambda (item-id) (orgtrello-buffer-write-item item-id entities))
          item-ids) ;; cursor will move with as much item as it exists
    (save-excursion ;; one item by line so we need to get back to as much item
      ;; as it exists
      (forward-line (* -1 nb-lines-to-get-back))
      (orgtrello-buffer-write-properties-at-pt checklist-id))))

(defun orgtrello-buffer-update-property-member-ids (entity)
  "Given ENTITY's date, update the users assigned property card entry."
  (->> entity
       orgtrello-data-entity-member-ids
       (replace-regexp-in-string org-trello--label-key-user-prefix "")
       orgtrello-buffer-set-usernames-assigned-property))

(defun orgtrello-buffer--write-comments (entity)
  "Given ENTITY's date, update last comments ."
  (->> entity
       orgtrello-data-entity-comments
       orgtrello-buffer--write-comments-at-point))

(defun orgtrello-buffer--write-comments-at-point (comments)
  "Write COMMENTS in the buffer at point."
  (when comments
    (mapc 'orgtrello-buffer--write-comment-at-point comments)
    (insert "\n")));; hack, otherwise, the buffer is messed up.
;; Please, people, again feel free to improve this.

(defun orgtrello-buffer--write-comment-at-point (comment)
  "Write the COMMENT at the current position."
  (-> comment
      orgtrello-buffer--serialize-comment
      insert)
  (orgtrello-buffer-write-local-comment-checksum-at-point))

(defun orgtrello-buffer--prepare-comment (comment)
  "Prepare COMMENT string for writing on disk.
This to avoid conflict between `org-mode' and markdown syntax."
  (->> (s-split "\n" comment)
       (-map (-rpartial #'s-append "  "))
       (s-join "\n")))

(defun orgtrello-buffer--serialize-comment (comment)
  "Serialize COMMENT as string."
  (let* ((comment-user (orgtrello-data-entity-comment-user comment))
         (comment-date (orgtrello-data-entity-comment-date comment))
         (comment-id (orgtrello-data-entity-comment-id comment))
         (comment-str (-> comment
                          orgtrello-data-entity-comment-text
                          orgtrello-buffer--prepare-comment)))
    (format "\n** COMMENT %s, %s\n:PROPERTIES:\n:orgtrello-id: %s\n:END:\n%s\n"
            comment-user comment-date comment-id comment-str)))

(defun orgtrello-buffer-update-properties-unknown (unknown-properties)
  "Write the alist UNKNOWN-PROPERTIES inside standard properties org drawer."
  (mapc (lambda (property)
          (let ((key (car property))
                (value (cdr property)))
            (orgtrello-buffer-org-entry-put (point) key value)))
        unknown-properties))

(defun orgtrello-buffer--write-card-description (description)
  "Write at point the current card's DESCRIPTION if present (and indent it)."
  (when description
    (let ((start (point)))
      (insert (format "%s" description))
      (indent-rigidly start (point) org-trello-buffer--indent-description))))

(defun orgtrello-buffer-write-card-header (card-id card)
  "Given a CARD-ID CARD entity, write its data and properties header."
  (orgtrello-buffer-write-entity card-id card)
  (orgtrello-buffer-update-property-member-ids card)
  (orgtrello-buffer-update-properties-unknown
   (orgtrello-data-entity-unknown-properties card))
  (orgtrello-buffer--write-card-description
   (orgtrello-data-entity-description card)))

(defun orgtrello-buffer-write-card (card-id card entities adjacency)
  "Write the CARD-ID CARD and its structure inside the org buffer.
The cursor position will move after the newly inserted card.
ENTITIES is the map of entities in the org-buffer.
ADJACENCY is map of entity-id, children of the entity."
  (orgtrello-buffer-write-card-header card-id card)
  (insert "\n")
  (-when-let (checklist-ids (gethash card-id adjacency))
    (mapc (lambda (checklist-id)
            (orgtrello-buffer-write-checklist checklist-id
                                              entities adjacency))
          checklist-ids))
  (save-excursion
    (orgtrello-entity-back-to-card)
    (orgtrello-buffer-write-properties-at-pt card-id))
  (orgtrello-buffer--write-comments card))

(defun orgtrello-buffer-checklist-beginning-pt ()
  "Compute the current checklist's beginning point."
  (cond ((orgtrello-entity-checklist-at-pt) (point-at-bol))
        ((orgtrello-entity-item-at-pt) (save-excursion
                                         (org-beginning-of-item-list)
                                         (forward-line -1)
                                         (beginning-of-line)
                                         (point)))))

(defun orgtrello-buffer--write-checksum-at-pt (compute-checksum-fn)
  "Generic function to write the checksum at current position.
COMPUTE-CHECKSUM-FN, function which takes no parameter and return a checksum."
  (->> (funcall compute-checksum-fn)
       (orgtrello-buffer-set-property org-trello--label-key-local-checksum)))

(defun orgtrello-buffer-write-local-card-checksum ()
  "Write the card's checksum."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (orgtrello-buffer-write-local-card-checksum-at-point)))

(defun orgtrello-buffer-write-local-card-checksum-at-point ()
  "Given the current card at point, set the local checksum of the card."
  (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-card-checksum))

(defun orgtrello-buffer-write-local-checklist-checksum ()
  "Write the local checksum of the checklist."
  (save-excursion
    (goto-char (orgtrello-buffer-checklist-beginning-pt))
    (orgtrello-buffer-write-local-checklist-checksum-at-point)))

(defun orgtrello-buffer-write-local-checklist-checksum-at-point ()
  "Given the current card at point, set the local checksum of the card."
  (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-checklist-checksum))

(defun orgtrello-buffer-write-local-item-checksum-at-point ()
  "Given the current checkbox at point, set the local checksum of the checkbox."
  (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-item-checksum))

(defun orgtrello-buffer-write-local-comment-checksum-at-point ()
  "Given the current comment at point, set the local checksum of the comment."
  (orgtrello-buffer--write-checksum-at-pt 'orgtrello-buffer-comment-checksum))

(defun orgtrello-buffer-write-local-checksum-at-pt ()
  "Update the checksum at point.
If on a card, update the card's checksum.
Otherwise, if on a checklist, update the checklist's and the card's checksum.
Otherwise, on an item, update the item's, checklist's and card's checksum."
  (save-excursion
    (let ((actions
           (cond ((orgtrello-entity-org-comment-p)
                  '(orgtrello-entity-back-to-card
                    orgtrello-buffer-write-local-comment-checksum-at-point
                    org-up-element
                    orgtrello-buffer-write-local-card-checksum))
                 ((orgtrello-entity-card-at-pt)
                  '(orgtrello-buffer-write-local-card-checksum-at-point))
                 ((orgtrello-entity-checklist-at-pt)
                  '(orgtrello-buffer-write-local-checklist-checksum-at-point
                    orgtrello-buffer-write-local-card-checksum))
                 ((orgtrello-entity-item-at-pt)
                  '(orgtrello-buffer-write-local-item-checksum-at-point
                    orgtrello-buffer-write-local-checklist-checksum
                    orgtrello-buffer-write-local-card-checksum)))))
      (mapc 'funcall actions))))

(defun orgtrello-buffer-write-properties-at-pt (id)
  "Update the properties at point, beginning with ID.
Depending on ORGCHECKBOX-P, compute the checkbox checksum or the card.
Update the current entity's id and compute the current checksum and update it."
  (orgtrello-buffer-set-property org-trello--label-key-id id)
  (when (orgtrello-data-id-p id) ;; we do not compute the checksum
    (orgtrello-buffer-write-local-checksum-at-pt)))

(defun orgtrello-buffer-write-entity (entity-id entity)
  "Write the ENTITY-ID ENTITY in the buffer to the current position.
Move the cursor position."
  (orgtrello-log-msg orgtrello-log-info
                     "Synchronizing entity '%s' with id '%s'..."
                     (orgtrello-data-entity-name entity) entity-id)
  (insert (orgtrello-buffer-compute-entity-to-org-entry entity)))

(defun orgtrello-buffer-clean-region (region-start region-end)
  "Clean region delimited by REGION-START and REGION-END.
Remove text and overlays."
  (orgtrello-buffer-remove-overlays region-start region-end)
  (delete-region region-start region-end))

(defun orgtrello-buffer--compute-entity-to-org-entry-fn (entity)
  "Given the ENTITY, compute the function that serializes entity in org format."
  (cond ((orgtrello-data-entity-card-p entity)
         'orgtrello-buffer--compute-card-to-org-entry)
        ((orgtrello-data-entity-checklist-p entity)
         'orgtrello-buffer--compute-checklist-to-org-entry)
        ((orgtrello-data-entity-item-p entity)
         'orgtrello-buffer--compute-item-to-org-entry)))

(defun orgtrello-buffer-compute-entity-to-org-entry (entity)
  "Given an ENTITY, compute its org representation."
  (funcall (orgtrello-buffer--compute-entity-to-org-entry-fn entity) entity))

(defun orgtrello-buffer--compute-due-date (due-date)
  "Compute the format of the DUE-DATE."
  (if due-date
      (format "%s <%s>\n" org-trello--property-deadline-prefix
              (orgtrello-date-convert-trello-date-to-org-date due-date))
    ""))

(defun orgtrello-buffer--private-compute-card-to-org-entry (name status due tags)
  "Compute the org format of a card with NAME, STATUS, DUE date and TAGS."
  (let ((prefix-string (format "*%s %s" (if status (format " %s" status) "")
                               name)))
    (format "%s%s\n%s" prefix-string
            (orgtrello-buffer--serialize-tags prefix-string tags)
            (orgtrello-buffer--compute-due-date due))))

(defun orgtrello-buffer--serialize-tags (prefix-string tags)
  "Given a PREFIX-STRING and TAGS, compute the 'org-mode' serialization string.
If tags is empty, return an empty string.
If PREFIX-STRING's length is superior to 72, return tags.
Otherwise, return tags with as much space needed to start at position 72."
  (if (or (null tags) (string= "" tags))
      ""
    (let ((l (length prefix-string)))
      (format "%s%s" (if (< 72 l) " " (orgtrello-utils-symbol " " (- 72 l)))
              tags))))

(defun orgtrello-buffer--compute-card-to-org-entry (card)
  "Given a CARD, compute its 'org-mode' entry equivalence."
  (orgtrello-buffer--private-compute-card-to-org-entry
   (orgtrello-data-entity-name card)
   (orgtrello-data-entity-keyword card)
   (orgtrello-data-entity-due card)
   (orgtrello-data-entity-tags card)))

(defun orgtrello-buffer--compute-state-checkbox (state)
  "Compute the STATE of the checkbox."
  (orgtrello-data--compute-state-generic state '("[X]" "[-]")))

(defun orgtrello-buffer--compute-level-into-spaces (level)
  "LEVEL 2 is 0 spaces, otherwise 2 spaces.
This plus the checklist indentation."
  (+ org-trello--checklist-indent (if (equal level org-trello--checklist-level)
                                      0
                                    2)))

(defun orgtrello-buffer--compute-checklist-to-org-checkbox (name
                                                            &optional level
                                                            status)
  "Compute checklist with NAME & optional LEVEL, STATUS to org checkbox format."
  (format "%s- %s %s\n"
          (-> level
              orgtrello-buffer--compute-level-into-spaces
              orgtrello-utils-space)
          (orgtrello-buffer--compute-state-checkbox status)
          name))

(defun orgtrello-buffer--compute-item-to-org-checkbox (name
                                                       &optional level status)
  "Compute item with NAME & optional LEVEL & STATUS to org checkbox format."
  (format "%s- %s %s\n"
          (-> level
              orgtrello-buffer--compute-level-into-spaces
              orgtrello-utils-space)
          (orgtrello-data--compute-state-item-checkbox status)
          name))

(defun orgtrello-buffer--compute-checklist-to-org-entry (checklist)
  "Given a CHECKLIST, compute its 'org-mode' entry equivalence.
The optional ORGCHECKBOX-P is not used."
  (orgtrello-buffer--compute-checklist-to-org-checkbox
   (orgtrello-data-entity-name checklist)
   org-trello--checklist-level
   "incomplete"))

(defun orgtrello-buffer--compute-item-to-org-entry (item)
  "Given a checklist ITEM, compute its 'org-mode' entry equivalence."
  (orgtrello-buffer--compute-item-to-org-checkbox
   (orgtrello-data-entity-name item)
   org-trello--item-level
   (orgtrello-data-entity-keyword item)))

(defun orgtrello-buffer--put-card-with-adjacency (cur-meta entities adjacency)
  "Deal with adding the CUR-META in ENTITIES and ADJACENCY."
  (-> cur-meta
      (orgtrello-buffer--put-entities entities)
      (list adjacency)))

(defun orgtrello-buffer--dispatch-create-entities-map-with-adjacency (entity)
  "Given the ENTITY, return the function to add the entity and adjacency."
  (if (orgtrello-data-entity-card-p entity)
      'orgtrello-buffer--put-card-with-adjacency
    'orgtrello-backend--put-entities-with-adjacency))

(defun orgtrello-buffer-build-org-card-structure (buffer-name)
  "Build the card structure on the current BUFFER-NAME at current point.
No synchronization is done."
  (->> (orgtrello-entity-card-region)
       (cons buffer-name)
       (apply 'orgtrello-buffer-build-org-entities)))

(defun orgtrello-buffer-build-org-entities (buffer-name
                                            &optional region-start region-end)
  "Compute the current entities hash from the BUFFER-NAME.
Return the list of entities map and adjacency map in this order.
If REGION-START and REGION-END are provided, will work on such defined region."
  (with-current-buffer buffer-name
    (save-excursion
      (save-restriction
        (let ((entities (orgtrello-hash-empty-hash))
              (adjacency (orgtrello-hash-empty-hash)))
          (when (and region-start region-end)
            (narrow-to-region region-start region-end))
          (orgtrello-buffer-org-map-entities-without-params
           (lambda ()
             (org-show-subtree) ;; unfold every entries, otherwise #53
             (let ((current-checksum  (orgtrello-buffer-compute-checksum))
                   (previous-checksum (orgtrello-buffer-get-local-checksum)))
               (unless (string= current-checksum previous-checksum)
                 (let* ((full-meta (orgtrello-buffer-entry-get-full-metadata))
                        (entity    (orgtrello-data-current full-meta)))
                   (unless (-> entity
                               orgtrello-data-entity-id
                               orgtrello-data-id-p)
                     (let ((marker (orgtrello-buffer--compute-marker-from-entry
                                    entity)))
                       (orgtrello-buffer--set-marker marker)
                       (orgtrello-data-put-entity-id marker entity)
                       (orgtrello-data-put-current entity full-meta)))
                   (--> entity
                        (orgtrello-buffer--dispatch-create-entities-map-with-adjacency it)
                        (funcall it full-meta entities adjacency)))))))
          (list entities adjacency))))))

(defun orgtrello-buffer--put-entities (current-meta entities)
  "Deal with adding a the current entry from CURRENT-META in ENTITIES."
  (-> current-meta
      orgtrello-data-current
      (orgtrello-backend-add-entity-to-entities entities)))

(defalias 'orgtrello-buffer--set-marker (-partial
                                         #'orgtrello-buffer-set-property
                                         org-trello--label-key-id)
  "Set a MARKER to get back to later.")

(defun orgtrello-buffer-set-marker-if-not-present (entity marker)
  "Set the ENTITY with MARKER to the entry if we never did."
  ;; if never created before, we need a marker to add inside the file
  (unless (string= (orgtrello-data-entity-id entity) marker)
    (orgtrello-buffer--set-marker marker)))

(defun orgtrello-buffer-org-map-entities-without-params (fn-to-execute)
  "Execute FN-TO-EXECUTE function for all entities from buffer.
FN-TO-EXECUTE is a function without any parameters."
  (org-map-entries
   (lambda ()
     (let ((current-checksum (orgtrello-buffer-card-checksum))
           (previous-checksum (orgtrello-buffer-get-card-local-checksum)))
       (unless (or (orgtrello-entity-org-comment-p) ;; we should not have to do it ourselves...
                   (string= current-checksum previous-checksum))
         (cons (funcall fn-to-execute)
               (orgtrello-cbx-map-checkboxes fn-to-execute)))))
   nil nil 'comment 'archive)) ;; erf... the comment are supposed to be skipped... by org-map-entities and are not so we code it

(defun orgtrello-buffer-get-usernames-assigned-property ()
  "Read the org users property from the current entry."
  (org-entry-get nil org-trello--property-users-entry))

(defun orgtrello-buffer-set-usernames-assigned-property (csv-users)
  "Update users org property from CSV-USERS."
  (orgtrello-buffer-org-entry-put nil
                                  org-trello--property-users-entry
                                  csv-users))

(defun orgtrello-buffer-delete-property-from-entry (property)
  "Delete the PROPERTY."
  (org-entry-delete nil property))

(defun orgtrello-buffer-delete-property (property)
  "If a checkbox PROPERTY is found, delete it from the buffer."
  (save-excursion
    (orgtrello-buffer-delete-property-from-entry property)
    (goto-char (point-min))
    (while (re-search-forward " :PROPERTIES: {.*" nil t)
      (orgtrello-buffer-remove-overlays (point-at-bol) (point-at-eol))
      (replace-match "" nil t))))

(defun orgtrello-buffer-remove-overlays (&optional start end)
  "Remove every org-trello overlays from the current buffer.
When START/END are specified, use those boundaries.
Otherwise, work on the all buffer."
  (remove-overlays (if start start (point-min))
                   (if end end (point-max))
                   'invisible
                   'org-trello-cbx-property))

(defun orgtrello-buffer-install-overlays ()
  "Install overlays throughout all buffer.
Function to be triggered by `before-save-hook` on org-trello-mode buffer."
  (when (orgtrello-setup-org-trello-on-p)
    (orgtrello-buffer-remove-overlays)
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward  "\\(:PROPERTIES: {.*}\\)" nil t)
        (orgtrello-buffer-install-overlay (match-beginning 1))))))

(defun orgtrello-buffer-indent-region (indent region)
  "Given an INDENT and a REGION, check if we need to indent.
If yes, indent such region with INDENT space."
  (let ((start (car region))
        (end   (cadr region)))
    (unless (< end start)
      (save-restriction
        (narrow-to-region start end)
        (goto-char (point-min))
        (unless (<= indent (org-get-indentation));; if need be
          (indent-rigidly start end indent))))));; indent rightfully

(defun orgtrello-buffer-indent-card-descriptions ()
  "Indent the buffer's card descriptions rigidly starting at 2.
Function to be triggered by `before-save-hook` on org-trello-mode buffer."
  (when (orgtrello-setup-org-trello-on-p)
    (orgtrello-buffer-org-map-entries
     (lambda ()
       (-when-let (card-description
                   (-> (orgtrello-buffer-entry-get-full-metadata)
                       orgtrello-data-current
                       orgtrello-data-entity-description))
         (orgtrello-buffer-indent-region
          org-trello-buffer--indent-description
          (orgtrello-entity-card-metadata-region)))))))

(defun orgtrello-buffer-indent-card-data ()
  "Indent the card data rigidly starting at 2.
Function to be triggered by `before-save-hook` on org-trello-mode buffer."
  (when (orgtrello-setup-org-trello-on-p)
    (orgtrello-buffer-org-map-entries
     (lambda ()
       (orgtrello-buffer-indent-region org-trello--checklist-indent
                                       (orgtrello-entity-card-data-region))))))

(defalias 'orgtrello-buffer-org-entity-metadata 'org-heading-components
  "Compute the basic org-mode metadata.")

(defun orgtrello-buffer--extract-metadata ()
  "Extract the current metadata depending on org-trello's checklist policy."
  (funcall (if (orgtrello-entity-org-checkbox-p)
               'orgtrello-cbx-org-checkbox-metadata
             'orgtrello-buffer-org-entity-metadata)))

(defun orgtrello-buffer-extract-identifier (point)
  "Extract the identifier from POINT."
  (orgtrello-buffer-org-entry-get point org-trello--label-key-id))

(defun orgtrello-buffer-set-property (key value)
  "Either set the property normally at KEY with VALUE.
Deal with org entities and checkbox as well."
  (funcall (if (orgtrello-entity-org-checkbox-p)
               'orgtrello-cbx-org-set-property
             'org-set-property) key value))

(defalias 'orgtrello-buffer-card-entry-get 'org-entry-get)

(defun orgtrello-buffer-org-entry-get (point key)
  "Extract the identifier from the POINT at KEY.
Deal with org entities and checkbox as well."
  (funcall (if (orgtrello-entity-org-checkbox-p)
               'orgtrello-cbx-org-get-property
             'orgtrello-buffer-card-entry-get) point key))

(defun orgtrello-buffer--usernames-to-id (usernames-ids usernames)
  "Given USERNAMES-IDS, compute convention name from USERNAMES to a list of ids.
:: Dict String Id -> [String] -> [Id]"
  (-map (-compose (-rpartial #'gethash usernames-ids)
                  (-partial #'format "%s%s" org-trello--label-key-user-prefix))
        usernames))

(defun orgtrello-buffer--user-ids-assigned-to-current-card ()
  "Compute the user ids assigned to the current card.
Retrieve the csv string of usernames, recompute the list of org-trello
properties and map it to a string of ids."
  (->> (orgtrello-buffer-get-usernames-assigned-property)
       orgtrello-data--users-from
       (orgtrello-buffer--usernames-to-id org-trello--hmap-users-name-id)
       orgtrello-data--users-to))

(defun orgtrello-buffer--extract-description-at-point ()
  "Extract description at point depending on the entity's nature."
  (cond ((orgtrello-entity-org-card-p)
         (orgtrello-buffer--extract-card-description-at-point))
        ((orgtrello-entity-org-comment-p)
         (orgtrello-buffer--extract-comment-description-at-point))))

(defun orgtrello-buffer-entity-metadata ()
  "Compute the metadata for a given org entry.
Also add some metadata identifier/due-data/point/buffer-name/etc..."
  (let ((current-point (point)))
    (->> (orgtrello-buffer--extract-metadata)
         (cons (-> current-point
                   (orgtrello-buffer-org-entry-get "DEADLINE")
                   orgtrello-date-convert-org-date-to-trello-date))
         (cons (orgtrello-buffer-extract-identifier current-point))
         (cons current-point)
         (cons (buffer-name))
         (cons (orgtrello-buffer--user-ids-assigned-to-current-card))
         (cons (orgtrello-buffer--extract-description-at-point))
         (cons (orgtrello-buffer-org-unknown-drawer-properties))
         orgtrello-buffer--to-orgtrello-metadata)))

(defun orgtrello-buffer--filter-out-known-properties (l)
  "Filter out the known org-trello properties from L."
  (--filter (not (or (string-match-p "^orgtrello-.*" (car it))
                     (string= "CATEGORY" (car it)))) l))

(defun orgtrello-buffer-org-unknown-drawer-properties ()
  "Retrieve the key/value pairs of org-trello unknown drawer properties."
  (->> (org-entry-properties (point) 'standard)
       orgtrello-buffer--filter-out-known-properties))

(defun orgtrello-buffer-org-up-parent ()
  "A function to get back to the current entry's parent."
  (funcall (if (orgtrello-entity-org-checkbox-p)
               'orgtrello-cbx-org-up
             'org-up-heading-safe)))

(defun orgtrello-buffer--parent-metadata ()
  "Extract the metadata from the current heading's parent."
  (save-excursion
    (orgtrello-buffer-org-up-parent)
    (orgtrello-buffer-entity-metadata)))

(defun orgtrello-buffer--grandparent-metadata ()
  "Extract the metadata from the current heading's grandparent."
  (save-excursion
    (orgtrello-buffer-org-up-parent)
    (orgtrello-buffer-org-up-parent)
    (orgtrello-buffer-entity-metadata)))

(defun orgtrello-buffer-safe-entry-full-metadata ()
  "Compute the full entry's metadata without any underlying error.
Return nil if entry is not correct, full entity metadata structure otherwise."
  (condition-case nil
      (orgtrello-buffer-entry-get-full-metadata)
    ('error nil)))

(defun orgtrello-buffer-entry-get-full-metadata ()
  "Compute metadata needed into a map with keys :current, :parent, :grandparent.
Returns nil if the level is superior to 4."
  (save-excursion
    (let* ((current   (orgtrello-buffer-entity-metadata))
           (level     (orgtrello-data-entity-level current)))
      (when (< level org-trello--out-of-bounds-level)
        (let* ((ancestors (cond ((= level org-trello--card-level)
                                 '(nil nil))
                                ((= level org-trello--checklist-level)
                                 `(,(orgtrello-buffer--parent-metadata) nil))
                                ((= level org-trello--item-level)
                                 `(,(orgtrello-buffer--parent-metadata)
                                   ,(orgtrello-buffer--grandparent-metadata)))))
               (parent      (car ancestors))
               (grandparent (cadr ancestors)))
          (orgtrello-data-put-parent grandparent parent)
          (orgtrello-data-put-parent parent current)
          (orgtrello-data-make-hierarchy current parent grandparent))))))

(defun orgtrello-buffer--to-orgtrello-metadata (heading-metadata)
  "Given the HEADING-METADATA returned by the function 'org-heading-components.
Make it a hashmap with key :level,  :keyword,  :name and their respective value."
  (-let (((unknown-properties description member-ids buffer-name point id due
                              level _ keyword _ name tags) heading-metadata))
    (orgtrello-data-make-hash-org
     member-ids
     level
     (if keyword keyword (car org-trello--org-keyword-trello-list-names))
     name
     id
     due
     point
     buffer-name
     description
     tags unknown-properties)))

(defun orgtrello-buffer-filtered-kwds ()
  "Org keywords used (based on org-todo-keywords-1)."
  (let ((keywords org-todo-keywords-1))
    (nreverse (reverse keywords))))

(defun orgtrello-buffer-org-file-properties ()
  "Compute the org buffer's file properties."
  (let ((org-trello-file-properties org-file-properties))
    org-trello-file-properties))

(defun orgtrello-buffer-org-map-entries (fn-to-execute)
  "Execute for each heading the FN-TO-EXECUTE."
  (org-map-entries fn-to-execute nil nil 'comment))

(defun orgtrello-buffer-end-of-line-point ()
  "Compute the end of line for an org-trello buffer."
  (let* ((pt (save-excursion (org-end-of-line) (point))))
    (if (orgtrello-entity-org-checkbox-p)
        (-if-let (s (orgtrello-buffer-compute-overlay-size))
            (- pt s 1)
          pt)
      pt)))

(defun orgtrello-buffer-end-of-line ()
  "Move the cursor at the end of the line.
For a checkbox, move to the 1- point (because of overlays)."
  (interactive)
  (goto-char (orgtrello-buffer-end-of-line-point)))

(defun orgtrello-buffer-org-decorator (org-fn)
  "If on org-trello checkbox move to the org end of the line.
Trigger the needed indentation for the card's description and data.
In any case, execute ORG-FN."
  (orgtrello-buffer-indent-card-descriptions)
  (orgtrello-buffer-indent-card-data)
  (when (orgtrello-entity-org-checkbox-p)
    (org-end-of-line))
  (funcall org-fn))

(defun orgtrello-buffer-org-return ()
  "Move the cursor at the real end of the line.
Then execute org-return."
  (interactive)
  (orgtrello-buffer-org-decorator 'org-return))

(defun orgtrello-buffer-org-ctrl-c-ret ()
  "Move the cursor at the end of the line.
For a checkbox, move to the 1- point (because of overlays)."
  (interactive)
  (orgtrello-buffer-org-decorator 'org-ctrl-c-ret))

(defun orgtrello-buffer-install-overlay (start-position)
  "Install org-trello overlay from START-POSITION.
First, it removes the current org-trello overlay on actual line.
Then install the new one."
  ;; remove overlay present on current position
  (orgtrello-buffer-remove-overlays (point-at-bol) (point-at-eol))
  ;; build an overlay to hide the cbx properties
  (overlay-put (make-overlay start-position
                             (point-at-eol)
                             (current-buffer)
                             t
                             nil)
               'invisible 'org-trello-cbx-property))

(defun orgtrello-buffer-get-overlay-at-pos ()
  "Retrieve overlay at current position.
Return nil if none."
  (->> (overlays-in (point-at-bol) (point-at-eol))
       (-filter (-compose (-partial 'eq 'org-trello-cbx-property)
                          (-rpartial 'overlay-get 'invisible)))
       car))

(defun orgtrello-buffer-compute-overlay-size ()
  "Compute the overlay size to the current position."
  (-when-let (o (orgtrello-buffer-get-overlay-at-pos))
    (- (overlay-end o) (overlay-start o))))

(defun orgtrello-buffer--compute-marker-from-entry (entry)
  "Compute and set the ENTRY marker (either a sha1 or the id of the entry)."
  (-if-let (current-entry-id (orgtrello-data-entity-id entry))
      current-entry-id
    (orgtrello-buffer-compute-marker (orgtrello-data-entity-buffername entry)
                                     (orgtrello-data-entity-name entry)
                                     (orgtrello-data-entity-position entry))))

(defun orgtrello-buffer-compute-marker (buffer-name name position)
  "Compute the orgtrello marker which is composed of BUFFER-NAME, NAME and POSITION."
  (->> (list org-trello--label-key-marker buffer-name name
             (if (stringp position) position (int-to-string position)))
       (-interpose "-")
       (apply 'concat)
       sha1
       (concat org-trello--label-key-marker "-")))

(defun orgtrello-buffer-save-buffer (buffer-name)
  "Given a BUFFER-NAME, save it."
  (with-current-buffer buffer-name
    (call-interactively 'save-buffer)))

(defun orgtrello-buffer-overwrite-card (card-region entity entities adjacencies)
  "At current position, overwrite the CARD-REGION with new card ENTITY.
ENTITIES and ADJACENCIES provide information on card's structure."
  (let ((region-start (car card-region))
        (region-end   (1- (cadr card-region)))
        (card-id      (orgtrello-data-entity-id entity)))
    (orgtrello-buffer-clean-region region-start region-end)
    (orgtrello-buffer-write-card card-id entity entities adjacencies)))

(defun orgtrello-buffer-checksum (string)
  "Compute the checksum of the STRING."
  (secure-hash 'sha256 string))

(defun orgtrello-buffer--compute-string-for-checksum (region)
  "Given a REGION, compute the string to checksum."
  (lexical-let ((region region)
                (buffer-name (current-buffer)))
    (with-temp-buffer
      (apply 'insert-buffer-substring (cons buffer-name region))
      (let ((org-startup-with-latex-preview nil))
        (org-mode))
      (orgtrello-buffer-delete-property org-trello--label-key-local-checksum)
      (when orgtrello-setup-use-position-in-checksum-computation
        (goto-char (point-max))
        (insert (format "\n%s" (car region))))
      (buffer-substring-no-properties (point-min) (point-max)))))

(defun orgtrello-buffer-compute-generic-checksum (compute-region-fn)
  "Compute the entity's checksum.
COMPUTE-REGION-FN is the region computation function (takes no parameter)."
  (-> compute-region-fn
      funcall
      orgtrello-buffer--compute-string-for-checksum
      orgtrello-buffer-checksum))

(defun orgtrello-buffer-compute-checksum ()
  "Compute the checksum of the current entity at point."
  (funcall (cond ((orgtrello-entity-org-card-p)
                  'orgtrello-buffer-card-checksum)
                 ((orgtrello-entity-checklist-at-pt)
                  'orgtrello-buffer-checklist-checksum)
                 ((orgtrello-entity-item-at-pt)
                  'orgtrello-buffer-item-checksum)
                 ((orgtrello-entity-org-comment-p)
                  'orgtrello-buffer-comment-checksum))))

(defun orgtrello-buffer-card-checksum ()
  "Compute the card's checksum at point."
  (orgtrello-buffer-compute-generic-checksum 'orgtrello-entity-card-region))

(defun orgtrello-buffer-checklist-checksum ()
  "Compute the checkbox's checksum."
  (orgtrello-buffer-compute-generic-checksum
   'orgtrello-entity-compute-checklist-region))

(defun orgtrello-buffer-item-checksum ()
  "Compute the checkbox's checksum."
  (orgtrello-buffer-compute-generic-checksum
   'orgtrello-entity-compute-item-region))

(defun orgtrello-buffer-comment-checksum ()
  "Compute the comment's checksum."
  (orgtrello-buffer-compute-generic-checksum 'orgtrello-entity-comment-region))

(defun orgtrello-buffer-archive-cards (trello-cards)
  "Given a list of TRELLO-CARDS, archive those if they are present on buffer."
  (when trello-cards
    (orgtrello-buffer-org-map-entries
     (lambda ()
       (let ((card-id (-> (orgtrello-buffer-entry-get-full-metadata)
                          orgtrello-data-current
                          orgtrello-data-entity-id)))
         (when (-some? (-compose (-partial 'string= card-id) 'orgtrello-data-entity-id)
                       trello-cards) ;; find a card to archive
           (org-archive-subtree)))))))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-buffer loaded!")

(provide 'org-trello-buffer)
;;; org-trello-buffer.el ends here
