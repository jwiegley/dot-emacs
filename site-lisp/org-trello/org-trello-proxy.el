;;; org-trello-proxy.el --- `Proxy' namespace

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

;; This namespace is badly named.
;; Historically, there was a proxy in charge of reading actions
;; parsing them back and discuss with trello.

;; Now, the controller namespace directly triggers actions from here
;; and still in charge with discussion of trello.

;;; Commentary:
;;; Code:

(require 'org-trello-log)
(require 'org-trello-setup)
(require 'org-trello-query)
(require 'org-trello-api)
(require 'org-trello-data)
(require 'org-trello-hash)
(require 'org-trello-entity)
(require 'org-trello-cbx)
(require 'org-trello-buffer)
(require 'org-trello-action)

(defun orgtrello-proxy--getting-back-to-headline (data)
  "Another approach for getting back to header computing normal form of DATA."
  (orgtrello-proxy--getting-back-to-marker
   (orgtrello-buffer-compute-entity-to-org-entry data)))

(defalias 'orgtrello-proxy--compute-pattern-search-from-marker 'identity
  "Given a MARKER, compute the pattern to look for in the file.
At the moment, `identify' function is sufficient.")

(defun orgtrello-proxy--getting-back-to-marker (marker)
  "Given a MARKER, getting back to marker function.
Move the cursor position."
  (goto-char (point-min))
  (re-search-forward
   (orgtrello-proxy--compute-pattern-search-from-marker marker)
   nil
   t))

(defun orgtrello-proxy--get-back-to-marker (marker data)
  "Getting back to MARKER if possible, otherwise return to the DATA headline.
Move the cursor position."
  (-if-let (goto-ok (orgtrello-proxy--getting-back-to-marker marker))
      goto-ok
    (orgtrello-proxy--getting-back-to-headline data)))

(defun orgtrello-proxy--compute-sync-next-level (entity entities-adjacencies)
  "Trigger the sync for ENTITY's children.
ENTITIES-ADJACENCIES provides needed information."
  (mapcar (lambda (child-id)
            (--> child-id
                 (orgtrello-data-get-entity it entities-adjacencies)
                 (orgtrello-proxy-sync-entity it entities-adjacencies)
                 (eval it)))
          (orgtrello-data-get-children entity entities-adjacencies)))

(defun orgtrello-proxy--update-entities-adjacencies (old-entity
                                                     entity-synced
                                                     entities-adjacencies)
  "Given OLD-ENTITY and ENTITY-SYNCED, update in place ENTITIES-ADJACENCIES.
This will also update ENTITY-SYNCED with its parent.
This will remove OLD-ENTITY's id and update with the ENTITY-SYNCED's one.
This will update the references in arborescence (children with ENTITY-SYNCED).
Returns a list (updated-entity-synced, updated-entities, updated-adjacencies)."
  (-let* (((entities adjacencies) entities-adjacencies)
          (old-entity-id (orgtrello-data-entity-id-or-marker old-entity))
          (entry-new-id  (orgtrello-data-entity-id-or-marker entity-synced))
          (children-ids  (gethash old-entity-id adjacencies)))
    (orgtrello-data-put-parent (orgtrello-data-parent old-entity) entity-synced)
    (mapc (lambda (child-id) ;; update parent reference in children in entities
            (let ((child (gethash child-id entities)))
              (--> child
                   (orgtrello-data-put-parent entity-synced it)
                   (puthash child-id it entities))))
          children-ids)
    ;; update in-place with new entries...
    (puthash entry-new-id entity-synced entities)
    (puthash entry-new-id children-ids adjacencies)
    ;; return updated values
    (list entity-synced entities adjacencies)))

(defun orgtrello-proxy--standard-post-or-put-success-callback (entity-to-sync
                                                               entities-adjacencies)
  "Return a callback fn able to deal with the update of ENTITY-TO-SYNC.
This will update the buffer at the entity synced's position on buffer.
ENTITIES-ADJACENCIES provides (entities adjacencies) list.
ENTITIES is the map of all objects.
ADJACENCIES is the map of children's list per entity.
All maps are indexed by trello or marker id."
  (lexical-let ((buffer-name  (orgtrello-data-entity-buffername entity-to-sync))
                (marker-id    (orgtrello-data-entity-id-or-marker entity-to-sync))
                (entity-name  (orgtrello-data-entity-name entity-to-sync))
                (entities-adj entities-adjacencies)
                (entity-not-yet-synced entity-to-sync))

    (lambda (response)
      (let* ((entity-synced (request-response-data response))
             (entry-new-id  (orgtrello-data-entity-id entity-synced)))
        (with-current-buffer buffer-name
          (save-excursion
            (-when-let (str-msg (when (orgtrello-proxy--get-back-to-marker
                                       marker-id
                                       entity-synced)
                                  (-if-let (entry-id (when (orgtrello-data-id-p
                                                            marker-id)
                                                       marker-id))
                                      (progn ;; id already present, do nothing,
                                        (orgtrello-buffer-write-local-checksum-at-pt)
                                        (format "Entity '%s' with id '%s' synced!"
                                                entity-name
                                                entry-id))
                                    (progn ;; not present, update with trello id
                                      (orgtrello-buffer-write-properties-at-pt
                                       entry-new-id)
                                      (format "Newly entity '%s' with id '%s' synced!"
                                              entity-name
                                              entry-new-id)))))
              (let* ((updates (orgtrello-proxy--update-entities-adjacencies
                               entity-not-yet-synced
                               entity-synced entities-adj))
                     (updated-entity-synced (car updates))
                     (updated-entities-adj  (cdr updates)))
                (orgtrello-proxy--compute-sync-next-level updated-entity-synced
                                                          updated-entities-adj))
              (orgtrello-log-msg orgtrello-log-info str-msg))))))))

(defun orgtrello-proxy--cleanup-meta (entity)
  "Clean the ENTITY metadata up."
  (unless (orgtrello-data-entity-id entity)
    (orgtrello-cbx-org-delete-property org-trello--label-key-id)))

(defun orgtrello-proxy--retrieve-state-of-card (card-meta)
  "Given a CARD-META, retrieve its state depending on its :keyword metadata.
If empty, default to org-trello--todo, otherwise, return its current state."
  (-if-let (card-kwd (orgtrello-data-entity-keyword card-meta org-trello--todo))
      card-kwd
    org-trello--todo))

(defun orgtrello-proxy--checks-before-sync-card (card-meta)
  "Given the CARD-META, check is done before synchronizing the cards."
  (if (orgtrello-data-entity-name card-meta)
      :ok
    org-trello--error-sync-card-missing-name))

(defun orgtrello-proxy--tags-to-labels (tags)
  "Transform org TAGS string to csv labels."
  (if tags
      (let* ((s (s-split ":" tags))
             (ns (if (string= "" (car s)) (cdr s) s)))
        (s-join "," ns))
    ""))

(defun orgtrello-proxy--card (card-meta)
  "Deal with create/update CARD-META query build.
If the checks are ko, the error message is returned."
  (let ((checks-ok-or-error-message (orgtrello-proxy--checks-before-sync-card
                                     card-meta)))
    ;; name is mandatory
    (if (equal :ok checks-ok-or-error-message)
        ;; parent and grandparent are useless here
        (let* ((card-kwd (orgtrello-proxy--retrieve-state-of-card card-meta))
               (list-id (orgtrello-buffer-org-file-get-property card-kwd))
               (card-id (orgtrello-data-entity-id card-meta))
               (card-name (orgtrello-data-entity-name card-meta))
               (card-due (orgtrello-data-entity-due card-meta))
               (card-desc (orgtrello-data-entity-description card-meta))
               (card-user-ids-assigned (orgtrello-data-entity-member-ids
                                        card-meta))
               (card-labels (orgtrello-proxy--tags-to-labels
                             (orgtrello-data-entity-tags card-meta)))
               (card-pos (orgtrello-data-entity-position card-meta)))
          (if card-id
              ;; update
              (orgtrello-api-move-card
               card-id
               list-id
               card-name
               card-due
               card-user-ids-assigned
               card-desc
               card-labels
               card-pos)
            ;; create
            (orgtrello-api-add-card
             card-name
             list-id
             card-due
             card-user-ids-assigned
             card-desc
             card-labels
             card-pos)))
      checks-ok-or-error-message)))

(defun orgtrello-proxy--checks-before-sync-checklist (checklist-meta card-meta)
  "Check all is good before synchronizing the CHECKLIST-META.
CARD-META for necessary data."
  (-if-let (checklist-name (orgtrello-data-entity-name checklist-meta))
      (-if-let (card-id (orgtrello-data-entity-id card-meta))
          :ok
        org-trello--error-sync-checklist-sync-card-first)
    org-trello--error-sync-checklist-missing-name))

(defun orgtrello-proxy--checklist (checklist-meta)
  "Deal with create/update CHECKLIST-META query build.
If the checks are ko, the error message is returned."
  (let* ((card-meta (orgtrello-data-parent checklist-meta))
         (checks-ok-or-error-message
          (orgtrello-proxy--checks-before-sync-checklist checklist-meta
                                                         card-meta)))
    (if (equal :ok checks-ok-or-error-message)
        (let ((checklist-name (orgtrello-data-entity-name checklist-meta))
              (checklist-pos  (orgtrello-data-entity-position checklist-meta)))
          (-if-let (checklist-id (orgtrello-data-entity-id checklist-meta))
              ;; update
              (orgtrello-api-update-checklist checklist-id
                                              checklist-name
                                              checklist-pos)
            ;; create
            (orgtrello-api-add-checklist (orgtrello-data-entity-id card-meta)
                                         checklist-name
                                         checklist-pos)))
      checks-ok-or-error-message)))

(defun orgtrello-proxy--compute-state (state)
  "Given a STATE (TODO/DONE) compute the trello state equivalent."
  (orgtrello-data--compute-state-generic state '("complete" "incomplete")))

(defun orgtrello-proxy--compute-check (state)
  "Given a STATE (TODO/DONE) compute the trello check equivalent."
  (orgtrello-data--compute-state-generic state '(t nil)))

(defun orgtrello-proxy--checks-before-sync-item (item-meta
                                                 checklist-meta
                                                 card-meta)
  "Check ITEM-META synchronization is possible.
CHECKLIST-META and CARD-META are needed to check this."
  (if (orgtrello-data-entity-name item-meta)
      (if (orgtrello-data-entity-id checklist-meta)
          (if (orgtrello-data-entity-id card-meta)
              :ok
            org-trello--error-sync-item-sync-card-first)
        org-trello--error-sync-item-sync-checklist-first)
    org-trello--error-sync-item-missing-name))

(defun orgtrello-proxy--item (item-meta)
  "Deal with create/update ITEM-META query build.
If the checks are ko, the error message is returned."
  (let* ((checklist-meta (orgtrello-data-parent item-meta))
         (card-meta (orgtrello-data-parent checklist-meta))
         (checks-ok-or-error-message (orgtrello-proxy--checks-before-sync-item
                                      item-meta
                                      checklist-meta
                                      card-meta)))
    ;; name is mandatory
    (if (equal :ok checks-ok-or-error-message)
        (let* ((item-id         (orgtrello-data-entity-id item-meta))
               (checklist-id    (orgtrello-data-entity-id checklist-meta))
               (card-id         (orgtrello-data-entity-id card-meta))
               (item-name       (orgtrello-data-entity-name item-meta))
               (item-state      (orgtrello-data-entity-keyword item-meta))
               (item-pos        (orgtrello-data-entity-position item-meta)))
          ;; update/create items
          (if item-id
              ;; update - rename, check or uncheck the item
              (orgtrello-api-update-item card-id
                                         checklist-id
                                         item-id
                                         item-name
                                         (orgtrello-proxy--compute-state item-state)
                                         item-pos)
            ;; create
            (orgtrello-api-add-items checklist-id
                                     item-name
                                     (orgtrello-proxy--compute-check item-state)
                                     item-pos)))
      checks-ok-or-error-message)))

(defun orgtrello-proxy--compute-dispatch-fn (entity map-dispatch-fn)
  "Generic function to dispatch, depending on the ENTITY level, functions.
MAP-DISPATCH-FN is a map of function taking the one parameter ENTITY."
  (-> entity
      orgtrello-data-entity-level
      (gethash map-dispatch-fn 'orgtrello-action--too-deep-level)
      (funcall entity)))

(defvar orgtrello-proxy--map-fn-dispatch-create-update
  (orgtrello-hash-make-properties
   `((,org-trello--card-level      . orgtrello-proxy--card)
     (,org-trello--checklist-level . orgtrello-proxy--checklist)
     (,org-trello--item-level      . orgtrello-proxy--item)))
  "Dispatch map for the creation/update of card/checklist/item.")

(defun orgtrello-proxy--compute-sync-query-request (entity)
  "Dispatch the ENTITY creation/update depending on the nature of the entry."
  (orgtrello-proxy--compute-dispatch-fn
   entity
   orgtrello-proxy--map-fn-dispatch-create-update))

(defun orgtrello-proxy--delete-region (start end)
  "Delete a region defined by START and END bound."
  (orgtrello-buffer-remove-overlays start end) ;; remove overlays on the card region
  (delete-region start end))

(defun orgtrello-proxy--delete-card-region ()
  "Delete the card region (including overlays and line)."
  (orgtrello-entity-back-to-card)
  (let ((starting-point (point))
        (ending-point (save-excursion (if (org-goto-sibling)
                                          (point)
                                        (point-max))))) ;; next card or max
    (orgtrello-proxy--delete-region starting-point ending-point)))

(defun orgtrello-proxy--delete-checkbox-checklist-region ()
  "Delete the checklist region."
  (let ((starting-point (point-at-bol))
        (ending-point
         (save-excursion
           (-if-let (result (orgtrello-entity-goto-next-checkbox-with-same-level
                             org-trello--checklist-level))
               result
             (orgtrello-entity-card-end-point))))) ;; next checkbox/card/max
    (orgtrello-proxy--delete-region starting-point ending-point)))

(defun orgtrello-proxy--delete-checkbox-item-region ()
  "Delete the item region."
  (let ((starting-point (point-at-bol))
        (ending-point (1+ (point-at-eol))))
    (orgtrello-proxy--delete-region starting-point ending-point)))

(defun orgtrello-proxy--delete-entity-region (entity)
  "Compute the delete region function depending on the ENTITY's nature."
  (cond ((orgtrello-data-entity-card-p entity)
         'orgtrello-proxy--delete-card-region)
        ((orgtrello-data-entity-checklist-p entity)
         'orgtrello-proxy--delete-checkbox-checklist-region)
        ((orgtrello-data-entity-item-p entity)
         'orgtrello-proxy--delete-checkbox-item-region)))

(defun orgtrello-proxy--standard-delete-success-callback (entity-to-del)
  "Return a callback function able to deal with the ENTITY-TO-DEL deletion."
  (lexical-let ((entry-buffer-name (orgtrello-data-entity-buffername entity-to-del))
                (marker            (orgtrello-data-entity-id entity-to-del))
                (level             (orgtrello-data-entity-level entity-to-del)))
    (lambda (response)
      (with-current-buffer entry-buffer-name
        (save-excursion
          (when (orgtrello-proxy--getting-back-to-marker marker)
            (-> (orgtrello-buffer-entry-get-full-metadata)
                orgtrello-data-current
                orgtrello-proxy--delete-entity-region
                funcall)
            (when (< org-trello--card-level level) ;; when on checklist or item
              (forward-line -1) ;; get back one line then update card's checksum
              (orgtrello-buffer-write-local-card-checksum-at-point))))))))

(defun orgtrello-proxy--card-delete (card-meta)
  "Deal with the deletion query of a CARD-META."
  (orgtrello-api-delete-card (orgtrello-data-entity-id card-meta)))

(defun orgtrello-proxy--checklist-delete (checklist-meta)
  "Deal with the deletion query of a CHECKLIST-META."
  (orgtrello-api-delete-checklist (orgtrello-data-entity-id checklist-meta)))

(defun orgtrello-proxy--item-delete (item-meta)
  "Deal with create/update query of an ITEM-META."
  (let ((checklist (orgtrello-data-parent item-meta)))
    (orgtrello-api-delete-item (orgtrello-data-entity-id checklist)
                               (orgtrello-data-entity-id item-meta))))

(defvar orgtrello-proxy--map-fn-dispatch-delete
  (orgtrello-hash-make-properties
   `((,org-trello--card-level      . orgtrello-proxy--card-delete)
     (,org-trello--checklist-level . orgtrello-proxy--checklist-delete)
     (,org-trello--item-level      . orgtrello-proxy--item-delete)))
  "Dispatch map for the deletion query of card/checklist/item.")

(defun orgtrello-proxy--compute-delete-query-request (entity)
  "Dispatch the call to the delete function depending on ENTITY level info."
  (orgtrello-proxy--compute-dispatch-fn entity orgtrello-proxy--map-fn-dispatch-delete))

(defun orgtrello-proxy--execute-async-computations (computations log-ok log-ko)
  "Compute the deferred COMPUTATIONS.
Display LOG-OK or LOG-KO depending on the result."
  `(deferred:$
     (deferred:parallel
       ,@computations)
     (deferred:error it
       (lambda () (orgtrello-log-msg orgtrello-log-error ,log-ko)))
     (deferred:nextc it
       (lambda () (orgtrello-log-msg orgtrello-log-debug ,log-ok)))))

(defun orgtrello-proxy-execute-async-computations (computations log-ok log-ko)
  "Compute the deferred COMPUTATIONS.
Display LOG-OK or LOG-KO depending on the result."
  (eval (orgtrello-proxy--execute-async-computations computations log-ok log-ko)))

(defun orgtrello-proxy-delete-entity (entity)
  "Compute the delete action to remove ENTITY."
  (lexical-let ((query-map (orgtrello-proxy--compute-delete-query-request entity))
                (entity-to-delete entity))
    (if (hash-table-p query-map)
        (orgtrello-query-http-trello
         query-map
         nil ; async
         (orgtrello-proxy--standard-delete-success-callback entity)
         (lambda (response)
           (orgtrello-log-msg
            orgtrello-log-error
            "client - Problem during the deletion request to the proxy - error-thrown: %s"
            (request-response-error-thrown response))
           (orgtrello-proxy--cleanup-meta entity-to-delete)))
      (orgtrello-log-msg orgtrello-log-error query-map))))

(defun orgtrello-proxy-sync-entity (entity entities-adjacencies)
  "Compute the sync action on entity ENTITY.
Use ENTITIES-ADJACENCIES to provide further information."
  (lexical-let ((query-map (orgtrello-proxy--compute-sync-query-request entity))
                (entity-to-sync entity))
    (if (hash-table-p query-map)
        (orgtrello-query-http-trello
         query-map
         nil ; async
         (orgtrello-proxy--standard-post-or-put-success-callback entity entities-adjacencies)
         (lambda (response)
           (orgtrello-proxy--cleanup-meta entity-to-sync)
           (orgtrello-log-msg
            orgtrello-log-error
            "client - Problem during the sync request to the proxy - error-thrown: %s"
            (request-response-error-thrown response))))
      (progn ;; cannot execute the request
        (orgtrello-proxy--cleanup-meta entity-to-sync)
        (orgtrello-log-msg orgtrello-log-error query-map)
        query-map))))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-proxy loaded!")

(provide 'org-trello-proxy)
;;; org-trello-proxy.el ends here
