;;; org-trello-api.el --- Interface functions to Trello API

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

(require 'dash)
(require 'org-trello-setup)
(require 'org-trello-log)
(require 'org-trello-hash)
(require 'org-trello-data)

(defun orgtrello-api-make-query (method uri &optional params)
  "Make a query hash map from a METHOD, URI and optional parameter PARAMS."
  (let ((h (orgtrello-hash-empty-hash)))
    (->> (if params (orgtrello-data-put-entity-params params h) h)
      (orgtrello-data-put-entity-method method)
      (orgtrello-data-put-entity-uri uri))))

(defun orgtrello-api--deal-with-optional-value (optional-entry value entries)
  "Add the optional value in entries depending on optional-entry.
If OPTIONAL-ENTRY is non nil, cons the VALUE to ENTRIES and return it.
Otherwise,return ENTRIES."
  (if optional-entry (cons value entries) entries))

(defun orgtrello-api--deal-with-optional-values (optional-entries-values entries)
  "Add the optional entry/value OPTIONAL-ENTRIES-VALUES in ENTRIES.
Return entries updated with value if entry, entries untouched otherwise."
  (--reduce-from (orgtrello-api--deal-with-optional-value (car it) (cdr it) acc)
                 entries
                 optional-entries-values))

(defun orgtrello-api-add-board (name &optional description)
  "Create a board query from NAME and optional DESCRIPTION."
  (orgtrello-api-make-query "POST" "/boards"
                            (orgtrello-api--deal-with-optional-value
                             description
                             `("desc" . ,description)
                             `(("name" . ,name)))))

(defun orgtrello-api-get-boards (&optional filter)
  "Retrieve the current boards of the user.
If FILTER is specified, this will filter on this."
  (orgtrello-api-make-query "GET" "/members/me/boards"
                            (orgtrello-api--deal-with-optional-values
                             `((,filter . ("filter" . ,filter)))
                             `(("lists" . "open")))))

(defun orgtrello-api-get-board (id)
  "Create a retrieve board with board ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/boards/%s" id)
   '(("memberships" . "active")
     ("memberships_member" . "true")
     ("lists" . "open")
     ("fields" . "name,memberships,closed")
     ("labels" . "all")
     ("label_fields" . "name,color"))))

(defun orgtrello-api-do (api-uri id &optional undo-flag)
  "Compute the query to do/undo thing using API-URI and ID.
When UNDO-FLAG is set, trigger the undo computation."
  (orgtrello-api-make-query "PUT" (format api-uri id)
                            `(("value" . ,(if undo-flag "false" "true")))))

(defun orgtrello-api-close-board (board-id)
  "Close a board with id BOARD-ID."
  (orgtrello-api-do "/boards/%s/closed" board-id))

(defun orgtrello-api-open-board (board-id)
  "Open a board with id BOARD-ID."
  (orgtrello-api-do "/boards/%s/closed" board-id 'open))

(defun orgtrello-api-get-members (board-id)
  "Retrieve the memberships from a BOARD-ID."
  (orgtrello-api-make-query "GET" (format "/boards/%s/members" board-id)))

(defun orgtrello-api-get-cards (board-id)
  "Create a cards retrieval from the board with BOARD-ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/boards/%s/cards" board-id)
   '(("actions" .  "commentCard")
     ("fields" .
      "closed,desc,due,idBoard,idChecklists,idList,idMembers,name,pos"))))

(defun orgtrello-api-get-full-cards (board-id)
  "Create a cards retrieval from the board with BOARD-ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/boards/%s/cards" board-id)
   '(("actions" .  "commentCard")
     ("checklists" . "all")
     ;;("checkItemStates" . "true")
     ("filter" . "open")
     ("fields" .
      "closed,desc,due,idBoard,idList,idMembers,labels,name,pos"))))

(defun orgtrello-api-get-archived-cards (board-id)
  "Create a cards retrieval from the board with BOARD-ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/boards/%s/cards" board-id)
   '(("filter" . "closed")
     ("fields" .
      "closed,desc,due,idBoard,idList,idMembers,labels,name,pos"))))

(defun orgtrello-api-get-card (card-id)
  "Create a get-card with CARD-ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/cards/%s" card-id)
   '(("actions" . "commentCard")
     ("action_fields" . "data")
     ("action_memberCreator_fields" . "username")
     ("fields" .
      "closed,dateLastActivity,desc,due,idChecklists,idList,idMembers,labels,name,pos"))))

(defun orgtrello-api-get-full-card (card-id)
  "Create a get-card with details query with CARD-ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/cards/%s" card-id)
   '(("actions" . "commentCard")
     ("action_fields" . "data,date")
     ("checklists" . "all")
     ("action_memberCreator_fields" . "username")
     ("fields" .  "closed,dateLastActivity,desc,due,idList,idMembers,labels,name,pos"))))

(defun orgtrello-api-delete-card (card-id)
  "Create a delete card with id CARD-ID query."
  (orgtrello-api-make-query "DELETE" (format "/cards/%s" card-id)))

(defun orgtrello-api-archive-card (card-id)
  "Archive a card with id CARD-ID."
  (orgtrello-api-do "/cards/%s/closed" card-id))

(defun orgtrello-api-unarchive-card (card-id)
  "Unarchive a card with id CARD-ID."
  (orgtrello-api-do "/cards/%s/closed" card-id 'unarchive))

(defun orgtrello-api-get-lists (board-id)
  "Create a get-lists of the board with BOARD-ID."
  (orgtrello-api-make-query "GET" (format "/boards/%s/lists" board-id)))

(defun orgtrello-api-close-list (list-id)
  "Create a close list with id LIST-ID query."
  (orgtrello-api-do "/lists/%s/closed" list-id))

(defun orgtrello-api-open-list (list-id)
  "Create a close list with id LIST-ID query."
  (orgtrello-api-do "/lists/%s/closed" list-id 'open))

(defun orgtrello-api-add-list (name idBoard &optional pos)
  "Create an add a list with NAME, IDBOARD and optional POS."
  (orgtrello-api-make-query "POST" "/lists/"
                            (orgtrello-api--deal-with-optional-value
                             pos
                             `("pos" . ,pos)
                             `(("name" . ,name) ("idBoard" . ,idBoard)))))

(defun orgtrello-api-add-card (name idList
                                    &optional due id-members desc labels pos)
  "Create an add a card with NAME to the list IDLIST.
Optional fields DUE, ID-MEMBERS, DESC, LABELS, POS query."
  (orgtrello-api-make-query
   "POST"
   "/cards/"
   (orgtrello-api--deal-with-optional-values
    `((,id-members . ("idMembers" . ,id-members))
      (,due . ("due" . ,due))
      (,desc . ("desc" . ,desc))
      (,labels . ("labels" . ,labels))
      (,pos . ("pos" . ,pos)))
    `(("name" . ,name)
      ("idList" . ,idList)))))

(defun orgtrello-api-move-card (card-id idList
                                        &optional name due id-members desc
                                        labels pos)
  "Create an update a card CARD-ID to IDLIST.
Optional NAME, DUE date, ID-MEMBERS, DESC, LABELS, POS query."
  (let ((due (if due due "")))
    (->> (orgtrello-api--deal-with-optional-values
          `((,name . ("name" . ,name))
            (,id-members . ("idMembers" . ,id-members))
            (,due . ("due" . ,due))
            (,desc . ("desc" . ,desc))
            (,labels . ("labels" . ,labels))
            (,pos . ("pos" . ,pos)))
          `(("idList" . ,idList)))
         (orgtrello-api-make-query "PUT" (format "/cards/%s" card-id)))))

(defun orgtrello-api-add-checklist (card-id name pos)
  "Create an add a checklist to a card CARD-ID, checklist with NAME, POS query."
  (orgtrello-api-make-query "POST"
                            (format "/cards/%s/checklists" card-id)
                            `(("name" . ,name)
                              ("pos" . ,pos))))

(defun orgtrello-api-update-checklist (checklist-id name pos)
  "Create an update the checklist CHECKLIST-ID with NAME, POS query."
  (orgtrello-api-make-query "PUT"
                            (format "/checklists/%s" checklist-id)
                            `(("name" . ,name)
                              ("pos" . ,pos))))

(defun orgtrello-api-get-checklist (checklist-id &optional without-items)
  "Create a retrieve a checklist CHECKLIST-ID.
Optional fields WITHOUT-ITEMS flag query."
  (let ((default-params '(("fields" . "name,pos,idCard")
                          ("checkItem_fields" . "name,pos,state"))))
    (orgtrello-api-make-query "GET"
                              (format "/checklists/%s" checklist-id)
                              (if without-items
                                  (cons '("checkItems" . "none")
                                        default-params)
                                default-params))))

(defun orgtrello-api-delete-checklist (checklist-id)
  "Create a delete a checklist CHECKLIST-ID."
  (orgtrello-api-make-query "DELETE" (format "/checklists/%s" checklist-id)))

(defun orgtrello-api-add-items (checklist-id name &optional checked pos)
  "Create an add items to a checklist CHECKLIST-ID with NAME.
Optional fields CHECKED state query and POS."
  (->> (orgtrello-api--deal-with-optional-values
        `((,checked . ("checked" . ,checked))
          (,pos     . ("pos" . ,pos)))
        `(("name" . ,name)))
       (orgtrello-api-make-query
        "POST"
        (format "/checklists/%s/checkItems" checklist-id))))

(defun orgtrello-api-update-item (card-id checklist-id item-id name
                                          &optional state pos)
  "Create an update item from the CARD-ID, CHECKLIST-ID and ITEM-ID with NAME.
Optional fields STATE query, POS."
  (->> (orgtrello-api--deal-with-optional-values `((,state . ("state" . ,state))
                                                   (,pos   . ("pos" . ,pos)))
                                                 `(("name" . ,name)))
       (orgtrello-api-make-query
        "PUT"
        (format "/cards/%s/checklist/%s/checkItem/%s"
                card-id checklist-id item-id))))

(defun orgtrello-api-get-item (checklist-id item-id)
  "Create a get item from the checklist CHECKLIST-ID and item ITEM-ID query."
  (orgtrello-api-make-query
   "GET"
   (format "/checklists/%s/checkItems/%s" checklist-id item-id)
   '(("fields" . "name,pos,state"))))

(defun orgtrello-api-delete-item (checklist-id item-id)
  "Create a delete from the checklist CHECKLIST-ID the item ITEM-ID query."
  (orgtrello-api-make-query
   "DELETE"
   (format "/checklists/%s/checkItems/%s" checklist-id item-id)))

(defun orgtrello-api-get-me ()
  "Retrieve the current user's member informations query."
  (orgtrello-api-make-query "GET" "/members/me"))

(defun orgtrello-api-add-card-comment (card-id comment-text)
  "Create a add a card comment to the card with id CARD-ID with the COMMENT-TEXT."
  (orgtrello-api-make-query "POST"
                            (format "/cards/%s/actions/comments" card-id)
                            `(("text" . ,comment-text))))

(defun orgtrello-api-update-card-comment (card-id comment-id comment-text)
  "Update the card CARD-ID comment COMMENT-ID with COMMENT-TEXT.
https://trello.com/docs/api/card/index.html#put-1-cards-card-id-or-shortlink-actions-idaction-comments"
  (orgtrello-api-make-query
   "PUT"
   (format "/cards/%s/actions/%s/comments" card-id comment-id)
   `(("text" . ,comment-text ))))

(defun orgtrello-api-delete-card-comment (card-id comment-id)
  "Delete the card (CARD-ID)'s comment with id COMMENT-ID.
https://trello.com/docs/api/card/index.html#delete-1-cards-card-id-or-shortlink-actions-idaction-comments"
  (orgtrello-api-make-query
   "DELETE" (format "/cards/%s/actions/%s/comments" card-id comment-id)))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-api loaded!")

(provide 'org-trello-api)
;;; org-trello-api.el ends here
