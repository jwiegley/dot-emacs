;;; org-trello-controller.el --- Controller of org-trello mode

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
(require 'org-trello-buffer)
(require 'org-trello-data)
(require 'org-trello-hash)
(require 'org-trello-api)
(require 'org-trello-entity)
(require 'org-trello-cbx)
(require 'org-trello-action)
(require 'org-trello-backend)
(require 'org-trello-buffer)
(require 'org-trello-input)
(require 'org-trello-proxy)
(require 'org-trello-deferred)
(require 'dash-functional)
(require 's)

(defun orgtrello-controller-log-success (prefix-log)
  "Return a function to log the success with PREFIX-LOG as prefix string."
  (-partial #'orgtrello-log-msg orgtrello-log-info (format "%s DONE."
                                                           prefix-log)))

(defun orgtrello-controller-log-error (prefix-log error-msg)
  "Return a function to log the error with PREFIX-LOG and ERROR-MSG."
  (-partial #'orgtrello-log-msg orgtrello-log-error (format "%s FAILED. %s"
                                                            prefix-log
                                                            error-msg)))

(defun orgtrello-controller--list-user-entries (props)
  "List the users entries from properties PROPS."
  (-filter (-compose
            (-partial 'string-match-p org-trello--label-key-user-prefix)
            'car) props))

(defun orgtrello-controller--hmap-id-name (org-keywords props)
  "Given an ORG-KEYWORDS and a properties PROPS, return a map.
This map is a key/value of (trello-id, trello-list-name-and-org-keyword-name).
If either org-keywords or properties is nil, return an empty hash-map."
  (if (or (null org-keywords) (null props))
      (orgtrello-hash-empty-hash)
    (--reduce-from (orgtrello-hash-puthash-data
                    (orgtrello-buffer-org-get-property it props) it acc)
                   (orgtrello-hash-empty-hash)
                   org-keywords)))

(defun orgtrello-controller-setup-properties (&optional args)
  "Setup `org-trello' properties according to `org-mode' setup in buffer.
Return :ok.
ARGS is not used."
  (orgtrello-action-reload-setup)
  (let* ((org-keywords (orgtrello-buffer-filtered-kwds))
         (org-file-properties (orgtrello-buffer-org-file-properties))
         (org-trello-users (orgtrello-controller--list-user-entries
                            org-file-properties)))

    (setq
     org-trello--org-keyword-trello-list-names org-keywords
     org-trello--hmap-list-orgkeyword-id-name (orgtrello-controller--hmap-id-name
                                               org-keywords
                                               org-file-properties)
     org-trello--hmap-users-id-name (orgtrello-hash-make-transpose-properties
                                     org-trello-users)
     org-trello--hmap-users-name-id (orgtrello-hash-make-properties
                                     org-trello-users)
     org-trello--user-logged-in (or (orgtrello-buffer-me)
                                    (orgtrello-setup-user-logged-in)))

    (mapc (-partial #'add-to-list 'org-tag-alist)
          '(("red" . ?r)
            ("green" . ?g)
            ("yellow" . ?y)
            ("blue" . ?b)
            ("purple" . ?p)
            ("orange" . ?o)))
    :ok))

(defun orgtrello-controller-control-properties (&optional args)
  "Org-trello needs some header buffer properties set (board id, list ids, ...).
Return :ok if ok, or the error message if problems.
ARGS is not used."
  (let ((hmap-count
         (hash-table-count org-trello--hmap-list-orgkeyword-id-name)))
    (if (and (orgtrello-buffer-org-file-properties)
             (orgtrello-buffer-board-id)
             (= (length org-trello--org-keyword-trello-list-names) hmap-count))
        :ok
      "Setup problem.\nEither you did not connect your org-mode buffer with a trello board, to correct this:\n  * attach to a board through C-c o I or M-x org-trello-install-board-metadata\n  * or create a board from scratch with C-c o b or M-x org-trello-create-board-and-install-metadata).\nEither your org-mode's todo keyword list and your trello board lists are not named the same way (which they must).\nFor this, connect to trello and rename your board's list according to your org-mode's todo list.\nAlso, you can specify on your org-mode buffer the todo list you want to work with, for example: #+TODO: TODO DOING | DONE FAIL (hit C-c C-c to refresh the setup)")))

(defun orgtrello-controller-migrate-user-setup (&optional args)
  "Migrate user's setup file.
From:
- ~/.trello/config.el to ~/.emacs.d/.trello/<trello-login>.el.
- Also the names of the constants have changed to *consumer-key* to
  org-trello-consumer-key and from *access-key* to org-trello-access-key.
ARGS is not used."
  (when (file-exists-p org-trello--old-config-dir) ;; old setup, migrate
    (-let (((consumer-key access-key)
            (if *consumer-key*
                `(,*consumer-key* ,*access-token*)
              `(,org-trello-consumer-key ,org-trello-access-token)))
           (user-login (orgtrello-buffer-me)))
      ;; load old setup
      (load org-trello--old-config-file)
      ;; persist setup
      (orgtrello-controller--do-install-config-file
       user-login
       consumer-key
       access-key)
      ;; delete old setup file
      (delete-directory org-trello--old-config-dir 'with-contents)))
  :ok)

(defun orgtrello-controller-config-file (&optional username)
  "Determine the configuration file as per user logged in.
If USERNAME is supplied, do not look into the current buffer."
  (format org-trello--config-file
          (if username username (orgtrello-setup-user-logged-in))))

(defun orgtrello-controller-user-config-files ()
  "List the actual possible users."
  (when (file-exists-p org-trello--config-dir)
    (directory-files org-trello--config-dir 'full-name "^.*\.el")))

(defalias 'orgtrello-controller-user-account-from-config-file 'file-name-base)

(defun orgtrello-controller-list-user-accounts (user-config-files)
  "Given a list of USER-CONFIG-FILES, return the trello accounts list."
  (mapcar #'orgtrello-controller-user-account-from-config-file user-config-files))

(defun orgtrello-controller--choose-account (accounts)
  "Let the user decide which ACCOUNTS (s)he wants to use.
Return such account name."
  (orgtrello-input-read-string-completion
   "Select org-trello account (TAB to complete): "
   accounts))

(defun orgtrello-controller-set-account (&optional args)
  "Set the org-trello account.
ARGS is not used."
  (let ((user-account-elected
         (-if-let (user-account (orgtrello-buffer-me))
             user-account ;; if already set, keep using the actual account
           ;; otherwise, user not logged in, determine which account to use
           (let ((user-accounts (orgtrello-controller-list-user-accounts
                                 (orgtrello-controller-user-config-files))))
             (if (= 1 (length user-accounts))
                 (car user-accounts)
               (orgtrello-controller--choose-account user-accounts))))))
    (orgtrello-setup-set-user-logged-in user-account-elected)
    :ok))

(defun orgtrello-controller-load-keys (&optional args)
  "Load the credentials keys from the configuration file.
ARGS is not used."
  (let ((user-config-file (orgtrello-controller-config-file)))
    (if (and (file-exists-p user-config-file) (load user-config-file))
        :ok
      "Setup problem - Problem during credentials loading (consumer-key and read/write access-token) - C-c o i or M-x org-trello-install-key-and-token")))

(defun orgtrello-controller-control-keys (&optional args)
  "Check `org-trello-consumer-key' and `org-trello-access-token' are set.
Returns :ok if everything is ok, or the error message if problems.
ARGS is not used."
  (if (and org-trello-consumer-key org-trello-access-token)
      :ok
    "Setup problem - You need to install the consumer-key and the read/write access-token - C-c o i or M-x org-trello-install-key-and-token"))

(defun orgtrello-controller--on-entity-p (entity)
  "Compute if the org-trello ENTITY exists.
If it does not not, error."
  (if entity
      :ok
    "You need to be on an org-trello entity (card/checklist/item) for this action to occur!"))

(defun orgtrello-controller--right-level-p (entity)
  "Compute if the ENTITY level is correct (not higher than level 4)."
  (if (and entity (< (-> entity
                         orgtrello-data-current
                         orgtrello-data-entity-level)
                     org-trello--out-of-bounds-level))
      :ok
    "Wrong level. Do not deal with entity other than card/checklist/item!"))

(defun orgtrello-controller--already-synced-p (entity)
  "Compute if the ENTITY has already been synchronized."
  (if (-> entity orgtrello-data-current orgtrello-data-entity-id)
      :ok
    "Entity must be synchronized with trello first!"))

(defun orgtrello-controller--entity-mandatory-name-ok-p (simple-entity)
  "Ensure SIMPLE-ENTITY can be synced regarding the mandatory data."
  (if simple-entity
      (let* ((level   (orgtrello-data-entity-level simple-entity))
             (name    (orgtrello-data-entity-name simple-entity)))
        (if (and name (< 0 (length name)))
            :ok
          (cond ((= level org-trello--card-level)
                 org-trello--error-sync-card-missing-name)
                ((= level org-trello--checklist-level)
                 org-trello--error-sync-checklist-missing-name)
                ((= level org-trello--item-level)
                 org-trello--error-sync-item-missing-name))))
    :ok))

(defun orgtrello-controller--mandatory-name-ok-p (entity)
  "Ensure ENTITY can be synced regarding the mandatory data."
  (-> entity
      orgtrello-data-current
      orgtrello-controller--entity-mandatory-name-ok-p))

(defun orgtrello-controller-checks-then-delete-simple ()
  "Do the deletion of an entity."
  (orgtrello-action-functional-controls-then-do
   '(orgtrello-controller--on-entity-p
     orgtrello-controller--right-level-p
     orgtrello-controller--already-synced-p)
   (orgtrello-buffer-safe-entry-full-metadata)
   'orgtrello-controller-delete-card
   (current-buffer)))

(defun orgtrello-controller-delete-card (full-meta &optional buffer-name)
  "Execute on FULL-META the ACTION.
BUFFER-NAME to specify the buffer with which we currently work."
  (with-current-buffer buffer-name
    (let* ((current (orgtrello-data-current full-meta))
           (marker  (orgtrello-buffer--compute-marker-from-entry current)))
      (orgtrello-buffer-set-marker-if-not-present current marker)
      (orgtrello-data-put-entity-id marker current)
      (eval (orgtrello-proxy-delete-entity current)))))

(defun orgtrello-controller-checks-then-sync-card-to-trello ()
  "Check then do the actual sync if everything is ok."
  (orgtrello-action-functional-controls-then-do
   '(orgtrello-controller--on-entity-p
     orgtrello-controller--right-level-p
     orgtrello-controller--mandatory-name-ok-p)
   (orgtrello-buffer-safe-entry-full-metadata)
   'orgtrello-controller-sync-card-to-trello
   (current-buffer)))

(defun orgtrello-controller-sync-card-to-trello (full-meta &optional buffer-name)
  "Do the actual card creation/update - from card to item.
FULL-META is actually dismissed and recomputed here.
BUFFER-NAME is the buffer on to which act."
  (let ((current-checksum (orgtrello-buffer-card-checksum))
        (previous-checksum (orgtrello-buffer-get-card-local-checksum)))
    (if (string= current-checksum previous-checksum)
        (orgtrello-log-msg orgtrello-log-info
                           "Card already synchronized, nothing to do!")
      (orgtrello-log-msg orgtrello-log-info
                         "Synchronizing card on board '%s'..."
                         (orgtrello-buffer-board-name))
      (org-show-subtree) ;; show subtree, otherwise org-trello/org-trello/#53
      (-> buffer-name
          orgtrello-buffer-build-org-card-structure
          orgtrello-controller-execute-sync-entity-structure))))

(defun orgtrello-controller-do-sync-buffer-to-trello ()
  "Full `org-mode' file synchronization."
  (orgtrello-log-msg orgtrello-log-warn
                     "Synchronizing org-mode file to board '%s'. This may take some time, some coffee may be a good idea..."
                     (orgtrello-buffer-board-name))
  (-> (current-buffer)
      orgtrello-buffer-build-org-entities
      orgtrello-controller-execute-sync-entity-structure))

(defun orgtrello-controller--sync-buffer-with-trello-data (data)
  "Update the current buffer with DATA (entities and adjacency)."
  (-let (((entities adjacencies) data))
    (goto-char (point-max)) ;; go at the end of the file
    (maphash
     (lambda (new-id entity)
       (when (orgtrello-data-entity-card-p entity)
         (orgtrello-buffer-write-card new-id entity entities adjacencies)))
     entities)
    (goto-char (point-min))                 ;; go back to the beginning of file
    (ignore-errors (org-sort-entries t ?o)) ;; sort entries on keywords & ignore errors (e.g. nothing to sort)
    (org-global-cycle '(4))))               ;; fold all entries

(defun orgtrello-controller--cleanup-org-entries ()
  "Cleanup org-entries from the buffer.
Does not preserve position."
  (goto-char (point-min))
  (outline-next-heading)
  (orgtrello-buffer-remove-overlays (point-at-bol) (point-max))
  (kill-region (point-at-bol) (point-max)))

(defun orgtrello-controller-sync-buffer-with-trello-cards (buffer-name
                                                           org-trello-cards)
  "Synchronize the buffer BUFFER-NAME with the ORG-TRELLO-CARDS."
  (with-local-quit
    (with-current-buffer buffer-name
      (save-excursion
        (let ((entities-from-org-buffer
               (orgtrello-buffer-build-org-entities buffer-name)))
          (-> org-trello-cards
              orgtrello-backend-compute-org-trello-card-from
              (orgtrello-data-merge-entities-trello-and-org
               entities-from-org-buffer)
              ((lambda (entry) (orgtrello-controller--cleanup-org-entries) entry))   ;; hack to clean the org entries just before synchronizing the buffer
              orgtrello-controller--sync-buffer-with-trello-data))))))

(defun orgtrello-controller--retrieve-archive-cards (data)
  "Retrieve the archive cards from DATA.
DATA is a list of (board-id &rest buffer-name point-start)."
  (-> data
      car
      orgtrello-api-get-archived-cards
      (orgtrello-query-http-trello 'sync)
      (cons data)))

(defun orgtrello-controller--retrieve-full-cards (data)
  "Retrieve the full cards from DATA.
DATA is a list of (archive-cards board-id &rest buffer-name point-start).
Return the initial list + the full cards."
  (-let* (((archive-cards board-id &rest) data)
          (cards (-> board-id
                     orgtrello-api-get-full-cards
                     (orgtrello-query-http-trello 'sync))))
    (cons cards data)))

(defun orgtrello-controller--sync-buffer-with-archived-and-trello-cards (data)
  "Update buffer at point with DATA.
DATA is a list of (cards archive-cards board-id buffername) in this order."
  (-let (((trello-cards trello-archived-cards _ buffer-name &rest) data))
    ;; first archive the cards that needs to be
    (orgtrello-log-msg orgtrello-log-debug
                       "Archived trello-cards: %S"
                       trello-archived-cards)
    (orgtrello-buffer-archive-cards trello-archived-cards)
    ;; Then update the buffer with the other opened trello cards
    (orgtrello-log-msg orgtrello-log-debug
                       "Opened trello-cards: %S"
                       trello-cards)
    (->> trello-cards
         (mapcar #'orgtrello-data-to-org-trello-card)
         (orgtrello-controller-sync-buffer-with-trello-cards
          buffer-name))
    ;; keep the state clean and returns it
    data))

(defun orgtrello-controller--after-sync-buffer-with-trello-cards (data)
  "Given the state DATA, save the buffer and return at initial point."
  (-let (((_ _ _ buffer-name board-name point-start) data))
    (orgtrello-buffer-save-buffer buffer-name)
    (goto-char point-start)))

(defun orgtrello-controller-do-sync-buffer-from-trello ()
  "Full `org-mode' file synchronization.
Beware, this will block Emacs as the request is synchronous."
  (let* ((buffer-name (current-buffer))
         (board-name  (orgtrello-buffer-board-name))
         (point-start (point))
         (board-id (orgtrello-buffer-board-id))
         (prefix-log (format "Sync trello board '%s' to buffer '%s'..."
                             board-name
                             buffer-name)))
    (orgtrello-deferred-eval-computation
     (list board-id buffer-name board-name point-start)
     `('orgtrello-controller--retrieve-archive-cards
       'orgtrello-controller--retrieve-full-cards
       'orgtrello-controller--sync-buffer-with-archived-and-trello-cards
       'orgtrello-controller--after-sync-buffer-with-trello-cards
       (orgtrello-controller-log-success ,prefix-log))
     prefix-log)))

(defun orgtrello-controller--check-user-account (data)
  "Check the user account in DATA is ok.
DATA is a list of (user)."
  (let ((user-me (car data)))
    (orgtrello-log-msg
     orgtrello-log-info
     (if user-me
         (format "Account %s configured! Everything is ok!"
                 (orgtrello-data-entity-username user-me))
       "There is a problem with your credentials.\nMake sure you used M-x org-trello-install-key-and-token and this installed correctly the consumer-key and access-token.\nSee http://org-trello.github.io/trello-setup.html#credentials for more information."))))

(defun orgtrello-controller--fetch-user-logged-in (data)
  "Fetch the user logged in and return the result in DATA.
DATA is a list of (boards buffername)."
  (-> (orgtrello-api-get-me)
      (orgtrello-query-http-trello 'sync)
      (cons data)))

(defun orgtrello-controller-check-trello-connection ()
  "Full `org-mode' file synchronization.
Beware, this will block Emacs as the request is synchronous."
  (orgtrello-deferred-eval-computation
   nil
   '('orgtrello-controller--fetch-user-logged-in
     'orgtrello-controller--check-user-account)
   "Checking trello connection..."
   'no-success-log))

(defun orgtrello-controller--map-cards-to-computations (entities-adjacencies)
  "Given an ENTITIES-ADJACENCIES structure, map to computations.
The ENTITY-STRUCTURE is self contained.
Entities at first position, adjacency list in second position.
Synchronization is done here."
  (lexical-let ((entities             (car entities-adjacencies))
                (entities-adjacencies entities-adjacencies)
                (card-computations))
    (maphash (lambda (id entity)
               (when (and (orgtrello-data-entity-card-p entity)
                          (eq :ok
                              (orgtrello-controller--entity-mandatory-name-ok-p
                               entity)))
                 (-> entity
                     (orgtrello-proxy-sync-entity entities-adjacencies)
                     (push card-computations))))
             entities)
    (nreverse card-computations)))

(defun orgtrello-controller-execute-sync-entity-structure (entities-adjacencies)
  "Execute synchronization of ENTITY-STRUCTURE.
ENTITIES-ADJACENCIES is self contained.
Entities at first position, adjacency list in second position (children).
Synchronization is done here.
Along the way, the buffer BUFFER-NAME is written with new information."
  (-if-let (card-computations (orgtrello-controller--map-cards-to-computations
                               entities-adjacencies))
      (orgtrello-proxy-execute-async-computations
       card-computations
       "card(s) sync ok!"
       "FAILURE! cards(s) sync KO!")
    (orgtrello-log-msg orgtrello-log-info "No card(s) to sync.")))

(defun orgtrello-controller-compute-and-overwrite-card (buffer-name
                                                        org-trello-card)
  "Given BUFFER-NAME & ORG-TRELLO-CARD, compute, merge & update the buffer."
  (when org-trello-card
    (with-local-quit
      (with-current-buffer buffer-name
        (save-excursion
          (let* ((card-id (orgtrello-data-entity-id org-trello-card))
                 (region (orgtrello-entity-card-region))
                 (entities-from-org-buffer (apply
                                            'orgtrello-buffer-build-org-entities
                                            (cons buffer-name region)))
                 (entities-from-trello (orgtrello-backend-compute-org-trello-card-from
                                        (list org-trello-card)))
                 (merged-entities (orgtrello-data-merge-entities-trello-and-org
                                   entities-from-trello
                                   entities-from-org-buffer))
                 (entities (car merged-entities))
                 (entities-adj (cadr merged-entities)))
            (orgtrello-buffer-overwrite-card region
                                             (gethash card-id entities)
                                             entities
                                             entities-adj)))))))

(defun orgtrello-controller-checks-then-sync-card-from-trello ()
  "Check then do the actual sync if everything is ok."
  (orgtrello-action-functional-controls-then-do
   '(orgtrello-controller--on-entity-p
     orgtrello-controller--right-level-p
     orgtrello-controller--already-synced-p)
   (orgtrello-buffer-safe-entry-full-metadata)
   'orgtrello-controller-sync-card-from-trello
   (current-buffer)))

(defun orgtrello-controller--retrieve-full-card (data)
  "Retrieve the full card from the DATA.
DATA is a list of (card-meta buffer-name point-start)."
  (-> data
      car
      orgtrello-data-entity-id
      orgtrello-api-get-full-card
      (orgtrello-query-http-trello 'sync)
      (cons data)))

(defun orgtrello-controller--sync-buffer-with-trello-card (data)
  "Sync the buffer with DATA.
DATA is a list of (full-card card-meta buffer-name point-start)."
  (-let (((trello-card _ buffer-name &rest) data))
    (orgtrello-log-msg orgtrello-log-debug "trello-card: %S" trello-card)
    (->> trello-card
         orgtrello-data-to-org-trello-card
         (orgtrello-controller-compute-and-overwrite-card buffer-name))
    data))

(defun orgtrello-controller--after-sync-buffer-with-trello-card (data)
  "Given the state DATA, save the buffer and return at initial point."
  (-let (((_ _ buffer-name card-name point-start) data))
    (orgtrello-buffer-save-buffer buffer-name)
    (goto-char point-start)))

(defun orgtrello-controller-sync-card-from-trello (full-meta &optional buffer-name)
  "Entity FULL-META synchronization (with its structure) from `trello'.
BUFFER-NAME is the actual buffer to work on."
  (let* ((point-start (point))
         (card-meta (progn
                      (unless (orgtrello-entity-card-at-pt)
                        (orgtrello-entity-back-to-card))
                      (orgtrello-data-current
                       (orgtrello-buffer-entry-get-full-metadata))))
         (card-name (orgtrello-data-entity-name card-meta))
         (prefix-log (format "Sync trello card '%s' to buffer '%s'..."
                             card-name
                             buffer-name)))
    (orgtrello-deferred-eval-computation
     (list card-meta buffer-name card-name point-start)
     '('orgtrello-controller--retrieve-full-card
       'orgtrello-controller--sync-buffer-with-trello-card
       'orgtrello-controller--after-sync-buffer-with-trello-card)
     prefix-log)))

(defun orgtrello-controller--do-delete-card ()
  "Delete the card."
  (when (orgtrello-entity-card-at-pt)
    (orgtrello-controller-checks-then-delete-simple)))

(defun orgtrello-controller-do-delete-entities ()
  "Launch a batch deletion of every single entities present on the buffer.
SYNC flag permit to synchronize the http query."
  (let ((do-it (if orgtrello-with-check-on-sensible-actions
                   (orgtrello-input-confirm "Do you want to delete all cards? ")
                 t)))
    (when do-it
      (org-map-entries 'orgtrello-controller--do-delete-card t 'file))))

(defun orgtrello-controller-checks-and-do-archive-card ()
  "Check the functional requirements, then if everything is ok, archive the card."
  (let ((buffer-name (current-buffer)))
    (with-current-buffer buffer-name
      (save-excursion
        (let ((card-meta (progn
                           (when (orgtrello-entity-org-checkbox-p)
                             (orgtrello-entity-back-to-card))
                           (orgtrello-buffer-entry-get-full-metadata))))
          (orgtrello-action-functional-controls-then-do
           '(orgtrello-controller--right-level-p
             orgtrello-controller--already-synced-p)
           card-meta
           'orgtrello-controller-do-archive-card
           buffer-name))))))

(defun orgtrello-controller--archive-that-card (data)
  "Archive the card present in the DATA structure.
DATA is a list of (card-meta card-name buffer-name point-start)."
  (-let (((card-meta card-name &rest) data))
    (-> card-meta
        orgtrello-data-entity-id
        orgtrello-api-archive-card
        (orgtrello-query-http-trello 'sync)
        (cons data))))

(defun orgtrello-controller--sync-buffer-with-archive (data) ;; org archive
  "Update buffer with archive DATA."
  (-let (((_ _ card-name buffer-name point-start) data))
    (with-current-buffer buffer-name
      (goto-char point-start)
      (org-archive-subtree))
    (orgtrello-buffer-save-buffer buffer-name)))

(defun orgtrello-controller-do-archive-card (full-meta &optional buffer-name)
  "Archive current FULL-META at point.
BUFFER-NAME specifies the buffer onto which we work."
  (save-excursion
    (let* ((point-start (point))
           (card-meta (orgtrello-data-current full-meta))
           (card-name (orgtrello-data-entity-name card-meta))
           (prefix-log (format "Archive card '%s'..." card-name)))
      (orgtrello-deferred-eval-computation
       (list card-meta card-name buffer-name point-start)
       '('orgtrello-controller--archive-that-card
         'orgtrello-controller--sync-buffer-with-archive)
       prefix-log))))

(defun orgtrello-controller--do-install-config-file (user-login
                                                     consumer-key
                                                     access-token
                                                     &optional overwrite-ask)
  "Persist the setup file with USER-LOGIN, CONSUMER-KEY and ACCESS-TOKEN.
OVERWRITE-ASK is a flag to set to prevent overwriting."
  (let ((new-user-config-file (orgtrello-controller-config-file user-login)))
    (make-directory org-trello--config-dir 'do-create-parent-if-need-be)
    (with-temp-file new-user-config-file
      (erase-buffer)
      (goto-char (point-min))
      (insert (format "(setq org-trello-consumer-key \"%s\"
      org-trello-access-token \"%s\")\n"
                      consumer-key access-token))
      (write-file new-user-config-file overwrite-ask))))

(defun orgtrello-controller--open-access-token-consumer-key-url (data)
  "Browse url for the consumer-key/access-token url from DATA."
  (browse-url (orgtrello-setup-compute-url "/1/appKey/generate"))
  data)

(defun orgtrello-controller--open-ask-permissions-url (data)
  "Open the ask permissions url.
DATA is not read."
  (let ((consumer-key (s-trim (orgtrello-input-read-not-empty "Consumer key: "))))
    (->> consumer-key
         (format "/1/authorize?response_type=token&name=org-trello&scope=read,write&expiration=never&key=%s")
         orgtrello-setup-compute-url
         browse-url)
    (cons consumer-key data)))

(defun orgtrello-controller--read-access-token (data)
  "Input the access token.
Returns DATA."
  (-> (orgtrello-input-read-not-empty "Access token: ")
      s-trim
      (cons data)))

(defun orgtrello-controller--install-key-and-token-login-from-data (data)
  "Install key and token from DATA."
  (-let (((access-token consumer-key user-login) data))
    (orgtrello-controller--do-install-config-file user-login consumer-key access-token 'do-ask-for-overwrite)))

(defun orgtrello-controller-do-install-key-and-token ()
  "Procedure to install consumer-key and access token as user config-file."
  (let* ((user-login
          (orgtrello-input-read-not-empty
           "Trello login account (you need to be logged accordingly in trello.com as we cannot check this for you): "))
         (user-config-file (orgtrello-controller-config-file user-login))
         (prefix-log "Install key and token..."))
    (if (file-exists-p user-config-file)
        (orgtrello-log-msg
         orgtrello-log-info
         "Configuration for user %s already existing (file %s), skipping."
         user-login user-config-file)
      (orgtrello-deferred-eval-computation
       (list user-login)
       '('orgtrello-controller--open-access-token-consumer-key-url
         'orgtrello-controller--open-ask-permissions-url
         'orgtrello-controller--read-access-token
         'orgtrello-controller--install-key-and-token-login-from-data)
       prefix-log))))

(defun orgtrello-controller--name-id (entities)
  "Given a list of ENTITIES, return a map of (id, name)."
  (--reduce-from
   (orgtrello-hash-puthash-data
    (orgtrello-data-entity-name it)
    (orgtrello-data-entity-id it)
    acc)
   (orgtrello-hash-empty-hash) entities))

(defun orgtrello-controller--list-boards ()
  "Return the map of the existing boards associated to the current account.
Synchronous request."
  (orgtrello-query-http-trello (orgtrello-api-get-boards "open") 'sync))

(defun orgtrello-controller--list-board-lists (board-id)
  "Return the map of the existing list of the board with id BOARD-ID.
Synchronous request."
  (orgtrello-query-http-trello (orgtrello-api-get-lists board-id) 'sync))

(defun orgtrello-controller-choose-board (boards)
  "Given a BOARDS map, ask the user to choose from.
This returns the identifier of such board."
  (-> (orgtrello-input-read-string-completion
       "Board to install (TAB to complete): "
       (orgtrello-hash-keys boards))
      (gethash boards)))

(defun orgtrello-controller--convention-property-name (name)
  "Given a NAME, use the org property convention used in org-file headers."
  (->> name
       (replace-regexp-in-string " " "-")
       (replace-regexp-in-string "[()]" "")))

(defun orgtrello-controller--delete-buffer-property (property-name)
  "A simple routine to delete a #+PROPERTY: PROPERTY-NAME from the buffer."
  (save-excursion
    (goto-char (point-min))
    (while (search-forward property-name nil t)
      (delete-region (point-at-bol) (point-at-eol))
      (delete-blank-lines))))

(defun orgtrello-controller-compute-property (prop-name &optional prop-value)
  "Compute a formatted entry from PROP-NAME and optional PROP-VALUE."
  (format "#+PROPERTY: %s %s" prop-name (if prop-value prop-value "")))

(defun orgtrello-controller--compute-hash-name-id-to-list (users-hash-name-id)
  "Compute the hashmap of name-id to list from USERS-HASH-NAME-ID."
  (let ((res-list nil))
    (maphash
     (lambda (name id)
       (--> name
            (replace-regexp-in-string org-trello--label-key-user-prefix "" it)
            (format "%s%s" org-trello--label-key-user-prefix it)
            (orgtrello-controller-compute-property it id)
            (push it res-list)))
     users-hash-name-id)
    res-list))

(defun orgtrello-controller--remove-properties-file (org-keywords
                                                     users-hash-name-id
                                                     user-me
                                                     &optional update-todo-kwds)
  "Remove the current org-trello header metadata.
ORG-KEYWORDS is the `org-mode' keywords
USERS-HASH-NAME-ID is a map of username to id
USER-ME is the user's name
UPDATE-TODO-KWDS is the org list of keywords.
Works only on properties file."
  (with-current-buffer (current-buffer)
    (apply 'narrow-to-region (orgtrello-buffer-global-properties-region))
    ;; compute the list of properties to purge
    (->> `(":PROPERTIES"
           ,(orgtrello-controller-compute-property
             org-trello--property-board-name)
           ,(orgtrello-controller-compute-property
             org-trello--property-board-id)
           ,@(-map (-compose #'orgtrello-controller-compute-property
                             (-partial #'orgtrello-controller--convention-property-name))
                   org-keywords)
           ,@(orgtrello-controller--compute-hash-name-id-to-list
              users-hash-name-id)
           ,(orgtrello-controller-compute-property org-trello--property-user-me
                                                   user-me)
           ,(when update-todo-kwds "#+TODO: ")
           ,@(-map (-partial 'format "#+PROPERTY: %s")
                   (orgtrello-buffer-colors))
           ":END:")
         (mapc 'orgtrello-controller--delete-buffer-property))
    (widen)
    (save-excursion
      (goto-char (point-min))
      (delete-blank-lines))))

(defun orgtrello-controller--properties-labels (board-labels)
  "Compute properties labels from BOARD-LABELS.
\[Dict symbol String\] -> [String]"
  (let ((res-list))
    (-map (lambda (hashm)
            (message "color key: %S" (gethash :color hashm "grey"))
            (-> (format "#+PROPERTY: %s %s"
                        (gethash (gethash :color hashm)
                                 orgtrello-setup-data-color-keywords
                                 :grey)
                        (gethash :name hashm ""))
                s-trim-right
                (push res-list)))
          board-labels)
    res-list))

(defun orgtrello-controller--compute-metadata (board-name
                                               board-id
                                               board-lists-hash-name-id
                                               board-users-hash-name-id
                                               user-me
                                               board-labels
                                               &optional update-todo-keywords)
  "Compute the org-trello metadata to dump on header file.
BOARD-NAME the current board's name
BOARD-ID the current board's id
BOARD-LISTS-HASH-NAME-ID is a map of the board's trello list name to ids
BOARD-USERS-HASH-NAME-ID is a map of username to id
USER-ME is the user's name
BOARD-LABELS the board's labels
UPDATE-TODO-KEYWORDS is the org list of keywords."
  `(":PROPERTIES:"
    ,(orgtrello-controller-compute-property org-trello--property-board-name
                                            board-name)
    ,(orgtrello-controller-compute-property org-trello--property-board-id
                                            board-id)
    ,@(orgtrello-controller--compute-board-lists-hash-name-id
       board-lists-hash-name-id)
    ,(if update-todo-keywords
         (orgtrello-controller--properties-compute-todo-keywords-as-string
          board-lists-hash-name-id) "")
    ,@(orgtrello-controller--properties-compute-users-ids
       board-users-hash-name-id)
    ,@(orgtrello-controller--properties-labels board-labels)
    ,(format "#+PROPERTY: %s %s"
             org-trello--property-user-me
             (if user-me user-me org-trello--user-logged-in))
    ":END:"))

(defun orgtrello-controller--compute-keyword-separation (name)
  "Given a insensitive keyword NAME, return a string '| done' or the keyword."
  (if (string= "done" (downcase name))
      (format "| %s" name)
    name))

(defun orgtrello-controller--compute-board-lists-hash-name-id
    (board-lists-hash-name-id)
  "Compute board lists of key/name from BOARD-LISTS-HASH-NAME-ID."
  (let ((res-list))
    (maphash
     (lambda (name id)
       (--> (orgtrello-controller--convention-property-name name)
            (format "#+PROPERTY: %s %s" it id)
            (push it res-list)))
     board-lists-hash-name-id)
    res-list))

(defun orgtrello-controller--properties-compute-todo-keywords-as-string
    (board-lists-hash-name-id)
  "Compute org keywords from the BOARD-LISTS-HASH-NAME-ID."
  (s-join " " `("#+TODO:"
                ,@(let ((res-list))
                    (maphash
                     (lambda (name _)
                       (-> name
                           orgtrello-controller--convention-property-name
                           orgtrello-controller--compute-keyword-separation
                           (push res-list)))
                     board-lists-hash-name-id)
                    (nreverse res-list)))))

(defun orgtrello-controller--properties-compute-users-ids
    (board-users-hash-name-id)
  "Given BOARD-USERS-HASH-NAME-ID, compute the properties for users."
  (let ((res-list))
    (maphash (lambda (name id) (--> name
                               (format "#+PROPERTY: %s%s %s"
                                       org-trello--label-key-user-prefix
                                       it
                                       id)
                               (push it res-list)))
             board-users-hash-name-id)
    res-list))

(defun orgtrello-controller--update-orgmode-file-with-properties
    (board-name
     board-id
     board-lists-hash-name-id
     board-users-hash-name-id
     user-me
     board-labels
     &optional update-todo-keywords)
  "Update the orgmode file with the needed headers for org-trello to work.
BOARD-NAME the current board's name
BOARD-ID the current board's id
BOARD-LISTS-HASH-NAME-ID is a map of the board's trello list name to ids
BOARD-USERS-HASH-NAME-ID is a map of username to id
USER-ME is the user's name
BOARD-LABELS the board's labels
UPDATE-TODO-KEYWORDS is the org list of keywords."
  (with-current-buffer (current-buffer)
    (goto-char (point-min))
    (set-buffer-file-coding-system 'utf-8-auto) ;; force utf-8
    (->> (orgtrello-controller--compute-metadata
          board-name
          board-id
          board-lists-hash-name-id
          board-users-hash-name-id
          user-me
          board-labels
          update-todo-keywords)
         (mapc (lambda (it) (insert it "\n"))))
    (goto-char (point-min))
    (org-cycle)))

(defun orgtrello-controller--fetch-boards (data)
  "Fetch open boards and return the result in DATA.
DATA is a list (buffername)."
  (-> (orgtrello-controller--list-boards)
      (cons data)))

(defun orgtrello-controller--choose-board-id (data)
  "Choose the board-id routine.
DATA is a list of (user-logged-in boards buffername)"
  (-let (((user-logged-in boards &rest) data))
    (-> boards
        orgtrello-controller--name-id
        orgtrello-controller-choose-board
        (cons data))))

(defun orgtrello-controller--fetch-board-information (data)
  "Retrieve the detailed information on board from DATA.
DATA is a list of (board-id user-logged-in boards buffername)."
  (-> data
      car
      orgtrello-api-get-board
      (orgtrello-query-http-trello 'sync)
      (cons data)))

(defun orgtrello-controller--update-buffer-with-board-metadata (data)
  "Update properties in buffer from DATA.
DATA is a list of (board board-id user-logged-in boards buffername)."
  (-let* (((board board-id user-logged-in &rest) data)
          (members
           (->> board
                orgtrello-data-entity-memberships
                orgtrello-controller--compute-user-properties
                orgtrello-controller--compute-user-properties-hash)))
    (orgtrello-controller-do-write-board-metadata
     board-id
     (orgtrello-data-entity-name board)
     (if (hash-table-p user-logged-in)
         (orgtrello-data-entity-username user-logged-in)
       user-logged-in)
     (orgtrello-data-entity-lists board)
     (orgtrello-data-entity-labels board)
     members)
    data))

(defun orgtrello-controller--save-buffer-and-reload-setup (data)
  "Save the buffer and reload the setup from DATA.
DATA is a list and the buffername is the last element of it."
  (let ((buffer-name (car (last data))))
    (orgtrello-buffer-save-buffer buffer-name)
    (orgtrello-action-reload-setup)))

(defun orgtrello-controller-do-install-board-and-lists ()
  "Command to install the list boards."
  (let ((buffer-name (current-buffer))
        (prefix-log "Install board metadata in buffer..."))
    (orgtrello-deferred-eval-computation
     (list buffer-name)
     '('orgtrello-controller--fetch-boards                      ;; [[boards] buffer]
       'orgtrello-controller--fetch-user-logged-in              ;; [user [board] buffer]
       'orgtrello-controller--choose-board-id                   ;; [board-id user [board] buffer]
       'orgtrello-controller--fetch-board-information           ;; [board board-id user [board] buffer]
       'orgtrello-controller--update-buffer-with-board-metadata ;; [board board-id user [board] buffer]
       'orgtrello-controller--save-buffer-and-reload-setup)
     prefix-log)))

(defun orgtrello-controller--close-board (data)
  "Close the board present in DATA.
DATA is a list of (board-id user boards buffername)."
  (-let (((board-id _ _ &rest) data))
    (-> data
        car
        orgtrello-api-close-board
        (orgtrello-query-http-trello 'sync))
    data))

(defun orgtrello-controller-do-close-board ()
  "Command to install the list boards."
  (orgtrello-deferred-eval-computation
   nil
   '('orgtrello-controller--fetch-boards    ;; [[boards]]
     'orgtrello-controller--fetch-user-logged-in              ;; [user [board]]
     'orgtrello-controller--choose-board-id ;; [board-id [board]]
     'orgtrello-controller--close-board)
   "Close board according to your wishes buffer..."))

(defun orgtrello-controller--compute-user-properties (memberships-map)
  "Given a map MEMBERSHIPS-MAP, extract the map of user information."
  (mapcar 'orgtrello-data-entity-member memberships-map))

(defun orgtrello-controller--compute-user-properties-hash (user-properties)
  "Compute user's properties from USER-PROPERTIES."
  (--reduce-from (orgtrello-hash-puthash-data
                  (orgtrello-data-entity-username it)
                  (orgtrello-data-entity-id it)
                  acc)
                 (orgtrello-hash-empty-hash)
                 user-properties))

(defun orgtrello-controller--create-board (board-name &optional board-desc)
  "Create a board with name BOARD-NAME and optionally a BOARD-DESC."
  (orgtrello-log-msg orgtrello-log-info
                     "Creating board '%s' with description '%s'"
                     board-name
                     board-desc)
  (orgtrello-query-http-trello
   (orgtrello-api-add-board board-name board-desc)
   'sync))

(defun orgtrello-controller--close-lists (list-ids)
  "Given a list of ids LIST-IDS, close those lists."
  (-> (--map (lexical-let ((list-id it))
               (orgtrello-query-http-trello
                (orgtrello-api-close-list it)
                nil
                (lambda (response) (orgtrello-log-msg orgtrello-log-info
                                                 "Closed list with id %s"
                                                 list-id))
                (lambda ())))
             list-ids)
      (orgtrello-proxy-execute-async-computations
       "List(s) closed."
       "FAILURE - Problem during closing list.")))

(defun orgtrello-controller--create-lists-according-to-keywords (board-id
                                                                 org-keywords)
  "For the BOARD-ID, create the list names from ORG-KEYWORDS.
The list order in the trello board is the same as the ORG-KEYWORDS.
Return the hashmap (name, id) of the new lists created."
  (->> org-keywords
       (--reduce-from (-let (((hash pos) acc))
                        (orgtrello-log-msg
                         orgtrello-log-info
                         "Board id %s - Creating list '%s'"
                         board-id
                         it)
                        (list (orgtrello-hash-puthash-data
                               it
                               (orgtrello-data-entity-id
                                (orgtrello-query-http-trello
                                 (orgtrello-api-add-list it board-id pos)
                                 'sync))
                               hash)
                              (+ pos 1)))
                      (list (orgtrello-hash-empty-hash) 1))
       car))

(defun orgtrello-controller--input-new-board-information (data)
  "Let the user input the information on the new board.
DATA is a list of (org-keywords buffername)."
  (let ((board-name (orgtrello-input-read-not-empty
                     "Please, input desired board name: "))
        (board-desc (orgtrello-input-read-string
                     "Please, input board description (empty for none): ")))
    (cons board-name (cons board-desc data))))

(defun orgtrello-controller--create-new-board (data)
  "Create the new board from DATA.
DATA is a list of (board-name board-desc org-keywords buffername)."
  (-let (((board-name board-desc &rest) data))
    (-> (orgtrello-controller--create-board board-name board-desc)
        (cons data))))

(defun orgtrello-controller--close-board-default-lists (data)
  "Compute the default board's lists and close them.
DATA is a list of (user board board-name board-desc org-keywords buffername)."
  (-let (((_ board &rest) data))
    (->> board
         orgtrello-data-entity-id
         orgtrello-controller--list-board-lists
         (mapcar 'orgtrello-data-entity-id)
         orgtrello-controller--close-lists)
    data))

(defun orgtrello-controller--create-user-lists-to-board (data)
  "Create the user's board list from DATA.
DATA is a list of (user board board-name board-desc org-keywords buffername)."
  (-let* (((_ board _ _ org-keywords &rest) data)
          (board-id (orgtrello-data-entity-id board)))
    (orgtrello-controller--create-lists-according-to-keywords board-id org-keywords)
    (cons board-id data)))

(defun orgtrello-controller-do-create-board-and-install-metadata ()
  "Command to create a board and the lists."
  (lexical-let ((org-keywords (orgtrello-buffer-filtered-kwds))
                (buffer-name  (current-buffer))
                (prefix-log   "Create board and install metadata..."))
    (orgtrello-deferred-eval-computation
     (list org-keywords buffer-name)
     '('orgtrello-controller--input-new-board-information       ;; [[keyword] buffer-name]
       'orgtrello-controller--create-new-board                  ;; [board-desc board-name [keyword] buffer-name]
       'orgtrello-controller--fetch-user-logged-in              ;; [user board-desc board-name [keyword] buffer-name]
       'orgtrello-controller--close-board-default-lists         ;; [user board-desc board-name [keyword] buffer-name]
       'orgtrello-controller--create-user-lists-to-board        ;; [board-id user board-desc board-name [keyword] buffer-name]
       'orgtrello-controller--fetch-board-information           ;; [board board-id user board-desc board-name [keyword] buffer-name]
       'orgtrello-controller--update-buffer-with-board-metadata ;; [board board-id user board-desc board-name [keyword] buffer-name]
       'orgtrello-controller--save-buffer-and-reload-setup)
     prefix-log)))

(defun orgtrello-controller--add-user (user users)
  "Add the USER to the USERS list."
  (if (member user users)
      users
    (cons user users)))

(defun orgtrello-controller--remove-user (user users)
  "Remove the USER from the USERS list."
  (if (member user users)
      (remove user users)
    users))

(defun orgtrello-controller--remove-prefix-usernames (usernames)
  "Given USERNAMES-IDS, compute convention name from USERNAMES to a list of ids.
:: [String] -> [String]"
  (-map (-partial #'s-chop-prefix org-trello--label-key-user-prefix) usernames))

(defun orgtrello-controller--usernames (users-id-name)
  "Given USERS-ID-NAME, return usernames without org-trello naming convention.
Dict Id String -> [String]"
  (->> (orgtrello-hash-values users-id-name)
       (-filter
        (-compose 'not
                  (-partial 'equal org-trello--property-user-me)))
       orgtrello-controller--remove-prefix-usernames))

(defun orgtrello-controller-toggle-assign-user ()
  "Command to let the user choose users to assign to card.
:: () -> ()"
  (->> (orgtrello-setup-users)
       orgtrello-controller--usernames
       (orgtrello-input-read-string-completion
        "Users to assign (TAB to complete): ")
       orgtrello-controller--toggle-assign-unassign-user))

(defun orgtrello-controller--unassign-user (username users-assigned)
  "Given a USERNAME, and current USERS-ASSIGNED, unassign it from a card.
:: String -> [String] -> ()"
  (-> username
      (orgtrello-controller--remove-user users-assigned)
      orgtrello-data--users-to
      orgtrello-buffer-set-usernames-assigned-property))

(defun orgtrello-controller--assign-user (username users-assigned)
  "Given a USERNAME, and current USERS-ASSIGNED, assign it to the card at point.
:: String -> [String] -> ()"
  (-> username
      (orgtrello-controller--add-user users-assigned)
      orgtrello-data--users-to
      orgtrello-buffer-set-usernames-assigned-property))

(defun orgtrello-controller--users-assigned ()
  "Retrieve the users assigned as list.
:: () -> [String]"
  (->> (orgtrello-buffer-get-usernames-assigned-property)
       orgtrello-data--users-from))

(defun orgtrello-controller--toggle-assign-unassign-user (username)
  "Command to toggle assign/unassign USERNAME from card.
:: String -> ()"
  (let ((users-assigned (orgtrello-controller--users-assigned)))
    (if (member username users-assigned)
        (orgtrello-controller--unassign-user username users-assigned)
      (orgtrello-controller--assign-user username users-assigned))))

(defun orgtrello-controller-toggle-assign-unassign-oneself ()
  "Command to toggle assign/unassign oneself from card.
:: () -> ()"
  (-> (orgtrello-setup-user-logged-in)
      orgtrello-controller--toggle-assign-unassign-user))

(defun orgtrello-controller-do-assign-me ()
  "Command to assign oneself to the card.
:: () -> ()"
  (let ((user-me (orgtrello-setup-user-logged-in))
        (users-assigned (orgtrello-controller--users-assigned)))
    (orgtrello-controller--assign-user user-me users-assigned)))

(defun orgtrello-controller-do-unassign-me ()
  "Command to unassign oneself of the card.
:: () -> ()"
  (let ((user-me (orgtrello-setup-user-logged-in))
        (users-assigned (orgtrello-controller--users-assigned)))
    (orgtrello-controller--unassign-user user-me users-assigned)))

(defun orgtrello-controller-do-add-card-comment ()
  "Wait for the input to add a comment to the current card."
  (save-excursion
    (orgtrello-entity-back-to-card)
    (let ((card-id (-> (orgtrello-buffer-entity-metadata)
                       orgtrello-data-entity-id)))
      (if (or (null card-id) (string= "" card-id))
          (orgtrello-log-msg
           orgtrello-log-info
           "Card not synchronized so cannot add comment - skip.")
        (orgtrello-controller-add-comment card-id)))))

(defun orgtrello-controller-do-delete-card-comment ()
  "Check then do the actual card deletion if everything is ok."
  (orgtrello-action-functional-controls-then-do
   '(orgtrello-controller--on-entity-p
     orgtrello-controller--right-level-p
     orgtrello-controller--already-synced-p)
   (orgtrello-buffer-safe-entry-full-metadata)
   'orgtrello-controller--do-delete-card-comment
   (current-buffer)))

(defun orgtrello-controller--delete-card-comment-from-data (data)
  "Delete the card's comment from DATA."
  (-let (((card-id comment-id) data))
    (-> card-id
        (orgtrello-api-delete-card-comment comment-id)
        (orgtrello-query-http-trello 'sync)
        (cons data))))

(defun orgtrello-controller--delete-comment-region-from-data (data)
  "Delete the region's buffer from DATA."
  (-let* (((_ _ _ comment-region) data)
          ((region-start region-end) comment-region))
    (delete-region region-start region-end)))

(defun orgtrello-controller--do-delete-card-comment (card-meta
                                                     &optional buffer-name)
  "Delete the comment at point from the CARD-META in the BUFFER-NAME."
  (save-excursion
    (let ((card-id (-> card-meta
                       orgtrello-data-parent
                       orgtrello-data-entity-id))
          (comment-id (-> card-meta
                          orgtrello-data-current
                          orgtrello-data-entity-id)))
      (if (or (null card-id)
              (string= "" card-id)
              (string= "" comment-id))
          (orgtrello-log-msg orgtrello-log-info "No comment to delete - skip.")
        (let ((comment-region (orgtrello-entity-comment-region))
              (prefix-log "Comment deletion..."))
          (orgtrello-deferred-eval-computation
           (list card-id comment-id comment-region)
           '('orgtrello-controller--delete-card-comment-from-data
             'orgtrello-controller--delete-comment-region-from-data)
           prefix-log))))))

(defun orgtrello-controller-do-sync-card-comment ()
  "Check then do the actual sync if everything is ok."
  (orgtrello-action-functional-controls-then-do
   '(orgtrello-controller--on-entity-p
     orgtrello-controller--right-level-p
     orgtrello-controller--already-synced-p)
   (progn
     (orgtrello-entity-back-to-card)
     (orgtrello-buffer-safe-entry-full-metadata))
   'orgtrello-controller--do-sync-card-comment
   (current-buffer)))

(defun orgtrello-controller--update-card-comment (data)
  "Update card comment from DATA.
DATA is a list of (card-id comment-id comment-text buffername)."
  (-let (((card-id comment-id comment-text &rest) data))
    (-> card-id
        (orgtrello-api-update-card-comment comment-id comment-text)
        (orgtrello-query-http-trello 'sync)
        (cons data))))

(defun orgtrello-controller--do-sync-card-comment (card-meta &optional buffer-name)
  "Sync the comments from the CARD-META in BUFFER-NAME."
  (save-excursion
    (let* ((card-id (-> card-meta
                        orgtrello-data-parent
                        orgtrello-data-entity-id))
           (entity-comment (orgtrello-data-current card-meta))
           (comment-id (orgtrello-data-entity-id entity-comment))
           (comment-text (orgtrello-data-entity-description
                          entity-comment))
           (prefix-log "Synchronizing comment..."))
      (if (or (null card-id)
              (string= "" card-id)
              (string= "" comment-id))
          (orgtrello-log-msg orgtrello-log-info "No comment to sync - skip.")
        (orgtrello-deferred-eval-computation
         (list card-id comment-id comment-text buffer-name)
         '('orgtrello-controller--update-card-comment)
         prefix-log)))))

(defun orgtrello-controller-do-cleanup-from-buffer (&optional globally-flag)
  "Clean org-trello data in current buffer.
When GLOBALLY-FLAG is not nil, remove also local entities properties."
  (when org-file-properties
    (orgtrello-controller--remove-properties-file
     org-trello--org-keyword-trello-list-names
     org-trello--hmap-users-name-id
     org-trello--user-logged-in
     t) ;; remove any orgtrello relative entries
    (when globally-flag
      (orgtrello-buffer-org-map-entries
       (lambda ()
         (mapc 'orgtrello-buffer-delete-property
               `(,org-trello--label-key-id
                 ,org-trello--property-users-entry
                 ,org-trello--label-key-local-checksum)))))))

(defun orgtrello-controller-do-write-board-metadata (board-id
                                                     board-name
                                                     user-logged-in
                                                     board-lists
                                                     board-labels
                                                     board-users-name-id)
  "Given a BOARD ID, write in the current buffer the updated data.
BOARD-ID the current board's id
BOARD-NAME the current board's name
USER-LOGGED-IN user properties from the current user logged in
BOARD-LISTS is a map of the board's trello list name to ids
BOARD-LABELS board's labels
BOARD-USERS-NAME-ID is a map of username to id."
  (let* ((board-lists-hname-id (orgtrello-controller--name-id board-lists))
         (board-list-keywords  (orgtrello-hash-keys board-lists-hname-id)))
    (orgtrello-controller-do-cleanup-from-buffer)
    (orgtrello-controller--update-orgmode-file-with-properties
     board-name
     board-id
     board-lists-hname-id
     board-users-name-id
     user-logged-in
     board-labels
     board-list-keywords)))

(defun orgtrello-controller-do-update-board-metadata ()
  "Update metadata about the current board we are connected to."
  (let ((buffer-name (current-buffer))
        (board-id (orgtrello-buffer-board-id))
        (user-logged-in (orgtrello-buffer-me))
        (prefix-log "Update board metadata..."))
    (orgtrello-deferred-eval-computation
     (list board-id user-logged-in buffer-name)
     '('orgtrello-controller--fetch-board-information
       'orgtrello-controller--update-buffer-with-board-metadata
       'orgtrello-controller--save-buffer-and-reload-setup)
     prefix-log)))

(defun orgtrello-controller-do-show-board-labels ()
  "Open a pop and display the board's labels."
  (->> (orgtrello-buffer-labels)
       orgtrello-data-format-labels
       (orgtrello-buffer-pop-up-with-content "Labels")))

(defun orgtrello-controller-jump-to-card ()
  "Given a current entry, execute the extraction and the jump to card action."
  (let* ((full-meta       (orgtrello-buffer-entry-get-full-metadata))
         (entity          (orgtrello-data-current full-meta))
         (right-entity-fn (cond ((orgtrello-data-entity-item-p entity)
                                 'orgtrello-data-grandparent)
                                ((orgtrello-data-entity-checklist-p entity)
                                 'orgtrello-data-parent)
                                ((orgtrello-data-entity-card-p entity)
                                 'orgtrello-data-current))))
    (-when-let (card-id (->> full-meta
                             (funcall right-entity-fn)
                             orgtrello-data-entity-id))
      (browse-url (orgtrello-setup-compute-url (format "/c/%s" card-id))))))

(defun orgtrello-controller-jump-to-board ()
  "At current position, execute the information extraction & jump to board."
  (->> (orgtrello-buffer-board-id)
       (format "/b/%s")
       orgtrello-setup-compute-url
       browse-url))

(defun orgtrello-controller-delete-setup ()
  "Global org-trello metadata clean up."
  (orgtrello-controller-do-cleanup-from-buffer t)
  (orgtrello-log-msg orgtrello-log-no-log "Cleanup done!"))

(defvar orgtrello-controller-register "*orgtrello-register*"
  "The variable holding the Emacs' org-trello register.")

(defun orgtrello-controller-add-comment (card-id)
  "Pop up a window for the user to input a comment.
CARD-ID is the needed id to create the comment."
  (lexical-let ((card-id-to-sync card-id)
                (return-buffer-name (current-buffer))
                (return-point (point)))
    (window-configuration-to-register orgtrello-controller-register)
    (delete-other-windows)
    (org-switch-to-buffer-other-window org-trello--title-buffer-information)
    (erase-buffer)
    (let ((org-inhibit-startup t))
      (org-mode)
      (insert
       (format
        "# Insert comment for card '%s'.
# Finish with C-c C-c, or cancel with C-c C-k.\n\n" card-id-to-sync))
      (define-key org-mode-map [remap org-ctrl-c-ctrl-c]
        (lambda () (interactive)
          (orgtrello-controller-kill-buffer-and-write-new-comment
           card-id-to-sync
           return-buffer-name
           return-point)))
      (define-key org-mode-map [remap org-kill-note-or-show-branches]
        (lambda () (interactive)
          (orgtrello-controller-close-popup return-buffer-name return-point))))))

(defun orgtrello-controller-close-popup (buffer-name point)
  "Close the current buffer at point (supposed to be a popup).
Then, gets back to the BUFFER-NAME at POINT."
  (kill-buffer (current-buffer))
  (jump-to-register orgtrello-controller-register)
  (define-key org-mode-map [remap org-ctrl-c-ctrl-c] nil)
  (define-key org-mode-map [remap org-kill-note-or-show-branches] nil)
  (pop-to-buffer buffer-name)
  (goto-char point))

(defun orgtrello-controller--add-comment-to-card (data)
  "Given a DATA structure, add the comment to the card.
DATA is a list (comment card-id prefix-log)."
  (-let (((comment card-id &rest) data))
    (-> card-id
        (orgtrello-api-add-card-comment comment)
        (orgtrello-query-http-trello 'sync)
        (cons data))))

(defun orgtrello-controller--sync-card-from-trello-with-data (data)
  "Given a DATA structure, update the buffer's card.
DATA is a list (comment card-id prefix-log).
DATA is not used actually."
  (orgtrello-controller-checks-then-sync-card-from-trello)
  data)

(defun orgtrello-controller--extract-comment-and-close-popup (data)
  "Extract the comment from the buffer.
DATA is the structure holding the buffer to work with."
  (-let (((_ buffer-name point &rest) data)
         (comment (orgtrello-buffer-trim-input-comment (buffer-string))))
    (orgtrello-controller-close-popup buffer-name point)
    (cons comment data)))

(defun orgtrello-controller-kill-buffer-and-write-new-comment (card-id
                                                               buffer-name
                                                               point)
  "Write comment present in the popup buffer for the CARD-ID.
Returns to BUFFER-NAME at POINT when done."
  (let ((prefix-log (format "Add comment to card '%s'..." card-id)))
    (orgtrello-deferred-eval-computation
     (list card-id buffer-name point prefix-log)
     '('orgtrello-controller--extract-comment-and-close-popup
       'orgtrello-controller--add-comment-to-card
       'orgtrello-controller--sync-card-from-trello-with-data)
     prefix-log)))

(defun orgtrello-controller-prepare-buffer ()
  "Prepare the buffer to receive org-trello data."
  (when (orgtrello-setup-org-trello-on-p)
    (orgtrello-buffer-install-overlays)
    (orgtrello-buffer-indent-card-descriptions)
    (orgtrello-buffer-indent-card-data)))

(defun orgtrello-controller-mode-on-hook-fn ()
  "Start org-trello hook function to install some org-trello setup."
  ;; Activate org-trello--mode-activated-p
  (setq org-trello--mode-activated-p 'activated)
  ;; buffer-invisibility-spec
  (add-to-invisibility-spec '(org-trello-cbx-property))
  ;; Setup the buffer
  (orgtrello-controller-setup-properties)
  ;; installing hooks
  (add-hook 'before-save-hook 'orgtrello-controller-prepare-buffer)
  ;; prepare the buffer at activation time
  (orgtrello-controller-prepare-buffer)
  ;; run hook at startup
  (run-hooks 'org-trello-mode-hook))

(defun orgtrello-controller-mode-off-hook-fn ()
  "Stop org-trello hook function to deinstall some org-trello setup."
  ;; remove the invisible property names
  (remove-from-invisibility-spec '(org-trello-cbx-property))
  ;; removing hooks
  (remove-hook 'before-save-hook 'orgtrello-controller-prepare-buffer)
  ;; remove org-trello overlays
  (orgtrello-buffer-remove-overlays)
  ;; deactivate org-trello--mode-activated-p
  (setq org-trello--mode-activated-p nil))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-controller loaded!")

(provide 'org-trello-controller)
;;; org-trello-controller.el ends here
