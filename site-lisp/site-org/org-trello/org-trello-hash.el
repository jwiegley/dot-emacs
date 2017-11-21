;;; org-trello-hash.el --- Hash manipulation functions (the base data structure)

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

(require 'org-trello-log)

(defun orgtrello-hash-empty-hash ()
  "Empty hash table with test 'equal."
  (make-hash-table :test 'equal))

(defun orgtrello-hash-gethash-data (key map &optional default-value)
  "Retrieve the value at KEY in MAP.
If the value is not found, return DEFAULT-VALUE."
  (when map (gethash key map default-value)))

(defun orgtrello-hash-puthash-data (key value entity)
  "Update at KEY the VALUE in the ENTITY map.
Return the entity updated or nil if the entity is nil."
  (when entity
    (puthash key value entity)
    entity))

(defun orgtrello-hash-make-properties (properties)
  "Return a hash-table from PROPERTIES key/values."
  (--reduce-from (orgtrello-hash-puthash-data (car it) (cdr it) acc)
                 (orgtrello-hash-empty-hash)
                 properties))

(defun orgtrello-hash-make-transpose-properties (properties)
  "Return a hash-table with transposed key/value from PROPERTIES key/values."
  (--reduce-from (orgtrello-hash-puthash-data (cdr it) (car it) acc)
                 (orgtrello-hash-empty-hash)
                 properties))

(defun orgtrello-hash-init-map-from (data)
  "Init a map from a given DATA.
If data is nil, return an empty hash table."
  (if data data (orgtrello-hash-empty-hash)))


(defun orgtrello-hash-keys (hash-table)
  "Return a list of keys in HASH-TABLE."
  (let ((keys '()))
    (maphash (lambda (k _v) (push k keys)) hash-table)
    (nreverse keys)))

(defun orgtrello-hash-values (hash-table)
  "Return a list of values in HASH-TABLE."
  (let ((values '()))
    (maphash (lambda (_k v) (push v values)) hash-table)
    (nreverse values)))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-hash loaded!")

(provide 'org-trello-hash)
;;; org-trello-hash.el ends here
