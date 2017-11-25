;;; docker-compose-mode-helpers.el --- Helper functions for docker-compose-mode  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Ricardo Martins

;; Author: Ricardo Martins

;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at
;;
;; http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.

;;; Code:

(require 'docker-compose-mode)
(require 'f)
(require 'json)

(defun docker-compose--extract-keywords-from-schema-tree (root tree)
  "Extract a list of keywords from docker-compose JSON schema TREE."
  (let-alist tree
    (-concat
     (when .$ref
       (docker-compose--extract-keywords-from-schema-tree root (docker-compose--dereference root .$ref)))
     (docker-compose--read-one-of root .oneOf)
     (docker-compose--read-properties root .properties)
     (docker-compose--read-pattern-properties root .patternProperties))))

(defun docker-compose--dereference (tree reference)
  "Find definition for a REFERENCE in the given JSON schema TREE."
  (string-match "#/definitions/\\(.+\\)" reference)
  (let ((refname (intern-soft (match-string-no-properties 1 reference)))
        (definitions (cdr (assq 'definitions tree))))
    (cdr (assq refname definitions))))

(defun docker-compose--read-pattern-properties (root pattern-properties)
  "Extract keywords from a PATTERN-PROPERTIES node in the docker-compose schema tree."
  (--map
   (-let (((regex . rest) it))
     (cons (symbol-name regex) (docker-compose--extract-keywords-from-schema-tree root rest)))
   pattern-properties))

(defun docker-compose--read-properties (root properties)
  "Extract keywords from a PROPERTIES node in the docker-compose schema tree."
  (--map
   (-let (((keyword . rest) it))
     (cons (symbol-name keyword) (docker-compose--extract-keywords-from-schema-tree root rest)))
   properties))

(defun docker-compose--read-one-of (tree alternatives)
  "Extract keywords from the ALTERNATIVES of a 'oneOf' node in the JSON schema TREE."
  (-non-nil
   (--mapcat (docker-compose--extract-keywords-from-schema-tree tree it) alternatives)))

(defun docker-compose--extract-keywords-from-schema-file (path)
  "Extract a list of keywords from the docker-compose JSON schema file at PATH."
  (let ((tree (json-read-file path)))
    (docker-compose--extract-keywords-from-schema-tree tree tree)))

(defun docker-compose--generate-lists-of-keywords (path)
  "Generate a list of lists of docker-compose keywords by extracting them from the schema files present in PATH."
  (--map
   (progn
     (string-match "config_schema_v\\(.*\\).json" it)
     (cons (docker-compose--normalize-version (match-string-no-properties 1 it))
           (docker-compose--extract-keywords-from-schema-file it)))
   (f-glob "config_schema_*.json" path)))

(provide 'docker-compose-mode-helpers)
;;; docker-compose-mode-helpers.el ends here
