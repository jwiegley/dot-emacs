;;; org-trello-action.el --- Reference some action functions

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

(require 'org)
(require 'org-trello-setup)
(require 'org-trello-log)
(require 'dash-functional)
(require 's)

(defalias 'orgtrello-action-reload-setup 'org-set-regexps-and-options
  "Reload org-trello setup.")

(defun orgtrello-action--execute-controls (controls-or-actions-fns &optional entity)
  "Given CONTROLS-OR-ACTIONS-FNS, execute them and return the results.
ENTITY is an optional parameter to pass to the list of functions."
  (-map (-rpartial #'funcall entity) controls-or-actions-fns))

(defun orgtrello-action--filter-error-messages (control-or-actions)
  "Given CONTROL-OR-ACTIONS done, filter only the error messages.
Return nil if no error message."
  (-filter (-compose #'not (-partial #'equal :ok)) control-or-actions))

(defun orgtrello-action--compute-error-message (error-msgs)
  "Given a list of error messages ERROR-MSGS, compute them as a string."
  (->> (-map (-partial #'format "- %s\n") error-msgs)
       (s-join "")))

(defun orgtrello-action-controls-or-actions-then-do (control-or-action-fns
                                                     fn-to-execute
                                                     &optional nolog-p)
  "If CONTROL-OR-ACTION-FNS is ok, execute the function FN-TO-EXECUTE.
If there are errors, display them (unless NOLOG-P is set)."
  (if control-or-action-fns
      (-if-let (error-messages (-> control-or-action-fns
                                   orgtrello-action--execute-controls
                                   orgtrello-action--filter-error-messages))
          (unless nolog-p
            ;; there are some trouble, we display all the error messages to help
            ;; the user understand the problem
            (orgtrello-log-msg orgtrello-log-error "List of errors:\n %s"
                               (orgtrello-action--compute-error-message
                                error-messages)))
        ;; ok execute the function as the controls are ok
        (funcall fn-to-execute))
    ;; no control, we simply execute the function
    (funcall fn-to-execute)))

(defun orgtrello-action-functional-controls-then-do (control-fns
                                                     entity
                                                     fn-to-execute
                                                     &optional args)
  "If CONTROL-FNS are ok, pass ENTITY as parameter to FN-TO-EXECUTE.
ENTITY and ARGS are function parameter of FN-TO-EXECUTE.
If any errors are thrown during controls, then display them."
  (if control-fns
      (-if-let (error-messages (-> control-fns
                                   (orgtrello-action--execute-controls entity)
                                   orgtrello-action--filter-error-messages))
          ;; there are some trouble, we display all the error messages to help
          ;; the user understand the problem
          (orgtrello-log-msg orgtrello-log-error "List of errors:\n %s"
                             (orgtrello-action--compute-error-message
                              error-messages))
        ;; ok execute the function as the controls are ok
        (funcall fn-to-execute entity args))
    ;; no control, we simply execute the function
    (funcall fn-to-execute entity args)))

(defun orgtrello-action-msg-controls-or-actions-then-do (msg
                                                         control-or-action-fns
                                                         fn-to-execute
                                                         &optional nolog-p)
  "A decorator fn to display some log MSG.
Then execute some CONTROL-OR-ACTION-FNS.
If all controls are ok, then execute the parameter-less FN-TO-EXECUTE.
`(Optionally)`
if NOLOG-P is set, this will not log anything."
  (unless nolog-p (orgtrello-log-msg orgtrello-log-info (concat msg "...")))
  (orgtrello-action-controls-or-actions-then-do control-or-action-fns
                                                fn-to-execute nolog-p))

(defun orgtrello-action--too-deep-level (entity)
  "Given an ENTITY with level too deep, display an error message about it.
ENTITY is actually not used (implementation detail)."
  "Your arborescence depth is too deep. We only support up to depth 3.
Level 1 - card\nLevel 2 - checklist\nLevel 3 - items")

(orgtrello-log-msg orgtrello-log-debug "orgtrello-action loaded!")

(provide 'org-trello-action)
;;; org-trello-action.el ends here
