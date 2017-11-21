;;; org-trello-deferred.el --- Deferred computations in org-trello

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

(defun orgtrello-deferred--compute-deferred-computation (initial-state
                                                         fns
                                                         msg-log
                                                         &optional no-success-log)
  "Given an INITIAL-STATE, thread the FNS together.
MSG-LOG is used in case of failure.
If NO-SUCCESS-LOG is set, do not execute the success message callback."
  (let ((deferred-fns (-map  (lambda (fn) `(deferred:nextc it ,fn)) fns)))
    (if no-success-log
        `(deferred:$
           (deferred:next (lambda () ',initial-state))
           ,@deferred-fns
           (deferred:error it
             (orgtrello-controller-log-error ,msg-log "Error: %S")))
      `(deferred:$
         (deferred:next (lambda () ',initial-state))
         ,@deferred-fns
         (deferred:nextc it
           (orgtrello-controller-log-success ,msg-log))
         (deferred:error it
           (orgtrello-controller-log-error ,msg-log "Error: %S"))))))

(defun orgtrello-deferred-eval-computation (initial-state
                                            fns
                                            msg-log
                                            &optional no-success-log)
  "Given an INITIAL-STATE, thread the FNS together.
MSG-LOG is used in case of failure.
If NO-SUCCESS-LOG is set, do not execute the success message callback."
  (orgtrello-log-msg orgtrello-log-info msg-log)
  (->> (orgtrello-deferred--compute-deferred-computation initial-state
                                                         fns
                                                         msg-log
                                                         no-success-log)
       eval))

(provide 'org-trello-deferred)
;;; org-trello-deferred.el ends here
