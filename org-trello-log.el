;;; org-trello-log.el --- Log related functions.

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

(defconst orgtrello-log-no-log 0 "No log level except for error.")
(defconst orgtrello-log-error  1 "Error log level.")
(defconst orgtrello-log-warn   2 "Warn log level.")
(defconst orgtrello-log-info   3 "Info log level.")
(defconst orgtrello-log-debug  4 "Debug log level.")
(defconst orgtrello-log-trace  5 "Trace log level.")

(defcustom orgtrello-log-level orgtrello-log-info
  "Set log level.
Levels:
0 - no log   (`orgtrello-log-quiet')
1 - errors   (`orgtrello-log-error')
2 - warnings (`orgtrello-log-warn')
3 - info     (`orgtrello-log-info')
4 - debug    (`orgtrello-log-debug')
5 - trace    (`orgtrello-log-trace')
To change such level, add this to your init.el file:
\(custom-set-variables '\(orgtrello-log-level orgtrello-log-trace\)\)"
  :options (list orgtrello-log-no-log
                 orgtrello-log-error
                 orgtrello-log-warn
                 orgtrello-log-info
                 orgtrello-log-debug
                 orgtrello-log-trace)
  :type 'integer
  :require 'org-trello
  :group 'org-trello)

(defun orgtrello-log-msg (level &rest args)
  "Log message with LEVEL.
Depending on `orgtrello-log-level', this will be displayed or not.
All errors are displayed anyway.
ARGS constitutes the parameters to feed to message."
  (when (or (<= level orgtrello-log-level) (eq orgtrello-log-error level))
    (apply 'message (format "org-trello - %s" (car args)) (cdr args))))

(orgtrello-log-msg orgtrello-log-debug "orgtrello-log loaded!")

(provide 'org-trello-log)
;;; org-trello-log.el ends here
