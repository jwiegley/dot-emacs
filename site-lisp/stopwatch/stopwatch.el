;; stopwatch.el --- Calculate the time

;; Copyright (C) 2010 tequilasunset

;; Author: tequilasunset <tequilasunset.mac@gmail.com>
;; Keywords: time, stopwatch, convenience

;; Forked: Copyright (C) 2013 
(defconst stopwatch-version "0.21")

;; This program is free software: you can redistribute it and/or modify
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

(require 'cl)

(defun stopwatch-formatting (time)
  (if (= (length time) 2)
      (append time '(0))
    time))

(defun stopwatch (time1 &optional time2)
  "Calculate the time between TIME1 and TIME2,
If TIME2 is ommitted, compare with a current time."
  (destructuring-bind (t10 t11 t12 t13 t20 t21 t22 t23)
      (append (stopwatch-formatting time1)
              (if time2
                  (stopwatch-formatting time2)
                (current-time)))
    (abs (- (+ (* (+ (* t10 100000) t11) 1000000) t12)
            (+ (* (+ (* t20 100000) t21) 1000000) t22)))))

(defmacro stopwatch-define-unit-fn (unit &rest divisors)
  "Define the function `stopwatch-by-UNIT'."
  `(progn (defun ,(intern (format "stopwatch-by-%s" unit))
             (time1 &optional time2 integer)
             ,(format "Calculate the time by %s.
If TIME2 is nil, compare with a current time.
Third optional argument INTEGER specifies whether
to return integer or float." unit)
             (/ (funcall (if integer 'identity 'float)
                         (stopwatch time1 time2)) ,@divisors))
;;            (defmacro ,(intern (format "with-stopwatch-%s" unit)) 
;;              (message &rest body)
;;              "Evaluate BODY with calculating the processing time of it
;; by millisecond, then return the value of BODY and display
;; the time with MESSAGE."
;;              (declare (indent 1))
;;              `(let ((msg (message "Running %s..." ,message))
;;                     (start (current-time))
;;                     (val (progn ,@body)))
;;                 (message "%sdone [%s ms]" msg (,(intern (format "stopwatch-by-%s" unit)) start))
;;                 val))
))

(stopwatch-define-unit-fn ms   1000)
(stopwatch-define-unit-fn sec  1000 1000)
(stopwatch-define-unit-fn min  1000 1000 60)
(stopwatch-define-unit-fn hour 1000 1000 60 60)
(stopwatch-define-unit-fn day  1000 1000 60 60 24)

(defmacro with-stopwatch (message &rest body)
  "Evaluate BODY with calculating the processing time of it
by millisecond, then return the value of BODY and display
the time with MESSAGE."
  (declare (indent 1))
  `(let ((msg (message "Running %s..." ,message))
         (start (current-time))
         (val (progn ,@body)))
     (message "%sdone [%.2f s]" msg (stopwatch-by-sec start))
     val))

(provide 'stopwatch)
;;; stopwatch.el ends here

;; Local Variables:
;; mode: emacs-lisp
;; coding: utf-8-unix
;; indent-tabs-mode: nil
;; End:
