;;; schedule.el --- calculate scheduled completion time(s)

;; Copyright (C) 1999, 2000 John Wiegley.

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 20 Jan 1999
;; Version: 2.0
;; Keywords: calendar
;; X-URL: http://www.gci-net.com/users/j/johnw/emacs.html

;; The program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This file provides a single Lisp function:
;; `schedule-completion-time'.  It takes an Emacs time object and a
;; quantity of seconds.  It returns an Emacs time object that
;; represents when the given number of seconds will be completed,
;; assuming that work can only be done during work hours.
;;
;; The available work hours are affected by several factors:
;;
;;   1. If timeclock.el is being used, the amount of time left
;;      in the current workday (timeclock-workday-remaining)
;;   2. The amount of time in each workday (schedule-workday)
;;   3. The definition of a work week (schedule-week)
;;   4. Any holidays defined in the Emacs calendar
;;   5. Any appointments in the Emacs diary
;;
;; Taking all of the "block out" periods into account,
;; `schedule-completion-time' will compute when the given number of
;; seconds will be done, based on your current definitions of time
;; available.
;;
;; As an example, here's a function which, given a list of durations
;; in seconds, will return a list of completion times starting from
;; the current moment:
;;
;;   (defun compute-completion-times (&rest durations)
;;     "Compute completion times for a list of DURATIONS (in seconds)."
;;     (let ((now (current-time)))
;;       (mapcar
;;        (function
;;         (lambda (dura)
;;           (setq now (schedule-completion-time now dura))))
;;        durations)))
;;
;; To call this function:
;;
;;    (compute-completion-times 3600 7200 3600)

;;; Code:

(require 'calendar)
(require 'diary-lib)
(require 'holidays)

(defconst schedule-version "2.0"
  "This version of schedule.")

(defgroup schedule nil
  "A mode to help keep track of project schedules."
  :group 'tasks)

;;; User Variables:

(defvar schedule-week-length nil
  "The length of the week in seconds.
This variable is computed whenever `schedule-week' is set.")

(defcustom schedule-workday (if (boundp 'timeclock-workday)
				timeclock-workday
			      (* 8 60 60))
  "*The length of a work period.
If the `timeclock' package is being used, it will be consulted in
order to determine a proper default value."
  :type 'integer
  :group 'schedule)

(defun schedule-duration-to-seconds (code)
  "Convert the given CODE into a integer quantity of seconds."
  (if (string-match "\\([0-9.]+\\)\\([smhdw]\\)" code)
      (let ((amount (string-to-number (match-string 1 code)))
	    (kind (match-string 2 code)))
	(cond ((equal kind "s")
	       amount)
	      ((equal kind "m")
	       (* amount 60))
	      ((equal kind "h")
	       (* amount 3600))
	      ((equal kind "d")
	       (* amount schedule-workday))
	      ((equal kind "w")
	       (* amount schedule-week-length))
	      (t
	       (error "Invalid duration code"))))
    (error "Invalid duration code")))

(defvar schedule-computed-week nil
  "The meaning of `schedule-week', converted into numeric form.")

(defun schedule-calculate-week ()
  "Convert `schedule-week' into `schedule-computed-week'."
  (setq
   schedule-week-length 0
   schedule-computed-week
   (mapcar
    (function
     (lambda (day)
       (when day
	 (let ((start (car day)))
	   (if (functionp start)
	       (setq start (funcall start)))
	   (if (string-match "^\\([0-9]+\\):\\([0-9]+\\)\\([ap]\\)m?$" start)
	       (let ((hour (string-to-number (match-string 1 start)))
		     (min (string-to-number (match-string 2 start)))
		     (ampm (match-string 3 start)))
		 (if (and (= hour 12) (string= ampm "a"))
		     (setq hour 0))
		 (if (and (< hour 12) (string= ampm "p"))
		     (setq hour (+ hour 12)))
		 (let ((length
			(if (functionp (cadr day))
			    (funcall (cadr day))
			  (schedule-duration-to-seconds (cadr day)))))
		   (setq schedule-week-length
			 (+ schedule-week-length length))
		   (list hour min length)))
	     nil)))))
    (symbol-value 'schedule-week))))    ; to quiet byte compiler

(defcustom schedule-week
  '(nil
    ("9:00a" "8h")
    ("9:00a" "8h")
    ("9:00a" "8h")
    ("9:00a" "8h")
    ("9:00a" "8h")
    nil)
  "*A description of what your regular week looks like.
The list should be seven elements long, the first entry being for
Sunday.  Each entry is either nil, or a list of the form (TIME-IN
DURATION).  TIME-IN should be a string of the form \"11:30a\", or a
function returning such a string; DURATION should be a duration
string, such as \"8h\", or a function returning a quantity of
seconds."
  :set (lambda (symbol value)
	 (setq schedule-week value)
	 (schedule-calculate-week)
	 schedule-week)
  :type '(repeat (choice (const :tag "No work" nil)
			 (list :tag "Workday"
			       (choice (string :tag "Time in")
				       function)
			       (choice (string :tag "Duration")
				       function))))
  :group 'schedule)

(defcustom schedule-diary-period nil
  "*How many days at a time we should look through the diary.
If you have lots of repeating appointments, things may go faster if
you decrease this number.  If this variable is set to nil, the diary
won't be consulted."
  :set (lambda (symbol value)
	 (if value
	     (require 'diary-lib))
	 (setq schedule-diary-period value))
  :type '(choice (integer :tag "Quantum of days to examine")
		 (const :tag "Don't consult diary" nil))
  :group 'schedule)

;;; Internal Variables:

(defvar schedule-day-remainder nil
  "The number of seconds remaining today.
Used in calculations only.")

(defvar schedule-diary-entries nil
  "A list of diary entries in a period.")

(defvar schedule-diary-entries-begin nil
  "The time of the beginning of `schedule-diary-entries'.")

(defvar schedule-holiday-list nil
  "A list of dates on which holidays will fall.")

(defvar schedule-initialized nil
  "Non-nil if the scheduling code has been initialized.")

;;; User Functions:

;;;###autoload
(defun schedule-completion-time (then count)
  "Advance THEN by COUNT seconds, skipping the weekends and holidays.
THEN must not already be in a holiday or non-worktime.  Make sure that
`schedule-align-now' is called at least once before this function ever
gets called."
  (unless schedule-initialized
    (schedule-initialize))
  ;; determine how much time is left in the current day
  (if (and (featurep 'timeclock)
	   (timeclock-currently-in-p)
	   (> (timeclock-workday-remaining) 0))
      (setq schedule-day-remainder (timeclock-workday-remaining))
    (setq then (schedule-align-now then)
	  schedule-day-remainder
	  (cdr (schedule-nearest-workday then))))
  ;; now calculate when the timeframe will actually end
  (while (> count 0)
    (if (< count schedule-day-remainder)
	(setq then (schedule-time-add-seconds then count)
	      schedule-day-remainder
	      (- schedule-day-remainder
		 count)
	      count 0)
      (setq count (- count schedule-day-remainder)
	    then (schedule-align-now (schedule-advance-day then))
	    schedule-day-remainder
	    (cdr (schedule-nearest-workday then)))))
  then)

;;; Internal Functions:

(defun schedule-initialize ()
  "Initialize the scheduling computation code."
  ;; initialize the cached diary entry lists
  (setq schedule-diary-entries nil
	schedule-diary-entries-begin nil)

  ;; if someone changes these values outside the customize buffer,
  ;; they will have to reload this module.
  (unless schedule-computed-week
    (schedule-calculate-week))

  ;; determine the holidays that will apply
  (setq schedule-holiday-list nil)
  (let ((h calendar-holidays))
    (while h
      (if (eq (caar h) 'holiday-fixed)
	  (setq schedule-holiday-list
		(cons (list (nth 1 (car h))
			    (nth 2 (car h)))
		      schedule-holiday-list)))
      (setq h (cdr h))))

  (setq schedule-initialized t))

(defsubst schedule-time-add-seconds (time seconds)
  "To TIME, add SECONDS.  Return result as a time value."
  (let* ((secint (truncate seconds))
	 (hi (/ secint 65536))
	 (lo (% secint 65536))
	 (calc (+ (cadr time) lo)))
    (if (< calc 65536)
	(list (+ (car time) hi) calc)
      (list (+ (car time) (1+ hi)) (% calc 65536)))))

(defsubst schedule-advance-day (then &optional count)
  "Given a time THEN, advance it by COUNT days."
  (schedule-time-add-seconds then (* 86400 (or count 1))))

(defsubst schedule-time-to-seconds (time)
  "Convert TIME to a floating point number."
  (+ (* (car time) 65536.0)
     (cadr time)
     (/ (or (car (cdr (cdr time))) 0) 1000000.0)))

(defsubst schedule-seconds-to-time (seconds)
  "Convert SECONDS (a floating point number) to an Emacs time structure."
  (list (floor seconds 65536)
	(floor (mod seconds 65536))
	(floor (* (- seconds (ffloor seconds)) 1000000))))

(defsubst schedule-time-diff (t1 t2)
  "Return the difference in seconds between T1 and T2."
  (- (schedule-time-to-seconds t1)
     (schedule-time-to-seconds t2)))

(defsubst schedule-time-less-p (t1 t2)
  "Say whether time T1 is less than time T2."
  (or (< (car t1) (car t2))
      (and (= (car t1) (car t2))
	   (< (nth 1 t1) (nth 1 t2)))))

(defsubst schedule-time-date (then)
  "Return the DATE part of THEN, in calendar friendly format."
  (let* ((elems (decode-time then)))
    (list (nth 4 elems)
	  (nth 3 elems)
	  (nth 5 elems))))

(defun schedule-seconds-to-duration (seconds)
  "Convert SECONDS to a compact time string."
  (let ((string
	 (cond ((< seconds 60)
		(format "%ds" seconds))
	       ((< seconds 3600)
		(format "%.1fm" (/ (float seconds) 60.0)))
	       ((< seconds schedule-workday)
		(format "%.1fh" (/ (float seconds) 3600.0)))
	       ((< seconds schedule-week-length)
		(format "%.1fd" (/ (float seconds) schedule-workday)))
	       (t
		(format "%.1fw"
			(/ (float seconds) schedule-week-length))))))
    (if (string-match "\\.0\\([mhdw]\\)" string)
	(replace-match "\\1" t nil string)
      string)))

(defun schedule-day-begin (then)
  "Given a time THEN, return its beginning time and length.
`schedule-week' is consulted to determine what the typical begin time
and length are for a given day of the week.  The return value is a
cons cell, with the car being a time value, and the cdr the number of
seconds during that day."
  (let* ((elems (decode-time then))
	 (dow (nth 6 elems))
	 (today (nth dow schedule-computed-week)))
    (if (not today)
	(cons then 0)
      (cons (apply 'encode-time 0 (cadr today) (car today)
		   (nthcdr 3 elems))
	    (nth 2 today)))))

;; This is from "cal-desk-calendar.el".  It should be part of Emacs.
(defun schedule-diary-entry-times (s)
  "List of times at beginning of string S in military-style integers.
For example, returns 1325 for 1:25pm.  Returns -9999 if no time is
recognized.  The recognized forms are XXXX or X:XX or XX:XX (military
time), XXam or XXpm, and XX:XXam or XX:XXpm.  If a range is given, the
list contains two elements which will be the start and end of the
range.  If only one time is given, both elements of the list will
contain the time given."
  (cond
   ;; Hour and minute range XX:XX-XX:XX[ap]m
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\):\\([0-9][0-9]\\)-\\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\>"
     s)
    (list
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 1) (match-end 1)))
		  12))
	(string-to-int (substring s (match-beginning 2) (match-end 2)))
	(if (string-equal "a"
			  (substring s (match-beginning 5) (match-end 5)))
	    0 1200))
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 3) (match-end 3)))
		  12))
	(string-to-int (substring s (match-beginning 4) (match-end 4)))
	(if (string-equal "a"
			  (substring s (match-beginning 5) (match-end 5)))
	    0 1200))
     (substring s (+ 2 (match-end 5)))))

   ;; Military time range
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\):?\\([0-9][0-9]\\)-\\([0-9]?[0-9]\\):?\\([0-9][0-9]\\)\\(\\|[^ap]\\)"
     s)
    (list
     (+ (* 100 (string-to-int
		(substring s (match-beginning 1) (match-end 1))))
	(string-to-int (substring s (match-beginning 2) (match-end 2))))
     (+ (* 100 (string-to-int
		(substring s (match-beginning 3) (match-end 3))))
	(string-to-int (substring s (match-beginning 4) (match-end 4))))
     (substring s (1+ (match-end 4)))))

   ;; Hour range HH[ap]m-HH[ap]m
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\)\\([ap]\\)m-\\([0-9]?[0-9]\\)\\([ap]\\)m\\>" s)
    (list
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 1) (match-end 1)))
		  12))
	(if (string-equal "a"
			  (substring s (match-beginning 2) (match-end 2)))
	    0 1200))
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 3) (match-end 3)))
		  12))
	(if (string-equal "a"
			  (substring s (match-beginning 4) (match-end 4)))
	    0 1200))
     (substring s (+ 2 (match-end 4)))))

   ;; Hour range HH-HH[ap]m
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\)-\\([0-9]?[0-9]\\)\\([ap]\\)m\\>" s)
    (list
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 1) (match-end 1)))
		  12))
	(if (string-equal "a"
			  (substring s (match-beginning 3) (match-end 3)))
	    0 1200))
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 2) (match-end 2)))
		  12))
	(if (string-equal "a"
			  (substring s (match-beginning 3) (match-end 3)))
	    0 1200))
     (substring s (+ 2 (match-end 3)))))

   ;; Hour and minute range XX:XX[ap]m-XX:XX[ap]m
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m-\\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\>"
     s)
    (list
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 1) (match-end 1)))
		  12))
	(string-to-int (substring s (match-beginning 2) (match-end 2)))
	(if (string-equal "a"
			  (substring s (match-beginning 3) (match-end 3)))
	    0 1200))
     (+ (* 100 (% (string-to-int
		   (substring s (match-beginning 4) (match-end 4)))
		  12))
	(string-to-int (substring s (match-beginning 5) (match-end 5)))
	(if (string-equal "a"
			  (substring s (match-beginning 6) (match-end 6)))
	    0 1200))
     (substring s (+ 2 (match-end 6)))))

   ;; Military time
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\):?\\([0-9][0-9]\\)\\(\\>\\|[^ap]\\)" s)
    (let ((time (+ (* 100 (string-to-int
			   (substring s (match-beginning 1)
				      (match-end 1))))
		   (string-to-int (substring s (match-beginning 2)
					     (match-end 2))))))
      (list time time (substring s (1+ (match-end 2))))))

   ;; Hour only XXam or XXpm
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\)\\([ap]\\)m\\>" s)
    (let ((time (+ (* 100 (% (string-to-int
			      (substring s (match-beginning 1) (match-end 1)))
			     12))
		   (if (string-equal
			"a" (substring s (match-beginning 2) (match-end 2)))
		       0 1200))))
      (list time time (substring s (+ 2 (match-end 2))))))

   ;; Hour and minute XX:XXam or XX:XXpm
   ((string-match
     "^[	]*\\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\>" s)
    (let ((time (+ (* 100 (% (string-to-int
			      (substring s (match-beginning 1)
					 (match-end 1)))
			     12))
		   (string-to-int (substring s (match-beginning 2)
					     (match-end 2)))
		   (if (string-equal
			"a" (substring s (match-beginning 3) (match-end 3)))
		       0 1200))))
      (list time time (substring s (+ 2 (match-end 3))))))

   ;; Sunrise/sunset produced by %%(diary-sunrise-sunset)
   ((string-match
     "^[	]*Sunrise \\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\> ([A-Za-z0-9+-]*), sunset \\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\> ([A-Za-z0-9+-]*)\\(.*\\)" s)
    (let ((sunrise-time
	   (+ (* 100 (% (string-to-int
			 (substring s (match-beginning 1) (match-end 1)))
			12))
	      (string-to-int (substring s (match-beginning 2) (match-end 2)))
	      (if (string-equal "a"
				(substring s (match-beginning 3) (match-end 3)))
		  0 1200)))
	  (sunset-time
	   (+ (* 100 (% (string-to-int
			 (substring s (match-beginning 4) (match-end 4)))
			12))
	      (string-to-int (substring s (match-beginning 5) (match-end 5)))
	      (if (string-equal "a"
				(substring s (match-beginning 6) (match-end 6)))
		  0 1200))))
      (list sunrise-time sunrise-time
	    (concat "Sunrise "
		    (substring s (match-beginning 1) (match-end 2)) "am"
		    (substring s (1+ (match-end 6)))
		    (substring s (match-beginning 7) (match-end 7)))
	    sunset-time sunset-time
	    (concat "Sunset "
		    (substring s (match-beginning 4) (match-end 5)) "pm"
		    (substring s (1+ (match-end 6)))
		    (substring s (match-beginning 7) (match-end 7))))))

   ;; Lunar phase produced by %%(diary-phases-of-moon)
   ((string-match
     "^[	]*\\(New\\|First Quarter\\|Full\\|Last Quarter\\) Moon \\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\> ([A-Z0-9+-]*)" s)
    (let ((time
	   (+ (* 100 (% (string-to-int
			 (substring s (match-beginning 2) (match-end 2)))
			12))
	      (string-to-int (substring s (match-beginning 3) (match-end 3)))
	      (if (string-equal
		   "a" (substring s (match-beginning 4) (match-end 4)))
		  0 1200))))
      (list time time s)))

   ;; Equinox/Solstice produced by %%(diary-equinoxes-solstices)
   ((string-match
     "^[	]*\\(Vernal Equinox\\|Summer Solstice\\|Autumnal Equinox\\|Winter Solstice\\) \\([0-9]?[0-9]\\):\\([0-9][0-9]\\)\\([ap]\\)m\\> ([A-Z0-9+-]*)" s)
    (let ((time
	   (+ (* 100 (% (string-to-int
			 (substring s (match-beginning 2) (match-end 2)))
			12))
	      (string-to-int (substring s (match-beginning 3) (match-end 3)))
	      (if (string-equal
		   "a" (substring s (match-beginning 4) (match-end 4)))
		  0 1200))))
      (list time time s)))

   ;; Unrecognizable
   (t (list -9999 -9999 s))))

(defun schedule-convert-diary-time (date diary-time)
  "Convert the given DATE and DIARY-TIME into a time value.
DIARY-TIME is an integer of the form HHMM, as returned by
`schedule-diary-entry-times'."
  (let ((minutes (* (+ (* (/ diary-time 100) 60)
		       (% diary-time 100)) 60)))
    (encode-time 0 (% minutes 60) (truncate (/ minutes 60))
		 (cadr date) (car date) (nth 2 date) nil)))

(defun schedule-get-diary-entries (then)
  "Find if there are any diary entries occurring THEN (a time value).
Return the amount of time they are scheduled to consume."
  (let ((then-date (schedule-time-date then))
	(day-length (schedule-day-begin then))
	(diff (and schedule-diary-entries-begin
		   (truncate
		    (/ (schedule-time-diff
			then schedule-diary-entries-begin) 86400)))))
    (if (or (not schedule-diary-entries)
	    (> diff schedule-diary-period))
	(let ((display-hook diary-display-hook))
	  (unwind-protect
	      (save-window-excursion
		(setq diary-display-hook nil
		      schedule-diary-entries
		      (list-diary-entries then-date
					  schedule-diary-period)
		      schedule-diary-entries-begin then))
	    (setq diary-display-hook display-hook))))
    (let ((entry schedule-diary-entries)
	  (length 0))
      (while entry
	(let ((date (caar entry)))
	  (if (equal date then-date)
	      (let* ((times (schedule-diary-entry-times
			     (cadr (car entry))))
		     (first (schedule-convert-diary-time
			     (cadr (car entry)) (car times)))
		     (last (schedule-convert-diary-time
			    (cadr (car entry)) (cadr times))))
		(if (and (schedule-time-less-p (car day-length)
					       first)
			 (schedule-time-less-p
			  last (schedule-time-add-seconds
				(car day-length) (cdr day-length))))
		    (setq length
			  (+ length (- (schedule-time-diff last first))))))))
	(setq entry (cdr entry)))
      length)))

(defun schedule-nearest-workday (then)
  "Given a time THEN, find the nearest workday."
  (let ((max 8) entry)
    (while (and (> max 0)
		(setq entry (schedule-day-begin then))
		(or (not entry) (= (cdr entry) 0)))
      (setq then (schedule-advance-day then)
	    max (1- max)))
    (if (= max 0)
	(error "There are is no work time defined during the week"))
    (and schedule-diary-period
	 (setcdr entry (- (cdr entry)
			  (schedule-get-diary-entries then))))
    entry))

(defun schedule-nearest-true-workday (then)
  "Given a time THEN, find the nearest real workday (not a holiday)."
  (let ((max 365) entry)
    (while (and (> max 0)
		(setq entry (schedule-nearest-workday then))
		;; jww (1999-04-23): this will need to be updated to
		;; handle floating holidays
		(let* ((date (schedule-time-date (car entry)))
		       (mon-day (list (car date) (cadr date))))
		  (member mon-day schedule-holiday-list)))
      (setq then (car entry)
	    then (schedule-advance-day then)
	    max (1- max)))
    (if (= max 0)
	(error "There is no time available for at least a year"))
    entry))

(defun schedule-align-now (then)
  "Given a time THEN, move it ahead to the next valid moment."
  (let ((day (schedule-nearest-true-workday then)))
    (if (schedule-time-less-p then (car day))
	(car day)
      (if (> (- (schedule-time-diff then (car day)))
	     (cdr day))
	  (car (schedule-nearest-true-workday
		(schedule-advance-day then)))
	then))))

(provide 'schedule)

;;; schedule.el ends here
