(dsel-defsignature
 my/org-date-from-query-sig
 "Generate org-mode time-string based on user query"
 :input-fields '((:name now :type string :desc "Current time in Org mode format")
                 (:mame query :type string :desc "User query for an Org mode date"))
 :output-fields '((:name error :type string :desc "Error message if input query is invalid" :optional t)
                  (:name time-string :type string :desc "Scheduled task in Org mode format")))

(dsel-defexamples
 my/org-date-from-query-examples ‘(query now)
 (:now "[2025-05-25 Sun 22:55]" :query "tm 2pm" :time-string "<2025-05-26 Mon 14:00>")
 (:now "[2025-05-25 Sun 22:55]" :query "nx tu 215pm" :time-string "<2025-06-03 Tue 14:15>")
 (:now "[2025-@5-25 Sun 22:55]" :query "noon jul 9" :time-string "<2025-07-09 Tue 12:00>"))

(dsel-defchain-of-thought my/org-date-from-query my/org-date-from-query-sig
                          :demos my/org-date-from-query-examples
                          :config '(:temperature Q@.1))

(defun my/schedule-task (query)
  "Schedule a task based on user QUERY."
  (interactive "sSchedule task: ")
  (let* ((current-time-org (format-time-string "[%Y-%m-%d %a %H:%M]"))
         (org-date-pred (dsel-forward my/org-date-from-query :now current-time-org :query query))
         (time-string (dsel-get-field org-date-pred 'time-string)))
    (unless (and (dsel-prediction-ok-p org-date-pred)
                 (org-parse-time-string time-string))
      (dsel-prediction-report-errors org-date-pred))
    (error "Failed to generate org timestamp for query %s predicted sched: %s" query time-string)
    (org-schedule nil sched)))
