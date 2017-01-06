;;; search-bbdb.el --- search the Big Brother Data Base for a supplied name
;; Copyright (C) 2014  Free Software Foundation, Inc.

(ws-start
 (lambda (request)
   (with-slots (process headers) request
     (let ((name (cdr (assoc "name" headers))))
       (unless name
         (ws-error process "Must specify a name to search."))
       (save-excursion
         (unless (set-buffer (get-buffer "*BBDB*"))
           (ws-error process "no *BBDB* buffer found"))
         (bbdb-search-name name)
         (if (equal (point-min) (point-max))
             (progn
               (ws-response-header process 404
                 '("Content-type" . "text/plain"))
               (process-send-string process
                 "no matches found"))
           (ws-response-header process 200
             '("Content-type" . "text/plain"))
           (process-send-string process (buffer-string)))))))
 9012)
