;;; file-upload.el --- use an uploaded file
;; Copyright (C) 2014  Free Software Foundation, Inc.

(ws-start
 '(((:POST . ".*") .
    (lambda (request)
      (with-slots (process headers) request
        (ws-response-header process 200 '("Content-type" . "text/plain"))
        (let ((file (cdr (assoc "file" headers))))
          (process-send-string process
            (concat (sha1 (cdr (assoc 'content file))) "  "
                    (cdr (assoc 'filename file)) "\n")))))))
 9008)
