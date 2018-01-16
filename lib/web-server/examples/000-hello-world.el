;;; hello-world.el --- simple hello world server using Emacs Web Server
;; Copyright (C) 2014  Free Software Foundation, Inc.

(ws-start
 (lambda (request)
   (with-slots (process headers) request
     (ws-response-header process 200 '("Content-type" . "text/plain"))
     (process-send-string process "hello world")))
 9000)
