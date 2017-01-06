;;; file-server.el --- serve any files using Emacs Web Server
;; Copyright (C) 2014  Free Software Foundation, Inc.

(lexical-let ((docroot default-directory))
  (ws-start
   (lambda (request)
     (with-slots (process headers) request
       (let ((path (substring (cdr (assoc :GET headers)) 1)))
         (if (ws-in-directory-p docroot path)
             (if (file-directory-p path)
                 (ws-send-directory-list process
                   (expand-file-name path docroot) "^[^\.]")
               (ws-send-file process (expand-file-name path docroot)))
           (ws-send-404 process)))))
   9003))
