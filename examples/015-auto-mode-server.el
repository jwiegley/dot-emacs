;;; auto-mode-server.el --- files with fontification from the `auto-mode-alist'
;; Copyright (C) 2014  Free Software Foundation, Inc.

(require 'htmlize)

(lexical-let ((docroot default-directory))
  (ws-start
   (lambda (request)
     (with-slots (process headers) request
       (let ((path (ws-in-directory-p
                    docroot (substring (cdr (assoc :GET headers)) 1))))
         (if path
             (if (file-directory-p path)
                 (ws-send-directory-list process
                   (expand-file-name path docroot) "^[^\.]")
               ;; send htmlize version of file
               (let ((mode (or (cdr (cl-assoc-if (lambda (re) (string-match re path))
                                                 auto-mode-alist))
                               'fundamental-mode)))
                 (ws-response-header process 200
                   '("Content-type" . "text/html; charset=utf-8"))
                 (process-send-string process
                   (with-temp-buffer
                     (insert-file-contents-literally path)
                     (funcall mode)
                     (let ((html (htmlize-buffer)))
                       (prog1 (with-current-buffer html (buffer-string))
                         (kill-buffer html)))))))
           (ws-send-404 process)))))
   9015))
