;;; org-mode-file-server.el --- serve on-demand exported Org-mode files
;; Copyright (C) 2014  Free Software Foundation, Inc.

(lexical-let ((docroot "/tmp/"))
  (ws-start
   (lambda (request)
     (with-slots (process headers) request
       (let ((path (ws-in-directory-p ; check if path is in docroot
                    docroot (substring (cdr (assoc :GET headers)) 1))))
         (unless path (ws-send-404 process)) ; send 404 if not in docroot
         (if (file-directory-p path)
             (progn ;; send directory listing, convert org files to html/tex/txt
               (ws-response-header proc 200 (cons "Content-type" "text/html"))
               (process-send-string proc
                 (concat "<ul>"
                         (mapconcat
                          (lambda (f)
                            (let* ((full (expand-file-name f path))
                                   (end (if (file-directory-p full) "/" ""))
                                   (url (url-encode-url (concat f end))))
                              (format "<li><a href=%s>%s</li>" url f)))
                          (apply #'append
                                 (mapcar
                                  (lambda (f)
                                    (list (concat f ".txt")
                                          (concat f ".tex")
                                          (concat f ".html")))
                                  (mapcar #'file-name-sans-extension
                                          (directory-files path nil
                                                           "^[^\.].*org$"))))
                          "\n") "</ul>")))
           ;; Export the file as requested and return the result
           (let* ((base (file-name-sans-extension path))
                  (type (case (intern (downcase (file-name-extension path)))
                          (html 'html)
                          (tex  'latex)
                          (txt  'ascii)
                          (t (ws-error process "%S export not supported"
                                       (file-name-extension path)))))
                  (orig (concat base ".org")))
             (unless (file-exists-p orig) (ws-send-404 process))
             (save-window-excursion (find-file orig)
                                    (org-export-to-file type path))
             (ws-send-file process path))))))
   9007))
