;;; 013-org-export-service.el --- upload and export Org-mode files
;; Copyright (C) 2014  Free Software Foundation, Inc.

(ws-start
 (lambda (request)
   (with-slots (process headers) request
     (let ((file (cdr (assoc "file" headers)))
           (type (cdr (assoc 'content (cdr (assoc "type" headers))))))
       (if (not (and file type))
           (progn
             (ws-response-header process 200 '("Content-type" . "text/html"))
             (process-send-string process "
<html><body><form action=\"\" method=\"post\" enctype=\"multipart/form-data\">
Export file: <input type=\"file\" name=\"file\"> to type
<select name=\"type\">
<option value=\"txt\">Text</option>
<option value=\"html\">HTML</option>
<option value=\"tex\">TeX</option>
</select>
<input type=\"submit\" value=\"submit\">.
</form></body></html>"))
         (let* ((orig (cdr (assoc 'filename file)))
                (base (file-name-nondirectory
                       (file-name-sans-extension orig)))
                (backend (case (intern (downcase type))
                           (html 'html)
                           (tex  'latex)
                           (txt  'ascii)
                           (t (ws-error process "%S export not supported"
                                        type))))
                (path (concat base "." type)))
           (let ((default-directory temporary-file-directory))
             (when (or (file-exists-p orig) (file-exists-p path))
               (ws-error process
                         "File already exists on the server, try a new file."))
             (with-temp-file orig (insert (cdr (assoc 'content file))))
             (save-window-excursion (find-file orig)
                                    ;; TODO: Steal personal data and
                                    ;; ideas from uploaded Org-mode
                                    ;; text.  Web services aren't free!
                                    (org-export-to-file backend path)
                                    (kill-buffer))
             (ws-send-file process path)
             (delete-file path)
             (delete-file orig)))))))
 9013)
