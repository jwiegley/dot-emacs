;;; web-file-upload.el -- example uploader -*- lexical-binding: t -*-

(require 'elnode)
(require 'fakir)
(require 'time-stamp)

(defun web-file-upload-handler (httpcon)
  (elnode-method httpcon
    (POST
     (let ((file-data (elnode-http-param httpcon "my-file")))
       (when file-data
         (with-current-buffer (get-buffer-create "elnode-file-upload")
           (insert (base64-decode-string file-data))
           (pop-to-buffer (current-buffer))))
       (elnode-send-status httpcon 200)))))

(defun web-file-json-upload-handler (httpcon)
  (elnode-method httpcon
    (POST
     (let ((file-data (elnode-http-param httpcon "package")))
       (when file-data
         (with-current-buffer (get-buffer-create "elnode-file-upload")
           (insert file-data)
           (pop-to-buffer (current-buffer))))
       (elnode-send-json httpcon '(("status" . "done")))))))

(defun web-file-upload-test ()
  ;; Start an elnode server...
  (elnode-start 'web-file-json-upload-handler :port 9020)
  ;; ... and then make a request to  it
  (fakir-with-file-buffer myfile
    (with-current-buffer myfile (insert "hello!!!!"))
    (web-http-post
     (lambda (con hdr data)(message "web -- from elnode: %s" hdr))
     :url "http://localhost:9020"
     :data `(("my-file" . ,myfile))
     :mime-type web-multipart-mimetype
     :logging t)))

(web-file-upload-test)

;;; web-file-upload.el ends here

