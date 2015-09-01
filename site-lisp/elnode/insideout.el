;; Expose your running emacs to the local web by using elnode
;; Copyright (C) 2010 by Nic Ferrier

(defun insideout-html-escape (str)
  "Escape significant HTML characters in 'str'"
  (replace-regexp-in-string 
   "<\\|\\&" 
   (lambda (src)
     (cond
      ((equal src "&") "&amp;")
      ((equal src "<")  "&lt;")))
   str))

(defun insideout-render (buf-name)
  "Render buffer 'buf' as HTML"
  (with-current-buffer (get-buffer buf-name)
    (format "<html>
<body><pre>%s</pre></body>
</html>"
            (insideout-html-escape
             (buffer-substring-no-properties (point-min) (point-max))))))

(defun insideout-handler (httpcon)
  "Turn your emacs insideout with elnode.

This exposes all your non * buffers to localhost - so beware."
  (let ((p (elnode-http-pathinfo httpcon)))
    (let ((buf-name (progn
                      (string-match "/\\(.*\\)" p)
                      (match-string 1 p))))
      ;; An individual buffer
      (progn
        (elnode-http-start httpcon 200 '("Content-Type" . "text/html"))
        (elnode-http-return 
         httpcon 
         (if (bufferp (get-buffer buf-name))
             (insideout-render buf-name)
           ;; The buffer index
           (format "<html><body><ul>%s</ul></body></html>"
                   (mapconcat
                    (lambda (buf)
                      (if (not (string-match "\\*" (buffer-name buf)))
                          (format "<li><a href='/%s'>%s</a></li>"
                                  (buffer-name buf)
                                  (buffer-name buf))))
                    (buffer-list)
                    "\n"))))))))

(elnode-start 'insideout-handler 8028 "localhost")

;; End
