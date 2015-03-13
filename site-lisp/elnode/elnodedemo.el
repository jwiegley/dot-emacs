;; Demo handlers for elnode

(require 'elnode)

(defun nicferrier-handler (httpcon)
  "Demonstration function.

This is a simple handler that just sends some HTML in response to
any request."
  (let* ((host (elnode-http-header httpcon "Host"))
         (pathinfo (elnode-http-pathinfo httpcon))
         )
    (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
    (elnode-http-return 
     httpcon 
     (format 
      "<html>
<body>
<h1>%s</h1>
<b>HELLO @ %s %s %s</b>
</body>
</html>
" 
      (or (cdr (assoc "name" (elnode-http-params httpcon))) "no name")
      host 
      pathinfo 
      (elnode-http-version httpcon)))))

(defun nicferrier-process-handler (httpcon)
  "Demonstration function

This is a handler based on an asynchronous process."
  (let* ((host (elnode-http-header httpcon "Host"))
         (pathinfo (elnode-http-pathinfo httpcon))
         )
    (elnode-http-start httpcon 200 '("Content-type" . "text/plain"))
    (elnode-child-process httpcon "cat" (expand-file-name "~/elnode/node.el"))))

(defun nicferrier-process-webserver (httpcon)
  "Demonstration webserver.

Shows how to use elnode's built in webserver toolkit to make
something that will serve a docroot."
  ;; Find the directory where this file is defined so we can serve
  ;; files from there
  (let ((docroot (file-name-directory
                  (buffer-file-name 
                   (car
                    (save-excursion 
                      (find-definition-noselect 'nicferrier-process-webserver nil)))))))
    (let ((webserver (elnode-webserver-handler-maker docroot)))
      (funcall webserver httpcon))))

(defun nicferrier-mapper-handler (httpcon)
  "Demonstration function

Shows how a handler can contain a dispatcher to make it simple to
handle more complex requests."
  (elnode-dispatcher httpcon
                     '(("$" . nicferrier-handler)
                       ("nicferrier/$" . nicferrier-handler))))

(defun nicferrier-post-handler (httpcon)
  "Handle a POST.

If it's not a POST send a 400."
  (if (not (equal "POST" (elnode-http-method httpcon)))
      (progn
        (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
        (elnode-http-return httpcon (format "<html>
<head>
<body>
<form method='POST' action='%s'>
<input type='text' name='a' value='100'/>
<input type='text' name='b' value='200'/>
<input type='submit' name='send'/>
</form>
</body>
</html>
" (elnode-http-pathinfo httpcon))))
    (let ((params (elnode-http-params httpcon)))
      (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
      (elnode-http-return 
       httpcon 
       (format "<html><body><ul>%s</ul></body></html>\n"
               (mapconcat 
                (lambda (param)
                  (format "<li>%s: %s</li>" (car param) (cdr param)))
                params
                "\n"))))))

(defun nicferrier-tache-enabled-post-handler (httpcon)
  "Handle a POST.

If it's not a POST send a 400."
  (if (not (equal "POST" (elnode-http-method httpcon)))
      (progn
        (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
        (elnode-http-return httpcon (format "<html>
<head>
<body>
<form method='POST' action='%s'>
<input type='text' name='a' value='100'/>
<input type='text' name='b' value='200'/>
<input type='submit' name='send'/>
</form>
</body>
</html>
" (elnode-http-pathinfo httpcon))))
    (let ((params (elnode-http-params httpcon)))
      (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
      (elnode-http-return 
       httpcon 
       (tache "<html><body><ul>((params<li>{{paramcar}}: {{paramcdr}}</li>))</ul></body></html>\n"
              `(:params
                (lambda ()
                  (mapconcat 
                   (lambda (e)
                     `(:paramcar ,(car e))
                       :paramcdr ,(cdr e))
                   params
                   "\n"))))
       )
      )
    )
  )


(defun nicferrier-everything-mapper-handler (httpcon)
  "Demonstration function

Shows how a handler can contain a dispatcher to make it simple to
handle more complex requests."
  (elnode-dispatcher 
   httpcon
   `(("$" . nicferrier-post-handler)
     ("nicferrier/\\(.*\\)$" . ,(elnode-webserver-handler-maker "~/public_html")))))



;; need to update this so something can 
(defvar nicferrier-defer-switch nil)

(defun nicferrier-defer-handler (httpcon)
  (if nicferrier-defer-switch 
      (progn
        (elnode-http-start httpcon 200 '("Content-type" . "text/html"))
        (elnode-http-return httpcon "<html>BING!</html>")
        )
    (progn 
      (setq nicferrier-defer-switch 't)
      (elnode-defer-now 'nicferrier-defer-handler))))

;; Boot elpad on port 8002
(elnode-start 'nicferrier-defer-handler 8002 "localhost")

;; End
