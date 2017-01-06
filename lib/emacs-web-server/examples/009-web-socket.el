;;; web-sockets.el --- communicate via web-sockets
;; Copyright (C) 2014  Free Software Foundation, Inc.

(lexical-let* ((web-socket-port 9009)
               (web-socket-page
                (format "<html>
<head>
<script type=\"text/javascript\">
var ws;
function connect(){
  ws = new WebSocket(\"ws://localhost:%d/\");

  ws.onopen    = function()    { alert(\"connected\"); };
  ws.onmessage = function(msg) { alert(\"server: \" + msg.data); };
  ws.onclose   = function()    { alert(\"connection closed\"); };
}

function message(){ ws.send(\"foo\"); }

function close(){ ws.close(); };
</script>
</head>
<body>
<ol>

<li>Press \"connect\" to initialize the web socket connection to
    the server.  The server will complete the web socket
    handshake at which point you'll see an alert with the text
    \"connected\".</li>

<li>Press \"message\" to send the string \"foo\" to the server.
    The server will reply with the text \"you said: foo\" which
    you will see in an alert as \"server: you said: foo\".</li>

<li>Press \"close\" to close the connection.  After the server
    responds with a close frame you will see an alert with the
    text \"connection closed\".</li>

</ol>
<a href=\"javascript:connect()\">connect</a>
<a href=\"javascript:message()\">message</a>
<a href=\"javascript:close()\">close</a>
</body>
</html>" web-socket-port)))
  (ws-start
   (lambda (request)
     (with-slots (process headers) request
       ;; if a web-socket request, then connect and keep open
       (if (ws-web-socket-connect request
             (lambda (proc string)
               (process-send-string proc
                 (ws-web-socket-frame (concat "you said: " string)))))
           (prog1 :keep-alive (setq my-connection process))
         ;; otherwise send the index page
         (ws-response-header process 200 '("Content-type" . "text/html"))
         (process-send-string process web-socket-page))))
   web-socket-port))
