;;; hello-world-utf8.el --- utf8 hello world server using Emacs Web Server
;; Copyright (C) 2014  Free Software Foundation, Inc.

(ws-start
 (lambda (request)
   (with-slots (process headers) request
     (let ((hellos '("こんにちは"
                     "안녕하세요"
                     "góðan dag"
                     "Grüßgott"
                     "hyvää päivää"
                     "yá'át'ééh"
                     "Γεια σας"
                     "Вiтаю"
                     "გამარჯობა"
                     "नमस्ते"
                     "你好")))
       (ws-response-header process 200
         '("Content-type" . "text/plain; charset=utf-8"))
       (process-send-string process
         (concat (nth (random (length hellos)) hellos) " world")))))
 9001)
