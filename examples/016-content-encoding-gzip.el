;;; content-encoding-gzip.el -- gzip content encoding
;; Copyright (C) 2014  Free Software Foundation, Inc.

(ws-start
 (lambda (request)
   (with-slots (process headers) request
     (ws-response-header process 200
       '("Content-type" . "text/plain; charset=utf-8")
       '("Content-Encoding" . "x-gzip"))
     (let ((s "Lorem ipsum dolor sit amet, consectetuer adipiscing elit. Donec
hendrerit tempor tellus. Donec pretium posuere tellus. Proin quam
nisl, tincidunt et, mattis eget, convallis nec, purus. Cum sociis
natoque penatibus et magnis dis parturient montes, nascetur
ridiculus mus. Nulla posuere. Donec vitae dolor. Nullam tristique
diam non turpis. Cras placerat accumsan nulla. Nullam rutrum. Nam
vestibulum accumsan nisl.

Lorem ipsum dolor sit amet, consectetuer adipiscing elit. Donec
hendrerit tempor tellus. Donec pretium posuere tellus. Proin quam
nisl, tincidunt et, mattis eget, convallis nec, purus. Cum sociis
natoque penatibus et magnis dis parturient montes, nascetur
ridiculus mus. Nulla posuere. Donec vitae dolor. Nullam tristique
diam non turpis. Cras placerat accumsan nulla. Nullam rutrum. Nam
vestibulum accumsan nisl."))
       (ws-send process s))))
 9016)
