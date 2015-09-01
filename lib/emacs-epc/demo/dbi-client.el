(require 'epc)

(defun edbc-query ()
  (interactive)
  (lexical-let*
      (
       (dbname (read-string "db file: "))
       (sql (read-string "SQL : "))
       (epc (epc:start-epc "perl" '("dbi-server.pl"))))
    (message "DB %s / %s [%S]" dbname sql epc)
    (deferred:$
      (epc:call-deferred epc 'connect dbname)
      (deferred:nextc it 
        (lambda (x) (message "Return : %S" x)
          (epc:call-deferred epc 'query sql)))
      (deferred:nextc it 
        (lambda (records) 
          (let ((buf (get-buffer-create "*EDBC Result*")))
            (with-current-buffer buf
              (erase-buffer)
              (loop for line in records do
                    (loop for col in line do
                          (insert (format "%s | " col)))
                    (insert "\n")))
            (pop-to-buffer buf))
          (epc:stop-epc epc)))
      (deferred:watch it
        (lambda (x) 
          (epc:stop-epc epc))))))
