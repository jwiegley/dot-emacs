(require 'epc)

(setq epc (epc:start-epc "perl" '("echo-server.pl")))
(setq epc2 (epc:start-epc "perl" '("echo-server.pl")))

(deferred:$
  (epc:call-deferred epc 'echo 10)
  (deferred:nextc it 
    (lambda (x) (message "Return : %S" x))))

(deferred:$
  (epc:call-deferred epc 'add '(10 40))
  (deferred:nextc it 
    (lambda (x) (message "Return : %S" x))))

(message "%S" (epc:call-sync epc 'echo '(10 40)))
(message "%S" (epc:call-sync epc2 'add '(10 40)))

(message "%S" (epc:sync epc (epc:query-methods-deferred epc)))

(epc:stop-epc epc)
(epc:stop-epc epc2)
