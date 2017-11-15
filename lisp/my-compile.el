(setq
 compile-command
 '(cond
   ((string-match "concerto" default-directory)
    "(cd ~/bae/concerto/solver ; make clean ; cabal build && PATH=./dist/build/solver solver --args test/TXRX.opts)")
   (t
    (car compile-history))))

(provide 'my-compile)
