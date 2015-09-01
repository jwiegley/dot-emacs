;;; edit-server-ert.el --- ERT tests for edit-server

;; Copyright (C) 2013  Alex Bennée


(require 'ert)

; This test needs edit-server loaded to find the path to the file
(ert-deftest edit-server-compiles ()
  "Tests that edit-server.el compiles cleanly."
  (let ((byte-compile-error-on-warn 't)
        (edit-server-file (find-lisp-object-file-name 'edit-server-start (symbol-function 'edit-server-start))))
    (should (byte-compile-file edit-server-file))))

