
(require 'ert)
(require 'eshell-up)

;;; Code:

(ert-deftest linux-common-usage-test ()
  (skip-unless (string= system-type "gnu/linux"))
  (let ((current-path "/home/user/first/second/third/current/"))
    (should (equal "/home/user/first/" (eshell-up-find-parent-dir current-path "st")))
    (should (equal "/home/user/first/second/" (eshell-up-find-parent-dir current-path "s")))
    (should (equal "/home/user/first/second/third/" (eshell-up-find-parent-dir current-path "h")))
    (should (equal "/home/user/" (eshell-up-find-parent-dir current-path "ser")))
    (should (equal "/home/" (eshell-up-find-parent-dir current-path "hom")))
    (should (equal nil (eshell-up-find-parent-dir current-path "homme")))
    (should (equal "/home/user/first/second/third/" (eshell-up-find-parent-dir current-path nil)))))

(ert-deftest linux-closest-parent-dir-test ()
  (skip-unless (string= system-type "gnu/linux"))
  (should (equal "/first/second/" (eshell-up-closest-parent-dir "/first/second/third" )))
  (should (equal "/first/second/" (eshell-up-closest-parent-dir "/first/second/third/" )))
  (should (equal "/home/" (eshell-up-closest-parent-dir "~" )))
  (should (equal "/" (eshell-up-closest-parent-dir "/home/" )))
  (should (equal "/" (eshell-up-closest-parent-dir "/" ))))

(ert-deftest windowsx-common-usage-test ()
  (skip-unless (string= system-type "windows-nt"))
  (let ((current-path "c:\\Program Files\\WindowsApps\\first\\current\\"))
    (should (equal "c:/Program Files/WindowsApps/first/" (eshell-up-find-parent-dir current-path "fi")))
    (should (equal "c:/Program Files/WindowsApps/" (eshell-up-find-parent-dir current-path "sA")))
    (should (equal "c:/Program Files/" (eshell-up-find-parent-dir current-path " ")))
    (should (equal nil (eshell-up-find-parent-dir current-path "Programm")))
    (should (equal "c:/Program Files/WindowsApps/first/" (eshell-up-find-parent-dir current-path nil)))))
;; Windows users use 'cd \\' to go to the current drive

(ert-deftest case-test ()
  (skip-unless (string= system-type "gnu/linux"))
  (let ((current-path "/path/paTh/pATh/PATH/current/"))
    (setq eshell-up-ignore-case t)
    (should (equal "/path/paTh/pATh/PATH/" (eshell-up-find-parent-dir current-path "pa")))
    (setq eshell-up-ignore-case nil)
    (should (equal "/path/paTh/" (eshell-up-find-parent-dir current-path "pa")))
    (should (equal "/path/paTh/pATh/PATH/" (eshell-up-find-parent-dir current-path "PATH")))
    (should (equal "/path/" (eshell-up-find-parent-dir current-path "pat")))))

(ert-deftest closest-parent-skipped-test ()
  (skip-unless (string= system-type "gnu/linux"))
  (let ((current-path "/abc/def/ghi/abc/"))
    (should (equal "/abc/" (eshell-up-find-parent-dir current-path "a")))))

(provide 'eshell-up-tests)

;;; eshell-up-tests.el ends here
