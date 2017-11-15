;;; prodigy-process-handling-test.el --- Prodigy: Tests various processes related things -*- lexical-binding: t; -*-

;; Copyright (C) 2014 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Code:

(require 'ert-async)


;;;; prodigy-start-service

(ert-deftest-async prodigy-start-service-test/callback-when-started (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-stop-service service nil done))))))

(ert-deftest-async prodigy-start-service-test/fail-when-not-started-after-tryouts (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service
                   :command "echo"
                   :args '("foo"))))
     (prodigy-start-service service)
     (prodigy-test/delay 2
       (lambda ()
         (when (eq (plist-get service :status) 'failed)
           (funcall done)))))))

(ert-deftest prodigy-start-service-test/path ()
  
  )

(ert-deftest prodigy-start-service-test/env ()
  
  )

(ert-deftest-async prodigy-start-service-test/start-service-with-sudo (done)
  (unwind-protect
      (with-sandbox
       (ad-add-advice
        'start-process-shell-command
        (list 'prodigy-sudo-test-spsc-advice
              nil t
              '(advice . (lambda ()
                           (should (s-starts-with-p "sudo " (ad-get-arg 2)))
                           (ad-set-arg 2 (substring (ad-get-arg 2) 5)))))
        'before 'first)
       (ad-activate 'start-process-shell-command)
       (mock (read-passwd "Sudo password for `cat': ") => "dummy-sudo-password")
       (let ((service (car
                       (prodigy-define-service
                         :name "Sudo test service"
                         :sudo t
                         :command "cat"
                         :on-output (lambda (&rest args)
                                      (should (string= (plist-get args :output) "dummy-sudo-password\n"))
                                      (funcall done))))))
         (prodigy-start-service service)))
    (ad-disable-advice 'start-process-shell-command 'before 'prodigy-sudo-test-spsc-advice)))

;;;; on-output

(ert-deftest-async prodigy-start-service-test/on-output/no-tags (done-log-foo done-stop)
  (with-sandbox
   (let ((service (prodigy-test/make-service
                   :on-output (lambda (&rest args)
                                (let ((output (plist-get args :output))
                                      (service (plist-get args :service)))
                                  (when (string-match-p (regexp-quote "foo\n") output)
                                    (funcall done-log-foo))
                                  (when (string-match-p (regexp-quote "bar\n") output)
                                    (prodigy-stop-service service nil done-stop)))))))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'log "foo")
         (prodigy-test/post-message service 'log "bar"))))))

(ert-deftest-async prodigy-start-service-test/on-output/with-tag (done-service done-stop)
  (with-sandbox
   (prodigy-define-tag
     :name 'tag
     :on-output (lambda (&rest args)
                  (let ((output (plist-get args :output))
                        (service (plist-get args :service)))
                    (when (string= output "foo\n")
                      (prodigy-stop-service service nil done-stop)))))
   (let ((service
          (prodigy-test/make-service
           :tags '(tag)
           :on-output (lambda (&rest args)
                        (let ((output (plist-get args :output))
                              (service (plist-get args :service)))
                          (when (string= output "foo\n")
                            (funcall done-service)))))))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'log "foo"))))))

;;;; ready-message

(ert-deftest-async prodigy-start-service-test/ready-message/no-tags (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service
                   :ready-message "Ready!")))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'log "I am Ready!")
         (prodigy-test/delay 0.1
           (lambda ()
             (should (eq (plist-get service :status) 'ready))
             (prodigy-stop-service service nil done))))))))

(ert-deftest-async prodigy-start-service-test/ready-message/with-tags (done)
  (with-sandbox
   (prodigy-define-tag
     :name 'tag1
     :ready-message "Foo")
   (prodigy-define-tag
     :name 'tag2
     :ready-message "Ready!")
   (let ((service (prodigy-test/make-service
                   :tags '(tag1 tag2))))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'log "I am Ready!")
         (prodigy-test/delay 0.1
           (lambda ()
             (should (eq (plist-get service :status) 'ready))
             (prodigy-stop-service service nil done))))))))

(ert-deftest-async prodigy-start-service-test/ready-message/other-message(done)
  (with-sandbox
   (let ((service (prodigy-test/make-service
                   :ready-message "Ready!")))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'log "Something else!")
         (prodigy-test/delay 0.1
           (lambda ()
             (should-not (eq (plist-get service :status) 'ready))
             (prodigy-stop-service service nil done))))))))

;;;; init

(ert-deftest prodigy-start-service-test/init ()
  
  )

;;;; init-async

(ert-deftest-async prodigy-start-service-test/init-async/callbacked (done-init-async done-stop)
  (with-sandbox
   (let ((service
          (prodigy-test/make-service
           :init-async (lambda (done)
                         (funcall done)
                         (funcall done-init-async)))))
     (prodigy-start-service service
       (lambda ()
         (prodigy-stop-service service nil done-stop))))))

(ert-deftest prodigy-init-async-test/not-callbacked ()
  (with-sandbox
   (should-error
    (let ((prodigy-init-async-timeout 1)
          (service
           (prodigy-test/make-service
            :init-async (lambda (done)))))
      (prodigy-start-service service)))))


;;;; prodigy-stop-service

(ert-deftest-async prodigy-stop-service-test/remove-process-and-process-status (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-stop-service service nil
           (lambda ()
             (should-not (plist-get service :process))
             (should-not (plist-get service :process-status))
             (funcall done))))))))

(ert-deftest-async prodigy-stop-service-test/status-failed (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'ignore-signal "SIGINT")
         (prodigy-test/delay 1
           (lambda ()
             (prodigy-stop-service service nil
               (lambda ()
                 (funcall done "should not stop because SIGINT ignored")))
             (prodigy-test/delay 2
               (lambda ()
                 (should (eq (plist-get service :status) 'failed))
                 (prodigy-stop-service service 'force done))))))))))

(ert-deftest-async prodigy-stop-service-test/force-kill (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/post-message service 'ignore-signal "SIGINT")
         (prodigy-test/delay 1
           (lambda ()
             (prodigy-stop-service service 'force
               (lambda ()
                 (funcall done))))))))))

(ert-deftest-async prodigy-stop-service-test/callback-when-stopped (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-stop-service service nil done))))))

(ert-deftest prodigy-stop-service-test/kill-process-buffer-on-stop ()
  )

(ert-deftest-async prodigy-stop-service-test/keep-buffer (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (switch-to-buffer (get-buffer-create "foo"))
         (insert "bar")
         (prodigy-stop-service service nil done)
         (should (string= (buffer-name) "foo"))
         (should (string= (buffer-string) "bar")))))))


;;;; prodigy-restart-service

(ert-deftest-async prodigy-restart-service-test/not-started (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-restart-service service
       (lambda ()
         (prodigy-stop-service service nil done))))))

(ert-deftest-async prodigy-restart-service-test/started (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-restart-service service
           (lambda ()
             (prodigy-stop-service service nil done))))))))


;;;; prodigy-process-filter

(provide 'prodigy-process-handling-test)

;;; prodigy-process-handling-test.el ends here
