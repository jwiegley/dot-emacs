;;; prodigy-view-test.el --- Prodigy: Tests for the view mode -*- lexical-binding: t; -*-

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

(defmacro with-view-mode (&rest body)
  "Yield BODY in a `prodigy-view-mode' buffer."
  `(with-temp-buffer
     (prodigy-view-mode)
     ,@body))

(ert-deftest prodigy-view-test/major-mode ()
  (with-view-mode
   (should (eq major-mode 'prodigy-view-mode))))

(ert-deftest prodigy-view-test/mode-line ()
  (with-view-mode
   (should (string= mode-name "Prodigy-view"))))

(ert-deftest prodigy-view-test/view-mode ()
  (with-view-mode (should view-mode)))

;; prodigy-view-mode/truncate

(defmacro prodigy-test-truncate
  (test-name service truncate-by-default &rest conditions)
  (declare (indent 3))
  `(ert-deftest-async ,test-name (done)
     (with-sandbox
      (setq prodigy-view-buffer-maximum-size 10
            prodigy-view-truncate-by-default ,truncate-by-default)
      (let ((service ,service))
        (prodigy-start-service service
          (lambda ()
            (prodigy-test/log-lines service 50)
            (prodigy-test/delay 0.5
              (lambda ()
                (prodigy-with-service-process-buffer service
                  (should (s-match "Line 49" (buffer-string)))
                  ,@conditions)
                (prodigy-stop-service service nil done)))))))))

(prodigy-test-truncate prodigy-view-test/truncate/none
    (prodigy-test/make-service) nil
  (should (>= (count-lines (point-min) (point-max)) 50)))

(prodigy-test-truncate prodigy-view-test/truncate/property
    (prodigy-test/make-service :truncate-output 30) nil
  (should (> (count-lines (point-min) (point-max)) 10))
  (should (<= (count-lines (point-min) (point-max)) 30)))

(prodigy-test-truncate prodigy-view-test/truncate/default-with-property
    (prodigy-test/make-service :truncate-output t) nil
  (should (<= (count-lines (point-min) (point-max)) 10)))

(prodigy-test-truncate prodigy-view-test/truncate/default
    (prodigy-test/make-service) t
  (should (<= (count-lines (point-min) (point-max)) 10)))

(ert-deftest-async prodigy-view-test/truncate/tag-inheritance (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service :tags '(foo))))
     (prodigy-define-tag :name 'foo :truncate-output 10)
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/log-lines service 50)
         (prodigy-test/delay 0.5
           (lambda ()
             (prodigy-with-service-process-buffer service
               (should (<= (count-lines (point-min) (point-max)) 10))
               (prodigy-stop-service service nil done)))))))))

(ert-deftest-async prodigy-view-test/tail (done)
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-start-service service
       (lambda ()
         (prodigy-test/log-lines service 20)
         (prodigy-test/delay 0.2
           (lambda ()
             (prodigy-with-service-process-buffer service
               (should (= (point) (point-max)))
               (goto-line 10))
             (prodigy-test/log-lines service 20)
             (prodigy-test/delay 0.2
               (lambda ()
                 (prodigy-with-service-process-buffer service
                   (should (= (line-number-at-pos) 10))
                   (goto-char (point-max)))
                 (prodigy-test/log-lines service 20)
                 (prodigy-test/delay 0.2
                   (lambda ()
                     (prodigy-with-service-process-buffer service
                       (should (= (point) (point-max))))
                     (prodigy-stop-service service nil done))))))))))))

(provide 'prodigy-view-test)

;;; prodigy-view-test.el ends here
