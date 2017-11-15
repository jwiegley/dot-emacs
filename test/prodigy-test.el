;;; prodigy-api.el --- Prodigy: Misc tests -*- lexical-binding: t; -*-

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


;;;; prodigy-url

(ert-deftest prodigy-url-test/with-url ()
  (let ((url "http://localhost:1234/secret.html"))
    (should (string= (prodigy-url (prodigy-test/make-service :url url)) url))))

(ert-deftest prodigy-url-test/no-url-with-port ()
  (let ((url "http://localhost:6001"))
    (with-mock
     (stub prodigy-service-port => 6001)
     (should (string= (prodigy-url (prodigy-test/make-service)) url)))))

(ert-deftest prodigy-url-test/no-url-no-port ()
  (with-mock
   (stub prodigy-service-port)
   (should-not (prodigy-url (prodigy-test/make-service)))))

(ert-deftest prodigy-url-test/inherit-from-tag ()
  (let ((prodigy-tags '((:name foo :url "http://localhost:3000")))
        (service '(:tags (foo))))
    (should (equal (prodigy-url service) "http://localhost:3000"))))

(ert-deftest prodigy-url-test/override-from-tag ()
  (let ((prodigy-tags '((:name foo :url "http://localhost:3000")))
        (service '(:tags (foo) :url "http://localhost:3001")))
    (should (equal (prodigy-url service) "http://localhost:3001"))))


;;;; prodigy-browse

(ert-deftest prodigy-browse-test/no-url ()
  (with-mock
   (stub prodigy-service-at-pos)
   (stub message)
   (not-called browse-url)
   (prodigy-browse)))

(ert-deftest prodigy-browse-test/single-url ()
  (with-mock
   (stub prodigy-service-at-pos => '(:url "http://localhost:3000"))
   (mock (browse-url "http://localhost:3000"))
   (prodigy-browse)))

(ert-deftest prodigy-browse-test/multiple-url ()
  (with-mock
   (stub prodigy-service-at-pos => '(:url ("http://localhost:3000"
                                           "http://localhost:3000/foo")))
   (stub prodigy-completing-read => "http://localhost:3000/foo")
   (mock (browse-url "http://localhost:3000/foo"))
   (prodigy-browse)))

(provide 'prodigy-api)

;;; prodigy-api.el ends here
