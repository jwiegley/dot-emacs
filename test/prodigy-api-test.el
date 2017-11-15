;;; prodigy-api-test.el --- Prodigy: Tests for the public API -*- lexical-binding: t; -*-

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


;;;; prodigy-add-filter

(ert-deftest prodigy-add-filter-test ()
  (prodigy-add-filter :tag 'tag)
  (prodigy-add-filter :name "name")
  (should (equal prodigy-filters '((:name "name")
                                   (:tag tag)))))


;;;; prodigy-define-service

(ert-deftest prodigy-define-service-test/new-service ()
  (prodigy-define-service
    :name "name"
    :command "foo"
    :cwd "/path/to/name")
  (should (equal prodigy-services '((:name "name" :command "foo" :cwd "/path/to/name")))))

(ert-deftest prodigy-define-service-test/override-service-by-name ()
  (prodigy-define-service
    :name "name"
    :command "foo"
    :cwd "/path/to/name")
  (prodigy-define-service
    :name "name"
    :command "bar"
    :cwd "/path/to/name")
  (should (equal prodigy-services '((:name "name" :command "bar" :cwd "/path/to/name")))))

(ert-deftest prodigy-define-service-test/preserve-process ()
  (prodigy-define-service :name "name" :process "process")
  (prodigy-define-service :name "name")
  (should (equal prodigy-services '((:name "name" :process "process")))))


;;;; prodigy-define-tag

(ert-deftest prodigy-define-tag-test/new-tag ()
  (prodigy-define-tag
    :name "name"
    :command "foo"
    :cwd "/path/to/name")
  (should (equal prodigy-tags '((:name "name" :command "foo" :cwd "/path/to/name")))))

(ert-deftest prodigy-define-tag-test/override-tag-by-name ()
  (prodigy-define-tag
    :name "name"
    :command "foo"
    :cwd "/path/to/name")
  (prodigy-define-tag
    :name "name"
    :command "bar"
    :cwd "/path/to/name")
  (should (equal prodigy-tags '((:name "name" :command "bar" :cwd "/path/to/name")))))


;;;; prodigy-define-status

(ert-deftest prodigy-define-status-test/new-status ()
  (with-sandbox
   (let (prodigy-status-list)
     (prodigy-define-status
       :id 'foo
       :name "Foo"
       :face 'foo-face)
     (let ((status '((:id foo :name "Foo" :face foo-face))))
       (should (equal prodigy-status-list status))))))

(ert-deftest prodigy-define-status-test/override-tag-by-name ()
  (with-sandbox
   (let (prodigy-status-list)
     (prodigy-define-status
       :id 'foo
       :name "Foo"
       :face 'foo-face)
     (prodigy-define-status
       :id 'foo
       :name "Bar"
       :face 'foo-face)
     (let ((status '((:id foo :name "Bar" :face foo-face))))
       (should (equal prodigy-status-list status))))))


;;;; prodigy-set-status

(ert-deftest prodigy-set-status-test/status-defined ()
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (prodigy-define-status :id 'waiting)
     (prodigy-set-status service 'waiting)
     (should (eq (plist-get service :status) 'waiting)))))

(ert-deftest prodigy-set-status-test/status-not-defined ()
  (with-sandbox
   (let ((service (prodigy-test/make-service)))
     (should-error (prodigy-set-status service 'waiting)))))


;;;; prodigy-callback

(ert-deftest prodigy-callback-test ()
  (apply
   (prodigy-callback (foo baz)
     (should (string= foo "bar"))
     (should (string= baz "qux")))
   (list :foo "bar" :baz "qux")))

(provide 'prodigy-api-test)

;;; prodigy-api-test.el ends here
