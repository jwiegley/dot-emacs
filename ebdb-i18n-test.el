;;; ebdb-i18n-test.el --- Tests for EBDB's internationalization support  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file obviously depends on ebdb-i18n and all region-specific
;; files that come with EBDB, and if you run the tests in an
;; interactive session it will load those files.  If you had EBDB
;; running as a normal user, loading these tests might change EBDB's
;; behavior.

;;; Code:

(require 'ert)
(require 'ebdb-i18n)

;; Basic name parsing.

;; Regular latin names shouldn't be parsed any differently with the
;; i18n files loaded.

(ert-deftest ebdb-i18n-parse-name ()
  (let ((max (ebdb-parse 'ebdb-field-name-complex "Max von Sydow"))
	(brigitte (ebdb-parse 'ebdb-field-name-complex "Brigitte Bardot")))
    (should (string= (ebdb-name-last max) "von Sydow"))
    (should (string= (ebdb-name-last brigitte) "Bardot"))))

(ert-deftest ebdb-i18n-parse-unhandled-name ()
  "Parse a name for which there is no `ebdb-i18n-parse' method
  defined.

This should fall back to the regular `ebdb-parse' method."
  ;; At present there's nothing defined for Arabic, update as
  ;; necessary.  I think this is only a surname, anyhow, I just copied
  ;; something off the internet.
  (let ((arabic-name "عامر"))
    (should (eieio-object-p
	     (ebdb-parse 'ebdb-field-name-complex arabic-name)))))

;; Sanity tests for other fields.
(ert-deftest ebdb-i18n-parse-unhandled-phone ()
  "Parse a phone number for which no `ebdb-i18n-parse' method is
defined."
  ;; There is currently no USA-specific phone parsing method, so this
  ;; should fall back to the default.
  (let ((phone-str "+1 (206) 555-5555"))
    (should (equal (slot-value
		    (ebdb-parse 'ebdb-field-phone phone-str)
		    'area-code)
		   206))))

(provide 'ebdb-i18n-test)
;;; ebdb-i18n-test.el ends here
