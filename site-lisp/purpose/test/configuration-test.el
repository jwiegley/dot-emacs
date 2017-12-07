;;; configuration-test.el --- Tests for window-purpose-configuration.el -*- lexical-binding: t -*-

;; Copyright (C) 2015, 2016 Bar Magal

;; Author: Bar Magal
;; Package: purpose

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
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
;; This file contains tests for window-purpose-configuration.el

;;; Code:

(ert-deftest purpose-test-compile-user-config ()
  "Test compilation of user configuration.
This tests that `purpose-compile-user-configuration' creates the correct
hash tables for the uncompiled alists."
  (purpose-with-empty-config
    (let
        ((purpose-user-mode-purposes '((prog-mode . edit)
                                       (dired-mode . dired)))
         (purpose-user-name-purposes '(("editor" . edit)
                                       ("foo" . bar)))
         (purpose-user-regexp-purposes '(("^\\*" . common))))
      (purpose-compile-user-configuration)
      (should (equal (hash-table-keys purpose--user-mode-purposes) '(dired-mode prog-mode)))
      (should (equal (hash-table-values purpose--user-mode-purposes) '(dired edit)))
      (should (equal (hash-table-keys purpose--user-name-purposes) '("foo" "editor")))
      (should (equal (hash-table-values purpose--user-name-purposes) '(bar edit)))
      (should (equal (hash-table-keys purpose--user-regexp-purposes) '("^\\*")))
      (should (equal (hash-table-values purpose--user-regexp-purposes) '(common))))
    (let (purpose-user-mode-purposes
          purpose-user-name-purposes
          purpose-user-regexp-purposes)
      (purpose-compile-user-configuration)
      (should (equal (hash-table-count purpose--user-mode-purposes) 0))
      (should (equal (hash-table-count purpose--user-name-purposes) 0))
      (should (equal (hash-table-count purpose--user-regexp-purposes) 0)))))


(ert-deftest purpose-test-compile-ext-config ()
  "Test compilation of extended configuration.
This tests that `purpose-compile-extended-configuration' creates the
correct hash tables for the uncompiled alists."
  (purpose-with-empty-config
    (let
        ((purpose-extended-conf
          (purpose-conf "test"
                        :mode-purposes '((prog-mode . edit)
                                         (dired-mode . dired))
                        :name-purposes '(("editor" . edit)
                                         ("foo" . bar))
                        :regexp-purposes '(("^\\*" . common)))))
      (purpose-set-extension-configuration :test purpose-extended-conf)
      (should (equal (hash-table-keys purpose--extended-mode-purposes) '(dired-mode prog-mode)))
      (should (equal (hash-table-values purpose--extended-mode-purposes) '(dired edit)))
      (should (equal (hash-table-keys purpose--extended-name-purposes) '("foo" "editor")))
      (should (equal (hash-table-values purpose--extended-name-purposes) '(bar edit)))
      (should (equal (hash-table-keys purpose--extended-regexp-purposes) '("^\\*")))
      (should (equal (hash-table-values purpose--extended-regexp-purposes) '(common))))
    (let (purpose-extended-configuration)
      (purpose-compile-extended-configuration)
      (should (equal (hash-table-count purpose--extended-mode-purposes) 0))
      (should (equal (hash-table-count purpose--extended-name-purposes) 0))
      (should (equal (hash-table-count purpose--extended-regexp-purposes) 0)))))


(ert-deftest purpose-test-compile-default-config ()
  "Test compilation of default configuration.
This tests that `purpose-compile-default-configuration' creates the
correct hash tables."
  (purpose-with-empty-config
    (purpose-compile-default-configuration)
    (should (equal (hash-table-keys purpose--default-mode-purposes)
                   '(package-menu-mode
                     image-mode
                     compilation-mode
                     grep-mode
                     occur-mode
                     Buffer-menu-mode
                     ibuffer-mode
                     dired-mode
                     term-mode
                     eshell-mode
                     comint-mode
                     css-mode
                     text-mode
                     prog-mode)))
    (should (equal (hash-table-values purpose--default-mode-purposes)
                   '(package
                     image
                     search
                     search
                     search
                     buffers
                     buffers
                     dired
                     terminal
                     terminal
                     terminal
                     edit
                     edit
                     edit)))
    (should (equal (hash-table-keys purpose--default-name-purposes)
                   '("*shell*" ".hgignore" ".gitignore")))
    (should (equal (hash-table-values purpose--default-name-purposes)
                   '(terminal edit edit)))
    (should (equal (hash-table-keys purpose--default-regexp-purposes)
                   '("^ \\*Minibuf-[0-9]*\\*$")))
    (should (equal (hash-table-values purpose--default-regexp-purposes)
                   '(minibuf)))))

(ert-deftest purpose-test-set-ext-conf-error ()
  "Test error cases for settings/deleting extension configuration.
See `purpose-set-extension-configuration' and
`purpose-del-extension-configuration'."
  (purpose-with-empty-config
    (should-error (purpose-set-extension-configuration 'foo (purpose-conf "foo")))
    (purpose-set-extension-configuration :foo (purpose-conf "foo"))
    (should-error (purpose-del-extension-configuration 'foo))
    (purpose-del-extension-configuration :foo)))

(ert-deftest purpose-test-temp-config-1 ()
  "Test macros for changing the purpose configuration temporarily.
This one tests `purpose-with-temp-purposes'."
  (let ((original-purposes (purpose-test-sort-symbols (purpose-get-all-purposes))))
    (purpose-with-temp-purposes
        '(("foo" . foo)) '((".*\\.c" . c)) '((python-mode . py))
      (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                     '(c foo general py))))
    (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                   original-purposes))))

(ert-deftest purpose-test-temp-config-2 ()
  "Test macros for changing the purpose configuration temporarily.
This one tests `purpose-with-empty-purposes'."
  (let ((original-purposes (purpose-test-sort-symbols (purpose-get-all-purposes))))
    (purpose-with-empty-purposes
      (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                     '(general))))
    (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                   original-purposes))))

(ert-deftest purpose-test-temp-config-3 ()
  "Test macros for changing the purpose configuration temporarily.
This one tests `purpose-with-additional-purposes'."
  (let ((original-purposes (purpose-test-sort-symbols (purpose-get-all-purposes))))
    (purpose-with-additional-purposes
        '(("foo" . foo)) '((".*\\.c" . c)) '((python-mode . py))
      (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                     (purpose-test-sort-symbols
                      (delete-dups (append original-purposes '(c foo py)))))))
    (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                   original-purposes))))

(ert-deftest purpose-test-ext-convenience ()
  "Test convenience funcions for changing extension purposese."
  (purpose-with-empty-purposes
    (message "Testing add/remove extension configuration with non-existent extension ...")
    (should-error (purpose-add-extension-configuration :none '((org-mode . org))))
    (should-error (purpose-remove-extension-purposes :none '((org-mode . org))))

    (message "Testing purpose-set-extension-configuration ...")
    (purpose-set-extension-configuration
     :python
     (purpose-conf "py"
                   :mode-purposes '((python-mode . python)
                                    (inferior-python-mode . interpreter))))
    (should (equal (hash-table-keys purpose--extended-mode-purposes) '(inferior-python-mode python-mode)))
    (should (equal (hash-table-values purpose--extended-mode-purposes) '(interpreter python)))
    (should (equal (hash-table-keys purpose--extended-name-purposes) nil))
    (should (equal (hash-table-values purpose--extended-name-purposes) nil))
    (should (equal (hash-table-keys purpose--extended-regexp-purposes) nil))
    (should (equal (hash-table-values purpose--extended-regexp-purposes) nil))

    (message "Testing purpose-add-extension-purposes with malformed arguments ...")
    (should-error (purpose-add-extension-purposes :python :modes '((1 . python2))))
    (should-error (purpose-add-extension-purposes :python :names '((1 . python2))))
    (should-error (purpose-add-extension-purposes :python :regexps '((1 . python2))))

    (message "Testing purpose-add-extension-purposes ...")
    (purpose-add-extension-purposes :python
                                    :regexps '(("\\.hy$" . python)))
    (should (equal (hash-table-keys purpose--extended-mode-purposes) '(inferior-python-mode python-mode)))
    (should (equal (hash-table-values purpose--extended-mode-purposes) '(interpreter python)))
    (should (equal (hash-table-keys purpose--extended-name-purposes) nil))
    (should (equal (hash-table-values purpose--extended-name-purposes) nil))
    (should (equal (hash-table-keys purpose--extended-regexp-purposes) '("\\.hy$")))
    (should (equal (hash-table-values purpose--extended-regexp-purposes) '(python)))

    (message "Testing purpose-remove-extension-purposes ...")
    (purpose-remove-extension-purposes :python
                                       :modes '(inferior-python-mode)
                                       :regexps '("\\.hy$"))
    (should (equal (hash-table-keys purpose--extended-mode-purposes) '(python-mode)))
    (should (equal (hash-table-values purpose--extended-mode-purposes) '(python)))
    (should (equal (hash-table-keys purpose--extended-name-purposes) nil))
    (should (equal (hash-table-values purpose--extended-name-purposes) nil))
    (should (equal (hash-table-keys purpose--extended-regexp-purposes) nil))
    (should (equal (hash-table-values purpose--extended-regexp-purposes) nil))))

(ert-deftest purpose-test-user-convenience ()
  "Test `purpose-add-user-purposes' and `purpose-remove-user-purposes'."
  (let ((original-purposes (purpose-test-sort-symbols (purpose-get-all-purposes))))
    "Testing purpose-add-user-purposes ..."
    (purpose-add-user-purposes :modes '((org-mode . org)
                                        (help-mode . popup))
                               :names '(("*scratch*" . scratch))
                               :regexps '(("^\\*foo" . foo)))
    (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                   (purpose-test-sort-symbols
                    (delete-dups (append original-purposes '(org popup scratch foo))))))
    "Testing purpose-remove-user-purposes ..."
    (purpose-remove-user-purposes :modes '(org-mode help-mode)
                                  :names '("*scratch*")
                                  :regexps '("^\\*foo"))
    (should (equal (purpose-test-sort-symbols (purpose-get-all-purposes))
                   original-purposes))))

(provide 'configuration-test)

;;; configuration-test.el ends here
