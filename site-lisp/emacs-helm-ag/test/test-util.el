;;; test-util.el --- test helm-ag utility functions

;; Copyright (C) 2014 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>

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

;;; Code:

(require 'ert)
(require 'helm-ag)

(ert-deftest construct-command ()
  "helm-ag--construct--command"
  (let ((helm-ag-base-command "ag --nocolor --nogroup")
        (helm-ag--last-query "pattern"))
    (let ((got (helm-ag--construct-command nil))
          (expected '("ag" "--nocolor" "--nogroup" "pattern")))
      (should (equal got expected)))))

(ert-deftest construct-command-this-file ()
  "helm-ag--construct--command for this file"
  (let ((helm-ag-base-command "ag --nocolor --nogroup")
        (helm-ag--last-query "pattern"))
    (let ((got (helm-ag--construct-command "foo.el"))
          (expected '("ag" "--nocolor" "--nogroup" "pattern" "foo.el")))
      (should (equal got expected)))))

(ert-deftest construct-command-with-options ()
  "helm-ag--construct--command with options"
  (let ((helm-ag-base-command "ag --nocolor --nogroup")
        (helm-ag-command-option "--all-text --hidden -D")
        (helm-ag--last-query "pattern"))
    (let ((got (helm-ag--construct-command nil))
          (expected '("ag" "--nocolor" "--nogroup" "--all-text" "--hidden" "-D"
                      "pattern")))
      (should (equal got expected)))))

(ert-deftest construct-command-with-options-in-input ()
  "helm-ag--construct--command with options in input"
  (let ((helm-ag-base-command "ag --nocolor --nogroup")
        (helm-ag-command-option "--all-text --hidden -D")
        (helm-ag--last-query "-G\\.md$ \"foo bar\""))
    (let ((got (helm-ag--construct-command nil))
          (expected '("ag" "--nocolor" "--nogroup" "--all-text" "--hidden" "-D"
                      "-G\\.md$" "foo bar")))
      (should (equal got expected)))))

(ert-deftest construct-command-with-ignore-patterns ()
  "helm-ag--construct--command with ignore options"
  (let ((helm-ag-base-command "ag --nocolor --nogroup")
        (helm-ag-ignore-patterns '("*.md" "*.el"))
        (helm-ag--last-query "foo"))
    (let ((got (helm-ag--construct-command nil))
          (expected '("ag" "--nocolor" "--nogroup" "--ignore=*.md" "--ignore=*.el" "foo")))
      (should (equal got expected)))))

(ert-deftest construct-do-ag-command ()
  "helm-ag--construct-do-ag-command"
  (let ((helm-ag-base-command "ag --nocolor --nogroup"))
    (let ((got (helm-ag--construct-do-ag-command "somepattern"))
          (expected '("ag" "--nocolor" "--nogroup" "--" "somepattern")))
      (should (equal got expected)))

    (let* ((helm-ag-command-option "--ignore-case --all-text")
           (got (helm-ag--construct-do-ag-command "somepattern"))
           (expected '("ag" "--nocolor" "--nogroup" "--ignore-case" "--all-text"
                       "--" "somepattern")))
      (should (equal got expected)))))

(ert-deftest construct-do-ag-command-with-extra-option ()
  "helm-ag--construct-do-ag-command with extra options"
  (let ((helm-ag-base-command "ag --nocolor --nogroup")
        (helm-ag--extra-options "-G\\.md$"))
    (let ((got (helm-ag--construct-do-ag-command "somepattern"))
          (expected '("ag" "--nocolor" "--nogroup" "-G\\.md$" "--" "somepattern")))
      (should (equal got expected)))))

(ert-deftest validate-regexp-with-valid-regexp ()
  (should (helm-ag--validate-regexp "[a-z]\\([[:word:]]\\)")))

(ert-deftest validate-regexp-with-invalid-regexp ()
  (should-not (helm-ag--validate-regexp "\\(")))

(ert-deftest transform-for-this-file ()
  "helm-ag--candidate-transform-for-this-file"
  (let ((helm-ag--last-query "hoge"))
    (should (helm-ag--candidate-transform-for-this-file "10:hoge"))
    (should-not (helm-ag--candidate-transform-for-this-file ":hoge"))))

(ert-deftest transform-for-files ()
  "helm-ag--candidate-transform-for-files"
  (let ((helm-ag--last-query "hoge"))
    (should (helm-ag--candidate-transform-for-files "10:5:hoge"))
    (should-not (helm-ag--candidate-transform-for-files "10:hoge"))))

;;; test-util.el ends here
