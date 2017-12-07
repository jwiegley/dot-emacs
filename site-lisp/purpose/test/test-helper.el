;;; test-helper --- Test helper for window-purpose -*- lexical-binding: t -*-

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
;; This file contains test helpers for window-purpose.
;; The sandbox part is inspired from https://github.com/tonini/overseer.el/blob/master/test/test-helper.el

;;; Code:

(require 'cl-lib)
(require 'f)

(defvar cpt-path
  (f-parent (f-this-file)))

(defvar window-purpose-test-path
  (f-dirname (f-this-file)))

(defvar window-purpose-root-path
  (f-parent window-purpose-test-path))

(defvar window-purpose-sandbox-path
  (f-expand "sandbox" window-purpose-test-path))

(when (f-exists? window-purpose-sandbox-path)
  (error "Something is already in %s. Check and destroy it yourself" window-purpose-sandbox-path))

(defmacro within-sandbox (&rest body)
  "Evaluate BODY in an empty sandbox directory."
  `(let ((default-directory window-purpose-sandbox-path))
     (when (f-exists? window-purpose-sandbox-path)
       (f-delete default-directory :force))
     (f-mkdir window-purpose-sandbox-path)
     ,@body
     (f-delete default-directory :force)))

(require 'ert)

(set-frame-width nil 80)
(set-frame-height nil 24)

(message "setting undercover")
(condition-case err
    (progn
      (require 'undercover)
      (undercover "*.el"))
  (error (message "error setting undercover: %s" err)))

(message "loading purpose")
(require 'window-purpose)
(require 'window-purpose-x)
(setq purpose-layout-dirs
      '("test/layouts2/"
        "test/layouts1/"))

;; (message "loading other packages")

;; (require 'lv)
;; (require 'helm)
;; (require 'neotree)
;; (require 'popwin)
;; (require 'guide-key)
;; (require 'which-key)

(message "defining helper functions and variables")

;;; `purpose-user-input-filename' and `purpose-insert-user-input' allow emulation of user input
;;; for tests. The emulation is done by setting a file as stdin for the Emacs
;;; process, and inserting the wanted input to the end of file just before
;;; reading from file.
;;; For the emulation to work, Emacs (ert-runner) needs to be run like this:
;;; rm test/user-input.txt && touch test/user-input.txt && cask exec ert-runner < test/user-input.txt
;;; `purpose-input-lines-inserted' keeps track of how many lines were inserted, so we
;;; can prevent ourselves from accidently writing huge amount of input.
(defconst purpose-user-input-filename "test/user-input.txt")
(defvar purpose-input-lines-inserted 0)
(defvar purpose-max-allowed-input-lines 100)
(defun purpose-validate-user-input (line)
  (when (string-match-p "\n" line)
    (error "LINE shouldn't contain any newlines."))
  (unless (< purpose-input-lines-inserted purpose-max-allowed-input-lines)
    (error "Wrote too many input lines already."))
  (setq purpose-input-lines-inserted (1+ purpose-input-lines-inserted)))
(defun purpose-insert-user-input (line)
  (purpose-validate-user-input line)            ; throws error if invalid input
  (message "inserting user input: %s" line)
  (shell-command (format "echo %s >> %s" line purpose-user-input-filename)))


(defvar test-happened nil
  "Variable for use in tests.
Set the value of this variable at the beginning of each test that uses
it.")

(unless (fboundp 'hash-table-keys)
  (defun hash-table-keys (hash-table)
    "Return a list of keys in HASH-TABLE."
    (let (result)
      (maphash #'(lambda (key value)
                   (setq result (append (list key) result)))
               hash-table)
      result))

  (defun hash-table-values (hash-table)
    "Return a list of values in HASH-TABLE."
    (let (result)
      (maphash #'(lambda (key value)
                   (setq result (append (list value) result)))
               hash-table)
      result)))

(defmacro purpose-with-empty-config (&rest body)
  (declare (indent defun) (debug body))
  `(let ((purpose--user-mode-purposes (make-hash-table))
         (purpose--user-name-purposes (make-hash-table :test #'equal))
         (purpose--user-regexp-purposes (make-hash-table :test #'equal))
         (purpose--extended-mode-purposes (make-hash-table))
         (purpose--extended-name-purposes (make-hash-table :test #'equal))
         (purpose--extended-regexp-purposes (make-hash-table :test #'equal))
         (purpose--default-mode-purposes (make-hash-table))
         (purpose--default-name-purposes (make-hash-table :test #'equal))
         (purpose--default-regexp-purposes (make-hash-table :test #'equal))
         (purpose-use-default-configuration t)
         purpose-user-mode-purposes
         purpose-user-name-purposes
         purpose-user-regexp-purposes
         purpose-extended-configuration)
     ,@body))

(defmacro purpose-with-temp-config (modes names regexps &rest body)
  (declare (indent 3) (debug (sexp sexp sexp body)))
  `(purpose-with-empty-config
     (let ((purpose-user-mode-purposes ,modes)
           (purpose-user-name-purposes ,names)
           (purpose-user-regexp-purposes ,regexps))
       (purpose-compile-user-configuration)
       ,@body)))

(defun purpose-kill-buffers-safely (&rest buffers)
  "Safely kill BUFFERS.
Each item in BUFFERS is either a buffer or a buffer's name."
  (let ((kill-buffer-query-functions nil)
        (kill-buffer-hook nil))
    (mapc #'(lambda (buf) (ignore-errors (kill-buffer buf))) buffers)))

(defmacro purpose-call-with-prefix-arg (arg command)
  (declare (indent defun) (debug 0))
  `(let ((current-prefix-arg ,arg))
     (call-interactively ,command)))

(defun purpose-create-buffers (&rest buffer-names)
  "Create buffers according to BUFFER-NAMES."
  (mapcar #'get-buffer-create buffer-names))

(cl-defun purpose-create-buffers-for-test (&key (p0 0) &key (p1 0) &key (p2 0))
  "Create buffers for purposes 'p0, 'p1 and 'p2.
P0, P1 and P2 should be integers denoting how many buffers should be
created for each purpose.
The buffers created have the names \"xxx-p0-0\", \"xxx-p0-1\",
\"xxx-p1-0\", \"xxx-p1-1\", \"xxx-p2-0\", etc."
  (cl-loop for times in (list p0 p1 p2)
           for purpose in '("p0" "p1" "p2")
           do (dotimes (index times)
                (purpose-create-buffers (format "xxx-%s-%s" purpose index)))))

(defun purpose-displayed-buffers (&optional frame)
  "Return a list of buffers displayed in FRAME."
  (mapcar #'window-buffer (window-list frame)))

(defun purpose-displayed-buffer-names (&optional frame)
  (mapcar #'buffer-name (purpose-displayed-buffers frame)))

(defmacro purpose-check-displayed-buffers (buffer-names)
  (declare (indent defun) (debug (&rest stringp)))
  `(should (equal (sort (purpose-displayed-buffer-names) #'string-lessp)
                  (sort ,buffer-names #'string-lessp))))

(defun purpose-test-delete-window-at (display-fn delete-fn)
  (save-window-excursion
    (unwind-protect
        (progn
          (delete-other-windows)
          (let ((window (selected-window)))
            (should (funcall display-fn (get-buffer-create "xxx-test") nil))
            (funcall delete-fn)
            (should (equal (window-list) (list window)))
            (should-error (funcall delete-fn))))
      (purpose-kill-buffers-safely "xxx-test"))))

(defun purpose-test-sort-symbols (symbols)
  "Sorts list of symbols alphabetically according to their names.
This is a destructive function; it reuses SYMBOLS' storage if possible."
  (cl-sort symbols #'string< :key #'symbol-name))

(message "done defining helpers")
;; (provide 'test-helper) ; https://github.com/rejeep/ert-runner.el/issues/38
;;; test-helper.el ends here
