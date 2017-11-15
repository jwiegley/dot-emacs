;;; prodigy-steps.el --- Prodigy: Ecukes step definitions -*- lexical-binding: t; -*-

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

(Given "^I start prodigy$"
  (lambda ()
    (call-interactively 'prodigy)))

(Given "^I am in a log buffer with output$"
  (lambda ()
    (switch-to-buffer (get-buffer-create "*log output*"))
    (insert "foo bar baz")
    (prodigy-view-mode)))

(Then "^I should be in prodigy mode$"
  (lambda ()
    (should (equal major-mode 'prodigy-mode))
    (should (equal mode-name "Prodigy"))))

(Then "^the buffer should be read only$"
  (lambda ()
    (should buffer-read-only)))

(Then "^the variable \"\\([^\"]+\\)\" should be undefined$"
  (lambda (variable-name)
    (should-not (boundp (intern variable-name)))))

(Then "^the variable \"\\([^\"]+\\)\" should have value \"\\([^\"]+\\)\"$"
  (lambda (variable-name value)
    (should (equal (eval (intern variable-name)) value))))

(Then "^I should not be in prodigy mode$"
  (lambda ()
    (should-not (equal major-mode 'prodigy-mode))))

(Given "^I add the following services:$"
  (lambda (table)
    (let ((head (car table))
          (rows (cdr table)))
      (let ((name-index (-elem-index "name" head))
            (cwd-index (-elem-index "cwd" head))
            (tags-index (-elem-index "tags" head))
            (status-index (-elem-index "status" head)))
        (mapc
         (lambda (row)
           (let ((service (list :name (nth name-index row))))
             (-when-let (tags (and tags-index (read (nth tags-index row))))
               (plist-put service :tags tags))
             (-when-let (cwd (and cwd-index (nth cwd-index row)))
               (plist-put service :cwd cwd))
             (-when-let (status (and status-index (read (nth status-index row))))
               (plist-put service :status status))
             (apply 'prodigy-define-service service)))
         rows)))))

(Then "^I should see services:$"
  (lambda (table)
    (save-excursion
      (let* ((overlays (overlays-in (line-beginning-position) (line-end-position)))
             (highlighted-line
              (and
               (eq 'hl-line (car (--map (overlay-get it 'face) overlays)))
               (line-number-at-pos)))
             (head (car table))
             (rows (cdr table))
             (name-index (-elem-index "name" head))
             (marked-index (-elem-index "marked" head))
             (highlighted-index (-elem-index "highlighted" head))
             (started-index (-elem-index "started" head))
             (tags-index (-elem-index "tags" head)))
        (goto-char (point-min))
        (-each
         rows
         (lambda (row)
           (let* ((expected-name        (and name-index (nth name-index row)))
                  (expected-marked      (and marked-index (read (nth marked-index row))))
                  (expected-highlighted (and highlighted-index (read (nth highlighted-index row))))
                  (expected-started     (and started-index (read (nth started-index row))))
                  (expected-tags        (and tags-index (read (nth tags-index row))))
                  (entry (tabulated-list-get-entry))
                  (actual-name (aref entry 1))
                  (actual-marked (aref entry 0))
                  (actual-started (aref entry 2))
                  (actual-tags
                   (-map 'intern (s-split ", " (aref entry 3) 'omit-nulls))))
             (when expected-name
               (should (string= expected-name actual-name)))
             (when expected-marked
               (should (string= "*" actual-marked)))
             (when expected-highlighted
               (should (= (line-number-at-pos) highlighted-line)))
             (when expected-started
               (should actual-started))
             (when expected-tags
               (should (equal expected-tags actual-tags))))
           (forward-line 1)))))))

(When "^I kill the prodigy buffer$"
  (lambda ()
    (kill-buffer prodigy-buffer-name)))

(When "^I filter by tag \"\\([^\"]+\\)\"$"
  (lambda (tag)
    (When "I start an action chain")
    (And "I press \"f\"")
    (And "I press \"t\"")
    (And "I type \"%s\"" tag)
    (And "I press \"RET\"")
    (And "I execute the action chain")))

(When "^I filter by name \"\\([^\"]+\\)\"$"
  (lambda (name)
    (When "I start an action chain")
    (And "I press \"f\"")
    (And "I press \"n\"")
    (And "I type \"%s\"" name)
    (And "I press \"RET\"")
    (And "I execute the action chain")))

(Then "^I should see services no services$"
  (lambda ()
    (should (string= (buffer-string) ""))))

(Then "^I should be on line \"\\([^\"]+\\)\"$"
  (lambda (line)
    (should (= (line-number-at-pos) (read line)))))

(Then "^I should be in magit status mode$"
  (lambda ()
    (should (eq major-mode 'magit-status-mode))))

(Then "^I should be in dired mode$"
  (lambda ()
    (should (eq major-mode 'dired-mode))))

(Then "^default directory should be \"\\([^\"]+\\)\"$"
  (lambda (dir)
    (should (string= dir default-directory))))

(provide 'prodigy-steps)

;;; prodigy-steps.el ends here
