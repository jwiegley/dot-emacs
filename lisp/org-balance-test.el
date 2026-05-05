;;; org-balance-test.el --- Tests for org-balance -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley

;;; Commentary:
;;
;; ERT tests for `org-balance'.  Run with:
;;
;;   emacs -batch -L . -l org-balance-test.el -f ert-run-tests-batch-and-exit

;;; Code:

(require 'ert)
(require 'org)
(require 'org-balance)

;;;; Pure functions

(ert-deftest org-balance-test-staleness-nil ()
  "A nil timestamp means never touched, fully stale."
  (should (= 1.0 (org-balance-staleness nil 30))))

(ert-deftest org-balance-test-staleness-zero-days ()
  "A timestamp equal to NOW yields zero staleness."
  (let ((now (current-time)))
    (should (= 0.0 (org-balance-staleness now 30 now)))))

(ert-deftest org-balance-test-staleness-half-life ()
  "At exactly the half-life, staleness is 0.5."
  (let* ((now (current-time))
         (then (time-subtract now (seconds-to-time (* 30 86400.0)))))
    (should (< (abs (- 0.5 (org-balance-staleness then 30 now)))
               1e-6))))

(ert-deftest org-balance-test-staleness-double-half-life ()
  "At twice the half-life, staleness is 0.75."
  (let* ((now (current-time))
         (then (time-subtract now (seconds-to-time (* 60 86400.0)))))
    (should (< (abs (- 0.75 (org-balance-staleness then 30 now)))
               1e-6))))

(ert-deftest org-balance-test-staleness-future ()
  "A future timestamp returns 0 staleness, not negative."
  (let* ((now (current-time))
         (future (time-add now (seconds-to-time (* 5 86400.0)))))
    (should (= 0.0 (org-balance-staleness future 30 now)))))

(ert-deftest org-balance-test-staleness-zero-half-life ()
  "Non-positive half-life returns 0 (avoids division by zero)."
  (should (= 0.0 (org-balance-staleness (current-time) 0))))

(ert-deftest org-balance-test-importance-known ()
  "Known priorities map to their configured factors."
  (let ((org-balance-importance-factors '((?A . 1.5) (?B . 1.0) (?C . 0.7))))
    (should (= 1.5 (org-balance-importance-factor ?A)))
    (should (= 1.0 (org-balance-importance-factor ?B)))
    (should (= 0.7 (org-balance-importance-factor ?C)))))

(ert-deftest org-balance-test-importance-default ()
  "Nil priority falls back to `org-default-priority'."
  (let ((org-balance-importance-factors '((?A . 1.5) (?B . 1.0) (?C . 0.7)))
        (org-default-priority ?B))
    (should (= 1.0 (org-balance-importance-factor nil)))))

(ert-deftest org-balance-test-importance-unknown ()
  "Unknown priority falls back to default-priority's factor."
  (let ((org-balance-importance-factors '((?A . 1.5) (?B . 1.0) (?C . 0.7)))
        (org-default-priority ?B))
    (should (= 1.0 (org-balance-importance-factor ?Z)))))

(ert-deftest org-balance-test-target-factor-equal ()
  "Target == actual yields a factor of 1."
  (let ((org-balance-target-clip '(0.5 . 2.0)))
    (should (= 1.0 (org-balance-target-factor 0.3 0.3)))))

(ert-deftest org-balance-test-target-factor-under-served ()
  "Target > actual yields a factor > 1, clipped to upper."
  (let ((org-balance-target-clip '(0.5 . 2.0)))
    (should (= 2.0 (org-balance-target-factor 0.5 0.1)))
    (should (< (abs (- 1.5 (org-balance-target-factor 0.3 0.2)))
               1e-6))))

(ert-deftest org-balance-test-target-factor-over-served ()
  "Target < actual yields a factor < 1, clipped to lower."
  (let ((org-balance-target-clip '(0.5 . 2.0)))
    (should (= 0.5 (org-balance-target-factor 0.1 0.5)))))

(ert-deftest org-balance-test-target-factor-no-activity ()
  "Zero actual share returns the upper clip — never-touched gets max boost."
  (let ((org-balance-target-clip '(0.5 . 2.0)))
    (should (= 2.0 (org-balance-target-factor 0.3 0)))))

(ert-deftest org-balance-test-target-factor-no-target ()
  "Zero target share returns the lower clip — explicitly-deweighted is damped."
  (let ((org-balance-target-clip '(0.5 . 2.0)))
    (should (= 0.5 (org-balance-target-factor 0 0.3)))))

(ert-deftest org-balance-test-score-combiner ()
  "The score combiner uses the multiplicative formula."
  (let ((org-balance-cat-weight 0.6)
        (org-balance-task-weight 0.4))
    (let ((score (org-balance--score 1.5 1.0 0.5 0.25)))
      ;; 1.5 * 1.0 * (0.6 * 0.5 + 0.4 * 0.25) = 1.5 * 0.4 = 0.6
      (should (< (abs (- 0.6 score)) 1e-6)))))

;;;; Activity collection

(ert-deftest org-balance-test-collect-activity ()
  "Parse LOGBOOK / CLOSED / CLOCK from a temp buffer."
  (with-temp-buffer
    (org-mode)
    (insert "\
* DONE Sample task
CLOSED: [2026-04-15 Wed 10:00]
:LOGBOOK:
- State \"DONE\" from \"DOING\" [2026-04-15 Wed 10:00]
- State \"DOING\" from \"TODO\" [2026-04-10 Mon 09:00]
CLOCK: [2026-04-12 Fri 14:00]--[2026-04-12 Fri 15:00] =>  1:00
:END:
")
    (goto-char (point-min))
    (let ((events (org-balance--collect-activity-at-point)))
      ;; Two state changes + one CLOSED + one CLOCK = 4 events.
      (should (= 4 (length events))))))

(ert-deftest org-balance-test-collect-activity-empty ()
  "An entry with no logged activity returns an empty list."
  (with-temp-buffer
    (org-mode)
    (insert "* TODO Bare task\n")
    (goto-char (point-min))
    (should (null (org-balance--collect-activity-at-point)))))

(ert-deftest org-balance-test-latest ()
  "`org-balance--latest' returns the most recent timestamp."
  (let* ((early (encode-time 0 0 10 1 4 2026))
         (mid   (encode-time 0 0 10 5 4 2026))
         (late  (encode-time 0 0 10 15 4 2026)))
    (should (equal late (org-balance--latest (list early late mid))))
    (should (null (org-balance--latest nil)))))

;;;; Effective target (alist + property aggregation)

(ert-deftest org-balance-test-effective-target-alist-only ()
  "With only the alist, `org-balance--effective-target' returns the alist value."
  (let ((org-balance-category-targets '(("Health" . 5) ("Work" . 3)))
        (org-balance-default-weight 1))
    (should (= 5 (org-balance--effective-target "Health" nil)))
    (should (= 3 (org-balance--effective-target "Work" 0)))
    (should (= 1 (org-balance--effective-target "Other" nil)))))

(ert-deftest org-balance-test-effective-target-with-property ()
  "Property contribution is added to the alist contribution."
  (let ((org-balance-category-targets '(("Health" . 5)))
        (org-balance-default-weight 1))
    (should (= 7 (org-balance--effective-target "Health" 2)))
    (should (= 4 (org-balance--effective-target "Other" 3)))))

(provide 'org-balance-test)
;;; org-balance-test.el ends here
