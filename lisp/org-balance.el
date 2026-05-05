;;; org-balance.el --- LifeBalance-inspired task balancing for Org-mode -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 2026-04-28
;; Version: 0.1.0
;; Package-Requires: ((emacs "27.1") (org "9.5") (org-ql "0.7"))
;; Keywords: org outlines tools agenda
;; URL: https://github.com/jwiegley/dot-emacs

;;; Commentary:

;; A LifeBalance-inspired (Llamagraphics, discontinued) task balancing
;; system for Org-mode.  Produces a custom agenda view that orders tasks so
;; neglected life areas surface to the top of the daily review.
;;
;; Each candidate task receives a numeric score combining:
;;
;;   1. Importance, from the task's [#A]/[#B]/[#C] priority cookie.
;;   2. Per-category staleness: how long since the *category* saw any
;;      activity (state change, completion, or clocking).
;;   3. Per-task staleness: how long since *this task* was last touched.
;;   4. Per-category target weight: a relative target share of attention,
;;      with a feedback factor that boosts under-served categories and
;;      damps over-served ones.
;;
;; The combination is multiplicative:
;;
;;   score = importance_factor
;;         × target_factor
;;         × ( w_cat  * staleness(cat_last)
;;           + w_task * staleness(task_last) )
;;
;; Staleness uses exponential decay with a configurable half-life, so a
;; user-facing "half-life in days" tunable controls how quickly an
;; untouched task / category climbs the rankings.
;;
;; Use `M-x org-balance-agenda' to open the Balanced TODO view, or wire
;; `org-balance-custom-agenda-command' into `org-agenda-custom-commands' to
;; bind it to an agenda dispatcher key.  In the resulting agenda buffer,
;; `M-x org-balance-explain-at-point' (also bound to `e') shows the score
;; breakdown for the task at point.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'org)
(require 'org-agenda)
(require 'org-ql)

(declare-function org-ext-subtask-p "org-ext" ())
(declare-function org-ext-habit-p "org-ext" ())
(declare-function org-is-habit-p "org-habit" (&optional epom))
(declare-function org-ql--normalize-query "org-ql" t t)
(declare-function org-ql-clear-cache "org-ql" ())
(defvar org-config-categories-regularly-reviewed)

;;;; Customization group

(defgroup org-balance nil
  "LifeBalance-inspired task balancing for Org-mode."
  :group 'org
  :prefix "org-balance-")

(defcustom org-balance-category-targets nil
  "Alist mapping CATEGORY (string) to relative target weight (number).
Categories absent from this alist receive `org-balance-default-weight'.
Values are *relative*; they are normalized internally.  This makes
`((\"Health\" . 5) (\"Work\" . 3))' equivalent in effect to
`((\"Health\" . 50) (\"Work\" . 30))'."
  :type '(alist :key-type string :value-type number)
  :group 'org-balance)

(defcustom org-balance-default-weight 1
  "Default relative target weight for categories without a configured target.
Also added to the per-tree `:BALANCE_TARGET:' contribution when no
property is set, so unlisted categories never have zero weight."
  :type 'number
  :group 'org-balance)

(defcustom org-balance-importance-factors
  '((?A . 1.5)
    (?B . 1.0)
    (?C . 0.7))
  "Alist mapping priority character to score multiplier.
Tasks with no priority cookie are treated as having priority
`org-default-priority' (Org's standard, usually `?B')."
  :type '(alist :key-type character :value-type number)
  :group 'org-balance)

(defcustom org-balance-cat-staleness-half-life-days 30
  "Half-life in days for category staleness.
After this many days without category activity, the category-staleness
contribution to the score reaches 0.5; after twice this many, 0.75; and
so on, asymptoting to 1."
  :type 'number
  :group 'org-balance)

(defcustom org-balance-task-staleness-half-life-days 60
  "Half-life in days for individual task staleness.
After this many days without activity on a task, the task-staleness
contribution reaches 0.5."
  :type 'number
  :group 'org-balance)

(defcustom org-balance-activity-window-days 365
  "Look-back window, in days, for computing per-category activity share.
Activity events older than this are ignored when computing
`cat_share' (the recent-activity proportion that drives the target
feedback factor).  Cat-staleness itself uses *all* recorded activity,
not the windowed count."
  :type 'number
  :group 'org-balance)

(defcustom org-balance-cat-weight 0.6
  "Weight on category-staleness in the score combiner.
Should sum with `org-balance-task-weight' to 1.0."
  :type 'number
  :group 'org-balance)

(defcustom org-balance-task-weight 0.4
  "Weight on task-staleness in the score combiner.
Should sum with `org-balance-cat-weight' to 1.0."
  :type 'number
  :group 'org-balance)

(defcustom org-balance-target-clip '(0.5 . 2.0)
  "Lower and upper clip on the target feedback factor.
The factor `(target_share / actual_share)' is clipped to this range so
no single category dominates or vanishes from the ranking."
  :type '(cons number number)
  :group 'org-balance)

(defcustom org-balance-eligible-todo-keywords
  '("TODO" "DOING" "WAIT" "TASK")
  "TODO keywords considered eligible for the Balanced TODO view."
  :type '(repeat string)
  :group 'org-balance)

(defcustom org-balance-excluded-categories nil
  "Categories excluded from the Balanced TODO view.
If nil, falls back to `org-config-categories-regularly-reviewed' when
that variable is bound, otherwise nothing is excluded.  Excluded
categories are also omitted from cat_share denominator and target
normalization."
  :type '(repeat string)
  :group 'org-balance)

(defcustom org-balance-eligibility-predicate
  #'org-balance-default-eligibility-predicate
  "Predicate called with point at a candidate heading.
Returns non-nil iff the entry should be included in the Balanced TODO
view.  Called *after* the org-ql query has filtered by TODO state and
basic exclusions; this hook lets you add custom restrictions."
  :type 'function
  :group 'org-balance)

(defcustom org-balance-max-items nil
  "Maximum number of tasks to show, or nil for unlimited.
Can be overridden with a numeric prefix arg to `org-balance-agenda'."
  :type '(choice (const :tag "Unlimited" nil) integer)
  :group 'org-balance)

(defcustom org-balance-buffer-name "*Org-Balance*"
  "Name of the buffer used to display the Balanced TODO view."
  :type 'string
  :group 'org-balance)

;;;; Internal state

(defvar org-balance--activity-cache nil
  "Per-invocation activity cache.
A plist with keys :cat-last, :cat-counts, :task-last, :total-count.
Populated by `org-balance--prime-activity', cleared by
`org-balance-refresh'.")

;;;; Pure scoring functions

(defun org-balance-staleness (timestamp half-life-days &optional now)
  "Return the staleness of TIMESTAMP, a number in [0, 1].
HALF-LIFE-DAYS controls how fast staleness grows: at HALF-LIFE-DAYS
days since TIMESTAMP, returns 0.5; at twice that, 0.75.

If TIMESTAMP is nil (i.e., never touched), returns 1 (maximally stale).
If TIMESTAMP is in the future or HALF-LIFE-DAYS is non-positive,
returns 0.

NOW, if non-nil, is used as the reference time (a Lisp time value);
otherwise `current-time' is used.  Useful for testing."
  (cond
   ((null timestamp) 1.0)
   ((<= half-life-days 0) 0.0)
   (t
    (let* ((now (or now (current-time)))
           (delta-secs (float-time (time-subtract now timestamp)))
           (delta-days (/ delta-secs 86400.0)))
      (if (<= delta-days 0) 0.0
        (- 1.0 (exp (- (/ (* (log 2) delta-days)
                          half-life-days)))))))))

(defun org-balance-importance-factor (priority-char)
  "Return the importance multiplier for PRIORITY-CHAR.
PRIORITY-CHAR is a character (e.g., `?A') or nil.  Nil falls back to
`org-default-priority'.  Unknown priorities also fall back to the
default."
  (let ((char (or priority-char org-default-priority)))
    (or (alist-get char org-balance-importance-factors)
        (alist-get org-default-priority org-balance-importance-factors)
        1.0)))

(defun org-balance-target-factor (target-share actual-share)
  "Return clipped target feedback factor.
TARGET-SHARE is the category's normalized target weight (sums to 1
across categories).  ACTUAL-SHARE is the category's normalized share
of recent activity (also sums to 1).  When ACTUAL-SHARE is 0, returns
the upper clip — a never-touched category gets the maximum boost."
  (let* ((clip-low  (car org-balance-target-clip))
         (clip-high (cdr org-balance-target-clip)))
    (cond
     ((or (null target-share) (zerop target-share)) clip-low)
     ((or (null actual-share) (zerop actual-share)) clip-high)
     (t (max clip-low
             (min clip-high
                  (/ target-share actual-share)))))))

(defun org-balance--score (importance target-factor cat-stale task-stale)
  "Combine sub-scores into a single number.
IMPORTANCE is the priority multiplier, TARGET-FACTOR the target
feedback, CAT-STALE and TASK-STALE the two staleness values."
  (* importance target-factor
     (+ (* org-balance-cat-weight  cat-stale)
        (* org-balance-task-weight task-stale))))

;;;; Activity collection (point-local)

(defconst org-balance--state-change-re
  (concat
   "^[ \t]*-[ \t]+State[ \t]+\"\\(?:[^\"]*\\)\"[ \t]+"
   "from[ \t]+\"\\(?:[^\"]*\\)\"[ \t]+"
   "\\[\\([^]]+\\)\\]")
  "Regexp for an Org LOGBOOK state-change entry.
Group 1 is the bracketed inactive timestamp.")

(defconst org-balance--clock-re
  "^[ \t]*CLOCK:[ \t]+\\[\\([^]]+\\)\\]"
  "Regexp for an Org CLOCK line.  Group 1 is the start timestamp.")

(defconst org-balance--closed-re
  (concat "^[ \t]*" org-closed-string "[ \t]+\\[\\([^]]+\\)\\]")
  "Regexp for an Org CLOSED line.  Group 1 is the timestamp.")

(defun org-balance--parse-ts (ts-string)
  "Parse Org timestamp TS-STRING into a Lisp time value, or nil."
  (when (and ts-string (stringp ts-string))
    (ignore-errors
      (org-time-string-to-time ts-string))))

(defun org-balance--collect-activity-at-point ()
  "Collect activity timestamps for the entry at point.
Returns a list of Lisp time values for state-change events, the CLOSED
stamp (if any), and CLOCK starts within the entry's body.  The list is
unsorted.  Point is preserved."
  (let (result)
    (save-excursion
      (save-restriction
        (org-back-to-heading t)
        (let ((begin (point))
              (end (save-excursion
                     (outline-next-heading)
                     (point))))
          (narrow-to-region begin end)
          (goto-char (point-min))
          (while (re-search-forward org-balance--state-change-re nil t)
            (when-let ((ts (org-balance--parse-ts (match-string 1))))
              (push ts result)))
          (goto-char (point-min))
          (while (re-search-forward org-balance--clock-re nil t)
            (when-let ((ts (org-balance--parse-ts (match-string 1))))
              (push ts result)))
          (goto-char (point-min))
          (when (re-search-forward org-balance--closed-re nil t)
            (when-let ((ts (org-balance--parse-ts (match-string 1))))
              (push ts result))))))
    result))

(defun org-balance--latest (timestamps)
  "Return the most recent time in TIMESTAMPS, or nil if empty."
  (when timestamps
    (seq-reduce
     (lambda (acc ts)
       (if (or (null acc) (time-less-p acc ts)) ts acc))
     timestamps
     nil)))

;;;; Activity stats (whole-corpus pass)

(defun org-balance--excluded-categories ()
  "Return the list of categories to exclude.
Falls back to `org-config-categories-regularly-reviewed' when
`org-balance-excluded-categories' is nil and the fallback is bound."
  (or org-balance-excluded-categories
      (and (boundp 'org-config-categories-regularly-reviewed)
           org-config-categories-regularly-reviewed)))

(defun org-balance-default-eligibility-predicate ()
  "Default predicate: skip habits, subtasks, and excluded categories.
Called with point at a candidate heading."
  (and (not (and (fboundp 'org-ext-habit-p) (org-ext-habit-p)))
       (not (and (fboundp 'org-is-habit-p) (org-is-habit-p)))
       (not (and (fboundp 'org-ext-subtask-p) (org-ext-subtask-p)))
       (not (member (org-get-category)
                    (org-balance--excluded-categories)))))

(defun org-balance--prime-activity ()
  "Build per-category and per-task activity statistics.
Stores results in `org-balance--activity-cache'.  Idempotent within a
session: a non-nil cache short-circuits."
  (unless org-balance--activity-cache
    (let ((window-cutoff
           (time-subtract (current-time)
                          (seconds-to-time
                           (* 86400 org-balance-activity-window-days))))
          (cat-last   (make-hash-table :test 'equal))
          (cat-counts (make-hash-table :test 'equal))
          (task-last  (make-hash-table :test 'equal))
          (total 0)
          (excluded (org-balance--excluded-categories)))
      (org-ql-select (org-agenda-files)
        '(or (todo) (done))
        :action
        (lambda ()
          (let* ((cat (org-get-category))
                 (id  (org-balance--task-key))
                 (events (org-balance--collect-activity-at-point))
                 (latest (org-balance--latest events)))
            (when (and latest (not (member cat excluded)))
              (let ((prev (gethash cat cat-last)))
                (when (or (null prev) (time-less-p prev latest))
                  (puthash cat latest cat-last))))
            (when latest
              (puthash id latest task-last))
            (unless (member cat excluded)
              (dolist (ev events)
                (when (not (time-less-p ev window-cutoff))
                  (puthash cat (1+ (gethash cat cat-counts 0)) cat-counts)
                  (cl-incf total)))))))
      (setq org-balance--activity-cache
            (list :cat-last cat-last
                  :cat-counts cat-counts
                  :task-last task-last
                  :total-count total)))))

(defun org-balance--task-key ()
  "Return a stable key for the entry at point.
Uses `ID' if present, otherwise file:position."
  (or (org-id-get)
      (format "%s:%d" (or (buffer-file-name) (buffer-name)) (point))))

;;;; Target normalization

(defun org-balance--all-categories ()
  "Return the set of categories observed in cached activity stats."
  (let (result)
    (when org-balance--activity-cache
      (maphash (lambda (k _v) (push k result))
               (plist-get org-balance--activity-cache :cat-counts))
      (maphash (lambda (k _v) (cl-pushnew k result :test #'equal))
               (plist-get org-balance--activity-cache :cat-last)))
    result))

(defun org-balance--effective-target (cat &optional point-target)
  "Effective target weight for CAT, including any inherited tree target.
POINT-TARGET, when non-nil, is the numeric value of the inherited
`:BALANCE_TARGET:' property at the current entry — passed in so that
this function stays pure / testable."
  (let ((alist-w (or (alist-get cat org-balance-category-targets nil nil #'equal)
                     org-balance-default-weight))
        (prop-w  (or point-target 0)))
    (+ alist-w prop-w)))

(defun org-balance--target-share (cat point-target)
  "Compute normalized target share for CAT.
POINT-TARGET is this entry's inherited `:BALANCE_TARGET:' value (or 0).
Normalization is over all categories observed in activity stats; an
unlisted category still contributes `org-balance-default-weight'."
  (let* ((cats (or (org-balance--all-categories) (list cat)))
         (this (org-balance--effective-target cat point-target))
         (total (apply #'+ (mapcar (lambda (c)
                                     (org-balance--effective-target c 0))
                                   cats))))
    (if (zerop total) 0
      (/ (float this) total))))

(defun org-balance--actual-share (cat)
  "Compute normalized recent-activity share for CAT."
  (let* ((counts (plist-get org-balance--activity-cache :cat-counts))
         (total  (plist-get org-balance--activity-cache :total-count))
         (n      (gethash cat counts 0)))
    (if (or (null total) (zerop total)) 0
      (/ (float n) total))))

;;;; Per-task scoring (called with point at a heading)

(defun org-balance--score-current-task ()
  "Compute the balance score for the entry at point.
Returns a plist with :score, :priority, :cat, :cat-stale, :task-stale,
:target-share, :actual-share, :target-factor, :importance-factor,
:cat-last, :task-last."
  (let* ((cat (org-get-category))
         (priority (org-balance--current-priority))
         (events (org-balance--collect-activity-at-point))
         (task-last (org-balance--latest events))
         (cat-last (gethash cat
                            (plist-get org-balance--activity-cache :cat-last)))
         (point-target
          (let ((s (org-entry-get nil "BALANCE_TARGET" t)))
            (and s (ignore-errors (string-to-number s)))))
         (target-share (org-balance--target-share cat point-target))
         (actual-share (org-balance--actual-share cat))
         (cat-stale (org-balance-staleness
                     cat-last org-balance-cat-staleness-half-life-days))
         (task-stale (org-balance-staleness
                      task-last org-balance-task-staleness-half-life-days))
         (imp-factor (org-balance-importance-factor priority))
         (tgt-factor (org-balance-target-factor target-share actual-share))
         (score (org-balance--score imp-factor tgt-factor
                                    cat-stale task-stale)))
    (list :score score
          :priority priority
          :cat cat
          :cat-stale cat-stale
          :task-stale task-stale
          :target-share target-share
          :actual-share actual-share
          :target-factor tgt-factor
          :importance-factor imp-factor
          :cat-last cat-last
          :task-last task-last)))

(defun org-balance--current-priority ()
  "Return priority character of entry at point, or nil."
  (save-excursion
    (org-back-to-heading t)
    (nth 3 (org-heading-components))))

;;;; Building the agenda view

(defun org-balance--candidate-tasks ()
  "Return scored candidate entries.
Each result is a plist with :marker, :heading, :score-info, :line."
  (let ((todo-states org-balance-eligible-todo-keywords)
        (excluded (org-balance--excluded-categories))
        (results nil))
    (org-ql-select (org-agenda-files)
      `(and (todo ,@todo-states)
            (not (scheduled))
            (not (deadline))
            (not (ts-active))
            (not (tags ,(or org-archive-tag "ARCHIVE"))))
      :action
      (lambda ()
        (when (and (not (member (org-get-category) excluded))
                   (funcall org-balance-eligibility-predicate))
          (let* ((info (org-balance--score-current-task))
                 (marker (point-marker))
                 (heading (org-get-heading t t t t)))
            (push (list :marker marker
                        :heading heading
                        :score-info info)
                  results)))))
    (sort results
          (lambda (a b)
            (> (plist-get (plist-get a :score-info) :score)
               (plist-get (plist-get b :score-info) :score))))))

(defun org-balance--format-line (entry)
  "Format ENTRY (a candidate plist) as an agenda line.
Adds `org-balance-score' and `org-marker' text properties so the score
is preserved across sorting and the line behaves like an agenda
entry."
  (let* ((info (plist-get entry :score-info))
         (score (plist-get info :score))
         (cat (plist-get info :cat))
         (heading (plist-get entry :heading))
         (marker (plist-get entry :marker))
         (priority (plist-get info :priority))
         (last-touched
          (or (plist-get info :task-last)
              (plist-get info :cat-last)))
         (last-str (if last-touched
                       (format-time-string "%Y-%m-%d" last-touched)
                     "never"))
         (line (format " %5.2f  %-12s [#%c] %-50s  %s"
                       score
                       (truncate-string-to-width (or cat "") 12 nil ?\s)
                       (or priority org-default-priority)
                       (truncate-string-to-width (or heading "") 50 nil ?\s)
                       last-str)))
    (org-add-props line nil
      'org-marker marker
      'org-hd-marker marker
      'face nil
      'mouse-face 'highlight
      'help-echo (format "Score: %.4f" score)
      'org-balance-score score
      'org-balance-info info
      'type "tagsmatch")))

(defvar org-balance-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map org-agenda-mode-map)
    (define-key map (kbd "g") #'org-balance-agenda-refresh)
    (define-key map (kbd "e") #'org-balance-explain-at-point)
    (define-key map (kbd "?") #'org-balance-explain-at-point)
    map)
  "Keymap for `org-balance-mode'.")

(define-derived-mode org-balance-mode org-agenda-mode "Org-Balance"
  "Agenda-like mode for the Balanced TODO view.
Inherits from `org-agenda-mode' so commands like RET, TAB, t (todo),
and so on continue to work on the listed entries."
  (setq-local org-agenda-redo-command '(org-balance-agenda-refresh)))

;;;###autoload
(defun org-balance-agenda (&optional arg)
  "Display the Balanced TODO agenda view.
With numeric prefix ARG, limit to ARG items.  Without prefix arg, uses
`org-balance-max-items' (nil = unlimited)."
  (interactive "P")
  (let ((limit (cond ((numberp arg) arg)
                     (arg nil)
                     (t org-balance-max-items))))
    (org-balance--prime-activity)
    (let* ((entries (org-balance--candidate-tasks))
           (entries (if (and limit (> (length entries) limit))
                        (seq-take entries limit)
                      entries))
           (lines (mapcar #'org-balance--format-line entries))
           (buf (get-buffer-create org-balance-buffer-name)))
      (with-current-buffer buf
        (let ((inhibit-read-only t))
          (erase-buffer)
          (org-balance-mode)
          (insert (propertize
                   (format "Balanced TODO (%d task%s, target half-lives %d/%dd, window %dd)\n"
                           (length entries)
                           (if (= (length entries) 1) "" "s")
                           org-balance-cat-staleness-half-life-days
                           org-balance-task-staleness-half-life-days
                           org-balance-activity-window-days)
                   'face 'org-agenda-structure))
          (insert (propertize
                   "  Score  Category     Pr Heading                                            Last\n"
                   'face 'org-agenda-structure))
          (dolist (line lines)
            (insert line "\n"))
          (goto-char (point-min))
          (forward-line 2)))
      (pop-to-buffer buf))))

;;;###autoload
(defun org-balance-agenda-refresh ()
  "Refresh activity caches and rebuild the Balanced TODO view."
  (interactive)
  (org-balance-refresh)
  (org-balance-agenda))

;;;###autoload
(defun org-balance-refresh ()
  "Clear the activity cache.  Call after large bulk edits."
  (interactive)
  (setq org-balance--activity-cache nil)
  (when (fboundp 'org-ql-clear-cache)
    (org-ql-clear-cache)))

;;;; Explanation popup

(defun org-balance--format-explanation (info heading)
  "Format INFO (a score-info plist) and HEADING into an explanation string."
  (let* ((score (plist-get info :score))
         (priority (plist-get info :priority))
         (cat (plist-get info :cat))
         (cat-stale (plist-get info :cat-stale))
         (task-stale (plist-get info :task-stale))
         (target-share (plist-get info :target-share))
         (actual-share (plist-get info :actual-share))
         (tgt (plist-get info :target-factor))
         (imp (plist-get info :importance-factor))
         (cat-last (plist-get info :cat-last))
         (task-last (plist-get info :task-last)))
    (format
     "Task:        %s
Category:    %s

Inputs
------
Priority:           [#%c]   importance_factor = %.2f
Task last touched:  %s   staleness = %.3f
Cat  last touched:  %s   staleness = %.3f
Target share:       %.3f
Actual share (%dd): %.3f   target_factor   = %.3f

Combiner
--------
score = importance × target × (w_cat × cat_stale + w_task × task_stale)
      = %.2f × %.3f × (%.2f × %.3f + %.2f × %.3f)
      = %.4f
"
     (or heading "(unknown)")
     (or cat "(no category)")
     (or priority org-default-priority) imp
     (org-balance--describe-time task-last) task-stale
     (org-balance--describe-time cat-last) cat-stale
     target-share
     org-balance-activity-window-days actual-share tgt
     imp tgt
     org-balance-cat-weight cat-stale
     org-balance-task-weight task-stale
     score)))

(defun org-balance--describe-time (ts)
  "Render TS (a Lisp time) as a `YYYY-MM-DD (Nd ago)' string, or `never'."
  (if (null ts)
      "never                "
    (let* ((days (floor (/ (float-time (time-subtract (current-time) ts))
                           86400.0)))
           (date (format-time-string "%Y-%m-%d" ts)))
      (format "%s (%4dd ago)" date days))))

;;;###autoload
(defun org-balance-explain-at-point ()
  "Show a breakdown of the score for the agenda entry at point."
  (interactive)
  (let* ((info (get-text-property (point) 'org-balance-info))
         (marker (get-text-property (point) 'org-marker))
         (heading
          (when (and marker (marker-buffer marker))
            (with-current-buffer (marker-buffer marker)
              (save-excursion
                (goto-char marker)
                (org-get-heading t t t t))))))
    (unless info
      (user-error "No org-balance entry at point"))
    (with-help-window "*org-balance-explain*"
      (princ (org-balance--format-explanation info heading)))))

;;;; Custom agenda command constructor

;;;###autoload
(defun org-balance-custom-agenda-command (&optional key description)
  "Return a `org-agenda-custom-commands' entry for the Balanced TODO view.
KEY defaults to \"b\", DESCRIPTION to \"Balanced TODO\".  Use this to
wire `org-balance-agenda' into the agenda dispatcher:

  (add-to-list \\='org-agenda-custom-commands
               (org-balance-custom-agenda-command))"
  (let ((key (or key "b"))
        (desc (or description "Balanced TODO")))
    (list key desc
          (lambda (&rest _) (org-balance-agenda)))))

(provide 'org-balance)
;;; org-balance.el ends here
