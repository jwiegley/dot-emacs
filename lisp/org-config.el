;;; org-config --- Configurations for Org-mode and related packages

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 1 Jul 2024
;; Version: 1.0
;; Keywords: org capture task todo context
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

(defgroup org-config nil
  "Configurations for Org-mode and related packages"
  :group 'org)

(defconst org-config-open-re "TODO={TODO\\|DOING\\|WAIT\\|TASK}")
(defconst org-config-closed-re "TODO={DONE\\|CANCELED\\|COMPLETE\\|ABORTED}")

(defun org-config-with-tags-search (tags)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive "sTags: ")
  (org-tags-view t (format "%s&%s" tags org-config-open-re)))

(defun org-config-with-tags-search-done (tags)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive "sTags: ")
  (org-tags-view t (format "%s&%s" tags org-config-closed-re)))

(defun org-config-with-category-search (who)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive
   (list (completing-read "Category: " (org-property-values "CATEGORY"))))
  (org-tags-view t (format "CATEGORY=\"%s\"&%s" who org-config-open-re)))

(defun org-config-with-item-search (who)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive "sItem: ")
  (org-tags-view t (format "ITEM={%s}&%s" who org-config-open-re)))

(eval-when-compile
  (require 'org-habit))

(defmacro org-config-agenda-skip-entry-if (body)
  "Skip all but the first non-done entry."
  `(when ,body
     (org-with-wide-buffer
      (or (outline-next-heading)
          (goto-char (point-max))))))

(defsubst org-config-agenda-skip-habit ()
  (org-config-agenda-skip-entry-if
   (org-is-habit-p)))

(defsubst org-config-skip-if-review-not-needed ()
  (org-config-agenda-skip-entry-if
   (and (org-review-last-review-prop nil)
        (not (org-review-toreview-p)))))

(defsubst org-config-skip-if-reviewed ()
  (org-config-agenda-skip-entry-if
   (org-review-last-review-prop nil)))

(defun org-config-agenda-skip-all-siblings-but-first
    (&optional include-non-projects include-low-prio-projects)
  "Skip all but the first non-done entry."
  (org-config-agenda-skip-entry-if
   (let (should-skip-entry)
     (unless (member (org-get-todo-state) '("TODO" "DOING"))
       (setq should-skip-entry t))
     (when (/= (point)
               (save-excursion
                 (org-goto-first-child)
                 (point)))
       (setq should-skip-entry t))
     (save-excursion
       (while (and (not should-skip-entry) (org-goto-sibling t))
         (when (org-entry-is-todo-p)
           (setq should-skip-entry t))))
     (unless (or should-skip-entry include-non-projects)
       (unless (and (string= "PROJECT" (org-extra-parent-keyword))
                    (or include-low-prio-projects
                        (> (org-extra-parent-priority) 0)))
         (setq should-skip-entry t)))
     should-skip-entry)))

(defun org-config-agenda-skip-entry-if-not-within (days)
  "Skip entry if it wasn't created within the given number of DAYS."
  (ignore-errors
    (let ((subtree-end (save-excursion (org-end-of-subtree t)))
          (day
           (time-to-days
            (org-time-string-to-time
             (org-entry-get nil "CREATED"))))
          (now (time-to-days (current-time))))
      (and day
           (> (- now day) days)
           subtree-end))))

(defun org-config-agenda-skip-entry-if-within (days)
  "Skip entry if it wasn't created within the given number of DAYS."
  (ignore-errors
    (let ((subtree-end (save-excursion (org-end-of-subtree t)))
          (day
           (time-to-days
            (org-time-string-to-time
             (org-entry-get nil "CREATED"))))
          (now (time-to-days (current-time))))
      (and day
           (<= (- now day) days)
           subtree-end))))

(setq
 org-capture-templates
 (let ((Inbox '(function org-extra-goto-inbox-heading)))
   `(("a" "TODO" entry
      ,Inbox
      "* TODO %?"
      :prepend t)

     ("A" "TODO (here)" entry
      (function org-extra-up-heading)
      "* TODO %?"
      :prepend t)

     ("h" "Habit" entry
      (file+headline ,(org-file "habits.org") "Personal")
      "* TODO %?
:PROPERTIES:
:STYLE:    habit
:REPEAT_TO_STATE: TODO
:LOG_INTO_DRAWER: t
:END:"
      :prepend t)

     ("n" "NOTE" entry
      ,Inbox
      "* NOTE %?"
      :prepend t)

     ("N" "NOTE (here)" entry
      (function org-extra-up-heading)
      "* NOTE %?"
      :prepend t)

     ("l" "Link" entry
      ,Inbox
      "* LINK %:description%?
:PROPERTIES:
:URL:      %:link
:END:"
      :prepend t)

     ("c" "Checklist" entry
      ,Inbox
      "* TODO %? [/]
- [ ] $0
:PROPERTIES:
:COOKIE_DATA: recursive
:RESET_CHECK_BOXES: t
:END:"
      :prepend t)

     ("C" "Category" entry
      (function org-extra-up-heading)
      "* %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
      :prepend t)

     ("m" "Meetings")

     ("mg" "Copper to Gold" entry
      (file+headline ,(org-file "todo.org") "Copper to Gold")
      "* TODO %?\nSCHEDULED: %t"
      :prepend t
      :clock-in t
      :clock-keep t)

     ("mA" "Ali Nakhjavani Development Fund" entry
      (file+headline ,(org-file "todo.org")
                     "Ali Nakhjavani Development Fund (ANDF)")
      "* TODO %?\nSCHEDULED: %t"
      :prepend t
      :clock-in t
      :clock-keep t)

     ("mq" "Quantum Trades" entry
      (file+headline ,(org-file "todo.org") "Quantum Trades")
      "* TODO %?\nSCHEDULED: %t"
      :prepend t
      :clock-in t
      :clock-keep t)

     ("B" "Org-contact" entry
      (file ,(org-file "people.org"))
      "* %^{NAME}
:PROPERTIES:
:PHONE:    %^{PHONE}
:EMAIL:    %^{EMAIL}
:END:"
      :prepend t)

     ("P" "PROJECT (here)" entry
      (function org-extra-up-heading)
      "* PROJECT %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
      :prepend t)

     ("p" "Project templates")

     ("pp" "PROJECT" entry
      ,Inbox
      "* PROJECT %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
      :prepend t)

     ("pt" "Trip" entry
      ,Inbox
      (file "~/doc/template/org/trip.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pT" "Taxes" entry
      (file+headline ,(org-file "todo.org") "Taxes")
      (file "~/doc/template/org/taxes.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pb" "Bahá’í templates")

     ("pba" "Assembly meeting" entry
      (file+headline ,(org-file "assembly/assembly.org")
                     "Carmichael Local Spiritual Assembly (LSA)")
      (file "~/doc/template/org/bahai/assembly-meeting.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbf" "Bahá’í Feast" entry
      (file+headline ,(org-file "assembly/assembly.org")
                     "Carmichael Local Spiritual Assembly (LSA)")
      (file "~/doc/template/org/bahai/feast.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbe" "Bahá’í event" entry
      ;; I don't know in advance which section it belongs in.
      ,Inbox
      (file "~/doc/template/org/bahai/bahai-event.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbE" "Recurring Bahá’í event" entry
      ;; I don't know in advance which section it belongs in.
      ,Inbox
      (file "~/doc/template/org/bahai/recurring-event.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbg" "Flow of guidance" entry
      (file+headline ,(org-file "assembly/assembly.org")
                     "Increasing the flow of guidance to the grassroots")
      (file "~/doc/template/org/bahai/flow-of-guidance.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbp" "Program (such as community devotional)" entry
      ;; I don't know in advance which section it belongs in.
      ,Inbox
      (file "~/doc/template/org/bahai/program.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pw" "Work templates")

     ("pwo" "Offsite Meeting" entry
      (file+headline ,(org-file "kadena/kadena.org") "Leadership")
      (file "~/doc/template/org/kadena/offsite-meeting.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwc" "Work Conference" entry
      (file+headline ,(org-file "kadena/kadena.org") "Conferences")
      (file "~/doc/template/org/kadena/conference.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwO" "Out of Office" entry
      (file+headline ,(org-file "kadena/kadena.org") "Operations (Ops)")
      (file "~/doc/template/org/kadena/out-of-office.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwn" "Network Incident" entry
      (file+headline ,(org-file "kadena/kadena.org") "Improve Response Process")
      (file "~/doc/template/org/kadena/network-incident.org")
      :immediate-finish t
      :jump-to-captured t)))

 org-roam-capture-templates
 `(("m" "Meeting notes" plain
    (file "~/doc/template/org/meeting.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-meeting.org"
     "#+category: Meeting\n#+date: %(setq my/org-start-date (my/org-read-date t))\n#+title: Meeting: %^{Purpose of meeting}\n")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("n" "Note" plain "%?"
    :target (file+head "%<%Y%m%d%H%M>.org"
                       "#+category: Note\n#+title: ${title}\n")
    :immediate-finish t
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("o" "One-on-one notes" plain
    (file "~/doc/template/org/kadena/one-on-one.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-1-on-1.org"
     "#+category: 1-on-1\n#+date: %(setq my/org-start-date (my/org-read-date t))\n#+title: 1-on-1: %^{Person meeting with}\n")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("q" "Quote" plain "%c\n\n─ %?"
    :target (file+head "%<%Y%m%d%H%M>.org"
                       "#+filetags: :quote:\n#+title: ${title}\n")
    :jump-to-captured t
    :empty-lines-before 1)

   ("w" "Work" plain "%?"
    :target (file+head "kadena/%<%Y%m%d%H%M>.org"
                       "#+filetags: :kadena:\n#+title: ${title}\n")
    :immediate-finish t
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("b" "Blog")

   ("bj" "johnwiegley.com" plain "%?"
    :jump-to-captured t
    :target (file+head "johnwiegley/%<%Y%m%d%H%M>.org"
                       ":PROPERTIES:
:SLUG:     ${slug}
:PUBLISH:  %^{Publish after date}U
:END:
#+date: %U
#+filetags: :publish/johnwiegley:
#+title: ${title}\n")
    :immediate-finish t
    :empty-lines-before 1
    :unnarrowed t)

   ("bn" "newartisans.com" plain "%?"
    :jump-to-captured t
    :target (file+head "newartisans/%<%Y%m%d%H%M>.org"
                       ":PROPERTIES:
:SLUG:     ${slug}
:PUBLISH:  %^{Publish after date}U
:END:
#+filetags: :publish/newartisans:
#+date: %U
#+title: ${title}\n")
    :immediate-finish t
    :empty-lines-before 1
    :unnarrowed t))

 org-roam-dailies-capture-templates
 '(("d" "default" entry "* %U %?"
    :target (file+head "%<%Y-%m-%d>.org"
                       "#+title: %<%Y-%m-%d>\n")))

 org-agenda-custom-commands
 '(("u" "Unfiled" tags "CATEGORY={Inbox\\|Pending}&LEVEL=2")

   ("n" "Notes" todo "NOTE")

   ("l" "Links" todo "LINK")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ("r" . "Review tasks")

   ("rr" "Tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'nottodo '("TODO" "DOING" "WAIT" "TASK" "PROJECT" "DEFER"))
           (org-config-skip-if-review-not-needed)))
     (org-agenda-cmp-user-defined 'org-review-compare)
     (org-agenda-prefix-format
      "%-10c%2(or (and (org-entry-get nil \"LAST_REVIEW\") \"→\") \"\") ")
     (org-agenda-sorting-strategy '(user-defined-down))))

   ("ru" "Unscheduled tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("rD" "Waiting/delegated" todo "WAIT|TASK"
    ((org-agenda-sorting-strategy
      '(todo-state-up priority-down category-up))))

   ("rd" "Deadlined" alltodo ""
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if 'notdeadline))
     (org-agenda-sorting-strategy '(category-up))))

   ("rs" "Scheduled" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if 'notscheduled)))
     (org-agenda-sorting-strategy '(category-up))))

   ("rR" "Deferred" todo "DEFER"
    ((org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("rn" "Next Actions" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-config-agenda-skip-all-siblings-but-first t)
           (org-agenda-skip-entry-if
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))))))

   ("rS" "Subtasks" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (not (org-extra-subtask-p))))))

   ("rm" "With tags match"
    (lambda (arg)
      (call-interactively #'org-config-with-tags-search nil)))

   ("rc" "With category"
    (lambda (arg)
      (call-interactively #'org-config-with-category-search nil)))

   ("rt" "With item"
    (lambda (arg)
      (call-interactively #'org-config-with-item-search nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ("p" . "Projects")

   ("pp" "All Projects" todo "PROJECT")

   ("pn" "Project Next Actions" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))
           (org-config-agenda-skip-all-siblings-but-first)))))

   ("pN" "Project Next Actions (including low priority)" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))
           (org-config-agenda-skip-all-siblings-but-first nil t)))))

   ("pa" "High Priority Projects" todo "PROJECT"
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if 'notregexp "\\[#A\\]"))))

   ("pb" "Lower Priority Projects" todo "PROJECT"
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if 'regexp "\\[#A\\]"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ("P" . "Priority views")

   ("Pa" "Today's priority #A tasks" agenda ""
    ((org-agenda-ndays 7)
     (org-agenda-skip-function
      '(org-agenda-skip-entry-if 'notregexp "\\[#A\\]"))))

   ("Pb" "Today's priority #A and #B tasks" agenda ""
    ((org-agenda-ndays 7)
     (org-agenda-skip-function
      '(org-agenda-skip-entry-if 'regexp "\\[#C\\]"))))

   ("Pc" "Today's priority #C tasks" agenda ""
    ((org-agenda-ndays 7)
     (org-agenda-skip-function
      '(org-agenda-skip-entry-if 'notregexp "\\[#C\\]"))))

   ("PA" "All priority #A tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'notregexp "\\[#A\\]"
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("PB" "All priority #B tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'regexp "\\[#[AC]\\]"
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("PC" "All priority #C tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'notregexp "\\[#C\\]"
            'nottodo '("TODO" "DOING" "WAIT" "TASK"))))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) "))))
 )

(provide 'org-config)

;;; org-config.el ends here
