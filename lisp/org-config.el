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

(defun org-agenda-files-except (&rest args)
  (let ((result org-agenda-files))
    (dolist (arg args)
      (setq result (delete arg result)))
    result))

(defun org-extra-with-tags-search (tags)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive "sTags: ")
  (org-tags-view
   t (format "%s&TODO={TODO\\|WAITING\\|DELEGATED}" tags)))

(defun org-extra-with-tags-search-done (tags)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive "sTags: ")
  (org-tags-view
   t (format "%s&TODO={DONE\\|CANCELED\\|COMPLETE\\|ABORTED}" tags)))

(defun org-extra-with-category-search (who)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive
   (list (completing-read "Category: " (org-property-values "CATEGORY"))))
  (org-tags-view
   t (format "CATEGORY=\"%s\"&TODO={TODO\\|WAITING\\|DELEGATED}" who)))

(defun org-extra-with-item-search (who)
  "Search by WITH propery, which is made inheritable for this function."
  (interactive "sItem: ")
  (org-tags-view
   t (format "ITEM={%s}&TODO={TODO\\|WAITING\\|DELEGATED}" who)))

(defun my-org-parent-keyword ()
  (save-excursion
    (org-up-heading-safe)
    (org-get-todo-state)))

(defun my-org-parent-priority ()
  (save-excursion
    (org-up-heading-safe)
    (save-match-data
      (beginning-of-line)
      (and (looking-at org-heading-regexp)
	   (org-get-priority (match-string 0))))))

(eval-when-compile
  (require 'org-habit))

(defun my-org-agenda-should-skip-p
    (&optional include-non-projects include-low-prio-projects)
  "Skip all but the first non-done entry."
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
      (unless (and (string= "PROJECT" (my-org-parent-keyword))
                   (or include-low-prio-projects
                       (> (my-org-parent-priority) 0)))
        (setq should-skip-entry t)))
    should-skip-entry))

(defun my-org-agenda-skip-all-siblings-but-first
    (&optional include-non-projects include-low-prio-projects)
  "Skip all but the first non-done entry."
  (when (my-org-agenda-should-skip-p
         include-non-projects include-low-prio-projects)
    (or (outline-next-heading)
        (goto-char (point-max)))))

(defun my-org-agenda-skip-habit ()
  (when (ignore-errors (org-is-habit-p))
    (or (outline-next-heading)
        (goto-char (point-max)))))

(defun my-org-skip-inactive-todos ()
  (unless (member (org-get-todo-state)
                  '("TODO" "DOING" "WAIT" "DELEGATED"))
    (or (outline-next-heading)
        (goto-char (point-max)))))

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

     ("pT" "Trip" entry
      ,Inbox
      (file "~/doc/template/org/trip.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pb" "Bahá’í templates")

     ("pba" "Assembly meeting" entry
      (file+headline ,(org-file "assembly.org")
                     "Carmichael Local Spiritual Assembly (LSA)")
      (file "~/doc/template/org/bahai/assembly-meeting.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbf" "Bahá’í Feast" entry
      (file+headline ,(org-file "assembly.org")
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
      (file+headline ,(org-file "assembly.org")
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
      (file+headline ,(org-file "kadena.org") "Leadership")
      (file "~/doc/template/org/kadena/offsite-meeting.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwc" "Work Conference" entry
      (file+headline ,(org-file "kadena.org") "Conferences")
      (file "~/doc/template/org/kadena/conference.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwO" "Out of Office" entry
      (file+headline ,(org-file "kadena.org") "Operations (Ops)")
      (file "~/doc/template/org/kadena/out-of-office.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwn" "Network Incident" entry
      (file+headline ,(org-file "kadena.org") "Improve Response Process")
      (file "~/doc/template/org/kadena/network-incident.org")
      :immediate-finish t
      :jump-to-captured t)))

 org-roam-capture-templates
 `(("m" "Meeting notes" plain
    (file "~/doc/template/org/meeting.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-meeting.org"
     "#+date: %(setq my/org-start-date (my/org-read-date t))\n#+title: Meeting: %^{Purpose of meeting}\n")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("n" "Note" plain "%?"
    :target (file+head "%<%Y%m%d%H%M>.org"
                       "#+title: ${title}\n")
    :immediate-finish t
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("o" "One-on-one notes" plain
    (file "~/doc/template/org/kadena/one-on-one.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-1-on-1.org"
     "#+date: %(setq my/org-start-date (my/org-read-date t))\n#+title: 1-on-1: %^{Person meeting with}\n")
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

   ("ru" "Unscheduled (last 90 days)" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp)
           (org-extra-agenda-skip-if-not-within 90)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
     (org-agenad-files
      (org-agenda-files-except
       (org-file "kadena/kadena.org")
       (org-file "OSS.org")))))

   ("rU" "All unscheduled" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
     (org-agenda-files
      (org-agenda-files-except
       (org-file "kadena/kadena.org")
       (org-file "OSS.org")))))

   ("ro" "Unscheduled open source" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp 'regexp
                                     "\\* \\(DEFER\\)")
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-sorting-strategy '(category-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
     (org-agenda-files
      (list (org-file "OSS.org")))))

   ("rw" "Unscheduled work (last 90 days)" alltodo ""
    ((org-agenda-sorting-strategy '(category-up user-defined-up))
     (org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp)
           (org-extra-agenda-skip-if-not-within 90)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
     (org-agenda-files
      (list (org-file "kadena/kadena.org")))))

   ("rW" "All unscheduled work" alltodo ""
    ((org-agenda-sorting-strategy '(category-up user-defined-up))
     (org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
     (org-agenda-files
      (list (org-file "kadena/kadena.org")))))

   ("rD" "Waiting/delegated" todo "WAIT|DELEGATED"
    ((org-agenda-skip-function
      '(or ;; (org-agenda-skip-entry-if 'scheduled)
        (my-org-agenda-skip-habit)))
     (org-agenda-sorting-strategy
      '(todo-state-up priority-down category-up))))

   ("rd" "Deadlined" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'notdeadline)
           (my-org-agenda-skip-habit)))
     (org-agenda-sorting-strategy '(category-up))))

   ("rs" "Scheduled" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'notscheduled)
           (my-org-agenda-skip-habit)))
     (org-agenda-sorting-strategy '(category-up))))

   ("rD" "Deferred" todo "DEFER"
    ((org-agenda-skip-function #'my-org-agenda-skip-habit)
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")))

   ("rn" "Next Actions" alltodo ""
    ((org-agenda-skip-function
      '(or (my-org-agenda-skip-all-siblings-but-first t)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))))

   ("rm" "With tags match"
    (lambda (arg)
      (call-interactively #'org-extra-with-tags-search nil)))

   ("rc" "With category"
    (lambda (arg)
      (call-interactively #'org-extra-with-category-search nil)))

   ("rt" "With item"
    (lambda (arg)
      (call-interactively #'org-extra-with-item-search nil)))

   ;; ("ra" "Archives" alltodo ""
   ;;  ((org-agenda-sorting-strategy '(category-up user-defined-up))
   ;;   (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
   ;;   (org-agenda-files
   ;;    (list (org-file "archive/archive.org")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ("p" . "Projects")

   ("pp" "All Projects" todo "PROJECT")

   ("pn" "Project Next Actions" alltodo ""
    ((org-agenda-skip-function
      '(or (my-org-agenda-skip-all-siblings-but-first)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))))

   ("pN" "Project Next Actions (including low priority)" alltodo ""
    ((org-agenda-skip-function
      '(or (my-org-agenda-skip-all-siblings-but-first nil t)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))))

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
      '(or (org-agenda-skip-entry-if 'notregexp "\\[#A\\]")
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")))

   ("PB" "All priority #B tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'regexp "\\[#[AC]\\]")
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")))

   ("PC" "All priority #C tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'notregexp "\\[#C\\]")
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) "))))
 )

(provide 'org-config)

;;; org-config.el ends here
