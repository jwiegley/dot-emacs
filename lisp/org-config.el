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

(defconst my-org-locations
  '(
    ;; todo.org
    ("Inbox"         . (node "DB5226DB-93BD-4FDC-89C6-0DBE5D1A607E"))
    ("Bahá’í"        . (node "9D1C6FD3-26C0-4E00-86B6-54ECDC54BF91"))
    ("Bahá’í:Ruhi"   . (node "387B9E7D-BF81-44B0-B9F1-088E5CC58560"))
    ("Bahá’í:Tutor"  . (node "4ED0C729-C8CE-4F58-8AB3-FE3C47827D13"))
    ("C2G"           . (node "FB6F3615-1A44-4FE4-9471-2F673F34ADD8"))
    ("QT"            . (node "57940F8A-16A0-48C3-8FB7-F87EC2E2E21E"))
    ("ANDF"          . (node "928B0CC7-200A-42B2-A212-3ED6B35E57B0"))
    ;; habits.org
    ("Habits"        . (node "7E048E6F-524E-42E9-BD38-76AD04299DE3"))
    ;; assembly.org
    ("Assembly"      . (node "79E1D48F-ACC3-442D-A716-1860BADDB9C4"))
    ("Assembly:Flow" . (node "852262E7-17E6-441C-B473-7473485217FE"))
    ;; kadena.org
    ("Kadena:Leads"  . (node "50E9E856-7F4B-4162-8BCD-12A9118B9857"))
    ("Kadena:Conf"   . (node "EF04DCF4-43D5-435E-856D-282431030BEE"))
    ("Kadena:Ops"    . (node "C1DCA4A4-497F-4A50-8218-079A310665A3"))
    ("Kadena:Core"   . (node "08447A8E-960C-4C19-81C2-BDD0B96661C3"))
    ))

(defsubst my-org-loc (name)
  (cdr (assoc name my-org-locations)))

(setq
 org-roam-capture-templates
 `(("a" "TODO" entry "* TODO %?"
    :target ,(my-org-loc "Inbox")
    :prepend t)

   ("h" "HABIT" entry "* TODO %?
:PROPERTIES:
:STYLE:    habit
:REPEAT_TO_STATE: TODO
:LOG_INTO_DRAWER: t
:END:"
    :target ,(my-org-loc "Habits")
    :prepend t)

   ("n" "NOTE" entry "* NOTE %?"
    :target ,(my-org-loc "Inbox")
    :prepend t)

   ("l" "Checklist" entry "* TODO %? [/]
- [ ] $0
:PROPERTIES:
:COOKIE_DATA: recursive
:RESET_CHECK_BOXES: t
:END:"
    :target ,(my-org-loc "Inbox")
    :prepend t)

   ("C" "Category" entry "* %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
    :target ,(my-org-loc "Inbox")
    :prepend t)

   ("c" "Meetings")

   ("cg" "Copper to Gold" entry "* TODO %?\nSCHEDULED: %t"
    :target ,(my-org-loc "C2G")
    :prepend t
    :clock-in t
    :clock-keep t)

   ("cA" "Ali Nakhjavani Development Fund" entry "* TODO %?\nSCHEDULED: %t"
    :target ,(my-org-loc "ANDF")
    :prepend t
    :clock-in t
    :clock-keep t)

   ("cq" "Quantum Trades" entry "* TODO %?\nSCHEDULED: %t"
    :target ,(my-org-loc "QT")
    :prepend t
    :clock-in t
    :clock-keep t)

   ("B" "Org-contact" entry "* %^{NAME}
:PROPERTIES:
:PHONE:    %^{PHONE}
:EMAIL:    %^{EMAIL}
:END:"
    :target (file ,(org-file "people.org"))
    :prepend t)

   ("r" "Org-roam notes")

   ("rn" "Note" plain "%?"
    :target (file+head "%<%Y%m%d%H%M>-${slug}.org"
                       "#+title: ${title}\n")
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("rq" "Quote" plain "%c\n\n─ %?"
    :target (file+head "%<%Y%m%d%H%M>-${slug}.org"
                       "#+filetags: :quote:\n#+title: ${title}\n")
    :jump-to-captured t
    :empty-lines-before 1)

   ("rk" "Kadena" plain "%?"
    :target (file+head "kadena/%<%Y%m%d%H%M>-${slug}.org"
                       "#+filetags: :kadena:\n#+title: ${title}\n")
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("b" "Blog")

   ("bj" "johnwiegley.com" plain "%?"
    :jump-to-captured t
    :target (file+head "johnwiegley/%<%Y%m%d%H%M>-${slug}.org"
                       ":PROPERTIES:
:SLUG:     ${slug}
:PUBLISH:  %^{Publish after date}U
:END:
,#+filetags: :publish/johnwiegley:
,#+date: %U
,#+title: ${title}\n")
    :empty-lines-before 1
    :unnarrowed t)

   ("bn" "newartisans.com" plain "%?"
    :jump-to-captured t
    :target (file+head "newartisans/%<%Y%m%d%H%M>-${slug}.org"
                       ":PROPERTIES:
:SLUG:     ${slug}
:PUBLISH:  %^{Publish after date}U
:END:
,#+filetags: :publish/newartisans:
,#+date: %U
,#+title: ${title}\n")
    :empty-lines-before 1
    :unnarrowed t)

   ("p" "Project templates")

   ("pp" "PROJECT" entry "* PROJECT %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
    :target ,(my-org-loc "Inbox")
    :prepend t)

   ("pT" "Trip" entry
    (file "~/doc/template/org/trip.org")
    :target ,(my-org-loc "Inbox")
    :jump-to-captured t)

   ("pb" "Bahá’í templates")

   ("pba" "Assembly meeting" entry
    (file "~/doc/template/org/bahai/assembly-meeting.org")
    :target ,(my-org-loc "Assembly")
    :jump-to-captured t)

   ("pbf" "Bahá’í Feast" entry
    (file "~/doc/template/org/bahai/feast.org")
    :target ,(my-org-loc "Assembly")
    :jump-to-captured t)

   ("pbe" "Bahá’í event" entry
    (file "~/doc/template/org/bahai/bahai-event.org")
    :target ,(my-org-loc "Bahá’í")
    :jump-to-captured t)

   ("pbg" "Flow of guidance" entry
    (file "~/doc/template/org/bahai/flow-of-guidance.org")
    :target ,(my-org-loc "Assembly:Flow")
    :jump-to-captured t)

   ("pbi" "Ruhi Intensive" entry
    (file "~/doc/template/org/bahai/ruhi-intensive.org")
    :target ,(my-org-loc "Bahá’í:Ruhi")
    :jump-to-captured t)

   ("pbt" "Ruhi Tutor Training" entry
    (file "~/doc/template/org/bahai/ruhi-tutor-training.org")
    :target ,(my-org-loc "Bahá’í:Tutor")
    :jump-to-captured t)

   ("pw" "Work templates")

   ("pwc" "Work Conference" entry
    (file "~/doc/template/org/kadena/conference.org")
    :target ,(my-org-loc "Kadena:Conf")
    :jump-to-captured t)

   ("pwo" "Offsite Meeting" entry
    (file "~/doc/template/org/kadena/offsite-meeting.org")
    :target ,(my-org-loc "Kadena:Leads")
    :jump-to-captured t)

   ("pwO" "Out of Office" entry
    (file "~/doc/template/org/kadena/out-of-office.org")
    :target ,(my-org-loc "Kadena:Ops")
    :jump-to-captured t)

   ("pwn" "Network Incident" entry
    (file "~/doc/template/org/kadena/network-incident.org")
    :target ,(my-org-loc "Kadena:Core")
    :jump-to-captured t)

   ("s" "Slide presentations")

   ("ss" "SKIP" entry "* %?
:PROPERTIES:
:BEAMER_act: <2->
:END:"
    :target ,(my-org-loc "Inbox")
    :prepend t)
   )

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
