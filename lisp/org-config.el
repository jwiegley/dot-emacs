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
   t (format "%s&TODO={DONE\\|CANCELED}" tags)))

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

(setq
 org-roam-capture-templates
 `(("a" "TODO" entry "* TODO %?"
    :target (node "DB5226DB-93BD-4FDC-89C6-0DBE5D1A607E")
    :prepend t)

   ("n" "NOTE" entry "* NOTE %?"
    :target (node "DB5226DB-93BD-4FDC-89C6-0DBE5D1A607E")
    :prepend t)

   ("c" "APPT")

   ("cc" "APPT" entry "* APPT %?"
    :target (node "DB5226DB-93BD-4FDC-89C6-0DBE5D1A607E")
    :prepend t)

   ("cg" "Copper to Gold" entry "* APPT %?\nSCHEDULED: %t"
    :target (node "FB6F3615-1A44-4FE4-9471-2F673F34ADD8")
    :prepend t
    :clock-in t
    :clock-keep t)

   ("cq" "Quantum Trades" entry "* APPT %?\nSCHEDULED: %t"
    :target (node "57940F8A-16A0-48C3-8FB7-F87EC2E2E21E")
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

   ("rr" "Note" plain "%?"
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

   ("pa" "Assembly meeting" entry
    (file "~/doc/template/org/assembly-meeting.org")
    :target (node "79E1D48F-ACC3-442D-A716-1860BADDB9C4")
    :jump-to-captured t)

   ("pf" "Bahá’í Feast" entry
    (file "~/doc/template/org/feast.org")
    :target (node "79E1D48F-ACC3-442D-A716-1860BADDB9C4")
    :jump-to-captured t)

   ("pe" "Bahá’í event" entry
    (file "~/doc/template/org/bahai-event.org")
    :target (node "9D1C6FD3-26C0-4E00-86B6-54ECDC54BF91")
    :jump-to-captured t)

   ("pg" "Flow of guidance" entry
    (file "~/doc/template/org/flow-of-guidance.org")
    :target (node "852262E7-17E6-441C-B473-7473485217FE")
    :jump-to-captured t)

   ("pi" "Ruhi Intensive" entry
    (file "~/doc/template/org/ruhi-intensive.org")
    :target (node "888C3848-8A90-4121-8077-B4078DDE7C57")
    :jump-to-captured t)

   ("pt" "Ruhi Tutor Training" entry
    (file "~/doc/template/org/ruhi-tutor-training.org")
    :target (node "888C3848-8A90-4121-8077-B4078DDE7C57")
    :jump-to-captured t)

   ("pc" "Work Conference" entry
    (file "~/doc/template/org/conference.org")
    :target (node "EF04DCF4-43D5-435E-856D-282431030BEE")
    :jump-to-captured t)
   )

 org-agenda-custom-commands
 '(("u" "Unfiled" tags "CATEGORY={Inbox\\|Pending}&LEVEL=2")

   ("n" "Notes" todo "NOTE")

   ("l" "Links" todo "LINK")

   ("c" "Appointment Calendar" agenda ""
    ((org-agenda-sorting-strategy '(time-up))
     (org-agenda-span 14)
     (org-agenda-ndays 14)
     (org-agenda-regexp-filter-preset '("+APPT"))))

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

   ("rW" "Unscheduled work" alltodo ""
    ((org-agenda-sorting-strategy '(category-up user-defined-up))
     (org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled 'deadline 'timestamp)
           (my-org-agenda-skip-habit)
           (my-org-skip-inactive-todos)))
     (org-agenda-prefix-format "%-11c%5(org-todo-age) ")
     (org-agenda-files
      (list (org-file "kadena/kadena.org")))))

   ("rw" "Waiting/delegated" todo "WAIT|DELEGATED"
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'scheduled)
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
