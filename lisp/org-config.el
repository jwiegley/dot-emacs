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

(defun org-config-review-compare (a b)
  (let* ((ma (or (get-text-property 0 'org-marker a)
                 (get-text-property 0 'org-hd-marker a)))
         (mb (or (get-text-property 0 'org-marker b)
                 (get-text-property 0 'org-hd-marker b)))
         (a-prop (org-review-last-review-prop ma))
         (b-prop (org-review-last-review-prop mb))
	 (ra (org-review-toreview-p ma))
	 (rb (org-review-toreview-p mb)))
    (if (and a-prop b-prop)
        (if (time-less-p ra rb)
            1
          -1)
      (if (and (null a-prop) (null b-prop))
          (org-compare-todo-age a b)
        (if a-prop
            -1
          1)))))

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
 `(("m" "Meetings")

   ("mm" "Meeting" plain
    (file "~/doc/template/org/meeting.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-meeting.org"
     ,(concat
       "#+category: Meeting\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :kadena:\n"
       "#+startup: showeverything\n"
       "#+title: Meeting: %^{Purpose of meeting}\n"))
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("ma" "All Hands" plain
    (file "~/doc/template/org/kadena/meetings/all-hands.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-all-hands.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mb" "BD <> Engineering" plain
    (file "~/doc/template/org/kadena/meetings/bd-engineering.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-bd-engineering.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mt" "CTO Meeting" plain
    (file "~/doc/template/org/kadena/meetings/cto.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-cto.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mx" "CXO Meeting" plain
    (file "~/doc/template/org/kadena/meetings/cxo.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-cxo.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("md" "DX <> Core" plain
    (file "~/doc/template/org/kadena/meetings/dx-and-core.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-dx-and-core.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("ms" "Core Eng Standup" plain
    (file "~/doc/template/org/kadena/meetings/eng-standup.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-eng-standup.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("me" "EVM Standup" plain
    (file "~/doc/template/org/kadena/meetings/evm-standup.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-evm-standup.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mh" "Hack-a-chain")

   ("mhr" "Hack-a-chain Indexer Review" plain
    (file "~/doc/template/org/kadena/meetings/hackachain-indexer-review.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-hackachain-indexer-review.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mhs" "Hack-a-chain Internal Standup" plain
    (file "~/doc/template/org/kadena/meetings/hackachain-internal-standup.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-hackachain-internal-standup.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mP" "John <> PM Team" plain
    (file "~/doc/template/org/kadena/meetings/john-pm-team.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-john-pm-team.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("ml" "Leads Strategy" plain
    (file "~/doc/template/org/kadena/meetings/leads-strategy.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-leads-strategy.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("mp" "Pact Posse" plain
    (file "~/doc/template/org/kadena/meetings/pact-posse.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-pact-posse.org")
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

   ("o" "1-on-1s")

   ("o." "1-on-1 meeting" plain
    (file "~/doc/template/org/kadena/one-on-one.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-1-on-1.org"
     ,(concat
       "#+category: 1-on-1\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :kadena:\n"
       "#+startup: showeverything\n"
       "#+title: 1-on-1: %^{Person meeting with}\n"))
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("oa" "Names beginning with A")

   ("oag" "1-on-1 Albert Groothedde" plain
    (file "~/doc/template/org/kadena/one-on-one/albert-groothedde.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-albert-groothedde.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("oao" "1-on-1 Annelise Osborne" plain
    (file "~/doc/template/org/kadena/one-on-one/annelise-osborne.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-annelise-osborne.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("oe" "Names beginning with E")

   ("oen" "1-on-1 Edmund Noble" plain
    (file "~/doc/template/org/kadena/one-on-one/edmund-noble.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-edmund-noble.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("oep" "1-on-1 Emily Pillmore" plain
    (file "~/doc/template/org/kadena/one-on-one/emily-pillmore.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-emily-pillmore.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("oj" "Names beginning with J")

   ("ojm" "1-on-1 Jesse Marquez" plain
    (file "~/doc/template/org/kadena/one-on-one/jesse-marquez.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-jesse-marquez.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("ojb" "1-on-1 June Boston" plain
    (file "~/doc/template/org/kadena/one-on-one/june-boston.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-june-boston.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("ol" "Names beginning with L")

   ("olk" "1-on-1 Lars Kuhtz" plain
    (file "~/doc/template/org/kadena/one-on-one/lars-kuhtz.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-lars-kuhtz.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("olb" "1-on-1 Leah Bingham" plain
    (file "~/doc/template/org/kadena/one-on-one/leah-bingham.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-leah-bingham.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("or" "Names beginning with R")

   ("ord" "1-on-1 Randy Daal" plain
    (file "~/doc/template/org/kadena/one-on-one/randy-daal.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-randy-daal.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("ors" "1-on-1 Robert Soeldner" plain
    (file "~/doc/template/org/kadena/one-on-one/robert-soeldner.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-robert-soeldner.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("os" "Names beginning with S")

   ("osp" "1-on-1 Stuart Popejoy" plain
    (file "~/doc/template/org/kadena/one-on-one/stuart-popejoy.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-stuart-popejoy.org")
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

   ("b" "Bahá’í templates")

   ("ba" "Assembly meeting" plain
    (file "~/doc/template/org/bahai/assembly-meeting.org")
    :target
    (file+head
     "journal/%<%Y%m%d%H%M>-meeting-local-spiritual-assembly.org"
     ,(concat
       "#+category: Assembly\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :todo:assembly:\n"
       "#+startup: showeverything\n"
       "#+title: Meeting: Local Spiritual Assembly\n"))
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bA" "Ali Nakhjavani Development Fund" plain
    (file "~/doc/template/org/bahai/ali-nakhjavani-development-fund.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-ali-nakhjavani-development-fund.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bc" "C2G Admin" plain
    (file "~/doc/template/org/bahai/meetings/c2g-admin.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-c2g-admin.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bD" "National Convention Delegate Report" plain
    (file "~/doc/template/org/bahai/meetings/national-convention-delegate-report.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-national-convention-delegate-report.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bn" "National Treasurer's Office" plain
    (file "~/doc/template/org/bahai/meetings/national-treasurers-office.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-national-treasurers-office.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bf" "Regional Council and the Flow of Guidance" plain
    (file "~/doc/template/org/bahai/meetings/regional-council-and-flow-of-guidance.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-regional-council-and-flow-of-guidance.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("br" "Regional Treasurer's Office" plain
    (file "~/doc/template/org/bahai/meetings/regional-treasurers-office.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-regional-treasurers-office.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bI" "Ruhi Intensive Reflection" plain
    (file "~/doc/template/org/bahai/meetings/ruhi-intensive-reflection.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-ruhi-intensive-reflection.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bi" "Ruhi Intensive" plain
    (file "~/doc/template/org/bahai/meetings/ruhi-intensive.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-ruhi-intensive.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("bu" "Unit Convention" plain
    (file "~/doc/template/org/bahai/meetings/unit-convention.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-unit-convention.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("B" "Blog")

   ("Bj" "johnwiegley.com" plain "%?"
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

   ("Bn" "newartisans.com" plain "%?"
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

   ("c" "Colors" todo "TODO"
    ((org-agenda-files
      (list (org-file "colors.org")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ("r" . "Review tasks")

   ("rA" "All tasks" alltodo ""
    ((org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rH" "All habits" todo "HABIT"
    ((org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rr" "Tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'nottodo '("TODO" "DOING" "WAIT" "TASK" "PROJECT" "DEFER" "HABIT"))
           (org-config-skip-if-review-not-needed)))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rU" "All tasks never reviewed" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if
            'nottodo '("TODO" "DOING" "WAIT" "TASK" "PROJECT" "DEFER" "HABIT"))
           (org-config-agenda-skip-entry-if
            (org-review-last-review-prop nil))))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("ru" "Unscheduled tasks" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'nottodo '("TODO" "DOING" "WAIT" "TASK" "HABIT"))))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("rs" "Scheduled" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if 'notscheduled)))
     (org-agenda-sorting-strategy '(category-up))))

   ("rD" "Waiting/delegated" todo "WAIT|TASK"
    ((org-agenda-sorting-strategy
      '(todo-state-up priority-down category-up))))

   ("rd" "Deadlined" alltodo ""
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if 'notdeadline))
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

(defun org-config-show-habits ()
  (interactive)
  (org-ql-search (org-agenda-files)
    '(habit)
    :sort '(scheduled)))

(defun org-config-show-todos ()
  (interactive)
  (org-ql-search (org-agenda-files)
    '(todo)
    :sort '(scheduled)))

(provide 'org-config)

;;; org-config.el ends here
