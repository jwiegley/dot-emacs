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

(require 'org)
(require 'org-extra)
(eval-when-compile
  (require 'org-habit))

(defgroup org-config nil
  "Configurations for Org-mode and related packages"
  :group 'org)

(defconst org-config-open-re "/TODO|DOING|WAIT|TASK|HABIT")
(defconst org-config-closed-re "/TODO/DONE|CANCELED")

(defun org-config-with-tags-search (tags)
  (interactive "sTags: ")
  (org-tags-view t (format "%s%s" tags org-config-open-re)))

(defun org-config-with-tags-search-done (tags)
  (interactive "sTags: ")
  (org-tags-view t (format "%s%s" tags org-config-closed-re)))

(defun org-config-with-category-search (who)
  (interactive
   (list (completing-read "Category: " (org-property-values "CATEGORY"))))
  (org-tags-view t (format "CATEGORY=\"%s\"%s" who org-config-open-re)))

(defun org-config-with-keyword-search (who)
  (interactive
   (list (completing-read "Keyword: " (org-property-values "KEYWORDS"))))
  (org-tags-view t (format "KEYWORDS={%s}%s" who org-config-open-re)))

(defun org-config-with-item-search (who)
  (interactive "sItem: ")
  (org-tags-view t (format "ITEM={%s}%s" who org-config-open-re)))

(defmacro org-config-agenda-skip-entry-if (body)
  "Skip all but the first non-done entry."
  `(when ,body
     (org-with-wide-buffer
      (or (outline-next-heading)
          (goto-char (point-max))))))

(defsubst org-config-agenda-skip-habit ()
  (org-config-agenda-skip-entry-if
   (org-extra-habit-p)))

(defsubst org-config-skip-if-review-not-needed ()
  (org-config-agenda-skip-entry-if
   (not (org-extra-needs-review-p))))

(defsubst org-config-skip-if-reviewed ()
  (org-config-agenda-skip-entry-if
   (org-review-last-review-prop nil)))

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

     ("h" "HABIT" entry
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

     ("l" "LINK" entry
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

     ("B" "Org-contact" entry
      (file ,(org-file "people.org"))
      "* %^{NAME}
:PROPERTIES:
:PHONE:    %^{PHONE}
:EMAIL:    %^{EMAIL}
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

     ("p" "Project templates")

     ("pp" "PROJECT" entry
      ,Inbox
      "* TODO %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
      :prepend t)

     ("pt" "Trip" entry
      ,Inbox
      (file "~/org/template/trip.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pT" "Taxes" entry
      (file+headline ,(org-file "todo.org") "Taxes")
      (file "~/org/template/taxes.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pb" "Bahá’í templates")

     ("pba" "Assembly meeting" entry
      (file+headline ,(org-file "assembly/assembly.org")
                     "Carmichael Local Spiritual Assembly (LSA)")
      (file "~/org/template/bahai/assembly-meeting.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbf" "Bahá’í Feast" entry
      (file+headline ,(org-file "assembly/assembly.org")
                     "Carmichael Local Spiritual Assembly (LSA)")
      (file "~/org/template/bahai/feast.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbe" "Bahá’í event" entry
      ;; I don't know in advance which section it belongs in.
      ,Inbox
      (file "~/org/template/bahai/bahai-event.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbE" "Recurring Bahá’í event" entry
      ;; I don't know in advance which section it belongs in.
      ,Inbox
      (file "~/org/template/bahai/recurring-event.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbg" "Flow of guidance" entry
      (file+headline ,(org-file "assembly/assembly.org")
                     "Increasing the flow of guidance to the grassroots")
      (file "~/org/template/bahai/flow-of-guidance.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pbp" "Program (such as community devotional)" entry
      ;; I don't know in advance which section it belongs in.
      ,Inbox
      (file "~/org/template/bahai/program.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pw" "Work templates")

     ("pwm" "Offsite Meeting" entry
      (file+headline ,(org-file "kadena/kadena.org") "Leadership")
      (file "~/org/template/kadena/offsite-meeting.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwc" "Work Conference" entry
      (file+headline ,(org-file "kadena/kadena.org") "Conferences")
      (file "~/org/template/kadena/conference.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwO" "Out of Office" entry
      (file+headline ,(org-file "kadena/kadena.org") "Operations (Ops)")
      (file "~/org/template/kadena/out-of-office.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwn" "Network Incident" entry
      (file+headline ,(org-file "kadena/kadena.org") "Improve Response Process")
      (file "~/org/template/kadena/network-incident.org")
      :immediate-finish t
      :jump-to-captured t)))

 org-roam-capture-templates
 `(("m" "Meeting" plain
    (file "~/org/template/meeting.org")
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

   ("n" "Note" plain "%?"
    :target (file+head "%<%Y%m%d%H%M>.org"
                       "#+category: Note\n#+title: ${title}\n")
    :immediate-finish t
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

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
    :unnarrowed t)

   ("p" "Project templates")

   ("pb" "Bahá’í templates")

   ("pba" "Assembly meeting" plain
    (file "~/org/template/bahai/assembly-meeting.org")
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

   ("pbc" "C2G Admin" plain
    (file "~/org/template/bahai/meetings/c2g-admin.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-c2g-admin.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbD" "National Convention Delegate Report" plain
    (file "~/org/template/bahai/meetings/national-convention-delegate-report.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-national-convention-delegate-report.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbf" "Ali Nakhjavani Development Fund" plain
    (file "~/org/template/bahai/meetings/ali-nakhjavani-development-fund.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-ali-nakhjavani-development-fund.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbF" "Regional Council and the Flow of Guidance" plain
    (file "~/org/template/bahai/meetings/regional-council-and-flow-of-guidance.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-regional-council-and-flow-of-guidance.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbn" "National Treasurer's Office" plain
    (file "~/org/template/bahai/meetings/national-treasurers-office.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-national-treasurers-office.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbr" "Regional Treasurer's Office" plain
    (file "~/org/template/bahai/meetings/regional-treasurers-office.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-regional-treasurers-office.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbi" "Ruhi Intensive" plain
    (file "~/org/template/bahai/meetings/ruhi-intensive.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-ruhi-intensive.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbI" "Ruhi Intensive Reflection" plain
    (file "~/org/template/bahai/meetings/ruhi-intensive-reflection.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-ruhi-intensive-reflection.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pbu" "Unit Convention" plain
    (file "~/org/template/bahai/meetings/unit-convention.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-unit-convention.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pw" "Work templates")

   ("pwa" "All Hands" plain
    (file "~/org/template/kadena/meetings/all-hands.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-all-hands.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwb" "BD <> Engineering" plain
    (file "~/org/template/kadena/meetings/bd-engineering.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-bd-engineering.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwt" "CTO Meeting" plain
    (file "~/org/template/kadena/meetings/cto.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-cto.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwx" "CXO Meeting" plain
    (file "~/org/template/kadena/meetings/cxo.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-cxo.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwd" "DX <> Core" plain
    (file "~/org/template/kadena/meetings/dx-and-core.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-dx-and-core.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pws" "Core Eng Standup" plain
    (file "~/org/template/kadena/meetings/eng-standup.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-eng-standup.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwe" "EVM Huddle" plain
    (file "~/org/template/kadena/meetings/evm-huddle.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-evm-huddle.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwh" "Hack-a-chain")

   ("pwhr" "Hack-a-chain Indexer Review" plain
    (file "~/org/template/kadena/meetings/hackachain-indexer-review.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-hackachain-indexer-review.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwhs" "Hack-a-chain Internal Standup" plain
    (file "~/org/template/kadena/meetings/hackachain-internal-standup.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-hackachain-internal-standup.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwj" "JS Team" plain
    (file "~/org/template/kadena/meetings/js-team.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-js-team.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwP" "John <> PM Team" plain
    (file "~/org/template/kadena/meetings/john-pm-team.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-john-pm-team.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwl" "Leads Strategy" plain
    (file "~/org/template/kadena/meetings/leads-strategy.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-leads-strategy.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwp" "Pact Posse" plain
    (file "~/org/template/kadena/meetings/pact-posse.org")
    :target (file "journal/%<%Y%m%d%H%M>-meeting-pact-posse.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwo" "1-on-1s")

   ("pwoo" "1-on-1 meeting" plain
    (file "~/org/template/kadena/one-on-one.org")
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

   ("pwoa" "Names beginning with A")

   ("pwoab" "1-on-1 Anastasia Bez" plain
    (file "~/org/template/kadena/one-on-one/anastasia-bez.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-anastasia-bez.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwoag" "1-on-1 Albert Groothedde" plain
    (file "~/org/template/kadena/one-on-one/albert-groothedde.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-albert-groothedde.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwoao" "1-on-1 Annelise Osborne" plain
    (file "~/org/template/kadena/one-on-one/annelise-osborne.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-annelise-osborne.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwoe" "Names beginning with E")

   ("pwoen" "1-on-1 Edmund Noble" plain
    (file "~/org/template/kadena/one-on-one/edmund-noble.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-edmund-noble.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwoep" "1-on-1 Emily Pillmore" plain
    (file "~/org/template/kadena/one-on-one/emily-pillmore.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-emily-pillmore.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwoj" "Names beginning with J")

   ("pwojb" "1-on-1 June Boston" plain
    (file "~/org/template/kadena/one-on-one/june-boston.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-june-boston.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwojc" "1-on-1 Jose Cardona" plain
    (file "~/org/template/kadena/one-on-one/jose-cardona.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-jose-cardona.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwojm" "1-on-1 Jesse Marquez" plain
    (file "~/org/template/kadena/one-on-one/jesse-marquez.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-jesse-marquez.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwol" "Names beginning with L")

   ("pwolb" "1-on-1 Leah Bingham" plain
    (file "~/org/template/kadena/one-on-one/leah-bingham.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-leah-bingham.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwolk" "1-on-1 Lars Kuhtz" plain
    (file "~/org/template/kadena/one-on-one/lars-kuhtz.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-lars-kuhtz.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwor" "Names beginning with R")

   ("pword" "1-on-1 Randy Daal" plain
    (file "~/org/template/kadena/one-on-one/randy-daal.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-randy-daal.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)
   ("pwors" "1-on-1 Robert Soeldner" plain
    (file "~/org/template/kadena/one-on-one/robert-soeldner.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-robert-soeldner.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("pwos" "Names beginning with S")

   ("pwosp" "1-on-1 Stuart Popejoy" plain
    (file "~/org/template/kadena/one-on-one/stuart-popejoy.org")
    :target (file "journal/%<%Y%m%d%H%M>-1-on-1-stuart-popejoy.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t))

 org-roam-dailies-capture-templates
 '(("d" "default" entry "* %U %?"
    :target (file+head "%<%Y-%m-%d>.org"
                       "#+title: %<%Y-%m-%d>\n")))

 org-agenda-custom-commands
 '(("a" "Agenda"
    ((agenda
      ""
      ((org-agenda-skip-function
        '(org-config-agenda-skip-entry-if
          (and (org-extra-habit-p)
               (org-review-last-review-prop nil)
               (not (org-extra-needs-review-p)))))
       (org-super-agenda-groups
        '((:name "Important"
                 :and (:priority "A" :not (:habit t)))
          (:name "Overdue"
                 :deadline past)
          (:name "Due Soon"
                 :deadline future)
          (:name "Reschedule"
                 :and (:scheduled past :not (:habit t)))
          (:name "Needs review"
                 :and (:todo ("WAIT" "TASK" "DOING")
                             :not (:priority "C")))
          (:name "Calls"
                 :tag "Call")
          (:name "Errands"
                 :tag "Errand")
          (:name "Tasks"
                 :not (:habit t))
          (:name "Habits"
                 :habit t)
          ))))
     ;; (alltodo
     ;;  ""
     ;;  ((org-agenda-overriding-header
     ;;    "Items needing review")
     ;;   (org-agenda-skip-function
     ;;    '(or (org-config-agenda-skip-entry-if
     ;;          (org-extra-subtask-p))
     ;;         (org-agenda-skip-entry-if
     ;;          'scheduled 'deadline 'timestamp
     ;;          'todo org-done-keywords)
     ;;         (org-config-skip-if-review-not-needed)))
     ;;   (org-agenda-cmp-user-defined 'org-config-review-compare)
     ;;   (org-agenda-prefix-format
     ;;    "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     ;;   (org-agenda-sorting-strategy '(user-defined-down))
     ;;   (org-overriding-columns-format
     ;;    "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))
     ))

   ("u" "Unfiled" tags "CATEGORY={Inbox\\|Pending}&LEVEL=2")

   ("n" "Notes" todo "NOTE")

   ("l" "Links" todo "LINK")

   ("c" "Colors" todo "TODO"
    ((org-agenda-files
      (list (org-file "colors.org")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   ("r" . "Review tasks")

   ("ra" "All tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-agenda-skip-entry-if
            (and (org-review-last-review-prop nil)
                 (not (org-review-toreview-p))))))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rr" "Tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rn" "Next Actions" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (or (not (org-extra-subtask-p))
            (org-extra-has-preceding-todo-p))))))

   ("rp" "Projects" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (not (org-extra-top-level-project-p))))))

   ("rP" "Stuck projects" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (or (not (org-extra-top-level-project-p))
            (org-extra-first-child-todo
             #'(lambda () (org-get-scheduled-time (point)))))))))

   ("rD" "Waiting/delegated" todo "WAIT|TASK"
    ((org-agenda-sorting-strategy
      '(todo-state-up priority-down category-up))))

   ("rR" "Deferred" todo "DEFER"
    ((org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("rA" "All tasks" alltodo ""
    ((org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rH" "Habits" todo "HABIT"
    ((org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rU" "Tasks never reviewed" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'todo org-done-keywords)
           (org-config-skip-if-reviewed)))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format
      "%-10c%-5e%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("ru" "Unscheduled tasks" alltodo ""
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if
        'scheduled 'deadline 'timestamp
        'todo org-done-keywords))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("rs" "Scheduled" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-habit)
           (org-agenda-skip-entry-if 'notscheduled)))
     (org-agenda-sorting-strategy '(category-up))))

   ("rd" "Deadlined" alltodo ""
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if 'notdeadline))
     (org-agenda-sorting-strategy '(category-up))))

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

   ("rk" "With keyword"
    (lambda (arg)
      (call-interactively #'org-config-with-keyword-search nil)))

   ("rt" "With item"
    (lambda (arg)
      (call-interactively #'org-config-with-item-search nil)))
   ))

(defun org-config-find (query)
  (interactive "sQuery: ")
  (org-ql-search (org-agenda-files)
    `(and (or (todo)
              (todo "NOTE"))
          (not (habit))
          (rifle ,query))))

(defun org-config-find-any (query)
  (interactive "sQuery: ")
  (org-ql-search (org-ql-search-directories-files)
    `(rifle ,query)))

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

(defun org-config-show-tasks-with-filetags (tag)
  "Report items pending review after one second."
  (interactive "sTag: ")
  (org-ql-search (org-agenda-files)
    `(and (todo)
          ;; (not (tags))
          ;; (save-excursion
          ;;   (goto-char (point-min))
          ;;   (re-search-forward (concat "#\\+filetags:.*:" ,tag ":") 4096 t))
          )
    :sort '(scheduled todo)))

(provide 'org-config)

;;; org-config.el ends here
