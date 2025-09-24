;;; org-config --- Configurations for Org-mode and related packages -*- lexical-binding: t -*-

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
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

(require 'org-constants)
(require 'org)
(require 'org-capture)
(require 'org-roam-capture)
(require 'org-roam-dailies)
(require 'org-ext)
(require 'org-ql)
(require 'org-agenda-random)
(eval-when-compile
  (require 'org-habit))

(defgroup org-config nil
  "Configurations for Org-mode and related packages"
  :group 'org)

(defun org-config-hide ()
  (interactive)
  (org-set-property "HIDE" "t"))

(defconst org-config-open-re "/TODO|DOING|WAIT|TASK|HABIT"
  "Tasks that are open and actionable. Excludes DEFER tasks.")
(defconst org-config-closed-re "/TODO/DONE|CANCELED|PASS"
  "Tasks that are closed.")

(defun org-config-tags-search (tags)
  (interactive "sTags: ")
  (org-tags-view t (format "%s%s" tags org-config-open-re)))

(defun org-config-tags-search-done (tags)
  (interactive "sTags: ")
  (org-tags-view t (format "%s%s" tags org-config-closed-re)))

(defun org-config-category-search (who)
  (interactive
   (list (completing-read "Category: " (org-ext-get-all-categories)
                          nil nil nil 'org-ext-category-history)))
  (org-tags-view t (format "CATEGORY=\"%s\"%s" who org-config-open-re)))

(defun org-config-raw-category-search (who)
  (interactive
   (list (completing-read "Category: " (org-ext-get-all-categories)
                          nil nil nil 'org-ext-category-history)))
  (org-tags-view t (format "CATEGORY=\"%s\"" who)))

(defun org-config-keyword-search (who)
  (interactive
   (list (completing-read "Keyword: " (org-property-values "KEYWORDS"))))
  (org-tags-view t (format "KEYWORDS={%s}%s" who org-config-open-re)))

(defun org-config-item-search (who)
  (interactive "sItem: ")
  (org-tags-view t (format "ITEM={%s}%s" who org-config-open-re)))

(defun org-config-tasks-for-query (who)
  (interactive "sTasks for: ")
  (org-ql-block `(tasks-for ,who)))

(defun org-config-text-search (regexp &optional include-closed)
  (interactive "sRegexp: \nP")
  (org-ql-search (org-ql-search-directories-files)
    (if include-closed
        `(regexp ,regexp)
      `(and (regexp ,regexp)
            (not (todo "CANCELED" "DONE"))))))

(defmacro org-config-agenda-skip-entry-if (body)
  "Skip all but the first non-done entry."
  `(when ,body
     (org-with-wide-buffer
      (or (outline-next-heading)
          (goto-char (point-max))))))

(defsubst org-config-agenda-skip-habit ()
  (org-config-agenda-skip-entry-if
   (org-ext-habit-p)))

(defcustom org-config-names-regularly-reviewed
  '(
    "Annelise"
    "Bez"
    "Brittaney"
    "Emily"
    "Jesse"
    "June"
    "Lars"
    "Leah"
    "Stuart"
    "Travis"
    "Linda"
    "Hafsah"
    "Robert"
    )
  "Tags \"regularly reviewed\" that don't need separate review."
  :type '(repeat string)
  :group 'org-config)

(defcustom org-config-categories-regularly-reviewed
  (append org-config-names-regularly-reviewed
          '("EVM"
            "PM"
            "JS"
            "Core"
            "Assembly"
            "Crmichael"
            "Feast"
            "Fund"))
  "Categories \"regularly reviewed\" that don't need separate review."
  :type '(repeat string)
  :group 'org-config)

(defun org-config-skip-if-regularly-reviewed ()
  (org-config-agenda-skip-entry-if
   (and (null (org-entry-get nil "HIDE"))
        (or (cl-intersection org-config-names-regularly-reviewed
                             (org-get-tags)
                             :test #'string=)
            (member (org-get-category)
                    org-config-categories-regularly-reviewed)
            (string-match-p "OSS" (buffer-file-name))))))

(defsubst org-config-skip-if-review-not-needed ()
  (org-config-agenda-skip-entry-if
   (not (org-ext-needs-review-p))))

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
          (my/org-compare-todo-age a b)
        (if a-prop
            -1
          1)))))

(defsubst org-config-meeting-template
    (keys title file dir &optional prefix location)
  `(,keys ,title plain
          (file ,(expand-file-name file dir))
          :target (file ,(concat (or location "meeting")
                                 "/%<%Y%m%d%H%M>-"
                                 (or prefix "") file))
          :immediate-finish t
          :jump-to-captured t
          :unnarrowed t
          :no-save t))

(defsubst org-config-kadena-meeting (keys title file)
  (org-config-meeting-template
   keys title file "~/org/template/kadena/meeting"))

(defsubst org-config-kadena-1-on-1 (keys title file)
  (org-config-meeting-template
   keys title file "~/org/template/kadena/one-on-one" "1-on-1-"))

(defsubst org-config-bahai-meeting (keys title file)
  (org-config-meeting-template
   keys title file "~/org/template/bahai/meeting" nil "bahai"))

(defsubst org-config-call-only (f)
  `(lambda (_arg) (call-interactively (function ,f) nil)))

(defsubst org-config-1-on-1-from-name (name)
  (let ((down (downcase name)))
    (org-config-kadena-1-on-1
     (apply #'concat "wo"
            (mapcar #'(lambda (word) (char-to-string (aref word 0)))
                    (split-string down)))
     (concat "1-on-1 " name)
     (concat (replace-regexp-in-string " " "-" down) ".org"))))

(defconst org-config-check-if-scheduled
  "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")

(defconst org-config-columns-for-reviewed
  "%-10c%-2(or (org-entry-get nil \"REVIEWS\") \" \")")

(defconst org-config-standard-columns
  "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")

(defun org-config-entry-in-inbox (entry)
  (let ((marker (org-compare--get-marker entry)))
    (with-current-buffer (marker-buffer marker)
      (member (org-get-category marker) '("Inbox" "Drafts")))))

(defun org-config-compare-items-needing-review ()
  (let ((compare-randomly (org-compare-randomly)))
    (lambda (x y)
      (let ((x-in-inbox (org-config-entry-in-inbox x))
            (y-in-inbox (org-config-entry-in-inbox y)))
        (if x-in-inbox
            1
          (if y-in-inbox
              -1
            (funcall compare-randomly x y)))))))

(setq
 org-capture-templates
 (let ((Inbox '(function org-ext-goto-inbox-heading)))
   `(("a" "TODO" entry
      ,Inbox
      "* TODO %?"
      :prepend t)

     ("d" "DRAFT" entry
      (file+headline ,org-constants-drafts-path "Drafts")
      "* DRAFT %U\n%?"
      :prepend t
      :hook (lambda ()
              (setq-local auto-save-interval 8
                          auto-save-timeout 1)))

     ("f" "Feedback" entry
      ,Inbox
      "* TODO Feedback: %?
- Can I give you some feedback?
- When you…
- What happens is…
- Is this something you can work on?"
      :prepend t)

     ("j" "Journal" entry
      (file ,(expand-file-name org-constants-journelly-path))
      "* %U\n%?"
      :prepend t)

     ("P" "Person" entry
      (file ,org-constants-contacts-path)
      "* %?
:PROPERTIES:
:ORG:      ?
:EMAIL:    ?
:PHONE:    ?
:NOTE:     ?
:ADDRESS:  ?
:END:"
      :prepend nil)

     ("h" "HABIT" entry
      (file+headline ,org-constants-flat-habits-path "Personal")
      "* TODO ↓△✶✓↑ %?
SCHEDULED: <`(created-stamp t 'no-brackets)` .+1d/3d>
:PROPERTIES:
:STYLE:    habit
:REPEAT_TO_STATE: HABIT
:LOG_INTO_DRAWER: t
:LOGGING:  DEFER(!) DONE(!) CANCELED(!)
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
:END:
%:initial"
      :prepend t)

     ("c" "Checklist" entry
      ,Inbox
      "* TODO %? [/]
:PROPERTIES:
:COOKIE_DATA: recursive
:RESET_CHECK_BOXES: t
:END:
- [ ] $0"
      :prepend t)

     ("C" "Category" entry
      (function org-ext-up-heading)
      "* %?
:PROPERTIES:
:CATEGORY: %^{CATEGORY}
:END:"
      :prepend t)

     ("B" "Org-contact" entry
      (file ,org-constants-contacts-path)
      "* %^{NAME}
:PROPERTIES:
:PHONE:    %^{PHONE}
:EMAIL:    %^{EMAIL}
:END:"
      :prepend t)

     ("b" "Bahá’í")

     ("bc" "Concentric circles" entry
      ,Inbox
      "** NOTE Concentric circles — %?
- *Population*
  Everyone in a geographic area

- *In Conversation*
  Has not yet participated in anything

- *Participating*
  Volition to be part of something

- *Shouldering Responsibility*
  Has arisen to share the Word of God with others

- *Accompanying Others*
  Encouraging others to share the Word of God"
      :immediate-finish t
      :jump-to-captured t)

     ("m" "Meetings")

     ("mg" "Copper to Gold" entry
      (file+headline ,org-constants-todo-path "Copper to Gold")
      "* TODO %?\nSCHEDULED: %t"
      :prepend t
      :clock-in t
      :clock-keep t)

     ("mA" "Ali Nakhjavani Development Fund" entry
      (file+headline ,org-constants-todo-path
                     "Ali Nakhjavani Development Fund (ANDF)")
      "* TODO %?\nSCHEDULED: %t"
      :prepend t
      :clock-in t
      :clock-keep t)

     ("mq" "Quantum Trades" entry
      (file+headline ,org-constants-todo-path "Quantum Trades")
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
      (file+headline ,org-constants-todo-path "Taxes")
      (file "~/org/template/taxes.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pb" "Bahá’í templates")

     ("pbf" "Bahá’í Feast" entry
      (file+headline ,org-constants-assembly-path
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
      (file+headline ,org-constants-assembly-path
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

     ("pwO" "Out of Office" entry
      (file+headline ,org-constants-work-todo-path "Operations (Ops)")
      (file "~/org/template/kadena/out-of-office.org")
      :immediate-finish t
      :jump-to-captured t)

     ("pwn" "Network Incident" entry
      (file+headline ,org-constants-work-todo-path "Improve Response Process")
      (file "~/org/template/kadena/network-incident.org")
      :immediate-finish t
      :jump-to-captured t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 org-roam-capture-templates
 `(("m" "Meeting" plain
    (file "~/org/template/meeting.org")
    :target
    (file+head
     "%<%Y%m%d%H%M>.org"
     ,(concat
       "#+category: Meeting\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :meeting:\n"
       "#+startup: showeverything\n"
       "#+title: %^{Purpose of meeting}\n"))
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

   ("b" "Bahá’í templates")

   ("bn" "Bahá’í Note" plain "%?"
    :target
    (file+head
     "bahai/%<%Y%m%d%H%M>.org"
     ,(concat "#+category: Bahá’í\n"
              "#+filetags: :bahai:\n"
              "#+title: ${title}\n"))
    :immediate-finish t
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("bm" "Bahá’í Meeting" plain
    (file "~/org/template/meeting.org")
    :target
    (file+head
     "bahai/%<%Y%m%d%H%M>.org"
     ,(concat
       "#+category: Bahá’í\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :bahai:\n"
       "#+startup: showeverything\n"
       "#+title: %^{Purpose of meeting}\n"))
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("ba" "Assembly meeting" plain
    (file "~/org/template/bahai/meeting/assembly-meeting.org")
    :target
    (file+head
     "assembly/%<%Y%m%d%H%M>-local-spiritual-assembly.org"
     ,(concat
       "#+category: Assembly\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :todo:assembly:\n"
       "#+title: Local Spiritual Assembly\n"))
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ;; ,(org-config-bahai-meeting "bc" "C2G Admin" "c2g-admin.org")
   ,(org-config-bahai-meeting "bD" "National Convention Delegate Report"
                              "national-convention-delegate-report.org")
   ,(org-config-bahai-meeting "bf" "Ali Nakhjavani Development Fund"
                              "ali-nakhjavani-development-fund.org")
   ,(org-config-bahai-meeting "bF" "Regional Council and the Flow of Guidance"
                              "regional-council-and-flow-of-guidance.org")
   ,(org-config-bahai-meeting "bn" "National Treasurer's Office"
                              "national-treasurers-office.org")
   ,(org-config-bahai-meeting "br" "Regional Treasurer's Office"
                              "regional-treasurers-office.org")
   ,(org-config-bahai-meeting "bi" "Institute Day" "institute-day.org")
   ,(org-config-bahai-meeting "bI" "Institute Day Reflection"
                              "institute-day-reflection.org")
   ,(org-config-bahai-meeting "bT" "Tutor Training" "tutor-training.org")
   ,(org-config-bahai-meeting "bu" "Unit Convention" "unit-convention.org")
   ,(org-config-bahai-meeting "bc" "Cluster Agencies" "cluster-agencies.org")
   ,(org-config-bahai-meeting "bA" "Arden Team Reflection"
                              "arden-team-reflection.org")
   ,(org-config-bahai-meeting "bS" "Institute Coordinators"
                              "institute-coordinators.org")

   ("w" "Work templates")

   ("wn" "Work Note" plain "%?"
    :target
    (file+head
     "kadena/%<%Y%m%d%H%M>.org"
     ,(concat "#+category: Kadena\n"
              "#+filetags: :kadena:\n"
              "#+title: ${title}\n"))
    :immediate-finish t
    :jump-to-captured t
    :empty-lines-before 1
    :unnarrowed t)

   ("wm" "Work Meeting" plain
    (file "~/org/template/meeting.org")
    :target
    (file+head
     "meeting/%<%Y%m%d%H%M>.org"
     ,(concat
       "#+category: Kadena\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :kadena:\n"
       "#+startup: showeverything\n"
       "#+title: %^{Purpose of meeting}\n"))
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ("wT" "Work Team Member" plain
    (file "~/org/template/kadena/team-member.org")
    :target
    (file "kadena/team/%<%Y%m%d%H%M>.org")
    :immediate-finish t
    :jump-to-captured t
    :unnarrowed t
    :no-save t)

   ,(org-config-kadena-meeting "wM" "Marketing <> Eng"  "marketing-eng.org")
   ,(org-config-kadena-meeting "wO" "Ops <> Eng"        "ops-eng.org")
   ,(org-config-kadena-meeting "wP" "Product <> Eng"    "product-eng.org")
   ,(org-config-kadena-meeting "wb" "BD <> Eng"         "bd-eng.org")
   ,(org-config-kadena-meeting "wp" "PM <> Eng"         "pm-eng.org")

   ,(org-config-kadena-meeting "wC" "Work Conference"   "conference.org")
   ,(org-config-kadena-meeting "wF" "Offsite Meeting"   "offsite.org")
   ,(org-config-kadena-meeting "wa" "All Hands"         "all-hands.org")
   ,(org-config-kadena-meeting "we" "EVM Posse"         "evm-posse.org")
   ,(org-config-kadena-meeting "wL" "EVM Product Leads" "evm-product-leads.org")
   ,(org-config-kadena-meeting "wj" "JS Team"           "js-team.org")
   ,(org-config-kadena-meeting "wl" "Leads Strategy"    "leads-strategy.org")
   ,(org-config-kadena-meeting "wE" "Eng Managers"      "eng-managers.org")
   ,(org-config-kadena-meeting "ws" "Eng Standup"       "eng-standup.org")
   ,(org-config-kadena-meeting "wt" "CTO Meeting"       "cto.org")

   ("wh" "Hack-a-chain")

   ,(org-config-kadena-meeting "whr" "Hack-a-chain Indexer"
                               "hackachain-indexer-review.org")
   ,(org-config-kadena-meeting "whs" "Hack-a-chain Standup"
                               "hackachain-internal-standup.org")

   ("wo" "1-on-1s")

   ("woo" "1-on-1 meeting" plain
    (file "~/org/template/kadena/one-on-one.org")
    :target
    (file+head
     "meeting/%<%Y%m%d%H%M>-1-on-1.org"
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

   ("woa" "Names beginning with A")
   ,(org-config-1-on-1-from-name "Albert Groothedde")
   ,(org-config-1-on-1-from-name "Anastasia Bez")
   ,(org-config-1-on-1-from-name "Annelise Osborne")

   ("woe" "Names beginning with E")
   ,(org-config-1-on-1-from-name "Edmund Noble")

   ("woh" "Names beginning with H")
   ,(org-config-1-on-1-from-name "Hafsah Asmat")

   ("woj" "Names beginning with J")
   ,(org-config-1-on-1-from-name "Javad Khalilian")
   ,(org-config-1-on-1-from-name "Jesse Marquez")
   ,(org-config-1-on-1-from-name "John Frost")
   ,(org-config-1-on-1-from-name "Jose Cardona")
   ,(org-config-1-on-1-from-name "June Boston")

   ("wol" "Names beginning with L")
   ,(org-config-1-on-1-from-name "Lars Kuhtz")
   ,(org-config-1-on-1-from-name "Leah Bingham")
   ,(org-config-1-on-1-from-name "Linda Ortega")
   ,(org-config-1-on-1-from-name "Lisa Gunn")
   ,(org-config-1-on-1-from-name "Louis Page")

   ("wom" "Names beginning with M")
   ,(org-config-1-on-1-from-name "Mike Herron")

   ("wor" "Names beginning with R")
   ,(org-config-1-on-1-from-name "Robert Soeldner")

   ("wos" "Names beginning with S")
   ,(org-config-1-on-1-from-name "Stuart Popejoy")

   ("wow" "Names beginning with W")
   ,(org-config-1-on-1-from-name "Will Martino")
   )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 org-roam-dailies-capture-templates
 '(("d" "default" entry "* %U %?"
    :target (file+head "%<%Y-%m-%d>.org"
                       "#+title: %<%Y-%m-%d>\n")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

 org-agenda-custom-commands
 `(("a" "Agenda\n"
    ((agenda
      ""
      ((org-agenda-skip-function
        '(org-config-agenda-skip-entry-if
          (and (org-ext-habit-p)
               (org-review-last-review-prop nil)
               (not (org-ext-needs-review-p)))))
       (org-super-agenda-groups
        '((:name "Important"  :and (:priority "A" :not (:habit t)))
          (:name "Overdue"    :deadline past)
          (:name "Due Soon"   :deadline future)
          (:name "Reschedule" :and (:scheduled past :not (:habit t)))
          (:name "Review"     :and (:todo ("WAIT" "TASK" "DOING")
                                          :not (:priority "C")))
          (:name "Calls"      :tag "Call")
          (:name "Errands"    :tag "Errand")
          (:name "Tasks"      :not (:habit t))
          (:name "Habits"     :habit t)
          ))))
     (alltodo
      ""
      ((org-agenda-overriding-header "\nItems needing review")
       (org-agenda-skip-function
        '(org-config-agenda-skip-entry-if
          (or (org-ext-habit-p)
              (org-agenda-skip-entry-if
               'scheduled 'deadline 'timestamp
               'todo org-done-keywords)
              (org-agenda-skip-entry-if 'todo '("DEFER"))
              (org-config-skip-if-review-not-needed)
              (org-config-skip-if-regularly-reviewed))))
       ;; (org-agenda-cmp-user-defined 'org-config-review-compare)
       (org-agenda-max-entries 38)
       ;; (org-agenda-cmp-user-defined (org-compare-randomly))
       (org-agenda-cmp-user-defined (org-config-compare-items-needing-review))
       (org-compare-random-refresh t)
       (org-agenda-prefix-format ,org-config-check-if-scheduled)
       (org-agenda-sorting-strategy '(user-defined-down))
       (org-overriding-columns-format ,org-config-standard-columns)))
     ))

   ("u" "Unfiled" tags "CATEGORY={Inbox\\|Pending\\|Drafts}&TODO<>\"SCRAP\"&LEVEL=2")
   ("n" "Notes"   todo "NOTE")
   ("l" "Links"   todo "LINK")

   ("A" "Events/Appointments" todo "APPT")

   (":" "With TAGS"      ,(org-config-call-only #'org-config-tags-search))
   ("c" "With CATEGORY"  ,(org-config-call-only #'org-config-category-search))
   ("C" "With CATEGORY+" ,(org-config-call-only #'org-config-raw-category-search))
   ("k" "With KEYWORD"   ,(org-config-call-only #'org-config-keyword-search))
   ("i" "With ITEM"      ,(org-config-call-only #'org-config-item-search))

   ("g" . "Org-ql queries")

   ("gg" "Regexp all tasks, all files (SLOW)"
    ,(org-config-call-only #'org-config-text-search))

   ("go" "Open source tasks"
    ((org-ql-block
      `(and (or (path "OSS")
                (category "Computer"))
            (todo "TODO" "DOING")
            (not (tags "ARCHIVE"))
            (not (scheduled))
            (property-ts "NEXT_REVIEW" :to ,(format-time-string "%Y-%m-%d")))
      ((org-ql-block-header "Open source tasks")))))

   ("gw" "Work tasks (needing to be seen)"
    ((org-ql-block
      `(and (about "kadena")
            (not (about ,@org-config-categories-regularly-reviewed))
            (todo "TODO" "DOING" "WAIT" "TASK")
            (not (tags "ARCHIVE"))
            (not (scheduled))
            (property-ts "NEXT_REVIEW" :to ,(format-time-string "%Y-%m-%d")))
      ((org-ql-block-header "Work tasks")))))

   ("gW" "Work tasks (all)"
    ((org-ql-block
      `(and (about "kadena")
            (todo "TODO" "DOING" "WAIT" "TASK")
            (not (tags "ARCHIVE"))
            (not (scheduled))
            (property-ts "NEXT_REVIEW" :to ,(format-time-string "%Y-%m-%d")))
      ((org-ql-block-header "Work tasks")))))

   ("gU" "Unnecessary wording"
    ((org-ql-block
      '(and (heading-regexp "[^\"#-]\\<\\(the\\|an?\\)\\>")
            (todo))
      ((org-ql-block-header "Tasks with unnecessary wording")))))

   ("gf" "Tasks for..." ,(org-config-call-only #'org-config-tasks-for-query))

   ("r" . "Review tasks\n")

   ("rr" "Tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-ext-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)
           (org-config-skip-if-regularly-reviewed)))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format ,org-config-columns-for-reviewed)
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format ,org-config-standard-columns)))

   ("rR" "All tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)))
     (org-agenda-prefix-format ,org-config-check-if-scheduled)
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format ,org-config-standard-columns)))

   ("r*" "All tasks" alltodo ""
    ((org-agenda-prefix-format ,org-config-check-if-scheduled)
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format ,org-config-standard-columns)))

   ("rn" "Next Actions" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (or (not (org-ext-subtask-p))
            (org-ext-has-preceding-todo-p))))))

   ("rp" "Projects" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (not (org-ext-top-level-project-p))))))

   ("r!" "Stuck projects" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (or (not (org-ext-top-level-project-p))
            (org-ext-first-child-todo
             #'(lambda () (org-get-scheduled-time (point)))))))))

   ("r@" "Waiting/delegated" todo "WAIT|TASK"
    ((org-agenda-sorting-strategy
      '(todo-state-up priority-down category-up))))

   ("r>" "Deferred" todo "DEFER"
    ((org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("r#" "Habits" todo "HABIT"
    ((org-agenda-prefix-format ,org-config-check-if-scheduled)
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format ,org-config-standard-columns)))

   ("ru" "Unscheduled tasks" alltodo ""
    ((org-agenda-skip-function
      '(org-agenda-skip-entry-if
        'scheduled 'deadline 'timestamp
        'todo org-done-keywords))
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("rU" "Tasks never reviewed" alltodo ""
    ((org-agenda-skip-function
      '(or (org-agenda-skip-entry-if 'todo org-done-keywords)
           (org-config-skip-if-reviewed)))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format ,org-config-check-if-scheduled)
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format ,org-config-standard-columns)))

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
        (not (org-ext-subtask-p))))))

   ("rl" "Tasks with long headlines" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (<= (length (replace-regexp-in-string "\\[\\[.+?\\]\\[\\(.+?\\)\\]\\]"
                                              "\\1" (org-get-heading t)))
            72)))))
   ))

(defun org-config-find (query &optional arg)
  (interactive "sQuery: \nP")
  (org-ql-search (org-agenda-files)
    `(and ,(if arg
               '(todo)
             '(or (todo)
                  (todo "NOTE")))
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

(defun org-config-show-tasks-with-filetags (_tag)
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

(defun org-config-show-invalid ()
  (interactive)
  (org-ql-search (org-ql-search-directories-files
                  :directories (list org-directory))
    '(and (not (todo))
          (property "Effort"))
    :sort '(scheduled todo)))

(provide 'org-config)

;;; org-config.el ends here
