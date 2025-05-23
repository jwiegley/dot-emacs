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
(require 'org-agenda-random)
(eval-when-compile
  (require 'org-habit))

(defgroup org-config nil
  "Configurations for Org-mode and related packages"
  :group 'org)

(defconst org-config-open-re "/TODO|DOING|WAIT|TASK|HABIT")
(defconst org-config-closed-re "/TODO/DONE|CANCELED|PASS")

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

(defconst org-config-names-regularly-reviewed
  '(
    "Albert"
    "Annelise"
    "Bez"
    "Brittaney"
    "Emily"
    "Javad"
    "Jesse"
    "June"
    "Lars"
    "Leah"
    "Randy"
    "Stuart"
    "Travis"
    ))

(defconst org-config-categories-regularly-reviewed
  (append org-config-names-regularly-reviewed
          '("EVM"
            "PM"
            "JS"
            "Core")))

(defsubst org-config-skip-if-regularly-reviewed ()
  (org-config-agenda-skip-entry-if
   (let ((tags (org-get-tags))
         (category (org-get-category)))
     (or (cl-intersection org-config-names-regularly-reviewed tags
                          :test #'string=)
         (member category org-config-categories-regularly-reviewed)))))

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

(defun org-config-meeting-template (keys title file dir &optional slug)
  `(,keys ,title plain
          (file ,(expand-file-name file dir))
          :target (file ,(concat "meeting/%<%Y%m%d%H%M>-"
                                 (or slug "") file))
          :immediate-finish t
          :jump-to-captured t
          :unnarrowed t
          :no-save t))

(defun org-config-kadena-meeting (keys title file)
  (org-config-meeting-template keys title file "~/org/template/kadena/meetings"))

(defun org-config-kadena-1-on-1 (keys title file)
  (org-config-meeting-template keys title file "~/org/template/kadena/one-on-one"
                               "1-on-1-"))

(defun org-config-bahai-meeting (keys title file)
  (org-config-meeting-template keys title file "~/org/template/bahai/meetings"))

(setq
 org-capture-templates
 (let ((Inbox '(function org-extra-goto-inbox-heading)))
   `(("a" "TODO" entry
      ,Inbox
      "* TODO %?\nSCHEDULED: %t"
      :prepend t)

     ("h" "HABIT" entry
      (file+headline ,(org-file "habits.org") "Personal")
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

     ;;      ("i" "Inbox" entry ,Inbox
     ;;       "* TODO %?\n%i\n%U"
     ;;       :kill-buffer t)
     ;;      ("l" "Inbox with link" entry ,Inbox
     ;;       "* TODO %?
     ;; :PROPERTIES:
     ;; :URL:      %a
     ;; :DATE:     %U
     ;; :END:
     ;; %(with-temp-buffer
     ;;   (insert \"%i\")
     ;;   (fill-region (point-min) (point-max))
     ;;   (buffer-string))"
     ;;       :kill-buffer t)

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
SCHEDULED: %t
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
     "meeting/%<%Y%m%d%H%M>.org"
     ,(concat
       "#+category: Meeting\n"
       "#+date: %(setq my/org-start-date (my/org-read-date t))\n"
       "#+filetags: :kadena:\n"
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
     "meeting/%<%Y%m%d%H%M>.org"
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
    (file "~/org/template/bahai/meetings/assembly-meeting.org")
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

   ,(org-config-bahai-meeting "bc" "C2G Admin" "c2g-admin.org")
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
   ,(org-config-bahai-meeting "bi" "Ruhi Intensive" "ruhi-intensive.org")
   ,(org-config-bahai-meeting "bI" "Ruhi Intensive Reflection"
                              "ruhi-intensive-reflection.org")
   ,(org-config-bahai-meeting "bu" "Unit Convention" "unit-convention.org")

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

   ,(org-config-kadena-meeting "wa"  "All Hands"            "all-hands.org")
   ,(org-config-kadena-meeting "wb"  "BD <> Engineering"    "bd-engineering.org")
   ,(org-config-kadena-meeting "wS"  "Ops <> Engineering"   "ops-engineering.org")
   ,(org-config-kadena-meeting "wC"  "Work Conference"      "conference.org")
   ,(org-config-kadena-meeting "wO"  "Offsite Meeting"      "offsite.org")
   ,(org-config-kadena-meeting "wt"  "CTO Meeting"          "cto.org")
   ,(org-config-kadena-meeting "ws"  "Eng Standup"          "eng-standup.org")
   ,(org-config-kadena-meeting "wM"  "Eng Managers"         "eng-managers.org")
   ,(org-config-kadena-meeting "we"  "EVM Posse"            "evm-posse.org")

   ("wh" "Hack-a-chain")

   ,(org-config-kadena-meeting "whr" "Hack-a-chain Indexer" "hackachain-indexer-review.org")
   ,(org-config-kadena-meeting "whs" "Hack-a-chain Standup" "hackachain-internal-standup.org")
   ,(org-config-kadena-meeting "wj" "JS Team"               "js-team.org")
   ,(org-config-kadena-meeting "wP" "John <> PM Team"       "john-pm-team.org")
   ,(org-config-kadena-meeting "wl" "Leads Strategy"        "leads-strategy.org")
   ,(org-config-kadena-meeting "wp" "Pact Posse"            "pact-posse.org")

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

   ,(org-config-kadena-1-on-1 "woab" "1-on-1 Anastasia Bez" "anastasia-bez.org")
   ,(org-config-kadena-1-on-1 "woag" "1-on-1 Albert Groothedde" "albert-groothedde.org")
   ,(org-config-kadena-1-on-1 "woao" "1-on-1 Annelise Osborne" "annelise-osborne.org")

   ("woe" "Names beginning with E")

   ,(org-config-kadena-1-on-1 "woen" "1-on-1 Edmund Noble" "edmund-noble.org")
   ,(org-config-kadena-1-on-1 "woep" "1-on-1 Emily Pillmore" "emily-pillmore.org")

   ("woh" "Names beginning with H")

   ,(org-config-kadena-1-on-1 "woha" "1-on-1 Hafsah Asmat" "hafsah-asmat.org")

   ("woj" "Names beginning with J")

   ,(org-config-kadena-1-on-1 "wojb" "1-on-1 June Boston" "june-boston.org")
   ,(org-config-kadena-1-on-1 "wojc" "1-on-1 Jose Cardona" "jose-cardona.org")
   ,(org-config-kadena-1-on-1 "wojm" "1-on-1 Jesse Marquez" "jesse-marquez.org")

   ("wol" "Names beginning with L")

   ,(org-config-kadena-1-on-1 "wolb" "1-on-1 Leah Bingham" "leah-bingham.org")
   ,(org-config-kadena-1-on-1 "wolk" "1-on-1 Lars Kuhtz" "lars-kuhtz.org")
   ,(org-config-kadena-1-on-1 "wolg" "1-on-1 Lisa Gunn" "lisa-gunn.org")
   ,(org-config-kadena-1-on-1 "wolo" "1-on-1 Linda Ortega" "linda-ortega.org")

   ("wor" "Names beginning with R")

   ,(org-config-kadena-1-on-1 "wors" "1-on-1 Robert Soeldner" "robert-soeldner.org")

   ("wos" "Names beginning with S")

   ,(org-config-kadena-1-on-1 "wosp" "1-on-1 Stuart Popejoy" "stuart-popejoy.org")

   ("wow" "Names beginning with W")

   ,(org-config-kadena-1-on-1 "wowm" "1-on-1 Will Martino" "will-martino.org")
   )

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
     ;;    "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     ;;   (org-agenda-sorting-strategy '(user-defined-down))
     ;;   (org-overriding-columns-format
     ;;    "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))
     ))

   ("u" "Unfiled" tags "CATEGORY={Inbox\\|Pending}&LEVEL=2")

   ("n" "Notes" todo "NOTE")

   ("l" "Links" todo "LINK")

   (":" "With tags match"
    (lambda (arg)
      (call-interactively #'org-config-with-tags-search nil)))

   ("c" "With category"
    (lambda (arg)
      (call-interactively #'org-config-with-category-search nil)))

   ("k" "With keyword"
    (lambda (arg)
      (call-interactively #'org-config-with-keyword-search nil)))

   ("i" "With item"
    (lambda (arg)
      (call-interactively #'org-config-with-item-search nil)))

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
      "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rR" "Tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)
           (org-config-skip-if-regularly-reviewed)))
     (org-agenda-cmp-user-defined 'org-config-review-compare)
     (org-agenda-prefix-format
      "%-10c%-2(or (org-entry-get nil \"REVIEWS\") \" \")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rr" "Tasks needing review (random sampling)" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)
           (org-config-skip-if-regularly-reviewed)))
     (org-agenda-max-entries 38)
     (org-agenda-cmp-user-defined (org-compare-randomly))
     (org-agenda-prefix-format
      "%-10c%-2(or (org-entry-get nil \"REVIEWS\") \" \")")
     (org-compare-random-refresh t)
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rZ" "All tasks needing review" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)))
     (org-agenda-prefix-format
      "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("rz" "All tasks needing review (random sampling)" alltodo ""
    ((org-agenda-skip-function
      '(or (org-config-agenda-skip-entry-if
            (org-extra-subtask-p))
           (org-agenda-skip-entry-if
            'scheduled 'deadline 'timestamp
            'todo org-done-keywords)
           (org-config-skip-if-review-not-needed)))
     (org-agenda-prefix-format
      "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-max-entries 20)
     (org-agenda-cmp-user-defined (org-compare-randomly))
     (org-compare-random-refresh t)
     (org-agenda-sorting-strategy '(user-defined-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

   ("r*" "All tasks (for confirmation)" alltodo ""
    ((org-agenda-prefix-format
      "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
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

   ("r!" "Stuck projects" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (or (not (org-extra-top-level-project-p))
            (org-extra-first-child-todo
             #'(lambda () (org-get-scheduled-time (point)))))))))

   ("r@" "Waiting/delegated" todo "WAIT|TASK"
    ((org-agenda-sorting-strategy
      '(todo-state-up priority-down category-up))))

   ("r>" "Deferred" todo "DEFER"
    ((org-agenda-sorting-strategy '(user-defined-up))
     (org-agenda-prefix-format "%-10c%5(org-todo-age) ")))

   ("r#" "Habits" todo "HABIT"
    ((org-agenda-prefix-format
      "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(category-up))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

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
     (org-agenda-prefix-format
      "%-10c%-2(or (and (org-entry-get nil \"SCHEDULED\") \"✓\") \"\")")
     (org-agenda-sorting-strategy '(user-defined-down))
     (org-overriding-columns-format
      "%9CATEGORY %52ITEM(Task) %LAST_REVIEW %NEXT_REVIEW")))

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

   ("rl" "Tasks with long headlines" alltodo ""
    ((org-agenda-skip-function
      '(org-config-agenda-skip-entry-if
        (<= (length (replace-regexp-in-string "\\[\\[.+?\\]\\[\\(.+?\\)\\]\\]"
                                              "\\1" (org-get-heading t))) 72)))))))

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
