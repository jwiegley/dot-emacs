;;; my-gnus-score --- Helper functions and variables to setup Gnus scoring

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 06 Jun 2012
;; Version: 1.0
;; Keywords: gnus scoring adaptive
;; X-URL: https://github.com/jwiegley/my-gnus-score

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

;; Here's how these scoring rules work:
;;
;;  - If you type 'c y' to catch-up a group and don't read certain
;;    threads at all, you should never see those threads again (unless
;;    some manual scoring rule applies in the future, or an author in
;;    the thread gets boosted later because you keep reading his or her
;;    posts).
;;
;;  - Use 'I A', 'I S' or 'I T' to manually boost authors, subjects and
;;    threads.  This interacts well with adaptive scoring, and guides
;;    it.
;;
;;  - If you dormant (?) an article, the subject *and* the author get a
;;    small boost.  But be aware that if dormant one article in a large
;;    thread, but don't read any of the other articles, you'll likely
;;    still not see that thread in future.
;;
;;  - If you tick (!) an article, the subject is boosted the same as if
;;    you read the article (using SPC).
;;
;;  - If you delete an article (using 'd'), the subject gets dinged the
;;    same as if you had caught-up the group without reading it.  This
;;    is the right way to "unread" an article, from the point of view of
;;    these adaptive scoring rules.
;;
;;  - If you kill an article or thread (using 'C-k'), it *seriously*
;;    dings the subject.  This is the way to drop a thread that got
;;    otherwise up-scored because of other scoring rules.
;;
;;  - If you mark an article as expirable (using 'E'), both the subject
;;    and the author are hugely dinged.  I impart this special meaning
;;    to the expirable mark because I don't use expirable marks for any
;;    other purpose (I use total expiry, or external expiration in tools
;;    like Leafnode).
;;
;;  - Scoring rules will decay after 30 days if they are not triggered
;;    again.  If a rule does get triggered, the 30 day counter resets.
;;    _Adaptive_ scoring rules are further "decayed" every day, so that
;;    they slowly migrate toward becoming disabled, rather than simply
;;    the "on/off" switch after 30 days that applies to normal scoring
;;    rules.
;;
;;  - If any article's score ends up beneath 0 -- but above
;;    `my-gnus-summary-expunge-below' -- it will still be in the
;;    *Summary* buffer, it just won't be visible.  Use '/ w' to reveal
;;    these silent articles.
;;
;;  - If any article's score ends up beneath
;;    `my-gnus-summary-expunge-below', it will not be in the *Summary*
;;    before at all.  You'll have to use '/ o' to pull in old articles
;;    to see these expunged articles (NOTE: This is not the same as
;;    IMAP's meaning of 'expunge', it just means it's not in the summary
;;    buffer at all).
;;
;; Some guidelines about proper using of scoring in Gnus:
;;
;; 1. Decide exactly which groups you will score in.  Configure
;;    `my-gnus-score-groups-regex' to reflect this.  For example, I only
;;    score for mailing lists and newsgroups.  Anything else, such as
;;    personal mail, should never see articles silently disappear from
;;    the *Summary* buffer.
;;
;; 2. Use manual scoring if necessary.  By default, this module uses
;;    adaptive scoring so that if you ignore threads, they ignore you
;;    right back.  But if you run across an author you really like, use
;;    'I A' to manually boost that person.  This may show you followups
;;    in future to threads you're currently ignoring.

;;; Code:

(eval-when-compile
  (require 'gnus-start))

(require 'gnus-sum)
(require 'gnus-score)

(defgroup my-gnus-score nil
  "Helper functions and variables to setup Gnus scoring"
  :group 'gnus-score)

;;; Helper functions:

(defun my-gnus-score-setter (symbol value)
  (set symbol value)
  (set (intern-soft (substring (symbol-name symbol) 3)) value))

(defmacro my-gnus-score-defcustom (varname value)
  `(defcustom ,(intern (concat "my-" (symbol-name varname))) ,value
     (documentation-property (quote ,varname) 'variable-documentation)
     :set 'my-gnus-score-setter
     :group 'my-gnus-score
     :type (plist-get (symbol-plist (quote ,varname)) 'custom-type)))

(put 'my-gnus-score-defcustom 'lisp-indent-function 1)

(font-lock-add-keywords
 'emacs-lisp-mode
 '(("(my-gnus-score-defcustom\\>" . font-lock-keyword-face)))

;;; Customization variables:

(defcustom my-gnus-score-groups-regex
  "\\`\\(list\\.\\|nntp\\+LocalNews:\\|nnvirtual:\\)"
  "Regexp to match groups where scoring should be performed."
  :type 'regexp
  :group 'my-gnus-score)

;;; Customization variable overrides:

;; These "overrides" specify the defaults that I have found useful over the
;; past 12 years.  I've had little reason to change them in all that time.

(my-gnus-score-defcustom gnus-default-adaptive-score-alist
  '((gnus-dormant-mark   (from 20)
                         (subject 100))
    (gnus-ticked-mark    (subject 30))
    (gnus-read-mark      (subject 30))
    (gnus-del-mark       (subject -150))
    (gnus-catchup-mark   (subject -150))
    (gnus-killed-mark    (subject -1000))
    (gnus-expirable-mark (from -1000)
                         (subject -1000))))

(my-gnus-score-defcustom gnus-score-default-duration  'p)
(my-gnus-score-defcustom gnus-score-expiry-days 30)

(my-gnus-score-defcustom gnus-thread-sort-functions
  '(gnus-thread-sort-by-most-recent-number
    gnus-thread-sort-by-score))

(my-gnus-score-defcustom gnus-use-adaptive-scoring '(line))
(my-gnus-score-defcustom gnus-summary-expunge-below -100)
(my-gnus-score-defcustom gnus-thread-expunge-below -1000)
(my-gnus-score-defcustom gnus-score-thread-simplify nil)
(my-gnus-score-defcustom gnus-decay-scores "\\.ADAPT\\'")

;;; Functions:

(defun my-gnus-score-group-p (&optional group)
  (string-match my-gnus-score-groups-regex (or group gnus-newsgroup-name "")))

(defun my-gnus-score-groups (&optional arg)
  (interactive)
  (save-excursion
    (dolist (info (cdr gnus-newsrc-alist))
      ;; Only consider this group if it's at or below the current level
      (when (<= (gnus-info-level info)
                (if (numberp arg)
                    arg
                  (or (gnus-group-default-level nil t)
                      (funcall
                       (symbol-function 'gnus-group-default-list-level))
                      gnus-level-subscribed)))
        (let* ((group (gnus-info-group info))
               (unread (gnus-group-unread group)))
          (when (and (numberp unread) (> unread 0)
                     (my-gnus-score-group-p group))
            (ignore-errors
              (gnus-summary-read-group group nil t))
            (when (and gnus-summary-buffer
                       (buffer-live-p gnus-summary-buffer)
                       (eq (current-buffer)
                           (get-buffer gnus-summary-buffer)))
              (gnus-summary-exit))))))))

;; Increase Score for all follow-ups to my own articles (can't
;; use message-id for scoring since it is changed later by
;; my news feed)
(defun hcz-gnus-score-followup (&optional score)
  "Add SCORE to all later articles in the thread the current
buffer is part of.  This version is for cases where the own
message-id will later be rewritten upstream.  It scores on the
message-id of the parent article (which has nearly the same eff
ect but also scores parallel replies).  If there is no parent
article (we are opening a thread), score on subject is done
instead."
  (interactive "P")
  (setq score (gnus-score-delta-default score))
  (when (gnus-buffer-live-p gnus-summary-buffer)
    (save-excursion
      (save-restriction
        (message-narrow-to-headers)
        (let ((refs (mail-fetch-field "references")))
          (if (and refs (string-match "\\(<[^<]+>\\)\\'" refs))
              (progn
                (set-buffer gnus-summary-buffer)
                (gnus-summary-score-entry
                 "references" (format "%s" (match-string 1 refs)) 's
                 score (current-time-string)))
            ;; if we didn't find a reference (probably due to no parent
            ;; article), we increase the score on subject:
            (let ((subj (mail-fetch-field "subject")))
              (when subj
                (set-buffer gnus-summary-buffer)
                (gnus-summary-score-entry
                 "subject" subj 's
                 score (current-time-string))))))))))

(defun my-gnus-score-followup (&optional score)
  (when (my-gnus-score-group-p)
    (gnus-score-followup-article score)
    (gnus-score-followup-thread score)
    (hcz-gnus-score-followup score)))

;; Install into Gnus

(defadvice gnus-score-adaptive (around my-gnus-score-adaptive activate)
  "Create adaptive score rules for this newsgroup, if applicable."
  (if (my-gnus-score-group-p)
      ad-do-it))

(add-hook 'message-sent-hook 'my-gnus-score-followup)

(eval-after-load "gnus-group"
  '(define-key gnus-group-score-map [?s] 'my-gnus-score-groups))

(provide 'my-gnus-score)

;;; my-gnus-score.el ends here
