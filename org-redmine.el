;;; org-redmine.el --- Org-mode interaction with Redmine tasks

;; Copyright (C) 2011 John Wiegley <johnw@gnu.org>

;; Emacs Lisp Archive Entry
;; Filename: org-redmine.el
;; Version: 0.1
;; Keywords: org-mode
;; Author: John Wiegley <johnw@gnu.org>
;; Maintainer: John Wiegley <johnw@gnu.org>
;; Description: Adds public key encryption to org-mode buffers
;; URL: http://www.newartpisans.com/software/emacs.html
;; Compatibility: Emacs23

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;; MA 02111-1307, USA.

;;; Commentary:

(require 'org-parse)

(defcustom org-redmine-id 13
  "The user id to create new bugs under in Redmine."
  :type 'integer
  :group 'org)

(defcustom org-redmine-url "https://hub.boostpro.com"
  "The URL to use when talking to Redmine."
  :type 'string
  :group 'org)

(defcustom org-redmine-api-key "f3dc6c4da15cf001cce6dd775452b576bd07feb5"
  "The API key to use when talking to Redmine."
  :type 'string
  :group 'org)

(defcustom org-redmine-projects '(("IT" . "it"))
  "Redmine projects list."
  :type '(alist :key-type string :value_type string)
  :group 'org)

(defcustom org-redmine-trackers '(("Support" . 3)
                                  ("Feature" . 2)
                                  ("Bug"     . 1))
  "An alist of all the trackers on the Redmine installation."
  :type '(alist :key-type string :value-type integer)
  :group 'org)

(defcustom org-redmine-priorities '(("Immediate" . 1)
                                    ("Urgent"    . 2)
                                    ("High"      . 3)
                                    ("Normal"    . 4)
                                    ("Low"       . 5))
  "An alist of all the priorities on the Redmine installation."
  :type '(alist :key-type string :value-type integer)
  :group 'org)

(defcustom org-redmine-statuses '(("TODO"     . ("New"         . 1))
                                  ("STARTED"  . ("In Progress" . 2))
                                  ("DONE"     . ("Resolved"    . 3))
                                  ("WAITING"  . ("Feedback"    . 4))
                                  (nil        . ("Closed"      . 5))
                                  ("CANCELED" . ("Rejected"    . 6)))
  "An alist of all the statuses on the Redmine installation.
These are keyed by the related Org mode state."
  :type '(alist :key-type string :value-type integer)
  :group 'org)

(defun org-redmine-convert-priority (org-priority)
  "Translate an Org-mode priority character into a Redmine priority id."
  (let ((org-priority (nth 3 (org-heading-components))))
    (cond
     ((and org-priority (= ?A org-priority))
      (cdr (assoc "High" org-redmine-priorities)))
     ((and org-priority (= ?C org-priority))
      (cdr (assoc "Low" org-redmine-priorities)))
     (t
      (cdr (assoc "Normal" org-redmine-priorities))))))

(defun org-redmine-todo-description ()
  (let ((contents
         (buffer-substring-no-properties (org-entry-beginning-position)
                                         (org-entry-end-position))))
    (with-temp-buffer
      (insert contents)

      (goto-char (point-min))
      (delete-region (point) (1+ (line-end-position)))
      (search-forward ":PROP")
      (delete-region (match-beginning 0) (point-max))
      (goto-char (point-min))
      (while (re-search-forward "^   " nil t)
        (delete-region (match-beginning 0) (match-end 0)))
      (goto-char (point-min))
      (while (re-search-forward "^SCHE" nil t)
        (delete-region (match-beginning 0) (1+ (line-end-position))))
      (goto-char (point-min))
      (if (eobp)
          ""
        (buffer-string)))))

(defun org-redmine-rest-api (type url &optional input params)
  (with-temp-buffer
    (if input (insert input))
    (shell-command-on-region
     (point-min) (point-max)
     (format (concat
              "curl -s -k -X %s %s "
              "-H 'Content-type: text/xml' -H 'Accept: text/xml' "
              "'%s/%s?%s%sformat=xml&key=%s'")
             type (if (string= type "GET") "" "-d @-")
             org-redmine-url url (or params "") (if params "&" "")
             org-redmine-api-key)
     nil t)
    (goto-char (point-min))
    (skip-syntax-forward " ")
    (unless (eobp)
      (nthcdr 2 (car (xml-parse-region (point-min) (point-max)))))))

;; ((id nil "744")
;;  (project ((name . "IT") (id . "5")))
;;  (tracker ((name . "Support") (id . "3")))
;;  (status ((name . "New") (id . "1")))
;;  (priority ((name . "Low") (id . "3")))
;;  (author ((name . "Dave Abrahams") (id . "3")))
;;  (assigned_to ((name . "John Wiegley") (id . "13")))
;;  (subject nil "Enable issue updates via email")
;;  (description nil "I think this would make our Redmine installation much nicer to use: http://www.redmine.org/projects/redmine/wiki/RedmineReceivingEmails")
;;  (start_date nil "2011-07-14")
;;  (due_date nil)
;;  (done_ratio nil "0")
;;  (estimated_hours nil)
;;  (spent_hours nil "0.0")
;;  (created_on nil "2011-07-14T13:22:38-07:00")
;;  (updated_on nil "2011-07-24T23:02:24-07:00")
;;  (journals ((type . "array"))
;;            (journal
;;             ((id . "2055"))
;;             (user ((name . "John Wiegley") (id . "13")))
;;             (notes nil "I do have a command-line utility right now that lets you add new tasks to Redmine with surpassing ease.  I just haven't integrated it with Org-mode yet, the way I have for a similar script I use with Bugzilla.")
;;             (created_on nil "2011-07-14T13:35:56-07:00")
;;             (details ((type . "array"))))
;;            (journal
;;             ((id . "2056"))
;;             (user ((name . "Dave Abrahams") (id . "3")))
;;             (notes nil "Thanks, but that doesn't address the desire here.  I get updates in my email already; I want to be able to reply there.  I also want this capability for \"regular users\" who aren't going to fire up the script.")
;;             (created_on nil "2011-07-14T13:48:18-07:00")
;;             (details ((type . "array"))))
;;            (journal
;;             ((id . "2057"))
;;             (user ((name . "John Wiegley") (id . "13")))
;;             (notes nil "I see.")
;;             (created_on nil "2011-07-14T14:00:07-07:00")
;;             (details ((type . "array"))))
;;            (journal
;;             ((id . "2069"))
;;             (user ((name . "John Wiegley") (id . "13")))
;;             (notes nil)
;;             (created_on nil "2011-07-24T23:02:24-07:00")
;;             (details ((type . "array"))
;;                      (detail ((name . "tracker_id") (property . "attr"))
;;                              (old_value nil "2")
;;                              (new_value nil "3"))))))

;; ((scheduled . "2011-08-02 Tue")
;;  (title . "[[redmine:772][#772]] WordPress logins not working")
;;  (priority . "B")
;;  (state . "DONE")
;;  (depth . 4)
;;  (properties
;;   ("Submitter" . "Jere Matlock <jere@wordsinarow.com>")
;;   ("Message" . "[[message://20110801001929.22873j25xv7o1hog@www.wordsinarow.com][wp logins not working]]")
;;   ("Date" . "Mon, 01 Aug 2011 00:19:29 -0700")
;;   ("CREATED" . "[2011-08-01 Mon 16:16]")
;;   ("ID" . "5C2E2321-16A2-4CA3-9785-6A17B6A00A33"))
;;  (log
;;   ((date . "2011-08-02 Tue 11:02")
;;    (from . "TODO")
;;    (to . "DONE")
;;    (depth . 6)))
;;  (tags "Net"))

(defun org-redmine-convert-timestamp (stamp &optional with-hm inactive)
  (when (string-match (concat "\\([0-9]+\\)-\\([0-9]+\\)-\\([0-9]+\\)"
                              "T\\([0-9]+\\):\\([0-9]+\\):\\([0-9]+\\)-.+")
                      stamp)
    (let ((year (string-to-number (match-string 1 stamp)))
          (mon  (string-to-number (match-string 2 stamp)))
          (day  (string-to-number (match-string 3 stamp)))
          (hour (string-to-number (match-string 4 stamp)))
          (min  (string-to-number (match-string 5 stamp)))
          (sec  (string-to-number (match-string 6 stamp))))
      (with-temp-buffer
        (org-insert-time-stamp (encode-time sec min hour day mon year)
                               with-hm inactive)
        (buffer-string)))))

(defun org-redmine-convert-to-org (data &optional existing)
  (let ((result (or existing (list (cons 'depth 1))))
        id)
    (dolist (elem data)
      (cond
       ((eq 'id (car elem))
        (setq id (string-to-number (nth 2 elem))))

       ((eq 'subject (car elem))
        (add-to-list 'result
                     (cons 'title (format "[[redmine:%d][#%d]] %s"
                                          id id (nth 2 elem)))))

       ((eq 'description (car elem))
        (unless (assq 'body result)
          (add-to-list 'result (cons 'body (nth 2 elem)))))

       ((eq 'status (car elem))
        (setq result (delq (assq 'status result) result))

        (let ((stat (cdr (assq 'name (cadr elem)))))
          (dolist (status org-redmine-statuses)
            (if (string= stat (cadr status))
                (setq stat (car status))))
          (add-to-list 'result
                       (cons 'state stat))))

       ((eq 'priority (car elem))
        (setq result (delq (assq 'priority result) result))
        (add-to-list
         'result
         (cons 'priority
               (let ((pri (cdr (assq 'name (cadr elem)))))
                 (cond
                  ((string-match "\\(High\\|Urgent\\|Immediate\\)" pri)
                   "A")
                  ((string= "Normal" pri)
                   "B")
                  ((string= "Low" pri)
                   "C"))))))

       ((eq 'created_on (car elem))
        (unless (assq 'properties result)
          (add-to-list
           'result
           (cons 'properties
                 (list
                  (cons "CREATED"
                        (org-redmine-convert-timestamp (nth 2 elem) t t)))))))

       ((eq 'journals (car elem))
        (dolist (journal (nthcdr 2 elem))
          (let* ((body (nth 2 (assq 'notes journal)))
                 (date (replace-regexp-in-string
                        "\\(\\`<\\|>\\'\\)" ""
                        (org-redmine-convert-timestamp
                         (nth 2 (assq 'created_on journal)) t)))
                 (entry-exists
                  (catch 'entry-exists
                    (dolist (entry (cdr (assq 'log result)))
                      (if (string= date (cdr (assq 'date entry)))
                          (throw 'entry-exists t)))))
                 log)
            (unless entry-exists
              (add-to-list
               'log (cons 'body
                          (concat (cdr (assq 'name
                                             (cadr (assq 'user journal))))
                                  ": " body)))
              (add-to-list 'log (cons 'date date))
              (when body
                (add-to-list 'log (cons 'note t))
                (let ((journal (assq 'log result)))
                  (if journal
                      (nconc journal (list log))
                    (add-to-list 'result
                                 (cons 'log (list log))))))))))))
    result))

(defun org-redmine-get-issue (issue-id)
  (org-redmine-rest-api "GET" (format "issues/%d.xml" issue-id)
                        nil "include=journals"))

(defun org-redmine-update ()
  (interactive)
  (let* ((heading (nth 4 (org-heading-components)))
         (id (and (string-match "\\[\\[redmine:\\([0-9]+\\)\\]" heading)
                  (string-to-number (match-string 1 heading)))))
    (if id
        (org-replace-entry
         (org-redmine-convert-to-org (org-redmine-get-issue id)
                                     (org-parse-entry))))))

(defun org-redmine-submit-issue
  (project &optional subject priority assigned-to tracker description)
  (let* ((result
          (org-redmine-rest-api
           "POST" "issues.xml"
           (format "<?xml version=\"1.0\"?>
<issue>
  <project_id>%s</project_id>
  <subject>%s</subject>
  <tracker_id>%d</tracker_id>
  <assigned_to_id>%d</assigned_to_id>
  <priority_id>%d</priority_id>
  <description>%s</description>
</issue>"
                   project
                   (xml-escape-string subject)
                   tracker
                   assigned-to
                   priority
                   (xml-escape-string description))))
         (id (nth 2 (assq 'id result))))
    (if id
        (string-to-number id)
      (error "Failed to submit issue for project %s" project))))

(defun org-redmine-add-note (issue-id note)
  (org-redmine-rest-api
   "PUT" (format "issues/%d.xml" issue-id)
   (format "<?xml version=\"1.0\"?>
<issue>
  <notes>%s</notes>
</issue>" (xml-escape-string note))))

(defun org-redmine-modify-status (issue-id status-id &optional note)
  (org-redmine-rest-api
   "PUT" (format "issues/%d.xml" issue-id)
   (format "<?xml version=\"1.0\"?>
<issue>
  <status_id>%s</status_id>
%s</issue>"
           status-id
           (if note
               (concat "  <notes>" (xml-escape-string note)
                       "</notes>\n")
             ""))))

(defun org-redmine-post-issue
  (project &optional subject priority assigned-to tracker description)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
         (goto-char omk)
         (let ((project
                (or (org-get-category)
                    (error "Current Org task has no category")))
               (components (org-heading-components)))
           (list
            (or (cdr (assoc project org-redmine-projects))
                (error "Could not determine Redmine project from Org category '%s'"
                       project))
            (nth 4 components) ;; todo heading
            (org-redmine-convert-priority (nth 3 components))
            (or org-redmine-id
                (error "Please configure your `org-redmine-id'"))
            (cdr (assoc
                  (ido-completing-read
                   "Tracker: " (mapcar #'car org-redmine-trackers)
                   nil t nil nil (caar org-redmine-trackers))
                  org-redmine-trackers))
            (org-redmine-todo-description)))))))
  (let ((id (org-redmine-submit-issue project subject priority
                                      assigned-to tracker description))
        (omk (get-text-property (point) 'org-marker)))
    (with-current-buffer (marker-buffer omk)
      (save-excursion
        (goto-char omk)
        (org-back-to-heading t)
        (re-search-forward
         (concat "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\)"
                 " \\(\\[#[ABC]\\] \\)?"))
        (insert (format "[[redmine:%s][#%s]] " id id)))))
  (org-agenda-redo))

(defadvice org-store-log-note (before org-redmine-post-note activate)
  (unless org-note-abort
    (let ((txt (buffer-string)) issue-id)
      (while (string-match "\\`#.*\n[ \t\n]*" txt)
        (setq txt (replace-match "" t t txt)))
      (if (string-match "\\s-+\\'" txt)
          (setq txt (replace-match "" t t txt)))
      (with-current-buffer (marker-buffer org-log-note-marker)
        (save-excursion
          (goto-char org-log-note-marker)
          (let ((heading (nth 4 (org-heading-components))))
            (when (string-match "\\[\\[redmine:\\([0-9]+\\)\\]" heading)
              (cond
               ((eq org-log-note-purpose 'note)
                (org-redmine-add-note
                 (string-to-number (match-string 1 heading)) txt))
               ((eq org-log-note-purpose 'state)
                (let ((state-id (cddr (assoc org-log-note-state
                                             org-redmine-statuses))))
                  (if state-id
                   (org-redmine-modify-status
                    (string-to-number (match-string 1 heading))
                    state-id txt))))))))))))

(defun make-bug-link ()
  (interactive)
  (let* ((omk (get-text-property (point) 'org-marker))
         (path (with-current-buffer (marker-buffer omk)
                 (save-excursion
                   (goto-char omk)
                   (org-get-outline-path)))))
    (cond
     ((string-match "/ledger/" (buffer-file-name (marker-buffer omk)))
      (call-interactively #'make-ledger-bugzilla-bug))
     ((string= "BoostPro" (car path))
      (call-interactively #'org-redmine-post-issue))
     (t
      (error "Cannot make bug, unknown category")))))

(provide 'org-redmine)

;;; org-redmine.el ends here
