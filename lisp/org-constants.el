;;; -*- lexical-binding: t -*-

;;; This file should be loaded before Org-mode, or any other modules that
;;; loads Org.

(defconst org-constants-directory "~/org/")

(defconst org-constants-journelly-path
  "~/Library/Mobile Documents/iCloud~com~xenodium~Journelly/Documents/Journelly.org")

(defconst org-constants-flat-habits-path
  "~/Library/Mobile Documents/com~apple~CloudDocs/Flat Habits/MyHabits.org")

(defconst org-constants-plain-org-path
  "~/Library/Mobile Documents/com~apple~CloudDocs/Plain Org/Mobile.org")

(defsubst org-constants-file (path)
  (expand-file-name path org-constants-directory))

(defalias 'org-file 'org-constants-file)

(defconst org-constants-drafts-path (org-file "drafts.org"))

(defconst org-constants-todo-path (org-file "todo.org"))

;; jww (2025-11-21): I need to have -womrk-paths here, not just -work-path
(defconst org-constants-work-todo-path (org-file "positron/positron.org"))

;; jww (2025-11-21): I need to have team files for all engagements
(defconst org-constants-positron-team-file "positron/team/202409042228-team.org"
  "File containing names of team members and links to their files.")

;; jww (2025-11-21): I need to have -bahai-paths here, not just -assembly-path
(defconst org-constants-assembly-path (org-file "bahai/assembly/assembly.org"))

(defconst org-constants-contacts-path (org-file "contacts.org"))

(defconst org-constants-agenda-base-files
  (list org-constants-todo-path
        org-constants-drafts-path
        org-constants-work-todo-path
        org-constants-assembly-path
        (org-file "quantum-trades/quantum-trades.org")))

(defconst org-constants-protected-filenames-list
  (list (file-name-nondirectory org-constants-todo-path)
        (file-name-nondirectory org-constants-drafts-path)
        (file-name-nondirectory org-constants-assembly-path)
        "quantum-trades/quantum-trades.org"
        (file-name-nondirectory org-constants-contacts-path)
        (file-name-nondirectory org-constants-journelly-path)
        (file-name-nondirectory org-constants-flat-habits-path)
        (file-name-nondirectory org-constants-plain-org-path)))

;; jww (2025-11-21): I need to automatically include archive files for all
;; files in the protected names list.
(defconst org-constants-protected-basenames-list
  (cl-delete-duplicates
   (append (mapcar #'file-name-nondirectory
                   org-constants-protected-filenames-list)
           '("archive.org"
             "assembly-archive.org"
             "GLSA.org"
             "badi-calendar.org"
             "bookmarks.org"
             "colors.org"
             "document-index.org"
             "home.org"
             "init.org"
             "writings.org"))))

(provide 'org-constants)

;;; org-constants.el ends here
