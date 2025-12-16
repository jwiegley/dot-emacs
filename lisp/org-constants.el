;;; -*- lexical-binding: t -*-

;;; This file should be loaded before Org-mode, or any other modules that
;;; loads Org.

;;; Code:

(require 'cl-lib)

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

(defconst org-constants-positron-team-file "positron/team/202511211741-team.org"
  "File containing names of team members and links to their files.")

(defconst org-constants-contacts-path (org-file "contacts.org"))

(defconst org-constants-agenda-base-files
  (list org-constants-drafts-path
        org-constants-todo-path
        (org-file "bahai/assembly/assembly.org")
        (org-file "bahai/council/council.org")
        (org-file "positron/positron.org")
        (org-file "quantum-trades/quantum-trades.org")))

(defconst org-constants-protected-filenames-list
  (list (file-name-nondirectory org-constants-drafts-path)
        (file-name-nondirectory org-constants-todo-path)
        "bahai/assembly/assembly.org"
        "bahai/council/council.org"
        "bahai/ruhi/ruhi-book9.org"
        "positron/positron.org"
        "quantum-trades/quantum-trades.org"
        (file-name-nondirectory org-constants-contacts-path)
        (file-name-nondirectory org-constants-journelly-path)
        (file-name-nondirectory org-constants-flat-habits-path)
        (file-name-nondirectory org-constants-plain-org-path)))

(defconst org-constants-protected-basenames-list
  (cl-delete-duplicates
   (append (mapcar #'file-name-nondirectory
                   org-constants-protected-filenames-list)
           '("archive.org"
             "assembly-archive.org"
             "council-archive.org"
             "positron-archive.org"
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
