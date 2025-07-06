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

(defconst org-constants-todo-path (org-file "todo.org"))

(defconst org-constants-work-todo-path (org-file "kadena/kadena.org"))

(defconst org-constants-work-asana-path (org-file "kadena/asana.org"))

(defconst org-constants-kadena-team-file "kadena/team/202409042228-team.org"
  "File containing names of team members and links to their files.")

(defconst org-constants-assembly-path (org-file "assembly/assembly.org"))

(defconst org-constants-open-source-path (org-file "OSS.org"))

(defconst org-constants-contacts-path (org-file "contacts.org"))

(defconst org-constants-agenda-base-files
  (list org-constants-todo-path
        org-constants-work-todo-path
        (org-file "assembly/assembly.org")
        (org-file "quantum-trades/quantum-trades.org")
        org-constants-open-source-path))

(defconst org-constants-protected-filenames-list
  (list (file-name-nondirectory org-constants-todo-path)
        "kadena/kadena.org"
        "assembly/assembly.org"
        "quantum-trades/quantum-trades.org"
        (file-name-nondirectory org-constants-open-source-path)
        (file-name-nondirectory org-constants-contacts-path)
        (file-name-nondirectory org-constants-journelly-path)
        (file-name-nondirectory org-constants-flat-habits-path)
        (file-name-nondirectory org-constants-plain-org-path)))

(defconst org-constants-protected-basenames-list
  (mapcar #'file-name-nondirectory org-constants-protected-filenames-list))

(provide 'org-constants)
