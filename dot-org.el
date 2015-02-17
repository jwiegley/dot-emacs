;;;_ , Org-mode

(load "org-settings")

(require 'org)
(require 'org-agenda)
(require 'org-smart-capture)
(require 'org-crypt)
(require 'org-bbdb)
(require 'org-devonthink)
(require 'org-debbugs)
(require 'org-magit)
(require 'org-velocity)
(require 'ob-R)
(require 'ob-python)
(require 'ob-ruby)
(require 'ob-emacs-lisp)
(require 'ob-haskell)
(require 'ob-sh)
(require 'ob-ditaa)
(require 'ox-md)
(require 'ox-opml)

(require 'async)

;;(load "org-log" t)

(defun org-babel-execute:ditaa (body params)
  "Execute a block of Ditaa code with org-babel.
This function is called by `org-babel-execute-src-block'."
  (let* ((result-params (split-string (or (cdr (assoc :results params)) "")))
	 (out-file (let ((el (cdr (assoc :file params))))
                     (or el
                         (error
                          "ditaa code block requires :file header argument"))))
	 (cmdline (cdr (assoc :cmdline params)))
	 (java (cdr (assoc :java params)))
	 (in-file (org-babel-temp-file "ditaa-"))
	 (eps (cdr (assoc :eps params)))
         (pdf-cmd (when (and (or (string= (file-name-extension out-file) "pdf")
                                 (cdr (assoc :pdf params))))
                    (concat
                     "epstopdf"
                     " " (org-babel-process-file-name (concat in-file ".eps"))
                     " -o=" (org-babel-process-file-name out-file))))
	 (cmd (concat org-babel-ditaa-java-cmd
		      " " java " " org-ditaa-jar-option " "
		      (shell-quote-argument
		       (expand-file-name
			(if eps org-ditaa-eps-jar-path org-ditaa-jar-path)))
		      " " cmdline
		      " " (org-babel-process-file-name in-file)
                      " " (if pdf-cmd
                              (org-babel-process-file-name (concat in-file ".eps"))
                            (org-babel-process-file-name out-file)))))
    (unless (file-exists-p org-ditaa-jar-path)
      (error "Could not find ditaa.jar at %s" org-ditaa-jar-path))
    (with-temp-file in-file (insert body))
    (message cmd) (shell-command cmd)
    (when pdf-cmd (message pdf-cmd) (shell-command pdf-cmd))
    nil))

(defun org-show-context (&optional key)
  "Make sure point and context are visible.
How much context is shown depends upon the variables
`org-show-hierarchy-above', `org-show-following-heading',
`org-show-entry-below' and `org-show-siblings'."
  (let ((heading-p   (org-at-heading-p t))
	(hierarchy-p (org-get-alist-option org-show-hierarchy-above key))
	(following-p (org-get-alist-option org-show-following-heading key))
	(entry-p     (org-get-alist-option org-show-entry-below key))
	(siblings-p  (org-get-alist-option org-show-siblings key)))
    ;; Show heading or entry text
    (if (and heading-p (not entry-p))
	(org-flag-heading nil)    ; only show the heading
      (and (or entry-p (outline-invisible-p) (org-invisible-p2))
	   (org-show-hidden-entry)))    ; show entire entry
    (when following-p
      ;; Show next sibling, or heading below text
      (save-excursion
	(and (if heading-p (org-goto-sibling) (outline-next-heading))
	     (org-flag-heading nil))))
    (when siblings-p (org-show-siblings))
    (when hierarchy-p
      ;; show all higher headings, possibly with siblings
      (save-excursion
	(while (and (condition-case nil
			(progn (org-up-heading-all 1) t)
		      (error nil))
		    (not (bobp)))
	  (org-flag-heading nil)
	  (when siblings-p (org-show-siblings)))))))

(defun org-link-to-named-task ()
  (interactive))
(fset 'org-link-to-named-task
   [?\C-  ?\C-  ?\C-e ?\C-w ?\C-s ?\M-y ?\C-a ?\M-f ?\C-c ?S ?\C-u ?\C-  ?\C-c ?\C-l return return ?\C-x ?\C-x ?\C-  ?\C- ])

(defun org-find-top-category (&optional pos)
  (let ((cat
         (save-excursion
           (with-current-buffer (if pos (marker-buffer pos) (current-buffer))
             (if pos (goto-char pos))
             ;; Skip up to the topmost parent
             (while (ignore-errors (outline-up-heading 1) t))
             (ignore-errors
               (nth 4 (org-heading-components)))))))
    (save-excursion
      (with-current-buffer (if pos (marker-buffer pos) (current-buffer))
        (org-entry-get pos "OVERLAY" t)))))

(defun jump-to-org-agenda ()
  (interactive)
  (let ((recordings-dir "~/Dropbox/Apps/Dropvox"))
    (if (directory-files recordings-dir nil "\\`[^.]")
        (find-file recordings-dir)))
  (let ((buf (get-buffer "*Org Agenda*"))
        wind)
    (if buf
        (if (setq wind (get-buffer-window buf))
            (when (called-interactively-p 'any)
              (select-window wind)
              (org-fit-window-to-buffer))
          (if (called-interactively-p 'any)
              (progn
                (select-window (display-buffer buf t t))
                (org-fit-window-to-buffer))
            (with-selected-window (display-buffer buf)
              (org-fit-window-to-buffer))))
      (call-interactively 'org-agenda-list))))

(defun org-export-tasks ()
  (interactive)
  (let ((index 1))
    (org-map-entries
     #'(lambda ()
         (outline-mark-subtree)
         (org-export-as-html 3)
         (write-file (format "%d.html" index))
         (kill-buffer (current-buffer))
         (setq index (1+ index)))
     "LEVEL=2")))

(defun org-get-global-property (name)
  (save-excursion
    (goto-char (point-min))
    (and (re-search-forward (concat "#\\+PROPERTY: " name " \\(.*\\)") nil t)
         (match-string 1))))

(defun org-agenda-add-overlays (&optional line)
  "Add overlays found in OVERLAY properties to agenda items.
Note that habitual items are excluded, as they already
extensively use text properties to draw the habits graph.

For example, for work tasks I like to use a subtle, yellow
background color; for tasks involving other people, green; and
for tasks concerning only myself, blue.  This way I know at a
glance how different responsibilities are divided for any given
day.

To achieve this, I have the following in my todo file:

  * Work
    :PROPERTIES:
    :CATEGORY: Work
    :OVERLAY:  (face (:background \"#fdfdeb\"))
    :END:
  ** TODO Task
  * Family
    :PROPERTIES:
    :CATEGORY: Personal
    :OVERLAY:  (face (:background \"#e8f9e8\"))
    :END:
  ** TODO Task
  * Personal
    :PROPERTIES:
    :CATEGORY: Personal
    :OVERLAY:  (face (:background \"#e8eff9\"))
    :END:
  ** TODO Task

The colors (which only work well for white backgrounds) are:

  Yellow: #fdfdeb
  Green:  #e8f9e8
  Blue:   #e8eff9

To use this function, add it to `org-agenda-finalize-hook':

  (add-hook 'org-finalize-agenda-hook 'org-agenda-add-overlays)"
  (let ((inhibit-read-only t) l c
        (buffer-invisibility-spec '(org-link)))
    (save-excursion
      (goto-char (if line (point-at-bol) (point-min)))
      (while (not (eobp))
        (let ((org-marker (get-text-property (point) 'org-marker)))
          (when (and org-marker
                     (null (overlays-at (point)))
                     (not (get-text-property (point) 'org-habit-p))
                     (string-match "\\(sched\\|dead\\|todo\\)"
                                   (get-text-property (point) 'type)))
            (let ((overlays
                   (or (org-entry-get org-marker "OVERLAY" t)
                       (with-current-buffer (marker-buffer org-marker)
                         (org-get-global-property "OVERLAY")))))
              (when overlays
                (goto-char (line-end-position))
                (let ((rest (- (window-width) (current-column))))
                  (if (> rest 0)
                      (insert (make-string rest ? ))))
                (let ((ol (make-overlay (line-beginning-position)
                                        (line-end-position)))
                      (proplist (read overlays)))
                  (while proplist
                    (overlay-put ol (car proplist) (cadr proplist))
                    (setq proplist (cddr proplist))))))))
        (forward-line)))))

(add-hook 'org-finalize-agenda-hook 'org-agenda-add-overlays)

(autoload 'gnus-goto-article ".gnus")
(autoload 'gnus-string-remove-all-properties "gnus-util")

(defun org-my-message-open (message-id)
  (let (gnus-mark-article-hook)
    (gnus-goto-article
     (gnus-string-remove-all-properties (substring message-id 2)))))

;;(defun org-my-message-open (message-id)
;;  (condition-case err
;;      (if (get-buffer "*Group*")
;;          (gnus-goto-article
;;           (gnus-string-remove-all-properties (substring message-id 2)))
;;        (org-mac-message-open message-id))
;;    (error
;;     (org-mac-message-open message-id))))

(add-to-list 'org-link-protocols (list "message" 'org-my-message-open nil))

(defun save-org-mode-files ()
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'org-mode)
        (if (and (buffer-modified-p) (buffer-file-name))
            (save-buffer))))))

(run-with-idle-timer 25 t 'save-org-mode-files)

(defun my-org-push-mobile ()
  (interactive)
  (with-current-buffer (find-file-noselect "~/Documents/todo.txt")
    (org-mobile-push)))

(eval-when-compile
  (defvar org-clock-current-task)
  (defvar org-mobile-directory)
  (defvar org-mobile-capture-file))

(defun org-my-auto-exclude-function (tag)
  (and (cond
        ((string= tag "call")
         (let ((hour (nth 2 (decode-time))))
           (or (< hour 8) (> hour 21))))
        ((string= tag "errand")
         (let ((hour (nth 2 (decode-time))))
           (or (< hour 12) (> hour 17))))
        ((or (string= tag "home") (string= tag "nasim"))
         (with-temp-buffer
           (call-process "/sbin/ifconfig" nil t nil "en0" "inet")
           (call-process "/sbin/ifconfig" nil t nil "en1" "inet")
           (call-process "/sbin/ifconfig" nil t nil "bond0" "inet")
           (goto-char (point-min))
           (not (re-search-forward "inet 192\\.168\\.9\\." nil t))))
        ((string= tag "net")
         (not (quickping "imap.gmail.com")))
        ((string= tag "fun")
         org-clock-current-task))
       (concat "-" tag)))

(defun my-mobileorg-convert ()
  (interactive)
  (while (re-search-forward "^\\* " nil t)
    (goto-char (match-beginning 0))
    (insert ?*)
    (forward-char 2)
    (insert "TODO ")
    (goto-char (line-beginning-position))
    (forward-line)
    (re-search-forward "^\\[")
    (goto-char (match-beginning 0))
    (let ((uuid
           (save-excursion
             (re-search-forward "^\\*\\* Note ID: \\(.+\\)")
             (prog1
                 (match-string 1)
               (delete-region (match-beginning 0)
                              (match-end 0))))))
      (insert (format "SCHEDULED: %s\n:PROPERTIES:\n"
                      (format-time-string (org-time-stamp-format))))
      (insert (format ":ID:       %s\n:CREATED:  " uuid)))
    (forward-line)
    (insert ":END:")))

(defun my-org-convert-incoming-items ()
  (interactive)
  (with-current-buffer
      (find-file-noselect (expand-file-name org-mobile-capture-file
                                            org-mobile-directory))
    (goto-char (point-min))
    (unless (eobp)
      (my-mobileorg-convert)
      (goto-char (point-max))
      (if (bolp)
          (delete-char -1))
      (let ((tasks (buffer-string)))
        (set-buffer-modified-p nil)
        (kill-buffer (current-buffer))
        (with-current-buffer (find-file-noselect "~/Documents/todo.txt")
          (save-excursion
            (goto-char (point-min))
            (re-search-forward "^\\* Inbox$")
            (re-search-forward "^:END:")
            (forward-line)
            (goto-char (line-beginning-position))
            (if (and tasks (> (length tasks) 0))
                (insert tasks ?\n))))))))

;;;_Don't sync agendas.org to MobileOrg.  I do this because I only use
;;;_MobileOrg for recording new tasks on the phone, and never for viewing
;;;_tasks.  This allows MobileOrg to start up and sync extremely quickly.

;;(add-hook 'org-mobile-post-push-hook
;;          (function
;;           (lambda ()
;;             (shell-command "/bin/rm -f ~/Dropbox/MobileOrg/agendas.org")
;;             (shell-command
;;              (concat "perl -i -ne 'print unless /agendas\\.org/;'"
;;                      "~/Dropbox/MobileOrg/checksums.dat"))
;;             (shell-command
;;              (concat "perl -i -ne 'print unless /agendas\\.org/;'"
;;                      "~/Dropbox/MobileOrg/index.org")))))

(defun my-org-mobile-pre-pull-function ()
  (my-org-convert-incoming-items))

(defun my-org-mobile-post-push-function ())

(add-hook 'org-mobile-pre-pull-hook 'my-org-mobile-pre-pull-function)
(add-hook 'org-mobile-post-push-hook 'my-org-mobile-post-push-function)

(defun org-my-state-after-clock-out (state)
  (if (string= state "STARTED")
      "TODO"
    state))

(defvar org-my-archive-expiry-days 1
  "The number of days after which a completed task should be auto-archived.
This can be 0 for immediate, or a floating point value.")

(defconst org-my-ts-regexp
  "[[<]\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} [^]>\r\n]*?\\)[]>]"
  "Regular expression for fast inactive time stamp matching.")

(defun org-my-closing-time ()
  (let* ((state-regexp
          (concat "- State \"\\(?:" (regexp-opt org-done-keywords)
                  "\\)\"\\s-*\\[\\([^]\n]+\\)\\]"))
         (regexp (concat "\\(" state-regexp "\\|" org-my-ts-regexp "\\)"))
         (end (save-excursion
                (outline-next-heading)
                (point)))
         begin
         end-time)
    (goto-char (line-beginning-position))
    (while (re-search-forward regexp end t)
      (let ((moment (org-parse-time-string (match-string 1))))
        (if (or (not end-time)
                (time-less-p (apply #'encode-time end-time)
                             (apply #'encode-time moment)))
            (setq end-time moment))))
    (goto-char end)
    end-time))

(defun org-my-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((done-regexp
           (concat "^\\*\\* \\(" (regexp-opt org-done-keywords) "\\) ")))
      (while (re-search-forward done-regexp nil t)
        (if (>= (time-to-number-of-days
                 (time-subtract (current-time)
                                (apply #'encode-time (org-my-closing-time))))
                org-my-archive-expiry-days)
            (org-archive-subtree))))
    (save-buffer)))

(defalias 'archive-done-tasks 'org-my-archive-done-tasks)

(defun org-get-inactive-time ()
  (float-time (org-time-string-to-time
               (or (org-entry-get (point) "TIMESTAMP")
                   (org-entry-get (point) "TIMESTAMP_IA")
                   (debug)))))

(defun org-get-completed-time ()
  (let ((begin (point)))
    (save-excursion
      (outline-next-heading)
      (and (re-search-backward "\\(- State \"\\(DONE\\|DEFERRED\\|CANCELED\\)\"\\s-+\\[\\(.+?\\)\\]\\|CLOSED: \\[\\(.+?\\)\\]\\)" begin t)
           (float-time (org-time-string-to-time (or (match-string 3)
                                                    (match-string 4))))))))

(defun org-my-sort-done-tasks ()
  (interactive)
  (goto-char (point-min))
  (org-sort-entries t ?F #'org-get-inactive-time #'<)
  (goto-char (point-min))
  (while (re-search-forward "


+" nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (insert "
"))
  (let (after-save-hook)
    (save-buffer))
  (org-overview))

(defalias 'sort-done-tasks 'org-my-sort-done-tasks)

(defun org-archive-done-tasks ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "\* \\(DONE\\|CANCELED\\) " nil t)
      (if (save-restriction
            (save-excursion
              (error "Need to replace org-x-narrow-to-entry")
              ;; (org-x-narrow-to-entry)
              (search-forward ":LOGBOOK:" nil t)))
          (forward-line)
        (org-archive-subtree)
        (goto-char (line-beginning-position))))))

(defun org-sort-all ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\* " nil t)
      (goto-char (match-beginning 0))
      (condition-case err
          (progn
            (org-sort-entries t ?a)
            (org-sort-entries t ?p)
            (org-sort-entries t ?o))
        (error nil))
      (forward-line))
    (goto-char (point-min))
    (while (re-search-forward "\* PROJECT " nil t)
      (goto-char (line-beginning-position))
      (ignore-errors
        (org-sort-entries t ?a)
        (org-sort-entries t ?p)
        (org-sort-entries t ?o))
      (forward-line))))

(defun org-cleanup ()
  (interactive)
  (org-archive-done-tasks)
  (org-sort-all)
  ;;(org-x-normalize-all-entries)
  )

(defvar my-org-wrap-region-history nil)

(defun my-org-wrap-region (&optional arg)
  (interactive "P")
  (save-excursion
    (goto-char (region-end))
    (if arg
        (insert "#+end_src\n")
      (insert ":END:\n"))
    (goto-char (region-beginning))
    (if arg
        (insert "#+begin_src "
                (read-string "Language: " nil 'my-org-wrap-region-history)
                ?\n)
      (insert ":OUTPUT:\n"))))

(defun org-maybe-remember (&optional done)
  (interactive "P")
  (if (string= (buffer-name) "*Remember*")
      (call-interactively 'org-ctrl-c-ctrl-c)
    (if (null done)
        (call-interactively 'org-remember)
      (let ((org-capture-templates
             '((110 "* STARTED %?
- State \"STARTED\"    %U
SCHEDULED: %t
:PROPERTIES:
:ID:       %(shell-command-to-string \"uuidgen\"):CREATED:  %U
:END:" "~/Documents/todo.txt" "Inbox"))))
        (org-remember))))
  (set-fill-column 72))

(defun org-inline-note ()
  (interactive)
  (switch-to-buffer-other-window "todo.txt")
  (goto-char (point-min))
  (re-search-forward "^\\* Inbox$")
  (re-search-forward "^:END:")
  (forward-line)
  (goto-char (line-beginning-position))
  (insert "** NOTE ")
  (save-excursion
    (insert (format "
:PROPERTIES:
:ID:       %s   :VISIBILITY: folded
:CREATED:  %s
:END:" (shell-command-to-string "uuidgen")
   (format-time-string (org-time-stamp-format t t))))
    (insert ?\n))
  (save-excursion
    (forward-line)
    (org-cycle)))

;;(defun org-get-apple-message-link ()
;;  (let ((subject (do-applescript "tell application \"Mail\"
;;        set theMessages to selection
;;        subject of beginning of theMessages
;;end tell"))
;;        (message-id (do-applescript "tell application \"Mail\"
;;        set theMessages to selection
;;        message id of beginning of theMessages
;;end tell")))
;;    (org-make-link-string (concat "message://" message-id) subject)))
;;
;;(defun org-get-message-sender ()
;;  (do-applescript "tell application \"Mail\"
;;        set theMessages to selection
;;        sender of beginning of theMessages
;;end tell"))
;;
;;(defun org-insert-apple-message-link ()
;;  (interactive)
;;  (insert (org-get-apple-message-link)))

(defun org-get-message-link (&optional title)
  (assert (get-buffer "*Group*"))
  (let (message-id subject)
    (with-current-buffer gnus-original-article-buffer
      (setq message-id (substring (message-field-value "message-id") 1 -1)
            subject (or title (message-field-value "subject"))))
    (org-make-link-string (concat "message://" message-id)
                          (rfc2047-decode-string subject))))

(defun org-insert-message-link (&optional arg)
  (interactive "P")
  (insert (org-get-message-link (if arg "writes"))))

(defun org-set-message-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Message" (org-get-message-link)))

(defun org-get-message-sender ()
  (assert (get-buffer "*Group*"))
  (let (message-id subject)
    (with-current-buffer gnus-original-article-buffer
      (message-field-value "from"))))

(defun org-set-message-sender ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Submitter" (org-get-message-sender)))

(defun org-get-safari-link ()
  (let ((subject (substring (do-applescript
                             (string-to-multibyte "tell application \"Safari\"
        name of document of front window
end tell")) 1 -1))
        (url (substring (do-applescript
                         (string-to-multibyte "tell application \"Safari\"
        URL of document of front window
end tell")) 1 -1)))
    (org-make-link-string url subject)))

(defun org-get-chrome-link ()
  (let ((subject (do-applescript
                  (string-to-multibyte "tell application \"Google Chrome\"
        title of active tab of front window
end tell")))
        (url (do-applescript
              (string-to-multibyte "tell application \"Google Chrome\"
        URL of active tab of front window
end tell"))))
    (org-make-link-string (substring url 1 -1) (substring subject 1 -1))))

(defun org-insert-url-link ()
  (interactive)
  (insert (org-get-safari-link)))

(defun org-set-url-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "URL" (org-get-safari-link)))

;;(defun org-get-file-link ()
;;  (let ((subject (do-applescript "tell application \"Finder\"
;;      set theItems to the selection
;;      name of beginning of theItems
;;end tell"))
;;        (path (do-applescript "tell application \"Finder\"
;;      set theItems to the selection
;;      POSIX path of (beginning of theItems as text)
;;end tell")))
;;    (org-make-link-string (concat "file:" path) subject)))
;;
;;(defun org-insert-file-link ()
;;  (interactive)
;;  (insert (org-get-file-link)))
;;
;;(defun org-set-file-link ()
;;  "Set a property for the current headline."
;;  (interactive)
;;  (org-set-property "File" (org-get-file-link)))

(defun org-set-dtp-link ()
  "Set a property for the current headline."
  (interactive)
  (org-set-property "Document" (org-get-dtp-link)))

(defun org-dtp-message-open ()
  "Visit the message with the given MESSAGE-ID.
This will use the command `open' with the message URL."
  (interactive)
  (re-search-backward "\\[\\[message://\\(.+?\\)\\]\\[")
  (do-applescript
   (format "tell application \"DEVONthink Pro\"
        set searchResults to search \"%%3C%s%%3E\" within URLs
        open window for record (get beginning of searchResults)
end tell" (match-string 1))))

(fset 'orgify-line
   [?\C-k ?\C-o ?t ?o ?d ?o tab ?\C-y backspace ?\C-a ?l ?\C-u ?\C-n ?\C-n ?\C-n])

(add-hook 'org-log-buffer-setup-hook
          (lambda ()
            (setq fill-column (- fill-column 5))))

(defun org-message-reply ()
  (interactive)
  (let* ((org-marker (get-text-property (point) 'org-marker))
         (submitter (org-entry-get (or org-marker (point)) "Submitter"))
         (subject (if org-marker
                      (with-current-buffer (marker-buffer org-marker)
                        (goto-char org-marker)
                        (nth 4 (org-heading-components)))
                    (nth 4 (org-heading-components)))))
    (setq subject (replace-regexp-in-string "\\`(.*?) " "" subject))
    (compose-mail-other-window submitter (concat "Re: " subject))))

;;;_  . make-bug-link

(defun make-ledger-bugzilla-bug (product component version priority severity)
  (interactive
   (let ((omk (get-text-property (point) 'org-marker)))
     (with-current-buffer (marker-buffer omk)
       (save-excursion
         (goto-char omk)
         (let ((components
                (list "data" "doc" "expr" "lisp" "math" "python" "report"
                      "test" "util" "website" "build" "misc"))
               (priorities (list "P1" "P2" "P3" "P4" "P5"))
               (severities (list "blocker" "critical" "major"
                                 "normal" "minor" "trivial" "enhancement"))
               (product "Ledger")
               (version "3.0.0-20120217"))
           (list product
                 (ido-completing-read "Component: " components
                                      nil t nil nil (car (last components)))
                 version
                 (let ((orgpri (nth 3 (org-heading-components))))
                   (cond
                    ((and orgpri (= ?A orgpri))
                     "P1")
                    ((and orgpri (= ?C orgpri))
                     "P3")
                    (t
                     (ido-completing-read "Priority: " priorities
                                          nil t nil nil "P2"))))
                 (ido-completing-read "Severity: " severities nil t nil nil
                                      "normal") ))))))
  (let ((omk (get-text-property (point) 'org-marker)))
    (with-current-buffer (marker-buffer omk)
      (save-excursion
        (goto-char omk)
        (let ((heading (nth 4 (org-heading-components)))
              (contents (buffer-substring-no-properties
                         (org-entry-beginning-position)
                         (org-entry-end-position)))
              bug)
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
            (when (eobp)
              (insert "No description.")
              (goto-char (point-min)))
            (insert (format "Product: %s
Component: %s
Version: %s
Priority: %s
Severity: %s
Hardware: Other
OS: Other
Summary: %s" product component version priority severity heading) ?\n ?\n)
            (let ((buf (current-buffer)))
              (with-temp-buffer
                (let ((tmpbuf (current-buffer)))
                  (if nil
                      (insert "Bug 999 posted.")
                    (with-current-buffer buf
                      (shell-command-on-region
                       (point-min) (point-max)
                       "~/bin/bugzilla-submit http://bugs.ledger-cli.org/"
                       tmpbuf)))
                  (goto-char (point-min))
                  (or (re-search-forward "Bug \\([0-9]+\\) posted." nil t)
                      (debug))
                  (setq bug (match-string 1))))))
          (save-excursion
            (org-back-to-heading t)
            (re-search-forward "\\(TODO\\|DEFERRED\\|STARTED\\|WAITING\\|DELEGATED\\) \\(\\[#[ABC]\\] \\)?")
            (insert (format "[[bug:%s][#%s]] " bug bug)))))))
  (org-agenda-redo))

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
     (t
      (error "Cannot make bug, unknown category")))))

;;;_  . keybindings

(defvar org-mode-completion-keys
  '((?d . "DONE")
    (?g . "DELEGATED")
    (?n . "NOTE")
    (?r . "DEFERRED")
    (?s . "STARTED")
    (?t . "TODO")
    (?w . "WAITING")
    (?x . "CANCELED")
    (?y . "SOMEDAY")
    ))

(defvar org-todo-state-map nil)
(define-prefix-command 'org-todo-state-map)

(dolist (ckey org-mode-completion-keys)
  (let* ((key (car ckey))
         (label (cdr ckey))
         (org-sym (intern (concat "my-org-todo-" (downcase label))))
         (org-sym-no-logging
          (intern (concat "my-org-todo-" (downcase label) "-no-logging")))
         (org-agenda-sym
          (intern (concat "my-org-agenda-todo-" (downcase label))))
         (org-agenda-sym-no-logging
          (intern (concat "my-org-agenda-todo-"
                          (downcase label) "-no-logging"))))
    (eval
     `(progn
        (defun ,org-sym ()
          (interactive)
          (org-todo ,label))
        (bind-key (concat "C-c x " (char-to-string ,key)) ',org-sym)

        (defun ,org-sym-no-logging ()
          (interactive)
          (let ((org-inhibit-logging t))
            (org-todo ,label)))
        (bind-key (concat "C-c x " (char-to-string  ,(upcase key)))
                  ',org-sym-no-logging)

        (defun ,org-agenda-sym ()
          (interactive)
          (let ((org-inhibit-logging
                 (let ((style (org-entry-get
                               (get-text-property (point) 'org-marker)
                               "STYLE")))
                   (and style (stringp style)
                        (string= style "habit")))))
            (org-agenda-todo ,label)))
        (define-key org-todo-state-map [,key] ',org-agenda-sym)

        (defun ,org-agenda-sym-no-logging ()
          (interactive)
          (let ((org-inhibit-logging t))
            (org-agenda-todo ,label)))
        (define-key org-todo-state-map [,(upcase key)]
          ',org-agenda-sym-no-logging)))))

(bind-key "C-c x b"
          (lambda (bug) (error "Define bug syntax!")
            ;; (interactive "sBug: ")
            ;; (insert (format "[[fpco:%s][#%s]]" bug bug))
            ))
(bind-key "C-c x e" 'org-export)
(bind-key "C-c x l" 'org-insert-dtp-link)
(bind-key "C-c x L" 'org-set-dtp-link)
(bind-key "C-c x m" 'org-insert-message-link)
(bind-key "C-c x M" 'org-set-message-link)
(bind-key "C-c x u" 'org-insert-url-link)
(bind-key "C-c x U" 'org-set-url-link)
(bind-key "C-c x f" 'org-insert-file-link)
(bind-key "C-c x F" 'org-set-file-link)

(autoload 'ledger-test-create "ldg-test" nil t)
(autoload 'ledger-test-run "ldg-test" nil t)

(add-to-list 'auto-mode-alist '("\\.test$" . ledger-mode))

(org-defkey org-mode-map [(control meta return)]
            'org-insert-heading-after-current)
(org-defkey org-mode-map [(control return)] 'other-window)
(org-defkey org-mode-map [return] 'org-return-indent)
(org-defkey org-mode-map
            [(control ?c) (control ?x) ?@] 'visible-mode)
(org-defkey org-mode-map [(control ?c) (meta ?m)] 'my-org-wrap-region)

;; (defvar my-org-expand-map)
;; (define-prefix-command 'my-org-expand-map)
;; (define-key org-mode-map [(control ?c) (control ?e)] 'my-org-expand-map)

;; (define-key my-org-expand-map [(control ?t)] 'ledger-test-create)

(eval-when-compile
  (defvar yas/trigger-key)
  (defvar yas/keymap)

  (autoload 'yas/expand "yasnippet"))

(defun yas/org-very-safe-expand ()
  (let ((yas/fallback-behavior 'return-nil)) (yas/expand)))

(add-hook 'org-mode-hook
          (lambda ()
            (require 'yasnippet)
            (set (make-local-variable 'yas/trigger-key) [tab])
            (add-to-list 'org-tab-first-hook 'yas/org-very-safe-expand)
            (define-key yas/keymap [tab] 'yas/next-field-or-maybe-expand)))

(remove-hook 'kill-emacs-hook 'org-babel-remove-temporary-directory)

;;;_  . org-agenda-mode

(let ((map org-agenda-mode-map))
  (define-key map "\C-n" 'next-line)
  (define-key map "\C-p" 'previous-line)

  (define-key map "g" 'org-agenda-redo)
  (define-key map "f" 'org-agenda-date-later)
  (define-key map "b" 'org-agenda-date-earlier)
  (define-key map "r" 'org-agenda-refile)
  (define-key map " " 'org-agenda-tree-to-indirect-buffer)
  (define-key map "F" 'org-agenda-follow-mode)
  (define-key map "q" 'delete-window)
  (define-key map [(meta ?p)] 'org-agenda-earlier)
  (define-key map [(meta ?n)] 'org-agenda-later)
  (define-key map "x" 'org-todo-state-map)

  (define-key map ">" 'org-agenda-filter-by-top-headline)

  (define-key org-todo-state-map "z" 'make-bug-link))

(unbind-key "M-m" org-agenda-keymap)

(defun org-fit-agenda-window ()
  "Fit the window to the buffer size."
  (and (memq org-agenda-window-setup '(reorganize-frame))
       (fboundp 'fit-window-to-buffer)
       (fit-window-to-buffer)))

(defadvice org-agenda-redo (after fit-windows-for-agenda-redo activate)
  "Fit the Org Agenda to its buffer."
  (org-fit-agenda-window))

(defadvice org-agenda (around fit-windows-for-agenda activate)
  "Fit the Org Agenda to its buffer."
  (let ((notes (directory-files
                "~/Dropbox/Apps/Drafts/" t "[0-9].*\\.txt\\'" nil)))
    (with-current-buffer (find-file-noselect "~/Documents/todo.txt")
      (save-excursion
        (goto-char (point-min))
        (re-search-forward "^\\* Inbox$")
        (re-search-forward "^:END:")
        (forward-line 1)
        (dolist (note notes)
          (insert
           "** TODO "
           (with-temp-buffer
             (insert-file-contents note)
             (goto-char (point-min))
             (forward-line)
             (unless (bolp))
             (insert ?\n)
             (insert (format "SCHEDULED: %s\n"
                             (format-time-string (org-time-stamp-format))))
             (goto-char (point-max))
             (unless (bolp)
               (insert ?\n))
             (let ((uuid (substring (shell-command-to-string "uuidgen") 0 -1))
                   (file (file-name-nondirectory note)))
               (insert (format (concat ":PROPERTIES:\n:ID:       %s\n"
                                       ":CREATED:  ") uuid))
               (string-match
                (concat "\\`\\([0-9]\\{4\\}\\)"
                        "-\\([0-9]\\{2\\}\\)"
                        "-\\([0-9]\\{2\\}\\)"
                        "-\\([0-9]\\{2\\}\\)"
                        "-\\([0-9]\\{2\\}\\)"
                        "-\\([0-9]\\{2\\}\\)"
                        "\\.txt\\'") file)
               (let ((year (string-to-number (match-string 1 file)))
                     (mon (string-to-number (match-string 2 file)))
                     (day (string-to-number (match-string 3 file)))
                     (hour (string-to-number (match-string 4 file)))
                     (min (string-to-number (match-string 5 file)))
                     (sec (string-to-number (match-string 6 file))))
                 (insert (format "[%04d-%02d-%02d %s %02d:%02d]\n:END:\n"
                                 year mon day
                                 (calendar-day-name (list mon day year) t)
                                 hour min))))
             (buffer-string)))
          (delete-file note t)))
      (when (buffer-modified-p)
        (save-buffer))))
  ad-do-it
  (org-fit-agenda-window))

(defadvice org-archive-subtree (before set-billcode-before-archiving activate)
  "Before archiving a task, set its BILLCODE and TASKCODE."
  (let ((billcode (org-entry-get (point) "BILLCODE" t))
        (taskcode (org-entry-get (point) "TASKCODE" t))
        (project  (org-entry-get (point) "PROJECT" t)))
    (if billcode (org-entry-put (point) "BILLCODE" billcode))
    (if taskcode (org-entry-put (point) "TASKCODE" taskcode))
    (if project (org-entry-put (point) "PROJECT" project))))

(when (and (boundp 'org-completion-handler)
           (require 'helm nil t))
  (defun org-helm-completion-handler
      (prompt collection &optional predicate require-match
              initial-input hist def inherit-input-method)
    (helm-comp-read prompt
                    collection
                    ;; the character \ is filtered out by default ;(
                    :fc-transformer nil
                    :test predicate
                    :must-match require-match
                    :initial-input initial-input
                    :history hist
                    :default def))

  (setq org-completion-handler 'org-helm-completion-handler))

(defun org-show-pending ()
  (interactive)
  (with-current-buffer (find-file-noselect "~/Documents/todo.txt")
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward
              "\\(^<\\|DEADLINE: <\\)\\([0-9]\\{4\\}-.*?\\)>" nil t)
        (let ((due-date (match-string 2)))
          (message due-date))))))

(defun org-todo-score (&optional ignore)
  "Compute the score of an Org-mode task.
Age gradually decreases the value given to a task.  After 28
days, its score is zero.
Effort should act as a multiplier on the value."
  1)

(defvar org-categories-pending-hashmap nil)
(defvar org-categories-completed-hashmap nil)

(defun org-compute-category-totals ()
  (interactive)
  (setq org-categories-pending-hashmap (make-hash-table :test 'equal)
        org-categories-completed-hashmap (make-hash-table :test 'equal))
  (dolist (file '("todo.txt" "archive.txt"))
    (with-current-buffer
        (find-file-noselect (expand-file-name file "~/Documents"))
      (save-excursion
        (goto-char (point-min))
        (while (not (eobp))
          (outline-next-heading)
          (let* ((state (org-get-todo-state))
                 (category
                  (or (org-entry-get (point) "ARCHIVE_CATEGORY" t)
                      (org-entry-get (point) "CATEGORY" t)))
                 (hashmap
                  (cond
                   ((string= state "TODO") org-categories-pending-hashmap)
                   ((string= state "DONE") org-categories-completed-hashmap)))
                 (value (and hashmap (gethash category hashmap 0))))
            (if hashmap
                (puthash category (+ value (org-todo-score)) hashmap))))))))

(defun org-category-total (category)
  ;; A category's final score is the sum of all open tasks (which raises the
  ;; value), subtracted by the sum of all closed tasks.  Thus, a category with
  ;; a higher score deserves more attention (it has been neglected or has not
  ;; seen much activity), while a category with a low score deserves less.
  ;;
  ;; Note that this score is affected by several heuristics.  See
  ;; `org-todo-score'.
  (unless org-categories-pending-hashmap
    (org-compute-category-totals))
  (- (gethash category org-categories-pending-hashmap 0)
     (gethash category org-categories-completed-hashmap 0)))

(defun org-cmp-category-totals (a b)
  (let ((cat-a (get-text-property 1 'org-category a))
        (cat-b (get-text-property 1 'org-category b)))
    (if (> (org-category-total cat-a)
           (org-category-total cat-b))
        1
      -1)))

;; (setq org-agenda-cmp-user-defined 'org-cmp-category-totals)

(provide 'dot-org)

;; Local Variables:
;;   mode: emacs-lisp
;;   mode: allout
;;   outline-regexp: "^;;;_\\([,. ]+\\)"
;; End:

;;; dot-gnus.el ends here
