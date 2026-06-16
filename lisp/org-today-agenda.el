;;; org-today-agenda.el --- Daily action list as an org-super-agenda view  -*- lexical-binding: t; -*-

;; Copyright (C) 2026  John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Version: 0.1
;; Package-Requires: ((emacs "27.1") (org-ql "0.9") (org-super-agenda "1.3"))
;; Keywords: hypermedia, outlines, Org, agenda

;;; Commentary:

;; Invokes the `today' Claude Code skill with JSON output, parses the
;; result, and renders it as an interactive `org-ql-view' buffer
;; sectioned via `org-super-agenda' groups by bucket.  Each agenda item
;; is backed by a live Org marker, so all standard agenda commands work
;; (`t' to change state, `C-c C-t', RET to jump, etc.).
;;
;; The Claude `today' skill is documented at
;; ~/.claude/skills/today/SKILL.md.  It runs five SQL-bucket queries
;; against the org PostgreSQL database and synthesises 3-5 picks for
;; the day.  This Elisp layer is purely about display + interaction.
;;
;; Usage:
;;
;;   M-x org-today-agenda
;;
;; Or bind to a key:
;;
;;   (global-set-key (kbd "C-c a t") #'org-today-agenda)

;;; Code:

(require 'cl-lib)
(require 'json)
(require 'subr-x)
(require 'org)
(require 'org-id)
(require 'org-element)
(require 'org-ql)
(require 'org-ql-view)
(require 'org-super-agenda)

;;;; Customization

(defgroup org-today-agenda nil
  "Render Claude's `today' skill as an interactive org-super-agenda."
  :group 'org-agenda
  :prefix "org-today-agenda-")

(defcustom org-today-agenda-claude-executable "claude"
  "Path to the Claude Code CLI.
Resolved against `exec-path' if unqualified."
  :type 'string
  :group 'org-today-agenda)

(defcustom org-today-agenda-claude-args '("-p")
  "Base arguments to pass to the Claude CLI before the prompt.
Defaults to `-p' for non-interactive print mode.  Output format is
text (the skill emits JSON directly to stdout)."
  :type '(repeat string)
  :group 'org-today-agenda)

(defcustom org-today-agenda-prompt
  (concat "/today json\n\n"
          "IMPORTANT: Output ONLY the JSON object as specified in the "
          "today skill's `args=json' output mode. No prose, no markdown "
          "code fences, no preamble. Start with `{' and end with `}'.")
  "Prompt text sent to Claude.
The trailing instruction is a belt-and-suspenders defense against
Claude wrapping the JSON in markdown despite the skill's spec."
  :type 'string
  :group 'org-today-agenda)

(defcustom org-today-agenda-working-directory "~/doc/org"
  "Working directory for the Claude subprocess.
Must NOT match positron / git-ai / tron paths so the `ai' wrapper
selects the `personal' Claude config dir where the today skill lives."
  :type 'directory
  :group 'org-today-agenda)

(defcustom org-today-agenda-buffer-name "*Org Today*"
  "Name of the agenda buffer produced by `org-today-agenda'."
  :type 'string
  :group 'org-today-agenda)

;;;; Bucket metadata

(defconst org-today-agenda--bucket-labels
  '(("PICK" . "⭐ Picks for today")
    ("A"    . "🟢 Calendar today, A-priority")
    ("B"    . "🔴 Overdue A-priority")
    ("C"    . "🟡 In-flight (DOING, last 14d)")
    ("D"    . "🌑 Dormant A-priority")
    ("E"    . "🔁 Habits due today"))
  "Ordered alist of bucket code to display label.
Order here drives section order in the agenda.")

(defun org-today-agenda--super-agenda-groups ()
  "Return `org-super-agenda-groups' value sectioning by bucket code."
  (mapcar
   (lambda (cell)
     (let ((code (car cell)) (label (cdr cell)))
       `(:name ,label
         :pred ,(lambda (item)
                  (equal code
                         (or (org-element-property :claude-today-bucket item)
                             (get-text-property 0 :claude-today-bucket item)))))))
   org-today-agenda--bucket-labels))

;;;; Locating live headings

(defun org-today-agenda--find-id (id)
  "Try `org-id-find' on ID in original case, then downcased, then upcased.
The org PostgreSQL indexer preserves the case stored in the file
itself, which is sometimes uppercase and sometimes lowercase across
the corpus.  Emacs's `org-id-find' is case-sensitive, so the JSON's
case may not match what's in `org-id-locations'."
  (when id
    (or (ignore-errors (org-id-find id 'marker))
        (let ((down (downcase id)))
          (and (not (equal down id))
               (ignore-errors (org-id-find down 'marker))))
        (let ((up (upcase id)))
          (and (not (equal up id))
               (ignore-errors (org-id-find up 'marker)))))))

(defun org-today-agenda--locate (id file byte-offset title)
  "Return a marker pointing at the entry identified by ID/FILE/BYTE-OFFSET/TITLE.
Strategy:
  1. `org-id-find' on ID (with case-fallback) — most reliable when the
     org-id cache is fresh.
  2. Title search in FILE — robust against byte-offset drift from
     stale DB indexing or edits since the last `make store'.
  3. Byte offset — only when buffer matches disk AND lands on a real
     headline (treats DB byte_offsets as advisory, not authoritative)."
  (or
   (org-today-agenda--find-id id)
   (and file (file-readable-p file)
        (let ((buf (or (find-buffer-visiting file)
                       (let ((b (delay-mode-hooks (find-file-noselect file t))))
                         (with-current-buffer b
                           (unless (derived-mode-p 'org-mode)
                             (delay-mode-hooks (org-mode))))
                         b))))
          (when buf
            (with-current-buffer buf
              (org-with-wide-buffer
               (let ((pos
                      (or
                       ;; Title search at start of headline line.
                       (and title
                            (let ((case-fold-search nil))
                              (goto-char (point-min))
                              (catch 'found
                                (while (search-forward title nil t)
                                  (beginning-of-line)
                                  (when (looking-at-p "^\\*+\\s-")
                                    (throw 'found (point)))
                                  (forward-line 1))
                                nil)))
                       ;; Byte offset — last resort, only on a real heading.
                       (and byte-offset (not (buffer-modified-p))
                            (let ((p (ignore-errors
                                       (filepos-to-bufferpos byte-offset 'exact))))
                              (when (and p
                                         (<= p (point-max))
                                         (progn (goto-char p)
                                                (looking-at-p "^\\*+\\s-")))
                                p))))))
                 (and pos (copy-marker pos))))))))))

;;;; Element construction

(defun org-today-agenda--element-from-row (row bucket-override)
  "Parse the heading referenced by ROW into an org-element and tag it.
ROW is an alist with keys `id', `file', `byte_offset', `title', `bucket',
`rationale'.  BUCKET-OVERRIDE, when non-nil, replaces the bucket code
(used to stamp picks with `PICK')."
  (let* ((id (alist-get 'id row))
         (file (alist-get 'file row))
         (byte-offset (alist-get 'byte_offset row))
         (title (alist-get 'title row))
         (bucket (or bucket-override (alist-get 'bucket row)))
         (rationale (alist-get 'rationale row))
         (marker (org-today-agenda--locate id file byte-offset title)))
    (when marker
      (with-current-buffer (marker-buffer marker)
        (org-with-wide-buffer
         (goto-char marker)
         (let ((element (org-ql--add-markers
                         (org-element-headline-parser (line-end-position)))))
           (org-element-put-property element :claude-today-bucket bucket)
           (when rationale
             (org-element-put-property element :claude-today-rationale rationale))
           element))))))

(defun org-today-agenda--collect (json)
  "Return a deduplicated list of org-elements from parsed JSON.
Picks are tagged with bucket `PICK' so super-agenda groups them first."
  (let* ((picks (alist-get 'picks json))
         (buckets (alist-get 'buckets json))
         (pick-ids (let ((h (make-hash-table :test 'equal)))
                     (dolist (p picks) (puthash (alist-get 'id p) t h))
                     h))
         (seen (make-hash-table :test 'equal))
         elements)
    ;; Picks first — gives them the live element when an entry also
    ;; appears in a bucket.
    (dolist (p picks)
      (let ((id (alist-get 'id p)))
        (unless (gethash id seen)
          (puthash id t seen)
          (when-let ((el (org-today-agenda--element-from-row p "PICK")))
            (push el elements)))))
    ;; Then bucketed entries that aren't already picked.
    (dolist (bucket-pair buckets)
      (dolist (row (cdr bucket-pair))
        (let ((id (alist-get 'id row)))
          (unless (gethash id seen)
            (puthash id t seen)
            (when-let ((el (org-today-agenda--element-from-row row nil)))
              (push el elements))))))
    (nreverse elements)))

;;;; Format augmentation

(defun org-today-agenda--annotate-string (el str)
  "Append the rationale (if any) on a continuation line after STR."
  (let ((rationale (org-element-property :claude-today-rationale el)))
    (if (and rationale (not (string-empty-p rationale)))
        (concat str (propertize (concat "\n    " rationale)
                                'face 'org-agenda-dimmed-todo-face))
      str)))

;;;; JSON extraction

(defun org-today-agenda--extract-json (buffer)
  "Return the parsed JSON object in BUFFER, or signal `user-error'.
Tolerates Claude prepending prose/code-fence: skips to the first `{'
that begins a JSON object."
  (with-current-buffer buffer
    (goto-char (point-min))
    (unless (re-search-forward "^\\s-*{" nil t)
      (user-error "org-today-agenda: no JSON object in Claude output: %s"
                  (buffer-substring-no-properties
                   (point-min) (min (point-max) (+ (point-min) 400)))))
    (goto-char (match-beginning 0))
    (condition-case err
        (json-parse-buffer :object-type 'alist :array-type 'list :null-object nil)
      (json-parse-error
       (user-error "org-today-agenda: JSON parse error: %s"
                   (error-message-string err))))))

;;;; Display

(defun org-today-agenda--display (elements)
  "Render ELEMENTS into the today agenda buffer."
  (let* ((title (format "Today (%s)" (format-time-string "%Y-%m-%d")))
         (strings
          (mapcar (lambda (el)
                    (org-today-agenda--annotate-string
                     el (org-ql-view--format-element el)))
                  elements))
         (org-ql-view-buffers-files nil)
         (org-ql-view-query nil)
         (org-ql-view-sort nil)
         (org-ql-view-narrow nil)
         (org-ql-view-title title)
         (org-ql-view-super-groups (org-today-agenda--super-agenda-groups)))
    (org-ql-view--display
     :header (org-ql-view--header-line-format :title title)
     :strings strings)
    (when-let ((buf (get-buffer org-ql-view-buffer)))
      (with-current-buffer buf
        (rename-buffer org-today-agenda-buffer-name t)))))

;;;; Async entry point

(defvar org-today-agenda--process nil
  "Currently running Claude subprocess, if any.")

;;;###autoload
(defun org-today-agenda ()
  "Run the Claude `today' skill and display today's action list.

Spawns Claude asynchronously (latency ~30–60s) and renders the result
as an interactive `org-ql-view' buffer sectioned via `org-super-agenda'
into buckets: picks, today's calendar, overdue, in-flight, dormant,
habits.  Live markers mean all standard agenda commands work."
  (interactive)
  (when (and org-today-agenda--process
             (process-live-p org-today-agenda--process))
    (user-error "org-today-agenda: a Claude subprocess is already running"))
  (let* ((stdout-buf (generate-new-buffer " *org-today-claude-stdout*"))
         (stderr-buf (generate-new-buffer " *org-today-claude-stderr*"))
         (default-directory (expand-file-name org-today-agenda-working-directory))
         (start (current-time)))
    (message "org-today-agenda: invoking Claude (this may take ~30-60s)…")
    (setq org-today-agenda--process
          (make-process
           :name "org-today-claude"
           :buffer stdout-buf
           :stderr stderr-buf
           :noquery t
           :command (append (list org-today-agenda-claude-executable)
                            org-today-agenda-claude-args
                            (list org-today-agenda-prompt))
           :sentinel
           (lambda (proc event)
             (when (memq (process-status proc) '(exit signal))
               (setq org-today-agenda--process nil)
               (unwind-protect
                   (let ((exit (process-exit-status proc))
                         (elapsed (float-time (time-since start))))
                     (cond
                      ((not (zerop exit))
                       (user-error
                        "org-today-agenda: claude exit %d after %.1fs: %s"
                        exit elapsed
                        (with-current-buffer stderr-buf
                          (string-trim
                           (buffer-substring-no-properties
                            (point-min) (min (point-max) 800))))))
                      (t
                       (let* ((json (org-today-agenda--extract-json stdout-buf))
                              (elements (org-today-agenda--collect json)))
                         (unless elements
                           (user-error "org-today-agenda: no entries located"))
                         (org-today-agenda--display elements)
                         (message
                          "org-today-agenda: %d items in %.1fs"
                          (length elements) elapsed)))))
                 (when (buffer-live-p stdout-buf) (kill-buffer stdout-buf))
                 (when (buffer-live-p stderr-buf) (kill-buffer stderr-buf)))))))))

;;;###autoload
(defun org-today-agenda-show-raw ()
  "Run Claude `today' and display the raw JSON in a buffer.
Useful for debugging the skill or the JSON parsing path."
  (interactive)
  (let ((default-directory (expand-file-name org-today-agenda-working-directory))
        (buf (get-buffer-create "*org-today-raw*")))
    (with-current-buffer buf
      (erase-buffer)
      (let ((exit (apply #'call-process
                         org-today-agenda-claude-executable nil t nil
                         (append org-today-agenda-claude-args
                                 (list org-today-agenda-prompt)))))
        (insert (format "\n;; exit=%d\n" exit)))
      (goto-char (point-min)))
    (display-buffer buf)))

(provide 'org-today-agenda)
;;; org-today-agenda.el ends here
