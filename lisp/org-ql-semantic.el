;;; org-ql-semantic.el --- Semantic search for org-ql via vector embeddings  -*- lexical-binding: t; -*-

;; Copyright (C) 2024-2026  John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Url: https://github.com/jwiegley/org-ql-semantic
;; Version: 0.1
;; Package-Requires: ((emacs "27.1") (org-ql "0.9"))
;; Keywords: hypermedia, outlines, Org, search

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; This library extends `org-ql' with a `semantic' predicate backed by
;; vector-embedding similarity search in a PostgreSQL database.  An
;; external Haskell CLI tool (`org db search') performs the actual
;; embedding lookup and returns matching entry IDs with relevance
;; scores.  The predicate then checks each heading against the cached
;; result set (by byte offset or :ID: property), enabling seamless
;; composition with all other `org-ql' predicates.
;;
;; Usage:
;;
;;   ;; Interactive semantic search displayed in an org-ql-view buffer:
;;   M-x org-ql-semantic-search RET "machine learning techniques" RET
;;
;;   ;; Programmatic use (query only needs to be specified once):
;;   (org-ql-semantic-search "project deadlines")
;;
;;   ;; Combined with other predicates:
;;   (org-ql-search (org-ql-semantic-files "project deadlines")
;;     '(and (semantic "project deadlines")
;;           (todo "TODO"))
;;     :sort #'org-ql-semantic--sort-by-score)

;;; Code:

;;;; Requirements

(require 'cl-lib)
(require 'subr-x)
(require 'org)
(require 'org-ql)
(require 'org-ql-search)

;;;; Customization

(defgroup org-ql-semantic nil
  "Semantic search integration for `org-ql'."
  :group 'org-ql
  :prefix "org-ql-semantic-")

(defcustom org-ql-semantic-org-executable "org"
  "Path to the `org' CLI executable.
This tool must support the `db search' subcommand."
  :type 'string
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-config-file nil
  "Path to the org YAML configuration file.
Passed as --config to the `org' CLI.  Required for all CLI invocations."
  :type '(choice (const :tag "None (will error)" nil)
                 (file :tag "Config file path"))
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-db-url nil
  "PostgreSQL connection URL for the embeddings database.
When non-nil, passed as the --db-url argument to `org db search'.
When nil, the tool uses its own default."
  :type '(choice (const :tag "Use tool default" nil)
                 (string :tag "Database URL"))
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-base-url nil
  "Base URL for the embedding API.
Passed as --base-url to `org db search'.  This MUST match the URL
used when embeddings were generated, or search results will be
meaningless.  Required."
  :type '(choice (const :tag "Not configured (will error)" nil)
                 (string :tag "API base URL"))
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-model nil
  "Embedding model name.
Passed as --model to `org db search'.  This MUST match the model
used when embeddings were generated, or search results will be
meaningless.  Required."
  :type '(choice (const :tag "Not configured (will error)" nil)
                 (string :tag "Model name"))
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-api-key nil
  "API key for the embedding service.
When non-nil, passed as --api-key to `org db search'.
Consider using `auth-source' or an environment variable instead
of storing the key directly in this variable."
  :type '(choice (const :tag "Use tool default" nil)
                 (string :tag "API key"))
  :group 'org-ql-semantic)

;; (defcustom org-ql-semantic-dimensions nil
;;   "Number of dimensions for the embedding vectors.
;; When non-nil, passed as --dimensions to `org db search'."
;;   :type '(choice (const :tag "Use tool default" nil)
;;                  (integer :tag "Dimensions"))
;;   :group 'org-ql-semantic)

(defcustom org-ql-semantic-files-directory nil
  "Base directory for resolving relative file paths from the database.
When non-nil, relative paths returned by `org db search' are resolved
against this directory.  When nil, defaults to `org-directory'."
  :type '(choice (const :tag "Use org-directory" nil)
                 (directory :tag "Base directory"))
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-default-limit 2000
  "Default maximum number of results to return from semantic search."
  :type 'integer
  :group 'org-ql-semantic)

(defcustom org-ql-semantic-max-distance 0.5
  "Maximum cosine distance for semantic search results.
Results with a distance greater than this are filtered out as
irrelevant.  Lower values are stricter (only very similar matches).
Cosine distance ranges from 0.0 (identical) to ~1.0 (unrelated)
for normalized embeddings.  Typical useful range: 0.3-0.7."
  :type 'number
  :group 'org-ql-semantic)

;;;; Path resolution

(defun org-ql-semantic--expand-file (file)
  "Expand FILE relative to the configured org files directory.
Uses `org-ql-semantic-files-directory' if set, otherwise `org-directory'."
  (expand-file-name file (or org-ql-semantic-files-directory org-directory)))

;;;; Internal state

(defvar org-ql-semantic--cache (make-hash-table :test 'equal)
  "Cache mapping query strings to search results.
Each value is a plist with keys:
  :ids     - hash table mapping entry ID strings to similarity scores
  :offsets - hash table mapping \"file:byte-offset\" to similarity scores
  :files   - list of unique file paths containing matches")

;;;; Cache management

;;;###autoload
(defun org-ql-semantic-clear-cache ()
  "Clear the semantic search result cache."
  (interactive)
  (clrhash org-ql-semantic--cache)
  (when (called-interactively-p 'interactive)
    (message "org-ql-semantic: cache cleared")))

;;;; CLI invocation

(defun org-ql-semantic--build-args (query &optional limit)
  "Build command-line arguments for `org db search'.
QUERY is the search text.  LIMIT overrides `org-ql-semantic-default-limit'.
The `org' CLI requires --config and input files for all invocations.
Note: --db-url is a `db' subcommand option and must precede `search'."
  (unless org-ql-semantic-config-file
    (user-error "org-ql-semantic: `org-ql-semantic-config-file' must be set"))
  (unless org-ql-semantic-base-url
    (user-error "org-ql-semantic: `org-ql-semantic-base-url' must be set (e.g. \"http://localhost:8080\")"))
  (unless org-ql-semantic-model
    (user-error "org-ql-semantic: `org-ql-semantic-model' must be set (e.g. \"bge-m3\")"))
  (let ((global-args (list "--config" (expand-file-name org-ql-semantic-config-file)))
        (db-args (list "db"))
        (search-args (list "search" query
                           "--format" "json"
                           "--limit" (number-to-string (or limit
                                                           org-ql-semantic-default-limit))
                           "--base-url" org-ql-semantic-base-url
                           "--model" org-ql-semantic-model))
        (input-args nil))
    (when org-ql-semantic-db-url
      (setq db-args (append db-args (list "--db-url" org-ql-semantic-db-url))))
    (when org-ql-semantic-api-key
      (setq search-args (append search-args (list "--api-key" org-ql-semantic-api-key))))
    ;; (when org-ql-semantic-dimensions
    ;;   (setq search-args (append search-args (list "--dimensions"
    ;;                                                (number-to-string org-ql-semantic-dimensions)))))
    (append global-args db-args search-args input-args)))

(defun org-ql-semantic--run-search (query &optional limit)
  "Run `org db search' for QUERY and return parsed results.
LIMIT overrides `org-ql-semantic-default-limit'.
Returns a list of alists, each parsed from one JSON line of output."
  (let ((args (org-ql-semantic--build-args query limit))
        (stderr-file (make-temp-file "org-ql-semantic-stderr")))
    (unwind-protect
        (with-temp-buffer
          (let ((exit-code (apply #'call-process
                                  org-ql-semantic-org-executable
                                  nil          ; no input
                                  (list (current-buffer) stderr-file)
                                  nil          ; don't redisplay
                                  args)))
            (unless (zerop exit-code)
              (user-error "org-ql-semantic: `%s db search' failed (exit %d): %s"
                          org-ql-semantic-org-executable exit-code
                          (with-temp-buffer
                            (insert-file-contents stderr-file)
                            (string-trim (buffer-string)))))
            (goto-char (point-min))
            (let (results)
              (while (not (eobp))
                (let ((line (buffer-substring-no-properties
                             (line-beginning-position) (line-end-position))))
                  (unless (string-empty-p (string-trim line))
                    (condition-case err
                        (push (json-parse-string line :object-type 'alist
                                                        :null-object nil)
                              results)
                      (json-parse-error
                       (message "org-ql-semantic: skipping malformed JSON line: %s"
                                (error-message-string err))))))
                (forward-line 1))
              (nreverse results))))
      (delete-file stderr-file))))

;;;; Cache population

(defun org-ql-semantic--offset-key (file byte-offset)
  "Return a cache key string for FILE at BYTE-OFFSET.
FILE is normalized via `file-truename' so symlinks don't cause mismatches
between the database paths and Emacs `buffer-file-name'."
  (format "%s:%d" (file-truename file) byte-offset))

(defun org-ql-semantic--title-key (file title)
  "Return a cache key string for FILE and TITLE.
FILE is normalized via `file-truename'."
  (format "%s:%s" (file-truename file) (downcase title)))

(defun org-ql-semantic--ensure-cache (query &optional limit)
  "Ensure QUERY results are cached, running the search if needed.
LIMIT overrides `org-ql-semantic-default-limit'.
Returns the cached plist for QUERY."
  (or (let ((cached (gethash query org-ql-semantic--cache)))
        (and cached
             (plist-get cached :offsets)
             (> (hash-table-count (plist-get cached :offsets)) 0)
             cached))
      (let* ((results (org-ql-semantic--run-search query limit))
             (ids (make-hash-table :test 'equal))
             (offsets (make-hash-table :test 'equal))
             (titles (make-hash-table :test 'equal))
             (files nil))
        (dolist (result results)
          (let* ((id (alist-get 'id result))
                 (file (alist-get 'file result))
                 (title (alist-get 'title result))
                 (byte-offset (alist-get 'byte_offset result))
                 (distance (or (alist-get 'distance result) 1.0))
                 (score (- 1.0 (float distance))))
            (when id
              (puthash id score ids))
            (when (and file byte-offset)
              (puthash (org-ql-semantic--offset-key file byte-offset)
                       score offsets))
            (when (and file title)
              (puthash (org-ql-semantic--title-key file title)
                       score titles))
            (when file
              ;; Use the original CLI path rather than file-truename for the
              ;; files list.  org-ql-select calls find-buffer-visiting which
              ;; resolves truenames internally; passing symlink paths ensures
              ;; it finds existing buffers that were opened via the symlink.
              ;; Truename paths may fail to match buffer-file-truename when
              ;; the symlink chain traverses Nix store paths that have been
              ;; rebuilt since the buffer was opened.
              (let ((normalized (org-ql-semantic--expand-file file)))
                (unless (member normalized files)
                  (push normalized files))))))
        ;; Filter out non-existent files to avoid "Can't open file"
        ;; warnings from org-ql-select that could confuse the user.
        (let* ((live-files (seq-filter #'file-readable-p (nreverse files)))
               (entry (list :ids ids :offsets offsets :titles titles
                            :files live-files)))
          (puthash query entry org-ql-semantic--cache)
          entry))))

;;;; Public API for file lists

;;;###autoload
(defun org-ql-semantic-files (query &optional limit)
  "Return list of files containing entries matching semantic QUERY.
LIMIT overrides `org-ql-semantic-default-limit'.
This is useful for pre-filtering the buffer list passed to
`org-ql-select' or `org-ql-search'."
  (let ((cache-entry (org-ql-semantic--ensure-cache query limit)))
    (plist-get cache-entry :files)))

;;;; Predicate helpers

(defun org-ql-semantic--match-score (query)
  "Return the semantic score for the heading at point for QUERY.
Tries byte-offset match first, then :ID: property, then title match.
Returns nil if no match.

The byte-offset check is only attempted when the buffer has not been
modified since its file was last read or saved; unsaved edits shift
heading positions and would produce false matches against stale
database offsets."
  (let ((cache-entry (gethash query org-ql-semantic--cache)))
    (when cache-entry
      (let ((offsets (plist-get cache-entry :offsets))
            (ids (plist-get cache-entry :ids))
            (titles (plist-get cache-entry :titles)))
        (or
         ;; Primary: match by :ID: property (always reliable).
         (when-let* ((id (org-entry-get nil "ID")))
           (gethash id ids))
         ;; Fallback 1: match by file + title (robust).
         (when titles
           (when-let* ((file (buffer-file-name))
                       (heading (org-get-heading t t t t))
                       (key (org-ql-semantic--title-key file heading)))
             (gethash key titles)))
         ;; Fallback 2: match by file path + file byte offset.
         ;; Only when unmodified — even saved edits shift offsets
         ;; relative to the DB, but at least this catches the
         ;; unsaved-buffer case.
         (when (and (not (buffer-modified-p))
                    (buffer-file-name))
           (when-let* ((file (buffer-file-name))
                       (byte-pos (bufferpos-to-filepos (point) 'exact))
                       (key (org-ql-semantic--offset-key file byte-pos)))
             (gethash key offsets))))))))

;;;; Predicate definition

(org-ql-defpred semantic (query)
  "Return non-nil if current heading matches semantic QUERY.
QUERY is a natural-language search string.  The first time a
given QUERY is used, the external `org db search' tool is called
to find matching entry IDs via vector-embedding similarity.
Subsequent uses of the same QUERY within a session use the
cached result set.

This predicate checks the current heading against the search
results by byte offset (primary) or :ID: property (fallback)."
  :normalizers ((`(semantic ,query)
                 (org-ql-semantic--ensure-cache query)
                 `(semantic ,query)))
  :body
  (org-ql-semantic--match-score query))

;;;; Sort comparator

(defun org-ql-semantic--sort-by-score (a b)
  "Compare Org elements A and B by semantic relevance score.
Returns non-nil if A should appear before B (higher score first).
Intended for use as the :sort argument to `org-ql-select' or
`org-ql-search'.

Elements are compared by looking up each element's score
in the semantic search cache.  Elements without a cached score
are sorted to the end."
  (let ((score-a (org-ql-semantic--element-score a))
        (score-b (org-ql-semantic--element-score b)))
    (> score-a score-b)))

(defun org-ql-semantic--element-score (element)
  "Return the semantic relevance score for ELEMENT.
Looks up the element by byte offset, ID, or title across all cached queries.
Returns 0.0 if no score is found."
  (let ((score 0.0))
    (maphash
     (lambda (_query entry)
       (let ((offsets (plist-get entry :offsets))
             (ids (plist-get entry :ids))
             (titles (plist-get entry :titles))
             (s nil))
         ;; Try ID first (always reliable).
         (when-let* ((id (org-element-property :ID element)))
           (setq s (gethash id ids)))
         ;; Fall back to title.
         (unless s
           (when (and titles (org-element-property :file element))
             (when-let* ((file (org-element-property :file element))
                         (title (org-element-property :raw-value element))
                         (key (org-ql-semantic--title-key file title)))
               (setq s (gethash key titles)))))
         ;; Last resort: byte offset (only for unmodified buffers).
         (unless s
           (when-let* ((file (org-element-property :file element))
                       (begin (org-element-property :begin element)))
             (let ((buf (find-buffer-visiting file)))
               (when (and buf (not (buffer-modified-p buf)))
                 (let ((byte-pos (with-current-buffer buf
                                   (bufferpos-to-filepos begin 'exact))))
                   (when byte-pos
                     (setq s (gethash (org-ql-semantic--offset-key file byte-pos)
                                      offsets))))))))
         (when (and s (> s score))
           (setq score s))))
     org-ql-semantic--cache)
    score))

;;;; Direct element collection

(defun org-ql-semantic--find-file-fast (file)
  "Return a buffer visiting FILE, opening it quickly if needed.
If FILE is already open, return that buffer.  Otherwise open it
with mode hooks suppressed so large org files don't stall."
  (or (find-buffer-visiting file)
      (let ((buf (delay-mode-hooks (find-file-noselect file t))))
        (with-current-buffer buf
          (unless (derived-mode-p 'org-mode)
            (delay-mode-hooks (org-mode))))
        buf)))

(defun org-ql-semantic--heading-title ()
  "Return the raw heading title at point, without TODO/priority/tags.
Uses a regexp to avoid `org-get-heading' which can trigger slow parsing."
  (when (looking-at org-complex-heading-regexp)
    (match-string-no-properties 4)))

(defun org-ql-semantic--normalize-title (title)
  "Strip any leading TODO keyword from TITLE for matching.
The DB may store titles like \"DONE Visit foo\" while `org-complex-heading-regexp'
group 4 returns just \"Visit foo\"."
  (if (string-match (concat "^\\(?:" (mapconcat #'regexp-quote org-todo-keywords-1 "\\|")
                            "\\)\\s-+")
                    title)
      (substring title (match-end 0))
    title))

(defun org-ql-semantic--title-matches-p (heading target)
  "Return non-nil if HEADING matches TARGET.
Both should be downcased.  Accepts exact or substring match in
either direction (the DB headline may include trailing tags and
whitespace that the extracted heading title lacks)."
  (or (string= heading target)
      (string-match-p (regexp-quote target) heading)
      (string-match-p (regexp-quote heading) target)))

(defun org-ql-semantic--locate-heading (byte-offset title)
  "Locate heading in current buffer by BYTE-OFFSET or TITLE.
Returns buffer position of the heading, or nil."
  (let* ((normalized (and title (org-ql-semantic--normalize-title title)))
         (found nil)
         (target (and normalized (downcase normalized))))
    ;; Try byte offset first, but verify the title matches.
    (when (and byte-offset target)
      (let ((pos (filepos-to-bufferpos byte-offset 'exact)))
        (when (and pos (<= pos (point-max)))
          (goto-char pos)
          (when (and (bolp) (looking-at-p "\\*")
                     (let ((h (org-ql-semantic--heading-title)))
                       (and h (org-ql-semantic--title-matches-p
                               (downcase h) target))))
            (setq found (point))))))
    ;; Fallback: search for normalized title text directly.
    (unless found
      (when target
        (goto-char (point-min))
        (while (and (not found) (search-forward normalized nil t))
          (beginning-of-line)
          (when (and (looking-at-p "\\*")
                     (let ((h (org-ql-semantic--heading-title)))
                       (and h (org-ql-semantic--title-matches-p
                               (downcase h) target))))
            (setq found (point)))
          (unless found (forward-line 1)))))
    found))

;;;; Interactive command

;;;###autoload
(defun org-ql-semantic--done-keywords ()
  "Return list of done-state TODO keywords.
Derives from `org-todo-keywords' (global) since `org-done-keywords'
is buffer-local and may be nil outside Org buffers."
  (or org-done-keywords
      (let (done)
        (dolist (entry org-todo-keywords)
          (when (listp entry)
            (let ((after-bar nil))
              (dolist (kw (cdr entry))
                (if (equal kw "|")
                    (setq after-bar t)
                  (when after-bar
                    (push (if (string-match "\\`\\([^(]+\\)" kw)
                              (match-string 1 kw)
                            kw)
                          done)))))))
        done)))

(defun org-ql-semantic--active-entry-p (result)
  "Return non-nil if RESULT is an open TODO, NOTE, QUOTE or PROMPT entry.
Entries with no keyword are excluded.  Entries whose keyword is a
done state (per `org-todo-keywords') are excluded.  All other
keyword entries are kept."
  (let* ((kw (alist-get 'keyword result))
         (effective-kw
          (or kw
              (let ((case-fold-search nil)
                    (hl (or (alist-get 'headline result) "")))
                (when (string-match "\\`\\([A-Z]+\\)\\(?: \\|$\\)" hl)
                  (match-string 1 hl))))))
    (when effective-kw
      (not (member effective-kw (org-ql-semantic--done-keywords))))))

(defun org-ql-semantic-search (query &optional all)
  "Search Org files semantically for QUERY and display results.
Runs `org db search' and displays the results directly in an
`org-ql-view' buffer sorted by relevance.

By default only shows entries with open TODO keywords, NOTE, QUOTE or
PROMPT. With prefix argument ALL, shows all results."
  (interactive
   (list (read-string "Semantic search: ")
         current-prefix-arg))
  (when (string-empty-p (string-trim query))
    (user-error "Query must not be empty"))
  (message "org-ql-semantic: running CLI search...")
  (let* ((raw-results (org-ql-semantic--run-search query nil))
         (results (if all raw-results
                    (seq-filter #'org-ql-semantic--active-entry-p raw-results)))
         (results (if org-ql-semantic-max-distance
                      (seq-filter
                       (lambda (r)
                         (<= (or (alist-get 'distance r) 1.0)
                             org-ql-semantic-max-distance))
                       results)
                    results))
         (elements nil)
         (by-file (make-hash-table :test 'equal))
         (unreadable-count 0)
         (no-file-count 0)
         (locate-fail-count 0)
         (grouped-count 0))
    (unless results
      (user-error "No results for semantic query: %s" query))
    (message "org-ql-semantic: CLI returned %d results (%d after filter), locating headings..."
             (length raw-results) (length results))
    ;; Group results by file so we only open each file once.
    (dolist (result results)
      (let ((file (alist-get 'file result)))
        (if (not file)
            (cl-incf no-file-count)
          (let ((expanded (org-ql-semantic--expand-file file)))
            (if (not (file-readable-p expanded))
                (progn
                  (cl-incf unreadable-count)
                  (when (<= unreadable-count 3)
                    (message "org-ql-semantic: unreadable: %s" expanded)))
              (cl-incf grouped-count)
              (push result (gethash expanded by-file)))))))
    (message "org-ql-semantic: grouped %d into %d files (%d no-file, %d unreadable)"
             grouped-count (hash-table-count by-file) no-file-count unreadable-count)
    ;; Process each file once.
    (maphash
     (lambda (file file-results)
       (condition-case err
           (with-current-buffer (org-ql-semantic--find-file-fast file)
             (org-with-wide-buffer
              (dolist (result (nreverse file-results))
                (condition-case err
                    (let* ((headline (alist-get 'headline result))
                           (title (alist-get 'title result))
                           (byte-offset (alist-get 'byte_offset result))
                           (distance (or (alist-get 'distance result) 1.0))
                           (score (- 1.0 (float distance)))
                           (pos (org-ql-semantic--locate-heading
                                 byte-offset title)))
                      (if pos
                          (progn
                            (goto-char pos)
                            (let ((element (org-ql--add-markers
                                            (org-element-headline-parser
                                             (line-end-position)))))
                              (org-element-put-property element :org-ql-semantic-score score)
                              (push (cons score element) elements)))
                        (cl-incf locate-fail-count)
                        (when (<= locate-fail-count 3)
                          (message "org-ql-semantic: locate failed: offset=%s title=%s in %s"
                                   byte-offset (or headline title) file))))
                  (error
                   (message "org-ql-semantic: error locating in %s: %s"
                            file (error-message-string err)))))))
         (error
          (message "org-ql-semantic: skipping file %s: %s" file (error-message-string err)))))
     by-file)
    ;; Sort by score descending and deduplicate by title (the same
    ;; heading may exist in both an active file and an archive file as
    ;; separate DB entries; keep only the highest-scored instance).
    (setq elements (mapcar #'cdr (sort elements (lambda (a b) (> (car a) (car b))))))
    (let ((seen-titles (make-hash-table :test 'equal)))
      (setq elements
            (seq-filter
             (lambda (elem)
               (let ((title (org-element-property :raw-value elem)))
                 (if (or (null title) (gethash title seen-titles))
                     nil
                   (puthash title t seen-titles)
                   t)))
             elements)))
    (unless elements
      (user-error "Could not locate any headings for query: %s" query))
    (message "org-ql-semantic: found %d headings (%d locate failures), formatting..."
             (length elements) locate-fail-count)
    (let* ((strings (mapcar #'org-ql-view--format-element elements))
           (title (format "Semantic%s: %s"
                          (if all "" " (active)") query))
           (org-ql-view-buffers-files nil)
           (org-ql-view-query nil)
           (org-ql-view-sort nil)
           (org-ql-view-narrow nil)
           (org-ql-view-super-groups nil)
           (org-ql-view-title title))
      (message "org-ql-semantic: displaying %d results..." (length strings))
      (org-ql-view--display
       :header (org-ql-view--header-line-format :title title)
       :strings strings))))

;;;; Diagnostics

;;;###autoload
(defun org-ql-semantic-dump-cache (query)
  "Dump the cache contents for QUERY to help diagnose matching issues.
Clears cache, re-runs the search, then shows what was cached."
  (interactive "sQuery to diagnose: ")
  (org-ql-semantic-clear-cache)
  (let* ((cache-entry (org-ql-semantic--ensure-cache query))
         (ids (plist-get cache-entry :ids))
         (offsets (plist-get cache-entry :offsets))
         (titles (plist-get cache-entry :titles))
         (files (plist-get cache-entry :files))
         (matched 0)
         (tested 0))
    (with-output-to-temp-buffer "*org-ql-semantic-cache*"
      (princ (format "Query: %S\n\n" query))
      (princ (format "=== FILES (%d) ===\n" (length files)))
      (dolist (f files) (princ (format "  %s\n" f)))
      (princ (format "\n=== IDS (%d) ===\n" (hash-table-count ids)))
      (maphash (lambda (k v) (princ (format "  %s -> %.4f\n" k v))) ids)
      (princ (format "\n=== OFFSETS (%d) ===\n" (hash-table-count offsets)))
      (maphash (lambda (k v) (princ (format "  %s -> %.4f\n" k v))) offsets)
      (princ (format "\n=== TITLES (%d) ===\n" (hash-table-count titles)))
      (maphash (lambda (k v) (princ (format "  %s -> %.4f\n" k v))) titles)
      (princ "\n=== MATCHING TEST ===\n")
      (dolist (file files)
        (if (not (file-exists-p file))
            (princ (format "  SKIPPED (not found): %s\n" file))
          (with-current-buffer (find-file-noselect file)
            (princ (format "  FILE: %s  modified: %s\n"
                           (buffer-file-name) (buffer-modified-p)))
            (org-with-wide-buffer
             (goto-char (point-min))
             (while (re-search-forward org-heading-regexp nil t)
               (save-excursion
                 (beginning-of-line)
                 (cl-incf tested)
                 (let ((score (org-ql-semantic--match-score query)))
                   (when score
                     (cl-incf matched)
                     (let* ((heading (org-get-heading t t t t))
                            (bpos (bufferpos-to-filepos (point) 'exact))
                            (id (org-entry-get nil "ID"))
                            (okey (org-ql-semantic--offset-key
                                   (buffer-file-name) bpos))
                            (tkey (when heading
                                    (org-ql-semantic--title-key
                                     (buffer-file-name) heading))))
                       (princ (format "  MATCH [%.4f]: %s\n" score heading))
                       (princ (format "    offset=%d/%s id=%s/%s title=%s\n\n"
                                      bpos
                                      (if (gethash okey offsets) "YES" "no")
                                      (or id "-")
                                      (if (and id (gethash id ids)) "YES" "no")
                                      (if (and tkey (gethash tkey titles))
                                          "YES" "no"))))))))))))
      (princ (format "\nTested %d headings, matched %d\n" tested matched)))))

;;;###autoload
(defun org-ql-semantic-test-search (query)
  "Run the CLI search for QUERY and display raw results for debugging.
Shows the exact command, exit code, stdout, stderr, and parsed results."
  (interactive "sTest search query: ")
  (let* ((args (org-ql-semantic--build-args query 5))
         (stderr-file (make-temp-file "org-ql-semantic-stderr")))
    (with-output-to-temp-buffer "*org-ql-semantic-test*"
      (princ (format "Executable: %s\n" org-ql-semantic-org-executable))
      (princ (format "Args: %S\n\n" args))
      (unwind-protect
          (with-temp-buffer
            (let ((exit-code (apply #'call-process
                                    org-ql-semantic-org-executable
                                    nil
                                    (list (current-buffer) stderr-file)
                                    nil
                                    args)))
              (let ((stdout (buffer-string))
                    (stderr (with-temp-buffer
                              (insert-file-contents stderr-file)
                              (buffer-string))))
                (princ (format "Exit code: %d\n" exit-code))
                (princ (format "Stdout length: %d bytes\n" (length stdout)))
                (princ (format "Stderr length: %d bytes\n\n" (length stderr)))
                (when (> (length stderr) 0)
                  (princ "=== STDERR ===\n")
                  (princ (substring stderr 0 (min 500 (length stderr))))
                  (princ "\n\n"))
                (princ "=== STDOUT ===\n")
                (princ (substring stdout 0 (min 2000 (length stdout))))
                (princ "\n\n")
                (princ "=== PARSED RESULTS ===\n")
                (goto-char (point-min))
                (let ((n 0))
                  (while (not (eobp))
                    (let ((line (buffer-substring-no-properties
                                 (line-beginning-position) (line-end-position))))
                      (unless (string-empty-p (string-trim line))
                        (condition-case err
                            (let ((parsed (json-parse-string line :object-type 'alist)))
                              (cl-incf n)
                              (princ (format "  [%d] id=%s file=%s offset=%s dist=%s\n"
                                             n
                                             (alist-get 'id parsed)
                                             (alist-get 'file parsed)
                                             (alist-get 'byte_offset parsed)
                                             (alist-get 'distance parsed))))
                          (json-parse-error
                           (princ (format "  PARSE ERROR: %s\n    line: %s\n"
                                          (error-message-string err)
                                          (substring line 0 (min 200 (length line)))))))))
                    (forward-line 1))
                  (princ (format "\nTotal parsed: %d\n" n))))))
        (delete-file stderr-file)))))

(provide 'org-ql-semantic)
;;; org-ql-semantic.el ends here
