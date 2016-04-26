;;; nnreddit.el --- Reddit backend for Gnus

;; Copyright (C) 2016  Paul Issartel

;; Author: Paul Issartel <paul.issartel@u-psud.fr>
;; Keywords: news

;; This file is not is part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; Code:

(eval-when-compile (require 'cl))

(require 'nnheader)
(require 'nnoo)
(require 'gnus-group)
(require 'gnus-sum)
(require 'gnus-art)
(require 'gnus-util)
(require 'json)
(require 'mm-url)

(nnoo-declare nnreddit)

(nnoo-define-basics nnreddit)

(defcustom nnreddit-subjects-from-body t
  "Construct the subject line of comment articles from the
comment's body."
  :group 'nnreddit)

(defcustom nnreddit-insert-title-in-body t
  "For 'link' articles, insert the full (unelided) title at the
beginning of the article's body."
  :group 'nnreddit)

(defcustom nnreddit-elide-link-subjects 120
  "If set to a number, cut long subject lines of 'link' posts
to the given width."
  :group 'nnreddit)

(defcustom nnreddit-elide-comment-subjects 70
  "If set to a number, cut long subject lines of 'comment' posts
to the given width."
  :group 'nnreddit)

(defcustom nnreddit-always-show-subject t
  "If t, always show the Subject header, even when
`nnreddit-subjects-from-body' is set to t."
  :group 'nnreddit)

(defcustom nnreddit-link-count 50
  "How many links to initially retrieve from a subreddit."
  :group 'nnreddit)

(defcustom nnreddit-insert-score-header nil
  "Whether to insert the Score: header in articles."
  :group 'nnreddit)

(defcustom nnreddit-auto-open-threads t
  "If t, automatically insert comments when a 'link' article is selected.
If nil, only insert comments when the keybinding for
`gnus-summary-show-thread' is pressed."
  :group 'nnreddit)

(defcustom nnreddit-show-images t
  "Whether to display images in the body of 'link' articles."
  :group 'nnreddit)

(defcustom nnreddit-preview-width 320
  "Width of the preview images in 'link' articles."
  :group 'nnreddit)

(defcustom nnreddit-num-comments-in-subject "(%d) "
  "If non-nil, prepend the number of comments to subject lines
according to the given format string."
  :group 'nnreddit)

(defconst nnreddit-subreddits-url
  "https://www.reddit.com/subreddits.json?limit=100")

(defconst nnreddit-subreddit-listing-url
  "https://www.reddit.com/r/%s/.json?limit=%d")

(defconst nnreddit-comments-url
  "https://www.reddit.com/r/%s/comments/%s/.json")

(defconst nnreddit-comment-kind "t1")
(defconst nnreddit-link-kind "t3")
(defconst nnreddit-subreddit-kind "t5")

(defvar nnreddit-subreddit nil)
(defvar nnreddit-subreddits-hashtb nil)
(defvar nnreddit-data-by-id-by-subreddit nil)
(defvar nnreddit-fetched-comment-pages nil)
(defvar nnreddit-links-by-reddit-ids nil)
(defvar nnreddit-comments-by-reddit-ids-by-subreddit nil)

;; From: https://github.com/death/reddit-mode/blob/master/reddit.el
(defmacro nnreddit-alet (vars alist &rest forms)
  (let ((alist-var (make-symbol "alist")))
    `(let* ((,alist-var ,alist)
            ,@(loop for var in vars
                    collecting `(,var (assoc-default ',var ,alist-var))))
       ,@forms)))

(defun nnreddit-sanitize-string (str)
  (gnus-replace-in-string
   (gnus-replace-in-string
    str
    " *\r?\n *" " ")
   "[\000-\037\177]+\\|^ +\\| +$" ""))

(defun nnreddit-decode-entities-string (string)
  (with-temp-buffer
    (insert string)
    (mm-url-decode-entities-nbsp)
    (buffer-string)))

(defun nnreddit-retrieve-subreddit-list-json ()
  ;; (message "fetching subreddit list")
  (with-temp-buffer
    (mm-url-insert nnreddit-subreddits-url)
    (goto-char (point-min))
    (json-read)))

(defun nnreddit-retrieve-subreddit-json (subreddit)
  ;; (message "fetching listing")
  (with-temp-buffer
    (mm-url-insert (format nnreddit-subreddit-listing-url
                           subreddit nnreddit-link-count))
    (goto-char (point-min))
    (json-read)))

(defun nnreddit-retrieve-comments-json (subreddit reddit-id)
  ;; (message "fetching comments")
  (with-temp-buffer
    (mm-url-insert (format nnreddit-comments-url subreddit reddit-id))
    (goto-char (point-min))
    (json-read)))

(defun nnreddit-parse-subreddit-description (data)
  (let ((kind (assoc-default 'kind data)))
    (assert (equal nnreddit-subreddit-kind kind))
    (nnreddit-alet (id display_name url public_description)
                   (assoc-default 'data data)
                   (list :id id
                         :name display_name
                         :url url
                         :description public_description))))

(defun nnreddit-find-preview-image-url (preview preferred-width)
  (condition-case nil
      (let* ((resolutions
              (assoc-default 'resolutions
                             (aref (assoc-default 'images preview) 0)))
             (best (car
                    (sort
                     (append resolutions nil)
                     (lambda (p1 p2)
                       (let ((w1 (assoc-default 'width p1))
                             (w2 (assoc-default 'width p2)))
                         (< (abs (- w1 preferred-width))
                            (abs (- w2 preferred-width)))))))))
        (assoc-default 'url best))
    (error nil)))

(defun nnreddit-field-exists (field)
  (and (stringp field) (not (equal field ""))))

(defun nnreddit-make-link-body ()
  ;; Here, "title", "selftext_html", "url", "is_self", "preview" and
  ;; "thumbnail" are bound from `nnreddit-parse-link'
  (let ((notself (not (eq is_self t)))) ; NOTE: "is_self" may be non-nil but
                                        ; still false, e.g. ":json-false"
    (concat
     ;; Prepend the full title if `nnreddit-insert-title-in-body' is set
     (and title
          nnreddit-insert-title-in-body
          ;; (format "<h1>%s</h1>\n" title))
          (format "<p>%s</p>\n" title))
     (cond
      ;; If the post contains a selftext, use that
      (selftext_html)
      ;; Otherwise try to use the preview image if available
      ((and nnreddit-show-images
            preview
            (let ((image-url (nnreddit-find-preview-image-url
                              preview
                              nnreddit-preview-width)))
              (if (nnreddit-field-exists image-url)
                  (nnreddit-decode-entities-string
                   (concat (format "<img width=\"%d\" src=\"%s\"/>"
                                   nnreddit-preview-width
                                   image-url)
                           ;; Append the link if provided
                           (and (nnreddit-field-exists url)
                                (format "<br/><br/><a href=\"%s\">%s</a>"
                                        url url))))))))
      ;; Or use the thumbnail if provided
      ((and nnreddit-show-images
            (nnreddit-field-exists thumbnail) notself)
       (nnreddit-decode-entities-string
        (if (nnreddit-field-exists url)
            (format "<a href=\"%s\"><img width=\"%d\" src=\"%s\"></a><br/><a href=\"%s\">%s</a>"
                    url nnreddit-preview-width thumbnail url url)
          (format "<img src=\"%s\">" thumbnail))))
      ;; Or just insert the link if this is not a "self" post
      ((and (nnreddit-field-exists url) notself)
       (nnreddit-decode-entities-string
        (format "<a href=\"%s\">%s</a>" url url)))))))

  (defun nnreddit-parse-link (data)
  (let ((kind (assoc-default 'kind data)))
    (assert (equal nnreddit-link-kind kind))
    (nnreddit-alet
     (id title author created_utc score thumbnail preview url is_self
         selftext_html num_comments)
     (assoc-default 'data data)
     (list :id id
           :title title
           :author author
           :date (seconds-to-time created_utc)
           :text (nnreddit-make-link-body)
           :score score
           :num_comments num_comments))))

(defun nnreddit-sort-by-score (c1 c2)
  "Sort two comments by highest score."
  (>= (plist-get c1 :score) (plist-get c2 :score)))

(defun nnreddit-parse-comment (data &optional parent-id sort-children)
  (let ((kind (assoc-default 'kind data)))
    ;; (assert (equal nnreddit-comment-kind kind))
    (when (equal nnreddit-comment-kind kind) ; FIXME: handle other types?
      (nnreddit-alet
       (id body body_html author created_utc score replies)
       (assoc-default 'data data)
       (let* ((replies-data
               (and (listp replies)
                    (assoc-default 'data replies)))
              (children
               (and (listp replies-data)
                    (assoc-default 'children replies-data)))
              (children-comments
               (remove nil
                       (mapcar
                        (lambda (data)
                          (nnreddit-parse-comment data id sort-children))
                        children))))
         (if sort-children
             (setq children-comments
                   (sort children-comments 'nnreddit-sort-by-score)))
         (list :id id
               :title nil
               :author author
               :date (seconds-to-time created_utc)
               :text body_html
               :raw_text body
               :score (or score 1)
               :parent_id parent-id
               :children children-comments))))))

;; Parse a list of subreddits converted from json format (with `json-read')
(defun nnreddit-parse-subreddit-list (data)
  (let ((kind (assoc-default 'kind data)))
    (assert (equal "Listing" kind))
    (let ((children (assoc-default 'children (assoc-default 'data data))))
      (mapcar #'nnreddit-parse-subreddit-description children))))

;; Parse a subreddit listing converted from json format (with `json-read')
(defun nnreddit-parse-subreddit (data)
  (let ((kind (assoc-default 'kind data)))
    (assert (equal "Listing" kind))
    (let ((children (assoc-default 'children (assoc-default 'data data))))
      (mapcar #'nnreddit-parse-link children))))

;; Parse a link+comments page converted from json format (with `json-read')
(defun nnreddit-parse-comments (data &optional parent-id sort-children)
  (assert (and (arrayp data))
          (>= (length data) 2))
  (let* ((link     (assoc-default 'data (aref data 0)))
         (comments (assoc-default 'data (aref data 1)))
         (children (assoc-default 'children comments))
         (comments
          (remove nil
                  (mapcar
                   (lambda (data)
                     (nnreddit-parse-comment data parent-id sort-children))
                   children))))
    (if sort-children
        (sort comments 'nnreddit-sort-by-score)
      comments)))

(defun nnreddit-make-date-header (date)
  (let ((system-time-locale "C"))
    (format-time-string "%a, %d %h %Y %T %z (%Z)" date)))

(defun nnreddit-make-message-id (reddit-id)
  (format "<%s@reddit.com>" reddit-id))

;; (defun nnreddit-id-to-number (reddit-id)
;;   "Convert a Reddit ID (6 alphanumeric characters) to an integer."
;;   (car (read-from-string (concat "#36r" reddit-id))))

;; ;; FIXME: does not give useful results on HTML content
;; (defun nnreddit-count-lines (str)
;;   (let ((start 0) (n 0))
;;     (while (string-match "\n" str start)
;;       (incf n)
;;       (setq start (match-end 0)))
;;     n))

(defun nnreddit-make-header (elt id)
  (let* ((reddit-id (plist-get elt :id))
         (title (plist-get elt :title))
         (clean-title (and title (nnreddit-sanitize-string title)))
         (clean-author (nnreddit-sanitize-string (plist-get elt :author)))
         (date-str (nnreddit-make-date-header (plist-get elt :date)))
         (message-id (nnreddit-make-message-id reddit-id))
         (text (plist-get elt :text))
         (score (plist-get elt :score))
         (num_comments (plist-get elt :num_comments)))
    (make-full-mail-header
     id
     clean-title
     clean-author
     date-str
     message-id
     nil ; no references
     (and text (string-bytes text))
     nil ;; (and text (nnreddit-count-lines text))
     nil ; no cross references
     ;; Extra headers
     (append `((X-Reddit-ID . ,reddit-id))
             (if (integerp score)
                 `((X-Reddit-Score . ,(number-to-string score))))
             (if (integerp num_comments)
                 `((X-Reddit-Comments . ,(number-to-string num_comments))))))))

(defun nnreddit-flatten-comments (comments)
  "Turn a comment tree into a comment list, with :children fields
set to nil."
  (let (result)
    (dolist (c comments)
      (let ((children (plist-get c :children)))
        (push (plist-put (copy-tree c) :children nil) result)
        (if (car children)
            (setq result
                  (append result
                          (nnreddit-flatten-comments children))))))
    (nreverse result)))

(defun nnreddit-elide-subject (subject width)
  (if (numberp width)
      (truncate-string-to-width
       subject
       width
       nil nil t)
    subject))

(defun nnreddit-alter-header (header data type)
  (let ((header (copy-tree header t)))
    (cond
     ((eq type 'link)
      (mail-header-set-subject
       header
       (concat
        (if (stringp nnreddit-num-comments-in-subject)
            (format nnreddit-num-comments-in-subject
                    (plist-get data :num_comments)))
        (nnreddit-elide-subject
         (mail-header-subject header)
         nnreddit-elide-link-subjects))))
     ((eq type 'comment)
      (if nnreddit-subjects-from-body
          (mail-header-set-subject
           header
           (let* ((raw-text (plist-get data :raw_text))
                  (decoded (and raw-text
                                (nnreddit-decode-entities-string
                                 (nnreddit-sanitize-string
                                  raw-text)))))
             (nnreddit-elide-subject decoded nnreddit-elide-comment-subjects))))))
    header))

(defun nnreddit-get-subreddit-articles ()
  (gethash nnreddit-subreddit nnreddit-data-by-id-by-subreddit))

(defun nnreddit-get-subreddit-comments ()
  (gethash nnreddit-subreddit nnreddit-comments-by-reddit-ids-by-subreddit))

(defun nnreddit-get-subreddit-article-ids (&optional not-root)
  (let (ids)
    (maphash (lambda (id value)
              (if (and (eq (caddr value) 'link)
                       ;; Exclude root articles when requested (root
                       ;; articles are single 'link' articles that
                       ;; serve as root of the group when the group is
                       ;; actually a single thread)
                       (or (not not-root) (not (cadddr value))))
                  (push id ids)))
            (nnreddit-get-subreddit-articles))
    (nreverse ids)))

(defun nnreddit-retrieve-headers (articles &optional group server fetch-old)
  (nnreddit-possibly-change-group group)
  (with-current-buffer nntp-server-buffer
    (erase-buffer)
    (dolist (id articles)
      (let ((value (gethash id (nnreddit-get-subreddit-articles))))
        (when value
          (let ((header (car value))
                (data (cadr value))
                (type (caddr value)))
            (nnheader-insert-nov
             (nnreddit-alter-header header data type)))))))
  'nov)

(defun nnreddit-treat-quotes ()
  "Convert the leading spaces from <blockquote> HTML tags to
proper citation marks."
  (gnus-with-article-buffer
    (article-goto-body)
    ;; ;; Unsplit URLs
    ;; (save-excursion
    ;;   (while (re-search-forward
    ;;           "\\(\\(https?\\|ftp\\)://\\S-+\\) *\n *\\(\\S-+\\)" nil t)
    ;;   (replace-match "\\1\\3" t)))
    ;;
    ;; Iterate over all lines that look like <blockquotes>
    ;; FIXME: seems to match <li> too...
    (while (re-search-forward "^ +" nil t)
      (beginning-of-line)
      ;; Don't add citation marks to the attribution line
      (when (re-search-forward "^\\( +\\).*wrote:$" nil t)
        (delete-region (match-beginning 1) (match-end 1))
        (forward-line)
        ;; Delete any blank line immediately following the
        ;; attribution line
        (if (looking-at "^ *$")
            (delete-region (point) (1+ (line-end-position)))))
      ;; Replace leading spaces with citation marks
      (while (re-search-forward "^ +" (line-end-position) t)
        (replace-match "> " t)
        (forward-line))
      ;; Delete any trailing blank line after the citation block
      (backward-char)
      (if (looking-back "> ")
          (delete-region (line-beginning-position) (point))))))

(defun nnreddit-request-article (id &optional group server buffer)
  (nnreddit-possibly-change-group group)
  (with-current-buffer (or buffer nntp-server-buffer)
    (erase-buffer)
    (let ((value (gethash id (nnreddit-get-subreddit-articles))))
      (when value
        (let ((header (car value))
              (data (cadr value))
              (type (caddr value)))

          (let ((nnreddit-num-comments-in-subject nil))
            (setq header (nnreddit-alter-header header data type)))

          ;; (nnheader-insert-header header)
          (insert
           "From: " (or (mail-header-from header) "(nobody)") "\n"
           (if (or nnreddit-always-show-subject
                   (not nnreddit-subjects-from-body))
               (concat "Subject: " (or (mail-header-subject header) "(none)") "\n")
             "")
           "Date: " (or (mail-header-date header) "") "\n"
           "Message-ID: " (or (mail-header-id header) (nnmail-message-id)) "\n"
           "References: " (or (mail-header-references header) "") "\n"
           "Content-Type: text/html; charset=utf-8" "\n"
           (let ((score (plist-get data :score)))
             (if (and nnreddit-insert-score-header
                      (numberp score)
                      (not (eq score 1)) ; default value for unscored posts
                      )
               (format "Score: %d\n" score)
               ""))
           "\n")

          (let ((text (plist-get data :text)))
            (when text
              (unless (string-match-p "&lt;blockquote&gt;" text)
                ;; If there is not already a citation block in the text,
                ;; quote the entire parent comment.
                ;; Can be paired with `nnreddit-treat-quotes' for
                ;; a better rendering of citations.
                (let* ((parent-id (plist-get data :parent_id))
                       (parent (and parent-id
                                    (or (gethash parent-id nnreddit-links-by-reddit-ids)
                                        (gethash parent-id (nnreddit-get-subreddit-comments)))))
                       (parent (and parent (cadr parent)))
                       (parent-text (and parent (plist-get parent :text))))
                  (when (and parent parent-text)
                    (insert "<blockquote>"
                            (nnreddit-sanitize-string
                             (plist-get parent :author)) " wrote:<br/>"
                             ;; Insert the parent comment, removing the image
                             ;; preview if needed
                             (replace-regexp-in-string
                              "<img[^>]*>\\(?:<br/>\\)*" ""
                              parent-text)
                             "</blockquote>\n\n"))))
              (goto-char (point-max))

              (insert text)
              (mm-url-decode-entities-nbsp)))

          ;; Return value, as per Gnus documentation
          (cons nnreddit-subreddit id))))))

(defmacro nnreddit-generate-comments (comments parent-link n)
  `(let (comment-ids)
     (dolist (c ,comments)
       ;; Only create a new article for this comment if one does
       ;; not already exist in the cache
       (let* ((comment-reddit-id (plist-get c :id))
              (value (gethash comment-reddit-id
                              (nnreddit-get-subreddit-comments))))
         (if value
             (push (car value) comment-ids)
           (let ((header (nnreddit-make-header c (incf ,n)))
                 (parent-id (or (plist-get c :parent_id)
                                (plist-get ,parent-link :id))))
             ;; FIXME: do this directly in `nnreddit-make-header'??
             (mail-header-set-references
              header
              (nnreddit-make-message-id parent-id))
             ;; FIXME: do this directly in `nnreddit-make-header'??
             (mail-header-set-subject
              header
              (plist-get ,parent-link :title))
             (push ,n comment-ids)
             (puthash ,n (list header c 'comment) (nnreddit-get-subreddit-articles))
             (puthash comment-reddit-id (list ,n c) (nnreddit-get-subreddit-comments))))))
     comment-ids))

(defun nnreddit-insert-comments (id)
  (let ((value (gethash id (nnreddit-get-subreddit-articles))))
    (when value
      (let* ((link (cadr value))
             (link-reddit-id (plist-get link :id))
             (comments
              (or
               ;; Don't fetch comments again if they are cached
               ;; TODO: add some way to force re-fetching comments
               (gethash link-reddit-id nnreddit-fetched-comment-pages)
               ;; Or fetch the comment page if we have to
               (let* ((json-data
                       (nnreddit-retrieve-comments-json
                        nnreddit-subreddit
                        link-reddit-id))
                      (comments
                       (nnreddit-flatten-comments
                         (nnreddit-parse-comments json-data link-reddit-id t))))
                 (puthash link-reddit-id comments nnreddit-fetched-comment-pages))))
             ;; Make sure to always create new article IDs
             (n (hash-table-count (nnreddit-get-subreddit-articles)))
             ;; Generate comments, fill in hash tables, and return
             ;; article IDs of the generated comments
             (comment-ids
              (nnreddit-generate-comments comments link n)))
        (let ((new-limit (number-sequence 1 n)))
          (gnus-summary-insert-articles comment-ids)
          (gnus-summary-limit new-limit)
          ;; `gnus-summary-limit' seems to auto-expand all other threads,
          ;; so we close them and re-expand the current thread
          (save-excursion
            (gnus-summary-hide-all-threads)
            (gnus-summary-goto-subject id)
            (gnus-summary-show-thread)))))))

(defun nnreddit-should-fetch-thread (article)
  "Check if the current article is a 'link' article, and is not
the \"root article\" of the group."
  (member article (nnreddit-get-subreddit-article-ids t)))

(defun nnreddit-expand-thread (&optional article)
  (let ((article (or article (gnus-summary-article-number))))
    (when (and (nnreddit-is-nnreddit)
               (nnreddit-should-fetch-thread article))
      (nnreddit-insert-comments article))))

(defun nnreddit-request-group (group &optional server dont-check info)
  (nnreddit-possibly-change-group group)
  (unless dont-check
    (cond
     ((not nnreddit-subreddit)
      (nnheader-report 'nnreddit "No subreddit selected"))
     (t
      (let ((json-data
             (nnreddit-retrieve-subreddit-json nnreddit-subreddit))
            (n 0))
        (cond
         ((arrayp json-data)
          ;; The requested group is actually a Reddit thread
          (let* ((link (nnreddit-parse-link
                        (aref
                         (assoc-default 'children
                                        (assoc-default 'data (aref json-data 0))) 0)))
                 (id (plist-get link :id))
                 (comments (nnreddit-flatten-comments
                            (nnreddit-parse-comments json-data id t)))
                 (header (nnreddit-make-header link (incf n))))
            ;; Create one "link" article, marked as a special "root article"
            ;; (4th parameter in the hash table)
            (puthash n (list header link 'link t) (nnreddit-get-subreddit-articles))
            (puthash id (list n link) nnreddit-links-by-reddit-ids)
            ;; Then generate comments and fill in hash tables
            (nnreddit-generate-comments comments link n)))
         (t
          ;; The requested group is a subreddit
          (let ((links (nnreddit-parse-subreddit json-data)))
            (dolist (l links)
              (let ((id (plist-get l :id))
                    (header (nnreddit-make-header l (incf n))))
                (puthash n (list header l 'link) (nnreddit-get-subreddit-articles))
                (puthash id (list n l) nnreddit-links-by-reddit-ids))))))
        (nnheader-insert "211 %d %d %d %s\n" n 1 n group)))))
  t)

(defun nnreddit-build-subreddit-list ()
  (unless nnreddit-subreddits-hashtb  ; only fetch the subreddit list once
    (setq nnreddit-subreddits-hashtb (make-hash-table :size 128))
    (let* ((json-data (nnreddit-retrieve-subreddit-list-json))
           (subreddits (nnreddit-parse-subreddit-list json-data)))
      (dolist (s subreddits)
        (let* ((name (plist-get s :name))
               (clean-name (downcase (nnreddit-sanitize-string name))))
          (puthash clean-name s nnreddit-subreddits-hashtb))))))

(defun nnreddit-request-list (&optional server)
  (nnreddit-possibly-change-group group)
  (with-current-buffer nntp-server-buffer
    (erase-buffer)
    (nnreddit-build-subreddit-list)
    (maphash (lambda (name s)
               ;; TODO: correct message count?
               (insert (format "%s %d 1 n\n" name nnreddit-link-count)))
             nnreddit-subreddits-hashtb))
  t)

(defun nnreddit-request-list-newsgroups (&optional server)
  (nnreddit-possibly-change-group group)
  (with-current-buffer nntp-server-buffer
    (erase-buffer)
    (nnreddit-build-subreddit-list)
    (maphash (lambda (name s)
               (insert (format "%s %s\n"
                               name
                               (nnreddit-decode-entities-string
                                (nnreddit-sanitize-string
                                 (plist-get s :description))))))
             nnreddit-subreddits-hashtb))
  t)

(defun nnreddit-request-newgroups (date &optional server)
  (nnheader-report 'nnreddit "NEWSGROUPS is not implemented."))

(defun nnreddit-request-type (group &optional article)
  'unknown)

(defun nnreddit-close-group (group &optional server)
  (nnreddit-possibly-change-group group)
  t)

(defun nnreddit-open-server (server &optional defs)
  t)

(defun nnreddit-possibly-change-group (&optional group)
  (unless nnreddit-data-by-id-by-subreddit
    (setq nnreddit-data-by-id-by-subreddit (make-hash-table :size 128 :test 'equal)))
  (unless nnreddit-fetched-comment-pages
    (setq nnreddit-fetched-comment-pages (make-hash-table :size 1024 :test 'equal)))
  (unless nnreddit-links-by-reddit-ids
    (setq nnreddit-links-by-reddit-ids (make-hash-table :size 1024 :test 'equal)))
  (unless nnreddit-comments-by-reddit-ids-by-subreddit
    (setq nnreddit-comments-by-reddit-ids-by-subreddit (make-hash-table :size 128 :test 'equal)))
  (when group
    (setq nnreddit-subreddit
          ;; Remove trailing slashes
          (replace-regexp-in-string "/$" "" group))
    (unless (gethash nnreddit-subreddit
                     nnreddit-data-by-id-by-subreddit)
      (puthash nnreddit-subreddit
               (make-hash-table :size 1024)
               nnreddit-data-by-id-by-subreddit))
    (unless (gethash nnreddit-subreddit
                     nnreddit-comments-by-reddit-ids-by-subreddit)
      (puthash nnreddit-subreddit
               (make-hash-table :size 1024)
               nnreddit-comments-by-reddit-ids-by-subreddit))))

(gnus-declare-backend "nnreddit" 'none)

(defun nnreddit-subscribe-to-thread (group)
  "Subscribe to the thread or sub-thread at point."
  (interactive
   (list
    (let* ((article (gnus-summary-article-number))
           (value (gethash article
                           (nnreddit-get-subreddit-articles)))
           (data (cadr value))
           (type (caddr value))
           (reddit-id (plist-get data :id))
           (subreddit
            (replace-regexp-in-string "/.*$" "" nnreddit-subreddit))
           (url (concat
                 (symbol-name
                  (car (gnus-find-method-for-group gnus-newsgroup-name)))
                 ":"
                 ;; FIXME: create new constants for these format strings
                 (cond
                  ((eq type 'link)
                   (format "%s/comments/%s" subreddit reddit-id))
                  ((eq type 'comment)
                   (let* ((root-article
                           (let ((parent article) a)
                             (while parent
                               (setq a parent)
                               (setq parent (gnus-summary-article-parent parent)))
                             a))
                          (root-reddit-id
                           (plist-get
                            (cadr
                             (gethash root-article
                                      (nnreddit-get-subreddit-articles))) :id)))
                     (format "%s/comments/%s/comments/%s"
                             subreddit
                             root-reddit-id
                             reddit-id)))))))
      (gnus-group-completing-read nil nil nil url))))
  (gnus-group-unsubscribe-group group))

;; ======================================================
;; Add a few hooks to automatically expand comments, etc.

(defun nnreddit-is-nnreddit ()
  (eq 'nnreddit (car (gnus-find-method-for-group gnus-newsgroup-name))))

;; If `nnreddit-auto-open-threads' is t, automatically insert comments
;; when a 'post' article is selected
(add-hook 'gnus-select-article-hook
          '(lambda ()
             (when (and (nnreddit-is-nnreddit)
                        nnreddit-auto-open-threads
                        (nnreddit-should-fetch-thread article))
               (nnreddit-expand-thread article))))

;; This function replaces the keybinding for `gnus-summary-show-thread'.
;; If `nnreddit-auto-open-threads' is nil, only insert comments when
;; this keybinding is pressed.
(defun nnreddit-show-thread ()
  (interactive)
  (unless nnreddit-auto-open-threads
    (nnreddit-expand-thread))
  (call-interactively 'gnus-summary-show-thread))

(add-hook 'gnus-summary-mode-hook
          (lambda ()
            (when (nnreddit-is-nnreddit)
              ;; We know that references are correct
              (set (make-local-variable 'gnus-summary-thread-gathering-function)
                   'gnus-gather-threads-by-references)
              ;; Prevent threads from jumping around when comments with
              ;; possibly more recent dates are dynamically inserted in
              ;; the summary buffer
              (set (make-local-variable 'gnus-thread-sort-functions)
                   'gnus-thread-sort-by-number)
              ;; Intercept the keybinding for `gnus-summary-show-thread'
              ;; to insert comments if `nnreddit-auto-open-threads'
              ;; is nil
              (substitute-key-definition 'gnus-summary-show-thread
                                         'nnreddit-show-thread
                                         (current-local-map)))))
(add-hook 'gnus-part-display-hook
          (lambda ()
            (when (nnreddit-is-nnreddit)
              ;; Treat citations
              (nnreddit-treat-quotes)
              ;; Also treat weird characters
              (article-translate-strings '((25 "'") (20 "—"))))))

(add-hook 'gnus-article-prepare-hook
          (lambda ()
            (when (nnreddit-is-nnreddit)
              ;; Display image previews on "link" articles
              (when nnreddit-show-images
                (gnus-article-show-images))
              ;; Show the Score: header
              (when nnreddit-insert-score-header
                (if (not (string-match-p "\\\\|^Score:" gnus-visible-headers))
                    (set (make-local-variable 'gnus-visible-headers)
                         (concat gnus-visible-headers "\\|^Score:")))))))

(provide 'nnreddit)

;;; nnreddit.el ends here
