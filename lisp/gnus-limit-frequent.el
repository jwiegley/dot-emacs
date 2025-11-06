;;; gnus-limit-frequent.el --- Limit to frequent authors/subjects -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Version: 0.1.0
;; Package-Requires: ((emacs "27.1") (gnus "5.13"))
;; Keywords: mail, news, gnus
;; URL: https://github.com/jwiegley/dot-emacs

;;; Commentary:

;; This package provides an interactive command to limit Gnus summary buffers
;; to articles where either the author or subject appears frequently (more than
;; a specified threshold).
;;
;; Usage:
;;   M-x gnus-summary-limit-to-frequent
;;
;; The command prompts for a threshold N and then shows only articles where:
;; - The author has sent more than N messages in the group, OR
;; - The subject appears in more than N messages in the group
;;
;; Subjects are normalized using `gnus-simplify-subject-re' to handle
;; Re:, Fwd:, etc. prefixes correctly.

;;; Code:

(require 'gnus)
(require 'gnus-sum)
(require 'cl-lib)

(defgroup gnus-limit-frequent nil
  "Limit Gnus summary to frequent authors or subjects."
  :group 'gnus-summary
  :prefix "gnus-limit-frequent-")

(defcustom gnus-limit-frequent-default-threshold 5
  "Default threshold for frequent author/subject filtering.
Articles are shown if the author or subject appears more than
this many times in the group."
  :type 'integer
  :group 'gnus-limit-frequent)

(defun gnus-limit-frequent--normalize-author (from)
  "Normalize FROM header for counting purposes.
Extracts email address or name, handling various formats."
  (when (and from (stringp from))
    (let ((cleaned (string-trim from)))
      ;; Extract email if present: "Name <email>" -> "email"
      (if (string-match "<\\([^>]+\\)>" cleaned)
          (match-string 1 cleaned)
        ;; Otherwise use the whole string, lowercased
        (downcase cleaned)))))

(defun gnus-limit-frequent--count-headers (articles)
  "Count occurrences of authors and subjects in ARTICLES.
Returns a cons cell (AUTHOR-TABLE . SUBJECT-TABLE) where each
table maps normalized headers to occurrence counts.

ARTICLES should be a list of article numbers."
  (let ((author-counts (make-hash-table :test 'equal :size 1000))
        (subject-counts (make-hash-table :test 'equal :size 1000)))

    (dolist (article articles)
      (let ((header (gnus-summary-article-header article)))
        (when header
          ;; Count authors
          (when-let ((from (mail-header-from header)))
            (when-let ((normalized-author (gnus-limit-frequent--normalize-author from)))
              (cl-incf (gethash normalized-author author-counts 0))))

          ;; Count subjects
          (when-let ((subject (mail-header-subject header)))
            (let ((normalized-subject (gnus-simplify-subject-re subject)))
              (when (and normalized-subject (> (length normalized-subject) 0))
                (cl-incf (gethash normalized-subject subject-counts 0))))))))

    (cons author-counts subject-counts)))

(defun gnus-limit-frequent--article-matches-p (article author-table subject-table threshold)
  "Check if ARTICLE matches frequency criteria.
Returns non-nil if either the author or subject of ARTICLE appears
more than THRESHOLD times in AUTHOR-TABLE or SUBJECT-TABLE."
  (let ((header (gnus-summary-article-header article)))
    (when header
      (or
       ;; Check author frequency
       (let ((from (mail-header-from header)))
         (when from
           (let ((normalized-author (gnus-limit-frequent--normalize-author from)))
             (when normalized-author
               (> (gethash normalized-author author-table 0) threshold)))))

       ;; Check subject frequency
       (let ((subject (mail-header-subject header)))
         (when subject
           (let ((normalized-subject (gnus-simplify-subject-re subject)))
             (when (and normalized-subject (> (length normalized-subject) 0))
               (> (gethash normalized-subject subject-table 0) threshold)))))))))

;;;###autoload
(defun gnus-summary-limit-to-frequent (threshold)
  "Limit summary buffer to articles with frequent authors or subjects.

Show only articles where either:
- The author has more than THRESHOLD messages in this group, OR
- The subject appears in more than THRESHOLD messages in this group

Subjects are normalized to ignore Re:, Fwd:, etc. prefixes.

When called interactively, prompts for THRESHOLD.
With a prefix argument, uses that value as THRESHOLD.

This is a limiting command; you can restore the full summary with
\\[gnus-summary-limit-to-marks] or \\[gnus-summary-pop-limit]."
  (interactive
   (list (if current-prefix-arg
             (prefix-numeric-value current-prefix-arg)
           (read-number "Show articles with > N occurrences: "
                        gnus-limit-frequent-default-threshold)))
   gnus-summary-mode)

  ;; Validate we're in a Gnus summary buffer
  (unless (derived-mode-p 'gnus-summary-mode)
    (user-error "Not in a Gnus summary buffer"))

  ;; Validate threshold
  (unless (and (integerp threshold) (>= threshold 1))
    (user-error "Threshold must be a positive integer, got: %s" threshold))

  (let* ((articles (gnus-summary-article-list))
         (article-count (length articles)))

    ;; Check for empty group
    (when (zerop article-count)
      (user-error "No articles in current group"))

    (message "Analyzing %d articles..." article-count)

    (condition-case err
        (let* ((counts (gnus-limit-frequent--count-headers articles))
               (author-table (car counts))
               (subject-table (cdr counts))
               (matching-articles nil)
               (author-matches 0)
               (subject-matches 0)
               (both-matches 0))

          ;; Find matching articles
          (dolist (article articles)
            (let* ((header (gnus-summary-article-header article))
                   (author-frequent-p
                    (and header
                         (when-let ((from (mail-header-from header)))
                           (when-let ((norm (gnus-limit-frequent--normalize-author from)))
                             (> (gethash norm author-table 0) threshold)))))
                   (subject-frequent-p
                    (and header
                         (when-let ((subject (mail-header-subject header)))
                           (let ((norm (gnus-simplify-subject-re subject)))
                             (and norm (> (length norm) 0)
                                  (> (gethash norm subject-table 0) threshold)))))))

              (when (or author-frequent-p subject-frequent-p)
                (push article matching-articles)
                (cond
                 ((and author-frequent-p subject-frequent-p)
                  (cl-incf both-matches))
                 (author-frequent-p
                  (cl-incf author-matches))
                 (subject-frequent-p
                  (cl-incf subject-matches))))))

          ;; Apply the limit
          (if matching-articles
              (progn
                (gnus-summary-limit-to-articles (nreverse matching-articles))
                (message
                 "Limited to %d/%d articles (threshold > %d): %d by author, %d by subject, %d both"
                 (length matching-articles) article-count threshold
                 author-matches subject-matches both-matches))
            (message "No articles found with author or subject appearing > %d times"
                     threshold)))

      (error
       (message "Error analyzing articles: %s" (error-message-string err))
       (signal (car err) (cdr err))))))

(provide 'gnus-limit-frequent)
;;; gnus-limit-frequent.el ends here
