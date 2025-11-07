;;; my-gnus-spam-catchup.el --- Spam processing on catchup -*- lexical-binding: t; -*-

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Version: 1.0.0
;; Package-Requires: ((emacs "27.1") (gnus "5.13"))
;; Keywords: mail, gnus, spam
;; URL: https://github.com/jwiegley/dot-emacs

;;; Commentary:

;; This package provides automatic spam/ham processing when using catchup
;; in Gnus.  The workflow is:
;;
;; 1. Ticked articles (!) → move to ham-process-destination (TrainGood)
;; 2. All other articles → move to spam-process-destination (TrainSpam)
;; 3. Group is caught up (all articles marked as read)
;;
;; This is useful for processing INBOX where most messages are spam, but
;; you want to save legitimate messages by ticking them first.
;;
;; Usage:
;;
;;   (require 'my-gnus-spam-catchup)
;;   (setq my-gnus-spam-catchup-groups-regex "\\`\\(INBOX\\|mail/\\)")
;;   (define-key gnus-summary-mode-map (kbd "C-c y")
;;     'my-gnus-catchup-with-spam-processing)
;;
;; Or with use-package:
;;
;;   (use-package my-gnus-spam-catchup
;;     :after gnus
;;     :bind (:map gnus-summary-mode-map
;;                 ("C-c y" . my-gnus-catchup-with-spam-processing))
;;     :custom
;;     (my-gnus-spam-catchup-groups-regex "\\`\\(INBOX\\|mail/\\)"))
;;
;; To override the default catchup keybinding (c y):
;;
;;   (with-eval-after-load 'gnus-sum
;;     (define-key gnus-summary-mode-map "cy"
;;       'my-gnus-catchup-with-spam-processing))

;;; Code:

(require 'gnus)
(require 'gnus-sum)

(defgroup my-gnus-spam-catchup nil
  "Spam processing on catchup for Gnus."
  :group 'gnus
  :prefix "my-gnus-spam-catchup-")

(defcustom my-gnus-spam-catchup-groups-regex "\\`INBOX\\'"
  "Regex matching groups where catchup should process spam/ham.
Only groups matching this regex will have automatic spam/ham
processing when using `my-gnus-catchup-with-spam-processing'."
  :type 'regexp
  :group 'my-gnus-spam-catchup)

(defcustom my-gnus-spam-catchup-ham-marks
  (list gnus-ticked-mark gnus-dormant-mark gnus-saved-mark)
  "List of marks to treat as ham (non-spam).
Articles with these marks will be moved to ham-process-destination
when catching up.  By default: ticked (!), dormant (?), and saved (S)."
  :type '(repeat integer)
  :group 'my-gnus-spam-catchup)

(defcustom my-gnus-spam-catchup-ask-before-processing t
  "If non-nil, ask before processing spam/ham on catchup.
When nil, always process automatically without asking."
  :type 'boolean
  :group 'my-gnus-spam-catchup)

(defun my-gnus-spam-catchup-group-p ()
  "Return non-nil if current group should process spam on catchup.
Checks if the current group matches `my-gnus-spam-catchup-groups-regex'
and has a spam-process-destination parameter set."
  (and gnus-newsgroup-name
       (string-match my-gnus-spam-catchup-groups-regex
                     gnus-newsgroup-name)
       (gnus-group-get-parameter gnus-newsgroup-name
                                 'spam-process-destination)))

(defun my-gnus-process-ham-articles ()
  "Move ham-marked articles to ham-process-destination.
Ham articles are those with marks in `my-gnus-spam-catchup-ham-marks'.
Returns the number of articles moved."
  (let ((ham-dest (gnus-group-get-parameter gnus-newsgroup-name
                                             'ham-process-destination))
        (ham-articles '()))
    (if (not ham-dest)
        (progn
          (message "No ham-process-destination set for %s" gnus-newsgroup-name)
          0)
      (gnus-summary-iterate nil
        (when (memq (gnus-summary-article-mark) my-gnus-spam-catchup-ham-marks)
          (push (gnus-summary-article-number) ham-articles)))
      (if ham-articles
          (progn
            (gnus-summary-move-article (nreverse ham-articles) ham-dest)
            (message "Moved %d ham article(s) to %s"
                     (length ham-articles) ham-dest)
            (length ham-articles))
        (message "No ham articles to process")
        0))))

(defun my-gnus-process-spam-articles ()
  "Move non-ham articles to spam-process-destination.
All articles NOT marked with `my-gnus-spam-catchup-ham-marks' are
considered spam.  Returns the number of articles moved."
  (let ((spam-dest (gnus-group-get-parameter gnus-newsgroup-name
                                              'spam-process-destination))
        (spam-articles '()))
    (if (not spam-dest)
        (progn
          (message "No spam-process-destination set for %s" gnus-newsgroup-name)
          0)
      (gnus-summary-iterate nil
        (let ((mark (gnus-summary-article-mark)))
          ;; Move anything that's not a ham mark
          (when (not (memq mark my-gnus-spam-catchup-ham-marks))
            (push (gnus-summary-article-number) spam-articles))))
      (if spam-articles
          (progn
            (gnus-summary-move-article (nreverse spam-articles) spam-dest)
            (message "Moved %d spam article(s) to %s"
                     (length spam-articles) spam-dest)
            (length spam-articles))
        (message "No spam articles to process")
        0))))

;;;###autoload
(defun my-gnus-catchup-with-spam-processing (&optional all)
  "Catchup with automatic spam/ham processing.

Articles with ham marks (see `my-gnus-spam-catchup-ham-marks')
are moved to ham-process-destination (typically TrainGood).

All other articles are moved to spam-process-destination
(typically TrainSpam).

After processing, the group is caught up (all articles marked as read)
and you exit the group.

With prefix argument ALL, catchup all articles unconditionally,
including ticked and dormant articles.

Only processes groups matching `my-gnus-spam-catchup-groups-regex'
that have spam-process-destination configured."
  (interactive "P")
  (if (not (my-gnus-spam-catchup-group-p))
      ;; Not a spam-processing group, just do normal catchup
      (progn
        (message "Group %s does not use spam processing, doing normal catchup"
                 gnus-newsgroup-name)
        (gnus-summary-catchup-and-exit))
    ;; Process spam/ham
    (when (or (not my-gnus-spam-catchup-ask-before-processing)
              (y-or-n-p "Process spam/ham before catchup? "))
      (let ((ham-count (my-gnus-process-ham-articles))
            (spam-count (my-gnus-process-spam-articles)))
        (message "Processed %d ham, %d spam articles" ham-count spam-count)))
    ;; Now do normal catchup
    (gnus-summary-catchup-and-exit all)))

;;;###autoload
(defun my-gnus-process-spam-ham-only ()
  "Process spam/ham in current group without catching up.
This moves articles to their destinations but doesn't mark them
as read or exit the group."
  (interactive)
  (if (not (my-gnus-spam-catchup-group-p))
      (message "Group %s does not use spam processing" gnus-newsgroup-name)
    (let ((ham-count (my-gnus-process-ham-articles))
          (spam-count (my-gnus-process-spam-articles)))
      (message "Processed %d ham, %d spam articles" ham-count spam-count)
      (gnus-summary-position-point))))

(provide 'my-gnus-spam-catchup)
;;; my-gnus-spam-catchup.el ends here
