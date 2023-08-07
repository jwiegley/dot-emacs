;;; gnus-harvest --- Harvest e-mail address from read/written articles

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 15 Aug 2011
;; Version: 1.0
;; Keywords: gnus email
;; X-URL: https://github.com/jwiegley/gnus-harvest

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This code requires that SQLite3 be installed.  Check to see if the command
;; "sqlite3" is already available on your system.
;;
;; Once you have that, add this to your .emacs:
;;
;;   (eval-after-load "gnus"
;;     '(progn (require 'gnus-harvest)
;;             (gnus-harvest-install)))
;;
;; If you use message-x, you can get TAB completion of harvested address in
;; your To:, Cc: and From: fields by using this instead of the above:
;;
;;   (eval-after-load "gnus"
;;     '(progn (require 'gnus-harvest)
;;             (gnus-harvest-install 'message-x)))
;;

(require 'gnus)
(require 'mailalias)
(require 'sendmail)
(require 'message)
(require 'bbdb nil t)
(require 'bbdb-com nil t)

(eval-when-compile
  (require 'cl))

(defgroup gnus-harvest nil
  "Harvest addresses from Gnus articles and messages"
  :group 'gnus)

(defcustom gnus-harvest-sqlite-program (executable-find "sqlite3")
  "Full path to the sqlite3 program."
  :type 'file
  :group 'gnus-harvest)

(defcustom gnus-harvest-db-path (expand-file-name ".addrs" gnus-home-directory)
  "Path to the addresses database used by Gnus harvest."
  :type 'file
  :group 'gnus-harvest)

(defcustom gnus-harvest-query-limit 50
  "The maximum number of addresses gnus-harvest will query for."
  :type 'integer
  :group 'gnus-harvest)

(defcustom gnus-harvest-move-to-subject-after-match t
  "After completing a single address, move to the subject field if empty."
  :type 'boolean
  :group 'gnus-harvest)

(defcustom gnus-harvest-match-by-prefix nil
  "If non-nil, only match from the database by prefix."
  :type 'boolean
  :group 'gnus-harvest)

(defcustom gnus-harvest-search-in-bbdb (featurep 'bbdb)
  "If non-nil, look for net addresses in the user's BBDB records.
If you want to complete based on the `mail-alias' field, see the
function `bbdb-mail-aliases'."
  :type 'boolean
  :group 'gnus-harvest)

(defcustom gnus-harvest-ignore-email-regexp
  "\\([+\"]\\|no-reply\\|@public.gmane.org\\|localhost\\)"
  "A regexps which, if an email matches, that email is ignored."
  :type 'regexp
  :group 'gnus-harvest)

(defcustom gnus-harvest-sender-alist nil
  "An alist of To addresses -> From (if not already set).
    For example, if you associate johnw@foo.bar with the From
address doug@foo.bar, then anytime you write a letter to
doug@foo.bar, or you reply to a message from him, your From
header will get set to johnw@foo.bar -- if it is not already set
to something else.
    If no entry matches, `user-mail-address' is used.
    If this variable is not, this feature is not used."
  :type '(alist :key-type regexp :value_type string)
  :group 'gnus-harvest)

(defcustom gnus-harvest-address-function nil
  "A function applied to the address string just before insertion.

For example, if you only want to insert the email address of
contacts set this variable to mail-strip-quoted-names.")

(defun gnus-harvest-set-from (&optional address)
  (unless (message-field-value "from")
    (let ((to (message-field-value "to")))
      (when to
        (setq to (cadr (mail-extract-address-components to)))
        (let* ((addrs (gnus-harvest-complete-stub to t))
               (addr (or address
                         (and addrs (cdar addrs))
                         (assoc-default to gnus-harvest-sender-alist
                                        'string-match
                                        user-mail-address))))
          (if addr
              (message-add-header
               (format "From: %s <%s>" user-full-name addr))))))))

(defun gnus-harvest-sqlite-invoke (sql &optional ignore-output-p)
  (let ((tmp-buf (and (not ignore-output-p)
                      (generate-new-buffer "*sqlite*"))))
    (if sql
        (call-process gnus-harvest-sqlite-program
                      nil tmp-buf nil "-noheader" "-list"
                      gnus-harvest-db-path sql)
      (call-process-region (point-min) (point-max)
                           gnus-harvest-sqlite-program
                           nil tmp-buf nil "-noheader" "-list"
                           gnus-harvest-db-path))
    (unless ignore-output-p
      (with-current-buffer tmp-buf
        (prog1
            (buffer-string)
          (kill-buffer (current-buffer)))))))

(defun gnus-harvest-create-db ()
  (gnus-harvest-sqlite-invoke "
CREATE TABLE
    addrs
    (
        email         TEXT(255)  NOT NULL,
        respond_email TEXT(255),
        fullname      TEXT(255),
        last_seen     INTEGER    NOT NULL,
        weight        INTEGER    NOT NULL,

        PRIMARY KEY (email), UNIQUE (email)
    )
" t)
  (gnus-harvest-sqlite-invoke "
CREATE UNIQUE INDEX IF NOT EXISTS email_idx on addrs (email)" t)
  (gnus-harvest-sqlite-invoke "
CREATE INDEX IF NOT EXISTS fullname_idx on addrs (fullname)" t)
  (gnus-harvest-sqlite-invoke "
CREATE INDEX IF NOT EXISTS last_seen_idx on addrs (last_seen)" t))

(defun gnus-harvest-complete-stub (stub &optional prefix-only-p)
  (let ((addrs
         (read (concat "("
                       (gnus-harvest-sqlite-invoke
                        (format "
SELECT
    '(\"' ||
    CASE
        WHEN fullname IS NOT NULL
        THEN fullname || ' <' || email || '>'
        ELSE email
    END
    || '\" . ' ||
    CASE
        WHEN respond_email IS NOT NULL
        THEN '\"' || respond_email || '\"'
        ELSE 'nil'
    END
    || ')'
FROM
    (
        SELECT
            email, respond_email, fullname, last_seen, weight
        FROM
            addrs
        WHERE
            (email LIKE '%s%s%%' OR fullname LIKE '%s%s%%')
        ORDER BY
            weight DESC,
            last_seen DESC
        LIMIT
            %d
    )"
                                (if prefix-only-p "" "%") stub
                                (if prefix-only-p "" "%") stub
                                gnus-harvest-query-limit))
                       ")"))))
    addrs))

(defun gnus-harvest-mailalias-complete-stub (stub)
  (sendmail-sync-aliases)
  (if (eq mail-aliases t)
      (progn
        (setq mail-aliases nil)
        (if (file-exists-p mail-personal-alias-file)
            (build-mail-aliases))))
  (let ((entry (assoc stub mail-aliases)))
    (if entry
        (let ((result (split-string (cdr entry) ", ")))
          (if (= (length result) 1)
              (car result)
            (mapconcat #'identity
                       (mapcar #'(lambda (entry)
                                   (or (cdr (assoc entry mail-aliases))
                                       entry))
                               result)
                       ",\n    ")))
      (delete nil
              (mapcar #'(lambda (entry)
                          (if (string-prefix-p stub (car entry))
                              (cdr entry)))
                      mail-aliases)))))

(defun gnus-harvest-bbdb-complete-stub (stub)
  (loop for record in (bbdb-search (bbdb-records) stub nil stub)
        for nets = (bbdb-record-mail record)
        when nets
        collect (format "%s <%s>" (bbdb-record-name record) (car nets))))

(defun gnus-harvest-insert-address (email respond-email fullname moment weight)
  (insert
   (format
    "
INSERT OR REPLACE INTO
    addrs (email, respond_email, fullname, last_seen, weight)
VALUES
    (lower('%s'), %s, %s, '%s', '%s');
"
    email
    (if respond-email
        (format "'%s'" respond-email)
      (format "(SELECT respond_email FROM addrs WHERE email='%s')" email))
    (if fullname
        (format "'%s'" fullname)
      (format "(SELECT fullname FROM addrs WHERE email='%s')" email))
    moment
    (number-to-string weight))))

;;;###autoload
(defun gnus-harvest-addresses ()
  "Harvest and remember the addresses in the current article buffer."

  ;; Ensure that we are looking at the article rather than summary
  ;; buffer.
  (when (derived-mode-p 'gnus-summary-mode)
    (set-buffer gnus-article-buffer))
  
  (let ((tmp-buf (generate-new-buffer "*gnus harvest*"))
        (moment (number-to-string (floor (float-time))))
        (email-list
         (mapcar #'(lambda (field)
                     (let ((value (message-field-value field)))
                       (and value
                            (cons field
                                  (mail-extract-address-components value t)))))
                 '("to" "reply-to" "from" "resent-from" "cc" "bcc")))
        respond-email)
    (catch 'found
      (mapc
       #'(lambda (info)
           (when info
             (mapc
              #'(lambda (addr)
                  (dolist (sender-match gnus-harvest-sender-alist)
                    (when (string= (cadr addr) (cdr sender-match))
                      (setq respond-email (cadr addr))
                      (throw 'found t))))
              (cdr info))))
       email-list))
    (with-current-buffer tmp-buf
      (insert "BEGIN;"))
    (mapc
     #'(lambda (info)
         (when info
           (let ((field (car info)))
             (mapc
              #'(lambda (addr)
                  (if (and (cadr addr)
                           (not (string-match gnus-harvest-ignore-email-regexp
                                              (cadr addr)))
                           (string-match "@" (cadr addr)))
                      (with-current-buffer tmp-buf
                        (unless (string= (cadr addr) respond-email)
                          (gnus-harvest-insert-address
                           (cadr addr) respond-email (car addr) moment
                           (if (string= "to" field)
                               10
                             1))))))
              (cdr info)))))
     email-list)
    (with-current-buffer tmp-buf
      (insert "COMMIT;")
      (gnus-harvest-sqlite-invoke nil t)
      (kill-buffer (current-buffer)))))

;;;###autoload
(defun gnus-harvest-find-address ()
  (interactive)
  (let* ((text-follows (not (looking-at "\\s-*$")))
         (stub
          (let ((here (point)))
            (re-search-backward "[:,]\\s-+")
            (goto-char (match-end 0))
            (prog1
                (buffer-substring-no-properties (point) here)
              (delete-region (point) here))))
         (aliases (let ((bbdb (and gnus-harvest-search-in-bbdb
                                   (gnus-harvest-bbdb-complete-stub stub)))
                        (mailrc (gnus-harvest-mailalias-complete-stub stub)))
                    (cond
                     ((stringp bbdb) bbdb)
                     ((stringp mailrc) mailrc)
                     (t
                      (nconc bbdb mailrc)))))
         addrs
         (addr
          (if (stringp aliases)
              aliases
            (setq addrs (gnus-harvest-complete-stub
                         stub gnus-harvest-match-by-prefix)
                  aliases
                  (delete-dups
                   (append aliases
                           (delete stub (mapcar #'car addrs)))))
            (cond
             ((> (length aliases) 1)
              (completing-read "Use address: " aliases nil t stub))
             ((= (length aliases) 1)
              (car aliases))
             (t
              (insert stub)
              (error "Could not find any matches for '%s'" stub))))))
    (insert (if gnus-harvest-address-function
                (funcall gnus-harvest-address-function addr) addr))
    (if text-follows
        (insert ", "))
    (gnus-harvest-set-from (and addrs (cdr (assoc addr addrs))))
    (if (and gnus-harvest-move-to-subject-after-match
             (null (message-field-value "subject")))
        (message-goto-subject))))

(defun gnus-harvest-capf ()
  (pcase-let ((`(,beg . ,end)
               (or (bounds-of-thing-at-point 'email)
                   (bounds-of-thing-at-point 'word))))
    (let* ((stub (buffer-substring-no-properties beg end))
           (aliases
            (let ((bbdb (and gnus-harvest-search-in-bbdb
                             (gnus-harvest-bbdb-complete-stub stub)))
                  (mailrc (gnus-harvest-mailalias-complete-stub stub)))
              (cond
               ((stringp bbdb) bbdb)
               ((stringp mailrc) mailrc)
               (t
                (nconc bbdb mailrc))))))
      (setq aliases
            (delete-dups
             (append aliases
                     (delete stub (mapcar #'car (gnus-harvest-complete-stub
                                                 stub gnus-harvest-match-by-prefix))))))
      `(,beg ,end ,aliases))))

;;;###autoload
(defun gnus-harvest-install (&rest features)
  (unless (file-readable-p gnus-harvest-db-path)
    (gnus-harvest-create-db))

  (add-hook 'gnus-article-prepare-hook 'gnus-harvest-addresses)
  (add-hook 'message-setup-hook 'gnus-harvest-set-from)
  (add-hook 'message-send-hook 'gnus-harvest-addresses)

  (dolist (feature features)
    (cond ((eq 'message-x feature)
           (load "message-x")
           (add-to-list 'message-x-completion-alist
                        '("\\([rR]esent-\\|[rR]eply-\\)?[tT]o:\\|[bB]?[cC][cC]:" .
                          gnus-harvest-find-address))))))

(provide 'gnus-harvest)

;;; gnus-harvest.el ends here
