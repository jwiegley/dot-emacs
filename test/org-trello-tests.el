;;; org-trello-tests.el --- org-trello tests utils
;;; Commentary:
;;; Code:

;; hackish way to set a timezone different from my own machine
;; and ensure the date are correclty dealt with through tests
(let ((tz-file (if (file-exists-p "/etc/NIXOS")
                   "/etc" ;; nixos-based os
                 "/usr/share"))) ;; debian-based
  (setenv "TZ" (format "%s/zoneinfo/Europe/London" tz-file)))

(defsubst hash-table-keys (hash-table)
  "Return a list of keys in HASH-TABLE."
  (let ((keys '()))
    (maphash (lambda (k _v) (push k keys)) hash-table)
    keys))

(defsubst hash-table-values (hash-table)
  "Return a list of values in HASH-TABLE."
  (let ((values '()))
    (maphash (lambda (_k v) (push v values)) hash-table)
    values))

(defun orgtrello-tests-hash-equal (hash1 hash2)
  "Are the 2 hash tables HASH1 and HASH2 are equal or not.
Deal with nested hash map."
  (catch 'flag (maphash (lambda (x y)
                          (or (and (hash-table-p y)
                                   (orgtrello-tests-hash-equal (gethash x hash2) y))
                              (equal (gethash x hash2) y)
                              (throw 'flag nil)))
                        hash1)
         (throw 'flag t)))

(defun org-trello-mode-test ()
  "Trigger org-trello-mode shaped for tests."
  (setq org-trello-mode-on-hook nil
        org-trello-mode-off-hook nil
        orgtrello-setup-use-position-in-checksum-computation 'please-do-use-position-in-checksum-computation
        orgtrello-log-level orgtrello-log-no-log
        org-trello--mode-activated-p t
        kill-whole-line t)
  (call-interactively 'org-trello-mode))

(defmacro orgtrello-tests-with-temp-buffer (text body-test
                                                 &optional nb-lines-forward)
  "A `org-trello' mode buffer helper test on buffer.
TEXT is the content of the buffer.
BODY-TEST is the assertion to test on the buffer.
NB-LINES-FORWARD is the number of lines to get back to."
  `(with-temp-buffer
     (org-mode)
     (insert ,text)
     (forward-line (if ,nb-lines-forward ,nb-lines-forward -1))
     (org-trello-mode-test)
     (orgtrello-controller-setup-properties)
     ,body-test))

(defmacro orgtrello-tests-with-temp-buffer-and-return-buffer-content
    (text body-test &optional nb-lines-forward)
  "A `org-trello' mode buffer helper test on buffer.
TEXT is the content of the buffer.
BODY-TEST is the assertion to test on the buffer.
NB-LINES-FORWARD is the number of lines to get back to.
This returns the buffer content after body-test has been performed."
  `(orgtrello-tests-with-temp-buffer
    ,text
    (progn
      ,body-test
      (buffer-substring-no-properties (point-min) (point-max)))
    ,nb-lines-forward))

(defmacro orgtrello-tests-with-temp-buffer-and-return-content-with-props
    (text body-test &optional nb-lines-forward)
  "A `org-trello' mode buffer helper test on buffer.
TEXT is the content of the buffer.
BODY-TEST is the assertion to test on the buffer.
NB-LINES-FORWARD is the number of lines to get back to.
This returns the buffer content after body-test has been performed."
  `(orgtrello-tests-with-temp-buffer
    ,text
    (progn
      ,body-test
      (buffer-substring (point-min) (point-max)))
    ,nb-lines-forward))

(defun orgtrello-tests-prepare-buffer ()
  "Prepare the buffer to receive org-trello data."
  (orgtrello-buffer-indent-card-descriptions)
  (orgtrello-buffer-indent-card-data))

(defmacro orgtrello-tests-with-temp-buffer-and-return-indented-content
    (text body-test &optional nb-lines-forward)
  "A `org-trello' mode buffer helper test on buffer.
TEXT is the content of the buffer.
BODY-TEST is the assertion to test on the buffer.
NB-LINES-FORWARD is the number of lines to get back to.
This returns the `org-trello' buffer after body-test has been executed."
  `(orgtrello-tests-with-temp-buffer
    ,text
    (progn
      ,body-test
      (orgtrello-tests-prepare-buffer) ;; force indentation without hook
      (buffer-substring-no-properties (point-min) (point-max)))
    ,nb-lines-forward))

(defmacro orgtrello-tests-with-org-buffer (text body-test)
  "A simple `org-mode' buffer.
TEXT is the content of the buffer.
BODY-TEST is the assertion to test on the buffer."
  `(with-temp-buffer
     (insert ,text)
     (org-mode)
     ,body-test))

(provide 'org-trello-tests)
;;; org-trello-tests.el ends here
