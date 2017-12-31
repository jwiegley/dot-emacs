;;; company-restclient.el --- company-mode completion back-end for restclient-mode

;; Public domain.

;; Author:    Iku Iwasa <iku.iwasa@gmail.com>
;; URL:       https://github.com/iquiw/company-restclient
;; Version:   0.2.0
;; Package-Requires: ((cl-lib "0.5") (company "0.8.0") (emacs "24") (know-your-http-well "0.2.0") (restclient "0.0.0"))

;;; Commentary:

;; `company-mode' back-end for `restclient-mode'.
;;
;; It provides auto-completion for HTTP methods and headers in `restclient-mode'.
;; Completion source is given by `know-your-http-well'.

;;; Code:

(require 'cl-lib)
(require 'company)
(require 'know-your-http-well)
(require 'restclient)

(defcustom company-restclient-header-values
  '(("content-type" . ("application/json"
                       "application/xml"
                       "application/x-www-form-urlencoded"
                       "text/csv"
                       "text/html"
                       "text/plain")))
  "Association list of completion candidates for HTTP header values.
The key is header name and the value is list of header values.")

(defvar company-restclient--current-context nil)

(defun company-restclient--find-context ()
  "Find context (method, header, body) of the current line."
  (save-excursion
    (forward-line 0)
    (cond
     ((looking-at-p "^:") 'vardecl)
     ((looking-at-p "^#") 'comment)
     (t
      (catch 'result
        (let ((state 0))
          (while (and (>= (forward-line -1) 0)
                      (null (looking-at-p "^#")))
            (cond
             ((looking-at-p "^\\([[:space:]]*$\\|:\\)")
              (cond
               ((= state 0) (setq state 1))
               ((= state 2) (setq state 3))))
             ((= state 0) (setq state 2))
             ((or (= state 1) (= state 3))
              (throw 'result 'body))))

          (if (or (= state 0) (= state 1))
              (throw 'result 'method)
            (throw 'result 'header))))))))

(defun company-restclient-prefix ()
  "Provide completion prefix at the current point."
  (cl-case (company-restclient--find-context)
    (method (or (let ((case-fold-search nil)) (company-grab "^[[:upper:]]*"))
                (company-restclient--grab-var)))
    (header (or (company-grab "^[-[:alpha:]]*")
                (company-restclient--grab-var)
                (company-grab-symbol)))
    (vardecl nil)
    (comment nil)
    (t (company-restclient--grab-var))))

(defun company-restclient--grab-var ()
  "Grab variable for completion prefix."
  (company-grab ".\\(:[^: \n]*\\)" 1))

(defun company-restclient-candidates (prefix)
  "Provide completion candidates for the given PREFIX."
  (cond
   ((string-match-p "^:" prefix)
    (setq company-restclient--current-context 'varref)
    (all-completions
     prefix
     (sort (mapcar #'car (restclient-find-vars-before-point)) #'string<)))
   (t
    (cl-case (setq company-restclient--current-context
                   (company-restclient--find-context))
      (method
       (all-completions prefix http-methods))
      (header
       (cond
        ((looking-back "^\\([-[:alpha:]]+\\): .*")
         (setq company-restclient--current-context 'header-value)
         (all-completions prefix
                          (cdr
                           (assoc
                            (downcase (match-string-no-properties 1))
                            company-restclient-header-values))))
        (t
         (all-completions (downcase prefix) http-headers))))))))

(defun company-restclient-meta (candidate)
  "Return description of CANDIDATE to display as meta information."
  (cl-case company-restclient--current-context
    (method (cl-caadr (assoc candidate http-methods)))
    (header (cl-caadr (assoc candidate http-headers)))))

(defun company-restclient-post-completion (candidate)
  "Format CANDIDATE in the buffer according to the current context.
For HTTP method, insert space after it.
For HTTP header, capitalize if necessary and insert colon and space after it."
  (cl-case company-restclient--current-context
    (method (insert " "))
    (header (let (start (end (point)))
              (when (save-excursion
                      (backward-char (length candidate))
                      (setq start (point))
                      (let ((case-fold-search nil))
                        (looking-at-p "[[:upper:]]")))
                (delete-region start end)
                (insert
                 (mapconcat 'capitalize (split-string candidate "-") "-"))))
            (insert ": "))))

;;;###autoload
(defun company-restclient (command &optional arg &rest ignored)
  "`company-mode' completion back-end for `restclient-mode'.
Provide completion info according to COMMAND and ARG.  IGNORED, not used."
  (interactive (list 'interactive))
  (cl-case command
    (interactive (company-begin-backend 'company-restclient))
    (prefix (and (derived-mode-p 'restclient-mode) (company-restclient-prefix)))
    (candidates (company-restclient-candidates arg))
    (ignore-case 'keep-prefix)
    (meta (company-restclient-meta arg))
    (post-completion (company-restclient-post-completion arg))))

(provide 'company-restclient)
;;; company-restclient.el ends here
