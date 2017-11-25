(require 'dash)
(require 'proof-shell)
(require 'company-coq)

(defconst company-coq-ltac-tracing-shorthand-regexp "=>_\\([a-zA-Z0-9_\\-]+\\) ")
(defconst company-coq-ltac-tracing-shorthand-replacement "=> (* COMPANY_COQ_TRACE: \\1 *) ")

;; (defconst company-coq-ltac-tracing-regexp "=> (\\* COMPANY_COQ_TRACE: \\([a-zA-Z0-9_\\- ]+\\) \\*) ")
(defconst company-coq-ltac-tracing-regexp "\\(=>\\s-*\\)?(\\* COMPANY_COQ_TRACE: \\(\\(?:[a-zA-Z0-9_\\-]+\\)\\|\\(?:\"[^\"]+\"\\)\\)\\( \\(?:\n\\|[^*]\\)*?\\)? \\*)")

(defun company-coq-ensure-quoted (str)
  (replace-regexp-in-string "\\(\\`\"*\\|\"*\\'\\)" "\"" str))

(defun company-coq-normalize-trace-annotations (string)
  (when string
    (replace-regexp-in-string company-coq-ltac-tracing-shorthand-regexp company-coq-ltac-tracing-shorthand-replacement string t)))

(defcustom company-coq-ltac-tracing-tactic "idtac"
  "Tactic to use when processing tracing comments."
  :group 'company-coq)

(defcustom company-coq-ltac-tracing t
  "Enable tracing based on comments in ltac forms.
When non-nil, any expression matching the pattern
`company-coq-ltac-tracing-regexp' is converted to a call to idtac
before being set to the prover.  For easier typing, one can use
the following syntax to input a trace annotation:
  match goal with
   | [  |- True ] =>_TrueCase apply I
  end.
This will (always) be converted to
  match goal with
   | [  |- True ] => (* COMPANY_COQ_TRACE: TrueCase *) apply I
  end.
If `company-coq-ltac-tracing' is non-nil, this will then be
dynamically expanded into the following (final) snippet:
  match goal with
   | [  |- True ] => TACTIC \"TrueCase\"; apply I
  end.
where TACTIC is `company-coq-ltac-tracing-tactic'."
  :group 'company-coq)

(defun company-coq-pad-to-length (str reference)
  ;; (message "[%s] [%s] [%s] [%s]" str reference (length str) (length reference))
  ;; (company-coq-dbg "Replacement string too long: [%s] %d > %d [%s]" str (length str) (length reference) reference))
  (when (>= (length reference) (length str))
    (setq str (concat str (make-string (- (length reference) (length str)) ?\ ))))
  str)

(defun company-coq-process-trace-annotations (string)
  "Process trace annotations in STRING.
Replace instances of `company-coq-ltac-tracing-regexp' in STRING
when `company-coq-ltac-tracing' is non-nil."
  (while (and string (string-match company-coq-ltac-tracing-regexp string))
    (setq string (replace-match (company-coq-pad-to-length
                                 (format "%stry(__T;idtac\"*\" %s %s)%s"
                                         (or (match-string-no-properties 1 string) ";")
                                         (company-coq-ensure-quoted (match-string-no-properties 2 string))
                                         (or (match-string-no-properties 3 string) "")
                                         (if (match-string-no-properties 1 string) ";" ""))
                                 (match-string-no-properties 0 string))
                                t nil string)))
  string)

(defun company-coq-end-of-proof-region-around-point ()
  "Uses `proof-segment-up-to-using-cache' to locate the end of the proof form surrounding the current point."
  (save-excursion (cl-loop for (type str end) in (proof-segment-up-to-using-cache (point))
                           when (eq type 'cmd) maximize end)))

(defun company-coq-rewrite-trace-annotations-before-proof-assert-until-point (&optional displayflags)
  (-when-let* ((start (proof-queue-or-locked-end))
               (late  (> (point) (proof-queue-or-locked-end)))
               (end   (copy-marker (company-coq-end-of-proof-region-around-point))))
    (save-excursion
      (goto-char start)
      (while (re-search-forward company-coq-ltac-tracing-shorthand-regexp (marker-position end) t)
        (replace-match company-coq-ltac-tracing-shorthand-replacement t)))))

(defun company-coq-annotate-all-cases (start end)
  (interactive "r")
  (when (and start end)
    (save-excursion
      (goto-char start)
      (setq end (copy-marker end))
      (cl-loop for    match-number = 1 then (1+ match-number)
               while  (search-forward "] => " (marker-position end) t)
               unless (save-excursion (goto-char (match-beginning 0))
                                      (skip-chars-forward "] ")
                                      (looking-at company-coq-ltac-tracing-regexp))
               do     (replace-match (replace-quote (format "] => (* COMPANY_COQ_TRACE: %d *) " match-number)))))))

(advice-add #'proof-assert-until-point :before
            #'company-coq-rewrite-trace-annotations-before-proof-assert-until-point)

(defconst company-coq-ltac-tracing-setup-forms
  '("Definition ___COMPANY_COQ_TRACE_FLAG___ := True."
    "Transparent ___COMPANY_COQ_TRACE_FLAG___."
    "Ltac __T := unfold ___COMPANY_COQ_TRACE_FLAG___."))

(defun company-coq-ltac-tracing-apply-form ()
  ;; First transparent added to ensure that Proof-General doesn't miss solved goals messages.
  (format "Transparent ___COMPANY_COQ_TRACE_FLAG___. %s ___COMPANY_COQ_TRACE_FLAG___. "
          (if company-coq-ltac-tracing "Transparent" "Opaque")))

(defun company-coq-ltac-tracing-setup-forms ()
  (append company-coq-ltac-tracing-setup-forms (list (company-coq-ltac-tracing-apply-form))))

(defun company-coq-apply-ltac-tracing-setting ()
  (interactive)
  (mapc #'proof-shell-invisible-cmd-get-result (company-coq-ltac-tracing-setup-forms)))

(defun company-coq-toggle-ltac-tracing ()
  (interactive)
  (setq company-coq-ltac-tracing (not company-coq-ltac-tracing))
  (when (company-coq-apply-ltac-tracing-setting)
    (message "Tracing %s." (if company-coq-ltac-tracing "enabled" "disabled"))))

(define-key company-coq-map (kbd "<f8>") #'company-coq-toggle-ltac-tracing)

(setq-default proof-script-preprocess nil) ;; #'company-coq-proof-script-preprocess)

(defun company-coq-preprocess-command ()
  "Preprocess company-coq's syntactic sugar"
  (when (and (boundp 'action) (eq action 'proof-done-advancing)
             (boundp 'string))
    (setq string (company-coq-normalize-trace-annotations string))
    (setq string (company-coq-process-trace-annotations string))
    ;; (setq string (concat (company-coq-ltac-tracing-apply-form) string))
    ))
    ;; (cond
    ;;  ((string-match-p "\\`\\s-*Set\\s-+Tracing\\.?\\s-*\\'" string)
    ;;   (setq string (company-coq-ltac-tracing-apply-form)))
    ;;  ((string-match-p "\\`\\s-*Unset\\s-+Tracing\\.?\\s-*\\'" string)
    ;;   (setq string (company-coq-ltac-tracing-apply-form)))
    ;;  ((string-match-p "\\`\\s-*Test\\s-+Tracing\\.?\\s-*\\'" string)
    ;;   (setq string (company-coq-ltac-tracing-apply-form))))
    ;; ;; (setq string (concat (company-coq-ltac-tracing-apply-form) string))))

(add-hook 'proof-shell-insert-hook #'company-coq-preprocess-command)
