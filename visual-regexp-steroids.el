;;; visual-regexp-steroids.el --- Extends visual-regexp to support other regexp engines

;; Copyright (C) 2013-2017 Marko Bencun

;; Author: Marko Bencun <mbencun@gmail.com>
;; URL: https://github.com/benma/visual-regexp-steroids.el/
;; Version: 1.1
;; Package-Requires: ((visual-regexp "1.1"))
;; Keywords: external, foreign, regexp, replace, python, visual, feedback

;; This file is part of visual-regexp-steroids

;; visual-regexp-steroids is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; visual-regexp-steroids is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with visual-regexp-steroids.  If not, see <http://www.gnu.org/licenses/>.

;;; WHAT'S NEW
;; 1.1: Add new engine: emacs-plain.
;; 1.0: Make compatible with visual-regexp 1.0.
;; 0.9: Fix warnings regarding free variables.
;; 0.8: Added support for pcre2el as a new engine.
;; 0.7: distinguish prompts in vr/replace, vr/query-replace, vr/mc-mark.
;; 0.6: new functions vr/select-replace, vr/select-query-replace, vr/select-mc-mark
;; 0.5: perform no case-conversion for non-emacs regexp engines.
;; 0.4: keep in sync with visual-regexp
;; 0.2: compatibility with visual-regexp 0.2
;; 0.1: initial release

;;; Tip Jar
;; If you found this useful, please consider donating.
;; BTC: 1KtDEa5saBdJ2AFcFq93QZ3jz3sYpq2z2

;;; Code:

(require 'visual-regexp)

;;; variables

(defvar vr--command-python-default
  (format "python %s" (expand-file-name "regexp.py" (file-name-directory load-file-name))))

(defcustom vr/command-python vr--command-python-default
  "External command used for the Python engine."
  :type 'string
  :group 'visual-regexp)

(defcustom vr/command-custom ""
  "Custom external command used when the engine is set to custom."
  :type 'string
  :group 'visual-regexp)

(defcustom vr/engine 'python
  "Which engine to use for searching/replacing.
Use Emacs to use Emacs-style regular expressions.
Use Python to use Python's regular expressions (see vr/command-python).
Use pcre2el (https://github.com/joddie/pcre2el) to use PCRE regular expressions.
Use Custom to use a custom external command (see vr/command-custom)."
  :type '(choice
          (const :tag "Emacs" emacs)
          (const :tag "pcre2el" pcre2el)
          (const :tag "Python" python)
          (const :tag "Custom" custom))
  :group 'visual-regexp)

(defcustom vr/default-regexp-modifiers '(:I nil :M t :S nil :U nil)
  "Modifiers that are applied by default. All modifiers are: '(I M S U).
See also: http://docs.python.org/library/re.html#re.I"
  ;;:type '(choice (const 10) (const 5))

  :type '(plist :key-type (choice
                           (const :tag "Enable the IGNORECASE modifier by default" :I)
                           (const :tag "Enable the MULTILINE modifier by default (^ and $ match on every line)" :M)
                           (const :tag "Enable the DOTALL modifier by default (dot matches newline)" :S)
                           (const :tag "Enable the UNICODE modifier by default" :U))
                :value-type boolean)
  :group 'visual-regexp)

;;; private variables

(defconst vr--engines '(emacs emacs-plain pcre2el python))

(defvar vr--use-expression nil
  "Use expression instead of string in replacement.")

;; modifiers IMSU (see http://docs.python.org/library/re.html#re.I)
(defvar vr--regexp-modifiers '()
  "Modifiers in use.")

(define-key vr/minibuffer-keymap (kbd "C-c i") (lambda () (interactive) (vr--toggle-regexp-modifier :I)))
(define-key vr/minibuffer-keymap (kbd "C-c m") (lambda () (interactive) (vr--toggle-regexp-modifier :M)))
(define-key vr/minibuffer-keymap (kbd "C-c s") (lambda () (interactive) (vr--toggle-regexp-modifier :S)))
(define-key vr/minibuffer-keymap (kbd "C-c u") (lambda () (interactive) (vr--toggle-regexp-modifier :U)))

(define-key vr/minibuffer-keymap (kbd "C-c C-c") (lambda () (interactive)
                                                   (when (vr--in-replace)
                                                     (setq vr--use-expression (not vr--use-expression))
                                                     (vr--update-minibuffer-prompt)
                                                     (vr--do-replace-feedback))))


;;; regexp modifiers

(add-hook 'vr/initialize-hook (lambda ()
                                (setq vr--use-expression nil)
                                (setq vr--regexp-modifiers (copy-sequence vr/default-regexp-modifiers))))

(defun vr--regexp-modifiers-enabled ()
  (eq vr/engine 'python))

(defun vr--toggle-regexp-modifier (modifier)
  "modifier should be one of :I, :M, :S, :U."
  (when (and (vr--in-from) (vr--regexp-modifiers-enabled))
    (plist-put vr--regexp-modifiers modifier
               (not (plist-get vr--regexp-modifiers modifier)))
    (vr--update-minibuffer-prompt)
    (vr--show-feedback)))

(defun vr--get-regexp-modifiers-prefix ()
  "Construct (?imsu) prefix based on selected modifiers."
  (if (vr--regexp-modifiers-enabled)
      (let ((s (mapconcat 'identity
                          (delq nil (mapcar (lambda (m)
                                              (when (plist-get vr--regexp-modifiers m)
                                                (cond ((equal m :I) "i")
                                                      ((equal m :M) "m")
                                                      ((equal m :S) "s")
                                                      ((equal m :U) "u")
                                                      (t nil))))
                                            (list :I :M :S :U)))
                          "")))
        (if (string= "" s) "" (format "(?%s)" s)))
    ""))

(defadvice vr--get-replacement (around get-unmodified-replacement (replacement match-data i) activate)
  (cond ((member vr/engine '(emacs pcre2el))
         ad-do-it)
        ((eq vr/engine 'emacs-plain)
         (let ((vr/plain t)) ad-do-it))
        (t
         (setq ad-return-value replacement))))

(defadvice vr--get-regexp-string (around get-regexp-string (&optional for-display) activate)
  ad-do-it
  (let ((regexp ad-return-value))
    (when (and (not for-display) (eq vr/engine 'pcre2el))
      (condition-case err
          (setq regexp (pcre-to-elisp regexp))
        (invalid-regexp (signal (car err) (cdr err))) ;; rethrow
        (error (signal (car err) (list "pcre2el error")))))

    (setq ad-return-value
          (concat (vr--get-regexp-modifiers-prefix)
                  regexp))))

;;; shell command / parsing functions

(defun vr--get-command ()
  (cond
   ((eq vr/engine 'python) vr/command-python)
   ((eq vr/engine 'custom) vr/command-custom)))

(defun vr--command (command)
  (let ((stdout-buffer (generate-new-buffer (generate-new-buffer-name " *pyregex stdout*")))
        output
        exit-code)
    (with-current-buffer vr--target-buffer
      (setq exit-code (call-process-region
                       vr--target-buffer-start
                       vr--target-buffer-end
                       shell-file-name
                       nil ;; don't delete region
                       stdout-buffer
                       nil ;; don't redisplay buffer
                       shell-command-switch
                       command)))
    (with-current-buffer stdout-buffer
      (setq output (buffer-string))
      (kill-buffer))
    (list output exit-code)))

(defun vr--run-command (args success)
  (cl-multiple-value-bind (output exit-code) (vr--command args)
    (cond ((equal exit-code 0)
           (funcall success output))
          ((equal exit-code 1)
           (message "script failed:%s\n" output))
          (t (error (format "External command failed with exit code %s" exit-code))))))

(defun vr--unescape (s)
  "Replacement/message strings returned by external script are base64 encoded."
  (decode-coding-string (base64-decode-string s) 'utf-8 t))

(defun vr--not-last-line ()
  "Output of external script ends in one line of message and one empty line.
Return t if current line is not the line with the message."
  (save-excursion (= 0 (forward-line 2))))

(defun vr--current-line ()
  (buffer-substring-no-properties (line-beginning-position) (line-end-position)))

(defun vr--parse-matches (s callback)
  "Parse string s with positions of matches and groups as returned by external script. For each position, callback is called with arguments (i j begin end),
i being the match and j the group index and begin/end being the span of the match.
The message line is returned.
"
  (let (message-line) ;; store message line (last non-empty line of output)
    (with-temp-buffer
      (insert s)
      (goto-char (point-min))
      (let ((offset vr--target-buffer-start))
        (cl-loop while (and (vr--not-last-line) (/= (line-beginning-position) (line-end-position))) ;; loop until empty line is reached
                 for i from 0 do
                 (cl-loop while (re-search-forward "\\([0-9]+\\) \\([0-9]+\\)" (line-end-position) t) ;; loop integer pairs in line
                          for j from 0 do
                          (let ((begin (+ offset (string-to-number (match-string 1))))
                                (end (+ offset (string-to-number (match-string 2)))))
                            (funcall callback i j begin end)))
                 (forward-line 1)))
      (setq message-line (vr--unescape (vr--current-line))))
    message-line))

(defun vr--parse-replace (s)
  "Parse string s with positions of matches and replacements as returned by external script.
Returns a list, in reverse order, of (replacement (list begin end) i) (i = index of match = index of corresponding overlay)
and the message line."
  (let ((replacements (list)) ;; store replacements (lines of output) in list
        message-line) ;; store message line (last non-empty line of output)
    (with-temp-buffer
      (insert s)
      (goto-char (point-min))
      (cl-loop while (and (vr--not-last-line) (/= (line-beginning-position) (line-end-position))) ;; loop until empty line is reached
               for i from 0 do
               (re-search-forward "\\([0-9]+\\) \\([0-9]+\\) " (line-end-position) t)
               (let ((replacement (buffer-substring-no-properties (point) (line-end-position)))
                     (begin (+ vr--target-buffer-start (string-to-number (match-string 1))))
                     (end (+ vr--target-buffer-start (string-to-number (match-string 2)))))
                 (setq replacements (cons (list (vr--unescape replacement) (list begin end) i) replacements)))
               (forward-line 1))
      (setq message-line (vr--unescape (vr--current-line))))
    (list replacements message-line)))

:;; prompt

(defadvice vr--set-minibuffer-prompt (around prompt activate)
  (let ((prompt (cond ((equal vr--calling-func 'vr--calling-func-query-replace)
                       "Query replace")
                      ((equal vr--calling-func 'vr--calling-func-mc-mark)
                       "Mark")
                      (t
                       "Replace"))))
    (when (vr--in-replace)
      (setq prompt (concat prompt
                           (let ((flag-infos (mapconcat 'identity
                                                        (delq nil (list (when vr--use-expression "using expression")
                                                                        (when vr--replace-preview "preview")))
                                                        ", ")))
                             (when (not (string= "" flag-infos ))
                               (format " (%s)" flag-infos))))))
    (when (not (vr--in-from))
      (setq prompt (concat prompt " " (vr--get-regexp-string t))))
    (setq prompt (concat prompt (if (vr--in-from) ": " " with: ")))
    (when (and (vr--in-from) (vr--regexp-modifiers-enabled))
      (setq prompt (concat prompt (vr--get-regexp-modifiers-prefix))))
    (setq ad-return-value prompt)))

(defadvice vr--minibuffer-help-text (around help activate)
  ad-do-it
  (let ((help ad-return-value))
    (when (and (vr--in-from) (vr--regexp-modifiers-enabled))
      (setq help (concat help ", C-c i: toggle case, C-c m: toggle multiline match of ^ and $, C-c s: toggle dot matches newline")))
    (when (vr--in-replace)
      (setq help (concat help ", C-c C-c: toggle expression")))
    (setq ad-return-value help)))

;; feedback / replace functions

(defadvice vr--feedback-function (around feedback-around (regexp-string forward feedback-limit callback) activate)
  "Feedback function for search using an external command."
  (cond ((member vr/engine '(emacs pcre2el))
         ad-do-it)
        ((eq vr/engine 'emacs-plain)
         (let ((vr/plain t)) ad-do-it))
        (t
         (setq ad-return-value
               (vr--run-command
                (format "%s matches --regexp %s %s %s"
                        (vr--get-command)
                        (shell-quote-argument regexp-string)
                        (when feedback-limit (format "--feedback-limit %s" feedback-limit))
                        (if forward "" "--backwards"))
                (lambda (output)
                  (vr--parse-matches
                   output
                   callback)))))))

(defadvice vr--get-replacements (around get-replacements-around (feedback feedback-limit) activate)
  "Get replacements using an external command."
  (cond ((member vr/engine '(emacs pcre2el))
         ad-do-it)
        ((eq vr/engine 'emacs-plain)
         (let ((vr/plain t)) ad-do-it))
        (t
         (setq ad-return-value
               (vr--run-command
                (format "%s replace %s %s %s --regexp %s --replace %s"
                        (vr--get-command)
                        (if feedback "--feedback" "")
                        (if feedback-limit
                            (format "--feedback-limit %s" feedback-limit)
                          "")
                        (if vr--use-expression "--eval" "")
                        (shell-quote-argument (vr--get-regexp-string))
                        (shell-quote-argument (vr--get-replace-string)))
                'vr--parse-replace)))))

(defun vr--select-engine ()
  (let ((default (symbol-name vr/engine))
        (choices vr--engines))
    ;; add custom engine if a custom command has been defined
    (unless (string= "" vr/command-custom)
      (setq choices (cons 'custom choices)))
    (intern (completing-read (format "Select engine (default: %s): " (symbol-name vr/engine)) (mapcar 'symbol-name choices) nil t nil nil default))))

;;;###autoload
(defun vr/select-replace ()
  (interactive)
  (let ((vr/engine (vr--select-engine)))
    (call-interactively 'vr/replace)))

;;;###autoload
(defun vr/select-query-replace ()
  (interactive)
  (let ((vr/engine (vr--select-engine)))
    (call-interactively 'vr/query-replace)))

;;;###autoload
(defun vr/select-mc-mark ()
  (interactive)
  (let ((vr/engine (vr--select-engine)))
    (call-interactively 'vr/mc-mark)))

;; isearch starts here

;;;###autoload
(defun vr/isearch-forward ()
  "Like isearch-forward, but using Python (or custom) regular expressions."
  (interactive)
  (if (eq vr/engine 'emacs)
      (isearch-forward-regexp)
    (let ((isearch-search-fun-function 'vr--isearch-search-fun-function))
      (isearch-forward-regexp))))

;;;###autoload
(defun vr/isearch-backward ()
  "Like isearch-backward, but using Python (or custom) regular expressions."
  (interactive)
  (if (eq vr/engine 'emacs)
      (isearch-backward-regexp)
    (let ((isearch-search-fun-function 'vr--isearch-search-fun-function))
      (isearch-backward-regexp))))

(defvar vr--isearch-cache-key nil)
(defvar vr--isearch-cache-val nil)

(defun vr--isearch-forward (string &optional bound noerror count)
  (vr--isearch t string bound noerror count))

(defun vr--isearch-backward (string &optional bound noerror count)
  (vr--isearch nil string bound noerror count))

(defun vr--isearch-find-match (forward matches start)
  (let ((i (vr--isearch-find-match-bsearch forward matches start 0 (- (length matches) 1))))
    (unless (eq i -1)
      (aref matches i))))

(defun vr--isearch-find-match-bsearch (forward matches start left right)
  (if (= 0 (length matches))
      -1
    (let ((mid (/ (+ left right) 2))
          (el (if forward 0 1)) ;; 0 => beginning of match; 1 => end of match
          (cmp (if forward '<= '>=)))
      (cond ((eq left right)
             (if (funcall cmp start (nth el (aref matches mid)))
                 left
               -1)
             )
            ((funcall cmp start (nth el (aref matches mid)))
             (vr--isearch-find-match-bsearch forward matches start left mid))
            (t
             (vr--isearch-find-match-bsearch forward matches start (1+ mid) right))))))

(defun vr--isearch (forward string &optional bound noerror count)
  ;; This is be called from isearch. In the first call, bound will be nil to find the next match.
  ;; Afterwards, lazy highlighting kicks in, which calls this function many times, for different values of (point), always with the same bound (window-end (selected-window)).
  ;; Calling a process repeatedly is noticeably  slow. To speed the lazy highlighting up, we fetch all matches in the visible window at once and cache them for subsequent calls.
  (let* ((is-called-from-lazy-highlighting bound) ;; we assume only lazy highlighting sets a bound. isearch does not, and neither does our own vr/query-replace.
         matches-vec ;; stores matches from regexp.py
         message-line ;; message from regexp.py
         (regexp (if (eq vr/engine 'pcre2el) (pcre-to-elisp string) string))
         (start
          (if forward
              (if is-called-from-lazy-highlighting (window-start (selected-window)) (point))
            (if is-called-from-lazy-highlighting bound (point-min))))
         (end
          (if forward
              (if is-called-from-lazy-highlighting bound (point-max))
            (if is-called-from-lazy-highlighting (window-end (selected-window)) (point))))
         (cache-key (list regexp start end)))
    (if (and is-called-from-lazy-highlighting (equal vr--isearch-cache-key cache-key))
        (setq matches-vec vr--isearch-cache-val) ;; cache hit
      (progn ;; no cache hit, populate matches-vec
        (setq vr--target-buffer-start start
              vr--target-buffer-end end
              vr--target-buffer (current-buffer))

        (let ((matches-list (list))
              (number-of-matches 0))
          (setq message-line
                (vr--feedback-function
                 regexp
                 forward
                 (if count
                     count
                   ;; if no bound, the rest of the buffer is searched for the first match -> need only one match
                   (if bound nil 1))
                 (lambda (i j begin end)
                   (when (= j 0) (setq number-of-matches (1+ number-of-matches)))
                   (setq matches-list (cons (list i j begin end) matches-list)))))

          ;; convert list to vector
          (setq matches-vec (make-vector number-of-matches nil))
          (let ((cur-match (list)))
            (mapc (lambda (el)
                    (cl-multiple-value-bind (i j begin end) el
                      (when (and (= j 0) (> i 0))
                        (aset matches-vec (- i 1) (nreverse cur-match))
                        (setq cur-match (list)))
                      (setq cur-match (cons end (cons begin cur-match)))))
                  (nreverse matches-list))
            (when cur-match
              (aset matches-vec (- (length matches-vec) 1) (nreverse cur-match)))))
        (when is-called-from-lazy-highlighting ;; store in cache
          (setq vr--isearch-cache-key cache-key
                vr--isearch-cache-val matches-vec))))

    (let ((match (vr--isearch-find-match forward matches-vec (point))))
      (if match
          (progn
            (set-match-data (mapcar 'copy-marker match)) ;; needed for isearch
            (if forward
                (goto-char (nth 1 match)) ;; move to end of match
              (goto-char (nth 0 match)) ;; move to beginning of match
              ))
        (progn
          (set-match-data (list 0 0))
          (when (string= "Invalid:" (substring message-line 0 8))
            (signal 'invalid-regexp (list message-line))))))))

(defun vr--isearch-search-fun-function ()
  "To enable vr/isearch, set isearch-search-fun-function to vr--isearch-search-fun-function, i.e. `(setq isearch-search-fun-function 'vr--isearch-search-fun-function)`."
  ;; isearch-search-fun is a function that returns the function that does the search. It calls isearch-search-fun-function (if it exists) to do its job.
  (if isearch-regexp ;; let us handle regexp search
      (if isearch-forward 'vr--isearch-forward 'vr--isearch-backward)
    (let ((isearch-search-fun-function nil)) ;; fall back to the default implementation of isearch, which will handle regular search and word search.
      (isearch-search-fun))))

(add-hook 'isearch-mode-end-hook (lambda ()
                                   (setq vr--isearch-cache-key nil
                                         vr--isearch-cache-val nil)))

(provide 'visual-regexp-steroids)

;;; visual-regexp-steroids.el ends here
