;;; git-gutter+.el --- Manage Git hunks straight from the buffer

;; Copyright (C) 2013 by Syohei YOSHIDA and contributors

;; Author: Syohei YOSHIDA <syohex@gmail.com> and contributors
;; URL: https://github.com/nonsequitur/git-gutter-plus
;; Version: 0.01

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
;; View, stage and revert Git changes straight from the buffer.

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'tramp)

(defgroup git-gutter+ nil
  "Port GitGutter"
  :prefix "git-gutter+-"
  :group 'vc)

(defcustom git-gutter+-window-width nil
  "Character width of the gutter margin. Set this variable if the automatically
calculated width looks wrong. (This can happen with some special characters.)"
  :type 'integer
  :group 'git-gutter+)

(defcustom git-gutter+-diff-options nil
  "List of strings containing extra arguments to 'git diff'"
  :type 'list
  :group 'git-gutter+)

(defcustom git-gutter+-separator-sign nil
  "Separator sign"
  :type 'string
  :group 'git-gutter+)

(defcustom git-gutter+-modified-sign "="
  "Modified sign"
  :type 'string
  :group 'git-gutter+)

(defcustom git-gutter+-added-sign "+"
  "Added sign"
  :type 'string
  :group 'git-gutter+)

(defcustom git-gutter+-deleted-sign "-"
  "Deleted sign"
  :type 'string
  :group 'git-gutter+)

(defcustom git-gutter+-unchanged-sign nil
  "Unchanged sign"
  :type 'string
  :group 'git-gutter+)

(defcustom git-gutter+-hide-gutter nil
  "Hide gutter if there are no changes"
  :type 'boolean
  :group 'git-gutter+)

(defcustom git-gutter+-lighter " GitGutter"
  "Minor mode lighter in mode-line"
  :type 'string
  :group 'git-gutter+)

(defface git-gutter+-separator
    '((t (:foreground "cyan" :weight bold)))
  "Face of the separator"
  :group 'git-gutter+)

(defface git-gutter+-modified
    '((t (:foreground "magenta" :weight bold)))
  "Face for modified lines"
  :group 'git-gutter+)

(defface git-gutter+-added
    '((t (:foreground "green" :weight bold)))
  "Face for added lines"
  :group 'git-gutter+)

(defface git-gutter+-deleted
    '((t (:foreground "red" :weight bold)))
  "Face for deleted lines"
  :group 'git-gutter+)

(defface git-gutter+-unchanged
    '((t (:background "yellow")))
  "Face for unchanged lines"
  :group 'git-gutter+)

(defcustom git-gutter+-disabled-modes nil
  "A list of modes for which `global-git-gutter+-mode' should be disabled."
  :type '(repeat symbol)
  :group 'git-gutter+)

(defvar git-gutter+-view-diff-function 'git-gutter+-view-diff-infos
  "Display diffs")

(defvar git-gutter+-clear-function 'git-gutter+-clear-diff-infos
  "Clear diff display")

(defvar git-gutter+-window-config-change-function 'git-gutter+-show-gutter
  "Function to call when the buffer's local window configuration has changed")

(defvar git-gutter+-diffinfos nil)
(defvar git-gutter+-diff-header nil)
(make-variable-buffer-local 'git-gutter+-diffinfos)
(make-variable-buffer-local 'git-gutter+-diff-header)

(defvar git-gutter+-popup-buffer "*git-gutter+-diff*")
(defvar git-gutter+-buffers-to-reenable nil)

(defconst git-gutter+-hunk-header-regex
  ;; The same as diff-hunk-header-re-unified
  "^@@ -\\([0-9]+\\)\\(?:,\\([0-9]+\\)\\)? \\+\\([0-9]+\\)\\(?:,\\([0-9]+\\)\\)? @@")

(defmacro git-gutter+-awhen (test &rest body)
  "Anaphoric when."
  (declare (indent 1))
  `(let ((it ,test))
     (when it ,@body)))

(defun git-gutter+-call-git (args file)
  (if (not (file-remote-p file))
      (apply #'call-process "git" nil t nil args)
    (apply #'process-file "git" nil t nil args)))

(defun git-gutter+-in-git-repository-p (file)
  (with-temp-buffer
    (let ((args '("rev-parse" "--is-inside-work-tree")))
      (when (zerop (git-gutter+-call-git args file))
        (goto-char (point-min))
        (string= "true" (buffer-substring-no-properties
                         (point) (line-end-position)))))))

(defun git-gutter+-root-directory (file)
  (with-temp-buffer
    (let* ((args '("rev-parse" "--show-toplevel"))
           (ret (git-gutter+-call-git args file)))
      (when (zerop ret)
        (goto-char (point-min))
        (let ((root (buffer-substring-no-properties (point) (line-end-position))))
          (unless (string= root "")
            (file-name-as-directory root)))))))

(defsubst git-gutter+-diff-args (file)
  (delq nil (list "--no-pager" "diff" "--no-color" "--no-ext-diff" "-U0"
                  git-gutter+-diff-options file)))

(defun git-gutter+-diff (curfile)
  (let ((args (git-gutter+-diff-args curfile))
        (file (buffer-file-name))) ;; for tramp
    (with-temp-buffer
      (when (zerop (git-gutter+-call-git args file))
        (goto-char (point-min))
        (let ((diff-header (git-gutter+-get-diff-header))
              (diffinfos   (git-gutter+-get-diffinfos)))
          (list diff-header diffinfos))))))

(defun git-gutter+-get-diff-header ()
  (save-excursion
    (if (re-search-forward git-gutter+-hunk-header-regex nil t)
        (buffer-substring (point-min) (match-beginning 0)))))

(defsubst git-gutter+-make-diffinfo (type content start end)
  (list :type type :content content :start-line start :end-line end))

(defun git-gutter+-get-diffinfos ()
  (loop while (re-search-forward git-gutter+-hunk-header-regex nil t)
        ;; @@ -{del-line},{del-len} +{add-line},{add-len} @@
        for del-len  = (string-to-number (or (match-string 2) "1"))
        for add-line = (string-to-number (match-string 3))
        for add-len  = (string-to-number (or (match-string 4) "1"))
        for type = (cond ((zerop del-len) 'added)
                         ((zerop add-len) 'deleted)
                         (t 'modified))
        for start-line = (if (eq type 'deleted)
                             (1+ add-line)
                           add-line)
        for end-line = (if (eq type 'deleted)
                           start-line
                         (1- (+ add-line add-len)))
        for content = (git-gutter+-diff-content)
        collect
        (git-gutter+-make-diffinfo type content start-line end-line)))

(defun git-gutter+-diff-content ()
  (save-excursion
    (goto-char (line-beginning-position))
    (let ((curpoint (point)))
      (forward-line 1)
      (if (re-search-forward "^@@" nil t)
          (backward-char 3) ;; for '@@'
        (goto-char (1- (point-max)))) ; Skip trailing newline
      (buffer-substring curpoint (point)))))

(defun git-gutter+-line-to-pos (line)
  (save-excursion
    (goto-char (point-min))
    (forward-line (1- line))
    (point)))

(defun git-gutter+-before-string (sign)
  (let* ((sep-sign git-gutter+-separator-sign)
         (sep (when sep-sign
                (propertize sep-sign 'face 'git-gutter+-separator)))
         (gutter-sep (concat sign sep)))
    (propertize " " 'display `((margin left-margin) ,gutter-sep))))

(defsubst git-gutter+-select-face (type)
  (case type
    (added 'git-gutter+-added)
    (modified 'git-gutter+-modified)
    (deleted 'git-gutter+-deleted)))

(defsubst git-gutter+-select-sign (type)
  (case type
    (added git-gutter+-added-sign)
    (modified git-gutter+-modified-sign)
    (deleted git-gutter+-deleted-sign)))

(defun git-gutter+-propertized-sign (type)
  (let ((sign (git-gutter+-select-sign type))
        (face (git-gutter+-select-face type)))
    (propertize sign 'face face)))

(defun git-gutter+-view-region (sign start-line end-line)
  (let ((beg (git-gutter+-line-to-pos start-line)))
    (goto-char beg)
    (while (and (<= (line-number-at-pos) end-line) (not (eobp)))
      (git-gutter+-view-at-pos sign (point))
      (forward-line 1))))

(defun git-gutter+-view-at-pos (sign pos)
  (let ((ov (make-overlay pos pos)))
    (overlay-put ov 'before-string (git-gutter+-before-string sign))
    (overlay-put ov 'git-gutter+ t)))

(defun git-gutter+-view-diff-info (diffinfo)
  (let* ((start-line (plist-get diffinfo :start-line))
         (end-line (plist-get diffinfo :end-line))
         (type (plist-get diffinfo :type))
         (sign (git-gutter+-propertized-sign type)))
    (case type
      ((modified added) (git-gutter+-view-region sign start-line end-line))
      (deleted (git-gutter+-view-at-pos
                sign (git-gutter+-line-to-pos start-line))))))

(defun git-gutter+-sign-width (sign)
  (loop for s across sign
        sum (char-width s)))

(defun git-gutter+-longest-sign-width ()
  (let ((signs (list git-gutter+-modified-sign
                     git-gutter+-added-sign
                     git-gutter+-deleted-sign)))
    (when git-gutter+-unchanged-sign
      (add-to-list 'signs git-gutter+-unchanged-sign))
    (+ (apply 'max (mapcar 'git-gutter+-sign-width signs))
       (git-gutter+-sign-width git-gutter+-separator-sign))))

(defun git-gutter+-view-for-unchanged ()
  (save-excursion
    (let ((sign (if git-gutter+-unchanged-sign
                    (propertize git-gutter+-unchanged-sign
                                'face 'git-gutter+-unchanged)
                  " ")))
      (goto-char (point-min))
      (while (not (eobp))
        (git-gutter+-view-at-pos sign (point))
        (forward-line 1)))))

(defun git-gutter+-set-window-margin (width)
  (let ((curwin (get-buffer-window)))
    (set-window-margins curwin width (cdr (window-margins curwin)))))

(defsubst git-gutter+-file-buffer-p ()
  (and (buffer-file-name)
       default-directory
       (file-directory-p default-directory)))

;;;###autoload
(define-minor-mode git-gutter+-mode
  "Git-Gutter mode"
  :group      'git-gutter+
  :init-value nil
  :global     nil
  :lighter    git-gutter+-lighter
  (if git-gutter+-mode
      (if (and (git-gutter+-file-buffer-p)
               (git-gutter+-in-git-repository-p (buffer-file-name)))
          (progn
            (git-gutter+-add-local-hooks)
            (git-gutter+-refresh))
        (if (called-interactively-p 'any)
            (message "No Git repo for current buffer"))
        (git-gutter+-mode -1))
    (git-gutter+-remove-local-hooks)
    (git-gutter+-clear)))

(defun git-gutter+-add-local-hooks ()
  (add-hook 'after-save-hook        'git-gutter+-refresh nil t)
  ;; Turn off `git-gutter+-mode' while reverting to prevent any redundant calls to
  ;; `git-gutter+-refresh'.
  (add-hook 'before-revert-hook     'git-gutter+-turn-off nil t)
  (add-hook 'change-major-mode-hook 'git-gutter+-reenable-after-major-mode-change nil t)
  (if git-gutter+-window-config-change-function
      (add-hook 'window-configuration-change-hook
                git-gutter+-window-config-change-function nil t)))

(defun git-gutter+-remove-local-hooks ()
  (remove-hook 'after-save-hook        'git-gutter+-refresh t)
  (remove-hook 'before-revert-hook     'git-gutter+-turn-off t)
  (remove-hook 'change-major-mode-hook 'git-gutter+-reenable-after-major-mode-change t)
  (if git-gutter+-window-config-change-function
      (remove-hook 'window-configuration-change-hook
                   git-gutter+-window-config-change-function t)))

(defmacro git-gutter+-in-all-buffers (&rest body)
  `(dolist (buf (buffer-list))
     (with-current-buffer buf
       ,@body)))

;; When `define-globalized-minor-mode' is used to define `global-git-gutter+-mode',
;; `git-gutter+-mode' and thus `git-gutter+-refresh' get run twice when a new file
;; is opened. (First for `fundamental-mode', then for the file-specific mode.)
;; The following definition of `global-git-gutter+-mode' avoids any redundant calls to
;; `git-gutter+-refresh'.

;;;###autoload
(define-minor-mode global-git-gutter+-mode ()
  "Global Git-Gutter mode"
  :group      'git-gutter+
  :init-value nil
  :global     t
  (if global-git-gutter+-mode
      (progn
        (add-hook 'find-file-hook 'git-gutter+-turn-on)
        (add-hook 'after-revert-hook 'git-gutter+-turn-on)
        (add-hook 'after-change-major-mode-hook 'git-gutter+-reenable-buffers)
        (git-gutter+-in-all-buffers (git-gutter+-turn-on)))
    (remove-hook 'find-file-hook 'git-gutter+-turn-on)
    (remove-hook 'after-revert-hook 'git-gutter+-turn-on)
    (remove-hook 'after-change-major-mode-hook 'git-gutter+-reenable-buffers)
    (git-gutter+-in-all-buffers (git-gutter+-turn-off))))

(defun git-gutter+-turn-on ()
  (when (and (buffer-file-name)
             (not (memq major-mode git-gutter+-disabled-modes))
             (not git-gutter+-mode))
    (git-gutter+-mode t)))

(defun git-gutter+-turn-off ()
  (if git-gutter+-mode (git-gutter+-mode -1)))

(defun git-gutter+-reenable-after-major-mode-change ()
  (if global-git-gutter+-mode
      (add-to-list 'git-gutter+-buffers-to-reenable (current-buffer))))

(defun git-gutter+-reenable-buffers ()
  (dolist (buf git-gutter+-buffers-to-reenable)
    (with-current-buffer buf
      (git-gutter+-turn-on)))
  (setq git-gutter+-buffers-to-reenable nil))

(defsubst git-gutter+-show-gutter-p (diffinfos)
  (if git-gutter+-hide-gutter
      (or diffinfos git-gutter+-unchanged-sign)
    (or global-git-gutter+-mode git-gutter+-unchanged-sign diffinfos)))

(defun git-gutter+-show-gutter (&optional diffinfos)
  (when (git-gutter+-show-gutter-p (or diffinfos git-gutter+-diffinfos))
    (let ((win-width (or git-gutter+-window-width
                         (git-gutter+-longest-sign-width))))
      (git-gutter+-set-window-margin win-width))))

(defun git-gutter+-view-diff-infos (diffinfos)
  (when (or git-gutter+-unchanged-sign
            git-gutter+-separator-sign)
    (git-gutter+-view-for-unchanged))
  (when diffinfos
    (save-excursion
      (mapc 'git-gutter+-view-diff-info diffinfos)))
  (git-gutter+-show-gutter diffinfos))

(defsubst git-gutter+-reset-window-margin-p ()
  (or git-gutter+-hide-gutter
      (not global-git-gutter+-mode)))

(defun git-gutter+-clear-diff-infos ()
  (when (git-gutter+-reset-window-margin-p)
    (git-gutter+-set-window-margin 0))
  (remove-overlays (point-min) (point-max) 'git-gutter+ t))

(defun git-gutter+-process-diff (curfile)
  (destructuring-bind
      (diff-header diffinfos) (git-gutter+-diff curfile)
    (setq git-gutter+-diff-header diff-header
          git-gutter+-diffinfos   diffinfos)
    (save-restriction
      (widen)
      (funcall git-gutter+-view-diff-function diffinfos))))

(defun git-gutter+-search-near-diff-index (diffinfos is-reverse)
  (loop with current-line = (line-number-at-pos)
        with cmp-fn = (if is-reverse '> '<)
        for diffinfo in (if is-reverse (reverse diffinfos) diffinfos)
        for index = 0 then (1+ index)
        for start-line = (plist-get diffinfo :start-line)
        when (funcall cmp-fn current-line start-line)
        return (if is-reverse
                   (1- (- (length diffinfos) index))
                 index)))

(defun git-gutter+-search-here-diffinfo (diffinfos)
  (loop with current-line = (line-number-at-pos)
        for diffinfo in diffinfos
        for start = (plist-get diffinfo :start-line)
        for end   = (or (plist-get diffinfo :end-line) (1+ start))
        when (and (>= current-line start) (<= current-line end))
        return diffinfo))

(defun git-gutter+-collect-deleted-line (str)
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (loop while (re-search-forward "^-\\(.*?\\)$" nil t)
          collect (match-string 1) into deleted-lines
          finally return deleted-lines)))

(defun git-gutter+-delete-added-lines (start-line end-line)
  (forward-line (1- start-line))
  (let ((start-point (point)))
    (forward-line (1+ (- end-line start-line)))
    (delete-region start-point (point))))

(defun git-gutter+-insert-deleted-lines (content)
  (dolist (line (git-gutter+-collect-deleted-line content))
    (insert (concat line "\n"))))

(defun git-gutter+-do-revert-hunk (diffinfo)
  (save-excursion
    (goto-char (point-min))
    (let ((start-line (plist-get diffinfo :start-line))
          (end-line (plist-get diffinfo :end-line))
          (content (plist-get diffinfo :content)))
      (case (plist-get diffinfo :type)
        (added (git-gutter+-delete-added-lines start-line end-line))
        (deleted (forward-line (1- start-line))
                 (git-gutter+-insert-deleted-lines content))
        (modified (git-gutter+-delete-added-lines start-line end-line)
                  (git-gutter+-insert-deleted-lines content))))))

;;;###autoload
(defun git-gutter+-revert-hunk ()
  "Revert current hunk."
  (interactive)
  (git-gutter+-awhen (git-gutter+-search-here-diffinfo git-gutter+-diffinfos)
    (save-window-excursion
      (git-gutter+-popup-hunk it)
      (when (yes-or-no-p "Revert current hunk?")
        (git-gutter+-do-revert-hunk it)
        (save-buffer))
      (delete-window (get-buffer-window (get-buffer git-gutter+-popup-buffer))))))

;;;###autoload
(defun git-gutter+-popup-hunk (&optional diffinfo)
  "popup current diff hunk"
  (interactive)
  (git-gutter+-awhen (or diffinfo
                        (git-gutter+-search-here-diffinfo git-gutter+-diffinfos))
    (save-selected-window
      (with-current-buffer (get-buffer-create git-gutter+-popup-buffer)
        (erase-buffer)
        (insert (plist-get it :content))
        (insert "\n")
        (goto-char (point-min))
        (diff-mode)
        (pop-to-buffer (current-buffer))))))

;;;###autoload
(defun git-gutter+-next-hunk (arg)
  "Move to next diff hunk"
  (interactive "p")
  (if (not git-gutter+-diffinfos)
      (message "No changes in buffer")
    (let* ((is-reverse (< arg 0))
           (diffinfos git-gutter+-diffinfos)
           (len (length diffinfos))
           (index (git-gutter+-search-near-diff-index diffinfos is-reverse))
           (real-index (if index
                           (let ((next (if is-reverse (1+ index) (1- index))))
                             (mod (+ arg next) len))
                         (if is-reverse (1- (length diffinfos)) 0)))
           (diffinfo (nth real-index diffinfos)))
      (goto-char (point-min))
      (forward-line (1- (plist-get diffinfo :start-line)))
      (when (buffer-live-p (get-buffer git-gutter+-popup-buffer))
        (save-window-excursion
          (git-gutter+-popup-hunk))))))

;;;###autoload
(defun git-gutter+-previous-hunk (arg)
  "Move to previous diff hunk"
  (interactive "p")
  (git-gutter+-next-hunk (- arg)))

(defun git-gutter+-default-directory (dir curfile)
  (if (not (file-remote-p curfile))
      dir
    (let* ((vec (tramp-dissect-file-name curfile))
           (method (aref vec 0))
           (user (aref vec 1))
           (host (aref vec 2)))
      (format "/%s:%s%s:%s" method (if user (concat user "@") "") host dir))))

(defun git-gutter+-relative-path (dir curfile)
  (if (not (file-remote-p curfile))
      (file-relative-name curfile dir)
    (let ((file (aref (tramp-dissect-file-name curfile) 3)))
      (replace-regexp-in-string (concat "\\`" dir) "" curfile))))

(defun git-gutter+-refresh ()
  (git-gutter+-clear)
  (let ((file (buffer-file-name)))
    (when (and file (file-exists-p file))
      (git-gutter+-awhen (git-gutter+-root-directory file)
        (let* ((default-directory (git-gutter+-default-directory it file))
               (curfile (git-gutter+-relative-path default-directory file)))
          (git-gutter+-process-diff curfile))))))

(defun git-gutter+-clear ()
  (save-restriction
    (widen)
    (funcall git-gutter+-clear-function))
  (setq git-gutter+-diffinfos nil))


;;; Staging

;;;###autoload
(defun git-gutter+-stage-hunks ()
  (interactive)
  (let* ((line-range (if (use-region-p)
                         (cons (line-number-at-pos (region-beginning))
                               (line-number-at-pos (region-end)))))
         (diffinfos (git-gutter+-diffinfos-to-stage line-range)))
    (when diffinfos
      (let ((error-msg (git-gutter+-stage-diffinfos diffinfos line-range)))
        (if error-msg
            (message "Error staging hunks:\n%s" error-msg))
        (git-gutter+-refresh)))))

(defun git-gutter+-diffinfos-to-stage (line-range)
  (if line-range
      (git-gutter+-diffinfos-between-lines line-range)
    (git-gutter+-awhen (git-gutter+-search-here-diffinfo git-gutter+-diffinfos)
      (list it))))

(defsubst git-gutter+-diffinfo-between-lines-p (diffinfo start-line end-line)
  (let ((diff-start (plist-get diffinfo :start-line))
        (diff-end   (plist-get diffinfo :end-line)))
    (and (<= start-line diff-end)
         (<= diff-start end-line))))

(defun git-gutter+-diffinfos-between-lines (line-range)
  (let ((start-line (car line-range))
        (end-line   (cdr line-range)))
    (delq nil
          (mapcar (lambda (diffinfo)
                    (if (git-gutter+-diffinfo-between-lines-p
                         diffinfo start-line end-line)
                        diffinfo))
                  git-gutter+-diffinfos))))

(defun git-gutter+-stage-diffinfos (diffinfos line-range)
  (let ((header git-gutter+-diff-header))
    (with-temp-buffer
      (insert header)
      ;; Insert hunks in reverse so that earlier hunks don't invalidate the line
      ;; number information of the later hunks.
      (dolist (diffinfo (nreverse diffinfos))
        (git-gutter+-insert-diffinfo diffinfo line-range)
        (goto-char (point-max)))
      (git-gutter+-call-on-current-buffer
       "git" "apply" "--unidiff-zero" "--cached" "-"))))

(defun git-gutter+-insert-diffinfo (diffinfo line-range)
  (let ((content (plist-get diffinfo :content))
        (type    (plist-get diffinfo :type)))
    (if (not line-range)
        (git-gutter+-insert-hunk content type)
      (let ((diff-start-line (plist-get diffinfo :start-line))
            (diff-end-line   (plist-get diffinfo :end-line))
            (start-line (car line-range))
            (end-line   (cdr line-range)))
        (git-gutter+-insert-hunk content type
                                (1+ (- start-line diff-start-line))
                                (1+ (- end-line diff-start-line)))))))

(defun git-gutter+-call-on-current-buffer (program &rest args)
  "Returns nil if PROGRAM ran successfully. Returns an error description otherwise."
  (unless (zerop (apply #'call-process-region (point-min) (point-max)
                        program t t nil args))
    (buffer-string)))

(defsubst git-gutter+-read-hunk-header (hunk)
  ;; @@ -{del-line},{del-len} +{add-line},{add-len} @@
  (string-match git-gutter+-hunk-header-regex hunk)
  (list (string-to-number (match-string 1 hunk))
        (string-to-number (or (match-string 2 hunk) "1"))
        (string-to-number (match-string 3 hunk))
        (string-to-number (or (match-string 4 hunk) "1"))))

(defun git-gutter+-insert-hunk (hunk type &optional start end)
  "If START and END are provided, only insert addition (+) lines between
START and END (inclusive). START and END are both line numbers starting with 1."
  (destructuring-bind
      (del-line del-len add-line add-len) (git-gutter+-read-hunk-header hunk)
    (let* ((start (max 1 (or start 1)))
           (end   (min add-len (or end add-len)))
           (insert-all-p (or (eq type :deleted)
                             (and (eq start 1) (eq end add-len))))
           (num-lines-selected (if insert-all-p
                                   add-len
                                 (1+ (- end start)))))
      ;; When the user selected the last lines of a hunk with type `modified' (but
      ;; not the complete hunk), then don't insert any deletion (-) lines from that
      ;; hunk.
      (if (and (eq type 'modified)
               (< 1 start) (= end add-len))
          (setq type 'modified-trailing))

      (save-excursion
        (insert hunk "\n"))

      (git-gutter+-delete-hunk-header)

      (if (not insert-all-p)
          (git-gutter+-modify-hunk type num-lines-selected del-len start end))

      (let ((hunk-header (git-gutter+-make-hunk-header type num-lines-selected
                                                      del-line del-len add-line)))
        (insert hunk-header "\n")))))

(defun git-gutter+-delete-hunk-header ()
  (let ((hunk-start (point)))
    (forward-line 1)
    (delete-region hunk-start (point))))

(defun git-gutter+-modify-hunk (type num-lines-selected del-len start end)
  (let ((first-line-selected (+ del-len (1- start)))
        selected-lines)
    (save-excursion
      (forward-line first-line-selected)
      (let ((start-point (point)))
        (forward-line num-lines-selected)
        (setq selected-lines (buffer-substring start-point (point)))))
    (save-excursion
      (if (eq type 'modified) (forward-line del-len)) ; skip over deletion (-) lines
      (delete-region (point) (point-max))
      (insert selected-lines))))

(defun git-gutter+-make-hunk-header (type num-lines-selected del-line del-len add-line)
  (let ((add-len num-lines-selected))
    (case type
      (added (setq add-line (1+ del-line)))
      (modified-trailing (setq add-line (+ del-line del-len)
                               del-line (1- add-line)
                               del-len 0))
      (t (setq add-line del-line)))
    (format "@@ -%d,%d +%d,%d @@"
            del-line del-len
            add-line add-len)))


;;; Committing

;;;###autoload
(defun git-gutter+-commit ()
  (interactive)
  (let ((file (buffer-file-name))
        (dir default-directory))
    (require 'magit)
    (setq magit-pre-log-edit-window-configuration (current-window-configuration))
    (magit-log-edit)
    (git-gutter+-show-staged-changes file dir)))

;;;###autoload
(defun git-gutter+-stage-and-commit ()
  (interactive)
  (git-gutter+-stage-hunks)
  (git-gutter+-commit))

(defun git-gutter+-show-staged-changes (file dir)
  (save-selected-window
    (let* ((buf    (get-buffer-create "*Staged Changes*"))
           (window (get-buffer-window buf)))
      (if window
          (select-window window)
        (if (<= (length (window-list)) 2)
            (split-window))
        (pop-to-buffer buf)))
    (erase-buffer)
    (let ((default-directory dir))
      (git-gutter+-call-git (list "diff" "--staged") file))
    (goto-char (point-min))
    (diff-mode)))

;;; Use Magit for committing staged hunks.
;;
;; `magit-log-edit-commit' expects `magit-find-status-buffer' to return the Magit
;; status buffer from which the commit edit was launched.
;; But when the commit edit is started by git-gutter+, a status buffer is not always
;; present.
;; Therefore, `magit-log-edit-commit' is patched to use a custom version of
;; `magit-find-status-buffer' that returns the current log edit buffer if no status
;; buffer is opened. This works fine, since Magit will accept any buffer that has the
;; correct `default-directory' set.
;;
;; Using Magit has two side effects:
;; 1. .git/MERGE_MSG gets deleted after commiting. (But before that, its contents
;; will have been pasted into the log edit buffer by Magit.)
;; 2. The buffer local value of `process-environment' is erased in the buffer that
;; started the commit edit. This is a bug in Magit that will be fixed in the next
;; minor release.

(defvar git-gutter+-orig-find-status-buffer)

(defvar git-gutter+-find-status-buf-or-cur-buf
  (lambda (&optional dir)
    (or (funcall git-gutter+-orig-find-status-buffer dir)
        (current-buffer))))

(defadvice magit-log-edit-commit (around without-status-buffer compile activate)
  ;; Rebind `magit-find-status-buffer' to `git-gutter+-find-status-buf-or-cur-buf'
  ;; while `magit-log-edit-commit' is running.
  ;; Using `flet' would have been much simpler, but it's deprecated since 24.3.
  (setq git-gutter+-orig-find-status-buffer (symbol-function 'magit-find-status-buffer))
  (fset 'magit-find-status-buffer git-gutter+-find-status-buf-or-cur-buf)
  (unwind-protect
      ad-do-it
    (fset 'magit-find-status-buffer git-gutter+-orig-find-status-buffer)))


;;; Magit synchronization
;; Force Magit to refresh git-gutter+ when updating the VC mode line.
;; Use the same strategy as for `magit-log-edit-commit'.

(defvar git-gutter+-orig-vc-find-file-hook)

(defvar git-gutter+-vc-find-file-hook-with-refresh
  (lambda ()
    (funcall git-gutter+-orig-vc-find-file-hook)
    (if git-gutter+-mode (git-gutter+-refresh))))

(defadvice magit-update-vc-modeline (around refresh-git-gutter+ compile activate)
  ;; `magit-update-vc-modeline' calls `vc-find-file-hook' (a function!) on each
  ;; buffer in the repo. Temporarily rebind it to `vc-find-file-hook-with-refresh'.
  (setq git-gutter+-orig-vc-find-file-hook (symbol-function 'vc-find-file-hook))
  (fset 'vc-find-file-hook git-gutter+-vc-find-file-hook-with-refresh)
  (unwind-protect
      ad-do-it
    (fset 'vc-find-file-hook git-gutter+-orig-vc-find-file-hook)))

(provide 'git-gutter+)

;;; git-gutter+.el ends here
