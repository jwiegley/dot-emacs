;;; git-gutter+.el --- Manage Git hunks straight from the buffer -*- lexical-binding: t; -*-

;; Copyright (C) 2013 by Syohei YOSHIDA and contributors

;; Author: Syohei YOSHIDA <syohex@gmail.com> and contributors
;; URL: https://github.com/nonsequitur/git-gutter-plus
;; Version: 0.4

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

;; Package-Requires: ((git-commit "0") (dash "0"))
;; Keywords: git vc

;;; Commentary:
;;
;; View, stage and revert Git changes straight from the buffer.

;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'tramp)
(require 'log-edit)
(require 'git-commit)

(defgroup git-gutter+ nil
  "Manage Git hunks straight from the buffer"
  :prefix "git-gutter+-"
  :group 'vc)

(defcustom git-gutter+-window-width nil
  "Character width of the gutter margin. Set this variable if the automatically
calculated width looks wrong. (This can happen with some special characters.)"
  :type '(choice (const :tag "Automatically determined" nil)
                 (integer :tag "Set manually"))
  :group 'git-gutter+)

(defcustom git-gutter+-git-executable "git"
  "The path of the Git executable."
  :type 'string
  :group 'git-gutter+)

(defcustom git-gutter+-diff-options nil
  "List of strings containing extra arguments to 'git diff'"
  :type '(repeat (string :tag "Option"))
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
  :type '(choice (const :tag "No sign" nil)
                 (string :tag "Sign"))
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

(defvar git-gutter+-mode-map
  (make-sparse-keymap))

(defvar git-gutter+-view-diff-function nil
  "Function to call for displaying diffs")

(defvar git-gutter+-clear-function nil
  "Function to call for clearing the diff display")

(defvar git-gutter+-window-config-change-function nil
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

(defalias 'git-gutter+-popup-hunk 'git-gutter+-show-hunk)
(defalias 'git-gutter+-revert-hunk 'git-gutter+-revert-hunks)

(defun git-gutter+-enable-default-display-mode ()
  (setq git-gutter+-view-diff-function 'git-gutter+-view-diff-infos
        git-gutter+-clear-function     'git-gutter+-clear-diff-infos
        git-gutter+-window-config-change-function 'git-gutter+-show-gutter))

(unless git-gutter+-view-diff-function
  (git-gutter+-enable-default-display-mode))

(defun git-gutter+-call-git (args &optional file output-destination)
  "Calls Git synchronously. Returns t on zero exit code, nil otherwise"
  (zerop (if (and file (file-remote-p file))
             (apply #'process-file git-gutter+-git-executable nil output-destination nil args)
           (apply #'call-process git-gutter+-git-executable nil output-destination nil args))))

(defun git-gutter+-insert-git-output (args &optional file)
  "Inserts stdout from Git into the current buffer, ignores stderr.
Returns t on zero exit code, nil otherwise."
  (git-gutter+-call-git args file '(t nil)))

(defun git-gutter+-in-git-repository-p (file)
  (with-temp-buffer
    (when (git-gutter+-insert-git-output '("rev-parse" "--is-inside-work-tree") file)
      (goto-char (point-min))
      (string= "true" (buffer-substring-no-properties
                       (point) (line-end-position))))))

(defun git-gutter+-root-directory (file)
  (with-temp-buffer
    (when (git-gutter+-insert-git-output '("rev-parse" "--show-toplevel") file)
      (goto-char (point-min))
      (let ((root (buffer-substring-no-properties (point) (line-end-position))))
        (unless (string= root "")
          (file-name-as-directory root))))))

(defsubst git-gutter+-diff-args (file)
  (delq nil `("--no-pager" "diff" "--no-color" "--no-ext-diff" "-U0"
                  ,@git-gutter+-diff-options ,file)))

(defun git-gutter+-diff (curfile)
  (let ((args (git-gutter+-diff-args curfile))
        (file (buffer-file-name))) ;; for tramp
    (with-temp-buffer
      (if (git-gutter+-insert-git-output args file)
          (progn (goto-char (point-min))
                 (let ((diff-header (git-gutter+-get-diff-header))
                       (diffinfos   (git-gutter+-get-diffinfos)))
                   (list diff-header diffinfos)))
        (message "Error callling git diff:\n%s" (buffer-string))
        nil))))

(defun git-gutter+-get-diff-header ()
  (save-excursion
    (if (re-search-forward git-gutter+-hunk-header-regex nil t)
        (buffer-substring (point-min) (match-beginning 0)))))

(defsubst git-gutter+-make-diffinfo (type content start end)
  (list :type type :content content :start-line start :end-line end))

(defun git-gutter+-get-diffinfos ()
  (cl-loop while (re-search-forward git-gutter+-hunk-header-regex nil t)
           ;; Hunk header format:
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
    (goto-char (line-beginning-position)) ; Move to beginning of hunk header
    (let ((hunk-start (point)))
      ;; Move to end of hunk
      (forward-line 1)
      (if (re-search-forward "^@@" nil t)
          (backward-char 3) ;; exclude "\n@@"
        (goto-char (1- (point-max)))) ; Skip trailing newline
      (buffer-substring hunk-start (point)))))

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
  (cl-case type
    (added 'git-gutter+-added)
    (modified 'git-gutter+-modified)
    (deleted 'git-gutter+-deleted)))

(defsubst git-gutter+-select-sign (type)
  (cl-case type
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
    (cl-case type
      ((modified added) (git-gutter+-view-region sign start-line end-line))
      (deleted (git-gutter+-view-at-pos
                sign (git-gutter+-line-to-pos start-line))))))

(defun git-gutter+-sign-width (sign)
  (cl-loop for s across sign
           sum (char-width s)))

(defun git-gutter+-longest-sign-width ()
  (let ((signs (list git-gutter+-modified-sign
                     git-gutter+-added-sign
                     git-gutter+-deleted-sign)))
    (when git-gutter+-unchanged-sign
      (push signs git-gutter+-unchanged-sign))
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
               (not (file-symlink-p (buffer-file-name)))
               (git-gutter+-in-git-repository-p (buffer-file-name)))
          (progn
            (git-gutter+-add-local-hooks)
            (git-gutter+-refresh))
        (if (called-interactively-p 'any)
            (message (if (and (buffer-file-name) (file-symlink-p (buffer-file-name)))
                         "Symlinked files are not supported by Git-Gutter+"
                       "No Git repo for current buffer")))
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
  (let ((diff-result (git-gutter+-diff curfile)))
    (when diff-result
      (cl-destructuring-bind
          (diff-header diffinfos) diff-result
        (setq git-gutter+-diff-header diff-header
              git-gutter+-diffinfos   diffinfos)
        (save-restriction
          (widen)
          (funcall git-gutter+-view-diff-function diffinfos))))))

(defun git-gutter+-search-near-diff-index (diffinfos is-reverse)
  (cl-loop with current-line = (line-number-at-pos)
           with cmp-fn = (if is-reverse '> '<)
           for diffinfo in (if is-reverse (reverse diffinfos) diffinfos)
           for index = 0 then (1+ index)
           for start-line = (plist-get diffinfo :start-line)
           when (funcall cmp-fn current-line start-line)
           return (if is-reverse
                      (1- (- (length diffinfos) index))
                    index)))

(defun git-gutter+-diffinfo-at-point ()
  (save-restriction
    (widen)
    (cl-loop with current-line = (line-number-at-pos)
             for diffinfo in git-gutter+-diffinfos
             for start = (plist-get diffinfo :start-line)
             for end   = (or (plist-get diffinfo :end-line) (1+ start))
             when (and (>= current-line start) (<= current-line end))
             return diffinfo)))

(defun git-gutter+-collect-deleted-line (str)
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (cl-loop while (re-search-forward "^-\\(.*?\\)$" nil t)
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
    (save-restriction
      (widen)
      (goto-char (point-min))
      (let ((start-line (plist-get diffinfo :start-line))
            (end-line (plist-get diffinfo :end-line))
            (content (plist-get diffinfo :content)))
        (cl-case (plist-get diffinfo :type)
          (added (git-gutter+-delete-added-lines start-line end-line))
          (deleted (forward-line (1- start-line))
                   (git-gutter+-insert-deleted-lines content))
          (modified (git-gutter+-delete-added-lines start-line end-line)
                    (git-gutter+-insert-deleted-lines content)))))))

(defun git-gutter+-revert-hunks ()
  "Revert hunk at point. If region is active, revert all hunks within the region."
  (interactive)
  (let* ((diffinfos (git-gutter+-selected-diffinfos))
         (one-diffinfo-p (= 1 (length diffinfos))))
    (save-window-excursion
      (if one-diffinfo-p (git-gutter+-show-hunk (car diffinfos)))
      (when (and diffinfos
                 (yes-or-no-p (if one-diffinfo-p
                                  "Revert hunk?"
                                (format "Revert %d hunks?" (length diffinfos)))))
        ;; Revert diffinfos in reverse so that earlier hunks don't invalidate the
        ;; line number information of the later hunks.
        (dolist (diffinfo (nreverse diffinfos))
          (git-gutter+-do-revert-hunk diffinfo))
        (save-buffer))
      (if one-diffinfo-p
          (--when-let (get-buffer git-gutter+-popup-buffer)
            (kill-buffer it))))))

(defun git-gutter+-show-hunk (&optional diffinfo)
  "Show hunk at point in another window"
  (interactive (list (git-gutter+-diffinfo-at-point)))
  (when diffinfo
    (save-selected-window
      (with-current-buffer (get-buffer-create git-gutter+-popup-buffer)
        (setq buffer-read-only nil)
        (erase-buffer)
        (insert (plist-get diffinfo :content) "\n")
        (goto-char (point-min))
        (diff-mode)
        (view-mode)
        (pop-to-buffer (current-buffer))))))

(defun git-gutter+-show-hunk-inline-at-point ()
  "Show hunk by temporarily expanding it at point"
  (interactive)
  (-when-let (diffinfo (git-gutter+-diffinfo-at-point))
    (let ((diff (with-temp-buffer
                  (insert (plist-get diffinfo :content) "\n")
                  (diff-mode)
                  ;; Force-fontify the invisible temp buffer
                  (font-lock-default-function 'diff-mode)
                  (font-lock-default-fontify-buffer)
                  (buffer-string))))
      (momentary-string-display diff (point-at-bol)))))

(defun git-gutter+-next-hunk (arg)
  "Move to next diff hunk"
  (interactive "p")
  (if (not git-gutter+-diffinfos)
      (message "No changes in buffer")
    (save-restriction
      (widen)
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
            (git-gutter+-show-hunk diffinfo)))))))

(defun git-gutter+-previous-hunk (arg)
  "Move to previous diff hunk"
  (interactive "p")
  (git-gutter+-next-hunk (- arg)))

(defun git-gutter+-remote-default-directory (dir file)
  (let* ((vec (tramp-dissect-file-name file))
         (method (aref vec 0))
         (user (aref vec 1))
         (host (aref vec 2)))
    (format "/%s:%s%s:%s" method (if user (concat user "@") "") host dir)))

(defun git-gutter+-remote-file-path (dir file)
  (let ((file (aref (tramp-dissect-file-name file) 3)))
    (replace-regexp-in-string (concat "\\`" dir) "" file)))

(defun git-gutter+-local-file-path (file)
  (if (eq system-type 'windows-nt)
      ;; Cygwin can't handle Windows absolute paths
      (file-relative-name file default-directory)
    file))

(defun git-gutter+-refresh ()
  (git-gutter+-clear)
  (let ((file (buffer-file-name)))
    (when (and file (file-exists-p file))
      (if (file-remote-p file)
          (let* ((repo-root (git-gutter+-root-directory file))
                 (default-directory (git-gutter+-remote-default-directory repo-root file)))
            (git-gutter+-process-diff (git-gutter+-remote-file-path repo-root file)))
        (git-gutter+-process-diff (git-gutter+-local-file-path file))))))

(defun git-gutter+-clear ()
  (save-restriction
    (widen)
    (funcall git-gutter+-clear-function))
  (setq git-gutter+-diffinfos nil))


;;; Staging

(defun git-gutter+-stage-hunks ()
  "Stage hunk at point. If region is active, stage all hunk lines within the region."
  (interactive)
  (git-gutter+-stage-hunks-between-lines (when (use-region-p)
                                          (cons (line-number-at-pos (region-beginning))
                                                (line-number-at-pos (region-end))))))

(defun git-gutter+-stage-hunks-between-lines (line-range)
  (let ((diffinfos (git-gutter+-selected-diffinfos line-range)))
    (when diffinfos
      (let ((error-msg (git-gutter+-stage-diffinfos diffinfos line-range)))
        (when error-msg
          (message "Error staging hunks:\n%s" error-msg))
        (git-gutter+-refresh)))))

(defun git-gutter+-selected-diffinfos (&optional line-range)
  (unless line-range
    (setq line-range (if (use-region-p)
                         (cons (line-number-at-pos (region-beginning))
                               (line-number-at-pos (region-end))))))
  (if line-range
      (git-gutter+-diffinfos-between-lines line-range)
    (--when-let (git-gutter+-diffinfo-at-point)
      (list it))))

(defsubst git-gutter+-diffinfo-between-lines-p (diffinfo start-line end-line)
  (let ((diff-start (plist-get diffinfo :start-line))
        (diff-end   (plist-get diffinfo :end-line)))
    (and (<= start-line diff-end)
         (<= diff-start end-line))))

(defun git-gutter+-diffinfos-between-lines (line-range)
  (save-restriction
    (widen)
    (let ((start-line (car line-range))
          (end-line   (cdr line-range)))
      (delq nil
            (mapcar (lambda (diffinfo)
                      (if (git-gutter+-diffinfo-between-lines-p
                           diffinfo start-line end-line)
                          diffinfo))
                    git-gutter+-diffinfos)))))

(defun git-gutter+-stage-diffinfos (diffinfos line-range)
  (let ((header git-gutter+-diff-header))
    (with-temp-buffer
      (insert header)
      ;; Insert hunks in reverse so that earlier hunks don't invalidate the line
      ;; number information of the later hunks.
      (dolist (diffinfo (nreverse diffinfos))
        (git-gutter+-insert-diffinfo diffinfo line-range)
        (goto-char (point-max)))
      (git-gutter+-call-git-on-current-buffer
       '("apply" "--unidiff-zero" "--cached" "-")))))

(defun git-gutter+-insert-diffinfo (diffinfo line-range)
  (let ((content (plist-get diffinfo :content))
        (type    (plist-get diffinfo :type)))
    (if (not line-range)
        (git-gutter+-insert-hunk content type)
      (let ((diff-start-line (plist-get diffinfo :start-line))
            (start-line (car line-range))
            (end-line   (cdr line-range)))
        (git-gutter+-insert-hunk content type
                                (1+ (- start-line diff-start-line))
                                (1+ (- end-line diff-start-line)))))))

;; Silence the byte-compiler
(declare-function tramp-sh-handle-call-process-region nil)

(unless (fboundp 'tramp-sh-handle-call-process-region)
  (defun tramp-sh-handle-call-process-region
    (start end program &optional delete buffer display &rest args)
    "Like `call-process-region', for Tramp files."
    (let ((tmpfile (tramp-compat-make-temp-file "")))
      (write-region start end tmpfile)
      (when delete (delete-region start end))
      (unwind-protect
          (apply 'process-file program tmpfile buffer display args)
        (delete-file tmpfile)))))

(defun git-gutter+-call-git-on-current-buffer (args)
  "Sends the current buffer contents to Git and replaces them with Git's output.

 RETURNS nil if Git ran successfully. Returns an error description otherwise."
  (let ((call-process-region-func
         (if (eq (tramp-find-foreign-file-name-handler default-directory)
                 'tramp-sh-file-name-handler)
             #'tramp-sh-handle-call-process-region
           #'call-process-region)))
    (unless (zerop (apply call-process-region-func (point-min) (point-max)
                          git-gutter+-git-executable t t nil args))
      (buffer-string))))

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
  (cl-destructuring-bind
      (del-line del-len add-line add-len) (git-gutter+-read-hunk-header hunk)
    (let* ((start (max 1 (or start 1)))
           (end   (min add-len (or end add-len)))
           (insert-all-p (or (eq type :deleted)
                             (and (= start 1) (= end add-len))))
           (num-lines-selected (if insert-all-p
                                   add-len
                                 (1+ (- end start)))))
      ;; When the user selected the last lines of a hunk with type `modified' (but
      ;; not the complete hunk), then don't insert any deletion (-) lines from that
      ;; hunk.
      (if (and (eq type 'modified)
               (> start 1) (= end add-len))
          (setq type 'modified-trailing))

      (save-excursion
        (insert hunk "\n"))

      (git-gutter+-delete-hunk-header)

      (if (not insert-all-p)
          (git-gutter+-modify-hunk type num-lines-selected del-len start))

      (let ((hunk-header (git-gutter+-make-hunk-header type num-lines-selected
                                                      del-line del-len add-line)))
        (insert hunk-header "\n")))))

(defun git-gutter+-delete-hunk-header ()
  (let ((hunk-start (point)))
    (forward-line 1)
    (delete-region hunk-start (point))))

(defun git-gutter+-modify-hunk (type num-lines-selected del-len start)
  "Remove all addition (+) lines from hunk that aren't selected.
If TYPE is not `modified', also remove all deletion (-) lines."
  (let ((first-line-selected (+ del-len (1- start)))
        selected-lines)
    (save-excursion
      (forward-line first-line-selected)
      (let ((selection-start (point)))
        (forward-line num-lines-selected)
        (setq selected-lines (buffer-substring selection-start (point)))))
    (save-excursion
      (if (eq type 'modified) (forward-line del-len)) ; skip over deletion (-) lines
      (delete-region (point) (point-max))
      (insert selected-lines))))

(defun git-gutter+-make-hunk-header (type num-lines-selected del-line del-len add-line)
  (let ((add-len num-lines-selected))
    (cl-case type
      (added (setq add-line (1+ del-line)))
      (modified-trailing (setq add-line (+ del-line del-len)
                               del-line (1- add-line)
                               del-len 0))
      (t (setq add-line del-line)))
    (format "@@ -%d,%d +%d,%d @@"
            del-line del-len
            add-line add-len)))


;;; Committing
;; This section draws heavily from old Magit source code.

(defvar git-gutter+-pre-commit-window-config nil)
(defvar git-gutter+-commit-origin-buffer nil
  "Buffer that started the commit")

(defconst git-gutter+-commit-buffer-name "*Commit Message*")
(defconst git-gutter+-staged-changes-buffer-name "*Staged Changes*")

;;;###autoload
(defun git-gutter+-commit ()
  "Commit staged changes. If nothing is staged, ask to stage the current buffer."
  (interactive)

  (when (and (not (git-gutter+-anything-staged-p))
             git-gutter+-diffinfos
             (y-or-n-p "Nothing staged. Stage current buffer? "))
    (git-gutter+-stage-whole-buffer))

  (let ((file (buffer-file-name))
        (dir default-directory))
    (git-gutter+-save-window-config-if-needed)
    (setq git-gutter+-commit-origin-buffer (current-buffer))
    (git-gutter+-open-commit-edit-buffer dir)
    (git-gutter+-show-staged-changes file dir)))

(defun git-gutter+-stage-and-commit ()
  (interactive)
  (git-gutter+-stage-hunks)
  (git-gutter+-commit))

(defun git-gutter+-stage-and-commit-whole-buffer ()
  (interactive)
  (git-gutter+-stage-whole-buffer)
  (git-gutter+-commit))

(defun git-gutter+-save-window-config-if-needed ()
  ;; Only save the window config if the temporary buffers that get popped-up by
  ;; git-gutter+ are not already visible.
  ;; In this way, `git-gutter+-commit' can be called twice in a row without
  ;; losing the original window config.
  (when (not (and git-gutter+-pre-commit-window-config
                  (get-buffer-window git-gutter+-commit-buffer-name)
                  (get-buffer-window git-gutter+-staged-changes-buffer-name)))
    (setq git-gutter+-pre-commit-window-config (current-window-configuration))))

(defun git-gutter+-open-commit-edit-buffer (dir)
  "Opens a buffer for composing the commit message"
  (pop-to-buffer (get-buffer-create git-gutter+-commit-buffer-name))
  (setq default-directory dir)
  (git-gutter+-commit-mode)
  (message "Type C-c C-c to commit (C-c C-k to cancel)."))

(defun git-gutter+-pop-to-staged-changes-buffer ()
  ;; Shift the bias towards vertical splitting.
  ;; If possible, the staged changes should be shown below the
  ;; commit message buffer.
  (let ((split-height-threshold 50))
    (pop-to-buffer git-gutter+-staged-changes-buffer-name)))

(defun git-gutter+-show-staged-changes (file dir)
  (save-selected-window
    (git-gutter+-pop-to-staged-changes-buffer)
    (setq buffer-read-only nil)
    (erase-buffer)
    (let ((default-directory dir))
      (git-gutter+-insert-git-output '("diff" "--staged") file))
    (goto-char (point-min))
    (diff-mode)
    (view-mode)))

(defsubst git-gutter+-abort-commit-when-no-changes (allow-empty amend)
  (unless (or amend
              allow-empty
              (git-gutter+-anything-staged-p))
    (error
     "Refusing to create empty commit. Maybe you want to amend (%s) or allow-empty (%s)?"
     (key-description (car (where-is-internal
                            'git-gutter+-commit-toggle-amending)))
     (key-description (car (where-is-internal
                            'git-gutter+-commit-toggle-allow-empty))))))

(defsubst git-gutter+-buffer-is-whitespace ()
  (save-excursion
    (goto-char (point-min))
    (looking-at-p "[ \t\n]*\\'")))

(defun git-gutter+-publish-commit ()
  "Publish commit"
  (interactive)
  (let* ((fields (git-gutter+-commit-get-fields))
         (amend       (equal "yes" (git-gutter+-commit-get-field 'amend       fields)))
         (allow-empty (equal "yes" (git-gutter+-commit-get-field 'allow-empty fields)))
         (author      (git-gutter+-commit-get-field 'author fields))
         (date        (git-gutter+-commit-get-field 'date fields)))

    (git-gutter+-abort-commit-when-no-changes allow-empty amend)

    (git-gutter+-push-to-comment-ring (buffer-string))

    (git-gutter+-commit-set-fields nil) ; Delete message header

    (when (git-gutter+-buffer-is-whitespace)
      (erase-buffer)
      (insert "(Empty description)"))

    (let ((error-msg (git-gutter+-call-git-on-current-buffer
                      (append '("--no-pager" "commit" "-F" "-")
                              (if amend '("--amend"))
                              (if allow-empty '("--allow-empty"))
                              (if author (list (concat "--author=" author)))
                              (if date   (list (concat "--date=" date)))))))
      (if error-msg
          (progn
            (message "Commit error:\n%s" error-msg)
            (erase-buffer)
            (insert (ring-ref log-edit-comment-ring 0))) ; Reinsert commit message
        (message "Commit successful.")
        (git-gutter+-close-commit-edit-buffer)
        (git-gutter+-update-vc-modeline)))))

(defun git-gutter+-close-commit-edit-buffer ()
  "Abort edits and discard commit message being composed."
  (interactive)
  (kill-buffer)
  (set-window-configuration git-gutter+-pre-commit-window-config))

(defun git-gutter+-update-vc-modeline ()
  (when (buffer-live-p git-gutter+-commit-origin-buffer)
    (with-current-buffer git-gutter+-commit-origin-buffer
      ;; Updating the modeline has no effect if the buffer still has
      ;; changes - it will remain in the 'modified' state. So skip it then.
      (unless git-gutter+-diffinfos
        (ignore-errors (vc-find-file-hook))))))

(defun git-gutter+-stage-whole-buffer ()
  (git-gutter+-stage-hunks-between-lines (cons (line-number-at-pos (point-min))
                                              (line-number-at-pos (point-max)))))

(defun git-gutter+-unstage-whole-buffer ()
  (interactive)
  (git-gutter+-call-git (list "reset" "--quiet" "HEAD" "--"
                             (file-name-nondirectory buffer-file-name)))
  (git-gutter+-refresh))

(defun git-gutter+-anything-staged-p ()
  "Return t if the current repo has staged changes"
  (not (git-gutter+-call-git '("diff" "--quiet" "--cached"))))

(defun git-gutter+-commit-toggle-amending ()
  "Toggle whether this will be an amendment to the previous commit.
\(i.e., whether commit is run via 'git commit --amend')"
  (interactive)
  ;; Remove the newline that 'git-commit-mode' adds to a new commit
  ;; message buffer by default. This prevents an ugly visual
  ;; gap between the commit message header and the previous commit
  ;; message.
  (when (git-gutter+-buffer-is-whitespace)
    (erase-buffer))

  (let ((amend-was-already-set (git-gutter+-commit-get-field 'amend)))
    (git-gutter+-commit-toggle-field 'amend t)
    (unless amend-was-already-set
      ;; Insert previous commit message
      (goto-char (point-max))
      (unless (zerop (current-column))
        (insert "\n"))
      (insert (git-gutter+-get-last-commit-msg)
              "\n"))))

(defun git-gutter+-commit-toggle-allow-empty ()
  "Toggle whether this commit is allowed to be empty.
\(i.e., whether commit is run via 'git commit --allow-empty')"
  (interactive)
  (git-gutter+-commit-toggle-field 'allow-empty t))

(defun git-gutter+-format-author (author email)
  (format "%s <%s>" author email))

(defun git-gutter+-commit-toggle-author ()
  "Toggle whether this commit should have a user-defined author."
  (interactive)
  (git-gutter+-commit-toggle-input
   'author (git-gutter+-format-author
            (or (git-gutter+-get-cfg "user" "name") "Author Name")
            (or (git-gutter+-get-cfg "user" "email") "author@email"))))

(defun git-gutter+-commit-toggle-date ()
  "Toggle whether this commit should have a user-defined date."
  (interactive)
  (git-gutter+-commit-toggle-input 'date
                                  ;; ISO 8601
                                  (format-time-string "%Y-%m-%dT%T%z" (current-time))))

(defun git-gutter+-push-to-comment-ring (comment)
  (when (or (ring-empty-p log-edit-comment-ring)
            (not (equal comment (ring-ref log-edit-comment-ring 0))))
    (ring-insert log-edit-comment-ring comment)))

(defun git-gutter+-get-last-commit-msg ()
  (git-gutter+-git-output '("log" "--max-count=1" "--pretty=format:%s%n%n%b" "HEAD")))

(defun git-gutter+-get-cfg (&rest keys)
  (git-gutter+-git-output (list "config" (mapconcat 'identity keys "."))))

(defun git-gutter+-git-output (args)
  (with-temp-buffer
    (git-gutter+-insert-git-output args)
    ;; Delete trailing newlines
    (goto-char (point-min))
    (if (re-search-forward "\n+\\'" nil t)
        (replace-match ""))
    (buffer-string)))


;;; Commit message header

(defconst git-gutter+-commit-header-end "-- End of commit options header --\n")

(defun git-gutter+-commit-get-field (name &optional fields)
  (cdr (assq name (or fields (git-gutter+-commit-get-fields)))))

(defun git-gutter+-commit-set-field (name value)
  (let* ((fields (git-gutter+-commit-get-fields))
         (cell   (assq name fields)))
    (cond (cell
           (if value
               (rplacd cell value)
             (setq fields (delq cell fields))))
          (t
           (if value
               (setq fields (append fields (list (cons name value)))))))
    (git-gutter+-commit-set-fields fields)))

(defun git-gutter+-commit-toggle-field (name default)
  "Toggle the commit header field named NAME.
If it's currently unset, set it to DEFAULT (t or nil)."
  (let* ((fields (git-gutter+-commit-get-fields))
         (cell   (assq name fields)))
    (if cell
        (rplacd cell (if (equal (cdr cell) "yes") "no" "yes"))
      (setq fields (cl-acons name (if default "yes" "no") fields)))
    (git-gutter+-commit-set-fields fields)))

(defun git-gutter+-commit-toggle-input (name default)
  "Toggle the commit header input named NAME.
If it's currently unset, set it to DEFAULT (a string). If it is
set remove it."
  (let* ((fields (git-gutter+-commit-get-fields))
         (cell (assq name fields)))
    (if cell
        (setq fields (assq-delete-all name fields))
      (setq fields (cl-acons name default fields)))
    (git-gutter+-commit-set-fields fields)))

(defun git-gutter+-commit-get-fields ()
  (let (result)
    (goto-char (point-min))
    (while (looking-at "^\\([A-Za-z0-9-_]+\\): *\\(.+\\)?$")
      (let ((name  (intern (downcase (match-string 1))))
            (value (read (or (match-string 2) "nil"))))
        (push (cons name value) result))
      (forward-line))
    (if (looking-at (regexp-quote git-gutter+-commit-header-end))
        (nreverse result))))

(defun git-gutter+-commit-set-fields (fields)
  (goto-char (point-min))
  ;; Delete commit header
  (if (search-forward-regexp (format "^\\(?:[A-Za-z0-9-_]+:.*\n\\)*%s"
                                     (regexp-quote git-gutter+-commit-header-end))
                             nil t)
      (delete-region (match-beginning 0) (match-end 0)))
  (goto-char (point-min))
  (when fields
    (dolist (field fields)
      (insert (capitalize (symbol-name (car field))) ": "
              (prin1-to-string (cdr field)) "\n"))
    (insert git-gutter+-commit-header-end)))


;;; git-gutter+-commit-mode
;; Like git-commit-mode, but adds keybindings to git-gutter+ commands and
;; highlighting support for the commit message header.

(defvar save-place) ; Silence byte-compiler

(define-derived-mode git-gutter+-commit-mode text-mode "Git-Gutter-Commit"
  ;; The following is copied from `git-commit-mode'.
  ;; Directly deriving from `git-commit-mode' would pull in unwanted setup code
  ;; that's incompatible with `git-gutter+-commit-mode'.
  (setq font-lock-defaults (list (git-commit-mode-font-lock-keywords) t))
  (set (make-local-variable 'font-lock-multiline) t)
  (git-commit-propertize-diff)
  (setq fill-column git-commit-fill-column)
  ;; Recognize changelog-style paragraphs
  (set (make-local-variable 'paragraph-start)
       (concat paragraph-start "\\|*\\|("))
  ;; Setup comments
  (set (make-local-variable 'comment-start) "#")
  (set (make-local-variable 'comment-start-skip)
       (concat "^" (regexp-quote comment-start) "+"
               "\\s-*"))
  (set (make-local-variable 'comment-use-syntax) nil)
  ;; Do not remember point location in commit messages
  (when (fboundp 'toggle-save-place)
    (setq save-place nil))
  ;; If the commit summary is empty, insert a newline after point
  (when (string= "" (buffer-substring-no-properties
                     (line-beginning-position)
                     (line-end-position)))
    (open-line 1))
  (set (make-local-variable 'log-edit-comment-ring-index) -1)
  (run-mode-hooks 'git-commit-mode-hook))

(put 'git-gutter+-commit-mode 'derived-mode-parent 'git-commit-mode)

(setq git-gutter+-commit-mode-map
  (let ((map (copy-keymap git-commit-mode-map)))
    (define-key map (kbd "C-c C-c") 'git-gutter+-publish-commit)
    (define-key map (kbd "C-c C-k") 'git-gutter+-close-commit-edit-buffer)
    (define-key map (kbd "C-c C-a") 'git-gutter+-commit-toggle-amending)
    (define-key map (kbd "C-c C-e") 'git-gutter+-commit-toggle-allow-empty)
    (define-key map (kbd "C-c C-u") 'git-gutter+-commit-toggle-author)
    (define-key map (kbd "C-c C-d") 'git-gutter+-commit-toggle-date)
    (define-key map (kbd "C-c C-b") 'git-commit-ack)
    (define-key map (kbd "M-p") 'log-edit-previous-comment)
    (define-key map (kbd "M-n") 'log-edit-next-comment)
    map))

(defface git-gutter+-commit-header-face
  '((t :inherit font-lock-comment-face))
  "Highlights the commit message header"
  :group 'git-gutter+-faces)

(defconst git-gutter+-commit-header-regex
  (concat "\\(?:.\\|\n\\)*?" (regexp-quote git-gutter+-commit-header-end)))

(defconst git-gutter+-skip-commit-header-regex
  (concat "\\`\\(?:" git-gutter+-commit-header-regex "\\)?"))

;; Modify git-commit-summary-regexp to ignore the commit header
(defadvice git-commit-summary-regexp
  (after ignore-git-gutter+-commit-header activate compile)
  (if (eq major-mode 'git-gutter+-commit-mode)
      (setq ad-return-value
            (concat git-gutter+-skip-commit-header-regex
                    (substring ; Remove leading "\\`"
                     ad-return-value 2)))))

(defun git-gutter+-commit-font-lock-keywords ()
  "Like `git-commit-mode-font-lock-keywords' but with commit header highlighting"
  `((,(concat "\\`" git-gutter+-commit-header-regex) . 'git-gutter+-commit-header-face)
    ,@(git-commit-mode-font-lock-keywords)))


;;; Magit synchronization

;; 1. Force Magit to refresh git-gutter+ when updating the VC mode line.
;;    This is not needed in newer Magit versions that use `auto-revert-mode'.
(defvar git-gutter+-orig-vc-find-file-hook)

(defvar git-gutter+-vc-find-file-hook-with-refresh
  (lambda ()
    (funcall git-gutter+-orig-vc-find-file-hook)
    (if git-gutter+-mode (git-gutter+-refresh))))

(defadvice magit-update-vc-modeline (around refresh-git-gutter+ compile activate)
  ;; `magit-update-vc-modeline' calls `vc-find-file-hook' (a function!) on each
  ;; buffer in the repo. Temporarily rebind it to `vc-find-file-hook-with-refresh',
  ;; which calls git-gutter+-refresh after updating the VC mode line.

  ;; Silence the byte-compiler. The top-level defvar for `git-gutter+-orig-vc-find-file-hook'
  ;; isn't sufficient for this compiled defadvice.
  (defvar git-gutter+-orig-vc-find-file-hook)
  ;; Using `flet' would have been much simpler, but it's deprecated since 24.3.
  (setq git-gutter+-orig-vc-find-file-hook (symbol-function 'vc-find-file-hook))
  (fset 'vc-find-file-hook git-gutter+-vc-find-file-hook-with-refresh)
  (unwind-protect
      ad-do-it
    (fset 'vc-find-file-hook git-gutter+-orig-vc-find-file-hook)))

;; 2. Refresh git-gutter+ when a buffer is staged or unstaged
(defvar git-gutter+-last-magit-head nil)
(defvar git-gutter+-previously-staged-files nil)
(defvar git-gutter+-staged-files nil)

(with-eval-after-load 'magit
  ;; Old Magit versions
  (add-hook 'magit-refresh-status-hook 'git-gutter+-on-magit-refresh-status)
  ;; New Magit versions
  (add-hook 'magit-status-refresh-hook 'git-gutter+-on-magit-refresh-status))

(defun git-gutter+-on-magit-refresh-status ()
  (let ((head (git-gutter+-get-magit-head)))
    (when head
      (setq git-gutter+-previously-staged-files git-gutter+-staged-files)
      (setq git-gutter+-staged-files (git-gutter+-get-magit-staged-files))

      (if (string= head git-gutter+-last-magit-head)
          (git-gutter+-magit-refresh)
        (setq git-gutter+-previously-staged-files git-gutter+-staged-files)
        (setq git-gutter+-last-magit-head head)))))

(defun git-gutter+-get-magit-head ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "Head:\\s-+\\([0-9a-z]+\\)" nil t)
      (match-string-no-properties 1))))

(defun git-gutter+-get-magit-staged-files ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^Staged changes" nil t)
      (let (staged-files)
        (while (re-search-forward "^\\s-*[Mm]odified\\s-+\\(.+\\)$" nil t)
          (push (match-string-no-properties 1) staged-files))
        staged-files))))

(defun git-gutter+-magit-refresh ()
  (dolist (file-to-refresh (cl-set-exclusive-or git-gutter+-previously-staged-files
                                                git-gutter+-staged-files
                                                :test 'equal))
    (let ((buffer (get-file-buffer file-to-refresh)))
      (when buffer
        (with-current-buffer buffer
          (git-gutter+-refresh))))))

(provide 'git-gutter+)

;;; git-gutter+.el ends here
