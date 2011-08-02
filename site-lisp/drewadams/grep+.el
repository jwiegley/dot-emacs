;;; grep+.el --- Extensions to standard library `grep.el'.
;; 
;; Filename: grep+.el
;; Description: Extensions to standard library `grep.el'.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2005-2011, Drew Adams, all rights reserved.
;; Created: Fri Dec 16 13:36:47 2005
;; Version: 22.0
;; Last-Updated: Thu Feb 24 15:16:55 2011 (-0800)
;;           By: dradams
;;     Update #: 486
;; URL: http://www.emacswiki.org/cgi-bin/wiki/grep+.el
;; Keywords: tools, processes, compile
;; Compatibility: GNU Emacs: 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   `avoid', `compile', `compile+', `compile-', `fit-frame',
;;   `font-lock', `frame-fns', `grep', `misc-fns', `syntax',
;;   `thingatpt', `thingatpt+'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary:
;;
;;  Extensions to standard library `grep.el':
;;
;;    1. Additional keys are bound here.
;;    2. Mouse-over is active on the entire hit line, not just on the
;;       file-name part.
;;    3. `grep' command provides a default search string in all cases,
;;       and that default value is better.
;;    4. Commands are provided to remove commented lines from `grep'
;;       output and toggle their automatic removal.
;;
;;  Put this in your initialization file (`~/.emacs'):
;;
;;    (require 'grep+)
;;
;;
;;  New user options defined here:
;;
;;    `grepp-default-comment-line-regexp', `grepp-default-regexp-fn'.
;;
;;  New commands defined here:
;;
;;    `choose-grep-buffer', `grepp-choose-grep-buffer',
;;    `grepp-new-grep-buffer', `grepp-remove-comments',
;;    `grepp-toggle-comments', `new-grep-buffer',
;;    `remove-grep-comments', `toggle-grep-comments'.
;;
;;  New non-interactive functions defined here:
;;
;;    `grepp-buffers', `grepp-default-regexp-fn'.
;;
;;
;;  ***** NOTE: The following variables defined in `grep.el'
;;              have been REDEFINED HERE:
;;
;;  `grep-mode-font-lock-keywords', `grep-regexp-alist'
;;    - Mouse-over the whole line.
;;  
;;
;;
;;  ***** NOTE: The following minor mode defined in `grep.el'
;;              has been REDEFINED HERE:
;;
;;  `grep-mode' - No change.  Redefined here so it uses modified value
;;                of `grep-regexp-alist'.
;;
;;
;;  ***** NOTE: The following functions defined in `grep.el'
;;              have been REDEFINED HERE:
;;
;;  `grep', `grep-default-command' - Use `grepp-default-regexp-fn'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change log:
;;
;; 2011/02/15 dadams
;;     For Emacs 24+, do not set grep-hit-face to font-lock-keyword-face.
;;     grep-regexp-alist, grep-mode-font-lock-keywords, grep-mode: Updated for Emacs 24.
;; 2011/01/04 dadams
;;     Removed autoload cookies from non-interactive functions.  Added them for defalias commands.
;; 2007/12/04 dadams
;;     grep, grepp-default-regexp-fn: Changed single-quote to double-quote.
;; 2007/12/02 dadams
;;     grep and doc strings of grepp-default-regexp-fn (option and function):
;;       If active, nonempty region, use its (quoted) text as default regexp.
;;         Thx to Martin Nordholts for the suggestion.
;; 2006/12/11 dadams
;;     Added: grepp-toggle-comments.  Bound to M-;.
;; 2006/12/09 dadams
;;     Added: grep-mode-font-lock-keywords.  Needed for refontification (e.g. flush-lines).
;;     Added: grepp-remove-comments, grepp-default-comment-line-regexp.  Bound former to ;.
;; 2006/11/17 dadams
;;     grep-regexp-alist: Defined explicitly, not by modifying original.
;;                        Use nil for HIGHLIGHT part of structure.
;; 2006/11/14 dadams
;;     Added: grepp-buffers, grepp-choose-grep-buffer, grepp-new-grep-buffer.
;;            Bound: grepp-choose-grep-buffer, grepp-new-grep-buffer.
;;     Renamed: grep-default-regexp-fn to grepp-default-regexp-fn.
;; 2006/09/10 dadams
;;     Updated definition of grep-mode with latest from grep.el.
;; 2005/12/17 dadams
;;     Added: grep-default-regexp-fn, grep-default-command.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; ;; Floor, Boston, MA 02110-1301, USA.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

(require 'compile+ nil t) ;; (no error if not found) - to pick up enhancements for grep too.
(require 'font-lock) ;; font-lock-keyword-face
(require 'grep)
(require 'thingatpt+ nil t) ;; (no error if not found) symbol-name-nearest-point

;;;;;;;;;;;;;;;;;;;;;;;


;;;###autoload
(defcustom grepp-default-comment-line-regexp ":[0-9]+: *;"
  "*Default regexp for a comment line, for use in `grepp-remove-comments'.
The default value matches lines that begin with a Lisp comment."
  :type 'string :group 'grep)

;;;###autoload
(defcustom grepp-default-regexp-fn (if (fboundp 'symbol-name-nearest-point)
                                       'symbol-name-nearest-point
                                     'word-at-point)
  "*Function of 0 args called to provide default search regexp to \\[grep].
Some reasonable choices: `word-nearest-point',
`symbol-name-nearest-point', `sexp-nearest-point'.

This is ignored if Transient Mark mode is on and the region is active
and non-empty.  In that case, the quoted (\") region text is used as
the default regexp.

If `grepp-default-regexp-fn' is nil and no prefix arg is given to
`grep', then no defaulting is done.

Otherwise, if the value is not a function, then function
`grepp-default-regexp-fn' does the defaulting."
  :type '(choice (const :tag "No default search regexp (unless you use `C-u')" nil)
          (function :tag "Function of zero args to provide default search regexp"))
  :group 'grep)

(defun grepp-default-regexp-fn ()
  "*Function of 0 args called to provide default search regexp to \\[grep].
This is used only if both of the following are true:
- Transient Mark mode is off or the region is inactive or empty.
- The value of option `grepp-default-regexp-fn' is
  `grepp-default-regexp-fn'.

When this is used, the default regexp is provided by calling the
first of these that references a defined function:
  - variable `grepp-default-regexp-fn'
  - variable `find-tag-default-function'
  - the `find-tag-default-function' property of the `major-mode'
  - function `symbol-name-nearest-point', if bound
  - function `grep-tag-default'"
  (cond ((fboundp grepp-default-regexp-fn) grepp-default-regexp-fn)
        (find-tag-default-function)
        ((get major-mode 'find-tag-default-function))
        ((fboundp 'symbol-name-nearest-point) 'symbol-name-nearest-point)
        (t 'find-tag-default)))



;;; REPLACE ORIGINAL in `grep.el'
;;; Use `grepp-default-regexp-fn' to define `tag-default'.
;;;
(defun grep-default-command ()
  (let ((tag-default (shell-quote-argument (or (funcall (grepp-default-regexp-fn)) "")))
        (sh-arg-re "\\(\\(?:\"\\(?:[^\"]\\|\\\\\"\\)+\"\\|'[^']+'\\|[^\"' \t\n]\\)+\\)")
        (grep-default (or (car grep-history) grep-command)))
    ;; Replace the thing matching for with that around cursor.
    (when (or (string-match
               (concat "[^ ]+\\s +\\(?:-[^ ]+\\s +\\)*" sh-arg-re "\\(\\s +\\(\\S +\\)\\)?")
               grep-default)
              (string-match "\\(\\)\\'" grep-default)) ; If the string is not yet complete.
      (unless (or (not (stringp buffer-file-name))
                  (when (match-beginning 2)
                    (save-match-data
                      (string-match (wildcard-to-regexp (file-name-nondirectory
                                                         (match-string 3 grep-default)))
                                    (file-name-nondirectory buffer-file-name)))))
        (setq grep-default (concat (substring grep-default 0 (match-beginning 2))
                                   " *."
                                   (file-name-extension buffer-file-name))))
      (replace-match tag-default t t grep-default 1))))



;;; REPLACE ORIGINAL in `grep.el'
;;; Use `grepp-default-regexp-fn' to define default search string.
;;;
;;;###autoload
(defun grep (command-args &optional highlight-regexp)
  "Run `grep', with user-specified args, and collect output in a buffer.
COMMAND-ARGS are the user-specified arguments.
While `grep' runs asynchronously, you can use the
\\[next-error] command (M-x next-error), or \\<grep-mode-map>\\[compile-goto-error]
in the *grep* output buffer, to find the text that `grep' hits refer to.

This command uses a special history list for its COMMAND-ARGS, so you can
easily repeat a grep command.

The text (regexp) to find is defaulted as follows:

- If Transient Mark mode is on and the region is active and nonempty,
  then the double-quoted region text is used.  (If the region contains
  double-quotes (\"), then you will need to escape them by hand.)

- If option `grepp-default-regexp-fn' is a function, then it is called
  to return the default regexp.

- If `grepp-default-regexp-fn' is nil and no prefix arg is provided,
  then no default regexp is used.

If a prefix arg is provided, then the default text is substituted
into the last grep command in the grep command history (or into
`grep-command' if that history list is empty).  That is, the same
command options and files to search are used as the last time.

If specified, optional second arg HIGHLIGHT-REGEXP is the regexp to
temporarily highlight in visited source lines."
  (interactive
   (progn
     (unless (and grep-command (or (not grep-use-null-device) (eq grep-use-null-device t)))
       (grep-compute-defaults))
     (let ((default (grep-default-command)))
       (list (read-from-minibuffer
              "grep <pattern> <files> :  "
              (if current-prefix-arg
                  default
                (concat grep-command
                        (if (and transient-mark-mode mark-active
                                 (not (eq (region-beginning) (region-end))))
                            ;; $$$$$ Would it be better to use `shell-quote-argument' on the region?
                            (concat "\"" (buffer-substring (region-beginning) (region-end)) "\"")
                          (and grepp-default-regexp-fn (funcall (grepp-default-regexp-fn))))
                        " "))
              nil nil 'grep-history
              (if current-prefix-arg nil default))))))

  ;; Setting process-setup-function makes exit-message-function work
  ;; even when async processes aren't supported.
  (compilation-start (if (and grep-use-null-device null-device)
                         (concat command-args " " null-device)
                       command-args)
                     'grep-mode nil highlight-regexp))


;;;###autoload
(defalias 'new-grep-buffer 'grepp-new-grep-buffer)
;;;###autoload
(defun grepp-new-grep-buffer ()
  "Rename current grep buffer and switch to new buffer *grep*.
Current buffer must be a grep buffer.  It is renamed to *grep*<N>."
  (interactive)
  (unless (string-match "\\*grep\\*" (buffer-name (current-buffer)))
    (error "Not in a grep buffer"))
  (rename-uniquely)
  (switch-to-buffer "*grep*")
  (grep-mode))


;;;###autoload
(defalias 'choose-grep-buffer 'grepp-choose-grep-buffer)
;;;###autoload
(defun grepp-choose-grep-buffer (buf)
  "Switch to a grep buffer."
  (interactive
   (let ((bufs (grepp-buffers)))
     (unless bufs (error "No grep buffers"))
     (list (completing-read "Grep buffer: " bufs nil t nil nil
                            (and grep-last-buffer (buffer-name grep-last-buffer))))))
  (switch-to-buffer buf)
  (select-frame-set-input-focus (selected-frame))
  (grep-mode))

(defun grepp-buffers ()
  "List of names of grep buffers."
  (let ((bufs nil))
    (dolist (buf (buffer-list))
      (when (string-match "\\*grep\\*" (buffer-name buf))
        (push (list (buffer-name buf)) bufs)))
    (nreverse bufs)))

;;;###autoload
(defalias 'remove-grep-comments 'grepp-remove-comments)
;;;###autoload
(defun grepp-remove-comments (&optional read-regexp-p)
  "Remove lines that are completely commented out.
With a prefix argument, you are prompted for the regexp used to match
 commented lines.  The default value is 
 `grepp-default-comment-line-regexp'.
With no prefix argument, this default value is used as the regexp.

You can use command `grep-toggle-comments' to toggle automatic removal
of commented lines.

Note: This simply removes lines that begin with the regexp you
provide.  It does not, in general, remove multi-line comments.  Use it
to remove C++ comments that start with //, but not multi-line comments
between /* and */."
  (interactive "P")
  (when (eq major-mode 'grep-mode) ; Do nothing otherwise, so can use in `compilation-filter-hook'.
    (let ((inhibit-read-only t)
          (regexp
           (if read-regexp-p
               (read-from-minibuffer "Comment regexp: " nil nil nil 'regexp-history
                                     grepp-default-comment-line-regexp)
             grepp-default-comment-line-regexp)))
      (save-excursion (flush-lines regexp (point-min) (point-max))))))

;;;###autoload
(defalias 'toggle-grep-comments 'grepp-toggle-comments)
;;;###autoload
(defun grepp-toggle-comments ()
  "Toggle removal of commented lines in grep output."
  (interactive)
  (cond ((and (boundp 'compilation-filter-hook)
              (memq 'remove-grep-comments compilation-filter-hook))
         (remove-hook 'compilation-filter-hook 'remove-grep-comments)
         (when (consp grep-history) (grep (car grep-history)))
         (message "Automatic removal of commented lines is now OFF"))
        (t
         (add-hook 'compilation-filter-hook 'remove-grep-comments)
         (when (consp grep-history) (grep (car grep-history)))
         (message "Automatic removal of commented lines is now ON"))))


;; New bindings.
(define-key grep-mode-map "g" 'grep)
(define-key grep-mode-map "G" 'grep)
(define-key grep-mode-map "n" 'next-error-no-select)
(define-key grep-mode-map "N" 'next-error-no-select)
(define-key grep-mode-map "p" 'previous-error-no-select)
(define-key grep-mode-map "P" 'previous-error-no-select)
(define-key grep-mode-map "+" 'grepp-new-grep-buffer)
(define-key grep-mode-map "b" 'grepp-choose-grep-buffer)
(define-key grep-mode-map "B" 'grepp-choose-grep-buffer)
(define-key grep-mode-map ";" 'grepp-remove-comments)
(define-key grep-mode-map [(meta ?\;)] 'grepp-toggle-comments)

;; New face values
(set-face-foreground grep-match-face nil)
(set-face-background grep-match-face "SkyBlue")
(unless (> emacs-major-version 23) (setq grep-hit-face font-lock-keyword-face))



;;; REPLACE ORIGINAL `grep-regexp-alist' defined in `grep.el'.
;;;
;;; Use mouseover on whole line.  Same as original, except for this.
(unless (featurep 'grep+)
  (setq grep-regexp-alist
        '(("^\\(.+?\\)\\(:[ \t]*\\)\\([1-9][0-9]*\\)\\2" 1 3)
          ;; Rule to match column numbers is commented out since no known grep produces them
          ;; ("^\\(.+?\\)\\(:[ \t]*\\)\\([0-9]+\\)\\2\\(?:\\([0-9]+\\)\\(?:-\\([0-9]+\\)\\)?\\2\\)?"
          ;;  1 3 (4 . 5))

          ;; DREW ADAMS: 1) appended `.*', 2) changed HIGHLIGHT to nil, to highlight whole match.
          ("^\\(\\(.+?\\):\\([1-9][0-9]*\\):\\).*?\
\\(\033\\[01;31m\\(?:\033\\[K\\)?\\)\\(.*?\\)\\(\033\\[[0-9]*m\\).*" ; DREW ADAMS appended `.*'.
           2 3
           ;; Calculate column positions (beg . end) of first grep match on a line
           ((lambda ()
              (setq compilation-error-screen-columns nil)
              (- (match-beginning 4) (match-end 1)))
            .
            (lambda () (- (match-end 5) (match-end 1)
                     (- (match-end 4) (match-beginning 4)))))
           nil
           nil) ; DREW ADAMS changed HIGHLIGHT to nil, to highlight whole match.
          ("^Binary file \\(.+\\) matches$" 1 nil nil 0 1))))



;;; REPLACE ORIGINAL `grep-regexp-alist' defined in `grep.el'.
;;;
;;; Use mouseover on whole line.  Same as original, except for this.
(unless (featurep 'grep+)
  (setq grep-mode-font-lock-keywords
        '( ;; Command output lines.
          ("^\\(.+?\\):\\([0-9]+\\):.*" (0 '(face nil mouse-face compilation-mouseover)))
          ;; ("^\\([A-Za-z_0-9/\.+-]+\\)[ \t]*:" 1 font-lock-function-name-face)) ; Removed by Stefan, Emacs 24.
          (": \\(.+\\): \\(?:Permission denied\\|No such \\(?:file or directory\\|device or \
address\\)\\)$"
           1 grep-error-face)
          ;; remove match from grep-regexp-alist before fontifying
          ;; Set both `compilation-message' and `message' to nil, since Emacs before version 24 uses `message'.
          ("^Grep[/a-zA-z]* started.*"
           (0 '(face nil compilation-message nil message nil help-echo nil mouse-face nil) t))
          ("^Grep[/a-zA-z]* finished \\(?:(\\(matches found\\))\\|with \\(no matches found\\)\\).*"
           ;; Set both `compilation-message' and `message' to nil, since Emacs before version 24 uses `message'.
           (0 '(face nil compilation-message nil message nil help-echo nil mouse-face nil) t)
           (1 compilation-info-face nil t)
           (2 compilation-warning-face nil t))
          ("^Grep[/a-zA-z]* \\(exited abnormally\\|interrupt\\|killed\\|terminated\\)\\(?:.*with \
code \\([0-9]+\\)\\)?.*"
           ;; Set both `compilation-message' and `message' to nil, since Emacs before version 24 uses `message'.
           (0 '(face nil compilation-message nil message nil help-echo nil mouse-face nil) t)
           (1 grep-error-face)
           (2 grep-error-face nil t))
          ("^.+?-[0-9]+-.*\n" (0 grep-context-face))
          ;; Highlight grep matches and delete markers
          ("\\(\033\\[01;31m\\)\\(.*?\\)\\(\033\\[[0-9]*m\\)"
           ;; Refontification does not work after the markers have been
           ;; deleted.  So we use the font-lock-face property here as Font
           ;; Lock does not clear that.
           (2 (list 'face nil 'font-lock-face grep-match-face))
           ((lambda (bound))
            (progn
              ;; Delete markers with `replace-match' because it updates
              ;; the match-data, whereas `delete-region' would render it obsolete.
              (when (> emacs-major-version 23) (syntax-ppss-flush-cache (match-beginning 0)))
              (replace-match "" t t nil 3)
              (replace-match "" t t nil 1))))
          ("\033\\[[0-9;]*[mK]"
           ;; Delete all remaining escape sequences
           ((lambda (bound))
            (when (> emacs-major-version 23) (syntax-ppss-flush-cache (match-beginning 0)))
            (replace-match "" t t))))))


;;; REPLACE ORIGINAL `grep-mode' defined in `grep.el'.
;;; Re-create, so it uses the modified `grep-regexp-alist'.
;;; This definition SHOULD BE THE SAME AS THE ORIGINAL in `grep.el'.
;;;
(define-compilation-mode grep-mode "Grep"
  "Sets `grep-last-buffer' and `compilation-window-height'."
  (setq grep-last-buffer (current-buffer))
  (when (boundp 'grep-mode-tool-bar-map)
    (set (make-local-variable 'tool-bar-map) grep-mode-tool-bar-map))
  (set (make-local-variable 'compilation-error-face) grep-hit-face)
  (set (make-local-variable 'compilation-error-regexp-alist) grep-regexp-alist)
  (set (make-local-variable 'compilation-process-setup-function) 'grep-process-setup)
  (set (make-local-variable 'compilation-disable-input) t))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'grep+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; grep+.el ends here
