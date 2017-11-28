;;; worf.el --- A warrior does not press so many keys! (in org-mode)

;; Copyright (C) 2014 Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/worf
;; Version: 0.1.0
;; Package-Requires: ((swiper "0.7.0") (ace-link "0.1.0") (hydra "0.13.0") (zoutline "0.1.0"))
;; Keywords: lisp

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This extension works similar to http://orgmode.org/manual/Speed-keys.html,
;; while adding in a bit of vi flavor.
;;
;; Representing the point with "|", pressing a-z, A-Z, or 0-9 while
;; the text is as below will call a command instead of inserting these
;; characters:
;;
;;   |* foo
;;   *|* bar
;;   |#+ baz
;;
;; As you see, the general theme is beginning of line + org markup.
;; Below, "#+..." will be referred to as markup.
;; Similar to vi, "hjkl" represent the arrow keys:
;;
;; - "j" moves down across headings and markup, but does not switch
;;   between either: use "h"/"l" for that. The exception is the first
;;   markup in the file that does not belong to any heading.
;;
;; - "k" moves up across headings and markup, with same rules as "j".
;;
;; - "h" moves left, i.e. to the parent heading of current thing.
;;   You can use it e.g. to go from fifth level 3 heading to the
;;   parent level 2 heading, or from the second source block to the
;;   parent heading.
;;
;; - "l" moves right (i.e. to the first child of current heading).
;;   You can use it to get to the first markup of current heading.
;;
;; Worf borrows the idea of verbs and nouns from vi: the commands are
;; sentences, combinations of a verb and a noun used together.
;; Verb #1 is "goto", which is implicit and active by default.
;;
;; 5 nouns are available currently:
;; "h" - left
;; "j" - down
;; "k" - up
;; "l" - right
;; "a" - add heading
;; "p" - property
;;
;; Verb #2 is `worf-change-mode', bound to "c". Verbs in worf are
;; sticky: once you press "c", change verb will be active until you
;; switch to a different verb. This is different from vi, where the
;; verb will deactivate itself after the first command.
;;
;; Use the same letter to deactivate a verb as to activate it,
;; i.e. "c" will deactivate `worf-change-mode'.  "q" will universally
;; deactivate any verb and return you to "goto" implicit verb.
;;
;; While `worf-change-mode' is active, "hjkl" move the current heading
;; in appropriate directions: it's the same as holding "M-" and using
;; arrow keys in the default org.
;; "p" will change the selected property.
;;
;; Verb #3 is `worf-change-tree-mode', bound to "cf".  While
;; `worf-change-tree-mode' is active, "hjkl" move the current heading
;; tree in appropriate directions: it's the same as holding "S-M-" and
;; using arrow keys in the default org.
;;
;; Verb #4 is `worf-change-shift-mode', bound to "cs".
;; It make "hjkl" act as "S-" and arrows in default org.
;;
;; Verb #5 is `worf-keyword-mode', bound to "w". You select a keyword
;; e.g. TODO or NEXT and "j"/"k" move just by the selected keyword,
;; skipping all other headings. Additionally "a" will add a new
;; heading with the appropriate keyword, e.g. "wta" will add a new
;; TODO, and "wna" will add a new "NEXT".
;;
;; Verb #6 is `worf-clock-mode', bound to "C". This one isn't sticky
;; and has only two nouns that work with it "i" (in) and "o" (out).
;;
;; Verb #7 is `worf-delete-mode', bound to "d". This one isn't sticky
;; and changes the behavior of "j" to delete down, and "k" to delete
;; up. You can mix in numbers to delete many times, i.e. d3j will
;; delete 3 headings at once.
;; "p" will delete the selected property.
;;
;; Verb #8 is `worf-yank-mode', bound to "y". It's similar to
;; `worf-delete-mode', but will copy the headings into the kill ring
;; instead of deleting.
;;
;; Verb #9 is `worf-mark-mode', bound to "m". It's similar to
;; `worf-delete-mode', but will mark the headings instead.
;;
;; Some other things included in worf, that don't fit into the
;; verb-noun structure, are:
;;
;;  - "o" (`worf-ace-link'): open a link within current heading that's
;;    visible on screen. See https://github.com/abo-abo/ace-link for a
;;    package that uses this method in other modes.
;;
;;  - "g" (`worf-goto'): select an outline in the current buffer, with
;;    completion.  It's very good when you want to search/navigate to
;;    a heading by word or level. See https://github.com/abo-abo/lispy
;;    for a package that uses this method to navigate Lisp code.
;;
;;  - "L" (`worf-copy-heading-id'): copy the link to current heading
;;    to the kill ring. This may be useful when you want to create a
;;    lot of links.
;;

;;; Code:

;; ——— Requires ————————————————————————————————————————————————————————————————
(require 'ace-link)
(require 'org)
(require 'org-id)
(require 'org-clock)
(require 'zoutline)
(require 'flyspell)

(defgroup worf nil
  "Navigate Org-mode with plain keys."
  :group 'org
  :prefix "worf-")

;; ——— Minor mode ——————————————————————————————————————————————————————————————
(defvar worf-sharp "^#\\+"
  "Shortcut for the org's #+ regex.")

(defvar worf-regex "^\\(?:\\*\\|#\\+\\)"
  "Shortcut for worf's special regex.")

(defvar worf-regex-full "^\\(?:\\*+ \\|#\\+\\|:\\)"
  "Shortcut for worf's special regex.")

(defvar worf-mode-map
  (make-sparse-keymap))

;;;###autoload
(define-minor-mode worf-mode
    "Minor mode for navigating and editing `org-mode' files.

When `worf-mode' is on, various unprefixed keys call commands
if the (looking-back \"^*+\") is true.

\\{worf-mode-map}"
  :group 'worf
  :lighter " ✇")

;; ——— Macros ——————————————————————————————————————————————————————————————————
(defmacro worf-dotimes-protect (n &rest bodyform)
  "Execute N times the BODYFORM unless an error is signaled.
Return nil couldn't execute BODYFORM at least once.
Otherwise return t."
  (declare (indent 1))
  `(let ((i 0)
         out)
     (ignore-errors
       (while (<= (cl-incf i) ,n)
         ,@bodyform
         (setq out t)))
     out))

(defmacro worf-flet (binding &rest body)
  "Temporarily override BINDING and execute BODY."
  (declare (indent 1))
  (let* ((name (car binding))
         (old (cl-gensym (symbol-name name))))
    `(let ((,old (symbol-function ',name)))
       (unwind-protect
            (progn
              (fset ',name (lambda ,@(cdr binding)))
              ,@body)
         (fset ',name ,old)))))

;; ——— Key binding machinery ———————————————————————————————————————————————————
(defun worf--insert-or-call (def alist)
  "Return a lambda to call DEF if position is special.
Otherwise call `self-insert-command'."
  (let ((disable (cdr (assoc :disable alist)))
        (break (cdr (assoc :break alist))))
    `(lambda ,(help-function-arglist def)
       ,(format "Call `%s' when special, self-insert otherwise.\n\n%s"
                (symbol-name def) (documentation def))
       ,(interactive-form def)
       (let (cmd)
         (cond ((worf--special-p)
                ,(when disable `(,disable -1))
                (,def ,@(delq '&rest (delq '&optional (help-function-arglist def))))
                (unless (or ,break (worf--special-p))
                  (worf-up 1)))

               (t
                (setq this-command 'org-self-insert-command)
                (org-self-insert-command 1)))))))

(defvar ac-trigger-commands '(self-insert-command))
(defvar company-begin-commands '(self-insert-command))

(defun worf--flag-to-alist (lst flag)
  "If FLAG is on LST, change it to (FLAG . t)."
  (let ((x (memq flag lst)))
    (when x
      (setcar x (cons flag t)))
    lst))

(defun worf-define-key (keymap key def &rest plist)
  "Forward to (`define-key' KEYMAP KEY DEF)
DEF is modified by `worf--insert-or-call'."
  (let ((func (defalias (intern (concat "wspecial-" (symbol-name def)))
                  (worf--insert-or-call def (worf--flag-to-alist
                                             plist :break)))))
    (unless (member func ac-trigger-commands)
      (push func ac-trigger-commands))
    (unless (member func company-begin-commands)
      (push func company-begin-commands))
    (unless (memq func flyspell-delayed-commands)
      (add-to-list 'flyspell-delayed-commands func))
    (define-key keymap (kbd key) func)))

;; ——— Verb machinery ——————————————————————————————————————————————————————————
(defvar worf-known-verbs '(worf-keyword-mode)
  "List of registered verbs.")

(defun worf-disable-verbs-except (verb)
  "Disable all verbs except VERB."
  (mapc
   (lambda (v) (funcall v -1))
   (remq verb worf-known-verbs)))

(defmacro worf-defverb (name grammar)
  (let ((sym (intern (format "worf-%s-mode" name)))
        (keymap (intern (format "worf-%s-mode-map" name)))
        (doc (format "%s verb." (capitalize name)))
        (lighter (format " [%s]" name)))
    `(progn
       (defvar ,keymap (make-sparse-keymap))
       (define-minor-mode ,sym
           ,doc
         :keymap ,keymap
         :group 'worf
         :lighter ,lighter
         (cond (,sym
                (worf-disable-verbs-except ',sym))
               (t nil)))
       (mapc (lambda (x)
               (let ((y (memq :disable x)))
                 (when y
                   (setcar y (cons :disable ',sym))))
               (apply 'worf-define-key (cons ,keymap x)))
             ,grammar)
       (unless (memq ',sym worf-known-verbs)
         (push ',sym worf-known-verbs))
       worf-known-verbs)))

;; ——— Verbs: change ———————————————————————————————————————————————————————————
(defun worf-change-name ()
  "Change #+name of the current source block."
  (interactive)
  (let ((el (org-element-at-point)))
    (if (eq (org-element-type el) 'src-block)
        (let ((beg (org-element-property :begin el)))
          (if (org-element-property :name el)
              (let ((end (org-element-property :end el))
                    (case-fold-search t))
                (goto-char beg)
                (re-search-forward "#\\+name: " end)
                (delete-region (point)
                               (line-end-position)))
            (goto-char beg)
            (insert "#+name: \n")
            (backward-char)))
      (error "Not in a source block"))))

(defun worf-mark ()
  "Mark the title of current heading."
  (interactive)
  (cond ((region-active-p)
         (deactivate-mark)
         (worf-backward))
        ((worf--special-p)
         (org-back-to-heading)
         (re-search-forward " ")
         (set-mark (point))
         (end-of-line))
        (t
         (setq this-command 'org-self-insert-command)
         (org-self-insert-command 1))))

(worf-defverb
 "change"
 '(("j" org-metadown)
   ("k" org-metaup)
   ("h" org-metaleft)
   ("l" org-metaright)
   ("t" org-set-tags :disable)
   ("n" worf-change-name :disable :break)
   ("a" org-meta-return :disable :break)))

(defhydra hydra-worf-change (:idle 1.0
                             :hint nil)
  "
^ ^ _w_ ^ ^    _t_ags    _p_rop    _r_: shiftcontrol
_h_ ^+^ _l_    _n_ame    _e_dit    _i_: shift
^ ^ _s_ ^ ^    _a_dd     ^ ^       _f_: shiftmeta (tree)"
  ;; arrows
  ("j" worf-down :exit t)
  ("k" worf-up :exit t)
  ("w" org-metaup)
  ("s" org-metadown)
  ("h" org-metaleft)
  ("l" org-metaright)
  ("e" move-end-of-line :exit t)
  ;; modes
  ("f" worf-change-tree-mode :exit t)
  ("i" worf-change-shift-mode :exit t)
  ("r" worf-change-shiftcontrol-mode :exit t)
  ;; misc
  ("p" org-set-property :exit t)
  ("t" org-set-tags :exit t)
  ("n" worf-change-name :exit t)
  ("a" org-meta-return :exit t)
  ("o" hydra-worf-keyword/body :exit t)
  ("m" worf-archive-and-commit :exit t)
  ("q" nil)
  ("c" nil))

(defhydra hydra-worf-f (:idle 1.0
                        :exit t)
  ("f" (setq prefix-arg 9999) "fast-forward")
  ("s" worf-schedule-today "schedule today"))

(defun worf-schedule-today (arg)
  (interactive "p")
  (org-schedule nil (format "%+d" (- arg 1))))

;; ——— Verbs: change tree ——————————————————————————————————————————————————————
(worf-defverb
 "change-tree"
 '(("j" org-shiftmetadown)
   ("k" org-shiftmetaup)
   ("h" org-shiftmetaleft)
   ("l" org-shiftmetaright)))

;; ——— Verbs: change shift —————————————————————————————————————————————————————
(worf-defverb
 "change-shift"
 '(("j" org-shiftdown)
   ("k" org-shiftup)
   ("h" org-shiftleft)
   ("l" org-shiftright)))

;; ——— Verbs: change shift control —————————————————————————————————————————————
(worf-defverb
 "change-shiftcontrol"
 '(("j" org-shiftcontroldown)
   ("k" org-shiftcontrolup)
   ("h" org-shiftcontrolleft)
   ("l" org-shiftcontrolright)))

;; ——— Verbs: clock ————————————————————————————————————————————————————————————
(worf-defverb
 "clock"
 '(("i" org-clock-in :disable)
   ("o" org-clock-out :disable)))

(defun worf-clock-in-from-end (end)
  "Clock into the current heading from BEG to END.
END is a time. BEG is END minus the amount of minutes entered."
  (let* ((diff (seconds-to-time
                (* 60 (string-to-number
                       (read-string "Minutes spent: ")))))
         (start-time (time-subtract end diff)))
    (org-clock-in nil start-time)
    (org-clock-out nil nil end)))

(defun worf-log-time (start-time end-time)
  "Insert clocking info from START-TIME to END-TIME into the current logbook."
  (save-excursion
    (org-back-to-heading)
    (goto-char (org-log-beginning))
    (if (looking-at ":LOGBOOK:")
        (beginning-of-line 2)
      (insert ":LOGBOOK:\n:END:\n")
      (beginning-of-line 0))
    (insert "CLOCK: ")
    (org-insert-time-stamp start-time 'with-hm 'inactive)
    (insert "--")
    (org-insert-time-stamp end-time 'with-hm 'inactive)
    (let* ((seconds (cadr (time-subtract end-time start-time)))
           (hours (floor (/ seconds 3600)))
           (minutes (/ (- seconds (* 3600 hours)) 60)))
      (insert (format " =>  %d:%d\n" hours minutes)))))

(defun worf-clock-in-and-out (arg)
  "Clock-in and out of a missed deadline.

The clock-in time is always the deadline's original time.

The clock-out time is the clock in time plus user-specified
number of minutes.

When ARG is 2, mark the deadline as DONE at the clock-out time.

When ARG is 3, the clock end time becomes the current time.

Works both in a buffer and in the agenda."
  (interactive "p")
  (save-window-excursion
    (when (eq major-mode 'org-agenda-mode)
      (let ((hdmarker (or (org-get-at-bol 'org-hd-marker)
                          (org-agenda-error))))
        (switch-to-buffer (marker-buffer hdmarker))
        (goto-char hdmarker)))
    (org-back-to-heading)
    (if (= arg 3)
        (worf-clock-in-from-end (current-time))
      (let* ((heading (org-element-at-point))
             (deadline (or (org-element-property :deadline heading)
                           (org-element-property :scheduled heading))))
        (if (null deadline)
            (if (setq deadline (org-element-property :closed heading))
                (worf-clock-in-from-end
                 (org-timestamp--to-internal-time deadline))
              (worf-clock-in-from-end (current-time)))
          (let* ((timestamp (org-element-property :raw-value deadline))
                 (parsed-timestamp (org-parse-time-string timestamp t))
                 (start-time (if (null (and (nth 1 parsed-timestamp)
                                            (nth 2 parsed-timestamp)))
                                 (apply #'encode-time (org-parse-time-string (org-read-date)))
                               (apply #'encode-time parsed-timestamp)))
                 (time-str (read-string "Minutes spent: "))
                 (diff (if (string= time-str "")
                           (time-subtract (current-time) start-time)
                         (seconds-to-time
                          (* 60 (string-to-number time-str)))))
                 (end-time (time-add start-time diff)))
            (worf-log-time start-time end-time)
            (org-add-planning-info 'closed end-time)))
        (when (eq arg 2)
          (let ((org-log-done nil))
            (org-todo 'done))
          (save-buffer)))))
  (when (eq major-mode 'org-agenda-mode)
    ;; `org-agenda-list' uses `current-prefix-arg', why...
    (setq current-prefix-arg nil)
    (org-agenda-redo t)))

;; ——— Verbs: delete ———————————————————————————————————————————————————————————
(defun worf-delete-k (arg)
  (interactive "p")
  (let ((pt (point)))
    (when (ignore-errors
            (org-speed-move-safe
             'outline-previous-visible-heading) t)
      (kill-region pt (point)))))

(defun worf-delete-w ()
  "Delete keyword from current heading."
  (interactive)
  (org-todo 'none)
  (org-back-to-heading))

(defun worf-delete-name ()
  "Delete #name of the current source block."
  (interactive)
  (let ((el (org-element-at-point)))
    (if (eq (org-element-type el) 'src-block)
        (let ((beg (org-element-property :begin el)))
          (if (org-element-property :name el)
              (let ((end (org-element-property :end el))
                    (case-fold-search t))
                (goto-char beg)
                (re-search-forward "#\\+name: " end)
                (delete-region (line-beginning-position)
                               (1+ (line-end-position))))
            (error "Source block already doesn't have a name")))
      (error "Not in a source block"))))

(defun worf-cut-subtree (arg)
  (interactive "p")
  (let (beg end)
    (org-back-to-heading t)
    (setq beg (point))
    (save-match-data
      (save-excursion
        (outline-end-of-heading))
      (ignore-errors
        (org-forward-heading-same-level
         (1- arg)
         t))
      (org-end-of-subtree t t))
    (setq end (min (point) (- (point-max) 2)))
    (skip-chars-backward "\n ")
    (delete-region (point) end)
    (setq end (point))
    (kill-region beg end)
    (backward-char 1)
    (org-back-to-heading t)
    (message
     "Cut: Subtree(s) with %d characters"
     (length (current-kill 0)))))

(worf-defverb
 "delete"
 '(("p" org-delete-property :disable)
   ("k" worf-delete-k :disable)
   ("j" worf-cut-subtree :disable)
   ("w" worf-delete-w :disable)
   ("n" worf-delete-name :disable)))

;; ——— Verbs: yank —————————————————————————————————————————————————————————————
(worf-defverb
 "yank"
 '(("j" org-copy-subtree :disable)))

;; ——— Verbs: mark —————————————————————————————————————————————————————————————
(defun worf-mark-down (arg)
  (interactive "p")
  (let ((bnd (worf--bounds-subtree)))
    (worf-down (- arg 1))
    (set-mark (cdr (worf--bounds-subtree)))
    (goto-char (car bnd))))

(defun worf-mark-left ()
  (interactive)
  (worf-left)
  (let ((bnd (worf--bounds-subtree)))
    (goto-char (car bnd))
    (set-mark (cdr bnd))))

(worf-defverb
 "mark"
 '(("j" worf-mark-down :disable)
   ("h" worf-mark-left :disable)))

;; ——— Verbs: keyword ——————————————————————————————————————————————————————————
(defvar worf-keyword-mode-map
  (make-sparse-keymap))

(defvar worf-keyword-mode-lighter "")

(defvar worf--keyword nil
  "Current `org-mode' keyword, i.e. one of \"TODO\", \"DONE\" etc.")

(defsubst worf-mod-keyword ()
  "Return current keyword."
  worf--keyword)

(define-minor-mode worf-keyword-mode
    "Minor mode that makes j/k to move by keywords."
  :keymap worf-keyword-mode-map
  :group 'worf
  :lighter worf-keyword-mode-lighter
  (cond (worf-keyword-mode
         (call-interactively 'worf-keyword))
        (t
         (setq worf--keyword nil))))

(defun worf-keyword (&optional keyword)
  "Set the current keyword.
All next `worf-down' and `worf-up' will move by this keyword.
When the chain is broken, the keyword is unset."
  (interactive)
  (setq keyword
        (or keyword
            (let* ((c (read-char "[t]odo, [d]one, [n]ext, [c]ancelled")))
              (message
               (cl-case c
                 (?t "TODO")
                 (?d "DONE")
                 (?n "NEXT")
                 (?c "CANCELLED"))))))
  (org-todo keyword))

(defhydra hydra-worf-keyword (:idle 1.5 :color teal)
  ("t" (org-todo "TODO") "TODO")
  ("d" (org-todo "DONE") "DONE")
  ("n" (org-todo "NEXT") "NEXT")
  ("c" (org-todo "CANCELLED") "CANCELLED"))

(defvar worf--keyword-no-invalidate-list
  '(wspecial-worf-keyword-mode
    worf-keyword
    wspecial-worf-up
    wspecial-worf-down
    wspecial-digit-argument))

(defun worf--invalidate-keyword ()
  (message "%s" this-command)
  (unless (memq this-command worf--keyword-no-invalidate-list)
    (worf-keyword-mode -1)
    (remove-hook 'post-command-hook 'worf--invalidate-keyword)))

(let ((map worf-keyword-mode-map))
  (worf-define-key map "w" 'worf-keyword))

(defun worf--set-change-switches (key mode)
  "Bind MODE to KEY for change modes."
  (mapc (lambda (map) (worf-define-key map key mode))
        (list worf-change-mode-map
              worf-change-tree-mode-map
              worf-change-shift-mode-map
              worf-change-shiftcontrol-mode-map)))

(worf--set-change-switches "c" 'worf-change-mode)
(worf--set-change-switches "f" 'worf-change-tree-mode)
(worf--set-change-switches "s" 'worf-change-shift-mode)
(worf--set-change-switches "r" 'worf-change-shiftcontrol-mode)

;; ——— Nouns: arrows ———————————————————————————————————————————————————————————
(defvar worf-recenter nil)
(defun worf-recenter-mode ()
  "Toggle centering on the current window line.

`worf-down' and `worf-up' are affected by this, and will
automatically recenter."
  (interactive)
  (if worf-recenter
      (progn
        (hl-line-mode -1)
        (setq worf-recenter nil))
    (hl-line-mode 1)
    (setq worf-recenter (- (line-number-at-pos)
                           (line-number-at-pos (window-start))))))

(defun worf-up (arg)
  "Move ARG headings up."
  (interactive "p")
  (cond ((worf-mod-keyword)
         (worf-dotimes-protect arg
           (worf--prev-keyword (worf-mod-keyword))))
        ((worf--at-property-p)
         (worf--prev-property arg))
        ((looking-at worf-sharp)
         (worf--sharp-up))
        (t
         (zo-up arg)
         (when worf-recenter
           (recenter worf-recenter)))))

(defun worf-down (arg)
  "Move ARG headings down."
  (interactive "p")
  (cond ((worf-mod-keyword)
         (worf-dotimes-protect arg
           (worf--next-keyword (worf-mod-keyword))))
        ((worf--at-property-p)
         (worf--next-property arg))
        ((looking-at worf-sharp)
         (worf--sharp-down))
        (t
         (let ((actual (zo-down arg)))
           (when (and (numberp actual) (< actual arg))
             (message "Reached end after %d headings" actual)))
         (when worf-recenter
           (recenter worf-recenter)))))

(defun worf-right ()
  "Move right."
  (interactive)
  (let ((pt (point))
        result)
    (save-restriction
      (org-narrow-to-subtree)
      (forward-char)
      (if (re-search-forward worf-regex nil t)
          (progn
            (goto-char (match-beginning 0))
            (setq result t))
        (goto-char pt)))
    (worf--ensure-visible)
    result))

(defun worf-left ()
  "Move one level up backwards."
  (interactive)
  (if (looking-at worf-sharp)
      (goto-char (car (worf--bounds-subtree)))
    (ignore-errors
      (org-up-heading-safe))))

;; ——— Nouns: property —————————————————————————————————————————————————————————
(defun worf-property ()
  "Operate on property."
  (interactive)
  (cl-destructuring-bind (beg . end)
      (worf--bounds-subtree)
    (let ((pt (car (org-get-property-block beg))))
      (if pt
          (progn
            (unless (bound-and-true-p reveal-mode)
              (goto-char beg)
              (org-show-subtree))
            (goto-char pt))
        (error "No properties. Use \"c p\" to add properties")))))

(defun worf-paste ()
  (interactive)
  (let ((bnd (worf--bounds-subtree)))
    (when bnd
      (goto-char (cdr bnd))
      (skip-chars-backward "\n")
      (forward-char 1)
      (save-excursion (yank)))))

(defun worf-occur ()
  (interactive)
  (let* ((bnd (worf--bounds-subtree))
         (candidates
          (save-restriction
            (narrow-to-region (car bnd) (cdr bnd))
            (swiper--init)
            (swiper--candidates))))
    (ivy-read "pattern: " candidates
              :require-match t
              :update-fn #'swiper--update-input-ivy
              :action #'swiper--action
              :unwind #'swiper--cleanup
              :caller 'worf-occur)))

;; ——— Nouns: new heading ——————————————————————————————————————————————————————
(require 'reveal)
(defun worf-add (arg)
  "Add a new heading below.
Positive ARG shifts the heading right.
Negative ARG shifts the heading left."
  (interactive "p")
  (let ((lvl (org-current-level))
        (spacing (max (abs
                       (save-excursion
                         (skip-chars-backward "\n")))
                      1)))
    (if (zo-down-visible)
        (progn
          (backward-char)
          (skip-chars-backward "\n")
          (insert "\n"))
      (outline-end-of-subtree)
      (skip-chars-backward "\n")
      (dotimes (i spacing)
        (insert "\n"))
      (reveal-post-command))
    (insert (concat (make-string lvl ?*) " "))
    (cond ((> arg 1)
           (worf-dotimes-protect (1- arg)
             (org-metaright)))
          ((cl-minusp arg)
           (worf-dotimes-protect (- arg)
             (org-metaleft))))
    (when worf-keyword-mode
      (insert (worf-mod-keyword) " ")
      (worf-keyword-mode -1))))

(defun worf-new-right (arg)
  (interactive "p")
  (org-insert-heading-respect-content)
  (worf-dotimes-protect arg
    (org-metaright)))

(defun worf-new-down ()
  (interactive)
  (end-of-line)
  (org-insert-heading-respect-content)
  (beginning-of-line))

(defhydra worf-new (:exit t)
  ("j" worf-new-down)
  ("k" org-insert-heading)
  ("h" org-metaleft)
  ("l" worf-new-right))

(defun worf-new-copy ()
  "Copy marked region to kill ring."
  (interactive)
  (if (region-active-p)
      (kill-new
       (buffer-substring-no-properties
        (region-beginning)
        (region-end)))))

;; ——— Other movement ——————————————————————————————————————————————————————————
(defun worf-backward ()
  "Go backwards to closest special position."
  (interactive)
  (re-search-backward worf-regex-full nil t)
  (while (worf--invisible-p)
    (worf-backward)))

(defun worf-forward ()
  "Go forwards to closest special position."
  (interactive)
  (forward-char 1)
  (re-search-forward worf-regex-full nil t)
  (beginning-of-line))

(defun worf-back-to-heading ()
  (interactive)
  (org-back-to-heading))

(defvar worf-beginning-of-line t)

(defun worf-beginning-of-line ()
  "Replaces `org-beginning-of-line'."
  (interactive)
  (beginning-of-line))

(defcustom worf-completion-method 'ivy
  "Method to select a candidate from a list of strings."
  :type '(choice
          (const :tag "Ivy" ivy)
          ;; sensible choice for many tags
          (const :tag "Helm" helm)))

(defun worf--goto-candidates ()
  (let ((extra (< (buffer-size) 100000))
        candidates)
    (org-map-entries
     (lambda ()
       (let ((comp (org-heading-components))
             (h (org-get-heading)))
         (push
          (cons (format "%d%s%s" (car comp)
                        (make-string (1+ (* 2 (1- (car comp)))) ?\ )
                        (if (get-text-property 0 'fontified h)
                            h
                          (worf--pretty-heading (nth 4 comp) (car comp))))
                (point))
          candidates)
         (when extra
           (save-restriction
             (narrow-to-region
              (progn (org-back-to-heading t) (point))
              (progn (worf-down 1) (point)))
             (save-excursion
               (goto-char (point-min))
               (while (re-search-forward "^#\\+name \\(.*\\)$" nil t)
                 (push (cons (propertize (match-string 1) 'face 'org-meta-line)
                             (line-beginning-position))
                       candidates))))))))
    (nreverse candidates)))

(defun worf-goto-action (x)
  (with-ivy-window
    (goto-char (cdr x))
    (outline-show-children 1000)
    (worf-more)))

(defun worf-goto ()
  "Jump to a heading with completion."
  (interactive)
  (let ((cands (worf--goto-candidates)))
    (cond ((eq worf-completion-method 'helm)
           (require 'helm-multi-match)
           (let (helm-update-blacklist-regexps
                 helm-candidate-number-limit)
             (helm :sources
                   `((name . "Headings")
                     (candidates . ,cands)
                     (action . worf-goto-action)
                     (pattern-transformer . worf--pattern-transformer)))))
          ((eq worf-completion-method 'ivy)
           (ivy-read "Heading: " cands
                     :action 'worf-goto-action)))))

(defun worf-meta-newline ()
  "Copy current markup block at newline.
Sometimes useful for #+LaTeX_HEADER."
  (interactive)
  (if (looking-back "^#\\+\\([^:]*:\\).*"
                    (line-beginning-position))
      (progn
        (end-of-line)
        (insert "\n#+" (match-string 1) " "))
    (indent-new-comment-line)))

;; ——— View ————————————————————————————————————————————————————————————————————
(defun worf-tab (arg)
  "Hide/show heading.

When ARG is 0, show the heading contents, no matter if the
heading fold state.

When ARG is 1, toggle between fully hidden state and a fully
visible state.

When ARG isn't 0 or 1, show full file contents for that level,
i.e. `org-shifttab'.

When at a #+ marker, forward to `org-cycle'."
  (interactive "p")
  (let ((v (this-command-keys-vector))
        (bnd (worf--end-positions)))
    (when (let ((case-fold-search t))
            (looking-at "#\\+end"))
      (worf--sharp-up))
    (cond
      ((eq (car (org-element-at-point)) 'clock)
       (org-clock-update-time-maybe))
      ((looking-at "#\\+")
       (org-cycle))
      ((looking-at "^:")
       (org-cycle))
      ((= arg 0)
       (outline-flag-region (car bnd) (cdr bnd) t)
       (org-cycle-internal-local))
      ((and (= 2 (length v))
            (string-match "[0-9]" (concat v)))
       (org-shifttab arg))
      (t
       (let ((eoh (car bnd))
             (eos (cdr bnd)))
         (if (and (eq (get-char-property (1- eos) 'invisible) 'outline)
                  (eq (get-char-property (1+ eoh) 'invisible) 'outline))
             (outline-flag-region eoh eos nil)
           (outline-flag-region eoh eos t)))))))

(defun worf-tab-contents ()
  "Show only the names of the heading's children."
  (interactive)
  (worf-tab 0))

(defun worf--end-positions ()
  "Return a cons of heading end and subtree end."
  (save-excursion
    (org-back-to-heading)
    (cons
     (save-excursion (outline-end-of-heading) (point))
     (save-excursion (org-end-of-subtree t t)
                     (when (bolp) (backward-char)) (point)))))

(defhydra hydra-org-tab (:color blue
                         :hint nil)
  "
_g_lobal cycle    _b_ranches
_a_ll             _c_hildren
_s_tartup
"
  ("s" (org-global-cycle '(4)))
  ("g" org-global-cycle :exit nil)
  ("a" outline-show-all)
  ("b" outline-show-branches)
  ("c" outline-show-children))

(defun worf-hydratab ()
  (interactive)
  (if (worf--special-p)
      (hydra-org-tab/body)
    (call-interactively 'org-cycle)))

(defun worf-shifttab (arg)
  "Hide/show everything.
Forward to `org-shifttab' with ARG."
  (interactive "P")
  (if arg
      (org-content)
    (when (eq org-cycle-global-status 'overview)
      (setq org-cycle-global-status 'contents))
    (setq this-command last-command)
    (org-cycle-internal-global)))

(defun worf-more ()
  "Unhide current heading."
  (interactive)
  (org-show-subtree)
  (org-cycle-hide-drawers 'all)
  (recenter))

(defun worf-view ()
  "Recenter current heading to the first screen line.
If already there, return it to previous position."
  (interactive)
  (defvar worf-view-line 0)
  (let ((window-line (count-lines (window-start) (point))))
    (if (or (= window-line 0)
            (and (not (bolp)) (= window-line 1)))
        (recenter worf-view-line)
      (setq worf-view-line window-line)
      (recenter 0))))

;; ——— Links ———————————————————————————————————————————————————————————————————
(defun worf-follow ()
  "Follow the link at point."
  (interactive)
  (condition-case nil
      (progn
        (push-mark)
        (org-open-at-point)
        (worf-more))
    (error (newline-and-indent))))

(defun worf-ace-link ()
  "Visit a link within current heading by ace jumping."
  (interactive)
  (let ((cands (save-excursion
                 (save-restriction
                   (org-narrow-to-subtree)
                   (ace-link--org-collect)))))
    (let ((pt (avy-with ace-link-org
                (avy--process
                 (mapcar
                  #'cdr
                  cands)
                 #'avy--overlay-pre))))
      (ace-link--org-action pt))))

(defun worf-ace-link-eww ()
  "Visit a link within current heading by ace jumping."
  (interactive)
  (let ((browse-url-browser-function 'eww-browse-url))
    (worf-ace-link)))

;; ——— Files ———————————————————————————————————————————————————————————————————
(defun worf-attach ()
  "Interface to attachments."
  (interactive)
  (call-interactively 'org-attach)
  (org-align-all-tags))

(defun worf-attach-visit ()
  "Interface to attachments."
  (interactive)
  (call-interactively 'org-attach-open))

(defvar worf-visit-function 'find-file
  "Function to call when visiting a file.
For example, the user might prefer to visit pdf or mp4 with
external applications.")

(defun worf-visit (arg)
  "Forward to find file in project with ARG."
  (interactive "p")
  (let (attach-dir)
    (cond ((setq attach-dir (org-attach-dir))
           (let* ((files (org-attach-file-list attach-dir))
                  (file (if (= (length files) 1)
                            (car files)
                          (completing-read "Open attachment: "
                                           (mapcar #'list files) nil t)))
                  (file (expand-file-name file attach-dir)))
             (funcall worf-visit-function file)))
          ((= arg 1)
           (projectile-find-file nil))
          ((= arg 2)
           (projectile-find-file-other-window))
          (t
           (projectile-find-file arg)))))

(defun worf-save ()
  "Save buffer."
  (interactive)
  (save-buffer))

;; ——— Refile ——————————————————————————————————————————————————————————————————
(defun worf-refile-targets (maxlevel)
  (cons (cons (cl-set-difference
               (delq nil
                     (mapcar
                      (lambda (b)
                        (let ((name (buffer-file-name b)))
                          (and name
                               (string-match "org$" (buffer-file-name b))
                               name)))
                      (buffer-list)))
               org-agenda-files
               :test 'equal)
              (cons :maxlevel maxlevel))
        (cl-remove-if
         (lambda (x) (null (car x)))
         org-refile-targets)))

(defun worf-refile-other (arg)
  "Refile the current heading to another heading.

The other heading can be in another file.  All currently open Org
files are eligible for refiling, even if they aren't on
`org-refile-targets'.

When the heading has attachments and the target is in another
directory, the attachments will be moved."
  (interactive "p")
  (let* ((id (org-entry-properties nil "ID"))
         (dir1 default-directory)
         (adir1 (and id (org-attach-dir)))
         (org-refile-targets (worf-refile-targets (+ arg 2))))
    (org-refile)
    (save-buffer)
    (save-window-excursion
      (org-refile-goto-last-stored)
      (save-buffer)
      (when (and adir1 (not (equal default-directory dir1)))
        (rename-file adir1
                     (file-name-directory
                      (org-attach-dir t)) t)
        (when (equal (directory-files (file-name-directory adir1)) '("." ".."))
          (dired-delete-file (file-name-directory adir1)))))
    (when (bound-and-true-p org-capture-mode)
      (org-capture-kill))))

(defun worf-refile-this (arg)
  "Interface to refile with :maxlevel set to ARG."
  (interactive "p")
  (when (= arg 1)
    (setq arg 5))
  (let ((org-refile-targets `((nil :maxlevel . ,arg))))
    (call-interactively 'org-refile))
  (save-buffer))

(defun worf-refile-other-window ()
  (interactive)
  (let* ((fname (save-window-excursion
                  (other-window 1)
                  (buffer-file-name)))
         (org-agenda-files nil)
         (org-refile-targets `(((,fname) :maxlevel . 3))))
    (call-interactively 'org-refile)))

(defun worf-refile-last ()
  "Refile to the last location without prompting."
  (interactive)
  (let ((completing-read-function
         (lambda (_p coll _pred _rm _ii _h default &rest _)
           default)))
    (worf-refile-other 1)))

(defhydra hydra-worf-promote (:color teal)
  "meta"
  ("p" org-pomodoro "pomodoro")
  ("q" nil "quit"))

(defun worf-x ()
  "A prefix for other commands."
  (interactive)
  (hydra-worf-promote/body))

(defhydra hydra-refile (:hint nil
                        :color teal)
  "
Refile:^^   _k_eep: %`org-refile-keep
----------------------------------
_l_ast      _a_rchive
_o_ther
_t_his

"
  ("t" worf-refile-this)
  ("w" worf-refile-other-window)
  ("o" worf-refile-other)
  ("l" worf-refile-last)
  ("k" (setq org-refile-keep (not org-refile-keep))
       :exit nil)
  ("a" (org-archive-subtree))
  ("q" nil "quit"))

(defhydra hydra-worf-cj (:color teal)
  "C-j"
  ("j" (org-open-at-point) "open")
  ("n" (worf-add 1) "same")
  ("m" (worf-add 2) "more")
  ("l" (worf-add -1) "less"))

;; ——— Misc ————————————————————————————————————————————————————————————————————
(defun worf-delete-subtree (arg)
  "Delete subtree or ARG chars."
  (interactive "p")
  (if (and (looking-at "\\*")
           (looking-back "^\\**" (line-beginning-position)))
      (org-cut-subtree)
    (delete-char arg)))

(defun worf-copy-heading-id (arg)
  "Copy the id link of current heading to kill ring.
When ARG is true, add a CUSTOM_ID first."
  (interactive "P")
  (let ((heading (substring-no-properties
                  (org-get-heading)))
        id)
    (when (string-match "\\`\\(.*?\\) +:.*:\\'" heading)
      (setq heading (match-string-no-properties 1 heading)))
    (when arg
      (org-entry-put nil "CUSTOM_ID"
                     (replace-regexp-in-string
                      "[=?]" ""
                      (replace-regexp-in-string
                       "," ""
                       (replace-regexp-in-string
                        " +" "-"
                        (downcase heading))))))
    (if (setq id (org-entry-get nil "CUSTOM_ID"))
        (kill-new (format "[[#%s][%s]]" id heading))
      (setq id (org-id-get nil 'create))
      (kill-new (format "[[id:%s][%s]]" id heading)))))

(defun worf-quit ()
  "Remove modifiers."
  (interactive)
  (mapc (lambda (x) (funcall x -1)) worf-known-verbs))

(defun worf-todo (arg)
  "Forward to `org-todo' with ARG."
  (interactive "P")
  (let* ((marker (or (org-get-at-bol 'org-marker) (point)))
         (buffer (if (eq major-mode 'org-agenda-mode)
                     (marker-buffer marker)
                   (current-buffer))))
    (with-current-buffer buffer
      (save-excursion
        (goto-char marker)
        (let* ((all-keywords (append (cl-remove-if-not
                                      (lambda (x)
                                        (stringp (car x)))
                                      org-todo-key-alist)
                                     (list (cons "CLEAR" ?k))))
               (done-keywords org-done-keywords)
               (hint (mapconcat (lambda (x)
                                  (format "[%c] %s" (cdr x) (car x)))
                                all-keywords
                                " "))
               (key (read-char hint))
               (keyword-cons (rassoc key all-keywords))
               (keyword (car keyword-cons)))
          (when keyword
            (if (string= keyword "CLEAR")
                (org-todo 'none)
              (when (string= keyword "DONE")
                (save-excursion
                  (org-back-to-heading)
                  (when (looking-at ".*?\\([0-9]+\\) *:recurring:$")
                    (let ((idx (string-to-number (match-string 1))))
                      (replace-match (prin1-to-string (1+ idx))
                                     nil t nil 1)))))
              (org-todo keyword))))))
    (when (eq major-mode 'org-agenda-mode)
      (org-agenda-redo t))))

(defun worf-reserved ()
  "Do some cybersquatting."
  (interactive)
  (message "Nothing here, move along."))

;; ——— Predicates ——————————————————————————————————————————————————————————————
(defun worf--at-property-p ()
  "Return t if point is at property."
  (looking-at "^:"))

(defun worf--special-p ()
  "Return t if point is special.
When point is special, alphanumeric keys call commands instead of
calling `self-insert-command'."
  (or (region-active-p)
      (looking-at worf-regex)
      (worf--at-property-p)
      (looking-back "^\\*+" (line-beginning-position))
      (and (bolp) (looking-at "CLOCK:"))))

(defun worf--invisible-p ()
  "Test if point is hidden by an `org-block' overlay."
  (cl-some (lambda (ov) (memq (overlay-get ov 'invisible)
                              '(org-hide-block outline)))
           (overlays-at (point))))

(defun worf--ensure-visible ()
  "Remove overlays hiding point."
  (let ((overlays (overlays-at (point)))
        ov expose)
    (while (setq ov (pop overlays))
      (if (and (invisible-p (overlay-get ov 'invisible))
               (setq expose (overlay-get ov 'isearch-open-invisible)))
          (funcall expose ov)))))

(defun worf-delete-backward-char (arg)
  (interactive "p")
  (if (region-active-p)
      (delete-active-region)
    (let (ov expose)
      (if (and (eolp)
               (setq ov (car (overlays-at (1- (point)))))
               (invisible-p (overlay-get ov 'invisible)))
          (progn
            (goto-char (1- (overlay-end ov)))
            (when (and (invisible-p (overlay-get ov 'invisible))
                       (setq expose (overlay-get ov 'isearch-open-invisible)))
              (funcall expose ov)
              (forward-char 1)))
        (org-delete-backward-char arg)))))

;; ——— Pure ————————————————————————————————————————————————————————————————————
(defun worf--bounds-subtree ()
  "Return bounds of the current subtree as a cons."
  (save-excursion
    (save-match-data
      (condition-case e
          (cons
           (progn
             (org-back-to-heading t)
             (point))
           (progn
             (org-end-of-subtree t t)
             (when (and (org-at-heading-p)
                        (not (eobp)))
               (backward-char 1))
             (point)))
        (error
         (if (string-match
              "^Before first headline"
              (error-message-string e))
             (cons (point-min)
                   (or (ignore-errors
                         (org-speed-move-safe 'outline-next-visible-heading)
                         (point))
                       (point-max)))
           (signal (car e) (cdr e))))))))

;; ——— Utilities ———————————————————————————————————————————————————————————————
(defun worf--next-property (arg)
  "Move to the next property line."
  (interactive "p")
  (let ((bnd (worf--bounds-subtree))
        (pt (point))
        (success nil))
    (forward-char 1)
    (while (and (null success)
                (< (point) (cdr bnd))
                (re-search-forward "^:" (cdr bnd) t arg))
      (backward-char 1)
      (if (worf--invisible-p)
          (forward-char 1)
        (setq success t)))
    (unless success
      (goto-char pt))))

(defun worf--prev-property (arg)
  "Move to the previous property line."
  (interactive "p")
  (let ((bnd (worf--bounds-subtree)))
    (while (and (> (point) (car bnd))
                (re-search-backward "^:" (car bnd) t arg)
                (worf--invisible-p)))
    ;; (org-speed-move-safe 'outline-previous-visible-heading)
    ))

(defun worf--pattern-transformer (x)
  "Transform X to make 1-9 select the heading level in `worf-goto'."
  (if (string-match "^[1-9]" x)
      (setq x (format "^%s" x))
    x))

(defun worf--sharp-down ()
  "Move down to the next #+."
  (let ((pt (point))
        (bnd (worf--bounds-subtree)))
    (forward-char)
    (while (and (re-search-forward worf-sharp (cdr bnd) t)
                (worf--invisible-p)))
    (cond ((worf--invisible-p)
           (goto-char pt))
          ((looking-back worf-sharp (line-beginning-position))
           (goto-char (match-beginning 0)))
          (t
           (if (= (car bnd) (point-min))
               (ignore-errors
                 (org-speed-move-safe 'outline-next-visible-heading))
             (goto-char pt))))))

(defun worf--sharp-up ()
  "Move up to the next #+."
  (let ((pt (point)))
    (while (and (re-search-backward worf-sharp (car (worf--bounds-subtree)) t)
                (worf--invisible-p)))
    (cond ((worf--invisible-p)
           (prog1 nil
             (goto-char pt)))
          ((= pt (point))
           nil)
          (t
           (goto-char
            (match-beginning 0))))))

(defun worf--pretty-heading (str lvl)
  "Prettify heading STR or level LVL."
  (setq str (or str ""))
  (setq str (propertize str 'face (nth (1- lvl) org-level-faces)))
  (let (desc)
    (while (and (string-match org-bracket-link-regexp str)
                (stringp (setq desc (match-string 3 str))))
      (setq str (replace-match
                 (propertize desc 'face 'org-link)
                 nil nil str)))
    str))

(defun worf--prev-keyword (str)
  "Move to the prev keyword STR within current file."
  (reveal-mode 1)
  (let ((pt (point)))
    (unless (catch 'break
              (while t
                (outline-previous-heading)
                (when (and (string= str (nth 2 (org-heading-components)))
                           (looking-at "^\\*"))
                  (throw 'break t))
                (when (= (point) (point-min))
                  (throw 'break nil))))
      (goto-char pt))))

(defun worf--next-keyword (str)
  "Move to the next keyword STR within current file."
  (reveal-mode 1)
  (let ((pt (point)))
    (unless (catch 'break
              (while t
                (outline-next-heading)
                (when (= (point) (point-max))
                  (throw 'break nil))
                (when (string= str (nth 2 (org-heading-components)))
                  (throw 'break t))))
      (goto-char pt))))

(defun worf-set-added ()
  (interactive)
  (org-set-property "ADDED" (format-time-string "[%Y-%m-%d %a]")))

(defun worf-symbolize (arg)
  "Quote all occurences of symbol at point with =.*=."
  (interactive "p")
  (if (eq arg 4)
      (let* ((bnd (bounds-of-thing-at-point 'symbol))
             (str (buffer-substring-no-properties (car bnd) (cdr bnd)))
             (re (format "[^=]\\(\\_<%s\\_>\\)[^=]" str))
             (cnt 0))
        (undo-boundary)
        (save-excursion
          (goto-char (point-min))
          (while (re-search-forward re nil t)
            (replace-match (format "=%s=" str) nil t nil 1)
            (cl-incf cnt))
          (message "quoted %d symbol%s" cnt (if (> cnt 1) "s" ""))))
    (self-insert-command arg)))

(let ((map worf-mode-map))
  ;; ——— Global ———————————————————————————————
  (define-key map "[" 'worf-backward)
  (define-key map "]" 'worf-forward)
  (define-key map "=" 'worf-symbolize)
  (define-key map (kbd "M-j") 'worf-meta-newline)
  (define-key map "\C-j" 'hydra-worf-cj/body)
  (define-key map (kbd "C-M-g") 'worf-goto)
  (define-key map (kbd "C-d") 'worf-delete-subtree)
  (define-key map (kbd "DEL") 'worf-delete-backward-char)
  (define-key map (kbd "C-a") 'worf-beginning-of-line)
  (define-key map (kbd "<tab>") nil)
  (define-key map (kbd "<S-iso-lefttab>") 'worf-shifttab)
  ;; ——— Local ————————————————————————————————
  (mapc (lambda (k) (worf-define-key map k 'worf-reserved))
        '("b" "B" "C" "D" "e" "E" "f" "G" "H" "M" "n" "P" "Q"
          "S" "U" "w" "x" "X" "Y" "z" "Z"))
  ;; ——— navigation/arrows ————————————————————
  (worf-define-key map "j" 'worf-down)
  (worf-define-key map "k" 'worf-up)
  (worf-define-key map "h" 'worf-left)
  (worf-define-key map "l" 'worf-right)
  (worf-define-key map "f" 'hydra-worf-f/body)
  (worf-define-key map "J" 'outline-next-visible-heading)
  (worf-define-key map "K" 'outline-previous-visible-heading)
  ;; ——— navigation/unstructured ——————————————
  (worf-define-key map "g" 'worf-goto)
  (worf-define-key map "o" 'worf-ace-link)
  (worf-define-key map "O" 'worf-ace-link-eww)
  ;; ——— hide/show ————————————————————————————
  (worf-define-key map "i" 'worf-tab)
  (worf-define-key map "/" 'worf-tab-contents)
  (worf-define-key map "I" 'worf-shifttab)
  ;; (worf-define-key map "m" 'worf-more)

  (worf-define-key map "v" 'worf-view)
  ;; ——— files ————————————————————————————————
  (worf-define-key map "F" 'worf-attach-visit)
  (worf-define-key map "A" 'worf-attach)
  (worf-define-key map "V" 'worf-visit)
  ;; ——— refile ———————————————————————————————
  (worf-define-key map "r" 'hydra-refile/body)
  ;; ——— misc —————————————————————————————————
  (worf-define-key map "x" 'hydra-worf-promote/body)
  (worf-define-key map "L" 'worf-copy-heading-id)
  (worf-define-key map "a" 'worf-add :break t)
  (worf-define-key map "e" 'move-end-of-line :break t)
  (worf-define-key map "s" 'worf-save)
  ;; ——— narrow/widen —————————————————————————
  (worf-define-key map "N" 'org-narrow-to-subtree)
  (worf-define-key map "W" 'widen)
  ;; ——— verbs ————————————————————————————————
  (worf-define-key map "c" 'hydra-worf-change/body)
  (worf-define-key map "d" 'worf-delete-mode)
  (worf-define-key map "y" 'worf-occur :break t)
  (worf-define-key map "C" 'worf-clock-mode)
  (worf-define-key map "T" 'worf-clock-in-and-out)
  (worf-define-key map "w" 'worf-keyword)
  (define-key map "m" 'worf-mark)
  (worf-define-key map "q" 'worf-quit)
  (worf-define-key map "n" 'worf-new-copy)
  ;; ——— nouns ————————————————————————————————
  (worf-define-key map "p" 'worf-property)
  (worf-define-key map "P" 'worf-paste)
  ;; ——— misc —————————————————————————————————
  (worf-define-key map "t" 'worf-todo)
  (worf-define-key map "u" 'undo)
  (worf-define-key map "R" 'worf-recenter-mode)
  ;; ——— digit argument ———————————————————————
  (mapc (lambda (x) (worf-define-key map (format "%d" x) 'digit-argument))
        (number-sequence 0 9))
  (worf-define-key map "-" 'negative-argument))

(defconst worf-fl-summary
  '(("\\(^\\(#\\+caption: [^\n]*\n\\)?\\(#\\+attr_latex: [^\n]*\n\\)?\\(#\\+label: [^\n]*\\)?\\)\n"
     (0
      (progn
        (put-text-property
         (match-beginning 1)
         (match-end 1) 'display
         (concat (worf--squashed-string)))
        nil)))))

(defun worf--summary-on ()
  (interactive)
  (save-buffer)
  (font-lock-add-keywords
   'org-mode
   worf-fl-summary)
  (revert-buffer nil t))

(defun worf--summary-off ()
  (interactive)
  (font-lock-remove-keywords
   'org-mode
   worf-fl-summary)
  (save-buffer)
  (let ((file-name (buffer-file-name)))
    (kill-buffer (current-buffer))
    (find-file file-name)))

(defun worf--org-attribute (str)
  (save-match-data
   (if (string-match "^#\\+[^:]*: \\(.*\\)$" str)
       (match-string 1 str)
     (error "Bad attribute: %s" str))))

(defun worf--squashed-string ()
  (let ((strs (split-string
               (match-string-no-properties 1)
               "\n" t)))
    (propertize
     (mapconcat 'worf--org-attribute strs " / ")
     'face
     'org-meta-line)))

(declare-function org-get-local-archive-location "org-archive")
(declare-function org-extract-archive-file "org-archive")

;;;###autoload
(defun worf-archive ()
  (interactive)
  (require 'org-datetree)
  (require 'org-archive)
  (if (not (org-entry-is-done-p))
      (user-error "not done")
    (let* ((time (org-time-string-to-time
                  (cdar (org-entry-properties nil "CLOSED"))))
           (dct (decode-time time))
           (y (nth 5 dct))
           (m (nth 4 dct))
           (d (nth 3 dct))
           (this-buffer (current-buffer))
           (location (org-get-local-archive-location))
           (afile (org-extract-archive-file location))
           (org-archive-location
            (format "%s::%s %04d-%02d-%02d %s" afile
                    (make-string (org-get-valid-level 0 2) ?*) y m d
                    (format-time-string "%A" (encode-time 0 0 0 d m y))))
           (id (org-attach-dir)))
      (when id
        (let ((new-location
               (file-name-directory
                (expand-file-name
                 (file-relative-name id)
                 (file-name-directory afile))))
              (id-parent (file-name-directory id)))
          (make-directory new-location t)
          (rename-file id new-location)
          (when (equal (directory-files id-parent)
                       '("." ".."))
            (delete-directory id-parent))))
      (org-set-tags-to (org-get-tags-at))
      (if (null afile)
          (error "Invalid `org-archive-location'")
        (org-cut-subtree)
        (save-buffer)
        (with-current-buffer (find-file-noselect afile)
          (goto-char (point-min))
          (unless (re-search-forward (format "^\\* %d" y) nil t)
            (goto-char (point-max))
            (insert (format "\n* %d" y)))
          (save-restriction
            (org-narrow-to-subtree)
            (goto-char (point-min))
            (let ((cm m))
              (while (and (> cm 0)
                          (not (re-search-forward
                                (format "^\\*\\* %d-%02d" y cm)
                                nil t)))
                (cl-decf cm))
              (unless (= cm m)
                (if (= cm 0)
                    (end-of-line)
                  (outline-end-of-subtree))
                (insert (format "\n** %d-%02d %s"
                                y m
                                (format-time-string "%B" time)))))
            (org-narrow-to-subtree)
            (let ((cd d)
                  (re-fmt (format "^\\*\\*\\* %d-%02d-%%02d" y m)))
              (while (and (> cd 0)
                          (not (re-search-forward (format re-fmt cd) nil t)))
                (cl-decf cd))
              (if (= cd d)
                  (progn
                    (org-narrow-to-subtree)
                    (goto-char (point-max)))
                (if (= (org-outline-level) 2)
                    (end-of-line)
                  (org-narrow-to-subtree)
                  (goto-char (point-max)))
                (insert (format "\n*** %d-%02d-%02d %s"
                                y m d
                                (format-time-string "%A" time)))))
            (unless (bolp)
              (insert "\n"))
            (org-paste-subtree 4)
            (save-excursion
              (goto-char (point-max))
              (while (eq (char-before) ?\n)
                (delete-char -1))))
          (save-buffer))))))

;;;###autoload
(defun worf-archive-and-commit ()
  (interactive)
  (let ((cmd (format "git add -u . && git commit -m \"%s: archive\""
                     (file-name-nondirectory (buffer-file-name)))))
    (worf-archive)
    (shell-command cmd)))

(defun worf-fixup-whitespace ()
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\\( +\\)CLOSED:" nil t)
      (delete-region (match-beginning 1)
                     (match-end 1)))
    (save-buffer)))

;;* Agenda commands
(defun worf-schedule ()
  (interactive)
  (if (null current-prefix-arg)
      (call-interactively 'org-agenda-schedule)
    (org-agenda-schedule 0 (format "+%dd" current-prefix-arg))))

(defvar worf-agenda-files nil
  "List of agenda groups.

Each item is (DESCRIPTION AGENDA-FILES).
DESCRIPTION is a string offered for completion.
AGENDA-FILES is a list of files.")

(defun worf-agenda-narrow-action (context)
  (setq org-agenda-files (cadr context))
  (org-agenda-redo))

(defun worf-agenda-narrow ()
  (interactive)
  (ivy-read "agenda context:" worf-agenda-files
            :action #'worf-agenda-narrow-action))

(defun worf-agenda-widen ()
  (interactive)
  (setq org-agenda-files
        (cl-remove-if-not
         #'file-exists-p
         (delete-dups
          (apply #'append (mapcar #'cadr worf-agenda-files)))))
  (org-agenda-redo))

(provide 'worf)

;;; Local Variables:
;;; outline-regexp: ";; ———"
;;; End:

;;; worf.el ends here
