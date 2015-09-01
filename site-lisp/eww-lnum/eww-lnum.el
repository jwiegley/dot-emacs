;;; eww-lnum.el --- Conkeror-like functionality for eww  -*- lexical-binding: t -*-

;; Copyright (C) 2014-2015 Andrey Kotlarski <m00naticus@gmail.com>

;; Version: 1.2
;; Keywords: eww, browse, conkeror
;; Author: Andrey Kotlarski <m00naticus@gmail.com>
;; URL: https://github.com/m00natic/eww-lnum
;; Package-Requires ((emacs "24.4"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This package extends the EWW browser with Conkeror style operations:
;; `eww-lnum-follow' for visiting links, form fields or pushing buttons;
;; `eww-lnum-universal' for selecting element and then providing
;; relevant options.

;;; Usage:

;; Example setup:
;; (eval-after-load "eww"
;;   '(progn (define-key eww-mode-map "f" 'eww-lnum-follow)
;;           (define-key eww-mode-map "F" 'eww-lnum-universal)))

;;; Code:

(require 'eww)

(defface eww-lnum-number
  '((((class color grayscale) (min-colors 88) (background light))
     :foreground "grey50")
    (((class color grayscale) (min-colors 88) (background dark))
     :foreground "grey70")
    (((class color) (min-colors 8) (background light))
     :foreground "green")
    (((class color) (min-colors 8) (background dark))
     :foreground "yellow"))
  "Face used for item numbers."
  :group 'eww)

(defcustom eww-lnum-quick-browsing 'quick-numbers
  "If non-nil, do aggressive selection.  Possible values are:
`quick-numbers' quick selection only when entering numbers
`quick-filter' ditto only when filtering
`quick-all' always quick selecting"
  :group 'eww :type '(radio (const :format "%v " nil)
                            (const :format "%v " quick-numbers)
                            (const :format "%v " quick-filter)
                            (const :format "%v" quick-all)))

(defcustom eww-lnum-context-alist
  '(("news.ycombinator.com" . 2) ("reddit.com" . 1))
  "Alist specifying number of additional items to be numbered after \
filtering for particular url."
  :group 'eww :type 'alist)

(defvar eww-lnum-actions-custom-type
  '(repeat (choice :format "%[Value Menu%] %v"
                   (string :tag "Information line")
                   (group :tag "Keycode and Action" :indent 2
                          (character :tag "Key")
                          function
                          (string :tag "Prompt")))))

(defcustom eww-lnum-actions-general
  '("----  Default   ----"
    (?g (lambda (info) (push-mark (point))
          (goto-char (cadr info))) "Move to"))
  "Alist specifying keycodes and available actions over selected anchor."
  :group 'eww :type eww-lnum-actions-custom-type)

(defcustom eww-lnum-actions-link-alist
  '("----  Link   ----"
    (?f eww-lnum-visit "Visit")
    (?e (lambda (info) (eww-lnum-visit info nil t)) "Edit URL and visit")
    (?F (lambda (info) (eww-lnum-visit info t)) "Visit in new buffer")
    (?E (lambda (info) (eww-lnum-visit info t t))
        "Edit URL and visit in new buffer")
    (?b (lambda (info) (eww-lnum-visit info :background)) "Open in background")
    (?B (lambda (info) (eww-lnum-visit info :background t))
        "Edit URL and open in background")
    (?d (lambda (info) (save-excursion
                    (goto-char (cadr info))
                    (eww-download))) "Download")
    (?w (lambda (info) (let ((url (car info)))
                    (kill-new url)
                    (message url)))
        "Copy")
    (?& (lambda (info) (eww-browse-with-external-browser (car info)))
        "Open in external browser"))
  "Alist specifying keycodes and available actions over a selected link."
  :group 'eww :type eww-lnum-actions-custom-type)

(defcustom eww-lnum-actions-button-alist
  '("---- Button  ----"
    (?p eww-lnum-activate-form "Push"))
  "Alist specifying keycodes and available actions over a selected button."
  :group 'eww :type eww-lnum-actions-custom-type)

(defun eww-lnum-current-url ()
  "Get current page url."
  (if (boundp 'eww-current-url)
      eww-current-url
    (plist-get eww-data :url)))

(defun eww-lnum-remove-overlays (&optional start end)
  "Remove numbering and match overlays between START and END points.
If missing, clear the current visible window."
  (let* ((start-pos (window-start))
         (window-size (- (window-end) start-pos))
         (start (or start (max (- start-pos window-size)
                               (point-min))))
         (end (or end (min (+ start-pos (* 2 window-size))
                           (point-max)))))
    (dolist (overlay (overlays-in start end))
      (if (or (overlay-get overlay 'eww-lnum-overlay)
              (overlay-get overlay 'eww-lnum-match))
          (delete-overlay overlay)))))

(defmacro eww-lnum-set-overlay (pos index)
  "Set numbering overlay at POS with INDEX."
  `(let ((overlay (make-overlay ,pos (1+ ,pos))))
     (let ((num (format "[%d]" (setq ,index (1+ ,index)))))
       (overlay-put overlay 'before-string num)
       (add-text-properties 0 (length num) '(face eww-lnum-number) num)
       (overlay-put overlay 'evaporate t))
     (overlay-put overlay 'eww-lnum-overlay ,index)))

(defun eww-lnum-replace-regexps-in-string (string &rest regexps)
  "In STRING replace an alist of REGEXPS."
  (if (cadr regexps)
      (replace-regexp-in-string
       (car regexps) (cadr regexps)
       (apply #'eww-lnum-replace-regexps-in-string string (cddr regexps)))
    string))

(defun eww-lnum-set-numbering (next-func &optional reg dont-clear-p)
  "Make overlays that display link numbers.  Return last used index.
NEXT-FUNC is function to iterate numbered elements.
REG is filter string for anchor text.
DONT-CLEAR-P determines whether previous numbering has to be cleared."
  (setq reg
        (if reg
            (eww-lnum-replace-regexps-in-string ; escape special characters
             reg "\\?" "\\\\?" "\\!" "\\\\!" "\\[" "\\\\["
             "\\*" "\\\\*" "\\+" "\\\\+" "\\." "\\\\." "\\^" "\\\\^"
             "\\$" "\\\\$")
          ""))
  (or dont-clear-p
      (eww-lnum-remove-overlays))
  (let ((pos (max (1- (window-start)) (point-min)))
        (pmax (min (window-end) (point-max)))
        (index 0)
        (context (or (assoc-default (eww-lnum-current-url)
                                    eww-lnum-context-alist
                                    'string-match-p)
                     0)))
    (while (and pos (setq pos (funcall next-func pos))
                (< pos pmax))
      (when (string-match-p reg (buffer-substring-no-properties
                                 pos (or (next-single-property-change
                                          pos 'help-echo)
                                         (point-max))))
        (eww-lnum-set-overlay pos index)
        (let ((counter context))
          (while (and (>= (setq counter (1- counter)) 0)
                      (setq pos (funcall next-func pos))
                      (< pos pmax))
            (eww-lnum-set-overlay pos index)))))
    index))

(defun eww-lnum-next (&optional pos)
  "Return position of next element to be numbered starting at POS.
If POS is not given, start from current point."
  (or pos (setq pos (point)))
  (if (get-char-property pos 'help-echo) ; currently over such element
      (setq pos (next-single-property-change pos 'help-echo)))
  (if (and pos
           (or (get-char-property pos 'help-echo)
               (setq pos (next-single-property-change pos 'help-echo))))
      pos
    (point-max)))

(defun eww-lnum-next-filter (next-func filter pmin pmax)
  "Search next element according to NEXT-FUNC and FILTER.
Do this in region between points PMIN and PMAX.
If such element is found, return its position.  Nil otherwise."
  (setq filter
        (eww-lnum-replace-regexps-in-string ; escape special characters
         filter "\\?" "\\\\?" "\\!" "\\\\!" "\\[" "\\\\["
         "\\*" "\\\\*" "\\+" "\\\\+" "\\." "\\\\." "\\^" "\\\\^"
         "\\$" "\\\\$"))
  (let ((pos pmin))
    (catch 'found
      (while (and pos (setq pos (funcall next-func pos))
                  (< pos pmax))
        (if (string-match-p filter (buffer-substring-no-properties
                                    pos (or (next-single-property-change
                                             pos 'help-echo)
                                            pmax)))
            (throw 'found pos))))))

(defun eww-lnum (&optional filter dont-clear-p)
  "Make overlays that display link numbers.  Return last used index.
FILTER is filter string for anchor text.
DONT-CLEAR-P determines whether previous numbering has to be cleared."
  (eww-lnum-set-numbering 'eww-lnum-next filter dont-clear-p))

(defmacro eww-lnum-prompt-str (num fun start def-anchor filter
                                   &optional show-num)
  "Construct a prompt string for function `eww-lnum-read-interactive'.
NUM is a number variable for currently to be selected element.
FUN is a function to be called with NUM as argument.
START is a string to start the prompt.
DEF-ANCHOR is info for the default 0 element.
FILTER is current string used for filtering.
SHOW-NUM if specified replaces NUM."
  `(let ((anchor (funcall ,fun ,num))
         (show-num ,show-num))
     (setq anchor (if anchor (concat " [" anchor "]")
                    (setq ,num 0
                          show-num "")
                    ,def-anchor))
     (concat ,start
             (or show-num (propertize (number-to-string ,num)
                                      'face 'minibuffer-prompt))
             " " ,filter anchor)))

(defun eww-lnum-read-interactive (prompt fun last-index &optional
                                         def-anchor filter def-num)
  "Interactively read a valid integer from minubuffer with PROMPT.
Execute a one argument function FUN with every current valid integer.
DEF-ANCHOR is initial element to print.
FILTER is the initial aplied filter.
DEF-NUM is the initial selected element, 1 if not given.
Use <return> to submit current selection; <backspace> for correction;
<C-g> or <escape> to quit action;
<space> and <delete> for scrolling page.
Entering 0 may choose default anchor without <return>.
Every other character is appended to a filtering string.
<CTRL>+<DIGIT> is appended to the filtering string as <DIGIT>.
If `eww-lnum-quick-browse' is non-nil, choose without
<return> on single possible selection.
Return list of selected number and last applied filter."
  (setq def-anchor (if def-anchor (concat " [" def-anchor "]")
                     "")
        prompt (propertize prompt 'face 'minibuffer-prompt))
  (let ((filter (or filter ""))
        (auto-num (or (null def-num) (= def-num 0)))
        ch)
    (let ((num (if auto-num 1 def-num)))
      (catch 'select
        (let ((temp-prompt (eww-lnum-prompt-str num fun prompt
                                                def-anchor filter
                                                (if auto-num ""))))
          (while (not (memq		; while not return or escape
                       (setq ch (read-event temp-prompt t))
                       '(return 10 13 ?\n ?\r ?\C-g escape 27 ?\e)))
            (cond
             ((memq ch '(backspace 8 127 ?\C-h))
              (if auto-num
                  (or (string-equal filter "") ; delete last filter character
                      (setq num 1
                            filter (substring-no-properties
                                    filter 0 (1- (length filter)))
                            last-index (eww-lnum filter)
                            temp-prompt
                            (eww-lnum-prompt-str num fun prompt
                                                 def-anchor filter "")))
                (setq num (/ num 10))	; delete last digit
                (if (zerop num)
                    (setq num 1
                          auto-num t))
                (setq temp-prompt
                      (eww-lnum-prompt-str num fun prompt
                                           def-anchor filter
                                           (if auto-num "")))))
             ;; scroll options
             ((memq ch '(32 ?\ ))		; scroll down
              (eww-lnum-remove-overlays)
              (ignore-errors
                (scroll-up)
                ;; scroll-up sets wrongly window-start/end
                (redisplay))
              (setq last-index (eww-lnum filter t))
              (if (zerop last-index) ; filter left nothing
                  (let* ((pmax (point-max))
                         (pos (eww-lnum-next-filter ;search below
                               'eww-lnum-next filter
                               (min (window-end) pmax) pmax)))
                    (when pos
                      (goto-char pos)
                      (redisplay)
                      (setq last-index (eww-lnum filter t)))))
              (setq num (if (zerop last-index) 0 1)
                    auto-num t
                    temp-prompt (eww-lnum-prompt-str num fun prompt
                                                     def-anchor
                                                     filter "")))
             ((eq ch 'delete)		; scroll up
              (eww-lnum-remove-overlays)
              (scroll-down)
              (redisplay)
              (setq last-index (eww-lnum filter t))
              (if (zerop last-index) ; filter left nothing
                  (let ((pos (eww-lnum-next-filter ;search above
                              'eww-lnum-next filter
                              (point-min) (window-start))))
                    (when pos
                      (goto-char pos)
                      (redisplay)
                      (setq last-index (eww-lnum filter t)))))
              (setq num (if (zerop last-index) 0 1)
                    auto-num t
                    temp-prompt (eww-lnum-prompt-str num fun prompt
                                                     def-anchor
                                                     filter "")))
             ;; iteration options
             ((memq ch '(left up))
              (setq num (if (> num 1) (1- num)
                          last-index)
                    auto-num t
                    temp-prompt
                    (eww-lnum-prompt-str num fun prompt def-anchor
                                         filter "")))
             ((memq ch '(right down))
              (setq num (if (< num last-index)
                            (1+ num)
                          1)
                    auto-num t
                    temp-prompt
                    (eww-lnum-prompt-str num fun prompt def-anchor
                                         filter "")))
             ((and (numberp ch) (< 47 ch) (< ch 58))
              (if auto-num
                  (if (= ch 48) (throw 'select (setq num 0))
                    (setq num (- ch 48)
                          auto-num nil))
                (setq num (+ (* num 10) ch -48)))
              (if (> num last-index)
                  (if (zerop (setq num (/ num 10)))
                      (setq num 1
                            auto-num t))
                (and (memq eww-lnum-quick-browsing
                           '(quick-all quick-numbers))
                     (> (* num 10) last-index)
                     (throw 'select num)))
              (setq temp-prompt
                    (eww-lnum-prompt-str num fun prompt def-anchor
                                         filter (if auto-num ""))))
             (t (setq ch (string (cond  ;append filter character
                                  ((= ch 67108896) 32) ;<ctrl>+SPACE
                                  ((and (< 67108911 ch) ;treat <ctrl>+DIGIT
                                        (< ch 67108922))
                                   (- ch 67108864)) ; as DIGIT
                                  (t ch)))
                      filter (concat filter ch)
                      last-index (eww-lnum filter))
                (if (and (= last-index 1)
                         (memq eww-lnum-quick-browsing
                               '(quick-all quick-filter)))
                    (throw 'select (setq num 1))
                  (when (zerop last-index) ; filter left nothing
                    (let* ((pmax (point-max))
                           (pos (or (eww-lnum-next-filter ;search below
                                     'eww-lnum-next filter
                                     (min (window-end) pmax) pmax)
                                    (eww-lnum-next-filter ;search above
                                     'eww-lnum-next filter
                                     (point-min) (window-start)))))
                      (when pos
                        (goto-char pos)
                        (redisplay)
                        (setq last-index (eww-lnum filter t))))
                    (if (zerop last-index) ; search found nothing, remove new char
                        (setq filter (substring-no-properties
                                      filter 0 (1- (length filter)))
                              last-index (eww-lnum filter t))))
                  (setq num 1
                        auto-num t
                        temp-prompt
                        (eww-lnum-prompt-str num fun prompt def-anchor
                                             filter "")))))))
        (if (memq ch '(?\C-g escape 27 ?\e))
            (keyboard-quit)))
      (list num filter))))

(defmacro eww-with-lnum (filter &rest body)
  "Within TYPE anchor numbering with FILTER execute BODY.
Otherwise activate numbering, then clear numbering overlays.
Within BODY, `last-index' is bound to the last used index number."
  `(let ((original-mode-line-format mode-line-format)
         (buffer (current-buffer)))
     (unwind-protect (progn
                       (setq mode-line-format
                             "RET: select | BACKSPACE: correction | \
chars, C-digit, C-SPACE: add chars, digits or space to string \
filter | arrows: move selection | SPACE,DEL: scroll | \
ESC, C-g: quit")
                       (force-mode-line-update)
                       (let ((last-index (eww-lnum ,filter)))
                         ,@body))
       (with-current-buffer buffer
         (setq mode-line-format original-mode-line-format)
         (eww-lnum-remove-overlays (point-min) (point-max))))))

(defun eww-lnum-get-point-info (position)
  "Get `help-echo' property for POSITION."
  (or (get-text-property position 'eww-form)
      (get-text-property position 'help-echo)))

(defun eww-lnum-highlight-anchor (arg)
  "Highlight specified by ARG number anchor.  Return text description."
  (let (marked-label)
    (dolist (overlay (overlays-in (max (1- (window-start)) (point-min))
                                  (min (window-end) (point-max))))
      (cond
       ((overlay-get overlay 'eww-lnum-match)
        (delete-overlay overlay))
       ((eq arg (overlay-get overlay 'eww-lnum-overlay))
        (let* ((start (overlay-start overlay))
               (match-overlay
                (make-overlay
                 start
                 (next-single-property-change start 'help-echo))))
          (overlay-put match-overlay 'eww-lnum-match t)
          (overlay-put match-overlay 'face 'match)
          (or marked-label
              (let ((info (eww-lnum-get-point-info start)))
                (setq marked-label
                      (if (stringp info)
                          info
                        (or (get-text-property start 'help-echo)
                            (buffer-substring-no-properties
                             start (next-single-property-change
                                    start 'help-echo)))))))))))
    marked-label))

(defmacro eww-lnum-get-match-info (condition found-tag)
  "For the first overlay matching CONDITION throw through FOUND-TAG \
anchor info."
  `(dolist (overlay (overlays-in (max (1- (window-start)) (point-min))
                                 (min (window-end) (point-max))))
     (if ,condition
         (let ((pos (overlay-start overlay)))
           (throw ,found-tag (list (eww-lnum-get-point-info pos)
                                   pos))))))

(defun eww-lnum-get-anchor-info (&optional num)
  "Get info (url/action position image image-alt) of anchor numbered as NUM.
If NUM is not specified, use currently highlighted anchor."
  (catch 'found
    (if num
        (eww-lnum-get-match-info
         (eq num (overlay-get overlay 'eww-lnum-overlay)) 'found)
      (eww-lnum-get-match-info (overlay-get overlay 'eww-lnum-match)
                               'found))))

(defun eww-lnum-get-action (&optional prompt)
  "Turn on link numbers and return list of url or action, position \
of PROMPT selected anchor.
Highlight every intermediate result anchor.
Input 0 corresponds to location url."
  (eww-with-lnum
   ""
   (let ((current-url (eww-lnum-current-url)))
     (if (zerop last-index)
         (if (y-or-n-p (concat "No items found. Select default? ["
                               current-url "] "))
             (list current-url 0)
           (keyboard-quit))
       (let ((num (car (eww-lnum-read-interactive
                        (or prompt "Anchor number: ")
                        'eww-lnum-highlight-anchor
                        last-index current-url))))
         (if (zerop num)
             (list current-url 0)
           (eww-lnum-get-anchor-info num)))))))

(defun eww-lnum-browse-url (url &optional new-session)
  "Browse URL in NEW-SESSION.
Visit in background if NEW-SESSION is :background."
  (if new-session
      (let ((new-buffer "*eww*")
            (num 0))
        (while (get-buffer new-buffer)
          (setq num (1+ num)
                new-buffer (format "*eww*<%d>" num)))
        (if (eq new-session :background)
            (with-current-buffer (get-buffer-create new-buffer)
              (eww-mode)
              (eww-browse-url url))
          (switch-to-buffer new-buffer)
          (eww-mode)
          (eww-browse-url url)))
    (eww-browse-url url)))

(defun eww-lnum-visit (info &optional new-session edit)
  "Visit url determined with selection INFO.
Optionally visit in NEW-SESSION, in background if equal to :background.
If EDIT, edit url before visiting."
  (if (or new-session edit)
      (eww-lnum-browse-url (if edit
                               (read-string "Visit url: " (car info))
                             (car info))
                           new-session)
    (goto-char (cadr info))
    (eww-follow-link)))

(defun eww-lnum-activate-form (info)
  "Choose appropriate action for form specified by INFO."
  (push-mark (point))
  (goto-char (cadr info))
  (let ((type (plist-get (car info) :type)))
    (cond ((or (string-equal type "checkbox")
               (string-equal type "radio"))
           (eww-toggle-checkbox))
          ((string-equal (get-text-property (cadr info) 'help-echo)
                         "select field")
           (eww-change-select))
          ((or (string-equal type "submit")
               (eq (get-text-property (cadr info) 'face)
                   'eww-form-submit))
           (eww-submit)))))

;;;###autoload
(defun eww-lnum-follow (arg)
  "Turn on link numbers, ask for one and execute appropriate action on it.
If link - visit it; button - press; input - move to it.
With prefix ARG visit link in new session.
With `-' prefix ARG, visit in background.
With double prefix ARG, prompt for url to visit.
With triple prefix ARG, prompt for url and visit in new session."
  (interactive "p")
  (let* ((edit (or (or (< arg -1) (<= 16 arg))))
         (new-buffer (or (= arg 4) (< 16 arg)))
         (background (< arg 0))
         (info (eww-lnum-get-action (format "%sollow%s%s: "
                                            (if edit "Edit and f" "F")
                                            (if new-buffer
                                                " in new buffer"
                                              "")
                                            (if background
                                                " in background"
                                              "")))))
    (cond ((null info)
           (message "No valid anchor selected"))
          ((stringp (car info))         ; link
           (eww-lnum-visit info (if background
                                    :background
                                  new-buffer)
                           edit))
          (t (eww-lnum-activate-form info)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; universal

(defmacro eww-lnum-make-action (text cmd)
  "Return a TEXT propertized as a link that invokes CMD when clicked."
  `(propertize ,text 'action ,cmd 'mouse-face 'highlight))

(defun eww-lnum-universal-dispatch (info label action-alist)
  "Print available options for determined by INFO element.
LABEL is identifier to be echoed in the minibuffer.
ACTION-ALIST is an alist of available options where each element
is in the following format: (keycode function docstring).
Function has to take one argument that is selection info."
  (let ((action-alist (append action-alist eww-lnum-actions-general))
        char selection-made)
    (save-window-excursion
      (let ((original-mode-line-format mode-line-format))
        (unwind-protect
            (let ((selection-buffer (get-buffer-create
                                     "*eww action selection*")))
              (set-buffer selection-buffer)
              (setq mode-line-format "RET, left click: select | \
<down>,TAB/<up>,BACKTAB: move to next/previous action"
                    buffer-read-only nil)
              (force-mode-line-update)
              (mapc (lambda (option)
                      (if (consp option)
                          (insert
                           (eww-lnum-make-action
                            (concat "[    " (char-to-string
                                             (car option)) "    ] "
                                             (nth 2 option))
                            (cadr option))
                           "\n")
                        (insert option "\n")))
                    action-alist)
              (insert (eww-lnum-make-action
                       "[Backspace] Back to selection"
                       (lambda (_info) 'restart-selection))
                      "\n")
              (insert (eww-lnum-make-action "[   ESC   ] Quit"
                                            (lambda (_info) nil)))
              (setq buffer-read-only t)
              (goto-char (point-min))
              (while (not (get-text-property (point) 'action))
                (forward-line))		; go over first action
              (pop-to-buffer selection-buffer)
              (setq char (read-event
                          (concat
                           (propertize
                            "Select action: " 'face 'minibuffer-prompt)
                           "[" label "]")
                          t))
              (while (and (not selection-made)
                          (or (consp char)
                              (memq char '(up down tab backtab
                                              return 10 13 ?\n ?\r))))
                (if (consp char)		; mouse click?!
                    (progn (mouse-set-point char)	; move to mouse point
                           (let ((action (get-text-property (point)
                                                            'action)))
                             (if action (setq selection-made action))))
                  (cond ((memq char '(up backtab)) ; move to previous action
                         (when (/= (forward-line -1) 0)
                           (goto-char (point-max)) ; ...or start from bottom
                           (beginning-of-line))
                         (while (and (not (get-text-property (point) 'action))
                                     (= (forward-line -1) 0))))
                        ((memq char '(down tab)) ; move to next action
                         (forward-line)
                         (if (= (point) (point-max))
                             (goto-char (point-min))) ; or move to top
                         (while (and (not (get-text-property (point) 'action))
                                     (/= (point) (point-max)))
                           (forward-line)))
                        ((memq char '(return 10 13 ?\n ?\r)) ; <return> select
                         (let ((action (get-text-property (point)
                                                          'action)))
                           (if action (setq selection-made action))))))
                (unless selection-made
                  (setq char (read-event
                              (concat (propertize
                                       "Select action: " 'face
                                       'minibuffer-prompt)
                                      "[" label "]")
                              t)))))
          (setq mode-line-format original-mode-line-format)
          (kill-buffer (current-buffer)))))
    (unless (memq char '(?\C-g escape 27 ?\e))
      (cond (selection-made (funcall selection-made info))
            ((memq char '(backspace 8 ?\C-h))
             'restart-selection)
            (t (let ((dispatch (assoc-default char action-alist 'eq)))
                 (if dispatch (funcall (car dispatch) info)
                   (message "Invalid selection"))))))))

;;;###autoload
(defun eww-lnum-universal ()
  "Turn on link numbers, ask for one and offer actions over it \
depending on selection.
Actions may be selected either by hitting corresponding key,
pressing <return> over the action line or left clicking."
  (interactive)
  (let* ((filter "")
         (current-url (eww-lnum-current-url))
         (label current-url)
         num)
    (while
        (eq 'restart-selection
            (eww-with-lnum
             filter
             (let ((info
                    (if (zerop last-index)
                        (list current-url 0)
                      (let ((selection (eww-lnum-read-interactive
                                        "Anchor number: "
                                        'eww-lnum-highlight-anchor
                                        last-index current-url
                                        filter
                                        (if (eq num 1) nil num))))
                        (setq num (car selection)
                              filter (cadr selection))
                        (if (zerop num)
                            (progn (setq label current-url)
                                   (list current-url 0))
                          (setq label (eww-lnum-highlight-anchor num))
                          (eww-lnum-get-anchor-info num))))))
               (if info
                   (let ((action (car info)))
                     (if (stringp action)               ; url
                         (eww-lnum-universal-dispatch
                          info label eww-lnum-actions-link-alist)
                       (let ((type (plist-get action :type)))
                         (if (or (string-equal type "checkbox")
                                 (string-equal type "radio")
                                 (string-equal type "submit")
                                 (eq (get-text-property (cadr info)
                                                        'face)
                                     'eww-form-submit)
                                 (string-equal (get-text-property
                                                (cadr info) 'help-echo)
                                               "select field"))
                             (eww-lnum-universal-dispatch ; button
                              info label
                              eww-lnum-actions-button-alist)
                           (eww-lnum-universal-dispatch ; text
                            info label nil)))))
                 (message "No valid anchor selected"))))))))

;;; add link action for generic browser
(if browse-url-generic-program
    (setq eww-lnum-actions-link-alist
          (append eww-lnum-actions-link-alist
                  `((?m (lambda (info) (browse-url-generic (car info)))
                        ,(concat "Open with "
                                 browse-url-generic-program))))))

;;; add link action for curl if present
(if (executable-find "curl")
    (setq eww-lnum-actions-link-alist
          (append eww-lnum-actions-link-alist
                  '((?D (lambda (info)
                          (let ((olddir default-directory))
                            (cd (read-directory-name
                                 "Save to: " eww-download-directory
                                 nil t))
                            (shell-command
                             (concat "curl -k -O '" (car info) "' &")
                             "*Curl*")
                            (cd olddir)))
                        "Download with Curl")))))

(provide 'eww-lnum)

;;; eww-lnum.el ends here
