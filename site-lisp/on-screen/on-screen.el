;;; on-screen.el --- guide your eyes while scrolling

;; Copyright (C) 2013 - 2014 Michael Heerdegen

;; Author: Michael Heerdegen <michael_heerdegen@web.de>
;; Maintainer: Michael Heerdegen <michael_heerdegen@web.de>
;; Created: 24 Jan 2013
;; Keywords: convenience
;; Homepage: https://github.com/michael-heerdegen/on-screen.el
;; Version: 1.0
;; Package-Requires: ((cl-lib "0"))


;; This file is not part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:

;; Scrolling can be distracting because your eyes may lose
;; orientation.  This library implements a minor mode that highlights
;; the previously visible buffer part after each scroll.
;;
;; Installation: Put this library somewhere in your load-path, or
;; install via M-x package-list-packages.  Then add to your init-file:
;;
;;   (require 'on-screen)
;;
;; To invoke on-screen globally for all buffers, also add
;;
;;   (on-screen-global-mode +1)
;;
;; Alternatively you can use the buffer local version `on-screen-mode'.
;; For example, add this line to your init file:
;;
;;   (add-hook 'Info-mode-hook 'on-screen-mode)
;;
;; to enable it in all Info buffers.
;;
;; By default, fringe markers are used for highlighting - see
;; `on-screen-highlight-method' to change that.  Type M-x
;; customize-group RET on-screen RET to see what else can be
;; configured.  If you use a configuration file (.emacs), you may also
;; want to define mode specific settings by using buffer local
;; variables.  For example, to use non intrusive fringe markers by
;; default, but transparent overlays in w3m, you would add
;;
;;   (add-hook
;;    'w3m-mode-hook
;;    (lambda ()
;;      (set (make-local-variable 'on-screen-highlight-method)
;;       'shadow)))
;;
;; to your .emacs.
;;
;; If you use transparent overlays for highlighting and there is the
;; library "hexrgb.el" in your `load-path', it will be used to compute
;; highlighting colors dynamically instead of using constant faces.
;; I.e. if you use non-default background colors (e.g. from custom
;; themes), on-screen will try to perform highlighting with a
;; suitable, slightly different color.  See
;; `on-screen-highlighting-to-background-delta' to control this.
;;
;;
;; Implementation notes (mainly for myself):
;;
;; Implementing this functionality is not as straightforward as one
;; might think.  There are commands that scroll other windows than the
;; current one.  Not only scrolling commands can scroll text - also
;; editing or even redisplay can cause windows to scroll.  There is
;; weird stuff such as folding and narrowing, influencing the visible
;; buffer part.  And although highlighting is realized in the
;; displayed buffers (with overlays), it must be organized on a
;; per-window basis, because different buffer parts may be displayed
;; in different windows, and their highlightings must not interfere.
;;
;; That all makes it necessary to observe windows via hacks in
;; different hooks, and to manage information about buffers, visible
;; parts and timers in a data structure (`on-screen-data').  It is
;; realized as an association list whose keys are windows.  There are
;; some pitfalls - e.g. the data can be out of date if the window
;; configuration has changed and windows display different buffers
;; now.  The data must be updated, but not simply be thrown away,
;; because the highlightings in the old buffers must be removed
;; nonetheless.
;;
;;
;; Acknowledgments:
;;
;; This library was inspired by a similar feature of the "Conqueror"
;; web browser.
;;
;; Thanks for Drew Adams for testing and contributions.




;;; Code:

;;; Requirements

(require 'cl-lib)
(require 'timer)
(require 'hexrgb nil t)


;;; Configuration stuff

(defgroup on-screen nil
  "Guide your eyes while scrolling."
  :group 'convenience
  :prefix "on-screen")

(defcustom on-screen-inverse-flag nil
  "What area to highlight.
When nil, highlight the previously visible screenful.  Else
highlight the previously off-screen parts."
  :group 'on-screen :type 'boolean)

(defcustom on-screen-highlight-method 'fringe
  "Type of highlighting used by `on-screen-mode'.
The following values are valid:

  fringe       - graphical markers in the fringe
  shadow       - transparent overlay on the text
  line         - transparent overlay on the confining text lines
  narrow-line  - narrow horizontal lines

The fringe and the narrow-line methods only work on graphical
displays.  narrow-line only works with Emacs 24 or higher.

`on-screen-inverse-flag' defines which part(s) of the buffers are
highlighted.

The face used for \"shadow\" and \"line\" may be computed
dynamically to support different background colors (color themes)
- see `on-screen-highlighting-to-background-delta'."
  :type '(choice
          (const :tag "Fringe markers"                     fringe)
          (const :tag "Transparent overlay"                shadow)
          (const :tag "Overlay on confining text lines"    line)
          (const :tag "Narrow horizontal line"             narrow-line))
  :group 'on-screen)

(defcustom on-screen-fringe-marker-position t
  "Where to display fringe markers.
Ignored if highlighting doesn't use the fringe."
  :type '(choice
          (const :tag "Left fringe only"  left)
          (const :tag "Right fringe only" right)
          (const :tag "Both sides"        t))
  :group 'on-screen)

(defface on-screen-shadow
  '((((class color) (min-colors 88) (background light))
     :background "#f2efcb" ;; alternative: "#f5f4ff" is a bit less intrusive
     )
    (((class color) (min-colors 88) (background dark))
     :background "#272620")
    (((class color) (min-colors 8)  (background light))
     :background "green")
    (((class color) (min-colors 8)  (background dark))
     :background "blue"))
  "Face used for displaying a transparent overlay."
  :group 'on-screen)

(defcustom on-screen-highlighting-to-background-delta .05
  "How much shadow and line highlighting should differ from background.
This should be a positive floating point number less than 1.
Smaller values will lead to a highlighting color being more
similar to the frame background.  A value of nil means to use use
just face `on-screen-shadow'.

This variable is ignored if the library \"hexrgb\" is not
available."
  :group 'on-screen
  :type '(choice (const :tag "Use standard face" nil)
                 (float :tag "Delta")))

(defface on-screen-fringe '((t (:inherit shadow)))
  "Face used for fringe markers."
  :group 'on-screen)

(defface on-screen-narrow-line
  '((((background dark))  (:width extra-expanded :underline (:color "gray30" :style wave)))
    (((background light)) (:width extra-expanded :underline (:color "gray70" :style wave))))
  "Face used by the narrow-line highlighting method."
  :group 'on-screen)

(defcustom on-screen-delay 5
  "How long `on-screen-mode' should display optical aids."
  :group 'on-screen :type 'number)

(defcustom on-screen-auto-update t
  "Whether to update highlighting for successive scrolls.
When non-nil, every scroll action will cause a highlighting
according to the previously visible screenful.  When nil, a once
drawn highlighting will remain fixed relative to the text even
if you scroll further until `on-screen-delay' is over."
  :group 'on-screen :type 'boolean)

(defcustom on-screen-remove-when-edit nil
  "Whether to instantly remove highlighting when editing.

In those situations where a single command causes multiple
changes to a buffer highlighting is always removed to avoid
confusion."
  :group 'on-screen :type 'boolean)

(defcustom on-screen-treat-cut-lines nil
  "Whether to care about vertically cut lines.
If nil, always count lines at the window start or end that are
only partially visible as part of the visible area.  Else, a
number between 0 and 1, meaning that lines will count as visible
when the hidden part of them is less than this number.  Note that
a non-nil value may make scrolling stuttering on slow computers."
  :group 'on-screen
  :type '(choice (const :tag "Count vertically cut lines as visible" nil)
                 (float :tag "Count lines with hidden part less than this as visible"
			:value .4)))

;;; Other variables

(defvar on-screen-overlay-priority 30     ; > stripe buffer, < ediff, isearch
  "Priority for all on-screen overlays.")

(defvar on-screen-initialized-p nil
  "Whether we have already added stuff to the hooks.")

(defvar on-screen-data nil
  "Association list holding internal data.")

(defvar on-screen-command-counter 0)
(defvar on-screen-last-change 0)


;;; User Commands

;;;###autoload
(define-minor-mode on-screen-mode
  "Buffer local minor mode guiding your eyes while scrolling.
With a prefix argument ARG, enable the mode if ARG is positive,
and disable it otherwise.  If called from Lisp, enable the mode
if ARG is omitted or nil.
Type M-x customize-group on-screen RET for configuration."
  :group 'on-screen
  (when on-screen-mode
    (unless on-screen-initialized-p
      (on-screen-initialize))))

;;;###autoload
(define-minor-mode on-screen-global-mode
  "Global minor mode guiding your eyes while scrolling.
With a prefix argument ARG, enable the mode if ARG is positive,
and disable it otherwise.  If called from Lisp, enable the mode
if ARG is omitted or nil.
Type M-x customize-group on-screen RET for configuration."
  :group 'on-screen :global t
  (when on-screen-global-mode
    (unless on-screen-initialized-p
      (on-screen-initialize))))

;;;###autoload
(defalias 'global-on-screen-mode 'on-screen-global-mode)


;;; Internal functions

(defun on-screen-window-start (&optional window)
  "Like `window-start', but exclude partially visible lines."
  (let* ((start (window-start window))
         (vis (and on-screen-treat-cut-lines (pos-visible-in-window-p start window t))))
    (if (not (cddr vis))
        start
      (cl-destructuring-bind (_x _y rtop _rbot rowh _vpos) vis
        (if (< (/ (float rtop) (+ rtop rowh)) on-screen-treat-cut-lines) ;; count as visible
            start
          (with-current-buffer (window-buffer window)
            (save-excursion
              (goto-char start)
              (on-screen-beginning-of-line +2)
              (point))))))))

(defun on-screen-window-end (&optional window)
  "Like `window-end', but exclude partially visible lines."
  (let* ((end (window-end window))
         (vis (and on-screen-treat-cut-lines (pos-visible-in-window-p (1- end) window t))))
    (if (not (cddr vis))
        end
      (cl-destructuring-bind (_x _y _rtop rbot rowh _vpos) vis
        (if (< (/ (float rbot) (+ rbot rowh)) on-screen-treat-cut-lines) ;; count as visible
            end
          (with-current-buffer (window-buffer window)
            (save-excursion
              (goto-char end)
              (on-screen-beginning-of-line 0)
              (point))))))))

(defun on-screen-beginning-of-line (&optional n)
  (cl-callf or n 1)
  (forward-visible-line (- n 1)))

(defun on-screen-end-of-line (&optional n)
  (cl-callf or n 1)
  (forward-visible-line (- n 1))
  (end-of-visible-line))

(defun on-screen-record-data (win area &optional timer overlays)
  ;; The collected data has the form ((beg end) timer overlays), and
  ;; this is what `on-screen-get-data' returns.  Internally, this
  ;; function also remembers the window-buffer of the window, to
  ;; enable the mode to check if remembered data still belongs to the
  ;; same buffer.
  "Store information for window WIN in `on-screen-data'.
AREA is a list (beg end).  TIMER is the currently active timer
object.  OVERLAYS are the on-screen overlays currently visible in
WIN.

A nil value for AREA, TIMER or OVERLAYS means that the remembered
values should not be changed.  If TIMER is the symbol `finished',
remember nil for the timer."
  (let* ((entry (assoc win on-screen-data))
	 (data  (cdr entry))
	 (same-buffer-p (eq (car data) (window-buffer win))))
    (setq area  (or area        (and same-buffer-p (cadr data)))
	  timer (cond  ((timerp timer) timer)
		       (timer nil)
		       (t (and same-buffer-p (cl-caddr data))))
	  overlays (or overlays (and same-buffer-p (cl-cadddr data)))
	  data  `(,(window-buffer win) ,area ,timer ,overlays))
    (if entry
	(setcdr entry data)
      (push (cons win data) on-screen-data))))

(defun on-screen-get-data (win)
  "Return stored data for WIN if existent and up-to-date."
  (let ((data (cdr (assoc win on-screen-data))))
    (if (eq (car data) (window-buffer win))
        (cdr data)
      nil)))

(defun on-screen-cleanup-data ()
  "Delete information stored for deleted windows."
  (setq on-screen-data
        (delq nil (mapcar (lambda (entry) (if (window-live-p (car entry)) entry nil))
                          on-screen-data))))

(defun on-screen-derive-from-frame-bg
  (win delta-brightness-dark-bg delta-brightness-light-bg delta-hue)
  "Helper calculating a suitable background color for highlighting."
  (let ((frame (window-frame win)))
    (and (display-graphic-p frame) (featurep 'hexrgb)
         (let* ((bg (or (let ((frame-bg  (cdr (assq 'background-color (frame-parameters frame)))))
                          (when (member frame-bg '(nil unspecified "unspecified-bg"))
                            (setq frame-bg  (if (eq (frame-parameter frame 'background-mode) 'dark)
                                                "Black"
                                              "White")))
                          (and frame-bg  (x-color-defined-p frame-bg)  frame-bg))))
                (sat (condition-case nil (hexrgb-saturation bg) (error nil))))
           (and sat
                (if (hexrgb-approx-equal sat 0.0)
                    ;; Grayscale - change bg value slightly.
                    (hexrgb-increment-value
                     bg (if (eq (frame-parameter frame 'background-mode) 'dark)
                            delta-brightness-dark-bg
                          delta-brightness-light-bg))
                  (hexrgb-increment-hue bg delta-hue)) ; Color - change bg hue slightly.
                )))))

(defun on-screen-get-shadow-face (win)
  "Return face for the transparent overlay in WIN."
  (or (and on-screen-highlighting-to-background-delta
           (let ((bg-col (apply #'on-screen-derive-from-frame-bg win
                                (mapcar (lambda (x) (* x on-screen-highlighting-to-background-delta))
                                        (list 1 -1 1)))))
             (and bg-col `((t (:background ,bg-col))))))
      'on-screen-shadow))

(defun on-screen-make-fringe-overlays (pos topp &optional inversep)
  "Create and return list of fringe overlays."
  (let (ov1 ov2)
    (unless (eq on-screen-fringe-marker-position 'left)
      (setq ov1  (save-excursion (make-overlay (progn (goto-char pos)
                                                      (on-screen-beginning-of-line
                                                       (cond ((not inversep) +1)
                                                             (topp           +2)
                                                             (t               0)))
                                                      (point))
                                               (1+ (point)))))
      (overlay-put ov1 'before-string (on-screen-fringe-string topp nil inversep)))
    (unless (eq on-screen-fringe-marker-position 'right)
      (setq ov2  (save-excursion (make-overlay (progn (goto-char pos)
                                                      (on-screen-beginning-of-line
                                                       (cond ((not inversep) +1)
                                                             (topp           +2)
                                                             (t               0)))
                                                      (point))
                                               (1+ (point)))))
      (overlay-put ov2 'before-string (on-screen-fringe-string topp t inversep)))
    (delq nil (list ov1 ov2))))

(defun on-screen-fringe-string (topp leftp &optional inversep)
  "Return a string suitable for displaying fringe markers."
  (let ((xor (lambda (x y) (if x (not y) y))))
    (propertize (purecopy " ")
                'display  (list (if leftp 'left-fringe 'right-fringe)
                                (if (funcall xor topp (not inversep))
                                    (if leftp 'top-left-angle 'top-right-angle)
                                  (if leftp 'bottom-left-angle 'bottom-right-angle))
                                'on-screen-fringe))))

(defun on-screen-make-line-overlay (pos)
  "Create an overlay around POS for the line method."
  (save-excursion
    (make-overlay (progn (goto-char pos) (on-screen-beginning-of-line)     (point))
                  (progn (goto-char pos) (on-screen-end-of-line)       (1+ (point))))))

(defun on-screen-make-narrow-line-overlay (win pos)
  "Create an overlay around POS for the narrow-line method."
  (let ((ov (save-excursion
              (make-overlay (progn (goto-char pos) (on-screen-beginning-of-line) (point))
                            (progn (goto-char pos) (on-screen-end-of-line)       (point))))))
    (overlay-put ov 'face 'on-screen-narrow-line)
    ;; The following is necessary to get a line spanning the entire
    ;; window width, because underlining is only applied to text - a
    ;; problem especially for empty lines.  However this hides any
    ;; other highlighting there, e.g. from stripe-buffer or
    ;; hl-line-mode.  I think there's nothing I can do about that.
    (overlay-put ov 'after-string (propertize "foo"
                                              'face 'on-screen-narrow-line
                                              'display `(space :align-to ,(window-width win))
                                              'cursor 0))
    ov))

(defun on-screen-get-windows (&optional all-frames)
  "Return a list of all windows.
With ALL-FRAMES non-nil, include all windows of all frames, else
only the windows of the selected frame."
  (apply #'nconc
         (mapcar (lambda (frame) (window-list frame))
                 (if all-frames (frame-list) (list (selected-frame))))))

(defun on-screen-pre-command ()
  "Remember visible buffer parts in the selected frame."
  ;;   This normally goes to `pre-command-hook'.
  (cl-incf on-screen-command-counter)
  (add-hook 'after-change-functions #'on-screen-after-change) ;$$$$ bug#16796
  (condition-case nil
      (mapc (lambda (win) (with-current-buffer (window-buffer win)
		       (when (on-screen-enabled-p)
			 (on-screen-record-data win (list (on-screen-window-start win)
							  (on-screen-window-end   win))))))
	    (on-screen-get-windows))
    ((debug error) nil)))

(defun on-screen-after-scroll (win display-start)
  "DTRT after scrolling.
This should normally go to `window-scroll-functions'."
  (condition-case nil
      (with-current-buffer (window-buffer win)
        (when (on-screen-enabled-p)
          (let* ((win-data (on-screen-get-data win))
                 (area     (car  win-data))
                 (timer    (cadr win-data))
                 (overlays (cl-caddr win-data))
                 (s1       (car area))
                 (s2       (cadr area)))
            (when (and
		   on-screen-auto-update
		   (timerp timer)
		   ;; avoid removing highlighting when `window-scroll-functions' is
		   ;; called multiple times in succession (follow-mode does that)
		   (not (eq (car-safe area) (on-screen-window-start win))))
              ;; do what the timer would do, and cancel timer
              (on-screen-remove-highlighting win)
              (cancel-timer timer)
              (on-screen-record-data win area 'finished)
              (setq timer nil))
            (cond
             ((timerp timer)
              (timer-set-time timer (timer-relative-time (current-time) on-screen-delay)))
             ((or (not area)
                  (= display-start s1)))
             (t
              (setq
               overlays
               (let ((method `(,on-screen-highlight-method . ,on-screen-inverse-flag)))

                 ;; prevent highlighting in certain situations
                 ;; note that `window-end' must not be used here!

                 (when (and s1 s2
                            (pos-visible-in-window-p (point-min) win)
                            (pos-visible-in-window-p (point-max) win))
                   ;; after narrow
                   (setq s1 nil s2 nil))
                 
                 (when (and s1 s2
                            (>= s2 (point-max))
                            (< s1 (on-screen-window-start win))
                            (pos-visible-in-window-p (point-max) win))
                   ;;scrolling down near buffer end
                   (setq s2 nil))

                 (cond 
                  ((equal method '(shadow . nil))
                   (if (and s1 s2) (list (make-overlay s1 s2)) ()))
                  ((eq (car method) 'shadow)
                   (list (and s1 (make-overlay (point-min)  s1))
                         (and s2 (make-overlay          s2  (point-max)))))
                  ((eq (car method) 'fringe)
                   (append (and s1 (on-screen-make-fringe-overlays     s1  nil (cdr method)))
                           (and s2 (on-screen-make-fringe-overlays (1- s2)   t (cdr method)))))
                  ((equal method '(line . nil))
                   (list (and s1 (on-screen-make-line-overlay     s1))
                         (and s2 (on-screen-make-line-overlay (1- s2)))))
                  ((eq (car method) 'line)
                   (list (and s1 (on-screen-make-line-overlay (1- s1)))
                         (and s2 (on-screen-make-line-overlay     s2))))
                  ((eq (car method) 'narrow-line)
                   (list (and s1 (on-screen-make-narrow-line-overlay win (1- s1)))
                         (and s2 (on-screen-make-narrow-line-overlay win (1- s2)))))))
               overlays (delq nil overlays))
              (dolist (ov overlays)
                (overlay-put ov 'window win) ; display only in selected window
                (overlay-put ov 'priority on-screen-overlay-priority)) 
              (when (memq on-screen-highlight-method '(shadow line))
                (dolist (ov overlays)
                  (overlay-put ov 'face (on-screen-get-shadow-face win))))
              (on-screen-record-data
               win nil
               (run-at-time (time-add (current-time) (seconds-to-time on-screen-delay)) nil
                            (lambda (win)
                              (condition-case nil
                                  (progn
                                    (when (window-live-p win)
                                      (with-current-buffer (window-buffer win)
                                        (on-screen-remove-highlighting win)
                                        (on-screen-record-data
                                         win (list (on-screen-window-start win)
                                                   (on-screen-window-end win))
                                         'finished)))
                                    (on-screen-cleanup-data))
                                ((debug error) nil)))
                            win)
               overlays))))))
    ((debug error) nil)))

(defun on-screen-remove-highlighting (win)
  "Delete all on-screen overlays in window WIN.
This has to be done for a previously buffer if the window-buffer
had changed."
  (let* ((entry (assoc win on-screen-data))
         (data  (cdr entry))
         (buffer (car data)))
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (let* ((data     (cdr data))
               (timer    (cadr data))
               (overlays (cl-caddr data)))
          (dolist (ov overlays) (delete-overlay ov))
          (when (timerp timer) (cancel-timer timer))))
      (setq on-screen-data (delq entry on-screen-data)))))

(defun on-screen-after-change (&rest _)
  "Reset highligting for current buffer after it was changed.
This has to be done for all its windows.  Goes to
`after-change-functions'."
  (when (or on-screen-remove-when-edit
	    (= on-screen-last-change on-screen-command-counter))
    (let ((buf (current-buffer)))
      (when (on-screen-enabled-p buf)
	(dolist (win (on-screen-get-windows t))
	  (when (eq (window-buffer win) buf)
	    (on-screen-remove-highlighting win))))))
  (setq on-screen-last-change on-screen-command-counter))

(defun on-screen-after-wconf-change ()
  "Clean up after the window configuration has changed.
I.e., for all windows of the selected frame, remove all
highlightings and clear all associated data."
  (let ((wins (on-screen-get-windows)))
    (dolist (win wins)
      (on-screen-remove-highlighting win))))

(defun on-screen-enabled-p (&optional buffer)
  "Return non-nil if on-screen is enabled in BUFFER."
  (with-current-buffer (or buffer (current-buffer))
    (if on-screen-global-mode t on-screen-mode)))

(defun on-screen-initialize ()
  "Prepare for using on-screen."
  (add-hook 'pre-command-hook        #'on-screen-pre-command)
  (add-hook 'window-scroll-functions #'on-screen-after-scroll)
  (add-hook 'after-change-functions  #'on-screen-after-change)
  (add-hook 'window-configuration-change-hook #'on-screen-after-wconf-change)
  (setq on-screen-initialized-p t))


(provide 'on-screen)

;;; on-screen.el ends here
