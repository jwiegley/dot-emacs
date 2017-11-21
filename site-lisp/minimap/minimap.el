;;; minimap.el --- Sidebar showing a "mini-map" of a buffer

;; Copyright (C) 2009-2014 Free Software Foundation, Inc.

;; Author: David Engster <deng@randomsample.de>
;; Keywords:
;; Version: 1.2

;; This file is part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file is an implementation of a minimap sidebar, i.e., a
;; smaller display of the current buffer on the left side.  It
;; highlights the currently shown region and updates its position
;; automatically.  You can navigate in the minibar by dragging the
;; active region with the mouse, which will scroll the corresponding
;; edit buffer.  Additionally, you can overlay information from the
;; tags gathered by CEDET's semantic analyzer.

;; Simply use M-x minimap-mode to toggle activation of the minimap.
;; Use 'M-x customize-group RET minimap RET' to adapt minimap to your
;; needs.

;;; KNOWN BUGS:

;; * Currently cannot deal with images.
;; * Display/movement can be a bit erratic at times.

;;; TODO:

;; * Fix known bugs.
;; * Make sidebar permanently visible. This requires something like a
;;   'window group' feature in Emacs, which is currently being worked on.
;; * Moving the active region with the keyboard / mouse-wheel ?


;;; News:
;;
;;;; Changes since v1.1:
;;
;; - Change some defaults: better colors, reduced update delay.
;; - `minimap-tag-only': New experimental feature to only display an
;;   'abstract view' of the buffer with overlays generated from
;;   Semantic information.  Works only for buffers parsed by Semantic.
;; - `minimap-highlight-line': Highlight current line in Minimap.
;; - Fix autoloads.
;; - Display lines denoting beginning/end of functions in Semantic
;;   overlays.
;;
;;;; Changes since v1.0:
;;
;; - Largely rewritten as a minor mode; use M-x minimap-mode to
;;   enable/disable.
;; - Minimap will now remain active for all buffers which derive from
;;   `prog-mode' (can be changed through `minimap-major-modes').  The
;;   minimap window will be automatically created or deleted (see new
;;   variables `minimap-recreate-window' and
;;   `minimap-automatically-delete-window').
;; - Possibility to set a minimum width of the minimap window
;;   (`minimap-minimum-width').
;; - Minimap window will be marked so that you should not be able to
;;   enter it.
;; - Semantic overlays will be automatically updated during editing.
;; - Lots of bug fixes.

(defgroup minimap nil
  "A minimap sidebar for Emacs."
  :group 'convenience)

(defface minimap-font-face
  '((default :family "DejaVu Sans Mono" :height 30))
  "Face used for text in minimap buffer, notably the font family and height.
This height should be really small.  You probably want to use a
TrueType font for this.  After changing this, you should
recreate the minimap to avoid problems with recentering."
  :group 'minimap)

(defface minimap-active-region-background
  '((((background dark)) (:background "#700000"))
    (t (:background "#C847D8FEFFFF")))
  "Face for the active region in the minimap.
By default, this is only a different background color."
  :group 'minimap)

(defface minimap-semantic-function-face
  '((((background dark))
     (:box (:line-width 1 :color "white")
	   :inherit (font-lock-function-name-face minimap-font-face)
	   :height 2.75 :background "#202414"))
    (t (:box (:line-width 1 :color "black")
	     :inherit (font-lock-function-name-face minimap-font-face)
	     :height 2.75 :background "gray90")))
  "Face used for functions in the semantic overlay.")

(defface minimap-semantic-variable-face
  '((((background dark))
     (:box (:line-width 1 :color "white")
	   :inherit (font-lock-variable-name-face minimap-font-face)
	    :height 2.75 :background "gray10"))
    (t (:box (:line-width 1 :color "black")
	     :inherit (font-lock-function-name-face minimap-font-face)
	     :height 2.75 :background "gray90")))
  "Face used for variables in the semantic overlay.")

(defface minimap-semantic-type-face
  '((((background dark))
     (:box (:line-width 1 :color "white")
	   :inherit (font-lock-type-face minimap-font-face)
	   :height 2.75 :background "gray10"))
    (t (:box (:line-width 1 :color "black")
	     :inherit (font-lock-function-name-face minimap-font-face)
	     :height 2.75 :background "gray90")))
  "Face used for types in the semantic overlay.")

(defcustom minimap-width-fraction 0.15
  "Fraction of width which should be used for minimap sidebar."
  :type 'number
  :group 'minimap)

(defcustom minimap-minimum-width 30
  "Minimum width of minimap in characters (default size).
Use nil to disable."
  :type 'number
  :group 'minimap)

(defcustom minimap-window-location 'left
  "Location of the minimap window.
Can be either the symbol `left' or `right'."
  :type '(choice (const :tag "Left" left)
		 (const :tag "Right" right))
  :group 'minimap)

(defcustom minimap-buffer-name " *MINIMAP*"
  "Buffer name of minimap sidebar."
  :type 'string
  :group 'minimap)

(defcustom minimap-update-delay 0.1
  "Delay in seconds after which sidebar gets updated.
Setting this to 0 will let the minimap react immediately, but
this will slow down scrolling."
  :type 'number
  :set (lambda (sym value)
	 (set sym value)
	 (when (and (boundp 'minimap-timer-object)
		    minimap-timer-object)
	   (cancel-timer minimap-timer-object)
	   (setq minimap-timer-object
		 (run-with-idle-timer
		  minimap-update-delay t 'minimap-update))))
  :group 'minimap)

(defcustom minimap-always-recenter nil
  "Whether minimap sidebar should be recentered after every point movement."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-recenter-type 'relative
  "Specifies the type of recentering the minimap should use.
The minimap can use different types of recentering, i.e., how the
minimap should behave when you scroll in the main window or when
you drag the active region with the mouse.  The following
explanations will probably not help much, so simply try them and
choose the one which suits you best.

`relative' -- The position of the active region in the minimap
corresponds with the relative position of this region in the
buffer.  This the default.

`middle' -- The active region will stay fixed in the middle of
the minimap.

`free' -- The position will be more or less free.  When dragging
the active region, the minimap will scroll when you reach the
bottom or top."
  :type '(choice (const :tag "Relative" relative)
		 (const :tag "Middle" middle)
		 (const :tag "Free" free))
  :group 'minimap)

(defcustom minimap-hide-scroll-bar t
  "Whether the minimap should hide the vertical scrollbar."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-hide-fringes nil
  "Whether the minimap should hide the fringes."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-dedicated-window t
  "Whether the minimap should create a dedicated window."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-display-semantic-overlays t
  "Display overlays from CEDET's semantic analyzer.
If you use CEDET and the buffer's major-mode is supported, the
minimap can display overlays generated by the semantic analyzer.
By default, it will apply the faces `minimap-semantic-<X>-face',
with <X> being \"function\", \"variable\" and \"type\".  Also, it
will display the name of the tag in the middle of the overlay in
the corresponding font-lock face.

See also `minimap-enlarge-certain-faces', which can be used as
fallback."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-enlarge-certain-faces 'as-fallback
  "Whether certain faces should be enlarged in the minimap.
All faces listed in `minimap-normal-height-faces' will be
displayed using the default font height, allowing you to still
read text using those faces.  By default, this should enlarge all
function names in the minimap, given you have font locking
enabled.  This variable can have the following values:

'as-fallback (the default) -- The feature will only be activated
  if information from CEDET's semantic analyzer isn't available
  (see: `minimap-display-semantic-overlays').
'always -- Always active.
nil -- Inactive."
  :type '(choice (const :tag "Fallback if CEDET unavailable." 'as-fallback)
		 (const :tag "Always active." 'always)
		 (const :tag "Inactive." nil))
  :group 'minimap)

(defcustom minimap-normal-height-faces '(font-lock-function-name-face)
  "List of faces which should be displayed with normal height.
When `minimap-enlarge-certain-faces' is non-nil, all faces in
this list will be displayed using the default font height.  By
default, this list contains `font-lock-function-name-face', so
you can still read function names in the minimap."
  :type '(repeat face)
  :group 'minimap)

(defcustom minimap-sync-overlay-properties '(face invisible)
  "Specifies which overlay properties should be synced.
Unlike text properties, overlays are not applied automatically to
the minimap and must be explicitly synced.  This variable
specifies which overlay properties should be synced by
`minimap-sync-overlays'.  Most importantly, this variable should
include 'invisible', so that hidden text does not appear in the
minimap buffer."
  :type '(repeat symbol)
  :group 'minimap)

(defcustom minimap-major-modes '(prog-mode)
  "Major modes for which a minimap should be created.
This can also be a parent mode like 'prog-mode.
If nil, a minimap must be explicitly created for each buffer."
  :type '(repeat symbol)
  :group 'minimap)

(defcustom minimap-recreate-window t
  "Whether the minimap window should be automatically re-created.
If this is non-nil, the side window for the minimap will be
automatically re-created as soon as you kill it."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-automatically-delete-window t
  "Whether the minimap window should be automatically deleted.
Setting this to non-nil will delete the minibuffer side window
when you enter a buffer which is not derived from
`minimap-major-modes' (excluding the minibuffer)."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-tag-only nil
  "Whether the minimap should only display parsed tags from CEDET."
  :type 'boolean
  :group 'minimap)

(defcustom minimap-highlight-line t
  "Whether the minimap should highlight the current line."
  :type 'boolean
  :group 'minimap)

;;; Internal variables

;; The buffer currently displayed in the minimap
(defvar minimap-active-buffer nil)
;; Window start/end from the base buffer
(defvar minimap-start nil)
(defvar minimap-end nil)
;; General overlay for the minimap
(defvar minimap-base-overlay nil)
;; Overlay for the active region
(defvar minimap-active-overlay nil)
;; Timer
(defvar minimap-timer-object nil)
;; Lines the minimap can display
(defvar minimap-numlines nil)
(defvar minimap-pointmin-overlay nil)
;; Line overlay
(defvar minimap-line-overlay nil)


;;; Helpers

(defun minimap-active-current-buffer-p ()
  "Whether the current buffer is displayed in the minimap."
  (and (eq (current-buffer) minimap-active-buffer)
       (get-buffer minimap-buffer-name)
       (with-current-buffer minimap-buffer-name
	 (eq minimap-active-buffer (buffer-base-buffer)))))

(defsubst minimap-get-window ()
  "Get current minimap window."
  (when (get-buffer minimap-buffer-name)
    (get-buffer-window minimap-buffer-name)))

(defsubst minimap-kill-buffer ()
  "Kill the minimap buffer."
  (when (get-buffer minimap-buffer-name)
    (kill-buffer minimap-buffer-name)))

(defun minimap-create-window ()
  (let ((width (round (* (window-width)
			 minimap-width-fraction))))
    (when (< width minimap-minimum-width)
      (setq width minimap-minimum-width))
    (if (eq minimap-window-location 'left)
	(split-window-horizontally width)
      (split-window-horizontally
       (* -1 width))
      (other-window 1))
    ;; Set up the minimap window:
    ;; You should not be able to enter the minimap window.
    (set-window-parameter nil 'no-other-window t)
    ;; Hide things.
    (when minimap-hide-scroll-bar
      (setq vertical-scroll-bar nil))
    (when minimap-hide-fringes
      (set-window-fringes nil 0 0))
    ;; Switch to buffer.
    (switch-to-buffer
     (get-buffer-create minimap-buffer-name) t t)
    ;; Do not fold lines in the minimap.
    (setq truncate-lines t)
    ;; Make it dedicated.
    (when minimap-dedicated-window
      (set-window-dedicated-p nil t))
    (prog1
	(selected-window)
      (other-window 1))))

(defun minimap-setup-hooks (&optional remove)
  "Hook minimap into other modes.
If REMOVE is non-nil, remove minimap from other modes."
  (if remove
      (progn
	(remove-hook 'outline-view-change-hook 'minimap-sync-overlays)
	(remove-hook 'hs-hide-hook 'minimap-sync-overlays)
	(remove-hook 'hs-show-hook 'minimap-sync-overlays))
    ;; outline-(minor-)mode
    (add-hook 'outline-view-change-hook 'minimap-sync-overlays)
    ;; hideshow
    (add-hook 'hs-hide-hook 'minimap-sync-overlays)
    (add-hook 'hs-show-hook 'minimap-sync-overlays)))

;;; Minimap creation / killing

;;;###autoload
(define-minor-mode minimap-mode
  "Toggle minimap mode."
  :global t
  :group 'minimap
  :lighter " MMap"
  (if minimap-mode
      (progn
	(when (and minimap-major-modes
		   (apply 'derived-mode-p minimap-major-modes))
	  (unless (minimap-get-window)
	    (minimap-create-window))
	  ;; Create minimap.
	  (minimap-new-minimap))
	;; Create timer.
	(setq minimap-timer-object
	      (run-with-idle-timer minimap-update-delay t 'minimap-update))
	;; Hook into other modes.
	(minimap-setup-hooks))
    ;; Turn it off
    (minimap-kill)
    (minimap-setup-hooks t)))

(defun minimap-create ()
  "Create a minimap sidebar."
  (interactive)
  (minimap-mode 1))

(defun minimap-new-minimap ()
  "Create new minimap BUFNAME for current buffer and window.
Re-use already existing minimap window if possible."
  (interactive)
  (let ((currentbuffer (current-buffer))
	(win (minimap-get-window))
	(indbuf (make-indirect-buffer (current-buffer)
				      (concat minimap-buffer-name "_temp")))
	(edges (window-pixel-edges)))
    ;; Remember the active buffer currently displayed in the minimap.
    (setq minimap-active-buffer (current-buffer))
    ;; Hook into CEDET if necessary.
    (when (and minimap-display-semantic-overlays
	       (boundp 'semantic-after-toplevel-cache-change-hook))
      (add-hook 'semantic-after-partial-cache-change-hook
		'minimap-apply-semantic-overlays nil t)
      (add-hook 'semantic-after-toplevel-cache-change-hook
		'minimap-apply-semantic-overlays nil t))
    (with-selected-window win
      ;; Now set up the minimap:
      (when (window-dedicated-p)
	(set-window-dedicated-p nil nil))
      (switch-to-buffer indbuf t t)
      (minimap-kill-buffer)
      (rename-buffer minimap-buffer-name)
      ;; Do not fold lines in the minimap.
      (setq truncate-lines t)
      (when minimap-dedicated-window
	(set-window-dedicated-p nil t))
      (setq minimap-base-overlay (make-overlay (point-min) (point-max) nil t t))
      (overlay-put minimap-base-overlay 'face 'minimap-font-face)
      (overlay-put minimap-base-overlay 'priority 1)
      (when minimap-tag-only
	(overlay-put minimap-base-overlay 'face
      		     `(:inherit minimap-font-face
				:foreground ,(face-background 'default))))
      (setq minimap-pointmin-overlay (make-overlay (point-min) (1+ (point-min))))
      (setq minimap-start (window-start)
	    minimap-end (window-end)
	    minimap-active-overlay (make-overlay minimap-start minimap-end)
	    line-spacing 0)
      (overlay-put minimap-active-overlay 'face
		   'minimap-active-region-background)
      (when minimap-tag-only
	(overlay-put minimap-active-overlay 'face
		     `(:inherit 'minimap-active-region-background
			       :foreground ,(face-background 'minimap-active-region-background))))
      (overlay-put minimap-active-overlay 'priority 5)
      (minimap-sb-mode 1)
      (when (and (boundp 'linum-mode)
		 linum-mode)
	(linum-mode 0))
      (setq buffer-read-only t)
      ;; Calculate the actual number of lines displayable with the minimap face.
      (setq minimap-numlines
	    (floor
	     (/
	      (- (nth 3 edges) (nth 1 edges))
	      (car (progn (redisplay t) (window-line-height)))))))
    (minimap-sync-overlays)))

(defun minimap-kill ()
  "Kill minimap."
  (interactive)
  (when (minimap-get-window)
    (delete-window (minimap-get-window)))
  (cancel-timer minimap-timer-object))

;;; Minimap update

(defun minimap-update (&optional force)
  "Update minimap sidebar if necessary.
This is meant to be called from the idle-timer or the post command hook.
When FORCE, enforce update of the active region."
  (interactive)
  ;; If we are in the minibuffer, do nothing.
  (unless (active-minibuffer-window)
    (if (minimap-active-current-buffer-p)
	;; We are still in the same buffer, so just update the minimap.
	(let ((win (minimap-get-window))
	      (start (window-start))
	      (end (window-end))
	      (pt (point)))
	  (when (and (null win)
		     minimap-recreate-window)
	    ;; The minimap window is no longer visible, so create it again...
	    (setq win (minimap-create-window))
	    ;; ...and switch to existing minimap buffer.
	    (with-selected-window win
	      (when (window-dedicated-p)
		(set-window-dedicated-p nil nil))
	      (switch-to-buffer minimap-buffer-name t t)
	      (when minimap-dedicated-window
		(set-window-dedicated-p nil t))))
	  (with-selected-window win
	    ;; Make sure the base overlay spans the whole buffer.
	    (unless (and (= (overlay-start minimap-base-overlay) (point-min))
			 (= (overlay-end minimap-base-overlay) (point-max)))
	      (move-overlay minimap-base-overlay (point-min) (point-max)))
	    (unless (and (not force)
			 (= minimap-start start)
			 (= minimap-end end))
	      ;; Update the overlay.
	      (move-overlay minimap-active-overlay start end)
	      (setq minimap-start start
		    minimap-end end)
	      (minimap-recenter (line-number-at-pos (/ (+ end start) 2))
				(/ (- (line-number-at-pos end)
				      (line-number-at-pos start))
				   2)))
	    (goto-char pt)
	    (beginning-of-line)
	    (unless minimap-line-overlay
	      (setq minimap-line-overlay (make-overlay (point) (1+ (point)) nil t))
	      (overlay-put minimap-line-overlay 'face '(:background "yellow" :foreground "yellow"))
	      (overlay-put minimap-line-overlay 'priority 6))
	    (move-overlay minimap-line-overlay (point) (line-beginning-position 2))
	    (when minimap-always-recenter
	      (recenter (round (/ (window-height) 2)))))
	  ;; Redisplay
	  (sit-for 0))
      ;; The buffer was switched, check if the minimap should switch, too.
      (if (and minimap-major-modes
	       (apply 'derived-mode-p minimap-major-modes))
	  (progn
	    ;; Create window if necessary...
	    (unless (minimap-get-window)
	      (minimap-create-window))
	    ;; ...and re-create minimap with new buffer...
	    (minimap-new-minimap)
	    ;; Redisplay
	    (sit-for 0)
	    ;; ...and call update again.
	    (minimap-update t))
	;; Otherwise, delete window if the user so wishes.
	(when (and (minimap-get-window)
		   minimap-automatically-delete-window)
	  ;; We wait a tiny bit before deleting the window, since we
	  ;; might only be temporarily in another buffer.
	  (run-with-timer 0.3 nil
			  (lambda ()
			    (when (and (null (minimap-active-current-buffer-p))
				       (minimap-get-window))
			      (delete-window (minimap-get-window))))))))))

;;; Overlay movement

(defun minimap-move-overlay-mouse (start-event)
  "Move overlay by tracking mouse movement."
  (interactive "e")
  (mouse-set-point start-event)
  (when (get-buffer-window (buffer-base-buffer (current-buffer)))
    (let* ((echo-keystrokes 0)
	   (end-posn (event-end start-event))
	   (start-point (posn-point end-posn))
	   (make-cursor-line-fully-visible nil)
	   (cursor-type nil)
	   (minimap-automatically-delete-window nil)
	   (pcselmode (when (boundp 'pc-selection-mode)
			pc-selection-mode))
           pt ev)
      (when (and pcselmode (fboundp 'pc-selection-mode))
	(pc-selection-mode -1))
      (move-overlay minimap-active-overlay start-point minimap-end)
      (track-mouse
	(minimap-set-overlay start-point)
	(while (and
		(consp (setq ev (read-event)))
		(eq (car ev) 'mouse-movement))
	  (setq pt (posn-point (event-start ev)))
	  (when (numberp pt)
	    (goto-char pt)
	    (beginning-of-line)
	    (minimap-set-overlay (point)))))
      (select-window (get-buffer-window (buffer-base-buffer)))
      (minimap-update)
      (when (and pcselmode (fboundp 'pc-selection-mode))
	(pc-selection-mode 1)))))

(defun minimap-set-overlay (pt)
  "Set overlay position, with PT being the middle."
  (goto-char pt)
  (let* ((ovstartline (line-number-at-pos minimap-start))
	 (ovendline (line-number-at-pos minimap-end))
	 (ovheight (round (/ (- ovendline ovstartline) 2)))
	 (line (line-number-at-pos))
	 (winstart (window-start))
	 (winend (window-end))
	 newstart newend)
    (setq pt (point-at-bol))
    (setq newstart (minimap-line-to-pos (- line ovheight)))
    ;; Perform recentering
    (minimap-recenter line ovheight)
    ;; Set new position in main buffer and redisplay
    (with-selected-window (get-buffer-window (buffer-base-buffer))
      (goto-char pt)
      (set-window-start nil newstart)
      (redisplay t)
      (setq newend (window-end)))
    (when (eq minimap-recenter-type 'free)
      (while (> newend winend)
	(scroll-up 5)
	(redisplay t)
	(setq winend (window-end))))
    (move-overlay minimap-active-overlay newstart newend)))

(defun minimap-line-to-pos (line)
  "Return point position of line number LINE."
  (save-excursion
    (goto-char 1)
    (if (eq selective-display t)
	(re-search-forward "[\n\C-m]" nil 'end (1- line))
      (forward-line (1- line)))
    (point)))

(defun minimap-recenter (middle height)
  "Recenter the minimap according to `minimap-recenter-type'.
MIDDLE is the line number in the middle of the active region.
HEIGHT is the number of lines from MIDDLE to begin/end of the
active region."
  (cond
   ;; Relative recentering
   ((eq minimap-recenter-type 'relative)
    (let* ((maxlines (line-number-at-pos (point-max)))
	   percentage relpos newline start numlines)
      (setq numlines (count-lines (window-start) (window-end)))
      (setq percentage (/ (float middle) (float maxlines)))
      (setq newline (ceiling (* percentage numlines)))
      (setq start (minimap-line-to-pos
		   (- middle height
		      (floor (* percentage
				(- numlines height height))))))
      (or (> start (point-min))
	  (setq start (point-min)))
      ;; If (point-max) already visible, don't go further
      (if (and (> start (window-start))
	       (with-selected-window (get-buffer-window (buffer-base-buffer))
		 (= (point-max) (window-end))))
	  (save-excursion
	    (goto-char (point-max))
	    (recenter -1))
	(unless (and (> start (window-start))
		     (= (point-max) (window-end)))
	  (set-window-start nil start)))))
   ;; Middle recentering
    ((eq minimap-recenter-type 'middle)
     (let ((start (- middle height
		     (floor (* 0.5
			       (- minimap-numlines height height))))))
       (if (< start 1)
	   (progn
	     ;; Hack: Emacs cannot scroll down any further, so we fake
	     ;; it using an overlay.  Otherwise, the active region
	     ;; would move to the top.
	     (overlay-put minimap-pointmin-overlay
			  'display (concat
				    (make-string (abs start) 10)
				    (buffer-substring (point-min) (1+ (point-min)))))
	     (overlay-put minimap-pointmin-overlay
			  'face `(:background ,(face-background 'default)))
	     (overlay-put minimap-pointmin-overlay
			  'priority 10)
	     (setq start 1))
	 (overlay-put minimap-pointmin-overlay 'display "")
	 (overlay-put minimap-pointmin-overlay 'face nil))
       (set-window-start nil (minimap-line-to-pos start))))
    ;; Free recentering
    ((eq minimap-recenter-type 'free)
     (let ((newstart (minimap-line-to-pos (- middle height)))
	   (winstart (window-start)))
       (while (< newstart winstart)
	 (scroll-down 5)
	 (redisplay t)
	 (setq winstart (window-start)))))))

;;; Minimap minor mode

 (defvar minimap-sb-mode-map (make-sparse-keymap)
  "Keymap used by `minimap-sb-mode'.")

(define-key minimap-sb-mode-map [down-mouse-1] 'minimap-move-overlay-mouse)
(define-key minimap-sb-mode-map [down-mouse-2] 'minimap-move-overlay-mouse)
(define-key minimap-sb-mode-map [down-mouse-3] 'minimap-move-overlay-mouse)

(define-minor-mode minimap-sb-mode
  "Minor mode for minimap sidebar."
  nil "minimap" minimap-sb-mode-map)

;;; Sync minimap with modes which create/delete overlays.

(defun minimap-sync-overlays ()
  "Synchronize overlays between base and minimap buffer.
Apply semantic overlays or face enlargement if necessary."
  (interactive)
  ;; Get overlays and Semantic status from base buffer.
  (when (and minimap-mode
	     (minimap-active-current-buffer-p))
    (with-current-buffer minimap-active-buffer
      (let ((baseov (overlays-in (point-min) (point-max)))
	    (semantic (and (boundp 'semantic-version)
			   (semantic-active-p)))
	    ov props p)
	;; Apply overlays to minimap.
	(with-current-buffer minimap-buffer-name
	  ;; Delete overlays (but keep our own).
	  (let ((ovs (overlays-in (point-min) (point-max))))
	    (dolist (ov ovs)
	      (unless (member ov (list minimap-pointmin-overlay
				       minimap-base-overlay
				       minimap-active-overlay))
		(delete-overlay ov))))
	  (while baseov
	    (when (and (eq (overlay-buffer (car baseov)) minimap-active-buffer)
		       (setq props (minimap-get-sync-properties (car baseov))))
	      (setq ov (make-overlay (overlay-start (car baseov))
				     (overlay-end (car baseov))))
	      (while (setq p (car props))
		(overlay-put ov (car p) (cadr p))
		(setq props (cdr props))))
	    (setq baseov (cdr baseov)))
	  (move-overlay minimap-pointmin-overlay (point-min) (1+ (point-min)))
	  ;; Re-apply font overlay
	  (move-overlay minimap-base-overlay (point-min) (point-max)))
	;; Face enlargement
	(when (and font-lock-mode
		   (or (eq minimap-enlarge-certain-faces 'always)
		       (and (eq minimap-enlarge-certain-faces 'as-fallback)
			    (or (not minimap-display-semantic-overlays)
				(not semantic)))))
	  (when (eq font-lock-support-mode 'jit-lock-mode)
	    (jit-lock-fontify-now))
	  (minimap-enlarge-faces))
	;; Semantic overlays
	(when (and semantic
		   minimap-display-semantic-overlays)
	  (minimap-apply-semantic-overlays t))))))

(defun minimap-get-sync-properties (ov)
  "Get properties from overlay OV which should be synced.
You can specify those properties with
`minimap-sync-overlay-properties'."
  (let ((syncprops minimap-sync-overlay-properties))
    (when minimap-tag-only
      (setq syncprops (delq 'face syncprops)))
    (delq nil
	  (mapcar
	   (lambda (p)
	     (let ((val (overlay-get ov p)))
	       (if val
		   (list p val)
		 nil)))
	   syncprops))))

(defun minimap-enlarge-faces ()
  "Apply default font to all faces in `minimap-normal-height-faces'."
  (let ((pos (next-single-property-change (point-min) 'face))
	next ov face)
    (while pos
      (setq face (get-text-property pos 'face))
      (when (and face
		 (member face minimap-normal-height-faces))
	(with-current-buffer minimap-buffer-name
	  (setq ov
		(make-overlay pos
			      (setq pos (next-single-property-change pos 'face))))
	  (overlay-put ov 'face `(:family ,(face-font 'default)))
	  (overlay-put ov 'priority 5)))
      (setq pos (next-single-property-change pos 'face)))))

(defun minimap-apply-semantic-overlays (tags)
  "Apply semantic overlays to the minimap.
TAGS is the list of tags.  If it is t, fetch tags from buffer."
  (when (and tags
	     minimap-mode)
    (with-current-buffer minimap-active-buffer
      (let (tag class ov ovnew)
	(when (eq tags t)
	  (setq tags (semantic-fetch-tags)))
	(while tags
	  (setq tag (car tags))
	  (setq class (semantic-tag-class tag))
	  (setq ov (semantic-tag-overlay tag))
	  (when (and (overlayp ov)
		     (or (eq class 'function)
			 (eq class 'type)
			 (eq class 'variable)))
	    (with-current-buffer minimap-buffer-name
	      (let* ((start (overlay-start ov))
		     (end (overlay-end ov))
		     (name (semantic-tag-name tag))
		     (lstart (line-number-at-pos start))
		     (lend (line-number-at-pos end)))
		;; First, remove old Semantic overlays.
		(remove-overlays start end 'minimap-semantic t)
	        (if minimap-tag-only
		    ;; Now put the new ones.
		    (overlay-put
		     (setq ovnew (make-overlay start end))
		     'face `(:background ,(face-background
					   (intern (format "minimap-semantic-%s-face"
							   (symbol-name class))))
					 :foreground
					 ,(face-background
					   (intern (format "minimap-semantic-%s-face"
							   (symbol-name class))))
					 ))
		  		    ;; Now put the new ones.
		    (overlay-put
		     (setq ovnew (make-overlay start end))
		     'face `(:background ,(face-background
					   (intern (format "minimap-semantic-%s-face"
							   (symbol-name class)))))))
		(overlay-put ovnew 'priority 4)
		(when (and (eq class 'function)
			   (> (- lend lstart) 5))
		  (overlay-put ovnew 'priority 1)
		  (overlay-put ovnew 'minimap-semantic t)
		  (overlay-put (setq ovnew (make-overlay start (progn (goto-char start) (point-at-eol))))
			       'display (make-string 200 ?\u203E))
		  (overlay-put ovnew 'minimap-semantic t)
		  (overlay-put ovnew 'face `(:foreground ,(face-foreground 'default) :overline nil))
		  (overlay-put ovnew 'priority 8)
		  (overlay-put (setq ovnew (make-overlay (progn (goto-char end) (point-at-bol)) end))
			       'display (make-string 200 ?_))
		  (overlay-put ovnew 'face `(:foreground ,(face-foreground 'default)))
		  (overlay-put ovnew 'minimap-semantic t)
		  (overlay-put ovnew 'priority 8))
		(setq start
		      (minimap-line-to-pos (/ (+ lstart lend) 2)))
		(goto-char start)
		(while (looking-at "^$")
		  (forward-line -1))
		(setq start (point))
		(setq end (progn (goto-char start) (point-at-eol)))
		(setq ovnew (make-overlay start end))
		(overlay-put ovnew 'face (format "minimap-semantic-%s-face"
						 (symbol-name class)))
		(overlay-put ovnew 'display (concat "  " name "  "))
		(overlay-put ovnew 'priority 7)
		(overlay-put ovnew 'minimap-semantic t)


		)))
	  (setq tags (cdr tags)))))))

(provide 'minimap)

;;; minimap.el ends here
