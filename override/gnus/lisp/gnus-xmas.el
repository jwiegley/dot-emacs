;;; gnus-xmas.el --- Gnus functions for XEmacs

;; Copyright (C) 1995-2014 Free Software Foundation, Inc.

;; Author: Lars Magne Ingebrigtsen <larsi@gnus.org>
;; Keywords: news

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(eval-when-compile
  (autoload 'gnus-active "gnus" nil nil 'macro)
  (autoload 'gnus-group-entry "gnus" nil nil 'macro)
  (autoload 'gnus-info-level "gnus" nil nil 'macro)
  (autoload 'gnus-info-marks "gnus" nil nil 'macro)
  (autoload 'gnus-info-method "gnus" nil nil 'macro)
  (autoload 'gnus-info-score "gnus" nil nil 'macro))

(require 'text-props)
(defvar menu-bar-mode (featurep 'menubar))
(require 'messagexmas)
(require 'wid-edit)
(require 'gnus-util)

(defgroup gnus-xmas nil
  "XEmacsoid support for Gnus"
  :group 'gnus)

(defcustom gnus-xmas-glyph-directory nil
  "Directory where Gnus logos and icons are located.
If this variable is nil, Gnus will try to locate the directory
automatically."
  :type '(choice (const :tag "autodetect" nil)
		 directory)
  :group 'gnus-xmas)

(unless gnus-xmas-glyph-directory
  (unless (setq gnus-xmas-glyph-directory
		(message-xmas-find-glyph-directory "gnus"))
    (error "Can't find glyph directory. \
Possibly the `etc' directory has not been installed.")))

;;; Internal variables.

;; Don't warn about these undefined variables.

;;defined in gnus.el
(defvar gnus-active-hashtb)
(defvar gnus-article-buffer)
(defvar gnus-auto-center-summary)
(defvar gnus-current-headers)
(defvar gnus-level-killed)
(defvar gnus-level-zombie)
(defvar gnus-newsgroup-bookmarks)
(defvar gnus-newsgroup-dependencies)
(defvar gnus-newsgroup-selected-overlay)
(defvar gnus-newsrc-hashtb)
(defvar gnus-read-mark)
(defvar gnus-refer-article-method)
(defvar gnus-reffed-article-number)
(defvar gnus-unread-mark)
(defvar gnus-version)
(defvar gnus-view-pseudos)
(defvar gnus-view-pseudos-separately)
(defvar gnus-visual)
(defvar gnus-zombie-list)
;;defined in gnus-msg.el
(defvar gnus-article-copy)
(defvar gnus-check-before-posting)
;;defined in gnus-vis.el
(defvar gnus-article-button-face)
(defvar gnus-article-mouse-face)
(defvar gnus-summary-selected-face)
(defvar gnus-group-reading-menu)
(defvar gnus-group-group-menu)
(defvar gnus-group-misc-menu)
(defvar gnus-summary-article-menu)
(defvar gnus-summary-thread-menu)
(defvar gnus-summary-misc-menu)
(defvar gnus-summary-post-menu)
(defvar gnus-summary-kill-menu)
(defvar gnus-article-article-menu)
(defvar gnus-article-treatment-menu)
(defvar gnus-mouse-2)
(defvar standard-display-table)
(defvar gnus-tree-minimize-window)
;;`gnus-agent-mode' in gnus-agent.el will define it.
(defvar gnus-agent-summary-mode)
(defvar gnus-draft-mode)

(defcustom gnus-xmas-force-redisplay nil
  "*If non-nil, force a redisplay before recentering the summary buffer.
This is ugly, but it works around a bug in `window-displayed-height'."
  :type 'boolean
  :group 'gnus-xmas)

(defun gnus-xmas-switch-horizontal-scrollbar-off ()
  (when (featurep 'scrollbar)
    (set-specifier scrollbar-height (cons (current-buffer) 0))))

(defun gnus-xmas-summary-recenter ()
  "\"Center\" point in the summary window.
If `gnus-auto-center-summary' is nil, or the article buffer isn't
displayed, no centering will be performed."
  ;; Suggested by earle@mahendo.JPL.NASA.GOV (Greg Earle).
  ;; Recenter only when requested.  Suggested by popovich@park.cs.columbia.edu.
  ;; Force redisplay to get properly computed window height.
  (when gnus-xmas-force-redisplay
    (sit-for 0))
  (when gnus-auto-center-summary
    (let* ((height (if (fboundp 'window-displayed-height)
		       (window-displayed-height)
		     (- (window-height) 2)))
	   (top (cond ((< height 4) 0)
		      ((< height 7) 1)
		      (t (if (numberp gnus-auto-center-summary)
			     gnus-auto-center-summary
			   2))))
	   (bottom (save-excursion (goto-char (point-max))
				   (forward-line (- height))
				   (point)))
	   (window (get-buffer-window (current-buffer))))
      (when (get-buffer-window gnus-article-buffer)
	;; Only do recentering when the article buffer is displayed,
	;; Set the window start to either `bottom', which is the biggest
	;; possible valid number, or the second line from the top,
	;; whichever is the least.
	;; NOFORCE parameter suggested by Daniel Pittman <daniel@danann.net>.
	(set-window-start
	 window (min bottom (save-excursion (forward-line (- top)) (point)))
	 t))
      ;; Do horizontal recentering while we're at it.
      (when (and (get-buffer-window (current-buffer) t)
		 (not (eq gnus-auto-center-summary 'vertical)))
	(let ((selected (selected-window)))
	  (select-window (get-buffer-window (current-buffer) t))
	  (gnus-summary-position-point)
	  (gnus-horizontal-recenter)
	  (select-window selected))))))

(defun gnus-xmas-summary-set-display-table ()
  ;; Setup the display table -- like `gnus-summary-setup-display-table',
  ;; but done in an XEmacsish way.
  (let ((table (make-display-table))
	(i 32))
    ;; Nix out all the control chars...
    (while (>= (setq i (1- i)) 0)
      (gnus-put-display-table i [??] table))
    ;; ... but not newline and cr, of course.  (cr is necessary for the
    ;; selective display).
    (gnus-put-display-table ?\n nil table)
    (gnus-put-display-table ?\r nil table)
    ;; We keep TAB as well.
    (gnus-put-display-table ?\t nil table)
    ;; We nix out any glyphs over 126 below ctl-arrow.
    (let ((i (if (integerp ctl-arrow) ctl-arrow 160)))
      (while (>= (setq i (1- i)) 127)
	(unless (gnus-get-display-table i table)
	  (gnus-put-display-table i [??] table))))
    ;; Can't use `set-specifier' because of a bug in 19.14 and earlier
    (add-spec-to-specifier current-display-table table (current-buffer) nil)))

(defun gnus-xmas-add-text-properties (start end props &optional object)
  (add-text-properties start end props object)
  (put-text-property start end 'start-closed nil object))

(defun gnus-xmas-put-text-property (start end prop value &optional object)
  (put-text-property start end prop value object)
  (put-text-property start end 'start-closed nil object))

(defun gnus-xmas-extent-start-open (point)
  (map-extents (lambda (extent arg)
		 (set-extent-property extent 'start-open t))
	       nil point (min (1+ (point)) (point-max))))

(defun gnus-xmas-article-push-button (event)
  "Check text under the mouse pointer for a callback function.
If the text under the mouse pointer has a `gnus-callback' property,
call it with the value of the `gnus-data' text property."
  (interactive "e")
  (set-buffer (window-buffer (event-window event)))
  (let* ((pos (event-closest-point event))
	 (data (get-text-property pos 'gnus-data))
	 (fun (get-text-property pos 'gnus-callback)))
    (goto-char pos)
    (when fun
      (funcall fun data))))

(defun gnus-xmas-move-overlay (extent start end &optional buffer)
  (set-extent-endpoints extent start end buffer))

(defun gnus-xmas-kill-all-overlays ()
  "Delete all extents in the current buffer."
  (map-extents (lambda (extent ignore)
		 (delete-extent extent)
		 nil)))

(defun gnus-xmas-overlays-at (pos)
  "Return a list of the extents that contain the character at POS."
  (mapcar-extents #'identity nil nil pos (1+ pos)))

(defun gnus-xmas-overlays-in (beg end)
  "Return a list of the extents that overlap the region BEG ... END."
  (mapcar-extents #'identity nil nil beg end))

(defun gnus-xmas-window-top-edge (&optional window)
  (nth 1 (window-pixel-edges window)))

(defun gnus-xmas-tree-minimize ()
  (when (and gnus-tree-minimize-window
	     (not (one-window-p)))
    (let* ((window-min-height 2)
	   (height (1+ (count-lines (point-min) (point-max))))
	   (min (max (1- window-min-height) height))
	   (tot (if (numberp gnus-tree-minimize-window)
		    (min gnus-tree-minimize-window min)
		  min))
	   (win (get-buffer-window (current-buffer)))
	   (wh (and win (1- (window-height win)))))
      (when (and win
		 (not (eq tot wh)))
	(let ((selected (selected-window)))
	  (select-window win)
	  (enlarge-window (- tot wh))
	  (select-window selected))))))

;; Select the lowest window on the frame.
(defun gnus-xmas-select-lowest-window ()
  (let* ((lowest-window (selected-window))
	 (bottom-edge (car (cdr (cdr (cdr (window-pixel-edges))))))
	 (last-window (previous-window))
	 (window-search t))
    (while window-search
      (let* ((this-window (next-window))
	     (next-bottom-edge (car (cdr (cdr (cdr
					       (window-pixel-edges
						this-window)))))))
	(when (< bottom-edge next-bottom-edge)
	  (setq bottom-edge next-bottom-edge)
	  (setq lowest-window this-window))

	(select-window this-window)
	(when (eq last-window this-window)
	  (select-window lowest-window)
	  (setq window-search nil))))))

(defmacro gnus-xmas-menu-add (type &rest menus)
  `(gnus-xmas-menu-add-1 ',type ',menus))
(put 'gnus-xmas-menu-add 'lisp-indent-function 1)

(defun gnus-xmas-menu-add-1 (type menus)
  (when (and menu-bar-mode
	     (gnus-visual-p (intern (format "%s-menu" type)) 'menu))
    (while menus
      (easy-menu-add (symbol-value (pop menus))))))

(defun gnus-xmas-group-menu-add ()
  (gnus-xmas-menu-add group
    gnus-group-reading-menu gnus-group-group-menu gnus-group-misc-menu))

(defun gnus-xmas-summary-menu-add ()
  (gnus-xmas-menu-add summary
    gnus-summary-misc-menu gnus-summary-kill-menu
    gnus-summary-article-menu gnus-summary-thread-menu
    gnus-summary-post-menu ))

(defun gnus-xmas-article-menu-add ()
  (gnus-xmas-menu-add article
    gnus-article-article-menu gnus-article-treatment-menu
    gnus-article-post-menu gnus-article-commands-menu))

(defun gnus-xmas-score-menu-add ()
  (gnus-xmas-menu-add score
    gnus-score-menu))

(defun gnus-xmas-pick-menu-add ()
  (gnus-xmas-menu-add pick
    gnus-pick-menu))

(defun gnus-xmas-topic-menu-add ()
  (gnus-xmas-menu-add topic
    gnus-topic-menu))

(defun gnus-xmas-binary-menu-add ()
  (gnus-xmas-menu-add binary
    gnus-binary-menu))

(defun gnus-xmas-agent-summary-menu-add ()
  (gnus-xmas-menu-add agent-summary
    gnus-agent-summary-menu))

(defun gnus-xmas-agent-group-menu-add ()
  (gnus-xmas-menu-add agent-group
    gnus-agent-group-menu))

(defun gnus-xmas-agent-server-menu-add ()
  (gnus-xmas-menu-add agent-server
    gnus-agent-server-menu))

(defun gnus-xmas-tree-menu-add ()
  (gnus-xmas-menu-add tree
    gnus-tree-menu))

(defun gnus-xmas-draft-menu-add ()
  (gnus-xmas-menu-add draft
    gnus-draft-menu))

(defun gnus-xmas-server-menu-add ()
  (gnus-xmas-menu-add menu
    gnus-server-server-menu gnus-server-connections-menu))

(defun gnus-xmas-browse-menu-add ()
  (gnus-xmas-menu-add browse
    gnus-browse-menu))

(defun gnus-xmas-read-event-char (&optional prompt)
  "Get the next event."
  (when prompt
    (display-message 'no-log (format "%s" prompt)))
  (let ((event (next-command-event)))
    (sit-for 0)
    ;; We junk all non-key events.  Is this naughty?
    (while (not (or (key-press-event-p event)
		    (button-press-event-p event)))
      (dispatch-event event)
      (setq event (next-command-event)))
    (cons (and (key-press-event-p event)
	       (event-to-character event))
	  event)))

(defun gnus-xmas-article-describe-bindings (&optional prefix)
  "Show a list of all defined keys, and their definitions.
The optional argument PREFIX, if non-nil, should be a key sequence;
then we display only bindings that start with that prefix."
  (interactive)
  (gnus-article-check-buffer)
  (let ((keymap (copy-keymap gnus-article-mode-map))
	(map (copy-keymap gnus-article-send-map))
	(sumkeys (where-is-internal 'gnus-article-read-summary-keys))
	parent agent draft)
    (define-key keymap "S" map)
    (set-keymap-default-binding map nil)
    (with-current-buffer gnus-article-current-summary
      (set-keymap-parent
       keymap
       (if (setq parent (keymap-parent gnus-article-mode-map))
	   (prog1
	       (setq parent (copy-keymap parent))
	     (set-keymap-parent parent (current-local-map)))
	 (current-local-map)))
      (let ((def (key-binding "S"))
	    gnus-pick-mode)
	(set-keymap-parent map (if (symbolp def)
				   (symbol-value def)
				 def))
	(dolist (key sumkeys)
	  (when (setq def (key-binding key))
	    (define-key keymap key def))))
      (when (boundp 'gnus-agent-summary-mode)
	(setq agent gnus-agent-summary-mode))
      (when (boundp 'gnus-draft-mode)
	(setq draft gnus-draft-mode)))
    (with-temp-buffer
      (setq major-mode 'gnus-article-mode)
      (use-local-map keymap)
      (set (make-local-variable 'gnus-agent-summary-mode) agent)
      (set (make-local-variable 'gnus-draft-mode) draft)
      (describe-bindings prefix))))

(defun gnus-xmas-define ()
  (setq gnus-mouse-2 [button2])
  (setq gnus-mouse-3 [button3])
  (setq gnus-widget-button-keymap widget-button-keymap)

  (unless (memq 'underline (face-list))
    (and (fboundp 'make-face)
	 (funcall (intern "make-face") 'underline)))
  ;; Must avoid calling set-face-underline-p directly, because it
  ;; is a defsubst in emacs19, and will make the .elc files non
  ;; portable!
  (unless (face-differs-from-default-p 'underline)
    (funcall (intern "set-face-underline-p") 'underline t))

  (defalias 'gnus-make-overlay
    (lambda (beg end &optional buffer front-advance rear-advance)
      "Create a new overlay with range BEG to END in BUFFER.
FRONT-ADVANCE and REAR-ADVANCE are ignored."
      (make-extent beg end buffer)))

  (defalias 'gnus-copy-overlay 'copy-extent)
  (defalias 'gnus-delete-overlay 'delete-extent)
  (defalias 'gnus-overlay-get 'extent-property)
  (defalias 'gnus-overlay-put 'set-extent-property)
  (defalias 'gnus-move-overlay 'gnus-xmas-move-overlay)
  (defalias 'gnus-overlay-buffer 'extent-object)
  (defalias 'gnus-overlay-start 'extent-start-position)
  (defalias 'gnus-overlay-end 'extent-end-position)
  (defalias 'gnus-overlays-at 'gnus-xmas-overlays-at)
  (defalias 'gnus-overlays-in 'gnus-xmas-overlays-in)
  (defalias 'gnus-kill-all-overlays 'gnus-xmas-kill-all-overlays)
  (defalias 'gnus-extent-detached-p 'extent-detached-p)
  (defalias 'gnus-add-text-properties 'gnus-xmas-add-text-properties)
  (defalias 'gnus-put-text-property 'gnus-xmas-put-text-property)
  (defalias 'gnus-deactivate-mark 'ignore)
  (defalias 'gnus-window-edges 'window-pixel-edges)
  (defalias 'gnus-assq-delete-all 'gnus-xmas-assq-delete-all)

  (unless (fboundp 'member-ignore-case)
    (defun member-ignore-case (elt list)
      (while (and list
		  (or (not (stringp (car list)))
		      (not (string= (downcase elt) (downcase (car list))))))
	(setq list (cdr list)))
      list))

  (unless (boundp 'standard-display-table)
    (setq standard-display-table nil))

  (defvar gnus-mouse-face-prop 'highlight)

  (unless (fboundp 'match-string-no-properties)
    (defalias 'match-string-no-properties 'match-string))

  (unless (fboundp 'char-width)
    (defalias 'char-width (lambda (ch) 1))))

(defun gnus-xmas-redefine ()
  "Redefine lots of Gnus functions for XEmacs."
  (defalias 'gnus-summary-set-display-table 'gnus-xmas-summary-set-display-table)
  (defalias 'gnus-visual-turn-off-edit-menu 'identity)
  (defalias 'gnus-summary-recenter 'gnus-xmas-summary-recenter)
  (defalias 'gnus-extent-start-open 'gnus-xmas-extent-start-open)
  (defalias 'gnus-article-push-button 'gnus-xmas-article-push-button)
  (defalias 'gnus-window-top-edge 'gnus-xmas-window-top-edge)
  (defalias 'gnus-read-event-char 'gnus-xmas-read-event-char)
  (defalias 'gnus-group-startup-message 'gnus-xmas-group-startup-message)
  (defalias 'gnus-tree-minimize 'gnus-xmas-tree-minimize)
  (defalias 'gnus-select-lowest-window
    'gnus-xmas-select-lowest-window)
  (defalias 'gnus-mail-strip-quoted-names 'gnus-xmas-mail-strip-quoted-names)
  (defalias 'gnus-character-to-event 'character-to-event)
  (defalias 'gnus-mode-line-buffer-identification
    'gnus-xmas-mode-line-buffer-identification)
  (defalias 'gnus-key-press-event-p 'key-press-event-p)
  (defalias 'gnus-region-active-p 'region-active-p)
  (defalias 'gnus-mark-active-p 'region-exists-p)
  (defalias 'gnus-annotation-in-region-p 'gnus-xmas-annotation-in-region-p)
  (defalias 'gnus-mime-button-menu 'gnus-xmas-mime-button-menu)
  (defalias 'gnus-mime-security-button-menu
    'gnus-xmas-mime-security-button-menu)
  (defalias 'gnus-image-type-available-p 'gnus-xmas-image-type-available-p)
  (defalias 'gnus-put-image 'gnus-xmas-put-image)
  (defalias 'gnus-create-image 'gnus-xmas-create-image)
  (defalias 'gnus-remove-image 'gnus-xmas-remove-image)
  (defalias 'gnus-article-describe-bindings
    'gnus-xmas-article-describe-bindings)

  ;; These ones are not defcutom'ed, sometimes not even defvar'ed. They
  ;; probably should. If that is done, the code below should then be moved
  ;; where each variable is defined, in order not to mess with user settings.
  ;; -- didier
  (add-hook 'gnus-score-mode-hook 'gnus-xmas-score-menu-add)
  (add-hook 'gnus-binary-mode-hook 'gnus-xmas-binary-menu-add)
  (add-hook 'gnus-server-mode-hook 'gnus-xmas-server-menu-add)
  (add-hook 'gnus-browse-mode-hook 'gnus-xmas-browse-menu-add)
  (add-hook 'gnus-draft-mode-hook 'gnus-xmas-draft-menu-add)
  (add-hook 'gnus-mailing-list-mode-hook 'gnus-xmas-mailing-list-menu-add))


;;; XEmacs logo and toolbar.

(defun gnus-xmas-group-startup-message (&optional x y)
  "Insert startup message in current buffer."
  ;; Insert the message.
  (erase-buffer)
  (cond
   ((and (console-on-window-system-p)
	 (or (featurep 'xpm)
	     (featurep 'xbm)))
    (let* ((logo-xpm (expand-file-name "gnus.xpm" gnus-xmas-glyph-directory))
	   (logo-xbm (expand-file-name "gnus.xbm" gnus-xmas-glyph-directory))
	   (glyph (make-glyph
		   (cond ((featurep 'xpm)
			  `[xpm
			    :file ,logo-xpm
			    :color-symbols
			    (("thing" . ,(car gnus-logo-colors))
			     ("shadow" . ,(cadr gnus-logo-colors))
			     ("oort" . "#eeeeee")
			     ("background" . ,(face-background 'default)))])
			 ((featurep 'xbm)
			  `[xbm :file ,logo-xbm])
			 (t [nothing])))))
      (insert " ")
      (set-extent-begin-glyph (make-extent (point) (point)) glyph)
      (goto-char (point-min))
      (while (not (eobp))
	(insert (make-string (/ (max (- (window-width) (or x 35)) 0) 2)
			     ?\ ))
	(forward-line 1)))
    (goto-char (point-min))
    (let* ((pheight (+ 20 (count-lines (point-min) (point-max))))
	   (wheight (window-height))
	   (rest (- wheight pheight)))
      (insert (make-string (max 0 (* 2 (/ rest 3))) ?\n))))
   (t
    (insert
     (format "              %s
          _    ___ _             _
          _ ___ __ ___  __    _ ___
          __   _     ___    __  ___
              _           ___     _
             _  _ __             _
             ___   __            _
                   __           _
                    _      _   _
                   _      _    _
                      _  _    _
                  __  ___
                 _   _ _     _
                _   _
              _    _
             _    _
            _
          __

"
	     ""))
    ;; And then hack it.
    (gnus-indent-rigidly (point-min) (point-max)
			 (/ (max (- (window-width) (or x 46)) 0) 2))
    (goto-char (point-min))
    (forward-line 1)
    (let* ((pheight (count-lines (point-min) (point-max)))
	   (wheight (window-height))
	   (rest (- wheight pheight)))
      (insert (make-string (max 0 (* 2 (/ rest 3))) ?\n)))
    ;; Paint it.
    (put-text-property (point-min) (point-max) 'face 'gnus-splash)))
  (setq modeline-buffer-identification
	(list (concat gnus-version ": *Group*")))
  (set-buffer-modified-p t))


;;; The toolbar.

(defun gnus-xmas-update-toolbars ()
  "Update the toolbars' appearance."
  (when (and (not noninteractive)
	     (featurep 'gnus-xmas))
    (save-excursion
      (dolist (buffer (buffer-list))
	(set-buffer buffer)
	(cond ((eq major-mode 'gnus-group-mode)
	       (gnus-xmas-setup-group-toolbar))
	      ((eq major-mode 'gnus-summary-mode)
	       (gnus-xmas-setup-summary-toolbar)))))))

(defcustom gnus-use-toolbar (if (featurep 'toolbar) 'default)
  "*Position to display the toolbar.  Nil means do not use a toolbar.
If it is non-nil, it should be one of the symbols `default', `top',
`bottom', `right', and `left'.  `default' means to use the default
toolbar, the rest mean to display the toolbar on the place which those
names show."
  :type '(choice (const default)
		 (const top) (const bottom) (const left) (const right)
		 (const :tag "no toolbar" nil))
  :set (lambda (symbol value)
	 (set-default
	  symbol
	  (if (or (not value)
		  (memq value (list 'default 'top 'bottom 'right 'left)))
	      value
	    'default))
	 (gnus-xmas-update-toolbars))
  :group 'gnus-xmas)

(defcustom gnus-toolbar-thickness
  (if (featurep 'toolbar)
      (cons (specifier-instance default-toolbar-height)
	    (specifier-instance default-toolbar-width)))
  "*Cons of the height and the width specifying the thickness of a toolbar.
The height is used for the toolbar displayed on the top or the bottom,
the width is used for the toolbar displayed on the right or the left."
  :type '(cons :tag "height & width"
	       (integer :tag "height") (integer :tag "width"))
  :set (lambda (symbol value)
	 (set-default
	  symbol
	  (if (and (consp value) (natnump (car value)) (natnump (cdr value)))
	      value
	    '(37 . 40)))
	 (gnus-xmas-update-toolbars))
  :group 'gnus-xmas)

(defvar gnus-group-toolbar
  '([gnus-group-get-new-news gnus-group-get-new-news t "Get new news"]
    [gnus-group-get-new-news-this-group
     gnus-group-get-new-news-this-group t "Get new news in this group"]
    [gnus-group-catchup-current
     gnus-group-catchup-current t "Catchup group"]
    [gnus-group-describe-group
     gnus-group-describe-group t "Describe group"]
    [gnus-group-unsubscribe gnus-group-unsubscribe t "Unsubscribe group"]
    [gnus-group-subscribe gnus-group-subscribe t "Subscribe group"]
    [gnus-group-kill-group gnus-group-kill-group t "Kill group"]
    [gnus-summary-mail-save
     gnus-group-save-newsrc t "Save .newsrc files"] ; borrowed icon.
    [gnus-group-exit gnus-group-exit t "Exit Gnus"])
  "The group buffer toolbar.")

(defvar gnus-summary-toolbar
  '([gnus-summary-prev-unread
     gnus-summary-prev-page-or-article t "Page up"]
    [gnus-summary-next-unread
     gnus-summary-next-page t "Page down"]
    [gnus-summary-post-news
     gnus-summary-post-news t "Post an article"]
    [gnus-summary-followup-with-original
     gnus-summary-followup-with-original t
     "Post a followup and yank the original"]
    [gnus-summary-followup
     gnus-summary-followup t "Post a followup"]
    [gnus-summary-reply-with-original
     gnus-summary-reply-with-original t "Mail a reply and yank the original"]
    [gnus-summary-reply
     gnus-summary-reply t "Mail a reply"]
    [gnus-summary-caesar-message
     gnus-summary-caesar-message t "Rot 13"]
    [gnus-uu-decode-uu
     gnus-uu-decode-uu t "Decode uuencoded articles"]
    [gnus-summary-save-article-file
     gnus-summary-save-article-file t "Save article in file"]
    [gnus-summary-save-article
     gnus-summary-save-article t "Save article"]
    [gnus-uu-post-news
     gnus-uu-post-news t "Post a uuencoded article"]
    [gnus-summary-cancel-article
     gnus-summary-cancel-article t "Cancel article"]
    [gnus-summary-catchup
     gnus-summary-catchup t "Catchup"]
    [gnus-summary-catchup-and-exit
     gnus-summary-catchup-and-exit t "Catchup and exit"]
    [gnus-summary-exit gnus-summary-exit t "Exit this summary"])
  "The summary buffer toolbar.")

(defvar gnus-summary-mail-toolbar
  '(
    [gnus-summary-prev-unread
     gnus-summary-prev-unread-article t "Prev unread article"]
    [gnus-summary-next-unread
     gnus-summary-next-unread-article t "Next unread article"]
    [gnus-summary-mail-reply gnus-summary-reply t "Reply"]
    [gnus-summary-mail-originate gnus-summary-post-news t "Originate"]
    [gnus-summary-mail-save gnus-summary-save-article t "Save"]
    [gnus-summary-mail-copy gnus-summary-copy-article t "Copy message"]
    [gnus-summary-mail-forward gnus-summary-mail-forward t "Forward message"]
    [gnus-summary-caesar-message
     gnus-summary-caesar-message t "Rot 13"]
    [gnus-uu-decode-uu
     gnus-uu-decode-uu t "Decode uuencoded articles"]
    [gnus-summary-save-article-file
     gnus-summary-save-article-file t "Save article in file"]
    [gnus-summary-save-article
     gnus-summary-save-article t "Save article"]
    [gnus-summary-cancel-article ; usenet : cancellation :: mail : deletion.
     gnus-summary-delete-article t "Delete message"]
    [gnus-summary-catchup
     gnus-summary-catchup t "Catchup"]
    [gnus-summary-catchup-and-exit
     gnus-summary-catchup-and-exit t "Catchup and exit"]
    [gnus-summary-exit gnus-summary-exit t "Exit this summary"])
  "The summary buffer mail toolbar.")

(defun gnus-xmas-setup-toolbar (toolbar)
  (when (featurep 'toolbar)
    (if (and gnus-use-toolbar
	     (message-xmas-setup-toolbar toolbar nil "gnus"))
	(let ((bar (or (intern-soft (format "%s-toolbar" gnus-use-toolbar))
		       'default-toolbar))
	      (height (car gnus-toolbar-thickness))
	      (width (cdr gnus-toolbar-thickness))
	      (cur (current-buffer))
	      bars)
	  (set-specifier (symbol-value bar) toolbar cur)
	  (set-specifier default-toolbar-height height cur)
	  (set-specifier default-toolbar-width width cur)
	  (set-specifier top-toolbar-height height cur)
	  (set-specifier bottom-toolbar-height height cur)
	  (set-specifier right-toolbar-width width cur)
	  (set-specifier left-toolbar-width width cur)
	  (if (eq bar 'default-toolbar)
	      (progn
		(remove-specifier default-toolbar-visible-p cur)
		(remove-specifier top-toolbar cur)
		(remove-specifier top-toolbar-visible-p cur)
		(remove-specifier bottom-toolbar cur)
		(remove-specifier bottom-toolbar-visible-p cur)
		(remove-specifier right-toolbar cur)
		(remove-specifier right-toolbar-visible-p cur)
		(remove-specifier left-toolbar cur)
		(remove-specifier left-toolbar-visible-p cur))
	    (set-specifier (symbol-value (intern (format "%s-visible-p" bar)))
			   t cur)
	    (setq bars (delq bar (list 'default-toolbar
				       'bottom-toolbar 'top-toolbar
				       'right-toolbar 'left-toolbar)))
	    (while bars
	      (set-specifier (symbol-value (intern (format "%s-visible-p"
							   (pop bars))))
			     nil cur))))
      (let ((cur (current-buffer)))
	(set-specifier default-toolbar-visible-p nil cur)
	(set-specifier top-toolbar-visible-p nil cur)
	(set-specifier bottom-toolbar-visible-p nil cur)
	(set-specifier right-toolbar-visible-p nil cur)
	(set-specifier left-toolbar-visible-p nil cur)))))

(defun gnus-xmas-setup-group-toolbar ()
  (gnus-xmas-setup-toolbar gnus-group-toolbar))

(defun gnus-xmas-setup-summary-toolbar ()
  (gnus-xmas-setup-toolbar (if (gnus-news-group-p gnus-newsgroup-name)
			       gnus-summary-toolbar
			     gnus-summary-mail-toolbar)))

(defun gnus-xmas-mail-strip-quoted-names (address)
  "Protect mail-strip-quoted-names from nil input.
XEmacs compatibility workaround."
  (if (null address)
      nil
    (mail-strip-quoted-names address)))

(defvar gnus-xmas-modeline-left-extent
  (let ((ext (copy-extent modeline-buffer-id-left-extent)))
    ext))

(defvar gnus-xmas-modeline-right-extent
  (let ((ext (copy-extent modeline-buffer-id-right-extent)))
    ext))

(defvar gnus-xmas-modeline-glyph
  (progn
    (let* ((file-xpm (expand-file-name "gnus-pointer.xpm"
				       gnus-xmas-glyph-directory))
	   (file-xbm (expand-file-name "gnus-pointer.xbm"
				       gnus-xmas-glyph-directory))
	   (glyph (make-glyph
		   ;; Gag gag gag.
		   (cond ((featurep 'xpm)
			  ;; Let's try a nifty XPM
			  `[xpm :file ,file-xpm])
			 ((featurep 'xbm)
			  ;; Then a not-so-nifty XBM
			  `[xbm :file ,file-xbm])
			 ;; Then the simple string
			 (t [string :data "Gnus:"])))))
      (set-glyph-face glyph 'modeline-buffer-id)
      glyph)))

(defun gnus-xmas-mode-line-buffer-identification (line)
  (let ((line (car line))
	chop)
    (cond
     ;; This is some weird type of id.
     ((not (stringp line))
      (list line))
     ;; This is non-standard, so we just pass it through.
     ((not (string-match "^Gnus:" line))
      (list line))
     ;; We have a standard line, so we colorize and glyphize it a bit.
     (t
      (setq chop (match-end 0))
      (list
       (if gnus-xmas-modeline-glyph
	   (cons gnus-xmas-modeline-left-extent gnus-xmas-modeline-glyph)
	 (cons gnus-xmas-modeline-left-extent (substring line 0 chop)))
       (cons gnus-xmas-modeline-right-extent (substring line chop)))))))

(defun gnus-xmas-annotation-in-region-p (b e)
  (or (map-extents (lambda (e u) t) nil b e nil nil 'mm t)
      (if (= b e)
	  (eq (cadr (memq 'gnus-undeletable (text-properties-at b))) t)
	(text-property-any b e 'gnus-undeletable t))))

(defun gnus-xmas-mime-button-menu (event prefix)
  "Construct a context-sensitive menu of MIME commands."
  (interactive "e\nP")
  (let ((response (get-popup-menu-response
		   `("MIME Part"
		     ,@(mapcar (lambda (c) `[,(caddr c) ,(car c) t])
			       gnus-mime-button-commands)))))
    (set-buffer (event-buffer event))
    (goto-char (event-point event))
    (funcall (event-function response) (event-object response))))

(defun gnus-xmas-mime-security-button-menu (event prefix)
  "Construct a context-sensitive menu of security commands."
  (interactive "e\nP")
  (let ((response
	 (get-popup-menu-response
	  `("Security Part"
	    ,@(delq nil
		    (mapcar (lambda (c)
			      (unless (eq (car c) 'undefined)
				`[,(caddr c) ,(car c) t]))
			    gnus-mime-security-button-commands))))))
    (set-buffer (event-buffer event))
    (goto-char (event-point event))
    (funcall (event-function response) (event-object response))))

(defun gnus-xmas-mailing-list-menu-add ()
  (gnus-xmas-menu-add mailing-list
		      gnus-mailing-list-menu))

(defun gnus-xmas-image-type-available-p (type)
  (and (if (fboundp 'display-images-p)
	   (display-images-p)
	 window-system)
       (featurep (if (eq type 'pbm) 'xbm type))))

(defun gnus-xmas-create-image (file &optional type data-p &rest props)
  (let ((type (cond
	       (type
		(symbol-name type))
	       ((and (not data-p)
		     (string-match "[.]" file))
		(car (last (split-string file "[.]"))))))
	(face (plist-get props :face))
	glyph)
    (when (equal type "pbm")
      (with-temp-buffer
	(if data-p
	    (insert file)
	  (insert-file-contents-literally file))
	(shell-command-on-region (point-min) (point-max)
				 "ppmtoxpm 2>/dev/null" t)
	(setq file (buffer-string)
	      type "xpm"
	      data-p t)))
    (setq glyph
	  (if (equal type "xbm")
	      (make-glyph (list (cons 'x file)))
	    (with-temp-buffer
	      (if data-p
		  (insert file)
		(insert-file-contents-literally file))
	      (make-glyph
	       (vector
		(if type
		    (intern type)
		  (mm-image-type-from-buffer))
		:data (buffer-string))))))
    (when face
      (set-glyph-face glyph face))
    glyph))

(defun gnus-xmas-put-image (glyph &optional string category)
  "Insert STRING, but display GLYPH.
Warning: Don't insert text immediately after the image."
  (let ((begin (point))
	extent)
    (if (and (bobp) (not string))
	(setq string " "))
    (if string
	(insert string)
      (setq begin (1- begin)))
    (setq extent (make-extent begin (point)))
    (set-extent-property extent 'gnus-image category)
    (set-extent-property extent 'duplicable t)
    (if string
	(set-extent-property extent 'invisible t))
    (set-extent-property extent 'end-glyph glyph))
  glyph)

(defun gnus-xmas-remove-image (image &optional category)
  "Remove the image matching IMAGE and CATEGORY found first."
  (map-extents
   (lambda (ext unused)
     (when (equal (extent-end-glyph ext) image)
       (set-extent-property ext 'invisible nil)
       (set-extent-property ext 'end-glyph nil)
       t))
   nil nil nil nil nil 'gnus-image category))

(defun gnus-xmas-assq-delete-all (key alist)
  (let ((elem nil))
    (while (setq elem (assq key alist))
      (setq alist (delq elem alist)))
    alist))

(provide 'gnus-xmas)

;;; gnus-xmas.el ends here
