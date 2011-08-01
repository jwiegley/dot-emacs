;;; highline.el --- minor mode to highlight current line in buffer

;; Copyright (C) 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008
;;   Vinicius Jose Latorre

;; Author: Vinicius Jose Latorre <viniciusjl@ig.com.br>
;; Maintainer: Vinicius Jose Latorre <viniciusjl@ig.com.br>
;; Time-stamp: <2008/12/19 11:42:46 vlatorre>
;; Keywords: faces, frames, editing
;; Version: 7.2.1
;; X-URL: http://www.emacswiki.org/cgi-bin/wiki/ViniciusJoseLatorre

;; This file is *NOT* (yet?) part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Introduction
;; ------------
;;
;; This package is a minor mode to highlight the current line in
;; buffer.
;;
;; highline was inspired by:
;;
;;    linemenu.el		  Bill Brodie <wbrodie@panix.com>
;;	 Hook function to highlight current line in buffer.
;;
;;    hl-line.el		  Dave Love <fx@gnu.org>
;;	 Highlight the current line.
;;
;;    highlight-current-line.el	  Christoph Conrad <christoph.conrad@gmx.de>
;;	 Highlight line where the cursor is.
;;
;; To use highline, insert in your ~/.emacs:
;;
;;    (require 'highline)
;;
;; For good performance, be sure to byte-compile highline.el, e.g.
;;
;;    M-x byte-compile-file <give the path to highline.el when prompted>
;;
;; This will generate highline.elc, which will be loaded instead of
;; highline.el.
;;
;; highline was tested with GNU Emacs 21, 22 and 23, XEmacs 21.4.20, and
;; Aquamacs Emacs 1.5.
;;
;;
;; Using highline
;; --------------
;;
;; * To customize highline, type:
;;	 M-x highline-customize RET
;;
;; * LOCAL highline (see NOTE 1 below):
;;    + To activate highline locally, type:
;;	    C-u 1 M-x highline-mode RET
;;
;;    + To deactivate highline locally, type:
;;	    C-u 0 M-x highline-mode RET
;;
;;    + To toggle highline locally, type:
;;	    M-x highline-mode RET
;;
;; * GLOBAL highline (see NOTE 1 below):
;;    + To activate highline globally, type:
;;	    C-u 1 M-x global-highline-mode RET
;;
;;    + To deactivate highline globally, type:
;;	    C-u 0 M-x global-highline-mode RET
;;
;;    + To toggle highline globally, type:
;;	    M-x global-highline-mode RET
;;
;; * INDIRECT highline (see NOTE 2 below):
;;    + To activate indirect highline, type:
;;	    C-u 1 M-x highline-view-mode RET
;;
;;    + To deactivate indirect highline, type:
;;	    C-u 0 M-x highline-view-mode RET
;;
;;    + To toggle indirect highline, type:
;;	    M-x highline-view-mode RET
;;
;;    + To split window and activate indirect highline, type:
;;	    M-x highline-split-window-vertically RET
;;	    M-x highline-split-window-horizontally RET
;;
;; You can also bind `highline-mode', `global-highline-mode',
;; `highline-customize', `highline-view-mode',
;; `highline-split-window-vertically' and
;; `highline-split-window-horizontally' to some key, like:
;;
;;    (global-set-key "\C-c-h" 'highline-mode)
;;    (global-set-key "\C-c-g" 'global-highline-mode)
;;    (global-set-key "\C-c-c" 'highline-customize)
;;    (global-set-key "\C-c-v" 'highline-view-mode)
;;    (global-set-key "\C-c-2" 'highline-split-window-vertically)
;;    (global-set-key "\C-c-3" 'highline-split-window-horizontally)
;;
;; NOTE 1: There is no problem if you mix local and global minor mode
;;	   usage.
;;
;; NOTE 2: Indirect highline (`highline-view-mode') is useful when you
;;	   wish to have various "visions" of the same buffer.
;;	   Indirect highline uses an indirect buffer to get the
;;	   "vision" of the buffer.  So, if you kill an indirect
;;	   buffer, the base buffer is not affected; if you kill the
;;	   base buffer, all indirect buffer related with the base
;;	   buffer is automagicaly killed.  Also, any text
;;	   insertion/deletion in any indirect or base buffer is
;;	   updated in all related buffers.
;;
;;
;; Example
;; -------
;;
;; As an example, try to insert this in your .emacs file:
;;
;;  (require 'highline)
;;  (defun highline-mode-on () (highline-mode 1))
;;  ;; Turn on local highlighting for Dired (C-x d)
;;  (add-hook 'dired-after-readin-hook #'highline-mode-on)
;;  ;; Turn on local highlighting for list-buffers (C-x C-b)
;;  (defadvice list-buffers (after highlight-line activate)
;;    (save-excursion
;;      (set-buffer "*Buffer List*")
;;      (highline-mode-on)))
;;
;;
;; Hooks
;; -----
;;
;; highline has the following hook variables:
;;
;; `global-highline-mode-hook'
;;    It is evaluated always when highline is turned on globally.
;;
;; `highline-mode-hook'
;;    It is evaluated always when highline is turned on locally.
;;
;; `highline-view-mode-hook'
;;    It is evaluated always when indirect highline is turned on.
;;
;; `highline-load-hook'
;;    It is evaluated after highline package is loaded.
;;
;;
;; Options
;; -------
;;
;; Below it's shown a brief description of highline options, please,
;; see the options declaration in the code for a long documentation.
;;
;; `highline-face'			Specify face used to highlight
;;					the current line.
;;
;; `highline-vertical-face'		Specify face used to highlight
;;					other than current line.
;;
;; `highline-line'			Specify which part of line
;;					should be highlighted.
;;
;; `highline-vertical'			Specify how many vertical
;;					lines should be highlighted.
;;
;; `highline-ignore-regexp'		Specify regexp for buffers to
;;					ignore.
;;
;; `highline-priority'			Specify highline overlay
;;					priority.
;;
;; `highline-view-prefix'		Specify prefix used in the
;;					indirect buffer name creation.
;;
;; `highline-keep-highlight'		Non-nil means keep highlight
;;					on nonselected windows with
;;					highline mode on.
;;
;; To set the above options you may:
;;
;; a) insert the code in your ~/.emacs, like:
;;
;;	 (setq highline-face 'highlight)
;;
;;    This way always keep your default settings when you enter a new
;;    Emacs session.
;;
;; b) or use `set-variable' in your Emacs session, like:
;;
;;	 M-x set-variable RET highline-face RET highlight RET
;;
;;    This way keep your settings only during the current Emacs
;;    session.
;;
;; c) or use customization, for example:
;;
;;    In Emacs 21 or lower:
;;	 click on menu-bar *Help* option,
;;	 then click on *Customize*,
;;	 then click on *Browse Customization Groups*,
;;	 expand *Editing* group,
;;	 expand *Highline* group
;;	 and then customize highline options.
;;
;;    In Emacs 22 or higher:
;;	 click on menu-bar *Options* option,
;;	 then click on *Customize Emacs*,
;;	 then click on *Browse Customization Groups*,
;;	 expand *Editing* group,
;;	 expand *Highline* group
;;	 and then customize highline options.
;;
;;    Through this way, you may choose if the settings are kept or not
;;    when you leave out the current Emacs session.
;;
;; d) or see the option value:
;;
;;	 C-h v highline-face RET
;;
;;    and click the *customize* hypertext button.
;;    Through this way, you may choose if the settings are kept or not when
;;    you leave out the current Emacs session.
;;
;; e) or invoke:
;;
;;	 M-x highline-customize RET
;;
;;    and then customize highline options.
;;    Through this way, you may choose if the settings are kept or not
;;    when you leave out the current Emacs session.
;;
;;
;; Acknowledgements
;; ----------------
;;
;; Thanks to David Reitter <david.reitter@gmail.com> for `highline-face' less
;; contrastive default values.
;;
;; Thanks to Stefan Kamphausen <ska@skamphausen.de> and Steven Tate
;; <state@odnosam.com> for testing.
;;
;; Thanks to Gwern Branwen <gwern0@gmail.com> for indicating defface
;; :group attribute.
;;
;; Thanks to Sandip Chitale <sandip.chitale@brokat.com> for
;; byte-compilation tests.
;;
;; Thanks to Stephan Engelke <engelke@gmx.ne> for XEmacs tests.
;;
;; Thanks to Roman Belenov <roman@nstl.nnov.ru> for `pre-command-hook'
;; suggestion.
;;
;; Thanks to Trey Jackson <bigfaceworm@hotmail.com> for
;; `highline-line' enhancements.
;;
;; Thanks to Fredrik Sundstroem <fresun-7@sm.luth.se> for
;; permanent-local overlay property indication.
;;
;; Thanks to:
;;    Bill Brodie <wbrodie@panix.com>		   linemenu.el
;;    Dave Love <fx@gnu.org>			   hl-line.el
;;    Christoph Conrad <christoph.conrad@gmx.de>   highlight-current-line.el
;; And to all people who contributed with them.
;;
;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:


(eval-and-compile
  (when (featurep 'xemacs)	      ; XEmacs
    ;; XEmacs needs overlay emulation package
    (or (require 'overlay)
	(error "`highline' requires `overlay' package."))))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; User Variables:


;;; Interface to the command system

(defgroup highline nil
  "Highlight the current line."
  :link '(emacs-library-link :tag "Source Lisp File" "highline.el")
  :group 'faces
  :group 'frames
  :group 'editing)


(defcustom highline-face 'highline-face
  "*Specify face used to highlight the current line."
  :type 'face
  :group 'highline)


(defface highline-face
  ;; (if (featurep 'xemacs)
  ;;    ;; XEmacs -- it doesn't have `:inherit' face specification
  ;;    '((((class color) (background light))
  ;;	 (:background "darkseagreen2"))
  ;;	(((class color) (background dark))
  ;;	 (:background "darkolivegreen"))
  ;;	(t (:inverse-video t)))
  ;;  ;; GNU Emacs
  ;;  '((t (:inherit highlight))))
  '((((class color) (background dark))
     (:background "#551100"))		; dark brown
    (((class color) (background light))
     (:background "#EEEEDD"))		; light red
    (t (:inverse-video t)))
  "Face used to highlight current line."
  :group 'highline)


(defcustom highline-vertical-face 'highline-vertical-face
  "*Specify face used to highlight other than current line.

See also `highline-vertical'."
  :type 'face
  :group 'highline)


(defface highline-vertical-face
  (if (featurep 'xemacs)
      ;; XEmacs -- it doesn't have `:inherit' face specification
      '((((class color) (background light))
	 (:background "yellow1"))
	(((class color) (background dark))
	 (:background "SkyBlue4"))
	(t (:inverse-video t)))
    ;; GNU Emacs
    '((t :inherit secondary-selection)))
  "Face used to highlight other than current line."
  :group 'highline)


(defcustom highline-line nil
  "*Specify which part of line should be highlighted.

Valid values are:

   t			mark up to end of line.

   nil			mark up to window border.  On XEmacs, it behaves as t.
			NOTE: Let me know, if you find a way to mark up to
			      window border on XEmacs.

   INTEGER		mark up from beginning of line to column INTEGER or to
			end of line if INTEGER exceeds line length.  If INTEGER
			is negative, the region marked starts from end of line
			instead of beginning of line.

   (LOWER . UPPER)	mark up the region from column LOWER to column UPPER or
			to end of line if UPPER exceeds line length.  Nothing
			happens if LOWER exceeds line length.
			It must: 0 <= LOWER < UPPER.

   (beyond . INTEGER)	mark up the region from column INTEGER to end of line.
			Nothing happens if INTEGER exceeds line length.
			It must: INTEGER > 0.

   (point . INTEGER)	mark up the region from column
			(- (current-column) INTEGER) to column
			(+ (current-column) INTEGER).  It never goes beyond
			beginning or end of line.
			It must: INTEGER > 0.

   FUNCTION             function symbol which is called without arguments and
                        must return one of the values above (see above).

Any other value is treated as t.

If the variable `line-move-visual' is non-nil, highlight only the current
visual line; otherwise, highlight the current line."
  :type '(choice :menu-tag "Mark Up To"
		 :tag "Mark Up To"
		 (const :tag "End Of Line" t)
		 (const :tag "Window Border" nil)
		 (integer :tag "Column")
		 (cons :tag "Point" :value (point . 0)
		       (const :tag "Point" point)
		       (integer :tag "To"))
		 (cons :tag "Beyond" :value (beyond . 0)
		       (const :tag "Beyond" beyond)
		       (integer :tag "From"))
		 (cons :tag "Range" :value (0 . 0)
		       (integer :tag "From")
		       (integer :tag "To"))
                 (function :tag "Function Symbol"))
  :group 'highline)


(defcustom highline-vertical nil
  "*Specify how many vertical lines should be highlighted.

Valid values are:

   nil			Highlight only current line.

   (ABOVE . BELOW)	Highlight the vertical range from line
			(current-line-number - ABOVE) to line
			(current-line-number + BELOW).  ABOVE and BELOW should
			be integers.  There are the following cases:

			1. ABOVE <= 0 and BELOW <= 0
				This is the same as nil, that is, only current
				line is highlighted.  It's recommended to set
				`highline-vertical' to nil instead of (0 . 0),
				it'll have a better performance.

			2. ABOVE <= 0 and BELOW > 0
				Only current line and lines below will be
				highlighted.

			3. ABOVE > 0 and BELOW <= 0
				Only current line and lines above will be
				highlighted.

			4. ABOVE > 0 and BELOW > 0
				Current line, lines above and lines below will
				be highlighted.

Any other value is treated as nil.

If the variable `line-move-visual' is non-nil, highlight only
visual line; otherwise, highlight whole line."
  :type '(choice :menu-tag ""
		 :tag ""
		 (const :tag "Only Current Line" nil)
		 (cons :tag "Vertical Range" :value (1 . 1)
		       (integer :tag "Above")
		       (integer :tag "Below")))
  :group 'highline)


(defcustom highline-ignore-regexp
  (concat "Faces\\|Colors\\|Minibuf"
	  "\\|\\*tip\\*\\|\\*Help\\*"
	  ;; for example:
	  ;; "\\|RMAIL.*summary\\|\\*Group\\|\\*Summary"
	  )
  "*Specify regexp for buffers to ignore.

Set to nil or \"\", to accept any buffer.

Used by `highline-highlight-current-line'."
  :type 'regexp
  :group 'highline)


(defcustom highline-priority 0
  "*Specify highline overlay priority.

Higher integer means higher priority, so highline overlay will have precedence
over overlays with lower priority.  *Don't* use negative number."
  :type 'integer
  :group 'highline)


(defcustom highline-view-prefix ":: View ::"
  "*Specify prefix used in the indirect buffer name creation.

See `highline-view-mode'."
  :type 'string
  :group 'highline)


(defcustom highline-keep-highlight nil
  "*Non-nil means keep highlight on nonselected windows with highline mode on."
  :type 'boolean
  :group 'highline)

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definitions for GNU Emacs 21 and 22, and XEmacs 21.4.20.


;; GNU Emacs
(or (fboundp 'line-beginning-position)
    (defun line-beginning-position (&optional n)
      "Return the character position of the first character on the current line.
With argument N not nil or 1, move forward N - 1 lines first.
If scan reaches end of buffer, return that position.

This function constrains the returned position to the current field
unless that would be on a different line than the original,
unconstrained result.  If N is nil or 1, and a front-sticky field
starts at point, the scan stops as soon as it starts.  To ignore field
boundaries bind `inhibit-field-text-motion' to t.

This function does not move point."
      (save-excursion
	(and n (/= n 1) (forward-line (1- n)))
	(forward-line 0)
	(point))))

;; GNU Emacs
(or (fboundp 'redisplay)
    (defun redisplay (&optional force)
      "Perform redisplay if no input is available.
If optional arg FORCE is non-nil or `redisplay-dont-pause' is non-nil,
perform a full redisplay even if input is available.
Return t if redisplay was performed, nil otherwise."
      (let ((redisplay-dont-pause (or redisplay-dont-pause force)))
	(sit-for 0))))

;; GNU Emacs
(or (boundp 'redisplay-dont-pause)
    (defvar redisplay-dont-pause nil
      "Non-nil means update isn't paused when input is detected."))

;; GNU Emacs
(or (boundp 'highlight-nonselected-windows)
    (defvar highlight-nonselected-windows nil
      "Non-nil means highlight region even in nonselected windows."))

;; GNU Emacs
(or (boundp 'line-move-visual)
    (defvar line-move-visual nil
      "When non-nil, `line-move' moves point by visual lines.
This movement is based on where the cursor is displayed on the
screen, instead of relying on buffer contents alone.  It takes
into account variable-width characters and line continuation."))

;; GNU Emacs
(or (fboundp 'beginning-of-visual-line)
    (defalias 'beginning-of-visual-line 'beginning-of-line))

;; GNU Emacs 21 - defalias doesn't have a docstring argument.

;;       "Move point to beginning of current visual line.
;; With argument N not nil or 1, move forward N - 1 visual lines first.
;; If point reaches the beginning or end of buffer, it stops there.
;; To ignore intangibility, bind `inhibit-point-motion-hooks' to t."))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization


;;;###autoload
(defun highline-customize ()
  "Customize highline group."
  (interactive)
  (customize-group 'highline))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; User commands


;;;###autoload
(define-minor-mode global-highline-mode
  "Toggle global minor mode to highlight line about point (HL on modeline).

If ARG is null, toggle global highline mode.
If ARG is a number and is greater than zero, turn on
global highline mode; otherwise, turn off global highline mode.
Only useful with a windowing system."
  :lighter    " HL"
  :init-value nil
  :global     t
  :group      'highline
  :version    "21"
  (cond
   (noninteractive			; running a batch job
    (setq global-highline-mode nil))
   (global-highline-mode		; global-highline-mode on
    (save-excursion
      (let ((buffers (buffer-list))
	    (temp    (get-buffer-create (make-temp-name " *Temp"))))
	;; be sure to access global `pre-command-hook' and `post-command-hook'
	(set-buffer temp)
	(add-hook 'mouse-leave-buffer-hook
		  #'highline-maybe-unhighlight-current-line)
        (add-hook 'change-major-mode-hook
		  #'highline-unhighlight-current-line)
	(add-hook 'pre-command-hook
		  #'highline-maybe-unhighlight-current-line)
	(add-hook 'post-command-hook
		  #'highline-highlight-current-line)
	(add-hook 'window-size-change-functions
		  #'highline-highlight-current-line)
	(while buffers			; adjust all local mode
	  (set-buffer (car buffers))
	  (unless highline-mode
	    (add-hook 'change-major-mode-hook
		      #'highline-unhighlight-current-line nil t)
	    (add-hook 'pre-command-hook
		      #'highline-maybe-unhighlight-current-line nil t)
	    (add-hook 'post-command-hook
		      #'highline-highlight-current-line nil t)
	    (add-hook 'window-size-change-functions
		      #'highline-highlight-current-line nil t)
	    (highline-highlight-current-line))
	  (setq buffers (cdr buffers)))
	(kill-buffer temp)))
    (highline-highlight-current-line))
   (t					; global-highline-mode off
    (save-excursion
      (let ((buffers (buffer-list))
	    (temp    (get-buffer-create (make-temp-name " *Temp"))))
	;; be sure to access global `pre-command-hook' and `post-command-hook'
	(set-buffer temp)
	(remove-hook 'mouse-leave-buffer-hook
		     #'highline-maybe-unhighlight-current-line)
        (remove-hook 'change-major-mode-hook
		     #'highline-unhighlight-current-line)
	(remove-hook 'pre-command-hook
		     #'highline-maybe-unhighlight-current-line)
	(remove-hook 'post-command-hook
		     #'highline-highlight-current-line)
	(remove-hook 'window-size-change-functions
		     #'highline-highlight-current-line)
	(while buffers			; adjust all local mode
	  (set-buffer (car buffers))
	  (unless highline-mode
	    (remove-hook 'change-major-mode-hook
			 #'highline-unhighlight-current-line t)
	    (remove-hook 'pre-command-hook
			 #'highline-maybe-unhighlight-current-line t)
	    (remove-hook 'post-command-hook
			 #'highline-highlight-current-line t)
	    (remove-hook 'window-size-change-functions
			 #'highline-highlight-current-line t)
	    (highline-unhighlight-current-line))
	  (setq buffers (cdr buffers)))
	(kill-buffer temp)))
    (highline-unhighlight-current-line))))


;;;###autoload
(define-minor-mode highline-mode
  "Toggle local minor mode to highlight the line about point (hl on modeline).

If ARG is null, toggle local highline mode.
If ARG is a number and is greater than zero, turn on
local highline mode; otherwise, turn off local highline mode.
Only useful with a windowing system."
  :lighter    " hl"
  :init-value nil
  :global     nil
  :group      'highline
  :version    "21"
  (cond
   (noninteractive			; running a batch job
    (setq highline-mode nil))
   (highline-mode			; highline-mode on
    (set (make-local-variable 'highlight-nonselected-windows)
	 highline-keep-highlight)
    (highline-local-on))
   (t					; highline-mode off
    (setq highlight-nonselected-windows
	  (default-value 'highlight-nonselected-windows))
    (highline-local-off))))


;;;###autoload
(define-minor-mode highline-view-mode
  "Toggle indirect mode to highlight current line in buffer (Ihl on modeline).

If ARG is null, toggle indirect highline mode.
If ARG is a number and is greater than zero, turn on
indirect highline mode; otherwise, turn off indirect highline mode.
Only useful with a windowing system.

Indirect highline (`highline-view-mode') is useful when you wish
to have various \"visions\" of the same buffer.

Indirect highline uses an indirect buffer to get the \"vision\" of the buffer.
So, if you kill an indirect buffer, the base buffer is not affected; if you
kill the base buffer, all indirect buffer related with the base buffer is
automagically killed.  Also, any text insertion/deletion in any indirect or base
buffer is updated in all related buffers.

See `highline-view-prefix'."
  :lighter    " Ihl"
  :init-value nil
  :global     nil
  :group      'highline
  :version    "21"
  (cond
   (noninteractive			; running a batch job
    (setq highline-mode nil))
   (highline-view-mode			; highline-view-mode on
    (let* ((local-buffer-read-only buffer-read-only)
	   (buffer (current-buffer))
	   (name (generate-new-buffer-name
		  (concat " " highline-view-prefix " "
			  (buffer-name (or (buffer-base-buffer buffer)
					   buffer))))))
      (switch-to-buffer (make-indirect-buffer buffer name t))
      (setq buffer-read-only local-buffer-read-only))
    (set (make-local-variable 'highlight-nonselected-windows) t)
    (highline-local-on))
   (t					; highline-view-mode off
    (highline-local-off)
    (let* ((buffer (current-buffer))
	   (base   (buffer-base-buffer buffer)))
      (when base
	(kill-buffer buffer)
	(switch-to-buffer base))))))


;;;###autoload
(defun highline-split-window-vertically (&optional arg)
  "Split window vertically then turn on indirect highline mode.

See `split-window-vertically' for explanation about ARG and for
documentation.

See also `highline-view-mode' for documentation."
  (interactive "P")
  (split-window-vertically arg)
  (highline-view-mode 1))


;;;###autoload
(defun highline-split-window-horizontally (&optional arg)
  "Split window horizontally then turn on indirect highline mode.

See `split-window-horizontally' for explanation about ARG and for
documentation.

See also `highline-view-mode' for documentation."
  (interactive "P")
  (split-window-horizontally arg)
  (highline-view-mode 1))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal functions


(defvar highline-overlays nil
  "Overlay list to highlight line(s)")
(make-variable-buffer-local 'highline-overlays)

(put 'highline-overlays 'permanent-local t)


(defvar highline-line-option nil
  "Used by `highline-overlay-start' and `highline-overlay-end'.")

(defvar highline-line-value  nil
  "Used by `highline-overlay-start' and `highline-overlay-end'.")


(defun highline-local-on ()
  "Turn on local minor mode."
  (add-hook 'mouse-leave-buffer-hook
	    #'highline-maybe-unhighlight-current-line)
  (add-hook (make-local-variable 'change-major-mode-hook)
	    #'highline-unhighlight-current-line nil t)
  (add-hook (make-local-variable 'pre-command-hook)
	    #'highline-maybe-unhighlight-current-line nil t)
  (add-hook (make-local-variable 'post-command-hook)
	    #'highline-highlight-current-line nil t)
  (add-hook (make-local-variable 'window-size-change-functions)
	    #'highline-highlight-current-line nil t)
  (highline-highlight-current-line))


(defun highline-local-off ()
  "Turn off local minor mode."
  (remove-hook 'mouse-leave-buffer-hook
	       #'highline-maybe-unhighlight-current-line)
  (remove-hook 'change-major-mode-hook
	       #'highline-unhighlight-current-line t)
  (remove-hook 'pre-command-hook
	       #'highline-maybe-unhighlight-current-line t)
  (remove-hook 'post-command-hook
	       #'highline-highlight-current-line t)
  (remove-hook 'window-size-change-functions
	       #'highline-highlight-current-line t)
  (highline-unhighlight-current-line))


(defun highline-maybe-unhighlight-current-line (&rest ignore)
  "Unhighlight current line only if `highlight-nonselected-windows' is non-nil."
  (unless highlight-nonselected-windows
    (save-excursion
      (highline-delete-overlays)
      ;; to avoid problems with displaying an overlay during window
      ;; scrolling/splitting
      (redisplay t))))			; force redisplay!!!


(defun highline-unhighlight-current-line (&rest ignore)
  "Unhighlight current line."
  (save-excursion
    (highline-delete-overlays)
    ;; to avoid problems with displaying an overlay during window
    ;; scrolling/splitting
    (redisplay t)))			; force redisplay!!!


(defun highline-highlight-current-line (&rest ignore)
  "Highlight current line."    
  (unless (save-match-data
	    (and highline-ignore-regexp
		 (not (equal "" highline-ignore-regexp))
		 (string-match highline-ignore-regexp (buffer-name))))
    (save-excursion
      (highline-delete-overlays)	  ; clean highline overlays
      (let ((inhibit-field-text-motion t) ; due to line-beginning-position
	    (column (highline-current-column))
	    (lines  (highline-vertical))
	    current-line)
	(setq current-line (cdr lines)
	      lines        (car lines))
	(highline-line-option)		; check highline-line value
	(when (> lines 0)
	  (while (progn
		   ;; move highlight to the current line
		   (highline-move-overlay
		    ;; overlay
		    (car (setq highline-overlays
			       (cons (make-overlay 1 1) ; hide it
				     highline-overlays)))
		    ;; overlay face
		    (if (= lines current-line)
			highline-face
		      highline-vertical-face)
		    ;; current column
		    column)
		   ;; prepare next iteration
		   (setq lines (1- lines))
		   (> lines 0))
	    (highline-forward-line 1)))))
    (save-excursion
      ;; to avoid problems with displaying an overlay during window
      ;; scrolling/splitting
      (redisplay t))))			; force redisplay!!!


(defun highline-delete-overlays ()
  "Delete highline overlays from current buffer."
  (while highline-overlays
    (delete-overlay (car highline-overlays))
    (setq highline-overlays (cdr highline-overlays))))


(defun highline-vertical ()
  "Return how much vertical lines to highlight.

Return the cons:

   (TOTAL-LINES . CURRENT-LINE-LEVEL)"
  (cond
   ;; (ABOVE . BELOW) - vertical range
   ((and (consp highline-vertical)
	 (integerp (car highline-vertical))
	 (integerp (cdr highline-vertical)))
    (let ((above (car highline-vertical))
	  (below (1+ (max (cdr highline-vertical) 0))))
      (cons (if (<= above 0)
		below
	      (highline-forward-line (- above))
	      (+ above below))
	    below)))
   ;; nil - only current line
   (t
    '(1 . 1))
   ))


(defun highline-line-option ()
  "Return a symbol for horizontal line highlight.

The symbol returned can be:

   t		highlight the whole line.

   nil		highlight the whole line until window border.

   integer	highlight from beginning of line until a column.

   beyond	highlight from a column until the end of line.

   point	highlight around current column.

   range	highlight from a column until another column.

The global variable `highline-line-option' is set to the symbol
returned.

The global variable `highline-line-value' is set to an apropriate
value."
  (setq highline-line-value (if (functionp highline-line)
                                (funcall highline-line)
                              highline-line))
  (setq highline-line-option
        (cond ((null highline-line-value)     nil)
              ((integerp highline-line-value) 'integer)
              ((and (consp highline-line-value)
                    (integerp (cdr highline-line-value))
                    (> (cdr highline-line-value) 0))
               (cond ((eq (car highline-line-value) 'beyond) 'beyond)
                     ((eq (car highline-line-value) 'point)  'point)
                     ((and (integerp (car highline-line-value))
                           (>= (car highline-line-value) 0)
                           (< (car highline-line-value)
                              (cdr highline-line-value)))    'range)
                     (t t)))
              (t t))))


(defun highline-move-overlay (ov ov-face column)
  "Move overlay OV considering column COLUMN with face OV-FACE."
  ;; set current overlay properties
  (overlay-put ov 'hilit    t)
  (overlay-put ov 'face     ov-face)
  (overlay-put ov 'priority (abs highline-priority)) ; force non-negative value
  ;; XEmacs doesn't have `window' overlay property
  (unless (featurep 'xemacs)
    (overlay-put ov 'window (if highlight-nonselected-windows
				nil
			      (selected-window))))
  ;; move highlight to the current line
  (move-overlay ov
		(highline-overlay-start column)
		(highline-overlay-end column)))


(defun highline-overlay-start (column)
  "Return the overlay start considering column COLUMN.

Use global variable `highline-line-option' and `highline-line-value'."
  (cond
   ;; integer
   ((eq highline-line-option 'integer)	; INTEGER
    (if (>= highline-line-value 0)
	(highline-line-beginning-position)
      (1- (highline-line-beginning-position 2))))
   ;; range
   ((eq highline-line-option 'range)	; (LOWER . UPPER)
    (highline-column-position (car highline-line-value)))
   ;; point
   ((eq highline-line-option 'point)	; (point . INTEGER)
    (highline-column-position
     (- column (cdr highline-line-value))))
   ;; beyond
   ((eq highline-line-option 'beyond)	; (beyond . INTEGER)
    (highline-column-position (cdr highline-line-value)))
   ;; t or nil
   (t					; t or nil
    (highline-line-beginning-position))))


(defun highline-overlay-end (column)
  "Return the overlay end considering column COLUMN.

Use global variable `highline-line-option' and `highline-line-value'."
  (cond
   ;; integer
   ((eq highline-line-option 'integer)	; INTEGER
    (highline-column-position
     (if (>= highline-line-value 0)
	 highline-line-value
       (end-of-line)
       (+ column highline-line-value))))
   ;; range
   ((eq highline-line-option 'range)	; (LOWER . UPPER)
    (highline-column-position (cdr highline-line-value)))
   ;; point
   ((eq highline-line-option 'point)	; (point . INTEGER)
    (highline-column-position
     (+ column (cdr highline-line-value))))
   ;; nil
   ((null highline-line-option)		; nil
    (min (point-max)
	 (highline-line-beginning-position 2)))
   ;; t or beyond
   (t					; t or (beyond . INTEGER)
    (1- (highline-line-beginning-position 2)))))


(defun highline-column-position (column)
  "Return the position from column COLUMN.

It does not move the point."
  (save-excursion
    (move-to-column (max 0 column))
    (point)))


(defun highline-forward-line (&optional arg)
  "Move ARG lines forward (backward if ARG is negative).

If the variable `line-move-visual' is non-nil, use `next-line'
function to move; otherwise, use `forward-line' function."
  (if line-move-visual
      (unless (eobp)
	(next-line arg))
    (forward-line arg)))


(defun highline-line-beginning-position (&optional n)
  "Return the character position of the first character on the current line.

If the variable `line-move-visual' is non-nil, use
`beginning-of-visual-line' function to get beginning of line
position; otherwise, use `line-beginning-position' function."
  (if line-move-visual
      (save-excursion
	(beginning-of-visual-line n)
	(point))
    (line-beginning-position n)))


(defun highline-current-column ()
  "Return the horizontal position of point.  Beginning of line is column 0.

If the variable `line-move-visual' is non-nil, use
`beginning-of-visual-line' function to get the current column of
current visual line; otherwise, use `current-column' function."
  (if line-move-visual
      (- (current-column)
	 (save-excursion
	   (beginning-of-visual-line)
	   (current-column)))
    (current-column)))


(defun highline-unload-function ()
  "Unload the highline library."
  (global-highline-mode -1)
  (save-current-buffer
    (dolist (buffer (buffer-list))
      (set-buffer buffer)
      (when highline-mode
	(highline-mode -1))))
  nil)					; continue standard unloading

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(provide 'highline)


(run-hooks 'highline-load-hook)


;;; highline.el ends here
