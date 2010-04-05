;;; cycbuf.el --- Cycle buffers code by Martin Pohlack, inspired by
;;;               swbuff.el, swbuff-x.el, and bs.el

;; Copyright (C) 2007, 2008 by Martin Pohlack

;; Author: Martin Pohlack martinp (at) gmx.de
;; Version: 0.4.8
;; Keywords: files, convenience, buffer switching
;; Time-stamp: <2008-10-15 martinp>

;; This file is NOT part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This is a combination of some features of swbuff-x (Kahlil (Kal)
;; HODGSON <dorge@tpg.com.au>), which is a modification to swbuff
;; (David Ponce) and bs (Olaf Sylvester <olaf@geekware.de>)
;;
;; I really liked the nicely layouted and composed buffer-selection
;; buffer of bs.  However, also fast switching buffers with one
;; key-stroke and showing a temporary buffer with a buffer list (with
;; hide timeout) a la swbuff is nice.  So I combined both's
;; advantages.
;;
;; Some current problems are documented in the code.

;;; Usage:

;; I define keyboard shortcuts and load cycbuf.el as follows (init.el):
;;
;; (require 'cycbuf)
;; (global-set-key [(meta right)] 'cycbuf-switch-to-next-buffer)
;; (global-set-key [(meta left)]  'cycbuf-switch-to-previous-buffer)

;;; Bugs:

;;  - Splitting windows does not work very well for very small frames sizes
;;  - large path names or buffer names may break column alignment

;;; Todo:

;; beautify column alignment stuff


;;; Changelog:

;; 0.4.8
;;  - incorporated some suggestions from Amilcar do Carmo Lucas
;;  - some code simplifications, now there are only two
;;    regexps (actually, lists of) for defining excluding /
;;    including buffer names, mostly to bsX-buffer-list
;;  - cycbuf-show-all is gone
;; 0.4.7
;;  - fixed buffer order restoration
;; 0.4.6
;;  - added cycbuf-sort-by-recency

;;; Code:

(require 'timer)

(defgroup cycbuf nil
  "Cyclic buffer switcher with temporary buffer list."
  :group 'extensions
  :group 'convenience
  :prefix "cycbuf-")

(defcustom cycbuf-file-name-replacements
  '(("/home/user/" "~/"))
  "*List of pairs, where the first of each pair is a regexp string and
the second a replacement string.  Each pair is applied with
replace-in-string on buffer file names in the given order, so you can
get usefull shortcuts in file name lists."
  :group 'cycbuf
  :type '(repeat sexp))

(defcustom cycbuf-mode-name-replacements
  '(("Fundamental" "Fund.")
    ("Lisp Interaction" "Lisp I."))
  "*List of pairs, where the first of each pair is a regexp string and
the second a replacement string.  Each pair is applied with
replace-in-string on buffer mode names in the given order, so you can
shorten mode names."
  :group 'cycbuf
  :type '(repeat sexp))

(defconst cycbuf-status-buffer-name "*cycbuf*"
  "Name of the working buffer used to display the buffer list.")

(defcustom cycbuf-dont-show-regexp
  '("^ "
    "^\\*cycbuf\\*$")
  "*List of regular expressions for excluded buffers.
The default setting excludes buffers whose name begin with a
blank character (emacs' auxiliary buffers) and cycbuf's auxiliary
buffer.  To exclude all emacs-internal buffers (i.e., *scratch*,
*Message*, etc.) you could add the following regexps: '^\\*.*\\*$'."
  :group 'cycbuf
  :type '(repeat (regexp :format "%v")))

(defcustom cycbuf-must-always-show-regexp nil
  "*List of regular expressions for specifying buffers to show always.
A buffer whose name matches any of these regular expression will
always be shown.  This list of regular expressions overrides
`cycbuf-dont-show-regexp'."
  :group 'cycbuf
  :type '(repeat (regexp :format "%v")))

(defcustom cycbuf-buffer-sort-function 'cycbuf-sort-by-filename
  "Sort function that is applied to the buffers that appear in Buffer
Selection Menu.  The functions gets two arguments - the buffers to compare."
  :group 'cycbuf
  :type 'function)

(defvar cycbuf-running-in-xemacs (string-match "XEmacs" (emacs-version))
  "Non-nil when running under XEmacs.")

(defconst cycbuf-header-lines-length 2
  "Number of lines for headers in Buffer Selection Menu.")

(defcustom cycbuf-max-window-height 20
  "*Maximal window height of Buffer Selection Menu."
  :group 'cycbuf
  :type 'integer)

(defcustom cycbuf-attributes-list
  '(("M"          1                      left  cycbuf-get-modified-string)
    ("R"          2                      left  cycbuf-get-readonly-string)
    ("Mode"      12                      left  cycbuf-get-mode-name)
    (""           2                      left  "  ")
    ("Directory"  cycbuf-get-file-length right cycbuf-get-file-name)
    (""           1                      left  " ")
    ("Buffer"     cycbuf-get-name-length left  cycbuf-get-name)
    (""           2                      left  "  "))
  "*List specifying the layout of a Buffer Selection Menu buffer.
Each entry specifies a column and is a list of the form of:
(HEADER LENGTH ALIGNMENT FUN-OR-STRING)
HEADER        : string for header for first line or a function
                which calculates column title.
LENGTH        : width of column (number or name of function).
                The function must return a positive integer.
ALIGNMENT     : alignment of column: (`left' `right' `middle')
FUN-OR-STRING : Name of a function for calculating the value or
                a string for a constant value.
                The function gets no parameters.  The function must
                return a string representing the columns value."
  :group 'cycbuf
  :type '(repeat sexp))

(defvar cycbuf-current-list nil
  "List of buffers shown in Buffer Selection Menu.
Used internally, only.")

(defvar cycbuf-old-current-line nil
  "Line number of previous current buffer.")

(defcustom cycbuf-maximal-buffer-name-column 45
  "*Maximum column width for buffer names.
The column for buffer names has dynamic width.  The width depends on
maximal and minimal length of names of buffers to show.  The maximal
width is bounded by `cycbuf-maximal-buffer-name-column'.
See also `cycbuf-minimal-buffer-name-column'."
  :group 'cycbuf
  :type 'integer)

(defcustom cycbuf-minimal-buffer-name-column 15
  "*Minimum column width for buffer names.
The column for buffer names has dynamic width.  The width depends on
maximal and minimal length of names of buffers to show.  The minimal
width is bounded by `cycbuf-minimal-buffer-name-column'.
See also `cycbuf-maximal-buffer-name-column'."
  :group 'cycbuf
  :type 'integer)

(defcustom cycbuf-maximal-file-name-column 45
  "*Maximum column width for file names.
The column for file names has dynamic width.  The width depends on
maximal and minimal length of names of files to show.  The maximal
width is bounded by `cycbuf-maximal-file-name-column'.
See also `cycbuf-minimal-file-name-column'."
  :group 'cycbuf
  :type 'integer)

(defcustom cycbuf-minimal-file-name-column 15
  "*Minimum column width for file names.
The column for file names has dynamic width.  The width depends on
maximal and minimal length of names of files to show.  The minimal
width is bounded by `cycbuf-minimal-file-name-column'.
See also `cycbuf-maximal-file-name-column'."
  :group 'cycbuf
  :type 'integer)

(defvar cycbuf-name-entry-length 20
  "Maximum length of all displayed buffer names.
Used internally, only.")

(defvar cycbuf-file-entry-length 20
  "Maximum length of all displayed file names.
Used internally, only.")

(defcustom cycbuf-clear-delay 3
  "*Time in seconds to delay before discarding the status window."
  :group 'cycbuf
  :type '(number :tag "seconds")) 

;;; faces

(defface cycbuf-current-face
  '((t (:background "light green" :bold t)))
  "Face for highlighting the current buffer in buffer list." )

(defface cycbuf-header-face
  '((t (:foreground "dark blue" :bold t)))
  "Face for highlighting the header line in buffer list." )

(defface cycbuf-uniquify-face
  '((t (:foreground "grey")))
  "Face for de-highlighting the uniquify part of buffer names, as
we also have the filename visible." )

;;; Local Variables

;; Store the initial buffer-list, buffer, window, and frame at the
;; time the switch sequence was called.
(defvar cycbuf-initial-buffer-list nil "")
(defvar cycbuf-initial-buffer nil "")
(defvar cycbuf-initial-window nil "")
(defvar cycbuf-initial-frame nil "")

;; Current buffer being displayed by cycbuf sequence.
(defvar cycbuf-current-buffer nil "")

;; Save the status buffer window, in case any external code that runs on a
;; timer changes the current window.
(defvar cycbuf-status-window nil "")

(defvar cycbuf-buffer-coming-from nil
  "The buffer in which the user started the current Buffer Selection Menu.")

(defvar cycbuf-display-timer nil)

(defvar cycbuf-this-frame-only t
"*If non-nil, buffers displayed in other visble or iconified frames are
skipped.  This is a convient way of temprorily excluding a particluar
buffer from your cycle list.")

(defvar cycbuf-include-buffer-regexps '("")
  "List of regular expressions matching buffer names to include in the
`cycbuf-buffer-list'.")

(defvar cycbuf-exclude-mode-regexp ""
  "Regular expression matching major modes to skip when cycling.")

(defvar cycbuf-buffer-list nil
  "Stores the current list of switchable buffers.
This way we only have to call `cycbuf-get-buffer-list' once.")


;; interactive interface

(defun cycbuf-switch-to-previous-buffer ()
  "\\[cycbuf-switch-to-previous-buffer] switch to the previous buffer
in the buffer list."
  (interactive)
  (run-hooks 'cycbuf-pre-switch-hook)
  (unless cycbuf-initial-buffer
    (cycbuf-initialize))
  (cycbuf-previous-buffer)
  (cycbuf-show-status-window))

(defun cycbuf-switch-to-next-buffer ()
  "\\[cycbuf-switch-to-next-buffer] switch to the next buffer in the
buffer list."
  (interactive)
  (run-hooks 'cycbuf-pre-switch-hook)
  (unless cycbuf-initial-buffer
    (cycbuf-initialize))
  (cycbuf-next-buffer)
  (cycbuf-show-status-window))

;; other stuff

(defun cycbuf-initialize ()
  "Initialize cycbuf variables prior to a switch sequence."
  (setq cycbuf-buffer-coming-from  (current-buffer)
        cycbuf-buffer-list         (bsX-buffer-list)
	cycbuf-initial-buffer-list (buffer-list)  ;cycbuf-buffer-list
	cycbuf-initial-buffer      (car cycbuf-initial-buffer-list)
	cycbuf-initial-window      (selected-window)
	cycbuf-initial-frame       (selected-frame)))

;; fixme: unify
(defun cycbuf-compute-col-width (blist min-len max-len get-prop)
  (let*
      ((map-fun (lambda (entry) (length (funcall get-prop entry))))
       (max-length-found (apply 'max (cons 0 (mapcar map-fun blist))))
       (entry-length (min max-len
                          (max min-len
                               max-length-found))))
    entry-length))

(defun cycbuf-layout-status-line (window bcurr)
  "Layout a status line in WINDOW current buffer.
BCURR is the buffer name to highlight."
  (let* ((blist cycbuf-buffer-list)
         current
         start
         end)

    (save-selected-window
      (select-window window)
      (cycbuf-mode)
      (setq cycbuf-current-list blist)
      (let* ((inhibit-read-only t))

        (if (and (or (eq last-command 'cycbuf-switch-to-next-buffer)
                     (eq last-command 'cycbuf-switch-to-previous-buffer))
                 (not (= (buffer-size) 0)))
            (progn  ; just move current-buffer marking a bit
              (when cycbuf-old-current-line ; redraw previous current line
                (goto-line cycbuf-old-current-line)
                (beginning-of-line)
                (setq start (point))
                (end-of-line)
                (setq end (point))
                (delete-region start end)
                (cycbuf-insert-one-entry
                 (nth (- cycbuf-old-current-line
                         (+ cycbuf-header-lines-length 1)) blist)))
              (setq line (+ 1 cycbuf-header-lines-length))
              (while blist ; highlight current current line
                (when (string-equal (buffer-name (car blist)) bcurr)
                  (progn
                    (setq cycbuf-old-current-line line)
                    (goto-line line)
                    (end-of-line)
                    (setq end (point))
                    (beginning-of-line)
                    (setq start (point))
                    (add-text-properties start end
                                         '(face cycbuf-current-face))))
                (setq blist (cdr blist))
                (setq line (+ 1 line))))
          (progn  ; complete redraw for whole buffer
            (erase-buffer)
            ; re-compute column widths, might have changed
            (setq cycbuf-name-entry-length
                  (cycbuf-compute-col-width blist
                                            cycbuf-minimal-file-name-column
                                            cycbuf-maximal-file-name-column
                                            'buffer-name))
            (setq cycbuf-file-entry-length
                  (cycbuf-compute-col-width blist
                                            cycbuf-minimal-file-name-column
                                            cycbuf-maximal-file-name-column
                                            'cycbuf-get-file-nameX))
	    (setq start (point))
            (cycbuf-show-header)
	    (setq end (point))
	    (set-text-properties start end '(face cycbuf-header-face))
            (while blist
              (setq start (point))
              (cycbuf-insert-one-entry (car blist))
              (setq end (point))
              (when (string-equal (buffer-name (car blist)) bcurr)
                (setq cycbuf-old-current-line (line-number-at-pos))
                (add-text-properties start end '(face cycbuf-current-face))
                (setq current start))
              (insert "\n")
              (setq blist (cdr blist)))
            (delete-backward-char 1)
            (cycbuf-set-window-height)
            (goto-char current)))
        ;; this sure looks ugly, maybe we should compute these numbers
        ;; somewhere else?
        (recenter (let ((l2bottom
                         (- (line-number-at-pos (point-max))
                            (line-number-at-pos))))
                    (if (< l2bottom (/ (window-height) 2))
                        (- -1 l2bottom)
                      (/ (window-height) 2))))))))

(defun cycbuf-next-buffer ()
  "Display and activate the next buffer in the buffer list."
  (let ((bufs cycbuf-buffer-list))  ; get curr. buffer list, sorted
                                    ; and filtered
    (setq buf bufs)
    (when buf
      (setq curh (memq (current-buffer) bufs))      ; find current buffer pos.
      (if (cadr curh)                               ; is there a next buffer ?
          (setq cycbuf-current-buffer (cadr curh))  ; switch to it
        (setq cycbuf-current-buffer (car bufs)))    ; or first one
      (switch-to-buffer cycbuf-current-buffer t)))) ; make it so ...

(defun cycbuf-previous-buffer ()
  "Display and activate the buffer at the end of the buffer list."
  (let ((bufs cycbuf-buffer-list))  ; get curr. buffer list, sorted
                                    ; and filtered
    (setq buf bufs)
    (when buf
      (setq last (car (last bufs)))
      (setq cycbuf-current-buffer last)
      (while buf                  ; iterate over all buffers
        (when (eq (car buf) (current-buffer))  ; if we hit current buffer ...
          (setq cycbuf-current-buffer last)    ; ... store the previous one
          ; break, anyone?
          )
        (setq last (car buf))
        (setq buf (cdr buf)))
      (switch-to-buffer cycbuf-current-buffer t))))  ; switch to found buffer

(defun cycbuf-get-file-nameX (buffer)
  (save-excursion
    (set-buffer buffer)
    (cycbuf-get-file-name)))

(defun cycbuf-get-file-name ()
  "Return string for column 'File' in Buffer Selection Menu.
This is the variable `buffer-file-name' of current buffer.
If current mode is `dired-mode' or shell-mode it returns the
default directory.  Also apply some filtering to shorten file names."
  (let ((string (copy-sequence (if (member major-mode
                                           '(shell-mode dired-mode))
                                   default-directory
                                 (or (if buffer-file-name
                                         (file-name-directory
                                          (buffer-file-name)))
                                     "")))))

    (setq repl-map cycbuf-file-name-replacements) ; filter file names
    (while (setq repl (car repl-map))
      (setq string (replace-regexp-in-string (car repl) (cadr repl) string))
      (setq repl-map (cdr repl-map)))

    string))

(defun cycbuf-get-mode-name ()
  "Return the name of mode of current buffer for Buffer Selection Menu,
apply some filtering for shortening."
  (let ((string (format-mode-line mode-name)))

    (setq repl-map cycbuf-mode-name-replacements) ; filter mode names
    (while (setq repl (car repl-map))
      (setq string (replace-regexp-in-string (car repl) (cadr repl) string))
      (setq repl-map (cdr repl-map)))

    string))

(defun cycbuf-sort-by-filename (b1 b2)
  "Compare buffers B1 and B2 by file name and as a secondary condition
   by buffer name.  This should give a stable order."
  (if (string< (buffer-file-name b1) (buffer-file-name b2))
      t
    (if (string< (buffer-file-name b2) (buffer-file-name b1))
        nil
      (if (string< (or (buffer-name b1) "")
                   (or (buffer-name b2) ""))
          t
        nil))))

(defun cycbuf-sort-by-recency (b1 b2)
  "Compare buffers B1 and B2 by their recency.  We have to trick
   a bit here, because we don't know this property, but we know that
   the original list is already sorted by this, so we always return
   nil and hope that the sort algorithm is smart."
  nil)

(defun cycbuf-discard-status-window ()
  "Discard the status window.  Called by both `sit-for' in
`cycbuf-show-status-window' and `cycbuf-post-command-hook'"

  (let ((buffer (get-buffer cycbuf-status-buffer-name))
	(buffer-list (nreverse cycbuf-initial-buffer-list)))

    (if (window-live-p cycbuf-status-window)
	(delete-window cycbuf-status-window))

    (if buffer (kill-buffer buffer))

    (unwind-protect
	(when (and cycbuf-initial-buffer cycbuf-current-buffer)
	  (save-window-excursion

	    ;; Because this may be called from a timer we have to be real
	    ;; careful that we are in the right frame, window and buffer
	    ;; at that time --- other timers (eg those called by
	    ;; speedbar) may put us elsewhere:-)

	    (select-frame cycbuf-initial-frame)
	    (select-window cycbuf-initial-window)

	    ;; reset visit order to what it was before the sequence began
	    (while (setq buffer (car buffer-list))
	      (switch-to-buffer buffer)
	      (setq buffer-list (cdr buffer-list)))
	    )
	  ;; then switch between the first and last buffers in the sequence
	  (and cycbuf-buffer-coming-from
	       (switch-to-buffer cycbuf-buffer-coming-from))
	  (and cycbuf-current-buffer
	       (switch-to-buffer cycbuf-current-buffer))
	  )
      ;; protect forms
      (setq cycbuf-initial-buffer	 nil
	    cycbuf-initial-buffer-list   nil
	    cycbuf-current-buffer	 nil
	    cycbuf-initial-frame	 nil
	    cycbuf-initial-window	 nil
	    cycbuf-status-window	 nil
            cycbuf-buffer-coming-from    nil))
    ))

(defun cycbuf-pre-command-hook ()
  "`pre-command-hook' used to track successive calls to switch commands."
  (when (eq (selected-frame) cycbuf-initial-frame)
    (remove-hook 'pre-command-hook 'cycbuf-pre-command-hook)
    (if (timerp cycbuf-display-timer)
	(cancel-timer cycbuf-display-timer))
    (setq cycbuf-display-timer nil)
    (unless (or (eq this-command 'cycbuf-switch-to-previous-buffer)
		(eq this-command 'cycbuf-switch-to-next-buffer))
      (cycbuf-discard-status-window)
      )))

(defun cycbuf-show-status-window ()
  "Pop-up a status window at the bottom of the selected window. The
status window shows the list of switchable buffers where the switched
one is hilighted using `cycbuf-current-buffer-face'. It is
automatically discarded after any command is executed or after the
delay specified by `cycbuf-clear-delay'."

  (if cycbuf-initial-buffer-list
      (let ((buffer-name (buffer-name cycbuf-current-buffer))
	    (window-min-height 1)
	    (cursor-in-non-selected-windows nil))
	(with-current-buffer (get-buffer-create cycbuf-status-buffer-name)
          ;; fixme: split-window-vertically will return an error for
          ;;        very small frame heights
          ;;        We should either:
          ;;         - only display the bufferlist buffer fully, or
          ;;         - only the chosen next target buffer
	  (let ((window (or (get-buffer-window cycbuf-status-buffer-name)
			    (split-window-vertically -2))))

	    ;; if we forget this we may end up with multiple status
	    ;; windows (kal)
	    (setq cycbuf-status-window window)

	    (set-window-buffer window (current-buffer))
	    (cycbuf-layout-status-line window buffer-name)
	    (add-hook 'pre-command-hook 'cycbuf-pre-command-hook)

	    ;; use a timer that we can cancel rather than sit-for
	    (if (timerp cycbuf-display-timer)
		(cancel-timer cycbuf-display-timer))
	    (setq cycbuf-display-timer
		  (run-with-timer cycbuf-clear-delay nil
				  'cycbuf-discard-status-window)))))
    (cycbuf-discard-status-window)
    (message "No buffers eligible for switching.")
    ))

(defun cycbuf-show-header ()
  "Insert header for Buffer Selection Menu in current buffer."
  (mapcar '(lambda (string)
	     (insert string "\n"))
	  (cycbuf-create-header)))

(defun cycbuf-create-header ()
  "Return all header lines used in Buffer Selection Menu as a list of strings."
  (list (mapconcat (lambda (column)
		     (cycbuf-format-aux (cycbuf-get-value (car column))
				     (nth 2 column) ; align
				     (cycbuf-get-value (nth 1 column))))
		   cycbuf-attributes-list
		   "")
	(mapconcat (lambda (column)
		     (let ((length (length (cycbuf-get-value (car column)))))
		       (cycbuf-format-aux (make-string length ?-)
				       (nth 2 column) ; align
				       (cycbuf-get-value (nth 1 column)))))
		   cycbuf-attributes-list
		   "")))

(defun cycbuf-format-aux (string align len)
  "Generate a string with STRING with alignment ALIGN and length LEN.
ALIGN is one of the symbols `left', `middle', or `right'."
  (let ((length (length string)))
    (if (>= length len)
	string
      (if (eq 'right align)
	  (concat (make-string (- len length) ? ) string)
	(concat string (make-string (- len length) ? ))))))

(defun cycbuf-get-value (fun &optional args)
  "Apply function FUN with arguments ARGS.
Return result of evaluation.  Will return FUN if FUN is a number
or a string."
  (cond ((numberp fun)
	 fun)
	((stringp fun)
	 fun)
	(t (apply fun args))))

(defun cycbuf-get-name-length ()
  "Return value of `cycbuf-name-entry-length'."
  cycbuf-name-entry-length)

(defun cycbuf-get-file-length ()
  "Return value of `cycbuf-file-entry-length'."
  cycbuf-file-entry-length)

(defun cycbuf-insert-one-entry (buffer)
  "Generate one entry for buffer BUFFER in Buffer Selection Menu.
It goes over all columns described in `cycbuf-attributes-list'
and evaluates corresponding string.  Inserts string in current buffer;
normally *buffer-selection*."
  (let ((string "")
	(columns cycbuf-attributes-list)
	(to-much 0))
    (save-excursion
      (while columns
	(set-buffer buffer)
	(let ((min   (cycbuf-get-value (nth 1 (car columns))))
	      (align (nth 2 (car columns)))
	      (fun   (nth 3 (car columns)))
	      (val   nil)
	      new-string)
	  (setq val (cycbuf-get-value fun))
	  (setq new-string (cycbuf-format-aux val align (- min to-much)))
	  (setq string (concat string new-string))
	  (if (> (length new-string) min)
	      (setq to-much (- (length new-string) min)))
	  ) ; let
	(setq columns (cdr columns))))
    (insert string)
    string))

(defun cycbuf-set-window-height ()
  "Change the height of the selected window to suit the current buffer list."
  (unless (one-window-p t)
    (shrink-window (- (window-height (selected-window))
		      ;; window-height in xemacs includes mode-line
		      (+ (if cycbuf-running-in-xemacs 3 1)    ;; content
			 cycbuf-header-lines-length
                         ;; diplay whole content of possible ...
			 (min (length cycbuf-current-list)
                              ;; ... but only up to user-specified # ...
			      (min cycbuf-max-window-height
                                   ;; ... or an even smaller number
                                   ;;     for small frames
                                   (- (frame-height) 10))))))))

(defun cycbuf-get-modified-string ()
  "Return a string which describes whether current buffer is modified."
  (if (buffer-modified-p) "*" " "))

(defun cycbuf-get-readonly-string ()
  "Return a string which describes whether current buffer is read only."
  (if buffer-read-only "%" " "))

(defun cycbuf-get-name ()
  "Return name of current buffer for Buffer Selection Menu."
  (let* ((name (copy-sequence (buffer-name)))
         (start (string-match "<" name)))
    (when start
      (set-text-properties start (length name)
                           '(face cycbuf-uniquify-face) name))
    (if (< (length name) cycbuf-name-entry-length)
        (concat name
                (make-string (- cycbuf-name-entry-length (length name)) ? ))
      name)))

(defun bsX-buffer-list (&optional list)
  "Return a list of buffers to be shown.
LIST is a list of buffers to test for appearence in Buffer
Selection Menu.  The result list depends on the global variables
`cycbuf-dont-show-regexp' and `cycbuf-buffer-sort-function'.  If
SORT-DESCRIPTION isn't nil the list will be sorted by a special
function.  SORT-DESCRIPTION is an element of
`cycbuf-sort-functions'."
  (setq list (or list (buffer-list)))
  (let ((result nil))
    (while list
      (let* ((buffername (buffer-name (car list)))
	     (extern-never-show
              (and 'cycbuf-dont-show-regexp
                   (assoc-default buffername cycbuf-dont-show-regexp
                                  'string-match t)))
	     (extern-must-show
              (and 'cycbuf-must-always-show-regexp
                   (assoc-default buffername cycbuf-must-always-show-regexp
                                  'string-match t))))
	(if (or extern-must-show (not extern-never-show))
	    (setq result (cons (car list) result)))
	(setq list (cdr list))))
    (setq result (reverse result))
    ;; The current buffer which was the start point of bs should be an element
    ;; of result list, so that we can leave with space and be back in the
    ;; buffer we started cycbuf-show.
    (if (and cycbuf-buffer-coming-from
	     (buffer-live-p cycbuf-buffer-coming-from)
	     (not (memq cycbuf-buffer-coming-from result)))
	(setq result (cons cycbuf-buffer-coming-from result)))
    ;; sorting
    (setq result (sort result cycbuf-buffer-sort-function))))

(defun cycbuf-mode ()
  "Major mode for editing a subset of Emacs' buffers.
Aside from two header lines each line describes one buffer."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'cycbuf-mode
	mode-name "Cycle-Buffers-Menu"
	buffer-read-only t
	truncate-lines t)
  (run-hooks 'cycbuf-mode-hook))

(provide 'cycbuf)
;;; cycbuf.el ends here
