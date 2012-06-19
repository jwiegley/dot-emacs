;;; per-window-point.el --- persisent per-window values of point

;; Copyright (c) 2011 Alp Aker

;; Author: Alp Aker <alp.tekin.aker@gmail.com>
;; Version: 1.65
;; Keywords: convenience

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; A copy of the GNU General Public License can be obtained from the
;; Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA

;;; Commentary:

;; Emacs conveniently allows one to work on different parts of the same
;; buffer at the same time, but the rules governing buffer display are, for
;; some people's editing habits, less than ideal.  Suppose for example that
;; one is editing two parts of buffer <buf> in windows <win1> and <win2>,
;; switches briefly to another buffer in <win2>, then returns to editing
;; <buf> in <win2>.  This latter window will now display the same part of
;; <buf> as <win1>, rather than the portion that one was just recently
;; editing in it.  Per-window-point creates persistent values of point and
;; window-start, so that in cases like that just described <win2> will return
;; to its previous position in <buf>.

;; In some cases, such as looking up a function definition via
;; `describe-function', it makes sense for per-window-point to allow other
;; Lisp programs to fix the value of point.  The package is reasonably
;; intelligent in identifying when when it should do so.  Further control
;; over repositioning is provided by the variables `pwp-no-reposition-names',
;; `pwp-no-reposition-regexps', and `pwp-reposition-tests'.  Note also that
;; the package always ignores minibuffer windows.

;; To install the package, put this file in your load path and put:
;;
;;  (require 'per-window-point)
;;
;; in your .emacs.  To toggle per-window-point on and off, use the command
;; `pwp-mode', or place 
;;
;;  (pwp-mode 1)
;;
;; in your .emacs to enable it automatically.

;; A Note on v24 (July, 2011):  The buffer display routines in v24 are
;; currently being rewritten in preparation for the release of v24.1.  I'm
;; not going to try to keep up with these changes until the relevant code
;; stabilizes.  Until then, users who build v24 from source using a recent rev
;; might see irregular behavior.

;;; Code: 

(unless (version<= "22" emacs-version)
  (error "Per-window-point requires at least version 22"))

;;; ---------------------------------------------------------------------
;;; User Options
;;; ---------------------------------------------------------------------

(defgroup per-window-point nil
  "Enable each window to remember its value of point in each buffer."
  :group 'convenience)

(defcustom pwp-no-reposition-regexps '("^\\*.+\\*$")
  "Per-Window-Point does not reposition a buffer whose name matches a regexp in this list."
  :group 'per-window-point
  :type '(repeat regexp))

(defcustom pwp-no-reposition-names nil
  "Per-Window-Point does not reposition a buffer whose name is an element of this list."
  :group 'per-window-point
  :type '(repeat string))

(defcustom pwp-reposition-tests nil
  "List of functions that control whether per-window-point positions point in a buffer.
When the buffer displayed in a window changes, per-window-point calls each
function in this list with two arguments, the window in question
and the buffer about to be displayed.  If any function returns
nil, per-window-point does not position the buffer."
  :group 'per-window-point
  :type 'hook)

(defcustom pwp-mode-hook nil 
  "Hook run when enabling and disabling per-window-point mode."
  :group 'per-window-point
  :type 'hook)

(defcustom pwp-mode-on-hook nil 
  "Hook run when enabling per-window-point mode."
  :group 'per-window-point
  :type 'hook)

(defcustom pwp-mode-off-hook nil 
  "Hook run when disabling per-window-point mode."
  :group 'per-window-point
  :type 'hook)

;;; ---------------------------------------------------------------------
;;; Internal Variables
;;; ---------------------------------------------------------------------

(defvar pwp-mode nil 
  "Non-nil if per-window-point mode is enabled.  

Do not set this variable directly.  Use the command
`pwp-mode' instead.  See the documentation of that command
for a description of the mode.")

;; Alist that records all per-window-point's data. Each element is of the
;; form (WIN BUF-DATA BUF-DATA ...). Each BUF-DATA is of the form (BUFFER
;; MARKER MARKER), where the markers record, respectively, the last values
;; for window-point and window-start for BUFFER in WIN.  (We can't store the
;; BUF-DATA for each window in a window-parameter because (a)
;; window-parameters aren't preserved by save-window-excursion, and (b)
;; they're not available on v22.)
(defvar pwp-alist nil)

(defconst pwp-hook-assignments 
  '((temp-buffer-setup-hook . pwp-before-temp-buffer)
    (window-configuration-change-hook . pwp-forget-dead-windows)
    (delete-frame-functions . pwp-forget-frame-windows)
    (kill-buffer-hook . pwp-forget-dead-buffer)))

(defconst pwp-advised-fns 
  (append '(switch-to-buffer
            set-window-buffer
            replace-buffer-in-windows
            kill-buffer
            bury-buffer)
          (if (version< emacs-version "23") 
              '(display-buffer))))

;;; ---------------------------------------------------------------------
;;; Mode Definition
;;; ---------------------------------------------------------------------

(defun pwp-mode (&optional arg) 
  "Toggle per-window-point mode on and off.

With argument ARG, turn per-window-point mode on if and only if ARG is t or positive.

Per-window-point mode changes how Emacs selects point when displaying a
buffer in a window.  While pwp-mode is enabled, each window
keeps a record of the last value of point in every buffer that
has been displayed in that window.  When switched back to one of
those buffers, the window will display that portion of the buffer
that was last displayed in that window.  

The mode is intelligent in inferring when it should defer to
other programs in setting point.  Further control over when
repositioning should happen is provided by the variables
`pwp-no-reposition-names', `pwp-no-reposition-regexps',
and `pwp-reposition-tests'."
  (interactive "P")
  (setq pwp-mode (if (not arg)
                         (not pwp-mode)
                       (> (prefix-numeric-value arg) 0)))
  (if pwp-mode
      ;; Enabling
      (progn 
        (ad-enable-regexp "per-window-point")
        (dolist (fn pwp-advised-fns)
          (ad-activate fn t))
        (dolist (hook pwp-hook-assignments)
          (add-hook (car hook) (cdr hook)))
        (run-hooks 'pwp-mode-on-hook)
        (message "Per-window-point mode enabled"))
    ;; Disabling
    (setq pwp-alist nil)      
    (ad-disable-regexp "per-window-point")
    (dolist (fn pwp-advised-fns)
      (ad-activate fn))
    (dolist (hook pwp-hook-assignments)
      (remove-hook (car hook) (cdr hook)))
    (run-hooks 'pwp-mode-off-hook)
    (message "Per-window-point mode disabled"))
  (run-mode-hooks 'pwp-mode-hook))

;;; ---------------------------------------------------------------------
;;; Advising Primitives
;;; ---------------------------------------------------------------------

;; The following are the primitives that change which buffers are displayed
;; in windows.  We advise them so that they record window-point and
;; window-start for the relevant window(s) before a change in display, then
;; call the repositioning function after the change in display.

(defadvice switch-to-buffer (around per-window-point)
  (pwp-register-win (selected-window))
  ad-do-it
  (pwp-reposition (selected-window)))

(defadvice set-window-buffer (around per-window-point)
  (pwp-register-win (ad-get-arg 0))
  ad-do-it
  (pwp-reposition (ad-get-arg 0)))

(when (version< emacs-version "23")
  (defadvice display-buffer (around per-window-point)
    (mapc #'pwp-register-win (window-list))
    ad-do-it
    (pwp-reposition ad-return-value)))

(defadvice replace-buffer-in-windows (around per-window-point)
  (let* ((buf (or (ad-get-arg 0) (current-buffer)))
         (winlist (get-buffer-window-list buf 'no-minibuf t)))
    (mapc #'pwp-register-win winlist)
    ad-do-it
    (mapc #'pwp-reposition winlist)))

;; The following two primitives call buffer display functions from C code,
;; bypassing our advice.  So we also advise them.

(defadvice bury-buffer (around per-window-point)
  ;; Bury buffer only changes which buffer is displayed if called with nil
  ;; argument and if the current buffer is displayed in the selected
  ;; window.  That's the case we care about.
  (if (or (ad-get-arg 0)
          (not (eq (current-buffer) (window-buffer (selected-window)))))
      ad-do-it
    (pwp-register-win (selected-window))
    ad-do-it
    (pwp-reposition (selected-window))))

(defadvice kill-buffer (around per-window-point)
  (let* ((buf (or (ad-get-arg 0) (current-buffer)))
         ;; Record windows we'll need to reposition.  
         (winlist (get-buffer-window-list buf 'no-minbuf t)))
    ad-do-it
    ;; Kill-buffer returns non-nil only when the buffer was successfully
    ;; killed, which is the only case in which we need to act.
    (when ad-return-value 
      (mapc #'pwp-reposition winlist))))

;; The special form with-output-to-temp-buffer also calls one of our advised
;; primitives from within C code.  But here we have a hook we can use, so we
;; don't need advice.  (We don't call for repositioning after display, on the
;; assumption that this form is only used when generating new content for the
;; temp buffer, in which case repositioning would be pointless.)
(defun pwp-before-temp-buffer () 
  (mapc #'pwp-register-win (window-list nil 'no-minibuf)))

;;; ---------------------------------------------------------------------
;;; List Maintenance
;;; ---------------------------------------------------------------------

;; Called when a buffer is about to be killed; removes info about that buffer
;; from pwp-alist.
(defun pwp-forget-dead-buffer ()
  (setq pwp-alist 
        (mapcar #'(lambda (x) (delq (assq (current-buffer) x) x))
                pwp-alist)))

;; Called when the window configuration changes; removes elements from
;; pwp-alist that are associated with dead windows.
(defun pwp-forget-dead-windows ()
  (setq pwp-alist 
        (delq nil (mapcar #'(lambda (x) (if (window-live-p (car x))
                                            x
                                          (pwp-kill-markers x)
                                          nil))
                          pwp-alist))))

;; Called when a frame is deleted (that event doesn't run the window
;; configuration change hook); removes any windows that become dead as a
;; result of frame deletion.
(defun pwp-forget-frame-windows (frame)
  (let (win-data)
    (dolist (win (window-list frame 'no-minibuf))
      (setq win-data (assq win pwp-alist)
            pwp-alist (delq win-data pwp-alist))
      (pwp-kill-markers win-data))))

(defun pwp-kill-markers (win-data)
  (dolist (buf-data (cdr win-data))
    (move-marker (nth 1 buf-data) nil)
    (move-marker (nth 2 buf-data) nil)))

;;; ---------------------------------------------------------------------
;;; Recording Data
;;; ---------------------------------------------------------------------

;; Called with argument WIN, records window-point and window-start for the
;; buffer currently displayed in WIN.
(defun pwp-register-win (win)
  ;; Never bother with minibuffer windows.
  (when (and (not (window-minibuffer-p win))
             (window-live-p win))
    ;; Get window data from the main alist, then buffer data from WIN's own
    ;; alist.  
    (let* ((buf (window-buffer win)) 
           (win-data (pwp-get-win-data win))
           (buf-data (pwp-get-buf-data buf win-data)))
      ;; Update the markers.
      (set-marker (nth 1 buf-data) (window-point win) buf)
      (set-marker (nth 2 buf-data) (window-start win) buf))))

;; Called with argument WIN, returns the element of `pwp-alist'
;; that has WIN as key.  If no such element exists, add one to pwp-alist
;; and return it.
(defun pwp-get-win-data (win)
  (or (assq win pwp-alist)
      (car (push (list win) pwp-alist))))

;; Called with argument BUF and WIN-DATA (an element of `pwp-alist'),
;; returns the element of WIN-DATA that has BUF as key.  If no such element
;; exists, add one to WIN-DATA and return it.
(defun pwp-get-buf-data (buf win-data)
  (or (assq buf win-data)
      (let ((new-buf-data (list buf (make-marker) (make-marker))))
        (nconc win-data (list new-buf-data))
        new-buf-data)))

;;; ---------------------------------------------------------------------
;;; Repositioning Re-displayed Buffers
;;; ---------------------------------------------------------------------

(defun pwp-reposition (win)
  (when (window-live-p win)
    (let ((buf (window-buffer win)))
      ;; First, check to see whether BUF is one we should ignore in WIN.
      (unless (pwp-exception-p buf win)
        ;; If not, check to see if there's point and window-start info for
        ;; displaying BUF in WIN. Reposition if so.
        (let ((data (assq buf (assq win pwp-alist))))
          (when data
            (set-window-point win (nth 1 data))
            (set-window-start win (nth 2 data))))))))

;; Function called to determine whether per-window-point should reposition a
;; buffer.  If it returns t, per-window-point does not reposition.
(defun pwp-exception-p (buf win)
  (or (pwp-defer-to-program-p buf win)
      (pwp-buffer-name-exception-p buf)
      (pwp-run-reposition-tests buf win)))

;; Check to see whether a lisp program has repositioned point in BUF, in
;; which case return t.  (For example, when looking up a function definition
;; via `describe-function', point is moved to the function definition before
;; the library that defines the function is displayed; we then don't want to
;; move point away from the definition after the library is displayed.)  The
;; test used here will return the wrong answer in two corner cases that (I
;; hope) are extremely uncommon.
(defun pwp-defer-to-program-p (buf win)
  (let ((point (with-current-buffer buf (point)))
        (l1 (mapcar 
             #'(lambda (x) (window-point x))
             (delq win (get-buffer-window-list buf 'no-minibuf t))))
        (l2 (mapcar 
             #'(lambda (x) 
                 (if (not (eq buf (window-buffer (car x))))
                     (pwp-safe-marker-pos (cadr (assq buf x)))))
             pwp-alist)))
    (not (or (memq point l1)
             (memq point l2)))))

(defun pwp-safe-marker-pos (m)
  (if (markerp m) 
      (marker-position m)))

;; Check to see if BUF's name matches against disallowed names or disallowed
;; regexps.
(defun pwp-buffer-name-exception-p (buf)
  (let ((name (buffer-name buf)))
    (or (member name pwp-no-reposition-names)
        (memq t (mapcar #'(lambda (x) (string-match x name)) 
                        pwp-no-reposition-regexps)))))

;; Check WIN and BUF against test functions the user has supplied.  
(defun pwp-run-reposition-tests (buf win)
 (memq nil (mapcar #'(lambda (x) (funcall x buf win))
                   pwp-reposition-tests)))

(provide 'per-window-point)

;;; per-window-point.el ends here
