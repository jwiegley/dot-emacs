;;; xgtags.el --- gtags facility for Emacs

;;
;; Copyright (c) 2006 Marco Gidde
;;
;; Author: Marco Gidde <marco.gidde@tiscali.de>
;; Maintainer: Marco Gidde <marco.gidde@tiscali.de>
;; URL: http://home.tiscali.de/mgidde/source/xgtags.el
;;
;; This program is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free Software
;; Foundation; either version 2, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
;; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
;; details.

;; You should have received a copy of the GNU General Public License along with
;; GNU Emacs; see the file COPYING.  If not, write to the Free Software
;; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

;; $Id: xgtags.el,v 1.46 2006/06/22 13:02:29 mgidde Exp $

;;; Commentary:
;;
;; xgtags.el provides an interface to the GLOBAL
;; (http://www.gnu.org/software/global) cross-refencing tools. While
;; gtags.el, that comes with the GLOBAL distribution, is more a
;; replacement for emacs' own find-tag/pop-tag-mark facility with some
;; extra stuff, xtags.el tries to permit the same functionality as
;; gtags.el, but behaves more like xcscope.el, the emacs interface for
;; cscope (http://cscope.sourceforge.net).
;;
;; xgtags consists of xgtags-mode, a minor that should work with any
;; major mode, especially the programming modes, and
;; xgtags-select-mode which presents the result of the last query to
;; the user.
;;
;;
;;; Installation
;;
;; To use xgtags copy this file to some place where emacs can find it,
;; if necessary add the path you chose to the load-path variable. In
;; your .emacs add the line
;;
;;	(require 'xgtags)
;;
;; In any buffer you can now toggle xgtags-mode by calling the
;; interactive command with same name. Since this is a bit annoying,
;; you might choose to turn it on for some specific modes. For c-mode
;; you can add something like the following snippet to your .emacs
;; file. Other modes provide similar hooks.
;;
;;         (add-hook 'c-mode-common-hook
;;                   (lambda ()
;; 		        (xgtags-mode 1)))
;;
;; After that you can use the predefined keybindings to query your
;; GLOBAL database. Call 'describe-function RET xgtags-mode' to get an
;; overview of those bindings.
;;
;;
;;; TODO:
;; - BUG: return in selection list
;; - show the database in the *xgtags* buffer
;; - customizable keybindings?
;;


;;; Dependencies

(eval-when-compile
  (require 'cl))
(require 'easymenu)


(defconst xgtags-running-xemacs (featurep 'xemacs)
  "Whether we are running XEmacs/Lucid Emacs")

(defgroup xgtags nil
  "Using gtags and global for crossrefencing"
  :group 'tools)

(defvar xgtags-mode-map nil
  "Keymap used in xgtags minor mode.")


;;; Faces

(defface xgtags-match-face
  '((((class color) (background dark))
     (:foreground "cyan"))
    (((class color) (background light))
     (:foreground "magenta"))
    (t (:bold t)))
  "Face used to highlight function name in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-match-selected-face
  '((((class color) (background dark))
     (:foreground "cyan" :bold t))
    (((class color) (background light))
     (:foreground "magenta" :bold t))
    (t (:bold t)))
  "Face used to highlight selected function name in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-file-face
  '((((class color) (background dark))
     (:foreground "yellow"))
    (((class color) (background light))
     (:foreground "blue"))
    (t (:bold t)))
  "Face used to highlight file name in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-file-selected-face
  '((((class color) (background dark))
     (:foreground "yellow" :bold t))
    (((class color) (background light))
     (:foreground "blue" :bold t))
    (t (:bold t)))
  "Face used to highlight selected file name in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-line-number-face
  '((((class color) (background dark))
     (:foreground "red"))
    (((class color) (background light))
     (:foreground "red"))
    (t (:bold t)))
  "Face used to highlight line number in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-line-number-selected-face
  '((((class color) (background dark))
     (:foreground "red" :bold t))
    (((class color) (background light))
     (:foreground "red" :bold t))
    (t (:bold t)))
  "Face used to highlight selected line number in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-line-face
  '((((class color) (background dark))
     (:foreground "green"))
    (((class color) (background light))
     (:foreground "black"))
    (t (:bold nil)))
  "Face used to highlight the rest of line in the *xgtags* buffer."
  :group 'xgtags)

(defface xgtags-line-selected-face
  '((((class color) (background dark))
     (:foreground "green" :bold t))
    (((class color) (background light))
     (:foreground "black" :bold t))
    (t (:bold nil)))
  "Face used to highlight the rest of line in the *xgtags* buffer."
  :group 'xgtags)


;;; Functions to support the customizations

(defun xgtags--set-overwrite-global-bindings (flag &optional keymap)
  (let ((map (or keymap (and (boundp 'xgtags-mode-map) xgtags-mode-map))))
    (cond
     ((not (keymapp map)))
     (flag (define-key map "\e*" 'xgtags-pop-stack)
           (define-key map "\e." 'xgtags-find-tag))
     (t (define-key map "\e*" nil)
        (define-key map "\e." nil)))))

(defun xgtags--set-overwrite-complete-bindings (flag &optional keymap)
  (let ((map (or keymap (and (boundp 'xgtags-mode-map) xgtags-mode-map))))
    (cond
     ((not (keymapp map)))
     (flag (define-key map "\e\t" 'xgtags-complete-tag))
     (t (define-key map "\e\t" nil)))))

(defun xgtags--set-support-mouse (flag &optional keymap)
  (let ((map (or keymap (and (boundp 'xgtags-mode-map) xgtags-mode-map))))
    (cond
     ((not (keymapp map)))
     (xgtags-running-xemacs
      (define-key map 'button3 (when flag 'xgtags-pop-stack))
      (define-key map 'button2 (when flag 'xgtags-find-tag-by-event)))
     (t
      (define-key map [mouse-3] (when flag 'xgtags-pop-stack))
      (define-key map [mouse-2] (when flag 'xgtags-find-tag-by-event))))))


;;; customization

(defcustom xgtags-overwrite-global-bindings t
  "*Should the default keybindings for tags, that is \M-. e.a., be
overwritten with the corresponding xgtags functionality?"
  :type 'boolean
  :group 'xgtags
  :set (lambda (symbol value)
         (set symbol value)
         (xgtags--set-overwrite-global-bindings value)))

(defcustom xgtags-overwrite-complete-bindings nil
  "*Should the default keybindings for symbol completition, that is
\M-<TAB>, be overwritten with the corresponding xgtags functionality?"
  :type 'boolean
  :group 'xgtags
  :set (lambda (symbol value)
         (set symbol value)
         (xgtags--set-overwrite-complete-bindings value)))

(defcustom xgtags-support-mouse t
  "*Should there be some default bindings for mouse-2 and mouse-3."
  :type 'boolean
  :group 'xgtags
  :set (lambda (symbol value)
         (set symbol value)
         (xgtags--set-support-mouse value)))

(defcustom xgtags-read-only nil
  "*When set to true, new files are opened in read only mode."
  :type 'boolean
  :group 'xgtags)

(defcustom xgtags-goto-tag 'always
  "*Whether to jump to the first query result."
  :type '(radio (const :tag "always" always)
                (const :tag "when unique" unique)
                (const :tag "never" never))
  :group 'xgtags)

(defcustom xgtags-show-paths 'absolute
  "*how to show paths in the selection buffer."
  :type '(radio (const :tag "Show absolute paths" absolute)
                (const :tag "Show relative paths" relative)
                (const :tag "Show expanded paths (true filename)" expanded))
  :group 'xgtags)

(defcustom xgtags-update-db nil
  "*Use this option when you like to automatically update your
database before calling 'global'. The options are no update at all, a
command to be called or an elisp function, that will be called with
the current rootdir."
  :type '(radio (const :tag "No update.")
                (string :tag "Command and options.")
                (function :tag "Elisp function to be called."))
  :group 'xgtags)

(defcustom xgtags-find-multiple-db nil
  "*When bound to a function this function is called with one
argument, namely the current directory, and should return a list of
directories with GTAGS databases. All databases are searched one after
another."
  :type 'function
  :group 'xgtags)

(defcustom xgtags-kill-buffers t
  "*Should the current buffer be killed when the stack entry is
popped?  Be careful: even buffers not opened by xgtags itself will be
killed!"
  :type 'boolean
  :group 'xgtags)

(defcustom xgtags-select-buffer-name "*xgtags*"
  "*Name to use as the select buffer."
  :type 'string
  :group 'xgtags)

(defcustom xgtags-rootdir nil
  "*Root directory of source tree."
  :type 'string
  :group 'xgtags)

(defconst xgtags--symbol-regexp "[A-Za-z_][A-Za-z_0-9]*"
  "Regexp matching tag name.")
(defconst xgtags--definition-regexp "#[ \t]*define[ \t]+\\|ENTRY(\\|ALTENTRY("
  "Regexp matching tag definition name.")
(defconst xgtags--tag-regexp "\\([^ \t]+\\)[ \t]+\\([0-9]+\\)[ \t]+\\([^ \t]+\\)[ \t]+\\([^\n]+\\)"
  "Regex matching the current output line for a tag.")
(defconst xgtags--file-regexp "\\([^ \t]+\\)[ \t]+\\([0-9]+\\)[ \t]+\\([^ \t\n]+\\)"
  "Regex matching the current output line for a tag.")

(defvar xgtags--completition-table nil
  "xgtags complete obarray.")
(defvar xgtags--history-list nil
  "xgtags history list.")

(defvar xgtags-minor-mode-text " xgtags"
  "xgtags text to be shown in the mode line.")
(setq xgtags-mode-map
      (let ((keymap (make-sparse-keymap))
            (sub-keymap (make-sparse-keymap)))
        (define-key keymap "\C-cw" sub-keymap)
        (define-key sub-keymap "d" 'xgtags-find-tag)
        (define-key sub-keymap "c" 'xgtags-find-rtag)
        (define-key sub-keymap "s" 'xgtags-find-symbol)
        (define-key sub-keymap "g" 'xgtags-find-with-grep)
        (define-key sub-keymap "i" 'xgtags-find-with-idutils)
        (define-key sub-keymap "n" 'xgtags-select-next-tag)
        (define-key sub-keymap "p" 'xgtags-select-prev-tag)
        (define-key sub-keymap "\t" 'xgtags-make-complete-list)
        (define-key sub-keymap "u" 'xgtags-pop-stack)
        ;;   (define-key sub-keymap "" 'xgtags-find-tag-from-here)
        (define-key sub-keymap "f" 'xgtags-find-file)
        ;;   (define-key sub-keymap "" 'xgtags-display-browser)
        (define-key sub-keymap "x" 'xgtags-switch-to-buffer)
        (define-key sub-keymap "\C-x" 'xgtags-switch-to-buffer-other-window)
        (define-key sub-keymap "r" 'xgtags-query-replace-regexp)
        (when xgtags-overwrite-global-bindings
          (xgtags--set-overwrite-global-bindings t keymap))
        (when xgtags-overwrite-complete-bindings
          (xgtags--set-overwrite-complete-bindings t keymap))
        (when xgtags-support-mouse
          (xgtags--set-support-mouse t keymap))
        keymap))

(defvar xgtags-select-mode-name "xgtags-select"
  "xgtags-select text to be shown in the mode line.")
(defvar xgtags-select-mode-map nil
  "Keymap used in xgtags select mode.")

(setq xgtags-select-mode-map
      (let ((keymap (make-sparse-keymap)))
        (define-key keymap "\e*" 'xgtags-pop-stack)
        (if (not xgtags-running-xemacs) nil
          (define-key keymap 'button3 'xgtags-pop-stack)
          (define-key keymap 'button2 'xgtags-select-tag-by-event))
        (if xgtags-running-xemacs nil
          (define-key keymap [mouse-3] 'xgtags-pop-stack)
          (define-key keymap [mouse-2] 'xgtags-select-tag-by-event))
        (define-key keymap "\^?" 'scroll-down)
        (define-key keymap " " 'scroll-up)
        (define-key keymap "\C-b" 'scroll-down)
        (define-key keymap "\C-f" 'scroll-up)
        (define-key keymap "k" 'previous-line)
        (define-key keymap "j" 'next-line)
        (define-key keymap "p" 'previous-line)
        (define-key keymap "n" 'next-line)
        (define-key keymap "q" 'xgtags-pop-stack)
        (define-key keymap "u" 'xgtags-pop-stack)
        (define-key keymap "\C-t" 'xgtags-pop-stack)
        (define-key keymap "\C-m" 'xgtags-select-tag-near-point)
        (define-key keymap "\e." 'xgtags-select-tag-near-point)
        keymap))

(defvar xgtags--tags nil
  "List of current tags.")
(defvar xgtags--selected-tag nil
  "The currently selected tag.")
(defvar xgtags--stack nil
  "Stack for tag browsing.")


;;; macros

(defmacro with-xgtags-environment (&rest body)
  `(let ((process-environment (copy-alist process-environment)))
     (when xgtags-rootdir
       (setenv "GTAGSROOT" xgtags-rootdir))
     ,@body))
(put 'with-xgtags-environment 'lisp-indent-function 0)

(defmacro* with-xgtags-buffer ((&key buffer save-excursion (read-only t))
                               &rest body)
  (let ((buffer-var (or buffer (gensym "buffer-"))))
    `(let ((,buffer-var (xgtags--get-buffer)))
       (,(if save-excursion 'save-excursion 'progn)
        (set-buffer ,buffer-var)
        (let ((buffer-read-only ,read-only))
          ,@body)))))
(put 'with-xgtags-buffer 'lisp-indent-function 1)


;;; utilities

(defun xgtags--list-sans-nil (&rest args)
  "Build a list from ARGS but leave nils out."
  (let ((result nil))
    (dolist (arg args (nreverse result))
      (when arg
        (push arg result)))))

(defun xgtags--token-at-point ()
  "Return a default tag to search for, based on the text at point."
  (save-excursion
    (cond
     ((looking-at "[0-9A-Za-z_]")
      (while (looking-at "[0-9A-Za-z_]")
        (forward-char -1))
      (forward-char 1))
     (t
      (while (looking-at "[ \t]")
        (forward-char 1))))
    (when (and (bolp) (looking-at xgtags--definition-regexp))
      (goto-char (match-end 0)))
    (when (looking-at xgtags--symbol-regexp)
      (match-string-no-properties 0))))

(defun xgtags--file-at-point ()
  "Return a default tag to search for, based on the text at point."
  (save-excursion
    (cond
     ((looking-at "[0-9A-Za-z_\.]")
      (while (looking-at "[0-9A-Za-z_\.]")
        (forward-char -1))
      (forward-char 1)))
    (when (looking-at "[0-9A-Za-z_\.]+")
      (match-string-no-properties 0))))

(defun xgtags--function-p ()
  "Is it a function?"
  (save-excursion
    (while (and (not (eolp)) (looking-at "[0-9A-Za-z_]"))
      (forward-char 1))
    (while (and (not (eolp)) (looking-at "[ \t]"))
      (forward-char 1))
    (looking-at "(")))

(defun xgtags--definition-p ()
  "Is it a definition?"
  (save-excursion
    (if (or (and (string-match "\.java$" buffer-file-name)
                 (looking-at "[^(]+([^)]*)[ \t]*{"))
            (bolp))
        t
      (forward-word -1)
      (cond
       ((looking-at "define")
        (forward-char -1)
        (while (and (not (bolp)) (looking-at "[ \t]"))
          (forward-char -1))
        (and (bolp) (looking-at "#")))
       ((looking-at "ENTRY\\|ALTENTRY")
        (bolp))))))

(defun xgtags--insert-with-face (string face)
  (let ((start (point)))
    (insert string)
    (put-text-property start (point) 'face face)))

(defun xgtags--update-minor-mode-text ()
  (let ((length (length xgtags--stack)))
    (if (zerop length)
        (setq xgtags-minor-mode-text " xgtags")
      (setq xgtags-minor-mode-text (format " xgtags[%d]" length)))))


;;; handling tags and the tags list

(defstruct xgtags--tag
  query abs-file file line match)

(defun xgtags--make-tag (&rest args)
  (let* ((tag (apply 'make-xgtags--tag args))
         (abs-file (expand-file-name (xgtags--tag-file tag))))
    (if (eq xgtags-show-paths 'expanded)
        (let ((expanded (file-truename abs-file)))
          (setf (xgtags--tag-abs-file tag) expanded
                (xgtags--tag-file tag) expanded))
      (setf (xgtags--tag-abs-file tag) abs-file))
    tag))

(defun xgtags--tag-position (tag)
  "Returns the position index of TAG in the tag-list."
  (let ((pos 0)
        (found nil)
        (tags xgtags--tags))
    (while (and tags (not (setq found (eq (car tags) tag))))
      (setq pos (1+ pos))
      (setq tags (cdr tags)))
    (when found
      pos)))

(defun* xgtags--next-tag (tag &optional (n 1))
  "Returns the N-th tag that follows TAG in the tag list or nil."
  (assert tag nil "No tag in call to xgtags--next-tag")
  (let ((pos (xgtags--tag-position tag)))
    (when (and (>= pos 0) (>= (+ pos n) 0))
      (nth (+ pos n) xgtags--tags))))

(defun xgtags--insert-tags (tags)
  "This function recieves a list of tags, erases the current buffer
and then inserts the tags nicely."
  (erase-buffer)
  (let ((current-file nil))
    (dolist (tag tags)
      (let ((file (xgtags--tag-file tag)))
        (unless (equal current-file file)
          (when current-file
            (insert "\n"))
          (setq current-file file)
          (xgtags--insert-tag-file tag)
          (insert "\n")))
      (xgtags--insert-tag tag)
      (insert "\n"))))

(defun xgtags--insert-tag-file (tag)
  "Insert the file entry TAG into the current buffer."
  (xgtags--insert-with-face (xgtags--tag-file tag) 'xgtags-file-face))

(defun xgtags--insert-tag (tag)
  "Insert a single tag TAG at point in the current buffer"
  (let ((start (point))
        (query (xgtags--tag-query tag))
        (line (xgtags--tag-line tag))
        (match (xgtags--tag-match tag))
        (selected-p (eq tag xgtags--selected-tag)))
    (xgtags--insert-with-face query
                              (if selected-p
                                  'xgtags-match-selected-face
                                'xgtags-match-face))
    (insert "[")
    (xgtags--insert-with-face (number-to-string line)
                              (if selected-p
                                  'xgtags-line-number-selected-face
                                'xgtags-line-number-face))
    (when match
      (insert "]\t\t")
      (xgtags--insert-with-face match (if selected-p
                                          'xgtags-line-selected-face
                                        'xgtags-line-face)))
    (put-text-property start (point) 'xgtags-tag tag)))

(defun xgtags--update-tag (tag)
  "Searches the tag TAG in the current buffer and replaces the current
representation with an updated one."
  (let ((region (xgtags--find-tag-region tag)))
    (when region
      (delete-region (car region) (cdr region))
      (goto-char (car region))
      (xgtags--insert-tag tag))))

(defun xgtags--find-tag-region (tag)
  "If TAG is found in the current buffer this functions returns a
list with the start and end positions, otherwise it returns nil"
  (when tag
    (let ((start (text-property-any (point-min) (point-max) 'xgtags-tag tag)))
      (when start
        (cons start (next-single-property-change start 'xgtags-tag))))))

(defun xgtags--select-tag (tag &optional update)
  "Make TAG the selected tag. If UPDATE is not nil, try to find the
previous selected tag and TAG in the current buffer, update their
representation and move point to the beginning of TAG."
  (let ((old-sel xgtags--selected-tag))
    (setq xgtags--selected-tag tag)
    (when update
      (xgtags--update-tag old-sel)
      (xgtags--update-tag xgtags--selected-tag)
      (goto-char (car (xgtags--find-tag-region xgtags--selected-tag)))
      (when (get-buffer-window (current-buffer))
        (set-window-point (get-buffer-window (current-buffer)) (point))))))

(defun xgtags--find-tag-near-point (&optional backwards)
  "Find the next selectable tag and move point to its beginning. If
there is none at the current line, step a line forward or backward to
find one."
  (beginning-of-line)
  (while (when (not (get-text-property (point) 'xgtags-tag))
           (zerop (forward-line (and backwards -1)))))
  (get-text-property (point) 'xgtags-tag))

(defun xgtags--follow-tag (tag)
  "Jump to the place that TAG points to."
  (interactive)
  (find-file (xgtags--tag-abs-file tag))
  (setq buffer-read-only (or buffer-read-only xgtags-read-only))
  (xgtags-mode 1)
  (goto-line (xgtags--tag-line tag))
  (let ((match (xgtags--tag-query tag))
        (found nil)
        (lines 0))
    (while (and (not found) (< lines 5))
      (let ((start (save-excursion (forward-line (- lines))
                                   (point)))
            (end (save-excursion (forward-line lines)
                                 (end-of-line)
                                 (point))))
        (save-excursion
          (goto-char start)
          (setq found (search-forward-regexp match end t))))
      (setq lines (1+ lines)))
    (when found
      (goto-char (match-beginning 0)))))

(defun xgtags--map-tags (func)
  "Maps over all tags in the *xgtags* buffer, jumps to the tag and
funcalls FUNC with the match as argument."
  (mapc (lambda (tag)
          (with-xgtags-buffer (:read-only nil)
                              (xgtags--select-and-follow-tag tag)
                              (funcall func (xgtags--tag-query tag))))
        xgtags--tags))

(defun xgtags--test-map-tags ()
  (interactive)
  (xgtags--map-tags
   (lambda (match)
     (message "foo: %s" match)
     (when (search-forward-regexp match
                                  (save-excursion (end-of-line) (point))
                                  t)
       (goto-char (match-beginning 0))
       (set-mark (match-end 0))
       (unless (y-or-n-p "More? ")
         (return-from xgtags--test-map-tags))))))


;;; handling the context and the context stack

(defstruct xgtags--context
  buffer point tags selected-tag)

(defun xgtags--make-context ()
  "Create a context object."
  (make-xgtags--context :buffer (current-buffer)
                        :point (point-marker)
                        :tags xgtags--tags
                        :selected-tag xgtags--selected-tag))

(defun xgtags--stacked-p (buffer)
  "If BUFFER exists on the xgtags stack."
  (memq buffer (mapcar 'xgtags--context-buffer xgtags--stack)))

(defun xgtags--push-context ()
  (first (push (xgtags--make-context) xgtags--stack)))

(defun xgtags--pop-context ()
  "Pop context from stack and return it."
  (pop xgtags--stack))


;;; handling the selection buffer

(defun xgtags--get-buffer ()
  "Return the selection buffer. If it was kill recreate and fill it
with the previous query results."
  (let ((buffer (get-buffer xgtags-select-buffer-name)))
    (unless buffer
      (setq buffer (get-buffer-create xgtags-select-buffer-name))
      ;; using with-xgtags-buffer here is not possible because it uses
      ;; xgtags--get-buffer itself
      (save-excursion
        (set-buffer buffer)
        (when xgtags--stack
          (xgtags--insert-tags xgtags--tags))
        (xgtags-select-mode)))
    buffer))

(defun xgtags--select-update-mode-text (tag)
  (let ((pos (xgtags--tag-position tag)))
    (if pos
        (setq mode-name (format "%s[%d/%d]"
                                xgtags-select-mode-name
                                (1+ pos) (length xgtags--tags)))
      (setq mode-name (format "%s[%d]"
                              xgtags-select-mode-name
                              (length xgtags--tags))))))

(defun xgtags--update-buffer (context)
  (let ((tags (xgtags--context-tags context))
        (selected-tag (xgtags--context-selected-tag context)))
    (xgtags--update-minor-mode-text)
    (when tags
      (with-xgtags-buffer (:save-excursion t :read-only nil)
                          (setq xgtags--tags tags)
                          (xgtags--insert-tags tags)
                          (xgtags--select-tag selected-tag t)
                          (xgtags--select-update-mode-text selected-tag)))))

(defun xgtags--select-and-follow-tag (tag)
  "Select TAG and follow the link."
  (when tag
    (with-xgtags-buffer (:read-only nil)
                        (xgtags--select-tag tag t)
                        (xgtags--select-update-mode-text tag))
    (xgtags--follow-tag tag)))


;;; options of the GLOBAL program

(defvar xgtags--gtags-options
  '((path . "%s: path not found")
    (grep . "%s: pattern not found")
    (idutils . "%s: token not found")
    (symbol . "%s: symbol not found")
    (reference . "%s: reference not found")
    (file . "%s: file not found")
    (absolute)))

(defun xgtags--option-string (symbol)
  (when symbol
    (assert (assoc symbol xgtags--gtags-options) t
            "Unknown gtags option symbol: %s" symbol)
    (concat "--" (symbol-name symbol))))

(defun xgtags--option-error-msg (symbol)
  (let ((opt (assoc symbol xgtags--gtags-options)))
    (if (and opt (cdr opt))
        (cdr opt)
      "%s: tag not found")))


;;; GLOBAL process handling

(defun xgtags--call-global (buffer-dir option tagname)
  (message "Searching %s ..." tagname)
  (let ((tags nil))
    (xgtags--do-in-all-directories
     buffer-dir
     (lambda (dir)
       (when dir
         (message "Searching %s in %s ..." tagname dir))
       (let ((xgtags-rootdir (and dir (file-name-as-directory dir))))
         (with-xgtags-environment
          (when xgtags-update-db
            (xgtags--update-db xgtags-rootdir))
          (with-temp-buffer
            (if (zerop (apply #'call-process "global" nil t nil
                              (xgtags--list-sans-nil
                               "--cxref"
                               (xgtags--option-string option)
                               (unless (eq xgtags-show-paths 'relative)
                                 "--absolute")
                               tagname)))
                (setq tags (append tags (xgtags--collect-tags-in-buffer)))
              (message (buffer-substring (point-min)(1- (point-max))))))))))
    (message "Searching %s done" tagname)
    tags))

(defun xgtags--do-in-all-directories (buffer-dir func)
  (let ((dirs (if xgtags-find-multiple-db
                  (funcall xgtags-find-multiple-db buffer-dir)
                (list xgtags-rootdir))))
    (dolist (dir dirs)
      (funcall func dir))))

(defun xgtags--update-db (directory)
  (cond
   ((stringp xgtags-update-db)
    (let ((default-directory directory)
          (split (split-string xgtags-update-db)))
      (apply #'call-process (car split) nil nil nil (cdr split))))
   ((functionp xgtags-update-db)
    (funcall xgtags-update-db directory))
   (t (error "xgtags-update-db has an unsupported type"))))

(defun xgtags--collect-tags-in-buffer ()
  "This function searches the current buffer for tag items and returns
a list with those."
  (save-excursion
    (goto-char (point-min))
    (let ((tags nil))
      (while (not (eobp))
        (cond
         ((looking-at xgtags--tag-regexp)
          (let* ((query (match-string-no-properties 1))
                 (line (string-to-number (match-string-no-properties 2)))
                 (file (match-string-no-properties 3))
                 (match (match-string-no-properties 4)))
            (push (xgtags--make-tag :query query
                                    :file file
                                    :line line
                                    :match match) tags)))
         ((looking-at xgtags--file-regexp)
          (let* ((query (match-string-no-properties 1))
                 (line (string-to-number (match-string-no-properties 2)))
                 (file (match-string-no-properties 3)))
            (push (xgtags--make-tag :query query
                                    :file file
                                    :line line) tags))))
        (forward-line))
      (nreverse tags))))


;;; navigating the selection buffer

(defun xgtags--select-next-prev-tag (arg)
  "Select the next or previous tag in the previous select buffer."
  (let ((tag (xgtags--next-tag xgtags--selected-tag arg)))
    (assert tag nil "The %s of the *xgtags* buffer has been reached"
            (if (> arg 0) "end" "beginning"))
    (xgtags--select-and-follow-tag tag)))

(defun xgtags-select-next-tag (&optional arg)
  "Select the next tag in the previous select buffer."
  (interactive "p")
  (xgtags--select-next-prev-tag arg))

(defun xgtags-select-prev-tag (&optional arg)
  "Select the previous tag in the previous select buffer."
  (interactive "p")
  (xgtags--select-next-prev-tag (- arg)))

(defun xgtags-select-tag-by-event (event)
  "Select a tag in [XGTAGS SELECT MODE] and move there."
  (interactive "e")
  (if xgtags-running-xemacs
      (goto-char (event-point event))
    (select-window (posn-window (event-end event)))
    (set-buffer (window-buffer (posn-window (event-end event))))
    (goto-char (posn-point (event-end event))))
  (xgtags-select-tag-near-point))


;;; finding and selecting tags

(defun xgtags--goto-tag (tagname &optional option)
  (let* ((window (selected-window))
         (file-name (buffer-file-name))
         (buffer-dir (and file-name (file-name-directory file-name)))
         (tags (xgtags--call-global buffer-dir option tagname))
         (num-tags (length tags)))
    (if (= num-tags 0)
        (message (xgtags--option-error-msg option) tagname)
      (xgtags--push-context)
      (xgtags--update-minor-mode-text)
      (with-xgtags-buffer (:save-excursion t :read-only nil)
                          (setq xgtags--tags tags)
                          (xgtags--insert-tags tags))
      (cond
       ((eq xgtags-goto-tag 'always)
        (when (/= num-tags 1)
          (xgtags-switch-to-buffer-other-window nil))
        (select-window window)
        (xgtags--select-and-follow-tag (first tags)))
       ((eq xgtags-goto-tag 'unique)
        (if (/= num-tags 1)
            (xgtags-switch-to-buffer-other-window t)
          (xgtags--select-and-follow-tag (first tags))))
       ((eq xgtags-goto-tag 'never)
        (xgtags-switch-to-buffer-other-window t))
       (t
        (error "Unrecognized value for xgtags-goto-tag: %s"
               xgtags-goto-tag))))))

(defun xgtags-select-tag-near-point ()
  "Select the tag near point and follow it."
  (interactive)
  (xgtags--select-and-follow-tag (xgtags--find-tag-near-point)))


;;; interactive commands

(defun xgtags-visit-rootdir ()
  "Tell tags commands the root directory of source tree."
  (interactive)
  (unless xgtags-rootdir
    (with-temp-buffer
      (setq xgtags-rootdir
            (if (zerop (call-process "global" nil t nil "-pr"))
                (file-name-as-directory (buffer-substring (point-min)
                                                          (1- (point-max))))
              default-directory))))
  (let ((input (read-file-name "Visit root directory: "
                               xgtags-rootdir xgtags-rootdir t)))
    (unless (equal "" input)
      (assert (file-directory-p input) t "%s is not directory" input)
      (setq xgtags-rootdir (expand-file-name input)))))

(defun* xgtags--find-with (dflt-prompt &key option
                                       (get-token 'xgtags--token-at-point)
                                       (history xgtags--history-list))
  (let* ((tagname (funcall get-token))
         (prompt (if tagname
                     (concat dflt-prompt " (default " tagname ") ")
                   (concat dflt-prompt " ")))
         (input (completing-read prompt xgtags--completition-table
                                 nil nil nil history tagname)))
    (xgtags--goto-tag input option)))

(defun xgtags-find-tag ()
  "Input tag name and move to the definition."
  (interactive)
  (xgtags--find-with "Find tag:"))

(defun xgtags-find-rtag ()
  "Input tag name and move to the referenced point."
  (interactive)
  (xgtags--find-with "Find tag (reference):" :option 'reference))

(defun xgtags-find-symbol ()
  "Input symbol and move to the locations."
  (interactive)
  (xgtags--find-with "Find symbol:" :option 'symbol))

(defun xgtags-find-with-grep ()
  "Input pattern, search with grep(1) and move to the locations."
  (interactive)
  (xgtags--find-with "Find pattern:" :option 'grep))
(defalias 'xgtags-find-pattern 'xgtags-find-with-grep)

(defun xgtags-find-with-idutils ()
  "Input pattern, search with id-utils(1) and move to the locations."
  (interactive)
  (xgtags--find-with "Find pattern:" :option 'idutils))

(defun xgtags-find-file ()
  "Input pattern and move to the top of the file."
  (interactive)
  (xgtags--find-with "Find file:"
                     :option 'path
                     :get-token 'xgtags--file-at-point
                     :history nil))

(defun xgtags-find-tag-from-here ()
  "Get the expression as a tagname around here and move there."
  (interactive)
  (let ((tagname (xgtags--token-at-point)))
    (when tagname
      (xgtags--goto-tag tagname (cond ((not (xgtags--function-p)) 'symbol)
                                      ((xgtags--definition-p) 'reference)
                                      (t nil))))))

(defun xgtags-find-tag-by-event (event)
  "Get the expression as a tagname around here and move there."
  (interactive "e")
  (if xgtags-running-xemacs
      (goto-char (event-point event))
    (select-window (posn-window (event-end event)))
    (set-buffer (window-buffer (posn-window (event-end event))))
    (goto-char (posn-point (event-end event))))
  (let ((tagname (xgtags--token-at-point)))
    (when tagname
      (xgtags--goto-tag tagname (cond ((not (xgtags--function-p)) 'symbol)
                                      ((xgtags--definition-p) 'reference)
                                      (t nil))))))

(defun xgtags-pop-stack ()
  "Move to previous point on the stack."
  (interactive)
  (let ((delete (and xgtags-kill-buffers
                     (not (xgtags--stacked-p (current-buffer)))))
        (context (xgtags--pop-context)))
    (assert context nil "The tags stack is empty")
    (when delete
      (kill-buffer (current-buffer)))
    (xgtags--update-buffer context)
    (switch-to-buffer (xgtags--context-buffer context))
    (goto-char (xgtags--context-point context))))

(defun xgtags-query-replace-regexp (to-string)
  "Run over the current *xgtags* buffer and to `query-replace-regexp'
for each tag."
  (interactive
   (list (read-from-minibuffer (format "Replace <%s> with: "
                                       (xgtags--tag-query
                                        (save-excursion
                                          (set-buffer (xgtags--get-buffer))
                                          (get-text-property (point) 'xgtags-tag))))
                               nil nil nil
                               query-replace-to-history-variable nil t)))
  (xgtags--map-tags
   (lambda (match)
     (query-replace-regexp match to-string nil
                           (point)
                           (save-excursion (end-of-line) (point))))))

(defun xgtags-parse-file ()
  "Input file name, parse it and show object list."
  (interactive)
  (let ((input (read-file-name "Parse file: "
                               nil nil t
                               (file-name-nondirectory buffer-file-name))))
    (assert (not (equal input "")) nil "No file speciafied")
    (xgtags--goto-tag (expand-file-name input) 'file)))

(defun xgtags-display-browser ()
  "Display current screen on hypertext browser."
  (interactive)
  (unless (and (not (equal (point-min) (point-max)))
               buffer-file-name)
    (let ((lno (save-excursion
                 (end-of-line)
                 (max 1 (count-lines (point-min) (point))))))
      (with-temp-buffer
        (unless (zerop (call-process "gozilla"  nil t nil
                                     (concat "+" (number-to-string lno))
                                     buffer-file-name))
          (message "%s" (buffer-string)))))))

(defun xgtags-make-complete-list ()
  "Make tag name list for completion."
  (interactive)
  (let* ((file-name (buffer-file-name))
         (buffer-dir (and file-name (file-name-directory file-name))))
    (message "Making completion list ...")
    (setq xgtags--completition-table (make-vector 511 0))
    (xgtags--do-in-all-directories
     buffer-dir
     (lambda (dir)
       (message "Making completion list in %s" dir)
       (let ((xgtags-rootdir (and dir (file-name-as-directory dir))))
         (with-xgtags-environment
          (with-temp-buffer
            (call-process "global" nil t nil "-c")
            (goto-char (point-min))
            (while (looking-at xgtags--symbol-regexp)
              (intern (match-string-no-properties 0) xgtags--completition-table)
              (forward-line)))))))
    (message "Making completion list ... Done")))

(defun xgtags-complete-tag ()
  ;;   "Perform tags completion on the text around point.
  ;; Completes to the set of names listed in the current tags table.
  ;; The string to complete is chosen in the same way as the default
  ;; for \\[find-tag] (which see)."
  (interactive)
  (unless xgtags--completition-table
    (error "No xgtags--completition-table created"))
  (while (looking-at "[ \t\n]")
    (backward-char 1))
  (let ((pattern (xgtags--token-at-point))
        (beg (match-beginning 0))
        (end (match-end 0))
        completion)
    (unless pattern
      (error "Nothing to complete"))
    (goto-char end)
    (setq completion (try-completion pattern xgtags--completition-table nil))
    (cond ((eq completion t))
          ((null completion)
           (message "Can't find completion for \"%s\"" pattern)
           (ding))
          ((not (string= pattern completion))
           (delete-region beg (point))
           (insert completion))
          (t
           (message "Making completion list...")
           (with-output-to-temp-buffer "*Completions*"
             (display-completion-list
              (all-completions pattern xgtags--completition-table)))
           (message "Making completion list...%s" "done")))))

(defun xgtags--switch-buffer (other-window jump-to-start-p)
  (with-xgtags-buffer (:buffer buffer)
                      (when jump-to-start-p
                        (goto-char (point-min)))
                      (if other-window
                          (switch-to-buffer-other-window buffer)
                        (switch-to-buffer buffer))))

(defun xgtags-switch-to-buffer (&optional jump-to-start-p)
  (interactive "P")
  (xgtags--switch-buffer nil jump-to-start-p))

(defun xgtags-switch-to-buffer-other-window (&optional jump-to-start-p)
  (interactive "P")
  (xgtags--switch-buffer t jump-to-start-p))


;;; definition and support for the minor mode

(easy-menu-define xgtags-menu
  xgtags-mode-map
  "xgtags menu"
  '("XGtags"
    [ "Find Tag" xgtags-find-tag t ]
    [ "Find Tag Reference" xgtags-find-rtag t ]
    [ "Find Symbol" xgtags-find-symbol t ]
    [ "Find Pattern With grep" xgtags-find-with-grep t ]
    [ "Find Pattern With idutils" xgtags-find-with-idutils t ]
    "-----------"
    [ "Find Previous Tag" xgtags-select-prev-tag t ]
    [ "Find Next Tag" xgtags-select-next-tag t ]
    [ "Query-replace Tag" xgtags-query-replace-regexp t ]
    "-----------"
    [ "Make Completion List" xgtags-make-complete-list t ]
    [ "Find File" xgtags-find-file t ]
    [ "Display in Browser" xgtags-display-browser t ]
    "-----------"
    [ "Parse File" xgtags-parse-file t ]
    [ "Visit Tags Directory" xgtags-visit-rootdir t ]))

(define-minor-mode xgtags-mode
  "Toggle xgtags-mode, a minor mode for browsing source code using GLOBAL.

Input tag name and move to the definition.
	\\[xgtags-find-tag]
Input tag name and move to the referenced point.
	\\[xgtags-find-rtag]
Input symbol and move to the locations.
	\\[xgtags-find-symbol]
Input pattern, search with grep(1) and move to the locations.
	\\[xgtags-find-with-grep]
Input pattern, search with id-utils(1) and move to the locations.
	\\[xgtags-find-with-idutils]
Input pattern and move to the top of the file.
	\\[xgtags-find-file]
Get the expression as a tagname around here and move there.
	\\[xgtags-find-tag-from-here]
Display current screen on hypertext browser.
	\\[xgtags-display-browser]
Get the expression as a tagname around here and move there.
	\\[xgtags-find-tag-by-event]
Move to previous point on the stack.
	\\[xgtags-pop-stack]
Make tag name list for completion.
	\\[xgtags-make-complete-list]

Key definitions:
\\{xgtags-mode-map}
Turning on xgtags-mode calls the value of the variable `xgtags-mode-hook'
with no args, if that value is non-nil."
  ;; The initial value.
  nil
  ;; The indicator for the mode line.
  xgtags-minor-mode-text
  ;; The minor mode bindings.
  'xgtags-mode-map)


;;; definition and support for the selection mode

(define-derived-mode xgtags-select-mode fundamental-mode xgtags-select-mode-name
  "Major mode for choosing a tag from tags list.

Select a tag in tags list and move there.
	\\[xgtags-select-tag-near-point]
Move to previous point on the stack.
	\\[xgtags-pop-stack]

Key definitions:
\\{xgtags-select-mode-map}
Turning on xgtags-select mode calls the value of the variable
`xgtags-select-mode-hook' with no args, if that value is non-nil."
  (setq buffer-read-only t
        truncate-lines t)
  (goto-char (point-min)))


;; ;;; process management

;; (defstruct xgtags--proc
;;   buffer proc cont output)

;; (defvar xgtags-procs nil)

;; (defun xgtags--make-proc (&rest args)
;;   (let ((proc (apply 'make-xgtags--proc args)))
;;     (push proc xgtags-procs)
;;     proc))

;; (defun xgtags--kill-proc (proc)
;;   (when (xgtags--proc-buffer proc)
;;     (kill-buffer (xgtags--proc-buffer proc)))
;;   (setf (xgtags--proc-buffer proc) nil)
;;   (setq xgtags-procs (delete proc xgtags-procs))
;;   proc)

;; (defun xgtags--proc-done-p (proc)
;;   (eq (process-status (xgtags--proc-proc proc)) 'exit))

;; (defun xgtags--run (prog-args &optional cont)
;;   (let ((process-connection-type nil))
;;     (lexical-let* ((buffer (generate-new-buffer "xgtags-proc"))
;; 		   (eproc (apply 'start-process "xgtags-prog" buffer prog-args))
;; 		   (proc (xgtags--make-proc :buffer buffer
;; 					    :proc eproc
;; 					    :cont cont)))
;;       (set-process-sentinel
;;        eproc
;;        (lambda (ignored-proc ignored-event)
;; 	 (save-excursion
;; 	   (message "Process: %s had the event `%s'" proc ignored-event)
;; 	   (set-buffer buffer)
;; 	   (when (xgtags--proc-cont proc)
;; 	     (funcall (xgtags--proc-cont proc) proc))
;; 	   (setf (xgtags--proc-output proc) (buffer-substring (point-min)
;; 							      (point-max)))
;; 	   (kill-buffer buffer))))
;;       proc)))

;; (defun xgtags--wait-for-procs (&rest procs)
;;   (let ((inhibit-redisplay nil))
;;     (while (memq 'nil (mapcar 'xgtags--proc-done-p procs))
;;       (message "wait for %s" (mapcar (lambda (proc)
;; 				       (process-status (xgtags--proc-proc proc)))
;; 				     procs))
;;       (sleep-for 0.1)
;;       (message "after")
;;       )))

;; (defun gaga ()
;;   (let ((p1 (xgtags--run '("sleep" "1")))
;; 	(p2 (xgtags--run '("sleep" "3")))
;; 	(p3 (xgtags--run '("echo" "tuuuuuuuuut"))))
;;     (xgtags--wait-for-procs p1 p2 p3)
;;     (accept-process-output)
;; ;;     (sit-for 0)
;;     (message "gaga done")
;;     (list p1 p2 p3)))

(provide 'xgtags)

;;; xgtags.el ends here
