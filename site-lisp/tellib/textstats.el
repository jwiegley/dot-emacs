;;; TEXTSTATS.EL --- Show text statistics

;; Copyright (C) 2001 Thomas Link

;; Author: Thomas Link AKA thomas DOT link AT a1 DOT net
;; Time-stamp: <2003-03-08>
;; Keywords: text statistics, word counting

(defvar textstats-version "1.5.0")
(defvar textstats-homepage "http://members.a1.net/t.link/filestats.html")
 
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	 See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

;;; Commentary:

;; Put this file into your load path -- type "\C-h v load-path" to
;; find a suitable directory. Put

;; (autoload 'textstats "textstats" "Display text statistics" t)

;; into your startup file, which is probably called "~/.emacs.el".
;; Invoke by typing "M-x textstats".

;; The cursor will remain in your main window; the textstats window
;; will disappear after a few seconds. In case this feature makes
;; troubles, set textstats-auto-hide-secs to 0.

;; Add your own definitions to the list 'textstats-list-optional'. See
;; the documentation by typing "\C-h v textstats-list". Examples:

;; (add-to-list 'textstats-list-optional
;;		   '(("Scheme" "Lisp" (lambda (buffer) (set-buffer buffer)
;;						    (equal comment-start ";")))
;;			"functions" 
;;			t
;;			(lambda () (textstats-search-forward "\n(define"))))

;; Using the new format, this can be defined like this:
;; (add-to-list 'textstats-list-optional
;;	     '(:name "vowels"
;;		     :how-many "[aeiouAEIOU]"
;;		     :view (lambda (buffer unit result)
;;			     (textstats-insert
;;			      buffer nil
;;			      (format "Wow, %s %s!" result unit)))))

;; Example:
;; Count words in LaTeX files using catdvi and wc:
;; (add-to-list
;;  'textstats-list-optional
;;  '(:name "LaTeX Summary"
;; 	 :mode "LaTeX"
;; 	 :accumulate nil
;; 	 :fun (lambda ()
;; 		(let* ((dvi (when buffer-file-name
;; 			      (concat (file-name-sans-extension buffer-file-name)
;; 				      ".dvi"))))
;;		   (when (and dvi (file-readable-p dvi))
;; 		    (shell-command-to-string
;; 		     (format "catdvi %S | wc" dvi)))))
;; 	 :view (lambda (buffer unit result)
;; 		 (let ((rl (car (read-from-string (concat "(" result ")")))))
;; 		   (textstats-insert
;; 		    buffer nil
;; 		    (textstats-format-result
;; 		     "CatDVI Words"
;; 		     (nth 1 rl)
;; 		     (format " (%s lines; %s chars)"
;; 			     (nth 0 rl) (nth 2 rl))))))))

;;; Credits:

;; This package is inspired by or loosely based upon work done by:
;; - Colin Walters ... "ibuffer.el"
;; - Chris Beggy <chrisb AT kippona.com>, sshteingold AT cctrading.com
;;   and ccurley AT trib.com ... "sds-word-count.el"
;; - Bob Glickstein ... "wcount.el"
;; - Alex Schroeder <alex AT gnu.org> ... "wiki.el"

;;; Change log:

;; textstats.el

;; 1.5
;; - Integration with tellib.el; removed references to concordance.el
;; - `textstats-auto-hide-predicates'
;; - `textstats-insert' text is not a &rest argument anymore (possibly
;; incompatible change)
;; `textstats-insert' and `textstats-insert-this' not take a separator
;; string as additional argumen
;; - Don't show statistic if the result is nil.
;; - Highlight statistic units in output (see `textstats-header-face').

;; 1.4
;; - Splitted filestats.el into textstats.el and concordance.el. All
;; identifiers were renamed from "filestats-" to "textstats-".

;; Under the name of "filestats.el"
;; 1.3
;; - New: File specific stats via file local variable `filestats-all'
;; and `filestats'. Now, you can put something like
;; ;;; Local Variables:
;; ;;; filestats: ((:name "Chapters" :how-many "\n%%"))
;; ;;; End: 
;; at the end of a file to define statistics for this file only.
;; - New: filestats-auto-update-secs

;; 1.2.2
;; - New: Convert words before lookup in concordance via
;; filestats-concordance-convert-word -- e.g. capitalize words.
;; - New: highlighting of word index. This can take quite a while on
;; slow machine. (see concordance-highlight-p)
;; - New: filestats-concordance-match-list and
;; filestats-concordance-filter-list ... a function with one argument
;; or a list (mode filter) is a valid entry.

;; 1.2.1
;; - Change: More flexible concordance export
;; - New: filestats-quit-hooks

;; 1.2
;; - New command: filestats-concordance-export
;; - New: filestats-concordance-match-list,
;; filestats-concordance-filter-list ... control which words are
;; included in concordance
;; - New: The concordance now shows a word index. Clicking on the
;; index takes you to the word's position.
;; - New format for filestats-list, filestats-list-optional
;; - New: filestats-hyper-view-alist ... handle mouse clicks
;; - Change: In concordance, auto hide is switched off
;; - Change: filestats-list takes two optional arguments:
;; pre-count-hook and post-count-hook
;; - Change: filestats-list's third argument can be a pair of form
;; (mode . fun)

;; 1.1
;; - New command: filestats-concordance
;; - New variables: filestats-kill-on-manual-quit-p,
;; filestats-preserve-if-current-buffer-p, filestats-expert-p
;; filestats-kill-on-auto-quit-p, filestats-preserve-stat-list-p
;; - Change: viewer's arguments are: buffer unit result (not as a string)
;; - Change: don't delete the filestats buffer, if it's the current buffer
;; (controlled by filestats-preserve-if-current-buffer-p)
;; - Change: an entry for filestats-list-optional now may have the form
;; (mode title accumulate-p regexp), e.g. '(t "a and b" t "[ab]")
;; - Bug fix: don't select deleted buffer

;; 1.0
;; Initial version

;;; To do:

;; - Auto hide (delete-other-windows) results in an error, if minibuffer
;; is active

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'tellib)

; (require 'assoc)
(require 'info)
(require 'thingatpt)
(require 'timer)
; (require 'cus-edit)

;; Xemacs compatibility
(eval-and-compile
  (if tellib-running-xemacs
      (progn
	(require 'overlay)
	(defun textstats-current-window-width nil
	  (let ((max (- (window-width) 8))
		(min 20))
	    (if (> max min)
		max
	      min)))
	(defun textstats-event-set-char (event)
	  (pop-to-buffer (event-buffer event))
	  (set-buffer (event-buffer event))
	  (let ((pos (event-point event)))
	    (if pos
		(goto-char pos)))))
    (progn
      (defun textstats-current-window-width nil
	(let ((edges (window-edges)))
	  (- (nth 2 edges) (nth 0 edges) 3)))
      (defun textstats-event-set-char (event)
	(let ((posn (event-start event)))
	  (set-buffer (window-buffer (posn-window posn)))
	  (goto-char (posn-point posn)))))))


(defvar textstats-list
  '(("" "words" t (lambda () (if (forward-word 1) 1 0)))
    ("" "sentences" t (lambda () (forward-sentence 1) 1))
    ("" "paragraphs" t (lambda () (forward-paragraph 1) 1))
    ("" "whitespace" t (lambda () (if (forward-whitespace 1) 1 0))))
  "Some standard statistics.

There are two formats available. The old one takes a list with at
least 4 elements, the new one takes a keyed list, which looks pretty
much like elisp's plists. If a entry is in old or new format is
determined by its first element. If it is :name, it is the new format.

Add mode specific definitions to textstats-list-optional. The
statistics described in textstats-list should be of general use.


* New format: In new format an entry has the form '(key value key
value ...). See concordance.el for example usage.

Mandatory keys:
 :name ... This corresponds to 'title' in the explanation below.
 [:search|:search-regexp|:how-many|:fun|:fun1] ... You have to choose
one of these.
    :fun ... a function that takes no arguments
    :search-regexp, :how-many ... a regular expession
    :search ... a string

Optional keys:
 :accumulate ... default is t, except if :how-many is defined
 :mode ... default is t
 :initial-value ... the result's initial value -- usually 0
 :pre-hook
 :post-hook
 :view ... a function as described in textstats-view-functions-alist's
documentation
 :on-select ... a function as described in
textstats-hyper-view-alist's documentation

* Old Format: In old format entries must have the following form:
 (mode title accumulate fun/0 &optional pre-hook/1 post-hook/2).


* Entries:

mode ... Determines if a specific statistics should be produced for
this buffer. Possible values are: t (accept), the name of a mode, or a
function taking the buffer as an argument and returning t (accept) or
nil (don't accept). You may also use a list of names and functions.

title ... A String telling what to count

accumulate ... This can be nil, t, or a pair of (clean-p .
function/2).

- If 'accumulate' is 'nil', 'fun' generates the results straight away.

- If 'accumulate' is 't', the results are accumulated using (surprise,
surprise) additions.

- If 'accumulate' is a pair of the form (clean-p . acc-fun), clean-p
determines if acc-fun actually sets a variable called 'result',
 (clean-p is nil) or if it returns the the new result (clean-p is t).
As long as you don't run into limits imposed by Emacs, you should use
the second solution. The function takes two arguments: the already
accumulated results and the latest one.

fun ... This is a regular expression or a function, which takes no
arguments. If accumulate-p is nil, this function should simply return
the result. If accumulate-p is t, the function should return the
number added to the result. In most cases this will be 1. If the
return value is nil or the buffer limits are exceeded, the counting
process terminates.

pre-hook ... Optional argument: This should be a function that takes
one argument -- the buffer for which the statistics should be
computed. If you need any local variables to cache intermediate
results, using this function is the right way to create them.

post-hook ... Optional argument: This should be a function that takes
two arguments -- the buffer and the result computed by 'fun' -- and
returns the result. Use this function to calculate summarizing
statistics or to modify the buffer according to the result.")


(defvar textstats-list-optional
  '((("TeX" "Fundamental") "sections" t
     (lambda ()
       (textstats-search-forward-regexp
	"\\\\\\(chapter\\|subsubsection\\|subsection\\|section\\)")))
    ("Emacs-Lisp" "functions" t
     (lambda () (textstats-search-forward "\n(defun"))))
  "User defined mode specific statistics.

These definitions will be appended to textstats-list. See documentation
for `textstats-list'.")


(defvar textstats-list-sds
  `(("" "words" nil textstats-sds-count-words)
    ("" "character" nil textstats-sds-count-chars)
    ("" "lines" nil textstats-sds-count-lines))
  "Alternative standard statistics. See documentation for
`textstats-list'.")


(defvar textstats-hyper-view-alist nil
  "Defines what to do, if you select an textstats entry with the mouse.
Association list of the form '((unit . (lambda () [process mouse
click])) ...)

See `concordance-at-point' for example usage.")


(defvar textstats-view-functions-alist nil
  "Display statistics of a certain type. Additional viewers. A valid
entry is a pair of a unit qualifier and function, which takes 3
arguments: (unit . (lambda (buffer unit result) ...)

buffer ... The buffer where the result should be displayed

unit ... Title of what we display

result ... The result.")


(defvar textstats-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "u") 'textstats-update)
    (define-key map (kbd "t") 'textstats-toggle-auto-hide)
    (define-key map (kbd "O") 'textstats-customize-options)
    (define-key map (kbd "q") 'textstats-quit)
    (define-key map (kbd "h") 'describe-mode)
    (define-key map (kbd "SPC") 'textstats-switch-other-window)
    (define-key map (kbd "RET") 'textstats-stat-at-point)
    (if tellib-running-xemacs
	(define-key map [button1] 'textstats-stat-at-mouse)
      (define-key map (kbd "<mouse-1>") 'textstats-stat-at-mouse))
    map))


(defgroup textstats nil
  "Show Text Statistics."
  :prefix "textstats-"
  :group 'files)

(defcustom textstats-hooks nil
  "Hooks to run when `textstats' is being called."
  :type 'hook
  :group 'textstats)

(defcustom textstats-mode-hooks nil
  "Hooks to run upon entry into `textstats-mode'."
  :type 'hook
  :group 'textstats)

(defcustom textstats-quit-hooks nil
  "Hooks to run when `textstats-quit' is being called."
  :type 'hook
  :group 'textstats)

(defcustom textstats-auto-hide-secs
  (if tellib-running-xemacs 20 4) ;;; Xemacs: set this value to 0
  "Remove textstats windows after N seconds. This doesn't work alway
as expected. Set this value to 0 to switch this feature off. This
feature is turned off, if you make use of
`textstats-auto-update-secs'."
  :type 'integer
  :group 'textstats)

(defcustom textstats-auto-update-secs 0
  "Update textstats every N seconds. This turns off auto-hiding. Set
this value to 0 to switch this feature off. This option is incompatible
with `textstats-auto-hide-secs'."
  :type 'integer
  :group 'textstats)

(defcustom textstats-resize-window-p t
  "Non-nil means, shrink textstats window as necessary."
  :type 'boolean
  :group 'textstats)

(defcustom textstats-switch-window-p t
  "Non-nil means, switch back to text buffer after displaying the
statistics."
  :type 'boolean
  :group 'textstats)

(defcustom textstats-kill-on-manual-quit-p t
  "Non-nil means, on manual quit (by pressing 'q') don't just bury the
buffer, but remove/kill it."
  :type 'boolean
  :group 'textstats)

(defcustom textstats-preserve-if-current-buffer-p t
  "Non-nil means, don't delete textstats buffer, if it's the current
buffer. To be used in conjunction with `textstats-auto-hide-secs'."
  :type 'boolean
  :group 'textstats)

(defcustom textstats-kill-on-auto-quit-p nil
  "Non-nil means, on auto-quit don't just bury the buffer, but remove
it. To be used in conjunction with `textstats-auto-hide-secs'."
  :type 'boolean
  :group 'textstats)

(defcustom textstats-sds-fast-count-p nil
  "Non-nil means, use `textstats-list-sds', which is possibly faster,
instead of `textstats-list'."
  :type 'boolean
  :group 'textstats)

(defcustom textstats-header-face '(bold)
  "Face to be used for marking statistic headers (the units)."
  :type 'sexp
  :group 'textstats)

(defcustom textstats-expert-p nil
  "Non-nil means, suppress messages and warnings."
  :type 'boolean
  :group 'textstats)


(defvar textstats nil "Additional file local statistics.")
(defvar textstats-all nil "List of all file local statistics.")
(defvar textstats-auto-action-p t)
(defvar textstats-auto-hide-predicates nil
  "The list of predicates determining if the textstats are auto-hidden.
If one of them returns non-nil, the buffer is marked as auto-hide.")
(defvar textstats-buffer-timer nil)
(defvar textstats-counter nil)
(defvar textstats-newline-prefix "     ")
(defvar textstats-stat-list nil)
(defvar textstats-stat-list-names nil)
(defvar textstats-stat-prefix "* ")
(defvar textstats-target-buffer nil)
(defvar textstats-target-buffer-file-name nil)

(make-local-variable 'textstats)
(make-local-variable 'textstats-all)
(make-local-variable 'textstats-auto-action-p)
(make-local-variable 'textstats-auto-hide-predicates)
(make-local-variable 'textstats-buffer-timer)
(make-local-variable 'textstats-counter)
(make-local-variable 'textstats-stat-list)
(make-local-variable 'textstats-stat-list-names)
(make-local-variable 'textstats-target-buffer)
(make-local-variable 'textstats-target-buffer-q-name)


;;; these are adapted from Colin Walters' "ibuffer.el"
(defun textstats (&optional stat-list textstats-no-auto-action-flag)
  "Calculate text all statistics for current buffer. Use STAT-LIST
instead standard statistics. Disable auto hiding and the like by setting
TEXTSTATS-NO-AUTO-ACTION-FLAG to non-nil."
  (interactive)
  (let* ((target-buffer (current-buffer))
	 (target-buffer-file-name
	  (buffer-name target-buffer))
	 (target-buffer-name
	  (concat "*Textstats: " target-buffer-file-name "*"))
	 (fs-buffer nil))
    (pop-to-buffer (get-buffer-create target-buffer-name))
    (setq fs-buffer (current-buffer))
    (if (not (eq major-mode 'textstats-mode))
	(textstats-mode))
    (setq textstats-auto-action-p (not textstats-no-auto-action-flag))
    (setq textstats-target-buffer target-buffer)
    (setq textstats-target-buffer-file-name target-buffer-file-name)
    (textstats-reset-local-variables)
    (setq textstats-stat-list (textstats-get-textstats-list target-buffer
							    stat-list))
    (textstats-update fs-buffer)
    (run-hooks 'textstats-hooks)
    (set-buffer fs-buffer)
    (textstats-message "Commands: u to update, q to quit; h for help")
    (if textstats-switch-window-p
	(textstats-switch-other-window))))

(defun textstats-customize-options nil
  "Customize textstats' options."
  (interactive)
  (customize-group 'textstats))

(defun textstats-reset-local-variables nil
  (setq textstats-stat-list nil)
  (setq textstats-stat-list-names nil)
  (setq textstats-auto-action-p (textstats-auto--test-p)))

(defun textstats-switch-other-window ()
  "Switch from textstats buffer to original window."
  (interactive)
  (if (textstats-target-buffer-still-alive-p)
	 (switch-to-buffer-other-window textstats-target-buffer)))

(defmacro textstats-eval-in-buffer (buffer &rest form)
  "Evaluate FORM in BUFFER."
  `(save-excursion
     (save-restriction
       (set-buffer ,buffer)
       ,@form)))

(defmacro textstats-eval-in-target-buffer (&rest form)
  "Evaluate FORM in target buffer."
  `(condition-case nil
       (when (and (textstats-target-buffer-still-alive-p)
		  textstats-target-buffer)
;		 (save-excursion
;	      (save-restriction
	 (progn
	   (set-buffer textstats-target-buffer)
	   ,@form))
     (error nil)))

(defun textstats-target-buffer-still-alive-p (&optional auto-kill-p)
  "Return non-nil if target buffer is still alive."
  (if (eq major-mode 'textstats-mode)
      (if (buffer-name textstats-target-buffer)
	  t
	(when auto-kill-p
	  (textstats-do-the-quit t (current-buffer))))
    t))

(defun textstats-mode ()
  "Show some text statistics.

\\{textstats-mode-map}
"
;   (interactive)
  (kill-all-local-variables)
  (use-local-map textstats-mode-map)
  (setq major-mode 'textstats-mode)
  (setq mode-name "Textstats")
  (setq buffer-read-only nil)
  (buffer-disable-undo)
  (setq truncate-lines t)
  (use-hard-newlines -1 'never)
  (run-hooks 'textstats-mode-hooks))

(defun textstats-toggle-auto-hide nil
  "Toggle auto-hide for current textstats buffer."
  (interactive)
  (if (eq major-mode 'textstats-mode)
      (progn
	(setq textstats-auto-action-p (not textstats-auto-action-p))
	(message (concat "Textstats: auto-hide is "
			 (if textstats-auto-action-p
			     (progn
			       (textstats-reset-buffer-timer (current-buffer))
			       "on")
			   "off"))))))

(defun textstats-auto--test-p nil
  "Returns non-nil if the textstats should be automatically hidden."
  (and 
   (or (null textstats-auto-hide-predicates)
       (not (tellib-ormap #'funcall textstats-auto-hide-predicates)))
   (or (> textstats-auto-hide-secs 0)
       (> textstats-auto-update-secs 0))))

(defun textstats-auto-quit (buffer)
  "Conditionally hiding of textstats buffer."
  (if textstats-auto-action-p
      (if (> textstats-auto-update-secs 0)
	  (textstats-update buffer)
	(if (and textstats-preserve-if-current-buffer-p
		 (eq buffer (current-buffer)))
	    (textstats-reset-buffer-timer buffer)
	  (textstats-do-the-quit textstats-kill-on-auto-quit-p buffer)))))

(defun textstats-quit ()
  "Quit this `textstats' session."
  (interactive)
  (textstats-do-the-quit textstats-kill-on-manual-quit-p (current-buffer)))

(defun textstats-do-the-quit (kill-buffer-flag buffer)
  "Hide or kill BUFFER."
  (message nil)
  (if (eq major-mode 'textstats-mode)
      (progn
	(textstats-remove-buffer-timer buffer)
	(textstats-delete-extents)
	(run-hooks 'textstats-quit-hooks)
	(if kill-buffer-flag
	    (kill-buffer buffer)
	  (bury-buffer buffer))
	(if (> (count-windows) 1)
	    (delete-window)))
    (if (> (count-windows) 1)
	(delete-other-windows))))

(defun textstats-not-yet-implemented nil
  (message "Textstats: Not yet implemented.")
  nil)


;;; These are adapted from a file I received from Chris Beggy
;;; <chrisb AT kippona.com>. The original source code says: credit to
;;; sshteingold AT cctrading.com and ccurley AT trib.com
(defun textstats-sds-count-chars (&optional buffer) 
  (textstats-sds-counter (lambda (start end)
			   (- end start)) 
			 buffer))

(defun textstats-sds-count-lines (&optional buffer)
  (textstats-sds-counter (lambda (start end)
			   (count-lines start end)) 
			 buffer))

(defun textstats-sds-count-words (&optional buffer)
  (textstats-sds-counter (lambda (start end)
			   (goto-char start)
			   (string-to-number (how-many "\\<")))
			 buffer))

(defun textstats-sds-counter (fun &optional buffer)
  (let* ((result "")
	 (cb (current-buffer))
	 (this-buffer (or buffer cb)))
    (set-buffer this-buffer)
    (save-excursion
      (save-restriction
	(let ((start (point-min))
	      (end (point-max)))
	  (setq result (funcall fun start end)))))
    (set-buffer cb)
    result))


;;; A generalised count procedure originating in Bob Glickstein's
;;; "wcount.el"
(defun textstats-general-count (what accumulate this-entry buffer
				     &optional show-message-flag)
  "A generalised count procedure.

WHAT ... unit's name we are counting
ACCUMULATE ... a valid textstats-list 'accumulate' entry
THIS-ENTRY ... a valid textstats-list entry
BUFFER ... Which buffer to choose
SHOW-MESSAGE-FLAG ... show messages"
  (set-buffer buffer)
  (save-excursion
    (save-restriction
      (let* ((pre-hook (textstats-get-pre-hook this-entry))
	     (post-hook (textstats-get-post-hook this-entry))
	     (fun (textstats-get-fun this-entry))
	     (result (textstats-get-initial-value this-entry))
	     (acc-mode (cond
			((listp accumulate) (car accumulate))
			(t t)))
	     (acc-fun (cond
		       ((listp accumulate) (cdr accumulate))
		       (t '+)))
	     (acc (if acc-mode
		      (lambda (ra rn)
			(setq result (funcall acc-fun ra rn)))
		    acc-fun))
	     (message-prefix (concat "Counting " what " ... "))
	     (show-message
	      (lambda (&optional txt)
		(if show-message-flag
		    (textstats-message (concat message-prefix txt))))))
	(funcall show-message)
	(setq textstats-counter 1)
	(if pre-hook
	    (funcall pre-hook buffer))
	(while (not (eobp))
	  (let ((r (funcall fun)))
	    (if r
		(progn
		  (funcall acc result r)
		  (setq textstats-counter (1+ textstats-counter)))
	      (goto-char (point-max)))))
	(funcall show-message "done")
	(if post-hook
	    (funcall post-hook buffer result)
	  result)))))


;;; Access textstats-list
(defun textstats-new-format-p (this-entry)
  "Return non-nil if `textstats-list' is in new format?"
  (equal (car this-entry) ':name))

(defun textstats-value-defined (this-entry key)
  "textstats-list (new format): check if KEY is defined in THIS-ENTRY."
  (let ((rest (member key this-entry)))
    (if rest
	t
      nil)))

(defun textstats-value-retrieve (this-entry key &optional default)
  "textstats-list (new format): retrieve value for KEY in THIS-ENTRY.
Use DEFAULT value if KEY is undefined."
  (let ((rest (member key this-entry)))
    (if rest
	(cadr rest) 
      default)))

(defun textstats-value-get (this-entry key &optional default old-format-pos)
  "textstats-list: get value (for old and new format)
THIS-ENTRY ... textstats-list's entry
KEY ... key, if entry is in new format
OLD-FORMAT-POS ... position if entry is in old format"
  (cond ((textstats-new-format-p this-entry)
	 (textstats-value-retrieve this-entry key default))
	(old-format-pos
	 (nth old-format-pos this-entry))
	(t default)))

(defun textstats-get-mode (this-entry)
  "Access textstats-list (new format): mode."
  (textstats-value-get this-entry ':mode t 0))

(defun textstats-get-name (this-entry)
  "Access textstats-list (new format): name."
  (textstats-value-get this-entry ':name "" 1))

(defun textstats-get-accumulate (this-entry)
  "Access textstats-list (new format): accumulate."
  (cond ((textstats-value-defined this-entry ':how-many) nil)
	((textstats-value-defined this-entry ':search) t)
	((textstats-value-defined this-entry ':search-regexp) t)
	(t  (textstats-value-get this-entry ':accumulate t 2))))

(defun textstats-get-fun (this-entry)
  "Access textstats-list (new format): search, search-regexp,
how-many, fun."
  (cond
   ((textstats-value-defined this-entry ':search)
    (lambda ()
      (textstats-search-forward-regexp
       (textstats-value-get this-entry ':search))))
   ((textstats-value-defined this-entry ':search-regexp)
    (lambda ()
      (textstats-search-forward-regexp
       (textstats-value-get this-entry ':search-regexp))))
   ((textstats-value-defined this-entry ':how-many)
    (lambda ()
      (string-to-number
       (how-many
	(textstats-value-get this-entry ':how-many)))))
   (t (let ((fun (textstats-value-get this-entry ':fun nil 3)))
	(if (stringp fun)
	    (lambda ()
	      (textstats-search-forward-regexp fun))
	  fun)))))

(defun textstats-get-initial-value (this-entry)
  "Access textstats-list (new format): initial-value."
  (textstats-value-get this-entry ':initial-value 0))

(defun textstats-get-pre-hook (this-entry)
  "Access textstats-list (new format): pre-hook."
  (textstats-value-get this-entry ':pre-hook nil 4))

(defun textstats-get-post-hook (this-entry)
  "Access textstats-list (new format): post-hook."
  (textstats-value-get this-entry ':post-hook nil 5))

(defun textstats-get-view (unit &optional this-entry)
  "Access textstats-list (new format): view."
  (if (and this-entry (textstats-value-defined this-entry ':view))
      (textstats-value-get this-entry ':view)
    (cdr (assoc unit textstats-view-functions-alist))))

(defun textstats-get-on-select (&optional this-entry)
  "Access textstats-list (new format): on-select."
  (textstats-value-get this-entry ':on-select))


;;; Textstats buffer & viewing
(defun textstats-set-buffer-timer (buffer timer)
  (set-buffer buffer)
  (if (timerp textstats-buffer-timer)
      (cancel-timer textstats-buffer-timer))
  (setq textstats-buffer-timer timer))

(defun textstats-reset-buffer-timer (buffer)
  (textstats-set-buffer-timer 
   buffer 
   (textstats-create-buffer-timer buffer)))

(defun textstats-remove-buffer-timer (buffer)
  (textstats-set-buffer-timer buffer nil))

(defun textstats-create-buffer-timer (buffer)
  (run-at-time textstats-auto-hide-secs 
	       nil
	       'textstats-auto-quit
	       buffer))

(defun textstats-message (text)
  (if (not textstats-expert-p)
    (message text)))

(defun textstats-insert-this (text &optional face sep)
  "General display function."
  (cond
   ((null text) nil)
   ((listp text)
    (loop for this in text do
      (textstats-insert-this this face sep)))
   ((numberp text)
    (textstats-insert-this (number-to-string text) face sep))
   ((stringp text)
    (when (>= (+ (length text) (current-column))
	      (textstats-current-window-width))
      (newline)
      (insert textstats-newline-prefix))
    (let ((start (point)))
      (insert text)
      (when sep
	(insert sep))
      (when face
	(textstats-make-extent face start (+ start (length text))))))
   (t 
    (tellib-error 'error "textstats: General confusion: trying to insert" text))))

(defun filesets-prepare-fs-buffer (buffer)
    (set-buffer buffer)
    (setq buffer-read-only nil))

(defun textstats-insert-header (fs-buffer face unit)
  (add-to-list 'textstats-stat-list-names unit)
  (textstats-insert fs-buffer face textstats-stat-prefix))

(defun textstats-insert (buffer face text &optional sep)
  "Insert some statistics in textstats buffer."
  (let ((cb (current-buffer)))
    (filesets-prepare-fs-buffer buffer)
    (textstats-insert-this text face sep)
    (setq buffer-read-only t)
    (set-buffer cb)))

(defun textstats-insert-result (buffer unit value &optional unit-face value-face sep)
  "Insert a result."
  (textstats-insert buffer unit-face (textstats-format-unit unit))
  (textstats-insert buffer value-face (textstats-format-value value))
  (textstats-insert buffer nil "\n"))

(defun textstats-format-unit (unit)
  "Format a result's unit."
  (format "%-15s" (concat unit ":")))

(defun textstats-format-value (value)
  "Format a result's value."
  (let ((hd (if (and value (listp value))
		(car value)
	      value))
	(tl (if (and value
		     (listp value)
		     (cdr value))
		(concat " " (mapconcat (lambda (x) (format "%s" x)) (cdr value) " "))
	      "")))
  (format "%10s%s" hd tl)))
;;test: (textstats-format-value 1)
;;test: (textstats-format-value '(1))
;;test: (textstats-format-value '(1 2))
;(if (numberp value)
;    (number-to-string value)
;  value)))

(defun textstats-format-result (what result &optional tail)
  "Format a result."
  (concat
   (textstats-format-unit what)
   (textstats-format-value result)
   tail))

(defun textstats-stat-at-point ()
  "Handle mouse click in file-stats window."
  (interactive)
;  (if mark-active
;	 (deactivate-mark))
  (let* ((which-stat
	  (save-excursion
	    (if (search-backward (concat "\n" textstats-stat-prefix)
				 nil t)
		(progn
		  (forward-word 1)
		  (thing-at-point 'word))
	      nil)))
	 (which-handler
	  (if which-stat
	      (cdr (assoc which-stat textstats-hyper-view-alist))
	    nil)))
    (if which-handler
	(funcall which-handler)
;	 (textstats-message
;	  (format "No handler for %s in %s" which-stat (current-buffer)))
      )))

;; adapted from Alex Schroeder's <alex AT gnu.org> wiki.el
(defun textstats-stat-at-mouse (event)
  "Find string matching stat at the mouse position."
  (interactive "e")
;  (save-excursion
    (textstats-event-set-char event)
    (textstats-stat-at-point))
;  )

;; adapted from Alex Schroeder's <alex AT gnu.org> wiki.el
(defun textstats-make-extent (faces from to)
  "Make an extent for the range [FROM, TO] in the current buffer."
  (let* ((extent (funcall 'make-overlay from to))
	 (face (if (listp faces) (car faces) faces)))
    (funcall 'overlay-put extent 'face face)
    (if (and (listp faces) (member ':highlight faces))
	(funcall 'overlay-put extent 'mouse-face 'highlight))
    (funcall 'overlay-put extent 'evaporate t)
    (funcall 'overlay-put extent 'textstats t)))

;; adapted from Alex Schroeder's <alex AT gnu.org> wiki.el
(defun textstats-delete-extents (&optional start end)
  "Delete all extents/overlays created by `textstats-make-extent'.
If optional arguments START and END are given, only the overlays in that
region will be deleted."
  (let* ((start (or start (point-min)))
	 (end (or end (point-max)))
	 (extents (overlays-in start end)))
    (if extents
	(dolist (extent extents)
	  (when (apply 'overlay-get extent '(textstats))
	    (apply 'delete-overlay (list extent)))))))


;;; Utilities
(defun textstats-search-forward (find-string)
  (if (null (search-forward find-string nil t)) 
      nil 1))

(defun textstats-search-forward-regexp (find-string)
  (if (null (search-forward-regexp find-string nil t))
      nil 1))


;;; Core functions
(defun textstats-check-mode-p (mode this-buffer)
  "Check if THIS-BUFFER is in a proper MODE (see `textstats-list')."
;  (message "1: %S %S %S" this-buffer mode mode-name)(sleep-for 5)
  (cond
   ((null mode) nil)
   ((equal mode t) t)
   ((equal mode "") t)
   ((listp mode)
    (or (textstats-check-mode-p (car mode) this-buffer)
	(textstats-check-mode-p (cdr mode) this-buffer)))
   ((stringp mode)
    (save-excursion
;      (message "2: %S %S %S" this-buffer mode mode-name)(sleep-for 5)
      (set-buffer this-buffer)
      (equal mode mode-name)))
   ((functionp mode) (funcall mode this-buffer))
   (t nil)))

(defun textstats-result-get-unit (result) (nth 0 result))
(defun textstats-result-get-view (result) (nth 1 result))
(defun textstats-result-get-result (result) (nth 2 result))

(defun textstats-run-count (fsl this-buffer)
  "Run all statistics in FSL (a list of statistics definitions) for
THIS-BUFFER."
  (if (null fsl)
      nil
    (let* ((this-entry (car fsl))
	   (mode (textstats-get-mode this-entry)))
      (if (textstats-check-mode-p mode this-buffer)
	  (let* ((accumulate (textstats-get-accumulate this-entry))
		 (what (textstats-get-name this-entry))
		 (view (textstats-get-view what this-entry))
		 (on-mouse (textstats-get-on-select this-entry))
		 (this-result
		  (progn
		    (set-buffer this-buffer)
		    (goto-char (point-min))
		    (let ((r (if accumulate
				 (textstats-general-count
				  what accumulate this-entry this-buffer)
			       (funcall
				(textstats-get-fun this-entry)))))
		      r))))
	    (if on-mouse
		(add-to-list 'textstats-hyper-view-alist
			     `(,what . ,on-mouse)))
	    `((,what ,view ,this-result)
	      . ,(textstats-run-count (cdr fsl) this-buffer)))
	(textstats-run-count (cdr fsl) this-buffer)))))

(defun textstats-get-max-chars (this-buffer)
  (let ((result 0)
	(cb (current-buffer)))
    (set-buffer this-buffer)
    (save-excursion
      (save-restriction
	(setq result (- (point-max) (point-min)))))
;    (setq result (buffer-size))
    (set-buffer cb)
    result))

(defun textstats-get-textstats-list (target-buffer &optional stat-list)
  "Which statistics should we compute for TARGET-BUFFER. Return
STAT-LIST if non-nil."
  (if stat-list
      stat-list
    (save-excursion
      (set-buffer target-buffer)
      (if textstats-all
	  textstats-all
	(append (if textstats-sds-fast-count-p
		    textstats-list-sds
		  textstats-list)
		textstats-list-optional
		(if textstats
		    textstats
		  nil))))))

(defun textstats-update-get-result (fs-buffer target-buffer)
  (if target-buffer
      (textstats-eval-in-target-buffer
	(textstats-run-count
	 (textstats-eval-in-buffer fs-buffer textstats-stat-list)
	 target-buffer))
    nil))

(defun textstats-update-init-buffer (fs-buffer this-buffer-name)
  (set-buffer fs-buffer)
  (textstats-remove-buffer-timer fs-buffer)
  (setq buffer-read-only nil)
  (textstats-delete-extents)
  (erase-buffer)
  (textstats-insert fs-buffer '(bold)
		    (format "Text statistics: %s\n" this-buffer-name)))

(defun textstats-update-cleanup (fs-buffer)
  (set-buffer fs-buffer)
  (setq buffer-read-only t)
  (goto-char 1)
  (if (and textstats-auto-action-p (textstats-auto--test-p))
      (textstats-reset-buffer-timer fs-buffer))
  (if textstats-resize-window-p
      (shrink-window-if-larger-than-buffer
       (get-buffer-window fs-buffer))))

(defun textstats-update-view-characters (fs-buffer buffer result)
  (let* ((characters-total
	  (textstats-get-max-chars buffer))
	 (characters-readable (- characters-total result)))
    (set-buffer fs-buffer)
    (textstats-insert-result
     fs-buffer
     "characters"
     (list (number-to-string characters-total)
	   (concat "(" (number-to-string characters-readable)
		   " + " (number-to-string result) ")"))
     '(bold))))

(defun textstats-update (&optional buffer)
  "Update text statistics"
  (interactive)
  (save-excursion
    (save-restriction
      (let* ((fs-buffer (or buffer (current-buffer)))
	     (this-buffer (if (buffer-name textstats-target-buffer)
			      textstats-target-buffer
			    nil)))
	(if this-buffer
	    (let* ((this-buffer-name
		    (or textstats-target-buffer-file-name buffer-file-name))
		   (result-list (textstats-update-get-result 
				 fs-buffer this-buffer)))
	      (progn
		(textstats-update-init-buffer fs-buffer this-buffer-name)
		(dolist (this-result result-list)
		  (let* ((unit (textstats-result-get-unit this-result))
			 (view (textstats-result-get-view this-result))
			 (result (textstats-result-get-result this-result)))
		    (when result
		      (if view
			  (progn
			    (textstats-insert-header fs-buffer '(bold) unit)
			    (funcall view fs-buffer unit result))
			(if (and (numberp result) (> result 0))
			    (progn
			      (textstats-insert-header fs-buffer '(bold) unit)
			      (if (equal unit "whitespace")
				  (textstats-update-view-characters
				   fs-buffer this-buffer result)
				(textstats-insert-result fs-buffer
							 unit
							 result
							 '(bold)))))))))
		(textstats-update-cleanup fs-buffer)))
	  (textstats-do-the-quit t fs-buffer))))))

(provide 'textstats)

;;; TEXTSTATS.EL ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
