;;; outorg.el --- Org-style comment editing

;; Author: Thorsten Jolitz <tjolitz AT gmail DOT com>
;; Version: 2.0
;; URL: https://github.com/tj64/outorg

;;;; MetaData
;;   :PROPERTIES:
;;   :copyright: Thorsten Jolitz
;;   :copyright-years: 2013+
;;   :version:  2.0
;;   :licence:  GPL 2 or later (free software)
;;   :licence-url: http://www.gnu.org/licenses/
;;   :part-of-emacs: no
;;   :author: Thorsten Jolitz
;;   :author_email: tjolitz AT gmail DOT com
;;   :inspiration:  org-src
;;   :keywords: emacs org-mode comment-editing
;;   :git-repo: https://github.com/tj64/outorg
;;   :git-clone: git://github.com/tj64/outorg.git
;;   :END:

;;;; Commentary
;;;;; About outorg

;; Outorg is for editing comment-sections of source-code files in
;; temporary Org-mode buffers. It turns conventional
;; literate-programming upside-down in that the default mode is the
;; programming-mode, and special action has to be taken to switch to the
;; text-mode (i.e. Org-mode). 

;; Outorg depends on Outshine, i.e. outline-minor-mode with outshine
;; extensions activated. An outshine buffer is structured like an
;; org-mode buffer, only with outcommented headlines. While in
;; Org-mode text is text and source-code is 'hidden' inside of special
;; src-blocks, in an outshine buffer source-code is source-code and
;; text is 'hidden' as comments.

;; Thus org-mode and programming-mode are just two different views on
;; the outshine-style structured source-file, and outorg is the tool
;; to switch between these two views. When switching from a
;; programming-mode to org-mode, the comments are converted to text
;; and the source-code is put into src-blocks. When switching back
;; from org-mode to the programming-mode, the process is reversed -
;; the text is outcommented again and the src-blocks that enclose the
;; source-code are removed.

;; When the code is more important than the text, i.e. when the task
;; is rather 'literate PROGRAMMING' than 'LITERATE programming', it is
;; often more convenient to work in a programming-mode and switch to
;; org-mode once in a while than vice-versa. Outorg is really fast,
;; even big files with 10k lines are converted in a second or so, and
;; the user decides if he wants to convert just the current subtree
;; (done instantly) or the whole buffer. Since text needs no session
;; handling or variable passing or other special treatment, the outorg
;; approach is much simpler than the Org-Babel approach. However, the
;; full power of Org-Babel is available once the *outorg-edit-buffer*
;; has popped up.

;;;;; Usage

;; Outorg (like outshine) assumes that you set
;; `outline-minor-mode-prefix' in your init-file to 'M-#':

;; #+BEGIN_EXAMPLE 
;; ;; must be set before outline is loaded
;; (defvar outline-minor-mode-prefix "\M-#")
;; #+END_EXAMPLE

;; Outorg's main command is 

;; #+begin_example
;;   M-# # (or M-x outorg-edit-as-org)
;; #+end_example

;; to be used in source-code buffers where `outline-minor-mode' is
;; activated with `outshine' extensions. The Org-mode edit-buffer popped
;; up by this command is called *outorg-edit-buffer* and has
;; `outorg-edit-minor-mode' activated, a minor-mode with only 2 commands:

;; #+begin_example
;;   M-# (outorg-copy-edits-and-exit)
;;   C-x C-s (outorg-save-edits-to-tmp-file)
;; #+end_example

;; If you want to insert Org-mode source-code or example blocks in
;; comment-sections, i.e. you don't want outorg to remove the
;; enclosing blocks, simply outcomment them in the outorg-edit buffer
;; before calling `outorg-copy-edits-and-exit'.

;; Note that outorg only treats 'active' src-blocks in a special way -
;; the blocks whose Babel language is equal to the major-mode of the
;; associated programming-mode buffer. All other (src-) blocks are
;; treated like normal text.

;; Note further that outorg uses example-blocks as 'fallback' when it
;; cannot find the major-mode of the programming-mode buffer in the
;; `org-babel-load-languages'. In this case you should not use
;; example-blocks for other tasks, since they will be removed when
;; exiting the *outorg-edit-buffer*, use e.g. quote-blocks or
;; verse-blocks instead.

;;;;; Installation

;; You can get outorg.el either from Github (see section MetaData) or
;; via MELPA. It depends on outshine.el, so you have to install and
;; configure outshine first to make outorg work.

;; Installation is easy, simply insert

;; #+begin_example
;;  (require 'outorg)
;; #+end_example

;; in your init file. When you use navi-mode.el too, the third Outshine
;; library, it suffices to (require 'navi), since it requires the other
;; two libraries. 

;;;;; Bugs and Shortcomings

;; Outorg started out purely line-based, it only worked with
;; 'one-line' comments, i.e. with comment-sections like those produced
;; by `comment-region' (a command that comments or uncomments each
;; line in the region). It was enhanced later on to recognize comment
;; regions too, i.e. those special multi-line comments found in many
;; programming languages. But using outorg on such multi-line comments
;; will probably change their syntax back to 'single-line', whenever
;; `comment-region' uses this style.

;;;;; Tests

;; A special kind of test has been developed for outorg using the
;; `ert-buffer' library, the so called 'conversion test'. It has the
;; following steps:

;;  1. programming-mode -> org-mode

;;  2. edit in org-mode, store undo-information

;;  3. org-mode -> programming-mode

;;  4. programming-mode -> org-mode (again)

;;  5. undo edits

;;  6. org-mode -> programming-mode (again)

;; After these 4 conversions, the original programming-mode buffer
;; must be unchanged when the conversion process is perfect, i.e. does
;; not introduce any changes itself. See `outorg-test.el' for details.

;;;;; Emacs Version

;; Outorg works with GNU Emacs 24.2.1 or later. No attempts of testing
;; with older versions or other types of Emacs have been made (yet).

;;;; ChangeLog

;; | date            | author(s)       | version |
;; |-----------------+-----------------+---------|
;; | <2014-09-20 Sa> | Thorsten Jolitz |     2.0 |
;; | <2013-05-03 Fr> | Thorsten Jolitz |     1.0 |
;; | <2013-02-11 Mo> | Thorsten Jolitz |     0.9 |

;;; Requires

(require 'outline)
(require 'org)
(require 'org-watchdoc nil t)
;; (unless (require 'outorg-export nil t)
;;  (message
;;   "Try library `outorg-export' for automated export to all Org
;;	   backends:\n%s"
;;   "https://github.com/jleechpe/outorg-export"))

(declare-function R-mode "ess-r-d")
(declare-function org-watchdoc-propagate-changes "org-watchdoc")
(declare-function org-watchdoc-set-md5 "org-watchdoc")

;;; Mode and Exporter Definitions
;;;; Outorg Edit minor-mode

(define-minor-mode outorg-edit-minor-mode
   "Minor mode for Org-mode buffers generated by outorg.
There is a mode hook, and two commands:
\\[outorg-copy-edits-and-exit] outorg-copy-edits-and-exit
\\[outorg-save-edits-to-tmp-file] outorg-save-edits-to-tmp-file"
  :lighter " Outorg")

;;; Variables
;;;; Consts

(defconst outorg-version "2.0"
  "outorg version number.")

(defconst outorg-edit-buffer-name "*outorg-edit-buffer*"
  "Name of the temporary outorg edit buffer.")

;; FIXME org-babel names should be correct, but major-mode names need
;; to be cross-checked!
(defconst outorg-language-name-assocs
  '((abc-mode . abc)
    (asymptote-mode . asymptote)
    (awk-mode . awk)
    (c-mode . C)			;
    (c++-mode . cpp)			;
    (calc-mode . calc)			;
    (clojure-mode . clojure)
    (css-mode . css)
    (d-mode . D)			;
    (ditaa-mode . ditaa)
    (dot-mode . dot)
    (emacs-lisp-mode . emacs-lisp)	;
    (eukleides-mode . eukleides)
    (fomus-mode . fomus)
    (fortran-mode . F90)
    (gnuplot-mode . gnuplot)
    (groovy-mode . groovy)
    (haskell-mode . haskell)
    (j-mode . J)
    (java-mode . java)
    (javascript-mode . js)
    (julia-mode . julia)
    (latex-mode . latex)		;
    (ledger-mode . ledger)
    (lilypond-mode . ly)
    (lisp-mode . lisp)
    (make-mode . makefile)
    (mathomatic-mode . mathomatic)
    (matlab-mode . matlab)
    (maxima-mode . max)
    (mscgen-mode . mscgen)
    (tuareg-mode . ocaml)		;
    (octave-mode . octave)
    (org-mode . org)			;
    (oz-mode . oz)
    (perl-mode . perl)
    (picolisp-mode . picolisp)		;
    (plantuml-mode . plantuml)
    (python-mode . python)
    (ess-mode . R)			;
    (ruby-mode . ruby)
    (sass-mode . sass)
    (scala-mode . scala)
    (scheme-mode . scheme)
    (shen-mode . shen)
    (sh-mode . sh)			;
    (sql-mode . sql)
    (sqlite-mode . sqlite)
    (tcl-mode . tcl))
"Associations between major-mode-name and org-babel language
names.")

(defconst outorg-tracked-markers '(point-marker
beg-of-subtree-marker mark-marker)
 "Outorg markers to be tracked. The actual marker names are constructed by adding a prefix, either 'outorg-code-buffer-' or 'outorg-edit-buffer-'.")

(defconst outorg-tracked-org-markers '(org-clock-marker
  org-clock-hd-marker org-clock-default-task
  org-clock-interrupted-task selected-task org-open-link-marker
  org-log-note-marker org-log-note-return-to
  org-entry-property-inherited-from)
 "Org markers to be tracked by outorg.")

;;;; Vars

(defvar outline-minor-mode-prefix "\C-c"
  "New outline-minor-mode prefix.")

(defvar outorg-edit-whole-buffer-p nil
  "Non-nil if the whole code-buffer is edited.")

(defvar outorg-initial-window-config nil
  "Initial window-configuration when editing as Org.")

(defvar outorg-code-buffer-read-only-p nil
  "Remember if code-buffer was read only before editing")

;; copied and adapted from ob-core.el
(defvar outorg-temporary-directory)    ; FIXME why this duplication?
(unless (or noninteractive (boundp 'outorg-temporary-directory))
  (defvar outorg-temporary-directory
    (or (and (boundp 'outorg-temporary-directory)
	     (file-exists-p outorg-temporary-directory)
	     outorg-temporary-directory)
	(make-temp-file "outorg-" t))
    "Directory to hold outorg's temporary files.
This directory will be removed on Emacs shutdown."))

(defvar outorg-last-temp-file nil
  "Storage for absolute file name of last saved temp-file.")

(defvar outorg-called-via-outshine-use-outorg-p nil
  "Non-nil if outorg was called via `outshine-use-outorg' command")

(defvar outorg-oldschool-elisp-headers-p nil
  "Non-nil if an Emacs Lisp file uses oldschool headers ';;;+'")

(defvar outorg-insert-default-export-template-p nil
  "Non-nil means either the file specified in
`outorg-export-template-for-org-mode' or a file given by the user
will be inserted at the top of the *outorg-edit-buffer* when it
is opened, and will be removed when it is closed, thus enabling
the user to e.g. define default export options in a file and use
them on-demand in the *outorg-edit-buffer*. The value of this variable is
  toggled with command `outorg-toggle-export-template-insertion'.")
;; (make-variable-buffer-local 'outorg-insert-default-export-template-p)

(defvar outorg-ask-user-for-export-template-file-p nil
  "Non-nil means user is prompted for export-template-file.")
;; (make-variable-buffer-local 'outorg-ask-user-for-export-template-file-p)

(defvar outorg-keep-export-template-p nil
  "Non-nil means inserted export template is permanent.")
;; (make-variable-buffer-local 'outorg-keep-export-template-p)

(defvar outorg-export-template-regexp
  (concat
   "[[:space:]\n]*"
   "# <<<\\*\\*\\* BEGIN EXPORT TEMPLATE [[:ascii:]]+"
   "# <<<\\*\\*\\* END EXPORT TEMPLATE \\*\\*\\*>>>[^*]*")
  "Regexp used to identify (and delete) export templates.")

(defvar outorg-propagate-changes-p nil
  "Non-nil means propagate changes to associated doc files.")
;; (make-variable-buffer-local 'outorg-propagate-changes-p)

(defvar outorg-code-buffer-point-marker (make-marker)
 "Marker to store position in code-buffer.")

(defvar outorg-edit-buffer-point-marker (make-marker)
 "Marker to store position in edit-buffer.")

(defvar outorg-code-buffer-beg-of-subtree-marker (make-marker)
  "Marker to store begin of current subtree in
  code-buffer.")

(defvar outorg-edit-buffer-beg-of-subtree-marker (make-marker)
  "Marker to store begin of current subtree in
  edit-buffer.")

(defvar outorg-markers-to-move nil
  "Markers that should be moved with a cut-and-paste operation.
Those markers are stored together with their positions relative to
the start of the region.")

(defvar outorg-org-finish-function-called-p nil
  "Non-nil if `org-finish-function' was called, nil otherwise.")

(defvar outorg-pt-A-marker (make-marker)
 "Outorg marker for tracking begin of comment.
If pt-A < pt-B, the region between A and B is out- or
uncommented.")

(defvar outorg-pt-B-marker (make-marker)
 "Outorg marker for tracking beginning of source-code.
If pt-B < pt-C, the region between B and C is wrapped/unwrapped
as source-block.")

(defvar outorg-pt-C-marker (make-marker)
 "Outorg marker for tracking end of source-code.
If pt-B < pt-C, the region between B and C is wrapped/unwrapped
as source-block.")

;; ;; pt-A
;; (defvar outorg-beg-comment-marker (make-marker)
;;  "Outorg marker for tracking begin of comment.")

;; ;; pt-B
;; (defvar outorg-beg-src-marker (make-marker)
;;  "Outorg marker for tracking beginning of source-code.")

;; ;; pt-C
;; (defvar outorg-end-src-marker (make-marker)
;;  "Outorg marker for tracking end of source-code.")


;;;; Hooks

(defvar outorg-hook nil
  "Functions to run after `outorg' is loaded.")

(defvar outorg-edit-minor-mode-hook nil
  "Hook run after `outorg' switched a source code file or subtree to
  Org-mode.")

;;;; Customs

;;;;; Custom Groups

(defgroup outorg nil
  "Library for outline navigation and Org-mode editing in Lisp buffers."
  :prefix "outorg-"
  :group 'lisp
  :link '(url-link
          "http://orgmode.org/worg/org-tutorials/org-outside-org.html"))

;;;;; Custom Vars

;; inspired by 'org-src.el'
(defcustom outorg-edit-buffer-persistent-message t
  "Non-nil means show persistent exit help message while in edit-buffer.
The message is shown in the header-line, which will be created in the
first line of the window showing the editing buffer."
  :group 'outorg
  :type 'boolean)

(defcustom outorg-unindent-active-source-blocks-p t
  "Non-nil means common indentation (e.g. 2 spaces) in the active
source-blocks of the *outorg-edit-buffer* (i.e. those in the
language of the associated source-code buffer, and only in those)
is removed before converting back from Org to source-code."
  :group 'outorg
  :type 'boolean)

;;; Functions
;;;; Non-interactive Functions
;;;;; Get Buffer Mode and Language Name

(defun outorg-comment-on-line ()
  "Look forward from point for a comment at the start of this
  line. If found, move point to the beginning of the text after
  `comment-start' syntax, and return the location of the
  beginning of the line. If the line does not start with
  `comment-start', returns `nil'."
  (and (search-forward-regexp (concat "\\("
                                      (regexp-quote comment-start)
                                      "[[:space:]]*\\)")
                              (line-end-position)
                              1)
       (eq (match-beginning 0) (point-at-bol))
       (point-at-bol)))

(defun outorg-comment-on-line-p ()
  "Determine if point is on a line that begins with a comment."
  (save-excursion
    (beginning-of-line)
    (outorg-comment-on-line)))

(defun outorg-comment-search-forward ()
  "Like `comment-search-forward', but looks only for comments
beginning with `comment-start' syntax at the start of a
line. Point is left at the beginning of the text after the line
comment syntax, while the returned point is at the beginning of
the line."
  (while (not (or (eobp) (outorg-comment-on-line))) (forward-line))
  (point-at-bol))
 
;; copied from http://www.emacswiki.org/emacs/basic-edit-toolkit.el
(defun outorg-region-or-buffer-limits ()
  "Return the start and end of the region as a list, smallest first.
If the region is not active or empty, then bob and eob are used."
  (if (or
       (not mark-active)
       (null (mark))
       (= (point) (mark)))
      (list (point-min) (point-max))
    (if (< (point) (mark))
	(list (point) (mark))
      (list (mark) (point)))))

(defun outorg-get-buffer-mode (&optional buf-or-strg as-strg-p)
  "Return major-mode of BUF-OR-STRG or current-buffer.

If AS-STRG-P is non-nil, a string is returned instead instead
of a symbol."
  (let ((buf (if buf-or-strg
		 (get-buffer buf-or-strg)
	       (current-buffer))))
    (with-current-buffer buf
	(if as-strg-p (symbol-name major-mode) major-mode))))

(defun outorg-get-babel-name (&optional mode-name as-strg-p)
  "Return the symbol associated in Org-Babel with MODE-NAME.

Uses `outorg-language-name-assocs' as association list between
the string returned by `major-mode' in the associated source-code
buffer and the symbol used for that language in
`org-babel-load-languages'. If AS-STRG-P is non-nil, a string
is returned."
  (let* ((mmode (or
		 (and mode-name
		      (cond
		       ((stringp mode-name) (intern mode-name))
		       ((symbolp mode-name) mode-name)
		       (t (error
			   "Mode-Name neither String nor Symbol"))))
		 major-mode))
	(bname (cdr (assoc mmode outorg-language-name-assocs))))
    (if as-strg-p (symbol-name bname) bname)))

(defun outorg-get-mode-name (babel-name &optional as-strg-p)
  "Return the major-mode name associated with BABEL-NAME.

Uses `outorg-language-name-assocs' as association list between
the symbol returned by `major-mode' in the associated source-code
buffer and the symbol used for that language in
`org-babel-load-languages'. If AS-STRG-P is non-nil, a string
is returned."
  (let* ((bname
	  (cond
	   ((stringp babel-name) (intern babel-name))
	   ((symbolp babel-name) babel-name)
	   (t (error "Babel-Name neither String nor Symbol"))))
	(mmode
	 (car
	  (rassoc bname outorg-language-name-assocs))))
    (if as-strg-p (symbol-name mmode) mmode)))
  
(defun outorg-get-language-name (&optional mode-name as-sym-p)
  "Extract car of splitted and normalized MODE-NAME.

If AS-SYM-P is non-nil, a symbol instead of a string is
returned."
  (let* ((mmode (or
		 (and mode-name
		      (cond
		       ((stringp mode-name) mode-name)
		       ((symbolp mode-name) (symbol-name mode-name))
		       (t (error
			   "Mode-Name neither String nor Symbol"))))
		 (symbol-name major-mode)))
         (splitted-mmode
          (split-string mmode "-mode"))
         (language-name
          (if (> (length splitted-mmode) 1)
              (car splitted-mmode)
            (car (split-string mmode "\\.")))))
    (if as-sym-p (intern language-name) language-name)))

(defun outorg-in-babel-load-languages-p (&optional mode-name)
  "Non-nil if MODE-NAME is in Org-Babel load languages.

If MODE-NAME is nil, check if Org-Babel identifier of major-mode of current buffer is in Org-Babel load languages."
  (let* ((mmode (or
		 (and mode-name
		      (cond
		       ((stringp mode-name) (intern mode-name))
		       ((symbolp mode-name) mode-name)
		       (t (error
			   "Mode-Name neither String nor Symbol"))))
		 major-mode)))
    (assoc
     ;; Note that babel's cpp (for C++) is packaged in ob-C with the C
     ;; language
     (let ((bname (outorg-get-babel-name mmode)))
       (if (eq bname (intern "cpp")) (intern "C") bname))
     org-babel-load-languages)))


;;;;; Configure Edit Buffer

;; copied and adapted from org-src.el
(defun outorg-edit-configure-buffer ()
  "Configure edit buffer"
  (let ((msg
         (concat "[ "
                 (buffer-name
                  (marker-buffer outorg-code-buffer-point-marker))
                 " ] "
                 "Exit with M-# (Meta-Key and #)")))

    ;; Only run the kill-buffer-hooks when the outorg edit buffer is
    ;; being killed. This is because temporary buffers may be created
    ;; by various org commands, and when those buffers are killed, we
    ;; do not want the outorg kill hooks to run.
    (org-add-hook 'kill-buffer-hook
                  (lambda ()
                    (when (string= (buffer-name) outorg-edit-buffer-name)
                      (outorg-save-edits-to-tmp-file)))
                  nil 'local)
    
    (org-add-hook 'kill-buffer-hook
                  (lambda ()
                    (when (string= (buffer-name) outorg-edit-buffer-name)
                      (outorg-reset-global-vars)) nil 'local))

    
    ;; (setq buffer-offer-save t)
    (and outorg-edit-buffer-persistent-message
         (org-set-local 'header-line-format msg))
    ;; (setq buffer-file-name
    ;;       (concat (buffer-file-name
    ;; (marker-buffer outorg-code-buffer-point-marker))
    ;;               "[" (buffer-name) "]"))
    (if (featurep 'xemacs)
        (progn
          (make-variable-buffer-local
           'write-contents-hooks) ; needed only for 21.4
          (setq write-contents-hooks
                '(outorg-save-edits-to-tmp-file)))
      (setq write-contents-functions
            '(outorg-save-edits-to-tmp-file)))
    ;; (setq buffer-read-only t) ; why?
    ))


;; (org-add-hook 'outorg-edit-minor-mode-hook 'outorg-edit-minor-mode)
(org-add-hook 'outorg-edit-minor-mode-hook
              'outorg-edit-configure-buffer)

;;;;; Backup Edit Buffer

;; copied and adapted from ob-core.el
(defun outorg-temp-file (prefix &optional suffix)
  "Create a temporary file in the `outorg-temporary-directory'.
Passes PREFIX and SUFFIX directly to `make-temp-file' with the
value of `temporary-file-directory' temporarily set to the value
of `outorg-temporary-directory'."
  (let ((temporary-file-directory
	 (if (file-remote-p default-directory)
	     (concat (file-remote-p default-directory) "/tmp")
	   (or (and (boundp 'outorg-temporary-directory)
		    (file-exists-p outorg-temporary-directory)
		    outorg-temporary-directory)
	       temporary-file-directory))))
      (make-temp-file prefix nil suffix)))

(defun outorg-save-edits-to-tmp-file ()
  "Save edit-buffer in temporary file"
  (interactive)
  (let* ((code-file (file-name-sans-extension
                     (file-name-nondirectory
                      (buffer-name
                       (marker-buffer
                        outorg-code-buffer-point-marker)))))
         (tmp-file (outorg-temp-file code-file))
         (tmp-dir (file-name-directory tmp-file)))
    (setq outorg-last-temp-file tmp-file)
    (setq buffer-file-name (concat tmp-dir "outorg-edit-" code-file))
    (write-region nil nil tmp-file nil 'VISIT)))

;; copied and adapted from ob-core.el
(defun outorg-remove-temporary-directory ()
  "Remove `outorg-temporary-directory' on Emacs shutdown."
  (when (and (boundp 'outorg-temporary-directory)
	     (file-exists-p outorg-temporary-directory))
    ;; taken from `delete-directory' in files.el
    (condition-case nil
	(progn
	  (mapc (lambda (file)
		  ;; This test is equivalent to
		  ;; (and (file-directory-p fn) (not (file-symlink-p fn)))
		  ;; but more efficient
		  (if (eq t (car (file-attributes file)))
		      (delete-directory file)
		    (delete-file file)))
		;; We do not want to delete "." and "..".
		(directory-files outorg-temporary-directory 'full
				 "^\\([^.]\\|\\.\\([^.]\\|\\..\\)\\).*"))
	  (delete-directory outorg-temporary-directory))
      (error
       (message "Failed to remove temporary outorg directory %s"
		(if (boundp 'outorg-temporary-directory)
		    outorg-temporary-directory
		  "[directory not defined]"))))))

(add-hook 'kill-emacs-hook 'outorg-remove-temporary-directory)

;;;;; Reset Global Vars

;; TODO better use buffer-local variables instead?
(defun outorg-reset-global-vars ()
  "Reset some global vars defined by outorg to initial values."
  (ignore-errors
    (set-marker outorg-code-buffer-point-marker nil)
    (set-marker outorg-code-buffer-beg-of-subtree-marker nil)
    (set-marker outorg-edit-buffer-point-marker nil)
    (set-marker outorg-edit-buffer-beg-of-subtree-marker nil)
    (setq outorg-edit-whole-buffer-p nil)
    (setq outorg-initial-window-config nil)
    (setq outorg-code-buffer-read-only-p nil)
    (setq outorg-oldschool-elisp-headers-p nil)
    (setq outorg-insert-default-export-template-p nil)
    (setq outorg-ask-user-for-export-template-file-p nil)
    (setq outorg-keep-export-template-p nil)
    (setq outorg-propagate-changes-p nil)
    (setq outorg-called-via-outshine-use-outorg-p nil)
    (when outorg-markers-to-move
      (mapc (lambda (m)
	      (when (markerp m)
		(move-marker m nil)))
	    outorg-markers-to-move)
      (setq outorg-markers-to-move nil))
    (setq outorg-org-finish-function-called-p nil)))

;;;;; Remove Trailing Blank Lines

;; inspired by `article-remove-trailing-blank-lines' in `gnus-art.el'
(defun outorg-remove-trailing-blank-lines ()
  "Remove all trailing blank lines from buffer.
Finally add one newline."
  (save-excursion
    (let ((inhibit-read-only t))
      (goto-char (point-max))
      (delete-region
       (point)
       (progn
	 (while (and (not (bobp))
		     (looking-at "^[ \t]*$"))
	   (forward-line -1))
	 (forward-line 1)
	 (point))))))

;;;;; Save and Restore Markers

;;  1. Deal with position markers in code and edit buffer, to get the
;;     least possible surprise about point position after switching
;;     buffers

;;  2. Deal with org markers set in the edit buffer and needed in
;;     after command hooks when edit buffer is already closed

(defun outorg-save-markers (marker-lst)
  "Save markers from MARKER-LST in `outorg-markers-to-move'."
  (save-restriction
    (widen)
    (let* ((beg (if (or outorg-edit-whole-buffer-p
			(equal (buffer-name)
			       outorg-edit-buffer-name))
		    (point-min)
		  (if (outline-on-heading-p)
		      (point)
		    (save-excursion
		      (outline-previous-heading)
		      (point)))))
	   (end (if (or outorg-edit-whole-buffer-p
			(equal (buffer-name)
			       outorg-edit-buffer-name))
		    (point-max)
		  (save-excursion
		    (outline-end-of-subtree)
		    (point))))
	   (prefix (cond
		    ((eq (current-buffer)
			 (marker-buffer
			  outorg-code-buffer-point-marker))
		     "outorg-code-buffer-")
		    ((eq (current-buffer)
			 (marker-buffer
			  outorg-edit-buffer-point-marker))
		     "outorg-edit-buffer-")
		    (t (error "This should not happen"))))
	   (markers (mapcar
		     (lambda (--marker)
		       (intern
			(format
			 "%s%s"
			 (if (string-match
			      "\\(org\\|mark\\)"
			      (car (split-string
				    (symbol-name --marker)
				    "-" t)))
			     ""
			   prefix)
			 --marker)))
		     marker-lst)))
      (mapc
       (lambda (--marker)
	 (outorg-check-and-save-marker --marker beg end))
       markers))))

;; adapted from org.el
(defun outorg-check-and-save-marker (marker-or-var beg end)
  "Check if MARKER-OR-VAR is between BEG and END.
If yes, remember the marker and the distance to BEG."
  (let ((marker (cond
		 ((markerp marker-or-var) marker-or-var)
		 ((boundp marker-or-var) (eval marker-or-var))
		 (t nil))))
    (when (and (markerp marker)
	       (marker-buffer marker)
	       (equal (marker-buffer marker) (current-buffer)))
      (when (and (>= marker beg) (< marker end))
	(let* ((splitted-marker-name
		(split-string
		 (symbol-name marker-or-var)
		 "\\(outorg-\\|-buffer-\\)" t))
	       (split-gt-1-p (> (length splitted-marker-name) 1))
	       (marker-buf
		(ignore-errors
		  (when split-gt-1-p
		    (intern (car splitted-marker-name)))))
	       (marker-typ
		(ignore-errors
		  (if split-gt-1-p
		      (intern (cadr splitted-marker-name))
		    (intern (car splitted-marker-name))))))
	  (push (list marker-buf marker-typ (- marker beg))
		outorg-markers-to-move))))))

(defun outorg-reinstall-markers-in-region (beg)
  "Move all remembered markers to their position relative to BEG."
  (mapc (lambda (--marker-lst)
          (move-marker
	   (eval
	    (intern
	     (format "%s%s"
		     (cond
		      ((eq (car --marker-lst) 'code)
		       "outorg-edit-buffer-")
		      ((eq (car --marker-lst) 'edit)
		       "outorg-code-buffer-")
		      ((and (booleanp (car --marker-lst))
			    (null (car --marker-lst)))
		       "")
		      (t (error "This should not happen.")))
		     (cadr --marker-lst))))
	   (+ beg (caddr --marker-lst))))
        outorg-markers-to-move)
  (setq outorg-markers-to-move nil))

;;;;; Copy and Convert

(defun outorg-convert-org-to-outshine
  (&optional mode infile outfile BATCH)
  "Convert an existing Org-mode file into an Outshine buffer.

If MODE is non-nil, the Outshine buffer will be put in this
major-mode, otherwise the major-mode of the language of the first
source-code block in the Org-mode buffer will be used.

If INFILE is non-nil, the specified Org-mode file will be
visited, otherwise the current buffer will be used (i.e. the
buffer content will be copied to a temporary *outorg-edit-buffer*
for further processing).

If OUTFILE is non-nil, the converted Outshine buffer will be
saved in this file. Its the user's responsability to make sure
that OUTFILE's file-extension is suited for the major-mode of the
Outshine buffer to be saved. When in doubt, consult variable
`auto-mode-alist' for associations between file-extensions and
major-modes.

If BATCH is non-nil (and OUTFILE is non-nil, otherwise it makes
no sense), the new Outshine file is saved and its buffer
deleted."
  (let* ((org-buffer (if infile
                         (if (and (file-exists-p infile)
                                  (string-equal
                                   (file-name-extension infile) "org"))
                             (find-file (expand-file-name infile))
                           (error
                            "Infile doesn't exist or is not an Org file"))
                       (current-buffer)))
         (maj-mode (or mode
                       (with-current-buffer org-buffer
                         (save-excursion
                           (goto-char (point-min))
                           (or
                            ;; major-mode of first src-block
                            (ignore-errors
                              (org-next-block
                               nil nil org-babel-src-block-regexp)
                              (format
                               "%s-mode"
                               (car (org-babel-get-src-block-info 'LIGHT))))
                            ;; default case emacs-lisp-mode
                            "emacs-lisp-mode"))))))
    (with-current-buffer (get-buffer-create
                          (generate-new-buffer-name "tmp"))
      (setq outorg-code-buffer-point-marker (point-marker))
      (funcall (intern maj-mode))
      (and outfile
           ;; ;; FIXME does not really avoid confirmation prompts
           ;; (add-to-list 'revert-without-query (expand-file-name outfile))
           (if BATCH
               (write-file (expand-file-name outfile))
             (write-file (expand-file-name outfile) 'CONFIRM))))
    (setq outorg-edit-whole-buffer-p t)
    (setq outorg-initial-window-config
          (current-window-configuration))
    (with-current-buffer (get-buffer-create outorg-edit-buffer-name)
      (erase-buffer)
      (insert-buffer-substring org-buffer)
      (org-mode)
      (outorg-transform-active-source-block-headers)
      (outorg-copy-edits-and-exit))
    ;; ;; FIXME ugly hack
    ;; (funcall major-mode)
    ;; (funcall major-mode)
    ;; (fontify-keywords)
    (when outfile
      (save-buffer)
      ;; (revert-buffer t t)
      ;; (remove
      ;;  (expand-file-name outfile)
      ;;  revert-without-query)
      (and BATCH (kill-buffer)))))

(defun outorg-transform-active-source-block-headers ()
  "Move switches and arguments on top of block.

This functions transforms all active source-blocks, i.e. those
with the associated source-code buffer's major-mode as
language. If there are switches and header arguments after the
language specification on the #+BEGIN_SRC line, they are moved on
top of the block.

The idea behind this function is that it should be possible to
specify permanent switches and arguments even for source-code
blocks that are transformed back to code after
`outorg-copy-and-switch' is called. They will remain as comment
lines directly over their code section in the source-code buffer,
and thus be transformed to text - and thereby activated -
everytime `outorg-edit-as-org' is called."
  (save-excursion
    (let* ((mode (outorg-get-buffer-mode
		  (marker-buffer outorg-code-buffer-point-marker)))
	   (active-lang
	    (outorg-get-babel-name mode 'as-strg-p)))
      (org-babel-map-src-blocks nil
	(when (string-equal active-lang lang)
	  (let ((sw switches)
		(args header-args))
	    (goto-char end-lang)
	    (delete-region (point) (line-end-position))
	    (goto-char beg-block)
	    (forward-line -1)
	    (when (org-string-nw-p sw)
	      (newline)
	      (insert (format "#+header: %s" sw)))
	    (when (org-string-nw-p args)
	      (let ((params
		     (ignore-errors
		       (org-split-string args)))
		    headers)
		(while params
		  (setq headers
			(cons
			 (format "#+header: %s %s"
				 (org-no-properties (pop params))
				 (org-no-properties (pop params)))
			 headers)))
		(newline)
		(insert (mapconcat 'identity headers "\n"))))))))))
	      ;; (insert (format "#+header: %s" args)))))))))

;; Thx to Eric Abrahamsen for the tip about `mail-header-separator'
(defun outorg-prepare-message-mode-buffer-for-editing ()
  "Prepare an unsent-mail in a message-mode buffer for outorg.

This function assumes that '--text follows this line--' (or
whatever is found inside variable `mail-header-separator') is the
first line below the message header, is always present, and never
modified by the user. It turns this line into an `outshine'
headline and out-comments all text below this line - if any."
    (goto-char (point-min))
    ;; (re-search-forward "--text follows this line--" nil 'NOERROR)
    (re-search-forward mail-header-separator nil 'NOERROR)
   (let ((inhibit-read-only t))
     (replace-match "* \\&"))
    ;; (replace-match "* \\&")
    (beginning-of-line)
    (let ((start-body (point)))
      (comment-region start-body (point-max))
      (narrow-to-region start-body (point-max))
      (forward-line)))

(defun outorg-prepare-message-mode-buffer-for-sending ()
  "Prepare an unsent-mail edited via `outorg-edit' for sending.

This function assumes that '* --text follows this line--' is the
first line below the message header and is, like all lines below
it, out-commented with `comment-region'. It deletes the leading
star and uncomments the line and all text below it - if any."
  (save-excursion
    (goto-char (point-min))
    (re-search-forward
     (concat
      "\\(" (regexp-quote "* ") "\\)"
      "--text follows this line--")
     nil 'NOERROR)
    (replace-match "" nil nil nil 1)
    (beginning-of-line)
    (let ((start-body (point)))
      (uncomment-region start-body (point-max))
      (widen))))

(defun outorg-prepare-iorg-edit-buffer-for-editing ()
  "Prepare a buffer opened with `edit' from iorg-scrape for outorg.

This function assumes that a PicoLisp symbol that contains the
text of an Org-mode file (fetched from an iOrg application) has
been loaded into a PicoLisp `edit' buffer. It transforms the
buffer content to a `outshine' compatible format, such that
`outorg-edit-as-org' can be applied on it.

In particular, this function assumes that the original `edit'
buffer has the following format

;; #+begin_quote
txt \"<content-org-file>\"

\(********\)
;; #+end_quote

and that the text must be transformed to a format that looks
somehow like this

;; #+begin_quote
## #+DESCRIPTION txt

\[## #+<OPTIONAL-EXPORT-HEADERS>\]

## * Org-file
## Content

\(********\)
;; #+end_quote

i.e. the symbol-name 'txt' is converted to a #+DESCRIPTION keyword
and is followed by the (expanded and unquoted) content of the Org
file. This whole section of the buffer is outcommented with
picolisp-mode comment syntax. Finally, at the end of the buffer
the '\(********\)' line is left as-is."
  (goto-char (point-min))
  (insert "#+DESCRIPTION: ")
  (re-search-forward "\\(\"\\|NIL\\)" nil 'NOERROR)
  (if (string-equal (match-string-no-properties 0) "NIL")
      (progn
        (backward-word)
        (newline 2)
        (looking-at "NIL")
        (replace-match "* <Header>" 'FIXEDCASE 'LITERAL))
    (replace-match "")
    (newline 2))
  (goto-char (point-max))
  (re-search-backward "[^*)(\n\t\s]" nil 'NOERROR)
  (if (string-equal (match-string-no-properties 0) "\"")
    (replace-match "")
    (forward-char))
  (newline)
  (let ((end-body (point))
        (start-body (point-min)))
    (save-excursion
      (goto-char start-body)
      (while (search-forward "^J" end-body t)
	(replace-match "\n" nil t)))
    ;; (replace-string "^J" "\n" nil start-body end-body)
    (goto-char (point-min))
    (re-search-forward
     (concat "(" (regexp-quote "********") ")") nil 'NOERROR)
    (forward-line -1)
    (setq end-body (point))
    (comment-region start-body end-body)))

(defun outorg-prepare-iorg-edit-buffer-for-posting ()
  "Prepare an `edit' buffer for posting via iorg-scrape.

This function assumes that a PicoLisp symbol that contains the
text of an Org-mode file (fetched from an iOrg application) has
been edited with outorg and converted back to PicoLisp. It
transforms the `edit' buffer content back to its original format,
such that it can be posted back to the PicoLisp system by closing
the emacsclient (via the protocol defined in `eedit.l').

In particular, this function assumes that the original `edit'
buffer had the following format

;; #+begin_quote
txt \"<content-org-file>\"

\(********\)
;; #+end_quote

and that the actual text that has to be transformed back to this
format looks somehow like this

;; #+begin_quote
## #+DESCRIPTION txt

\[## #+<OPTIONAL-EXPORT-HEADERS>\]

## * Org-file
## Content

\(********\)
;; #+end_quote

i.e. the symbol-name 'txt' has been converted to a #+DESCRIPTION
keyword and is followed by the (expanded and unquoted) content of
the Org file. This whole section of the buffer is outcommented
with picolisp-mode comment syntax. Finally, at the end of the
buffer the '\(********\)' line is found again."
  (let ((final-line
         (concat "(" (regexp-quote "********") ")")))
  (uncomment-region (point-min) (point-max))
  (goto-char (point-min))
  (re-search-forward (regexp-quote "#+DESCRIPTION: ") nil 'NOERROR)
  (replace-match "")
  (end-of-line)
  (let ((show-trailing-whitespace nil))
    (kill-line 2))
  (insert "\"")
  (re-search-forward final-line  nil 'NOERROR)   
  (beginning-of-line)
  (re-search-backward "[[:alnum:][:punct:]]" nil 'NOERROR)
  (forward-char)
  (insert "\"")
  (kill-line)
  (save-excursion
    (let ((pt (point)))
      (goto-char (point-min))
      (while (search-forward "^J" pt t)
	(replace-match "\n" nil t))))
  ;; (replace-string "\n" "^J" nil (point-min) (point))
  (goto-char (point-min))
  (when (looking-at
         (concat "\\(^.*\\)"
                 "\\(\"\\* <Header>\"\\)"
                 "\\([\s\t\n]+" final-line "\\)"))
      (replace-match (format "%s" "NIL") nil nil nil 2)
      ;; (kill-line)
      )))

(defun outorg-convert-oldschool-elisp-buffer-to-outshine ()
  "Transform oldschool elisp buffer to outshine.
In `emacs-lisp-mode', transform an oldschool buffer (only
semicolons as outline-regexp) into an outshine buffer (with
outcommented org-mode headers)."
  (save-excursion
    (goto-char (point-min))
    (when (outline-on-heading-p)
      (outorg-convert-oldschool-elisp-headline-to-outshine))
    (while (not (eobp))
      (outline-next-heading)
      (outorg-convert-oldschool-elisp-headline-to-outshine)))
    (funcall 'outshine-hook-function))

(defun outorg-convert-oldschool-elisp-headline-to-outshine ()
  "Transform oldschool headline to outshine.
In `emacs-lisp-mode', transform one oldschool header (only semicolons) into an outshine header (outcommented org-mode header)."
  (unless (bolp) (beginning-of-line))
  (when (looking-at "^;;[;]+ ")
  (let* ((header-level
	  (- (length (match-string-no-properties 0)) 3))
	 (replacement-string
	  (concat
	   ";; "
	   (let ((strg "*"))
	     (dotimes (i (1- header-level) strg)
	       (setq strg (concat strg "*"))))
	   " ")))
    (replace-match replacement-string))))

(defun outorg-copy-and-convert ()
  "Copy code buffer content to tmp-buffer and convert it to Org syntax.
If `outorg-edit-whole-buffer' is non-nil, copy the whole buffer, otherwise
  the current subtree."
  (when (buffer-live-p (get-buffer outorg-edit-buffer-name))
    (if (y-or-n-p
	 (format "%s exists - save and overwrite contents "
		 outorg-edit-buffer-name))
	(with-current-buffer outorg-edit-buffer-name
	  (outorg-save-edits-to-tmp-file))
      (user-error "Edit as Org cancelled.")))
  (let* ((edit-buffer
          (get-buffer-create outorg-edit-buffer-name)))
    (save-restriction
      (with-current-buffer edit-buffer
        (erase-buffer))
      ;; copy code buffer content
      (copy-to-buffer
       edit-buffer
       (if outorg-edit-whole-buffer-p
           (point-min)
         (save-excursion
           (outline-back-to-heading 'INVISIBLE-OK)
           (point)))
       (if outorg-edit-whole-buffer-p
           (point-max)
         (save-excursion
           (outline-end-of-subtree)
           (point)))))
    ;; switch to edit buffer
    (if (one-window-p) (split-window-sensibly (get-buffer-window)))
    (switch-to-buffer-other-window edit-buffer)
    ;; reinstall outorg-markers
    (outorg-reinstall-markers-in-region (point-min))  
    ;; set point
    (goto-char outorg-edit-buffer-point-marker)
    ;; activate programming language major mode and convert to org
    (let ((mode (outorg-get-buffer-mode
                 (marker-buffer outorg-code-buffer-point-marker))))
      ;; special case R-mode
      (if (eq mode 'ess-mode)
          (funcall 'R-mode)
        (funcall mode)))
    ;; convert oldschool elisp headers to outshine headers
    (when outorg-oldschool-elisp-headers-p
      (outorg-convert-oldschool-elisp-buffer-to-outshine)
      ;; reset var to original state after conversion
      (setq outorg-oldschool-elisp-headers-p t))
    ;; call conversion function
    (outorg-convert-to-org)
    ;; change major mode to org-mode
    (org-mode)
    ;; activate minor mode outorg-edit-minor-mode
    (outorg-edit-minor-mode)
    ;; set outline visibility
    (if (not outorg-edit-whole-buffer-p)
        (show-all)
      (hide-sublevels 3)
      (ignore-errors (show-subtree))
      ;; insert export template
      (cond
       (outorg-ask-user-for-export-template-file-p
        (call-interactively
         'outorg-insert-export-template-file))
       (outorg-insert-default-export-template-p
        (outorg-insert-default-export-template))))
    ;; update md5 for watchdoc
    (when (and outorg-propagate-changes-p
	       (require 'org-watchdoc nil t))
      (org-watchdoc-set-md5))
    ;; reset buffer-undo-list
    (setq buffer-undo-list nil)))

(defun outorg-wrap-source-in-block (lang &optional EXAMPLE-BLOCK-P)
  "Wrap code between in src-block of LANG.
If EXAMPLE-BLOCK-P is non-nil, use an example-block instead of a
source-block. Use `outorg-pt-B-marker' and
`outorg-pt-C-marker' to find start and end position of
block."
  (save-excursion
    ;; begin of block			
    (goto-char outorg-pt-B-marker)
    (newline)
    (forward-line -1)
    (insert
     (if EXAMPLE-BLOCK-P
	 "#+begin_example"
       (format "#+begin_src %s" lang)))
    (move-marker outorg-pt-B-marker (point-at-bol))
    ;; end of block
    (goto-char outorg-pt-C-marker)
    (newline)
    ;; (forward-line -1)
    (insert
     (if EXAMPLE-BLOCK-P
	 "#+end_example"
       "#+end_src"))))

;; We treat nestable comments as code. This is the fourth field of the
;; parser state vector: it is `t' if in a non-nestable comment, or the
;; comment nesting level if inside a comment that can be nested.

(defun skip-line-comment-or-ws ()
  "If the current line is a comment or whitespace, move to the
next line and return `t'. Otherwise, leaves point alone and
returns `nil'."
  (cond
   ((looking-at "[[:space:]]*$") (forward-line))
   ((outorg-comment-on-line-p) (forward-line))
   (t nil)))

;; Note: this behavior is slightly different than `forward-comment':
;; it leaves point at the beginning of the line that is not a line
;; comment or white space, not at the actual first character of code
;; on the line.
(defun forward-line-comments ()
  "Move forward across comments. Stop scanning if we find
something other than a comment or white space. Set point to where
scanning stops."
  (while (and (not (eobp)) (skip-line-comment-or-ws))))

(defun backward-line-comments ()
  "Move backward across comments. Stop scanning if we find
something other than a comment or white space. Point is left at
the end of the first line found to not be a line comment or white
space."
  (while (and (not (bobp)) (save-excursion (skip-line-comment-or-ws)) (forward-line -1)))
  (end-of-line))

(defun outorg-convert-to-org ()
  "Convert buffer content to Org Syntax"
  (let* ((buffer-mode
	  (outorg-get-buffer-mode
	   (marker-buffer outorg-code-buffer-point-marker)))
	 (babel-lang (outorg-get-babel-name buffer-mode))
	 (example-block-p
	  (not
	   (outorg-in-babel-load-languages-p buffer-mode))))
    
    (outorg-remove-trailing-blank-lines)
    ;; reset (left-over) markers
    (move-marker outorg-pt-A-marker nil)
    (move-marker outorg-pt-B-marker nil)
    (move-marker outorg-pt-C-marker nil)
    ;; special case beginning of buffer
    (save-excursion
      (goto-char (point-min))
      ;; buffer begins with code
      (unless (outorg-comment-on-line-p)
	;; mark beginning of code
	(move-marker outorg-pt-B-marker
		     (progn
                       (forward-line-comments)
		       (point))))
      ;; loop over rest of buffer
      (while (and (< (point) (point-max))
		   ;; mark beginning of comment
		  (marker-position
		   (move-marker outorg-pt-A-marker
                                (outorg-comment-search-forward))))
	(goto-char outorg-pt-A-marker)
	;; comment does not start at BOL -> skip
	;; looking at src-block delimiter -> skip
	(if (or (not (eq (marker-position outorg-pt-A-marker)
			 (point-at-bol)))
		(looking-at "^#\\+begin_")
		(looking-at "^#\\+end_"))
	    (forward-line)
	  ;; comments starts at BOL -> convert
	  (if (marker-position outorg-pt-B-marker)
	      ;; special case buffer begins with code
              (move-marker outorg-pt-C-marker
                           (progn
                             (beginning-of-line)
                             (backward-line-comments)
                             (point)))
	    ;; default case buffer begins with comments
	    ;; mark beginning of code
	    (move-marker outorg-pt-B-marker
			 ;; skip forward comments and whitespace
			 (progn
                           (forward-line-comments)
			   (point)))
	    ;; mark end of code
	    (move-marker outorg-pt-C-marker
			 ;; search next comment (starting at bol)
			 (progn
                           (forward-line)
                           (outorg-comment-search-forward)
			   ;; move point to beg of comment
			   (beginning-of-line)
			   (unless (bobp)
			     ;; skip backward comments and whitespace
                             (backward-line-comments)
			     ;; deal with trailing comment on line
			     (unless (bobp)
			       (end-of-line)))
                           (point)))))
	  ;; wrap code between B and C in block
	  (when (< outorg-pt-B-marker outorg-pt-C-marker)
	    (outorg-wrap-source-in-block
	     babel-lang example-block-p))
	  ;; remember marker positions
	  (let ((pt-A-pos		; beg-of-comment
		 (marker-position outorg-pt-A-marker))
		(pt-B-pos		; beg-of-code
		 (marker-position outorg-pt-B-marker))
		(pt-C-pos		; end-of-code
		 (marker-position outorg-pt-C-marker)))
	    ;; special case only comments and whitespace in buffer
	    (when (and (eq pt-A-pos 1)
		       (eq pt-B-pos 1))
	      ;; mark whole buffer
	      (move-marker outorg-pt-B-marker (point-max)))
	    ;; uncomment region between A and B
	    (when (< outorg-pt-A-marker
		     outorg-pt-B-marker)
	      (uncomment-region
	       outorg-pt-A-marker outorg-pt-B-marker)
	      ;; move point to end of src
	      (and pt-B-pos pt-C-pos
		   (cond
		    ;; special case only comments and whitespace in
		    ;; buffer -> finish loop
		    ((eq (marker-position outorg-pt-B-marker)
			 (point-max))
		     (goto-char outorg-pt-B-marker))
		    ;; loop until C is at EOB
		    ((< pt-B-pos pt-C-pos)
		     (goto-char outorg-pt-C-marker))
		    (t "This should not happen"))))
            (when (< pt-C-pos pt-B-pos) (goto-char (point-max))))
	  ;; reset markers
	  (move-marker outorg-pt-B-marker nil)
	  (move-marker outorg-pt-C-marker nil)
	  (move-marker outorg-pt-A-marker nil)))))

(defun outorg-indent-active-source-blocks (mode-name)
  "Indent active source-blocks after conversion to Org.

This function calls `org-indent-block' on source-blocks in the
major-mode language of the associated source-file."
  (let ((language (outorg-get-babel-name mode-name)))
    (save-excursion
      (org-babel-map-src-blocks nil
        ;; language given as argument equal to lang of processed
        ;; block?
        (and (string-equal language lang)
             (org-babel-mark-block)
             (org-indent-region
              (car (outorg-region-or-buffer-limits))
              (cadr (outorg-region-or-buffer-limits))))))))

(defun outorg-unindent-active-source-blocks (mode-name)
  "Remove common indentation from active source-blocks.

While editing in the *outorg-edit-buffer*, the source-code of the
source-blocks with language LANG (which should be the major-mode
language of the associated source-code buffer) might be indented
consciously or by accident. The latter happens e.g. when the
source-blocks are edited with `org-edit-special' (C-c '), and
variable `org-edit-src-content-indentation' has a value > 0.

This function removes the introduced common indentation (e.g. 2
spaces) in these source-blocks (and only in them) before
converting back from Org to source-code if customizable variable
`outorg-unindent-active-source-blocks-p' is non-nil."
  (let ((language (outorg-get-babel-name mode-name)))
    (save-excursion
      (org-babel-map-src-blocks nil
        ;; language given as argument equal to lang of processed
        ;; block?
        (and (string-equal language lang)
             (org-babel-mark-block)
                   (save-restriction
                     (narrow-to-region
                      (car (outorg-region-or-buffer-limits))
                      (cadr (outorg-region-or-buffer-limits)))
                     (org-do-remove-indentation)))))))


(defun outorg-convert-back-to-code ()
  "Convert edit-buffer content back to programming language syntax.
Assume that edit-buffer major-mode has been set back to the
  programming-language major-mode of the associated code-buffer
  before this function is called."
  (let* ((comment-style "plain")	; "multi-line"?
         (buffer-mode (outorg-get-buffer-mode))
         (in-org-babel-load-languages-p
	  (outorg-in-babel-load-languages-p buffer-mode))
	 (rgxp 
	  (if in-org-babel-load-languages-p
	      (format "%s%s%s"
		      "\\(?:^#\\+begin_src[[:space:]]+"
		      (regexp-quote
		       (outorg-get-babel-name
			buffer-mode 'AS-STRG-P))
		      "[^\000]*?\n#\\+end_src\\)") ; NUL char
	    (concat 
	     "\\(?:#\\+begin_example"
	     "[^\000]*?\n#\\+end_example\\)")))
	 (first-block-p t))
    ;; 1st run: outcomment text, delete (active) block delimiters
    ;; reset (left-over) marker
    (move-marker outorg-pt-B-marker nil)
    (move-marker outorg-pt-C-marker nil)
    ;; 1st run: outcomment text
    (goto-char (point-min))
    (while (re-search-forward rgxp nil 'NOERROR)
      ;; special case 1st block
      (if first-block-p
          (progn
            ;; Handle first block
	    (move-marker outorg-pt-B-marker (match-beginning 0))
	    (move-marker outorg-pt-C-marker (match-end 0))
            (if (eq (point-min) (match-beginning 0))
                (goto-char (match-end 0))
              (save-match-data
                (ignore-errors
                  (comment-region (point-min) (match-beginning 0)))))
	    (setq first-block-p nil))
	;; default case
        (let ((previous-beg-src
	       (marker-position outorg-pt-B-marker))
	      (previous-end-src
	       (marker-position outorg-pt-C-marker)))
	  (move-marker outorg-pt-B-marker (match-beginning 0))
	  (move-marker outorg-pt-C-marker (match-end 0))
	  (save-match-data
	    (ignore-errors
	      (comment-region previous-end-src
			      (match-beginning 0))))
	  (save-excursion
	    (goto-char previous-end-src)
	    (delete-region (1- (point-at-bol)) (point-at-eol))
	    (goto-char previous-beg-src)
            (if (eq (point-at-bol) (point-min))
                (delete-region 1 (1+ (point-at-eol)))
              (delete-region (1- (point-at-bol)) (point-at-eol)))))))
    ;; special case last block
    (ignore-errors
      (comment-region
       (if first-block-p (point-min) outorg-pt-C-marker)
       (point-max)))
    (unless first-block-p		; no src-block so far
      (save-excursion
	(goto-char outorg-pt-C-marker)
	(delete-region (1- (point-at-bol)) (point-at-eol))
	(goto-char outorg-pt-B-marker)
	(delete-region (1- (point-at-bol)) (point-at-eol)))))
  (move-marker outorg-pt-B-marker nil)
  (move-marker outorg-pt-C-marker nil)
  ;; 2nd (optional) run: convert elisp headers to oldschool
  (when outorg-oldschool-elisp-headers-p
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward
	      "\\(^;;\\)\\( [*]+\\)\\( \\)"
	      nil 'NOERROR)
	(let* ((org-header-level
		(- (length (match-string-no-properties 0)) 4))
	       (replacement-string
		(let ((strg ";"))
		  (dotimes (i (1- org-header-level) strg)
		    (setq strg (concat strg ";"))))))
	   (replace-match replacement-string nil nil nil 2))))))
  ;; ;; finally remove trailing empty lines REALLY?
  ;; (outorg-remove-trailing-blank-lines))

(defun outorg-replace-code-with-edits ()
  "Replace code-buffer contents with edits."
  (let* ((edit-buf (marker-buffer outorg-edit-buffer-point-marker))
         (code-buf (marker-buffer outorg-code-buffer-point-marker))
         (edit-buf-point-min
          (with-current-buffer edit-buf
            (point-min)))
         (edit-buf-point-max
          (with-current-buffer edit-buf
            (save-excursion
              (goto-char (point-max))
              (unless (and (bolp) (looking-at "^[ \t]*$"))
                (newline))
              (point)))))
    (with-current-buffer code-buf
      (if outorg-edit-whole-buffer-p
          (progn
            (if (buffer-narrowed-p)
                (delete-region (point-min) (point-max))
              (erase-buffer))
            (insert-buffer-substring-no-properties
             edit-buf edit-buf-point-min edit-buf-point-max)
	    (outorg-reinstall-markers-in-region (point-min)))
        (goto-char
	 (marker-position outorg-code-buffer-point-marker))
        (save-restriction
          (narrow-to-region
           (save-excursion
             (outline-back-to-heading 'INVISIBLE-OK)
             (point))
           (save-excursion
             (outline-end-of-subtree)
             (point)))
          (delete-region (point-min) (point-max))
          (insert-buffer-substring-no-properties
           edit-buf edit-buf-point-min edit-buf-point-max)
	  (outorg-reinstall-markers-in-region (point-min)))
        ;; (save-buffer)
        ))))

;;;; Commands
;;;;; Edit and Exit

;;;###autoload
(defun outorg-edit-as-org (&optional arg)
  "Convert and copy to temporary Org buffer

With ARG, act conditional on the raw value of ARG:

| prefix | raw | action 1          | action 2                       |
|--------+-----+-------------------+--------------------------------|
| C-u    | (4) | edit-whole-buffer | ---                            |
| C-1    |   1 | edit-whole-buffer | insert default export-template |
| C-2    |   2 | edit-whole-buffer | prompt user for template-file  |
| C-3    |   3 | edit-whole-buffer | insert & keep default template |
| C-4    |   4 | edit-whole-buffer | insert & keep template-file    |
| C-5    |   5 | propagate changes | ---                            |

"
  (interactive "P")
  (ignore-errors
    (outorg-reset-global-vars))
  (and buffer-file-read-only
       (error "Cannot edit read-only buffer-file"))
  (and buffer-read-only
       (if (not (y-or-n-p "Buffer is read-only - make writable "))
           (error "Cannot edit read-only buffer")
         (setq inhibit-read-only t)
         (setq outorg-code-buffer-read-only-p t)))
  (and (derived-mode-p 'message-mode)
       (outorg-prepare-message-mode-buffer-for-editing))
  (and (eq major-mode 'picolisp-mode)
       (save-excursion
         (save-match-data
           (goto-char (point-max))
           (re-search-backward
            (concat "(" (regexp-quote "********") ")")
	    nil 'NOERROR)))
       (outorg-prepare-iorg-edit-buffer-for-editing))
  (move-marker outorg-code-buffer-point-marker (point))
  (save-excursion
    (or
     (outline-on-heading-p 'INVISIBLE-OK)
     (ignore-errors
       (outline-back-to-heading 'INVISIBLE-OK))
     (ignore-errors
       (outline-next-heading)))
    (move-marker
     outorg-code-buffer-beg-of-subtree-marker (point)))
  (and arg
       (cond
        ((equal arg '(4))
         (setq outorg-edit-whole-buffer-p t))
        ((equal arg 1)
         (setq outorg-edit-whole-buffer-p t)
         (setq outorg-insert-default-export-template-p t))
        ((equal arg 2)
         (setq outorg-edit-whole-buffer-p t)
         (setq outorg-ask-user-for-export-template-file-p t))
        ((equal arg 3)
         (setq outorg-edit-whole-buffer-p t)
         (setq outorg-insert-default-export-template-p t)
         (setq outorg-keep-export-template-p t))
        ((equal arg 4)
         (setq outorg-edit-whole-buffer-p t)
         (setq outorg-ask-user-for-export-template-file-p t)
         (setq outorg-keep-export-template-p t))
        ((equal arg 5)
         (setq outorg-propagate-changes-p t))))
  (and (bound-and-true-p outshine-enforce-no-comment-padding-p)
       (setq outorg-oldschool-elisp-headers-p t))
  (setq outorg-initial-window-config
        (current-window-configuration))
  (outorg-save-markers (append outorg-tracked-markers
			       outorg-tracked-org-markers))
  (outorg-copy-and-convert))

;; (defun outorg-gather-src-block-data ()
;;   "Gather beg/end data of active src-blocks in curr-buf.
;; Store the data as alist with form

;;  #+begin_src emacs-lisp
;;    ((beg-block end-block) ... (beg-block end-block))
;;  #+end_src

;; in global variable `outorg-src-block-data'."
  
(defun outorg-copy-edits-and-exit ()
  "Replace code-buffer content with (converted) edit-buffer content and
  kill edit-buffer"
  (interactive)
  (if (not buffer-undo-list)
      ;; edit-buffer not modified at all
      (progn
	(move-marker outorg-edit-buffer-point-marker (point))
	;; restore window configuration
	(set-window-configuration
	 outorg-initial-window-config)
	;; avoid confirmation prompt when killing the edit buffer
	(with-current-buffer
	    (marker-buffer outorg-edit-buffer-point-marker)
	  (set-buffer-modified-p nil))
	(kill-buffer
	 (marker-buffer outorg-edit-buffer-point-marker))
	(and outorg-code-buffer-read-only-p
	     (setq inhibit-read-only nil))
	;; (and (eq major-mode 'message-mode)
	(and (derived-mode-p 'message-mode)
	     (outorg-prepare-message-mode-buffer-for-sending))
	(and (eq major-mode 'picolisp-mode)
	     (save-excursion
	       (save-match-data
		 (goto-char (point-max))
		 (re-search-backward
		  (concat "(" (regexp-quote "********") ")")
		  nil 'NOERROR))))
	;; clean up global vars
	(outorg-reset-global-vars))
    ;; edit-buffer modified
    (widen)
    ;; propagate changes to associated doc files
    (when (and outorg-propagate-changes-p
	       (require 'org-watchdoc nil t))
      (save-excursion
	(goto-char (point-min))
	(org-watchdoc-propagate-changes)))
    (let ((mode (outorg-get-buffer-mode
		 (marker-buffer outorg-code-buffer-point-marker))))
      (and outorg-unindent-active-source-blocks-p
	   (outorg-unindent-active-source-blocks mode))
      (move-marker outorg-edit-buffer-point-marker (point))
      (move-marker outorg-edit-buffer-beg-of-subtree-marker
		   (or (ignore-errors
			 (save-excursion
			   (outline-previous-heading)
			   (point)))
		       1))    
      ;; special case R-mode
      (if (eq mode 'ess-mode)
	  (funcall 'R-mode)
	(funcall mode)))
    (outorg-convert-back-to-code)
    (outorg-save-markers (append outorg-tracked-markers
				 outorg-tracked-org-markers))
    (outorg-replace-code-with-edits)
    (set-window-configuration
     outorg-initial-window-config)
    (goto-char outorg-code-buffer-point-marker)
    ;; avoid confirmation prompt when killing the edit buffer
    (with-current-buffer
	(marker-buffer outorg-edit-buffer-point-marker)
      (set-buffer-modified-p nil))
    (kill-buffer
     (marker-buffer outorg-edit-buffer-point-marker))
    (and outorg-code-buffer-read-only-p
	 (setq inhibit-read-only nil))
    (and (derived-mode-p 'message-mode)
	 (outorg-prepare-message-mode-buffer-for-sending))
    (and (eq major-mode 'picolisp-mode)
	 (save-excursion
	   (save-match-data
	     (goto-char (point-max))
	     (re-search-backward
	      (concat "(" (regexp-quote "********") ")")
	      nil 'NOERROR)))
	 (outorg-prepare-iorg-edit-buffer-for-posting))
    (outorg-reset-global-vars)))

;;;;; Insert Export Template

;; (defun outorg-toggle-export-template-insertion (&optional arg)
;;   "Toggles automatic insertion of export template into *outorg-edit-buffer*

;; With prefix arg, unconditionally deactivates insertion if numeric
;; alue of ARG is negative, otherwise unconditionally activates it, except value
;; is 16 (C-u C-u) - then `outorg-ask-user-for-export-template-file-p' will be
;; set to t and the user asked for a file to insert.

;; Toggles the value without prefix arg."
;;   (interactive "P")
;;   (let ((num (prefix-numeric-value arg)))
;;     (cond
;;      ((= num 1) (if outorg-insert-default-export-template-p
;;                     (prog
;;                      (setq outorg-insert-default-export-template-p nil)
;;                      (setq outorg-ask-user-for-export-template-file-p nil))
;;                   (setq outorg-insert-default-export-template-p t)
;;                   (setq outorg-ask-user-for-export-template-file-p nil)))
;;      ((= num 16) (setq outorg-ask-user-for-export-template-file-p t))
;;      ((< num 0) (setq outorg-insert-default-export-template-p nil)
;;       (setq outorg-ask-user-for-export-template-file-p nil))
;;      ((> num 1) (setq outorg-insert-default-export-template-p t))
;;      (setq outorg-ask-user-for-export-template-file-p nil))))


(defun outorg-insert-default-export-template (&optional arg)
  "Insert a default export template in the *outorg-edit-buffer*"
  (interactive "P")
  (and arg
       (cond
        ((equal arg '(4))
         (setq outorg-keep-export-template-p t))))
  (save-excursion
    (goto-char (point-min))
    (insert
     (concat
      (unless outorg-keep-export-template-p
        (concat 
        "# <<<*** BEGIN EXPORT TEMPLATE "
        "[edits will be lost at exit] ***>>>\n\n"))
      (format "#+TITLE: %s\n"
              (ignore-errors
                (file-name-sans-extension
                 (file-name-nondirectory
                  (buffer-file-name
                   (marker-buffer
                    (or outorg-code-buffer-point-marker
                        outorg-code-buffer-beg-of-subtree-marker)))))))
      (format "#+LANGUAGE: %s\n" "en")
      ;; ;; many people write in English, although locale is different
      ;; (ignore-errors
      ;;   (car (split-string (getenv "LANG") "_" 'OMIT-NULLS))))
      (format "#+AUTHOR: %s\n"
              (ignore-errors
                (user-full-name)))
      (format "#+EMAIL: %s\n" (ignore-errors
                                (or user-mail-address
                                    (getenv "MAIL"))))
      (concat "#+OPTIONS:   H:3 num:t   toc:3 \\n:nil @:t ::t "
              "|:t ^:nil -:t f:t *:t <:nil  prop:t\n")
      (concat "#+OPTIONS:   TeX:t LaTeX:nil skip:nil d:nil "
              "todo:t pri:nil tags:not-in-toc\n")
      "#+OPTIONS:   author:t creator:t timestamp:t email:t\n"
      "# #+DESCRIPTION: <<add description here>>\n"
      "# #+KEYWORDS:  <<add keywords here>>\n"
      "# #+SEQ_TODO: <<add TODO keywords here>>\n"
      (concat "#+INFOJS_OPT: view:nil toc:t ltoc:t mouse:underline "
              "buttons:0 path:http://orgmode.org/org-info.js\n")
      "#+EXPORT_SELECT_TAGS: export\n"
      "#+EXPORT_EXCLUDE_TAGS: noexport\n\n"
      (unless outorg-keep-export-template-p
        "# <<<*** END EXPORT TEMPLATE ***>>>\n\n")))))

(defun outorg-insert-export-template-file (arg template-file )
  "Insert a user export-template-file in the *outorg-edit-buffer*"
  (interactive "P\nfTemplate File: ")
  (and arg
       (cond
        ((equal arg '(4))
         (setq outorg-keep-export-template-p t))))
  (save-excursion
    (goto-char (point-min))
    (unless outorg-keep-export-template-p
     (insert
      (concat
       "# <<<*** BEGIN EXPORT TEMPLATE "
       "[edits will be lost at exit] ***>>>\n\n")))
    (forward-char
     (cadr (insert-file-contents template-file)))
    (newline)
    (unless outorg-keep-export-template-p
     (insert "# <<<*** END EXPORT TEMPLATE ***>>>\n")
     (newline))))


;;;;; Misc

;; courtesy to Trey Jackson (http://tinyurl.com/cbnlemg)
(defun outorg-edit-comments-and-propagate-changes ()
  "Edit first buffer tree and propagate changes.
Used to keep exported comment-sections in sync with their
source-files."
  (interactive)
  (goto-char (point-min))
  (unless (outline-on-heading-p 'INVISIBLE-OK)
    (ignore-errors
      (outline-next-heading)))
  (outorg-edit-as-org 5))

(defun outorg-replace-source-blocks-with-results
  (&optional arg &rest languages)
  "Replace source-blocks with their results.

Only source-blocks with ':export results' in their header
arguments will be mapped.

If LANGUAGES is non-nil, only those source-blocks with a
language found in the list are mapped.

If LANGUAGES is nil but a prefix-argument ARG is given, only the
languages read from the mini-buffer (separated by blanks) are mapped.

Otherwise, all languages found in `org-babel-load-languages' are mapped."
  (interactive "P\n")
  (let ((langs (or languages
                   (and arg
                        (split-string
                         (read-string
                          (concat "Org Babel languages separated by blanks: "))
                         " " 'OMIT-NULLS))
                   (mapcar
                    (lambda (X) (symbol-name (car X)))
                    org-babel-load-languages))))
    (org-babel-map-src-blocks nil
      (and
       (string-equal
        (cdr
         (assoc
          :exports
          (org-babel-parse-header-arguments header-args)))
        "results")
       (member lang langs)
       (org-babel-execute-src-block)
       (let* ((block-start (org-babel-where-is-src-block-head))
              (results-head (org-babel-where-is-src-block-result))
              (results-body
               (save-excursion
                 (goto-char results-head)
                 (forward-line)
                 (point))))
         (delete-region block-start results-body))))))

(defun outorg-which-active-modes ()
  "Give a message of which minor modes are enabled in the current buffer."
  (interactive)
  (let ((active-modes))
    (mapc
     (lambda (mode)
       (condition-case nil
           (if (and (symbolp mode) (symbol-value mode))
               (add-to-list 'active-modes mode))
         (error nil) ))
     minor-mode-list)
    active-modes))


;;; Menus and Keys
;;;; Menus

(defvar outorg-edit-menu-map
  (let ((map (make-sparse-keymap)))
    (define-key map [outorg-copy-edits-and-exit]
      '(menu-item "Copy and Exit" outorg-copy-edits-and-exit
                  :help "Copy edits to original-buffer
                  and exit outorg"))
    (define-key map [outorg-save-edits-to-tmp-file]
      '(menu-item "Save" outorg-save-edits-to-tmp-file
                  :help "Save edit buffer to temporary
                  file in the OS tmp directory"))
    map))

;;;; Keys

;;;;; Mode Keys

(defvar outorg-edit-minor-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\M-#"
      'outorg-copy-edits-and-exit)
    (define-key map "\C-x\C-s"
      'outorg-save-edits-to-tmp-file)
    (define-key map [menu-bar outorg-edit]
      (cons (purecopy "Outorg") outorg-edit-menu-map))
    map))

(add-to-list 'minor-mode-map-alist
             (cons 'outorg-edit-minor-mode
                   outorg-edit-minor-mode-map))

;;; Run hooks and provide

(run-hooks 'outorg-hook)

(provide 'outorg)

;; Local Variables:
;; coding: utf-8
;; ispell-local-dictionary: "en_US"
;; End:

;;; outorg.el ends here
