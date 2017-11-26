;;; outshine-org-cmds.el --- outshine-use-outorg functions

;; Author: Adam Porter <adam@alphapapa.net>
;; Version: 0.1
;; URL: https://github.com/alphapapa/outshine
;; Package-Requires: ((outorg "2.0") (cl-lib "0.5"))

;;;; MetaData
;;   :PROPERTIES:
;;   :copyright: Thorsten_Jolitz
;;   :copyright-from: 2016+
;;   :version:  0.1
;;   :licence:  GPL 2 or later (free software)
;;   :licence-url: http://www.gnu.org/licenses/
;;   :part-of-emacs: no
;;   :authors: Adam_Porter Thorsten_Jolitz
;;   :keywords: emacs outlines file_structuring
;;   :git-repo: https://github.com/alphapapa/outshine.git
;;   :git-clone: git://github.com/alphapapa/outshine.git
;;   :END:

;;;; Commentary

;; Functions that aim to make outshine headlines as 'intelligent' as
;; Org-mode headlines - whenever it is possible and makes sense.

;; This library contains outcommented skeletons of 'outshine-use-outorg'
;; functions for all interactive Org functions (as returned bei C-h
;; w). Each of these functions has been made a TODO entry, and the
;; following sequence is assumed: todo(->next|waiting)->done|cancelled.

;;  - TODO  :: nothing has been done
;;  - NEXT  :: modified, but not finished
;;  - WAITING :: work paused due to unsolved problems
;;  - DONE  :: finished and tested
;;  - CANCELLED :: makes no sense, or too difficult 

;;;; Fundamental Problems to be solved

;;;;; Outshine Agenda 

;;;;; Outshine Clocking

;;;; Templates

;; ;; TEMPLATE A
;; (defun outshine- ()
;;   "Call outorg to trigger `org-'."
;;   (interactive)
;;   (outshine-use-outorg 'org-))

;; ;; TEMPLATE B
;; (defun outshine- (&optional arg)
;;   "Call outorg to trigger `org-'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org- nil arg))


;;; Variables
;;; Functions
;;;; Agenda Functions
(defun outshine-agenda-create-temporary-agenda-file (&optional restriction-lock buf-or-name pos)
  "Create a single temporary outshine agenda file.

Concatenate all `outshine-agenda-files', after converting them to
Org-mode, into a single Org file in the
`outshine-temporary-directory'. Return that file's
buffer-file-name.

When RESTRICTION-LOCK is given, act conditional on its value:

 - file :: (symbol) restrict to buffer

 - t :: (any) restrict to subtree

Use current-buffer and point position, unless BUF-OR-NAME and/or
POS are non-nil."
  (let* ((temporary-file-directory outshine-temporary-directory)
	 (curr-agenda-file (make-temp-file "outshine-" nil ".org"))
	 (buf (if (and buf-or-name (buffer-file-name buf-or-name))
		  buf-or-name
		(current-buffer)))
	 (pos (if (and pos (integer-or-marker-p pos)
		       (<= pos (buffer-size buf)))
		  pos
		(point))))
    (with-current-buffer (find-file-noselect curr-agenda-file)
      (cond
       ((eq restriction-lock 'file)
	(insert
	 (with-current-buffer buf
	   (outshine-get-outorg-edit-buffer-content))))
       (restriction-lock
	(insert
	 (with-current-buffer buf
	   (save-excursion
	     (goto-char pos)
	     (save-restriction
	       (outshine-narrow-to-subtree)
	       (outshine-get-outorg-edit-buffer-content))))))
       (t (mapc
	   (lambda (--file)
	     (insert
	      (outshine-get-outorg-edit-buffer-content --file))
	     (forward-line 2))
	   outshine-agenda-files)))
      (save-buffer)
      (kill-buffer))
    curr-agenda-file))

;; rather obsolete - better use agenda restriction lock
(defun outshine-agenda-set-org-agenda-files (&rest file-lst)
  "Set `org-agenda-files' to FILE-LST.
Store old value in `outshine-agenda-old-org-agenda-files'."
  (setq outshine-agenda-old-org-agenda-files org-agenda-files)
  (setq org-agenda-files file-lst))

;; rather obsolete - better use agenda restriction lock
(defun outshine-agenda-restore-org-agenda-files ()
  "Restore `org-agenda-files'.
The old value is stored in
`outshine-agenda-old-org-agenda-files'."
  (setq org-agenda-files outshine-agenda-old-org-agenda-files)
  (setq outshine-agenda-old-org-agenda-files nil))

;;;; Special Case Latex-Mode
(defun outshine-get-latex-documentclass (&optional buf-or-name no-check-p)
  "Return latex document class of current-buffer.
If BUF-OR-NAME is non-nil, use it instead of current buffer. If
NO-CHECK-P is non-nil, assume BUF-OR-NAME is ok (i.e. live and in
latex-mode) and just use it."
  (catch 'exit
  (let ((buf (cond
	      ((and buf-or-name no-check-p) buf-or-name)
	      ((and buf-or-name
		    (buffer-live-p buf-or-name)
		    (with-current-buffer buf-or-name
		      (eq major-mode 'latex-mode)))
	       buf-or-name)
	      ((eq major-mode 'latex-mode) (current-buffer))
	      (t (throw 'exit nil)))))
    (with-current-buffer buf
      (save-excursion
	(save-restriction
	  (widen)
	  (goto-char (point-min))
	  (re-search-forward outshine-latex-documentclass-regexp
			     nil 'NOERROR 1)
	  (org-no-properties (match-string 1))))))))

;;;; Use Outorg functions

(defun outshine-comment-region (beg end &optional arg)
       "Use comment-style that always inserts at BOL.
Call `comment-region' with a comment-style that guarantees
   insertion of comment-start markers at beginning-of-line."
       (interactive "r")
       (let ((comment-style
              (if (member comment-style '(indent-or-triple indent))
                  'plain
                comment-style)))
         (comment-region beg end arg)))

(defun outshine-get-outorg-edit-buffer-content (&optional buf-or-file)
  "Get content of buffer `outorg-edit-buffer-name.'
Use current buffer for conversion, unless BUF-OR-FILE is given."
  (let (buf-strg)
    (with-current-buffer
	(cond
	 ((ignore-errors (file-exists-p buf-or-file))
	  (find-file-noselect buf-or-file))
	 ((ignore-errors (get-buffer buf-or-file))
	  buf-or-file)
	 (t (current-buffer)))
      (outshine-use-outorg
       (lambda ()
	 (interactive)
	 (setq buf-strg
	       (buffer-substring-no-properties
		(point-min) (point-max))))
       'WHOLE-BUFFER-P))
    buf-strg))

;; courtesy of Pascal Bourguignon
(defun outshine-use-outorg-finish-store-log-note ()
  "Finish store-log-note and exit recursive edit"
  (message "...entering outorg-finish-function")
  (setq outorg-org-finish-function-called-p t)
  (org-store-log-note)
  (outorg-copy-edits-and-exit))
  ;; (exit-recursive-edit))

(defun outshine-use-outorg (fun &optional whole-buffer-p &rest funargs)
  "Use outorg to call FUN with FUNARGS on subtree or thing at point.

FUN should be an Org-mode function that acts on the subtree or
org-element at point. Optionally, with WHOLE-BUFFER-P non-nil,
`outorg-edit-as-org' can be called on the whole buffer.

Sets the variable `outshine-use-outorg-last-headline-marker' so
that it always contains a point-marker to the last headline this
function was called upon."
  (save-excursion
    (unless (outline-on-heading-p)
      (or (outline-previous-heading)
	  (outline-next-heading)))
    (move-marker outshine-use-outorg-last-headline-marker (point)))
  (if whole-buffer-p
      (outorg-edit-as-org '(4))
    (outorg-edit-as-org))
  (setq outorg-called-via-outshine-use-outorg-p t)
  (goto-char outorg-edit-buffer-point-marker)
  (if funargs
      (apply fun funargs)
    (call-interactively fun))
  (outorg-copy-edits-and-exit))

;;; Commands
;;;; Outshine Agenda

(defun outshine-agenda-add-files (&optional append-p &rest files)
  "Prepend FILES to `outshine-agenda-files'.
Append rather than prepend if APPEND-P is given or
`current-prefix-arg' is non-nil."
  (interactive
   (let (file-lst)
     (list
      current-prefix-arg
      (if (derived-mode-p 'dired-mode)
	  (dired-get-marked-files)
	(setq file-lst
	      (cons
	       (expand-file-name
		(ido-read-file-name "New agenda file: "))
	       file-lst))
	(while (y-or-n-p "Add more files ")
	  (setq file-lst
		(cons (expand-file-name
		       (ido-read-file-name "New agenda file: "))
		      file-lst)))
	file-lst))))
  (if append-p
      (setq outshine-agenda-files
	    (delq nil (append outshine-agenda-files
			      (car-safe files))))
    (setq outshine-agenda-files
	  (delq nil (append (car-safe files)
			    outshine-agenda-files)))))

(defun outshine-agenda-remove-files (&optional remove-all-p &rest files)
  "Remove FILES from `outshine-agenda-files'.
Remove all agenda-files if REMOVE-ALL-P is given or
`current-prefix-arg' is non-nil."
  (interactive
   (let (file-lst)
     (list
      current-prefix-arg
      (unless current-prefix-arg
	(setq file-lst
	      (cons
	       (org-completing-read "Remove agenda file: "
				    outshine-agenda-files)
	       file-lst))
	(while (y-or-n-p "Remove more files ")
	  (setq file-lst
		(cons
		 (org-completing-read "Remove agenda file: "
				      outshine-agenda-files)
		 file-lst)))
	file-lst))))
  (if remove-all-p
      (setq outshine-agenda-files nil)
    (mapc
     (lambda (--file)
       (setq outshine-agenda-files
	     (remove --file outshine-agenda-files)))
     (car-safe files))))

(defun outshine-agenda-toggle-include-org-agenda (&optional arg)
  "Toggle inclusion of Org Agenda files in Outshine Agenda.
With prefix argument ARG, include if ARG is positive, otherwise
exclude."
  (interactive "P")
  (setq outshine-agenda-include-org-agenda-p
        (if (null arg)
            (not outshine-agenda-include-org-agenda-p)
          (> (prefix-numeric-value arg) 0)))
  (message "Outshine Agenda: inclusion of Org Agenda files %s"
           (if outshine-agenda-include-org-agenda-p
	       "enabled" "disabled")))

(defun outshine-agenda (&optional agenda-file include-org-p)
  "Create Outshine Agenda, i.e. Org Agenda on outshine files.

Use org-file AGENDA-FILE instead of `outshine-agenda-files' when
given. Include `org-agenda-files' when INCLUDE-ORG-P is non-nil.

With `current-prefix-arg' prompt the user for argument values."
  (interactive
   (when current-prefix-arg
     (list
      (ido-read-file-name "Agenda file: "
			  outshine-temporary-directory)
      (y-or-n-p "Include `org-agenda-files' "))))
  (let ((ag-file (or agenda-file
		     (outshine-agenda-create-temporary-agenda-file)))
	(with-org-agenda-files
	 (or include-org-p outshine-agenda-include-org-agenda-p)))
    (require 'org-agenda)
    (org-agenda-remove-restriction-lock)
    (if with-org-agenda-files
	;; FIXME
	(message "Sorry, this is not yet implemented.")
      (with-current-buffer (find-file-noselect ag-file)
	(org-agenda-set-restriction-lock 'file)
	(org-agenda)))))

;;;; Use Outorg for calling Org
;;;;; TODO org-add-note

;; ;; C-c C-z (org-add-note)
;; (defun outshine-add-note(&optional arg)
;;   "Call outorg to trigger `org-add-note'."
;;   (interactive "P")
      ;;   (outshine-use-outorg 'org-add-note nil arg))

;;;;; TODO org-agenda

;; ;; <menu-bar> <Org> <Agenda Command...>, C-c a (org-agenda)
;; (defun outshine-agenda(&optional arg)
;;   "Call outorg to trigger `org-agenda'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda nil arg))

;;;;; TODO org-agenda-columns

;; ;; M-x org-agenda-columns RET
;; (defun outshine-agenda-columns(&optional arg)
;;   "Call outorg to trigger `org-agenda-columns'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda-columns nil arg))

;;;;; TODO org-agenda-file-to-front

;; ;; <menu-bar> <Org> <File List for Agenda> <Add/Move Current File to Front of List> (org-agenda-file-to-front)
;; (defun outshine-agenda-file-to-front(&optional arg)
;;   "Call outorg to trigger `org-agenda-file-to-front'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda-file-to-front nil arg))

;;;;; TODO org-agenda-list

;; ;; M-x org-agenda-list RET
;; (defun outshine-agenda-list(&optional arg)
;;   "Call outorg to trigger `org-agenda-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda-list nil arg))

;;;;; TODO org-agenda-list-stuck-projects

;; ;; M-x org-agenda-list-stuck-projects RET
;; (defun outshine-agenda-list-stuck-projects(&optional arg)
;;   "Call outorg to trigger `org-agenda-list-stuck-projects'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda-list-stuck-projects nil arg))

;;;;; TODO org-agenda-prepare-buffers

;; ;; M-x org-agenda-prepare-buffers RET
;; (defun outshine-agenda-prepare-buffers(&optional arg)
;;   "Call outorg to trigger `org-agenda-prepare-buffers'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda-prepare-buffers nil arg))

;;;;; DONE org-agenda-set-restriction-lock
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:04]

;; C-c C-x < (org-agenda-set-restriction-lock)
(defun outshine-agenda-set-restriction-lock (&optional arg)
  "Call `outshine-agenda' with restriction.
With prefix ARG given, restrict to current subtree, otherwise to
current buffer(-file). "
  (interactive "P")
  (let ((ag-file
	 (if arg
	     (outshine-agenda-create-temporary-agenda-file t)
	   (outshine-agenda-create-temporary-agenda-file 'file))))
    (outshine-agenda ag-file)))

;;;;; TODO org-agenda-to-appt

;; ;; M-x org-agenda-to-appt RET
;; (defun outshine-agenda-to-appt(&optional arg)
;;   "Call outorg to trigger `org-agenda-to-appt'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-agenda-to-appt nil arg))

;;;;; TODO org-align-all-tags

;; ;; M-x org-align-all-tags RET
;; (defun outshine-align-all-tags(&optional arg)
;;   "Call outorg to trigger `org-align-all-tags'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-align-all-tags nil arg))

;;;;; TODO org-advertized-archive-subtree

;; ;; M-x org-advertized-archive-subtree RET;
;; ;;  its alias C-c $, C-c C-x C-s, <menu-bar> <Org> <Archive> <Move Subtree to Archive file> (org-archive-subtree)
;; (defun outshine-advertized-archive-subtree(&optional arg)
;;   "Call outorg to trigger `org-advertized-archive-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-advertized-archive-subtree nil arg))

;;;;; TODO org-archive-subtree

;; ;; C-c $, C-c C-x C-s, <menu-bar> <Org> <Archive> <Move Subtree to Archive file> (org-archive-subtree);
;; ;;  its alias M-x org-advertized-archive-subtree RET
;; (defun outshine-archive-subtree(&optional arg)
;;   "Call outorg to trigger `org-archive-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-archive-subtree nil arg))

;;;;; TODO org-archive-subtree-default

;; ;; C-c C-x C-a, <menu-bar> <Org> <Archive> <Archive (default method)> (org-archive-subtree-default)
;; (defun outshine-archive-subtree-default(&optional arg)
;;   "Call outorg to trigger `org-archive-subtree-default'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-archive-subtree-default nil arg))

;;;;; TODO org-archive-subtree-default-with-confirmation 

;; ;; M-x org-archive-subtree-default-with-confirmation RET
;; (defun outshine-archive-subtree-default-with-confirmation(&optional arg)
;;   "Call outorg to trigger `org-archive-subtree-default-with-confirmation'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-archive-subtree-default-with-confirmation nil arg))

;;;;; TODO org-archive-to-archive-sibling

;; ;; C-c C-x A, <menu-bar> <Org> <Archive> <Move subtree to Archive sibling> (org-archive-to-archive-sibling)
;; (defun outshine-archive-to-archive-sibling(&optional arg)
;;   "Call outorg to trigger `org-archive-to-archive-sibling'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-archive-to-archive-sibling nil arg))

;;;;; TODO org-ascii-export-as-ascii

;; ;; M-x org-ascii-export-as-ascii RET
;; (defun outshine-ascii-export-as-ascii(&optional arg)
;;   "Call outorg to trigger `org-ascii-export-as-ascii'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ascii-export-as-ascii nil arg))

;;;;; TODO org-ascii-export-to-ascii

;; ;; M-x org-ascii-export-to-ascii RET
;; (defun outshine-ascii-export-to-ascii(&optional arg)
;;   "Call outorg to trigger `org-ascii-export-to-ascii'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ascii-export-to-ascii nil arg))

;;;;; TODO org-at-date-range-p

;; ;; M-x org-at-date-range-p RET
;; (defun outshine-at-date-range-p(&optional arg)
;;   "Call outorg to trigger `org-at-date-range-p'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-at-date-range-p nil arg))

;;;;; TODO org-at-timestamp-p

;; ;; M-x org-at-timestamp-p RET
;; (defun outshine-at-timestamp-p(&optional arg)
;;   "Call outorg to trigger `org-at-timestamp-p'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-at-timestamp-p nil arg))

;;;;; TODO org-attach

;; ;; C-c C-a (org-attach)
;; (defun outshine-attach(&optional arg)
;;   "Call outorg to trigger `org-attach'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-attach nil arg))

;;;;; TODO org-babel-check-src-block

;; ;; C-c C-v c, C-c C-v C-c (org-babel-check-src-block)
;; (defun outshine-babel-check-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-check-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-check-src-block nil arg))

;;;;; TODO org-babel-demarcate-block

;; ;; C-c C-v d, C-c C-v C-d (org-babel-demarcate-block)
;; (defun outshine-babel-demarcate-block(&optional arg)
;;   "Call outorg to trigger `org-babel-demarcate-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-demarcate-block nil arg))

;;;;; TODO org-babel-describe-bindings

;; ;; C-c C-v h (org-babel-describe-bindings)
;; (defun outshine-babel-describe-bindings(&optional arg)
;;   "Call outorg to trigger `org-babel-describe-bindings'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-describe-bindings nil arg))

;;;;; TODO org-babel-detangle

;; ;; M-x org-babel-detangle RET
;; (defun outshine-babel-detangle(&optional arg)
;;   "Call outorg to trigger `org-babel-detangle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-detangle nil arg))

;;;;; TODO org-babel-do-key-sequence-in-edit-buffer

;; ;; C-c C-v x, C-c C-v C-x (org-babel-do-key-sequence-in-edit-buffer)
;; (defun outshine-babel-do-key-sequence-in-edit-buffer(&optional arg)
;;   "Call outorg to trigger `org-babel-do-key-sequence-in-edit-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-do-key-sequence-in-edit-buffer nil arg))

;;;;; TODO org-babel-examplify-region

;; ;; M-x org-babel-examplify-region RET;
;; ;;  its alias M-x org-babel-examplize-region RET
;; (defun outshine-babel-examplify-region(&optional arg)
;;   "Call outorg to trigger `org-babel-examplify-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-examplify-region nil arg))

;;;;; TODO org-babel-examplize-region

;; ;; M-x org-babel-examplize-region RET;
;; ;;  its alias M-x org-babel-examplify-region RET
;; (defun outshine-babel-examplize-region(&optional arg)
;;   "Call outorg to trigger `org-babel-examplize-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-examplize-region nil arg))

;;;;; TODO org-babel-execute-buffer

;; ;; C-c C-v b, C-c C-v C-b (org-babel-execute-buffer)
;; (defun outshine-babel-execute-buffer(&optional arg)
;;   "Call outorg to trigger `org-babel-execute-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-execute-buffer nil arg))

;;;;; TODO org-babel-execute-maybe

;; ;; C-c C-v C-e, C-c C-v e (org-babel-execute-maybe)
;; (defun outshine-babel-execute-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-execute-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-execute-maybe nil arg))

;;;;; TODO org-babel-execute-src-block

;; ;; M-x org-babel-execute-src-block RET
;; (defun outshine-babel-execute-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-execute-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-execute-src-block nil arg))

;;;;; TODO org-babel-execute-src-block-maybe

;; ;; M-x org-babel-execute-src-block-maybe RET
;; (defun outshine-babel-execute-src-block-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-execute-src-block-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-execute-src-block-maybe nil arg))

;;;;; TODO org-babel-execute-subtree

;; ;; C-c C-v s, C-c C-v C-s (org-babel-execute-subtree)
;; (defun outshine-babel-execute-subtree(&optional arg)
;;   "Call outorg to trigger `org-babel-execute-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-execute-subtree nil arg))

;;;;; TODO org-babel-exp-process-buffer

;; ;; M-x org-babel-exp-process-buffer RET
;; (defun outshine-babel-exp-process-buffer(&optional arg)
;;   "Call outorg to trigger `org-babel-exp-process-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-exp-process-buffer nil arg))

;;;;; TODO org-babel-exp-src-block

;; ;; M-x org-babel-exp-src-block RET
;; (defun outshine-babel-exp-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-exp-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-exp-src-block nil arg))

;;;;; TODO org-babel-expand-src-block

;; ;; C-c C-v v, C-c C-v C-v (org-babel-expand-src-block)
;; (defun outshine-babel-expand-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-expand-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-expand-src-block nil arg))

;;;;; TODO org-babel-expand-src-block-maybe

;; ;; M-x org-babel-expand-src-block-maybe RET
;; (defun outshine-babel-expand-src-block-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-expand-src-block-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-expand-src-block-maybe nil arg))

;;;;; TODO org-babel-goto-named-result

;; ;; C-c C-v C-r, C-c C-v r (org-babel-goto-named-result)
;; (defun outshine-babel-goto-named-result(&optional arg)
;;   "Call outorg to trigger `org-babel-goto-named-result'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-goto-named-result nil arg))

;;;;; TODO org-babel-goto-named-src-block

;; ;; C-c C-v g (org-babel-goto-named-src-block)
;; (defun outshine-babel-goto-named-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-goto-named-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-goto-named-src-block nil arg))

;;;;; TODO org-babel-goto-src-block-head

;; ;; C-c C-v C-u, C-c C-v u (org-babel-goto-src-block-head)
;; (defun outshine-babel-goto-src-block-head(&optional arg)
;;   "Call outorg to trigger `org-babel-goto-src-block-head'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-goto-src-block-head nil arg))

;;;;; TODO org-babel-hash-at-point

;; ;; M-x org-babel-hash-at-point RET
;; (defun outshine-babel-hash-at-point(&optional arg)
;;   "Call outorg to trigger `org-babel-hash-at-point'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-hash-at-point nil arg))

;;;;; TODO org-babel-hide-result-toggle

;; ;; M-x org-babel-hide-result-toggle RET
;; (defun outshine-babel-hide-result-toggle(&optional arg)
;;   "Call outorg to trigger `org-babel-hide-result-toggle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-hide-result-toggle nil arg))

;;;;; TODO org-babel-hide-result-toggle-maybe

;; ;; M-x org-babel-hide-result-toggle-maybe RET
;; (defun outshine-babel-hide-result-toggle-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-hide-result-toggle-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-hide-result-toggle-maybe nil arg))

;;;;; TODO org-babel-initiate-session

;; ;; M-x org-babel-initiate-session RET
;; (defun outshine-babel-initiate-session(&optional arg)
;;   "Call outorg to trigger `org-babel-initiate-session'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-initiate-session nil arg))

;;;;; TODO org-babel-insert-header-arg

;; ;; C-c C-v j, C-c C-v C-j (org-babel-insert-header-arg)
;; (defun outshine-babel-insert-header-arg(&optional arg)
;;   "Call outorg to trigger `org-babel-insert-header-arg'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-insert-header-arg nil arg))

;;;;; TODO org-babel-lilypond-tangle

;; ;; M-x org-babel-lilypond-tangle RET
;; (defun outshine-babel-lilypond-tangle(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-tangle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-tangle nil arg))

;;;;; TODO org-babel-lilypond-toggle-arrange-mode

;; ;; M-x org-babel-lilypond-toggle-arrange-mode RET
;; (defun outshine-babel-lilypond-toggle-arrange-mode(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-toggle-arrange-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-toggle-arrange-mode nil arg))

;;;;; TODO org-babel-lilypond-toggle-html-generation

;; ;; M-x org-babel-lilypond-toggle-html-generation RET
;; (defun outshine-babel-lilypond-toggle-html-generation(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-toggle-html-generation'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-toggle-html-generation nil arg))

;;;;; TODO org-babel-lilypond-toggle-midi-play

;; ;; M-x org-babel-lilypond-toggle-midi-play RET
;; (defun outshine-babel-lilypond-toggle-midi-play(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-toggle-midi-play'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-toggle-midi-play nil arg))

;;;;; TODO org-babel-lilypond-toggle-pdf-display

;; ;; M-x org-babel-lilypond-toggle-pdf-display RET
;; (defun outshine-babel-lilypond-toggle-pdf-display(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-toggle-pdf-display'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-toggle-pdf-display nil arg))

;;;;; TODO org-babel-lilypond-toggle-pdf-generation

;; ;; M-x org-babel-lilypond-toggle-pdf-generation RET
;; (defun outshine-babel-lilypond-toggle-pdf-generation(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-toggle-pdf-generation'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-toggle-pdf-generation nil arg))

;;;;; TODO org-babel-lilypond-toggle-png-generation

;; ;; M-x org-babel-lilypond-toggle-png-generation RET
;; (defun outshine-babel-lilypond-toggle-png-generation(&optional arg)
;;   "Call outorg to trigger `org-babel-lilypond-toggle-png-generation'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lilypond-toggle-png-generation nil arg))

;;;;; TODO org-babel-load-file

;; ;; M-x org-babel-load-file RET
;; (defun outshine-babel-load-file(&optional arg)
;;   "Call outorg to trigger `org-babel-load-file'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-load-file nil arg))

;;;;; TODO org-babel-load-in-session

;; ;; C-c C-v l, C-c C-v C-l (org-babel-load-in-session)
;; (defun outshine-babel-load-in-session(&optional arg)
;;   "Call outorg to trigger `org-babel-load-in-session'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-load-in-session nil arg))

;;;;; TODO org-babel-load-in-session-maybe

;; ;; M-x org-babel-load-in-session-maybe RET
;; (defun outshine-babel-load-in-session-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-load-in-session-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-load-in-session-maybe nil arg))

;;;;; TODO org-babel-lob-execute-maybe

;; ;; M-x org-babel-lob-execute-maybe RET
;; (defun outshine-babel-lob-execute-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-lob-execute-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lob-execute-maybe nil arg))

;;;;; TODO org-babel-lob-ingest

;; ;; C-c C-v i (org-babel-lob-ingest)
;; (defun outshine-babel-lob-ingest(&optional arg)
;;   "Call outorg to trigger `org-babel-lob-ingest'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-lob-ingest nil arg))

;;;;; TODO org-babel-mark-block

;; ;; C-c C-v C-M-h (org-babel-mark-block)
;; (defun outshine-babel-mark-block(&optional arg)
;;   "Call outorg to trigger `org-babel-mark-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-mark-block nil arg))

;;;;; TODO org-babel-next-src-block

;; ;; C-c C-v C-n, C-c C-v n (org-babel-next-src-block)
;; (defun outshine-babel-next-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-next-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-next-src-block nil arg))

;;;;; TODO org-babel-open-src-block-result

;; ;; C-c C-v C-o, C-c C-v o (org-babel-open-src-block-result)
;; (defun outshine-babel-open-src-block-result(&optional arg)
;;   "Call outorg to trigger `org-babel-open-src-block-result'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-open-src-block-result nil arg))

;;;;; TODO org-babel-picolisp-toggle-cmd

;; ;; M-x org-babel-picolisp-toggle-cmd RET
;; (defun outshine-babel-picolisp-toggle-cmd(&optional arg)
;;   "Call outorg to trigger `org-babel-picolisp-toggle-cmd'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-picolisp-toggle-cmd nil arg))

;;;;; TODO org-babel-pop-to-session

;; ;; M-x org-babel-pop-to-session RET;
;; ;;  its alias C-c C-v C-z (org-babel-switch-to-session)
;; (defun outshine-babel-pop-to-session(&optional arg)
;;   "Call outorg to trigger `org-babel-pop-to-session'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-pop-to-session nil arg))

;;;;; TODO org-babel-pop-to-session-maybe

;; ;; M-x org-babel-pop-to-session-maybe RET
;; (defun outshine-babel-pop-to-session-maybe(&optional arg)
;;   "Call outorg to trigger `org-babel-pop-to-session-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-pop-to-session-maybe nil arg))

;;;;; TODO org-babel-previous-src-block

;; ;; C-c C-v C-p, C-c C-v p (org-babel-previous-src-block)
;; (defun outshine-babel-previous-src-block(&optional arg)
;;   "Call outorg to trigger `org-babel-previous-src-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-previous-src-block nil arg))

;;;;; TODO org-babel-remove-inline-result

;; ;; M-x org-babel-remove-inline-result RET
;; (defun outshine-babel-remove-inline-result(&optional arg)
;;   "Call outorg to trigger `org-babel-remove-inline-result'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-remove-inline-result nil arg))

;;;;; TODO org-babel-remove-result

;; ;; M-x org-babel-remove-result RET
;; (defun outshine-babel-remove-result(&optional arg)
;;   "Call outorg to trigger `org-babel-remove-result'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-remove-result nil arg))

;;;;; TODO org-babel-remove-result-one-or-many

;; ;; C-c C-v k (org-babel-remove-result-one-or-many)
;; (defun outshine-babel-remove-result-one-or-many(&optional arg)
;;   "Call outorg to trigger `org-babel-remove-result-one-or-many'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-remove-result-one-or-many nil arg))

;;;;; TODO org-babel-result-hide-all

;; ;; M-x org-babel-result-hide-all RET
;; (defun outshine-babel-result-hide-all(&optional arg)
;;   "Call outorg to trigger `org-babel-result-hide-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-result-hide-all nil arg))

;;;;; TODO org-babel-sha1-hash

;; ;; C-c C-v a, C-c C-v C-a (org-babel-sha1-hash)
;; (defun outshine-babel-sha1-hash(&optional arg)
;;   "Call outorg to trigger `org-babel-sha1-hash'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-sha1-hash nil arg))

;;;;; TODO org-babel-switch-to-session

;; ;; C-c C-v C-z (org-babel-switch-to-session);
;; ;;  its alias M-x org-babel-pop-to-session RET
;; (defun outshine-babel-switch-to-session(&optional arg)
;;   "Call outorg to trigger `org-babel-switch-to-session'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-switch-to-session nil arg))

;;;;; TODO org-babel-switch-to-session-with-code

;; ;; C-c C-v z (org-babel-switch-to-session-with-code)
;; (defun outshine-babel-switch-to-session-with-code(&optional arg)
;;   "Call outorg to trigger `org-babel-switch-to-session-with-code'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-switch-to-session-with-code nil arg))

;;;;; TODO org-babel-tangle

;; ;; C-c C-v t, C-c C-v C-t (org-babel-tangle)
;; (defun outshine-babel-tangle(&optional arg)
;;   "Call outorg to trigger `org-babel-tangle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-tangle nil arg))

;;;;; TODO org-babel-tangle-clean

;; ;; M-x org-babel-tangle-clean RET
;; (defun outshine-babel-tangle-clean(&optional arg)
;;   "Call outorg to trigger `org-babel-tangle-clean'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-tangle-clean nil arg))

;;;;; TODO org-babel-tangle-file

;; ;; C-c C-v f, C-c C-v C-f (org-babel-tangle-file)
;; (defun outshine-babel-tangle-file(&optional arg)
;;   "Call outorg to trigger `org-babel-tangle-file'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-tangle-file nil arg))

;;;;; TODO org-babel-tangle-jump-to-org

;; ;; M-x org-babel-tangle-jump-to-org RET
;; (defun outshine-babel-tangle-jump-to-org(&optional arg)
;;   "Call outorg to trigger `org-babel-tangle-jump-to-org'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-tangle-jump-to-org nil arg))

;;;;; TODO org-babel-view-src-block-info

;; ;; C-c C-v I, C-c C-v TAB (org-babel-view-src-block-info)
;; (defun outshine-babel-view-src-block-info(&optional arg)
;;   "Call outorg to trigger `org-babel-view-src-block-info'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-view-src-block-info nil arg))

;;;;; TODO org-backward-element

;; ;; M-{ (org-backward-element)
;; (defun outshine-backward-element(&optional arg)
;;   "Call outorg to trigger `org-backward-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-backward-element nil arg))

;;;;; TODO org-backward-heading-same-level

;; ;; C-c C-b, <menu-bar> <Org> <Navigate Headings> <Previous Same Level> (org-backward-heading-same-level)
;; (defun outshine-backward-heading-same-level(&optional arg)
;;   "Call outorg to trigger `org-backward-heading-same-level'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-backward-heading-same-level nil arg))

;;;;; TODO org-backward-paragraph

;; ;; <C-up> (org-backward-paragraph)
;; (defun outshine-backward-paragraph(&optional arg)
;;   "Call outorg to trigger `org-backward-paragraph'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-backward-paragraph nil arg))

;;;;; TODO org-backward-sentence

;; ;; M-a (org-backward-sentence)
;; (defun outshine-backward-sentence(&optional arg)
;;   "Call outorg to trigger `org-backward-sentence'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-backward-sentence nil arg))

;;;;; TODO org-beamer-export-as-latex

;; ;; M-x org-beamer-export-as-latex RET
;; (defun outshine-beamer-export-as-latex(&optional arg)
;;   "Call outorg to trigger `org-beamer-export-as-latex'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beamer-export-as-latex nil arg))

;;;;; TODO org-beamer-export-to-latex

;; ;; M-x org-beamer-export-to-latex RET
;; (defun outshine-beamer-export-to-latex(&optional arg)
;;   "Call outorg to trigger `org-beamer-export-to-latex'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beamer-export-to-latex nil arg))

;;;;; TODO org-beamer-export-to-pdf

;; ;; M-x org-beamer-export-to-pdf RET
;; (defun outshine-beamer-export-to-pdf(&optional arg)
;;   "Call outorg to trigger `org-beamer-export-to-pdf'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beamer-export-to-pdf nil arg))

;;;;; TODO org-beamer-mode

;; ;; M-x org-beamer-mode RET
;; (defun outshine-beamer-mode(&optional arg)
;;   "Call outorg to trigger `org-beamer-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beamer-mode nil arg))

;;;;; TODO org-beamer-select-environment

;; ;; M-x org-beamer-select-environment RET
;; (defun outshine-beamer-select-environment(&optional arg)
;;   "Call outorg to trigger `org-beamer-select-environment'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beamer-select-environment nil arg))

;;;;; TODO org-beginning-of-item

;; ;; M-x org-beginning-of-item RET
;; (defun outshine-beginning-of-item(&optional arg)
;;   "Call outorg to trigger `org-beginning-of-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beginning-of-item nil arg))

;;;;; TODO org-beginning-of-item-list

;; ;; M-x org-beginning-of-item-list RET
;; (defun outshine-beginning-of-item-list(&optional arg)
;;   "Call outorg to trigger `org-beginning-of-item-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beginning-of-item-list nil arg))

;;;;; TODO org-beginning-of-line

;; ;; C-a (org-beginning-of-line)
;; (defun outshine-beginning-of-line(&optional arg)
;;   "Call outorg to trigger `org-beginning-of-line'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-beginning-of-line nil arg))

;;;;; TODO org-bibtex

;; ;; M-x org-bibtex RET
;; (defun outshine-bibtex(&optional arg)
;;   "Call outorg to trigger `org-bibtex'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex nil arg))

;;;;; TODO org-bibtex-check

;; ;; M-x org-bibtex-check RET
;; (defun outshine-bibtex-check(&optional arg)
;;   "Call outorg to trigger `org-bibtex-check'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-check nil arg))

;;;;; TODO org-bibtex-check-all

;; ;; M-x org-bibtex-check-all RET
;; (defun outshine-bibtex-check-all(&optional arg)
;;   "Call outorg to trigger `org-bibtex-check-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-check-all nil arg))

;;;;; TODO org-bibtex-create

;; ;; M-x org-bibtex-create RET
;; (defun outshine-bibtex-create(&optional arg)
;;   "Call outorg to trigger `org-bibtex-create'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-create nil arg))

;;;;; TODO org-bibtex-create-in-current-entry

;; ;; M-x org-bibtex-create-in-current-entry RET
;; (defun outshine-bibtex-create-in-current-entry(&optional arg)
;;   "Call outorg to trigger `org-bibtex-create-in-current-entry'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-create-in-current-entry nil arg))

;;;;; TODO org-bibtex-export-to-kill-ring

;; ;; M-x org-bibtex-export-to-kill-ring RET
;; (defun outshine-bibtex-export-to-kill-ring(&optional arg)
;;   "Call outorg to trigger `org-bibtex-export-to-kill-ring'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-export-to-kill-ring nil arg))

;;;;; TODO org-bibtex-import-from-file

;; ;; M-x org-bibtex-import-from-file RET
;; (defun outshine-bibtex-import-from-file(&optional arg)
;;   "Call outorg to trigger `org-bibtex-import-from-file'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-import-from-file nil arg))

;;;;; TODO org-bibtex-read

;; ;; M-x org-bibtex-read RET
;; (defun outshine-bibtex-read(&optional arg)
;;   "Call outorg to trigger `org-bibtex-read'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-read nil arg))

;;;;; TODO org-bibtex-read-buffer

;; ;; M-x org-bibtex-read-buffer RET
;; (defun outshine-bibtex-read-buffer(&optional arg)
;;   "Call outorg to trigger `org-bibtex-read-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-read-buffer nil arg))

;;;;; TODO org-bibtex-read-file

;; ;; M-x org-bibtex-read-file RET
;; (defun outshine-bibtex-read-file(&optional arg)
;;   "Call outorg to trigger `org-bibtex-read-file'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-read-file nil arg))

;;;;; TODO org-bibtex-search

;; ;; M-x org-bibtex-search RET
;; (defun outshine-bibtex-search(&optional arg)
;;   "Call outorg to trigger `org-bibtex-search'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-search nil arg))

;;;;; TODO org-bibtex-write

;; ;; M-x org-bibtex-write RET
;; (defun outshine-bibtex-write(&optional arg)
;;   "Call outorg to trigger `org-bibtex-write'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-write nil arg))

;;;;; TODO org-bibtex-yank

;; ;; M-x org-bibtex-yank RET
;; (defun outshine-bibtex-yank(&optional arg)
;;   "Call outorg to trigger `org-bibtex-yank'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-bibtex-yank nil arg))

;;;;; TODO org-calendar-goto-agenda

;; ;; M-x org-calendar-goto-agenda RET
;; (defun outshine-calendar-goto-agenda(&optional arg)
;;   "Call outorg to trigger `org-calendar-goto-agenda'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-calendar-goto-agenda nil arg))

;;;;; TODO org-calendar-select

;; ;; M-x org-calendar-select RET
;; (defun outshine-calendar-select(&optional arg)
;;   "Call outorg to trigger `org-calendar-select'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-calendar-select nil arg))

;;;;; TODO org-calendar-select-mouse

;; ;; M-x org-calendar-select-mouse RET
;; (defun outshine-calendar-select-mouse(&optional arg)
;;   "Call outorg to trigger `org-calendar-select-mouse'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-calendar-select-mouse nil arg))

;;;;; TODO org-cancel-repeater

;; ;; M-x org-cancel-repeater RET
;; (defun outshine-cancel-repeater(&optional arg)
;;   "Call outorg to trigger `org-cancel-repeater'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cancel-repeater nil arg))

;;;;; TODO org-capture

;; ;; C-M-r (org-capture)
;; (defun outshine-capture(&optional arg)
;;   "Call outorg to trigger `org-capture'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-capture nil arg))

;;;;; TODO org-capture-import-remember-templates

;; ;; M-x org-capture-import-remember-templates RET
;; (defun outshine-capture-import-remember-templates(&optional arg)
;;   "Call outorg to trigger `org-capture-import-remember-templates'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-capture-import-remember-templates nil arg))

;;;;; TODO org-capture-string

;; ;; M-x org-capture-string RET
;; (defun outshine-capture-string(&optional arg)
;;   "Call outorg to trigger `org-capture-string'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-capture-string nil arg))

;;;;; TODO org-cdlatex-environment-indent

;; ;; M-x org-cdlatex-environment-indent RET
;; (defun outshine-cdlatex-environment-indent(&optional arg)
;;   "Call outorg to trigger `org-cdlatex-environment-indent'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cdlatex-environment-indent nil arg))

;;;;; TODO org-cdlatex-math-modify

;; ;; <menu-bar> <Org> <LaTeX> <Modify math symbol> (org-cdlatex-math-modify)
;; (defun outshine-cdlatex-math-modify(&optional arg)
;;   "Call outorg to trigger `org-cdlatex-math-modify'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cdlatex-math-modify nil arg))

;;;;; TODO org-cdlatex-mode

;; ;; <menu-bar> <Org> <LaTeX> <Org CDLaTeX mode> (org-cdlatex-mode)
;; (defun outshine-cdlatex-mode(&optional arg)
;;   "Call outorg to trigger `org-cdlatex-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cdlatex-mode nil arg))

;;;;; TODO org-cdlatex-underscore-caret

;; ;; M-x org-cdlatex-underscore-caret RET
;; (defun outshine-cdlatex-underscore-caret(&optional arg)
;;   "Call outorg to trigger `org-cdlatex-underscore-caret'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cdlatex-underscore-caret nil arg))

;;;;; TODO org-change-tag-in-region

;; ;; <menu-bar> <Org> <TAGS and Properties> <Change tag in region> (org-change-tag-in-region)
;; (defun outshine-change-tag-in-region(&optional arg)
;;   "Call outorg to trigger `org-change-tag-in-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-change-tag-in-region nil arg))

;;;;; TODO org-check-after-date

;; ;; M-x org-check-after-date RET
;; (defun outshine-check-after-date(&optional arg)
;;   "Call outorg to trigger `org-check-after-date'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-check-after-date nil arg))

;;;;; TODO org-check-before-date

;; ;; M-x org-check-before-date RET
;; (defun outshine-check-before-date(&optional arg)
;;   "Call outorg to trigger `org-check-before-date'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-check-before-date nil arg))

;;;;; TODO org-check-dates-range

;; ;; M-x org-check-dates-range RET
;; (defun outshine-check-dates-range(&optional arg)
;;   "Call outorg to trigger `org-check-dates-range'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-check-dates-range nil arg))

;;;;; TODO org-check-deadlines

;; ;; <menu-bar> <Org> <Special views current file> <Check Deadlines> (org-check-deadlines)
;; (defun outshine-check-deadlines(&optional arg)
;;   "Call outorg to trigger `org-check-deadlines'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-check-deadlines nil arg))

;;;;; DONE org-clock-cancel
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:51]

;; C-c C-x C-q (org-clock-cancel)
(defun outshine-clock-cancel ()
  "Call outorg to trigger `org-clock-cancel'."
  (interactive)
  (with-current-buffer
      (condition-case err
	  (marker-buffer outshine-use-outorg-last-headline-marker)
	(error "Can't find header with running clock: %s" err))
    (goto-char outshine-use-outorg-last-headline-marker)
    (outshine-use-outorg 'org-clock-cancel)))

;;;;; TODO org-clock-display

;; ;; C-c C-x C-d, <menu-bar> <Org> <Logging work> <Display times> (org-clock-display)
;; (defun outshine-clock-display(&optional arg)
;;   "Call outorg to trigger `org-clock-display'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-clock-display nil arg))

;;;;; DONE org-clock-goto
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:44]

;; C-c C-x C-j (org-clock-goto)
(defun outshine-clock-goto ()
  "Similar semantics to `org-clock-goto'."
  (interactive)
  (switch-to-buffer
   (condition-case err
       (marker-buffer outshine-use-outorg-last-headline-marker)
     (error "Can't find header with running clock: %s" err)))
   (goto-char outshine-use-outorg-last-headline-marker))

;;;;; DONE org-clock-in
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:43]

;; C-c C-x TAB (org-clock-in)
(defun outshine-clock-in ()
  "Call outorg to trigger `org-clock-in'."
  (interactive)
  (outshine-use-outorg
   (lambda ()
     (interactive)
     (org-clock-in)
     (remove-hook 'kill-buffer-hook 'org-check-running-clock))))

;;;;; TODO org-clock-in-last

;; ;; C-c C-x C-x (org-clock-in-last)
;; (defun outshine-clock-in-last(&optional arg)
;;   "Call outorg to trigger `org-clock-in-last'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-clock-in-last nil arg))

;;;;; DONE org-clock-out
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:49]

;; C-c C-x C-o (org-clock-out)
(defun outshine-clock-out ()
  "Call outorg to trigger `org-clock-out'."
  (interactive)
  (with-current-buffer
      (condition-case err
	  (marker-buffer outshine-use-outorg-last-headline-marker)
	(error "Can't find header with running clock: %s" err))
    (goto-char outshine-use-outorg-last-headline-marker)
    (outshine-use-outorg 'org-clock-out)))

;;;;; TODO org-clock-remove-overlays

;; ;; M-x org-clock-remove-overlays RET
;; (defun outshine-clock-remove-overlays(&optional arg)
;;   "Call outorg to trigger `org-clock-remove-overlays'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-clock-remove-overlays nil arg))

;;;;; DONE org-clock-report
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:52]

;; C-c C-x C-r (org-clock-report)
(defun outshine-clock-report (&optional arg)
  "Call outorg to trigger `org-clock-report'."
  (interactive)
  (outshine-use-outorg 'org-clock-report 'WHOLE-BUFFER-P arg))

;;;;; TODO org-clock-update-time-maybe

;; ;; M-x org-clock-update-time-maybe RET
;; (defun outshine-clock-update-time-maybe(&optional arg)
;;   "Call outorg to trigger `org-clock-update-time-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-clock-update-time-maybe nil arg))

;;;;; TODO org-clone-subtree-with-time-shift

;; ;; C-c C-x c, <menu-bar> <Org> <Edit Structure> <Clone subtree, shift time> (org-clone-subtree-with-time-shift)
;; (defun outshine-clone-subtree-with-time-shift(&optional arg)
;;   "Call outorg to trigger `org-clone-subtree-with-time-shift'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-clone-subtree-with-time-shift nil arg))

;;;;; TODO org-columns

;; ;; C-c C-x C-c, <menu-bar> <Org> <TAGS and Properties> <Column view of properties> (org-columns)
;; (defun outshine-columns(&optional arg)
;;   "Call outorg to trigger `org-columns'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-columns nil arg))

;;;;; TODO org-columns-compute

;; ;; M-x org-columns-compute RET
;; (defun outshine-columns-compute(&optional arg)
;;   "Call outorg to trigger `org-columns-compute'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-columns-compute nil arg))

;;;;; TODO org-columns-remove-overlays

;; ;; M-x org-columns-remove-overlays RET
;; (defun outshine-columns-remove-overlays(&optional arg)
;;   "Call outorg to trigger `org-columns-remove-overlays'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-columns-remove-overlays nil arg))

;;;;; TODO org-comment-dwim

;; ;; M-; (org-comment-dwim)
;; (defun outshine-comment-dwim(&optional arg)
;;   "Call outorg to trigger `org-comment-dwim'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-comment-dwim nil arg))

;;;;; TODO org-compute-property-at-point

;; ;; M-x org-compute-property-at-point RET
;; (defun outshine-compute-property-at-point(&optional arg)
;;   "Call outorg to trigger `org-compute-property-at-point'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-compute-property-at-point nil arg))

;;;;; TODO org-content

;; ;; M-x org-content RET
;; (defun outshine-content(&optional arg)
;;   "Call outorg to trigger `org-content'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-content nil arg))

;;;;; TODO org-convert-to-odd-levels

;; ;; <menu-bar> <Org> <Edit Structure> <Convert to odd levels> (org-convert-to-odd-levels)
;; (defun outshine-convert-to-odd-levels(&optional arg)
;;   "Call outorg to trigger `org-convert-to-odd-levels'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-convert-to-odd-levels nil arg))

;;;;; TODO org-convert-to-oddeven-levels

;; ;; <menu-bar> <Org> <Edit Structure> <Convert to odd/even levels> (org-convert-to-oddeven-levels)
;; (defun outshine-convert-to-oddeven-levels(&optional arg)
;;   "Call outorg to trigger `org-convert-to-oddeven-levels'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-convert-to-oddeven-levels nil arg))

;;;;; TODO org-copy

;; ;; C-c M-w (org-copy)
;; (defun outshine-copy(&optional arg)
;;   "Call outorg to trigger `org-copy'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-copy nil arg))

;;;;; TODO org-copy-special

;; ;; <menu-bar> <Org> <Edit Structure> <Copy Subtree>, <menu-bar> <Tbl> <Rectangle> <Copy Rectangle>, C-c C-x M-w (org-copy-special)
;; (defun outshine-copy-special(&optional arg)
;;   "Call outorg to trigger `org-copy-special'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-copy-special nil arg))

;;;;; TODO org-copy-subtree

;; ;; M-x org-copy-subtree RET
;; (defun outshine-copy-subtree(&optional arg)
;;   "Call outorg to trigger `org-copy-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-copy-subtree nil arg))

;;;;; TODO org-copy-visible

;; ;; C-c C-x v, <menu-bar> <Org> <Edit Structure> <Copy visible text> (org-copy-visible)
;; (defun outshine-copy-visible(&optional arg)
;;   "Call outorg to trigger `org-copy-visible'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-copy-visible nil arg))

;;;;; TODO org-create-customize-menu

;; ;; <menu-bar> <Org> <Customize> <Expand This Menu> (org-create-customize-menu)
;; (defun outshine-create-customize-menu(&optional arg)
;;   "Call outorg to trigger `org-create-customize-menu'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-create-customize-menu nil arg))

;;;;; TODO org-create-math-formula

;; ;; M-x org-create-math-formula RET
;; (defun outshine-create-math-formula(&optional arg)
;;   "Call outorg to trigger `org-create-math-formula'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-create-math-formula nil arg))

;;;;; TODO org-ctrl-c-ctrl-c

;; ;; C-c C-c, <menu-bar> <Tbl> <Align> (org-ctrl-c-ctrl-c)
;; (defun outshine-ctrl-c-ctrl-c(&optional arg)
;;   "Call outorg to trigger `org-ctrl-c-ctrl-c'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ctrl-c-ctrl-c nil arg))

;;;;; TODO org-ctrl-c-minus

;; ;; C-c -, <menu-bar> <Tbl> <Row> <Insert Hline> (org-ctrl-c-minus)
;; (defun outshine-ctrl-c-minus(&optional arg)
;;   "Call outorg to trigger `org-ctrl-c-minus'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ctrl-c-minus nil arg))

;;;;; TODO org-ctrl-c-ret

;; ;; C-c RET (org-ctrl-c-ret)
;; (defun outshine-ctrl-c-ret(&optional arg)
;;   "Call outorg to trigger `org-ctrl-c-ret'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ctrl-c-ret nil arg))

;;;;; TODO org-ctrl-c-star

;; ;; C-c * (org-ctrl-c-star)
;; (defun outshine-ctrl-c-star(&optional arg)
;;   "Call outorg to trigger `org-ctrl-c-star'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ctrl-c-star nil arg))

;;;;; TODO org-customize

;; ;; <menu-bar> <Org> <Customize> <Browse Org Group> (org-customize)
;; (defun outshine-customize(&optional arg)
;;   "Call outorg to trigger `org-customize'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-customize nil arg))

;;;;; TODO org-cut-special

;; ;; C-c C-x C-w, <menu-bar> <Org> <Edit Structure> <Cut Subtree>, <menu-bar> <Tbl> <Rectangle> <Cut Rectangle> (org-cut-special)
;; (defun outshine-cut-special(&optional arg)
;;   "Call outorg to trigger `org-cut-special'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cut-special nil arg))

;;;;; TODO org-cut-subtree

;; ;; M-x org-cut-subtree RET
;; (defun outshine-cut-subtree(&optional arg)
;;   "Call outorg to trigger `org-cut-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cut-subtree nil arg))

;;;;; TODO org-cycle

;; ;; <tab>, TAB, <menu-bar> <Tbl> <Next Field>, <menu-bar> <Org> <Show/Hide> <Cycle Visibility> (org-cycle)
;; (defun outshine-cycle(&optional arg)
;;   "Call outorg to trigger `org-cycle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cycle nil arg))

;;;;; TODO org-cycle-agenda-files

;; ;; C-', C-,, <menu-bar> <Org> <File List for Agenda> <Cycle through agenda files> (org-cycle-agenda-files)
;; (defun outshine-cycle-agenda-files(&optional arg)
;;   "Call outorg to trigger `org-cycle-agenda-files'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cycle-agenda-files nil arg))

;;;;; TODO org-cycle-global

;; ;; M-x org-cycle-global RET
;; (defun outshine-cycle-global(&optional arg)
;;   "Call outorg to trigger `org-cycle-global'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cycle-global nil arg))

;;;;; TODO org-cycle-level

;; ;; M-x org-cycle-level RET
;; (defun outshine-cycle-level(&optional arg)
;;   "Call outorg to trigger `org-cycle-level'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cycle-level nil arg))

;;;;; TODO org-cycle-list-bullet

;; ;; M-x org-cycle-list-bullet RET
;; (defun outshine-cycle-list-bullet(&optional arg)
;;   "Call outorg to trigger `org-cycle-list-bullet'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cycle-list-bullet nil arg))

;;;;; TODO org-cycle-local

;; ;; M-x org-cycle-local RET
;; (defun outshine-cycle-local(&optional arg)
;;   "Call outorg to trigger `org-cycle-local'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-cycle-local nil arg))

;;;;; TODO org-date-from-calendar

;; ;; C-c <, <menu-bar> <Org> <Dates and Scheduling> <Date from Calendar> (org-date-from-calendar)
;; (defun outshine-date-from-calendar(&optional arg)
;;   "Call outorg to trigger `org-date-from-calendar'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-date-from-calendar nil arg))

;;;;; TODO org-dblock-update

;; ;; C-c C-x C-u (org-dblock-update)
;; (defun outshine-dblock-update(&optional arg)
;;   "Call outorg to trigger `org-dblock-update'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-dblock-update nil arg))

;;;;; DONE org-deadline
;;     - State "DONE"       from "TODO"       [2016-02-07 So 18:19]

;; C-c C-d (org-deadline)
(defun outshine-deadline (&optional arg)
  "Call outorg to trigger `org-deadline'."
  (interactive "P")
  (outshine-use-outorg
   (lambda ()
     (interactive)
     (let ((current-prefix-arg arg))
       (call-interactively 'org-deadline)))))

;;;;; TODO org-decrease-number-at-point

;; ;; <C-M-S-left> (org-decrease-number-at-point)
;; (defun outshine-decrease-number-at-point(&optional arg)
;;   "Call outorg to trigger `org-decrease-number-at-point'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-decrease-number-at-point nil arg))

;;;;; TODO org-delete-backward-char

;; ;; DEL (org-delete-backward-char)
;; (defun outshine-delete-backward-char(&optional arg)
;;   "Call outorg to trigger `org-delete-backward-char'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-delete-backward-char nil arg))

;;;;; TODO org-delete-char

;; ;; C-d (org-delete-char)
;; (defun outshine-delete-char(&optional arg)
;;   "Call outorg to trigger `org-delete-char'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-delete-char nil arg))

;;;;; TODO org-delete-indentation

;; ;; M-^ (org-delete-indentation)
;; (defun outshine-delete-indentation(&optional arg)
;;   "Call outorg to trigger `org-delete-indentation'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-delete-indentation nil arg))

;;;;; TODO org-delete-property

;; ;; M-x org-delete-property RET
;; (defun outshine-delete-property(&optional arg)
;;   "Call outorg to trigger `org-delete-property'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-delete-property nil arg))

;;;;; TODO org-delete-property-globally

;; ;; M-x org-delete-property-globally RET
;; (defun outshine-delete-property-globally(&optional arg)
;;   "Call outorg to trigger `org-delete-property-globally'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-delete-property-globally nil arg))

;;;;; TODO org-demote-subtree

;; ;; C-c C-> (org-demote-subtree)
;; (defun outshine-demote-subtree(&optional arg)
;;   "Call outorg to trigger `org-demote-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-demote-subtree nil arg))

;;;;; TODO org-display-inline-images

;; ;; M-x org-display-inline-images RET
;; (defun outshine-display-inline-images(&optional arg)
;;   "Call outorg to trigger `org-display-inline-images'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-display-inline-images nil arg))

;;;;; TODO org-display-outline-path

;; ;; M-x org-display-outline-path RET
;; (defun outshine-display-outline-path(&optional arg)
;;   "Call outorg to trigger `org-display-outline-path'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-display-outline-path nil arg))

;;;;; TODO org-do-demote

;; ;; M-x org-do-demote RET
;; (defun outshine-do-demote(&optional arg)
;;   "Call outorg to trigger `org-do-demote'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-do-demote nil arg))

;;;;; TODO org-do-promote

;; ;; M-x org-do-promote RET
;; (defun outshine-do-promote(&optional arg)
;;   "Call outorg to trigger `org-do-promote'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-do-promote nil arg))

;;;;; TODO org-down-element

;; ;; C-c C-_ (org-down-element)
;; (defun outshine-down-element(&optional arg)
;;   "Call outorg to trigger `org-down-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-down-element nil arg))

;;;;; TODO org-dp-prompt-all

;; ;; M-x org-dp-prompt-all RET
;; (defun outshine-dp-prompt-all(&optional arg)
;;   "Call outorg to trigger `org-dp-prompt-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-dp-prompt-all nil arg))

;;;;; TODO org-dp-prompt-for-src-block-props

;; ;; M-x org-dp-prompt-for-src-block-props RET
;; (defun outshine-dp-prompt-for-src-block-props(&optional arg)
;;   "Call outorg to trigger `org-dp-prompt-for-src-block-props'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-dp-prompt-for-src-block-props nil arg))

;;;;; TODO org-dp-toggle-headers

;; ;; M-x org-dp-toggle-headers RET
;; (defun outshine-dp-toggle-headers(&optional arg)
;;   "Call outorg to trigger `org-dp-toggle-headers'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-dp-toggle-headers nil arg))

;;;;; TODO org-dp-wrap-in-block

;; ;; C-c w w (org-dp-wrap-in-block)
;; (defun outshine-dp-wrap-in-block(&optional arg)
;;   "Call outorg to trigger `org-dp-wrap-in-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-dp-wrap-in-block nil arg))

;;;;; TODO org-drag-element-backward

;; ;; M-x org-drag-element-backward RET
;; (defun outshine-drag-element-backward(&optional arg)
;;   "Call outorg to trigger `org-drag-element-backward'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-drag-element-backward nil arg))

;;;;; TODO org-drag-element-forward

;; ;; M-x org-drag-element-forward RET
;; (defun outshine-drag-element-forward(&optional arg)
;;   "Call outorg to trigger `org-drag-element-forward'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-drag-element-forward nil arg))

;;;;; TODO org-drag-line-backward

;; ;; M-x org-drag-line-backward RET
;; (defun outshine-drag-line-backward(&optional arg)
;;   "Call outorg to trigger `org-drag-line-backward'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-drag-line-backward nil arg))

;;;;; TODO org-drag-line-forward

;; ;; M-x org-drag-line-forward RET
;; (defun outshine-drag-line-forward(&optional arg)
;;   "Call outorg to trigger `org-drag-line-forward'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-drag-line-forward nil arg))

;;;;; TODO org-edit-agenda-file-list

;; ;; M-x org-edit-agenda-file-list RET
;; (defun outshine-edit-agenda-file-list(&optional arg)
;;   "Call outorg to trigger `org-edit-agenda-file-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-agenda-file-list nil arg))

;;;;; TODO org-edit-export-block

;; ;; M-x org-edit-export-block RET
;; (defun outshine-edit-export-block(&optional arg)
;;   "Call outorg to trigger `org-edit-export-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-export-block nil arg))

;;;;; TODO org-edit-fixed-width-region

;; ;; M-x org-edit-fixed-width-region RET
;; (defun outshine-edit-fixed-width-region(&optional arg)
;;   "Call outorg to trigger `org-edit-fixed-width-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-fixed-width-region nil arg))

;;;;; TODO org-edit-footnote-reference

;; ;; M-x org-edit-footnote-reference RET
;; (defun outshine-edit-footnote-reference(&optional arg)
;;   "Call outorg to trigger `org-edit-footnote-reference'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-footnote-reference nil arg))

;;;;; TODO org-edit-inline-src-code

;; ;; M-x org-edit-inline-src-code RET
;; (defun outshine-edit-inline-src-code(&optional arg)
;;   "Call outorg to trigger `org-edit-inline-src-code'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-inline-src-code nil arg))

;;;;; TODO org-edit-special

;; ;; C-c ', <menu-bar> <Org> <Editing> <Edit Source Example>, <menu-bar> <Tbl> <Calculate> <Edit Formulas> (org-edit-special)
;; (defun outshine-edit-special(&optional arg)
;;   "Call outorg to trigger `org-edit-special'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-special nil arg))

;;;;; TODO org-edit-src-abort

;; ;; M-x org-edit-src-abort RET
;; (defun outshine-edit-src-abort(&optional arg)
;;   "Call outorg to trigger `org-edit-src-abort'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-src-abort nil arg))

;;;;; TODO org-edit-src-code

;; ;; M-x org-edit-src-code RET
;; (defun outshine-edit-src-code(&optional arg)
;;   "Call outorg to trigger `org-edit-src-code'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-src-code nil arg))

;;;;; TODO org-edit-src-continue

;; ;; M-x org-edit-src-continue RET
;; (defun outshine-edit-src-continue(&optional arg)
;;   "Call outorg to trigger `org-edit-src-continue'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-src-continue nil arg))

;;;;; TODO org-edit-src-exit

;; ;; M-x org-edit-src-exit RET
;; (defun outshine-edit-src-exit(&optional arg)
;;   "Call outorg to trigger `org-edit-src-exit'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-src-exit nil arg))

;;;;; TODO org-edit-src-save

;; ;; M-x org-edit-src-save RET
;; (defun outshine-edit-src-save(&optional arg)
;;   "Call outorg to trigger `org-edit-src-save'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-src-save nil arg))

;;;;; TODO org-edit-table.el

;; ;; M-x org-edit-table.el RET
;; (defun outshine-edit-table.el(&optional arg)
;;   "Call outorg to trigger `org-edit-table.el'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-edit-table.el nil arg))

;;;;; TODO org-element-cache-reset

;; ;; M-x org-element-cache-reset RET
;; (defun outshine-element-cache-reset(&optional arg)
;;   "Call outorg to trigger `org-element-cache-reset'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-element-cache-reset nil arg))

;;;;; TODO org-element-update-syntax

;; ;; M-x org-element-update-syntax RET
;; (defun outshine-element-update-syntax(&optional arg)
;;   "Call outorg to trigger `org-element-update-syntax'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-element-update-syntax nil arg))

;;;;; TODO org-emphasize

;; ;; C-c C-x C-f, <menu-bar> <Org> <Editing> <Emphasis...>, C-c M-# M-f (org-emphasize)
;; (defun outshine-emphasize(&optional arg)
;;   "Call outorg to trigger `org-emphasize'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-emphasize nil arg))

;;;;; TODO org-end-of-item

;; ;; M-x org-end-of-item RET
;; (defun outshine-end-of-item(&optional arg)
;;   "Call outorg to trigger `org-end-of-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-end-of-item nil arg))

;;;;; TODO org-end-of-item-list

;; ;; M-x org-end-of-item-list RET
;; (defun outshine-end-of-item-list(&optional arg)
;;   "Call outorg to trigger `org-end-of-item-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-end-of-item-list nil arg))

;;;;; TODO org-end-of-line

;; ;; C-e (org-end-of-line)
;; (defun outshine-end-of-line(&optional arg)
;;   "Call outorg to trigger `org-end-of-line'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-end-of-line nil arg))

;;;;; TODO org-entities-create-table

;; ;; M-x org-entities-create-table RET
;; (defun outshine-entities-create-table(&optional arg)
;;   "Call outorg to trigger `org-entities-create-table'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-entities-create-table nil arg))

;;;;; TODO org-entities-help

;; ;; M-x org-entities-help RET
;; (defun outshine-entities-help(&optional arg)
;;   "Call outorg to trigger `org-entities-help'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-entities-help nil arg))

;;;;; TODO org-escape-code-in-region

;; ;; M-x org-escape-code-in-region RET
;; (defun outshine-escape-code-in-region(&optional arg)
;;   "Call outorg to trigger `org-escape-code-in-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-escape-code-in-region nil arg))

;;;;; TODO org-evaluate-time-range

;; ;; C-c C-y, <menu-bar> <Org> <Dates and Scheduling> <Compute Time Range> (org-evaluate-time-range)
;; (defun outshine-evaluate-time-range(&optional arg)
;;   "Call outorg to trigger `org-evaluate-time-range'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-evaluate-time-range nil arg))

;;;;; DONE org-export-dispatch
;;     - State "DONE"       from "TODO"       [2016-02-07 So 18:38]

;; C-c C-e (org-export-dispatch)
(defun outshine-export-dispatch (&optional arg)
  "Call outorg to trigger `org-export-dispatch'."
  (interactive "P")
  (outshine-use-outorg 'org-export-dispatch
		       (y-or-n-p "Use whole buffer ")
		       arg))

;;;;; TODO org-export-insert-default-template

;; ;; M-x org-export-insert-default-template RET
;; (defun outshine-export-insert-default-template(&optional arg)
;;   "Call outorg to trigger `org-export-insert-default-template'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-insert-default-template nil arg))

;;;;; TODO org-export-stack

;; ;; M-x org-export-stack RET
;; (defun outshine-export-stack(&optional arg)
;;   "Call outorg to trigger `org-export-stack'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-stack nil arg))

;;;;; TODO org-export-stack-clear

;; ;; M-x org-export-stack-clear RET
;; (defun outshine-export-stack-clear(&optional arg)
;;   "Call outorg to trigger `org-export-stack-clear'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-stack-clear nil arg))

;;;;; TODO org-export-stack-mode

;; ;; M-x org-export-stack-mode RET
;; (defun outshine-export-stack-mode(&optional arg)
;;   "Call outorg to trigger `org-export-stack-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-stack-mode nil arg))

;;;;; TODO org-export-stack-remove

;; ;; M-x org-export-stack-remove RET
;; (defun outshine-export-stack-remove(&optional arg)
;;   "Call outorg to trigger `org-export-stack-remove'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-stack-remove nil arg))

;;;;; TODO org-export-stack-view

;; ;; M-x org-export-stack-view RET
;; (defun outshine-export-stack-view(&optional arg)
;;   "Call outorg to trigger `org-export-stack-view'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-stack-view nil arg))

;;;;; TODO org-feed-goto-inbox

;; ;; C-c C-x G, <menu-bar> <Org> <TODO Lists> <Go to the inbox of a feed...> (org-feed-goto-inbox)
;; (defun outshine-feed-goto-inbox(&optional arg)
;;   "Call outorg to trigger `org-feed-goto-inbox'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-feed-goto-inbox nil arg))

;;;;; TODO org-feed-show-raw-feed

;; ;; M-x org-feed-show-raw-feed RET
;; (defun outshine-feed-show-raw-feed(&optional arg)
;;   "Call outorg to trigger `org-feed-show-raw-feed'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-feed-show-raw-feed nil arg))

;;;;; TODO org-feed-update

;; ;; M-x org-feed-update RET
;; (defun outshine-feed-update(&optional arg)
;;   "Call outorg to trigger `org-feed-update'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-feed-update nil arg))

;;;;; TODO org-feed-update-all

;; ;; C-c C-x g, <menu-bar> <Org> <TODO Lists> <Get news from all feeds> (org-feed-update-all)
;; (defun outshine-feed-update-all(&optional arg)
;;   "Call outorg to trigger `org-feed-update-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-feed-update-all nil arg))

;;;;; TODO org-fill-paragraph

;; ;; M-x org-fill-paragraph RET
;; (defun outshine-fill-paragraph(&optional arg)
;;   "Call outorg to trigger `org-fill-paragraph'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-fill-paragraph nil arg))

;;;;; TODO org-find-entry-with-id

;; ;; M-x org-find-entry-with-id RET
;; (defun outshine-find-entry-with-id(&optional arg)
;;   "Call outorg to trigger `org-find-entry-with-id'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-find-entry-with-id nil arg))

;;;;; TODO org-find-file-at-mouse

;; ;; M-x org-find-file-at-mouse RET
;; (defun outshine-find-file-at-mouse(&optional arg)
;;   "Call outorg to trigger `org-find-file-at-mouse'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-find-file-at-mouse nil arg))

;;;;; TODO org-first-sibling-p

;; ;; M-x org-first-sibling-p RET
;; (defun outshine-first-sibling-p(&optional arg)
;;   "Call outorg to trigger `org-first-sibling-p'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-first-sibling-p nil arg))

;;;;; DONE org-footnote-action
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:12]

;; C-c C-x f (org-footnote-action)
(defun outshine-footnote-action (&optional special)
  "Call outorg to trigger `org-footnote-action'."
  (interactive "P")
  (outshine-use-outorg
   'org-footnote-action 'WHOLE-BUFFER-P special))

;;;;; TODO org-footnote-goto-definition

;; ;; M-x org-footnote-goto-definition RET
;; (defun outshine-footnote-goto-definition(&optional arg)
;;   "Call outorg to trigger `org-footnote-goto-definition'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-footnote-goto-definition nil arg))

;;;;; TODO org-footnote-goto-previous-reference

;; ;; M-x org-footnote-goto-previous-reference RET
;; (defun outshine-footnote-goto-previous-reference(&optional arg)
;;   "Call outorg to trigger `org-footnote-goto-previous-reference'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-footnote-goto-previous-reference nil arg))

;;;;; TODO org-footnote-new

;; ;; M-x org-footnote-new RET
;; (defun outshine-footnote-new(&optional arg)
;;   "Call outorg to trigger `org-footnote-new'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-footnote-new nil arg))

;;;;; TODO org-footnote-normalize

;; ;; M-x org-footnote-normalize RET
;; (defun outshine-footnote-normalize(&optional arg)
;;   "Call outorg to trigger `org-footnote-normalize'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-footnote-normalize nil arg))

;;;;; TODO org-footnote-renumber-fn:N

;; ;; M-x org-footnote-renumber-fn:N RET
;; (defun outshine-footnote-renumber-fn:N(&optional arg)
;;   "Call outorg to trigger `org-footnote-renumber-fn:N'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-footnote-renumber-fn:N nil arg))

;;;;; TODO org-force-cycle-archived

;; ;; <C-tab> (org-force-cycle-archived)
;; (defun outshine-force-cycle-archived(&optional arg)
;;   "Call outorg to trigger `org-force-cycle-archived'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-force-cycle-archived nil arg))

;;;;; TODO org-force-self-insert

;; ;; | (org-force-self-insert)
;; (defun outshine-force-self-insert(&optional arg)
;;   "Call outorg to trigger `org-force-self-insert'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-force-self-insert nil arg))

;;;;; TODO org-forward-element

;; ;; M-} (org-forward-element)
;; (defun outshine-forward-element(&optional arg)
;;   "Call outorg to trigger `org-forward-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-forward-element nil arg))

;;;;; TODO org-forward-heading-same-level

;; ;; C-c C-f, <menu-bar> <Org> <Navigate Headings> <Next Same Level> (org-forward-heading-same-level)
;; (defun outshine-forward-heading-same-level(&optional arg)
;;   "Call outorg to trigger `org-forward-heading-same-level'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-forward-heading-same-level nil arg))

;;;;; TODO org-forward-paragraph

;; ;; <C-down> (org-forward-paragraph)
;; (defun outshine-forward-paragraph(&optional arg)
;;   "Call outorg to trigger `org-forward-paragraph'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-forward-paragraph nil arg))

;;;;; TODO org-forward-sentence

;; ;; M-e (org-forward-sentence)
;; (defun outshine-forward-sentence(&optional arg)
;;   "Call outorg to trigger `org-forward-sentence'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-forward-sentence nil arg))

;;;;; TODO org-get-tags-at

;; ;; M-x org-get-tags-at RET
;; (defun outshine-get-tags-at(&optional arg)
;;   "Call outorg to trigger `org-get-tags-at'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-get-tags-at nil arg))

;;;;; TODO org-gfm-convert-region-to-md

;; ;; M-x org-gfm-convert-region-to-md RET
;; (defun outshine-gfm-convert-region-to-md(&optional arg)
;;   "Call outorg to trigger `org-gfm-convert-region-to-md'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-gfm-convert-region-to-md nil arg))

;;;;; TODO org-gfm-export-as-markdown

;; ;; M-x org-gfm-export-as-markdown RET
;; (defun outshine-gfm-export-as-markdown(&optional arg)
;;   "Call outorg to trigger `org-gfm-export-as-markdown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-gfm-export-as-markdown nil arg))

;;;;; TODO org-gfm-export-to-markdown

;; ;; M-x org-gfm-export-to-markdown RET
;; (defun outshine-gfm-export-to-markdown(&optional arg)
;;   "Call outorg to trigger `org-gfm-export-to-markdown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-gfm-export-to-markdown nil arg))

;;;;; TODO org-global-cycle

;; ;; M-x org-global-cycle RET
;; (defun outshine-global-cycle(&optional arg)
;;   "Call outorg to trigger `org-global-cycle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-global-cycle nil arg))

;;;;; TODO org-goto

;; ;; C-c C-j, <menu-bar> <Org> <Navigate Headings> <Jump> (org-goto)
;; (defun outshine-goto(&optional arg)
;;   "Call outorg to trigger `org-goto'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto nil arg))

;;;;; TODO org-goto-calendar

;; ;; C-c >, <menu-bar> <Org> <Dates and Scheduling> <Goto Calendar> (org-goto-calendar)
;; (defun outshine-goto-calendar(&optional arg)
;;   "Call outorg to trigger `org-goto-calendar'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto-calendar nil arg))

;;;;; TODO org-goto-left

;; ;; M-x org-goto-left RET
;; (defun outshine-goto-left(&optional arg)
;;   "Call outorg to trigger `org-goto-left'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto-left nil arg))

;;;;; TODO org-goto-local-auto-isearch

;; ;; M-x org-goto-local-auto-isearch RET
;; (defun outshine-goto-local-auto-isearch(&optional arg)
;;   "Call outorg to trigger `org-goto-local-auto-isearch'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto-local-auto-isearch nil arg))

;;;;; TODO org-goto-quit

;; ;; M-x org-goto-quit RET
;; (defun outshine-goto-quit(&optional arg)
;;   "Call outorg to trigger `org-goto-quit'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto-quit nil arg))

;;;;; TODO org-goto-ret

;; ;; M-x org-goto-ret RET
;; (defun outshine-goto-ret(&optional arg)
;;   "Call outorg to trigger `org-goto-ret'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto-ret nil arg))

;;;;; TODO org-goto-right

;; ;; M-x org-goto-right RET
;; (defun outshine-goto-right(&optional arg)
;;   "Call outorg to trigger `org-goto-right'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-goto-right nil arg))

;;;;; TODO org-hide-block-all

;; ;; M-x org-hide-block-all RET
;; (defun outshine-hide-block-all(&optional arg)
;;   "Call outorg to trigger `org-hide-block-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-hide-block-all nil arg))

;;;;; TODO org-hide-block-toggle

;; ;; M-x org-hide-block-toggle RET
;; (defun outshine-hide-block-toggle(&optional arg)
;;   "Call outorg to trigger `org-hide-block-toggle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-hide-block-toggle nil arg))

;;;;; TODO org-hide-block-toggle-maybe

;; ;; M-x org-hide-block-toggle-maybe RET
;; (defun outshine-hide-block-toggle-maybe(&optional arg)
;;   "Call outorg to trigger `org-hide-block-toggle-maybe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-hide-block-toggle-maybe nil arg))

;;;;; TODO org-html-convert-region-to-html

;; ;; M-x org-html-convert-region-to-html RET
;; (defun outshine-html-convert-region-to-html(&optional arg)
;;   "Call outorg to trigger `org-html-convert-region-to-html'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-html-convert-region-to-html nil arg))

;;;;; TODO org-html-export-as-html

;; ;; M-x org-html-export-as-html RET
;; (defun outshine-html-export-as-html(&optional arg)
;;   "Call outorg to trigger `org-html-export-as-html'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-html-export-as-html nil arg))

;;;;; TODO org-html-export-to-html

;; ;; M-x org-html-export-to-html RET
;; (defun outshine-html-export-to-html(&optional arg)
;;   "Call outorg to trigger `org-html-export-to-html'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-html-export-to-html nil arg))

;;;;; TODO org-html-htmlize-generate-css

;; ;; M-x org-html-htmlize-generate-css RET
;; (defun outshine-html-htmlize-generate-css(&optional arg)
;;   "Call outorg to trigger `org-html-htmlize-generate-css'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-html-htmlize-generate-css nil arg))

;;;;; TODO org-icalendar-combine-agenda-files

;; ;; M-x org-icalendar-combine-agenda-files RET
;; (defun outshine-icalendar-combine-agenda-files(&optional arg)
;;   "Call outorg to trigger `org-icalendar-combine-agenda-files'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-icalendar-combine-agenda-files nil arg))

;;;;; TODO org-icalendar-export-agenda-files

;; ;; M-x org-icalendar-export-agenda-files RET
;; (defun outshine-icalendar-export-agenda-files(&optional arg)
;;   "Call outorg to trigger `org-icalendar-export-agenda-files'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-icalendar-export-agenda-files nil arg))

;;;;; TODO org-icalendar-export-to-ics

;; ;; M-x org-icalendar-export-to-ics RET
;; (defun outshine-icalendar-export-to-ics(&optional arg)
;;   "Call outorg to trigger `org-icalendar-export-to-ics'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-icalendar-export-to-ics nil arg))

;;;;; TODO org-id-copy

;; ;; M-x org-id-copy RET
;; (defun outshine-id-copy(&optional arg)
;;   "Call outorg to trigger `org-id-copy'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-id-copy nil arg))

;;;;; TODO org-id-get-create

;; ;; M-x org-id-get-create RET
;; (defun outshine-id-get-create(&optional arg)
;;   "Call outorg to trigger `org-id-get-create'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-id-get-create nil arg))

;;;;; TODO org-id-goto

;; ;; M-x org-id-goto RET
;; (defun outshine-id-goto(&optional arg)
;;   "Call outorg to trigger `org-id-goto'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-id-goto nil arg))

;;;;; TODO org-id-store-link

;; ;; M-x org-id-store-link RET
;; (defun outshine-id-store-link(&optional arg)
;;   "Call outorg to trigger `org-id-store-link'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-id-store-link nil arg))

;;;;; TODO org-id-update-id-locations

;; ;; M-x org-id-update-id-locations RET
;; (defun outshine-id-update-id-locations(&optional arg)
;;   "Call outorg to trigger `org-id-update-id-locations'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-id-update-id-locations nil arg))

;;;;; TODO org-ido-switchb

;; ;; M-x org-ido-switchb RET;
;; ;;  its alias M-x org-iswitchb RET;
;; ;;  its alias M-x org-switchb RET
;; (defun outshine-ido-switchb(&optional arg)
;;   "Call outorg to trigger `org-ido-switchb'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ido-switchb nil arg))

;;;;; DONE org-inc-effort
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:08]

;; C-c C-x E (org-inc-effort)
(defun outshine-inc-effort ()
  "Call outorg to trigger `org-inc-effort'."
  (interactive)
  (outshine-use-outorg 'org-inc-effort))

;;;;; TODO org-increase-number-at-point

;; ;; <C-M-S-right> (org-increase-number-at-point)
;; (defun outshine-increase-number-at-point(&optional arg)
;;   "Call outorg to trigger `org-increase-number-at-point'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-increase-number-at-point nil arg))

;;;;; TODO org-indent-block

;; ;; M-x org-indent-block RET
;; (defun outshine-indent-block(&optional arg)
;;   "Call outorg to trigger `org-indent-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-block nil arg))

;;;;; TODO org-indent-drawer

;; ;; M-x org-indent-drawer RET
;; (defun outshine-indent-drawer(&optional arg)
;;   "Call outorg to trigger `org-indent-drawer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-drawer nil arg))

;;;;; TODO org-indent-item

;; ;; M-x org-indent-item RET
;; (defun outshine-indent-item(&optional arg)
;;   "Call outorg to trigger `org-indent-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-item nil arg))

;;;;; TODO org-indent-item-tree

;; ;; M-x org-indent-item-tree RET
;; (defun outshine-indent-item-tree(&optional arg)
;;   "Call outorg to trigger `org-indent-item-tree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-item-tree nil arg))

;;;;; TODO org-indent-line

;; ;; M-x org-indent-line RET
;; (defun outshine-indent-line(&optional arg)
;;   "Call outorg to trigger `org-indent-line'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-line nil arg))

;;;;; TODO org-indent-mode

;; ;; M-x org-indent-mode RET
;; (defun outshine-indent-mode(&optional arg)
;;   "Call outorg to trigger `org-indent-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-mode nil arg))

;;;;; TODO org-indent-region

;; ;; M-x org-indent-region RET
;; (defun outshine-indent-region(&optional arg)
;;   "Call outorg to trigger `org-indent-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-indent-region nil arg))

;;;;; TODO org-info

;; ;; <menu-bar> <Org> <Documentation> <Info Documentation> (org-info)
;; (defun outshine-info(&optional arg)
;;   "Call outorg to trigger `org-info'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-info nil arg))

;;;;; TODO org-insert-all-links

;; ;; C-c C-M-l (org-insert-all-links)
;; (defun outshine-insert-all-links(&optional arg)
;;   "Call outorg to trigger `org-insert-all-links'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-all-links nil arg))

;;;;; TODO org-insert-columns-dblock

;; ;; C-c C-x i, <menu-bar> <Org> <TAGS and Properties> <Insert Column View DBlock> (org-insert-columns-dblock)
;; (defun outshine-insert-columns-dblock(&optional arg)
;;   "Call outorg to trigger `org-insert-columns-dblock'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-columns-dblock nil arg))

;;;;; DONE org-insert-drawer
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:11]

;; C-c C-x d (org-insert-drawer)
(defun outshine-insert-drawer ()
  "Call outorg to trigger `org-insert-drawer'."
  (interactive)
  (outshine-use-outorg 'org-insert-drawer))

;;;;; TODO org-insert-heading

;; ;; M-RET, <menu-bar> <Org> <New Heading> (org-insert-heading)
;; (defun outshine-insert-heading(&optional arg)
;;   "Call outorg to trigger `org-insert-heading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-heading nil arg))

;;;;; TODO org-insert-heading-after-current

;; ;; M-x org-insert-heading-after-current RET
;; (defun outshine-insert-heading-after-current(&optional arg)
;;   "Call outorg to trigger `org-insert-heading-after-current'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-heading-after-current nil arg))

;;;;; TODO org-insert-heading-respect-content

;; ;; <C-return> (org-insert-heading-respect-content)
;; (defun outshine-insert-heading-respect-content(&optional arg)
;;   "Call outorg to trigger `org-insert-heading-respect-content'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-heading-respect-content nil arg))

;;;;; DONE org-insert-last-stored-link
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:37]

;; C-c M-l (org-insert-last-stored-link)
(defun outshine-insert-last-stored-link ()
  "Call outorg to trigger `org-insert-last-stored-link'."
  (interactive)
  (outshine-use-outorg 'org-insert-last-stored-link))

;;;;; DONE org-insert-link
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:15]

;; C-c C-l (org-insert-link)
(defun outshine-insert-link ()
  "Call outorg to trigger `org-insert-link'."
  (interactive)
  (outshine-use-outorg 'org-insert-link))

;;;;; TODO org-insert-link-global

;; ;; M-x org-insert-link-global RET
;; (defun outshine-insert-link-global(&optional arg)
;;   "Call outorg to trigger `org-insert-link-global'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-link-global nil arg))

;;;;; TODO org-insert-subheading

;; ;; M-x org-insert-subheading RET
;; (defun outshine-insert-subheading(&optional arg)
;;   "Call outorg to trigger `org-insert-subheading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-subheading nil arg))

;;;;; TODO org-insert-todo-heading

;; ;; <M-S-return>, ESC <S-return>, C-c C-x M (org-insert-todo-heading)
;; (defun outshine-insert-todo-heading(&optional arg)
;;   "Call outorg to trigger `org-insert-todo-heading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-todo-heading nil arg))

;;;;; TODO org-insert-todo-heading-respect-content

;; ;; <C-S-return> (org-insert-todo-heading-respect-content)
;; (defun outshine-insert-todo-heading-respect-content(&optional arg)
;;   "Call outorg to trigger `org-insert-todo-heading-respect-content'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-todo-heading-respect-content nil arg))

;;;;; TODO org-insert-todo-subheading

;; ;; M-x org-insert-todo-subheading RET
;; (defun outshine-insert-todo-subheading(&optional arg)
;;   "Call outorg to trigger `org-insert-todo-subheading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-todo-subheading nil arg))

;;;;; TODO org-iswitchb

;; ;; M-x org-iswitchb RET;
;; ;;  its alias M-x org-switchb RET;
;; ;;  its alias M-x org-ido-switchb RET
;; (defun outshine-iswitchb(&optional arg)
;;   "Call outorg to trigger `org-iswitchb'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-iswitchb nil arg))

;;;;; TODO org-kill-line

;; ;; C-k (org-kill-line)
;; (defun outshine-kill-line(&optional arg)
;;   "Call outorg to trigger `org-kill-line'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-kill-line nil arg))

;;;;; TODO org-kill-note-or-show-branches

;; ;; C-c C-k (org-kill-note-or-show-branches)
;; (defun outshine-kill-note-or-show-branches(&optional arg)
;;   "Call outorg to trigger `org-kill-note-or-show-branches'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-kill-note-or-show-branches nil arg))

;;;;; TODO org-latex-convert-region-to-latex

;; ;; M-x org-latex-convert-region-to-latex RET
;; (defun outshine-latex-convert-region-to-latex(&optional arg)
;;   "Call outorg to trigger `org-latex-convert-region-to-latex'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-latex-convert-region-to-latex nil arg))

;;;;; TODO org-latex-export-as-latex

;; ;; M-x org-latex-export-as-latex RET
;; (defun outshine-latex-export-as-latex(&optional arg)
;;   "Call outorg to trigger `org-latex-export-as-latex'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-latex-export-as-latex nil arg))

;;;;; TODO org-latex-export-to-latex

;; ;; M-x org-latex-export-to-latex RET
;; (defun outshine-latex-export-to-latex(&optional arg)
;;   "Call outorg to trigger `org-latex-export-to-latex'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-latex-export-to-latex nil arg))

;;;;; TODO org-latex-export-to-pdf

;; ;; M-x org-latex-export-to-pdf RET
;; (defun outshine-latex-export-to-pdf(&optional arg)
;;   "Call outorg to trigger `org-latex-export-to-pdf'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-latex-export-to-pdf nil arg))

;;;;; TODO org-lint

;; ;; M-x org-lint RET
;; (defun outshine-lint(&optional arg)
;;   "Call outorg to trigger `org-lint'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-lint nil arg))

;;;;; TODO org-list-insert-radio-list

;; ;; M-x org-list-insert-radio-list RET
;; (defun outshine-list-insert-radio-list(&optional arg)
;;   "Call outorg to trigger `org-list-insert-radio-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-list-insert-radio-list nil arg))

;;;;; TODO org-list-make-subtree

;; ;; C-c C-* (org-list-make-subtree)
;; (defun outshine-list-make-subtree(&optional arg)
;;   "Call outorg to trigger `org-list-make-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-list-make-subtree nil arg))

;;;;; TODO org-list-repair

;; ;; M-x org-list-repair RET
;; (defun outshine-list-repair(&optional arg)
;;   "Call outorg to trigger `org-list-repair'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-list-repair nil arg))

;;;;; TODO org-list-send-list

;; ;; M-x org-list-send-list RET
;; (defun outshine-list-send-list(&optional arg)
;;   "Call outorg to trigger `org-list-send-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-list-send-list nil arg))

;;;;; TODO org-mark-element

;; ;; M-h (org-mark-element)
;; (defun outshine-mark-element(&optional arg)
;;   "Call outorg to trigger `org-mark-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mark-element nil arg))

;;;;; TODO org-mark-ring-goto

;; ;; C-c & (org-mark-ring-goto)
;; (defun outshine-mark-ring-goto(&optional arg)
;;   "Call outorg to trigger `org-mark-ring-goto'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mark-ring-goto nil arg))

;;;;; TODO org-mark-ring-push

;; ;; C-c % (org-mark-ring-push)
;; (defun outshine-mark-ring-push(&optional arg)
;;   "Call outorg to trigger `org-mark-ring-push'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mark-ring-push nil arg))

;;;;; TODO org-mark-subtree

;; ;; C-c @ (org-mark-subtree)
;; (defun outshine-mark-subtree(&optional arg)
;;   "Call outorg to trigger `org-mark-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mark-subtree nil arg))

;;;;; TODO org-match-sparse-tree

;; ;; C-c \, <menu-bar> <Org> <Special views current file> <Tags/Property tree> (org-match-sparse-tree);
;; ;;  its alias M-x org-tags-sparse-tree RET
;; (defun outshine-match-sparse-tree(&optional arg)
;;   "Call outorg to trigger `org-match-sparse-tree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-match-sparse-tree nil arg))

;;;;; TODO org-md-convert-region-to-md

;; ;; M-x org-md-convert-region-to-md RET
;; (defun outshine-md-convert-region-to-md(&optional arg)
;;   "Call outorg to trigger `org-md-convert-region-to-md'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-md-convert-region-to-md nil arg))

;;;;; TODO org-md-export-as-markdown

;; ;; M-x org-md-export-as-markdown RET
;; (defun outshine-md-export-as-markdown(&optional arg)
;;   "Call outorg to trigger `org-md-export-as-markdown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-md-export-as-markdown nil arg))

;;;;; TODO org-md-export-to-markdown

;; ;; M-x org-md-export-to-markdown RET
;; (defun outshine-md-export-to-markdown(&optional arg)
;;   "Call outorg to trigger `org-md-export-to-markdown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-md-export-to-markdown nil arg))

;;;;; TODO org-meta-return

;; ;; <M-return>, ESC <return>, C-c C-x m (org-meta-return)
;; (defun outshine-meta-return(&optional arg)
;;   "Call outorg to trigger `org-meta-return'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-meta-return nil arg))

;;;;; TODO org-metadown

;; ;; <M-down>, ESC <down>, <menu-bar> <Org> <Edit Structure> <Move Subtree Down>, <menu-bar> <Tbl> <Row> <Move Row Down> (org-metadown)
;; (defun outshine-metadown(&optional arg)
;;   "Call outorg to trigger `org-metadown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-metadown nil arg))

;;;;; TODO org-metaleft

;; ;; <M-left>, ESC <left>, C-c C-x l, <menu-bar> <Org> <Edit Structure> <Promote Heading>, <menu-bar> <Tbl> <Column> <Move Column Left> (org-metaleft)
;; (defun outshine-metaleft(&optional arg)
;;   "Call outorg to trigger `org-metaleft'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-metaleft nil arg))

;;;;; TODO org-metaright

;; ;; <M-right>, ESC <right>, C-c C-x r, <menu-bar> <Org> <Edit Structure> <Demote Heading>, <menu-bar> <Tbl> <Column> <Move Column Right> (org-metaright)
;; (defun outshine-metaright(&optional arg)
;;   "Call outorg to trigger `org-metaright'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-metaright nil arg))

;;;;; TODO org-metaup

;; ;; <M-up>, ESC <up>, C-c C-x u, <menu-bar> <Org> <Edit Structure> <Move Subtree Up>, <menu-bar> <Tbl> <Row> <Move Row Up> (org-metaup)
;; (defun outshine-metaup(&optional arg)
;;   "Call outorg to trigger `org-metaup'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-metaup nil arg))

;;;;; TODO org-mobile-pull

;; ;; <menu-bar> <Org> <MobileOrg> <Get Captured and Flagged>, C-c C-x RET g (org-mobile-pull)
;; (defun outshine-mobile-pull(&optional arg)
;;   "Call outorg to trigger `org-mobile-pull'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mobile-pull nil arg))

;;;;; TODO org-mobile-push

;; ;; <menu-bar> <Org> <MobileOrg> <Push Files and Views>, C-c C-x RET p (org-mobile-push)
;; (defun outshine-mobile-push(&optional arg)
;;   "Call outorg to trigger `org-mobile-push'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mobile-push nil arg))

;;;;; TODO org-mode

;; ;; M-x org-mode RET
;; (defun outshine-mode(&optional arg)
;;   "Call outorg to trigger `org-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mode nil arg))

;;;;; TODO org-mode-restart

;; ;; <menu-bar> <Org> <Refresh/Reload> <Refresh setup current buffer> (org-mode-restart)
;; (defun outshine-mode-restart(&optional arg)
;;   "Call outorg to trigger `org-mode-restart'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-mode-restart nil arg))

;;;;; TODO org-move-item-down

;; ;; M-x org-move-item-down RET
;; (defun outshine-move-item-down(&optional arg)
;;   "Call outorg to trigger `org-move-item-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-move-item-down nil arg))

;;;;; TODO org-move-item-up

;; ;; M-x org-move-item-up RET
;; (defun outshine-move-item-up(&optional arg)
;;   "Call outorg to trigger `org-move-item-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-move-item-up nil arg))

;;;;; TODO org-move-subtree-down

;; ;; M-x org-move-subtree-down RET
;; (defun outshine-move-subtree-down(&optional arg)
;;   "Call outorg to trigger `org-move-subtree-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-move-subtree-down nil arg))

;;;;; TODO org-move-subtree-up

;; ;; M-x org-move-subtree-up RET
;; (defun outshine-move-subtree-up(&optional arg)
;;   "Call outorg to trigger `org-move-subtree-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-move-subtree-up nil arg))

;;;;; TODO org-narrow-to-block

;; ;; C-x n b (org-narrow-to-block)
;; (defun outshine-narrow-to-block(&optional arg)
;;   "Call outorg to trigger `org-narrow-to-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-narrow-to-block nil arg))

;;;;; TODO org-narrow-to-element

;; ;; C-x n e (org-narrow-to-element)
;; (defun outshine-narrow-to-element(&optional arg)
;;   "Call outorg to trigger `org-narrow-to-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-narrow-to-element nil arg))

;;;;; TODO org-narrow-to-subtree

;; ;; C-x n s (org-narrow-to-subtree)
;; (defun outshine-narrow-to-subtree(&optional arg)
;;   "Call outorg to trigger `org-narrow-to-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-narrow-to-subtree nil arg))

;;;;; TODO org-next-block

;; ;; C-c M-f (org-next-block)
;; (defun outshine-next-block(&optional arg)
;;   "Call outorg to trigger `org-next-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-next-block nil arg))

;;;;; TODO org-next-item

;; ;; M-x org-next-item RET
;; (defun outshine-next-item(&optional arg)
;;   "Call outorg to trigger `org-next-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-next-item nil arg))

;;;;; DONE org-next-link
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:46]

;; reimplementation
;; C-c C-x C-n (org-next-link)
(defun outshine-next-link ()
  "Similar semantics to `org-next-link'."
  (interactive)
  (re-search-forward org-link-re-with-space nil t 1)
  (goto-char (match-beginning 0)))

;;;;; TODO org-next-visible-heading

;; ;; C-c C-n, <menu-bar> <Org> <Navigate Headings> <Next> (org-next-visible-heading)
;; (defun outshine-next-visible-heading(&optional arg)
;;   "Call outorg to trigger `org-next-visible-heading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-next-visible-heading nil arg))

;;;;; TODO org-occur

;; ;; M-x org-occur RET
;; (defun outshine-occur(&optional arg)
;;   "Call outorg to trigger `org-occur'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-occur nil arg))

;;;;; TODO org-occur-in-agenda-files

;; ;; <menu-bar> <Org> <File List for Agenda> <Occur in all agenda files> (org-occur-in-agenda-files)
;; (defun outshine-occur-in-agenda-files(&optional arg)
;;   "Call outorg to trigger `org-occur-in-agenda-files'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-occur-in-agenda-files nil arg))

;;;;; TODO org-occur-link-in-agenda-files

;; ;; <menu-bar> <Org> <Hyperlinks> <Find existing link to here> (org-occur-link-in-agenda-files)
;; (defun outshine-occur-link-in-agenda-files(&optional arg)
;;   "Call outorg to trigger `org-occur-link-in-agenda-files'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-occur-link-in-agenda-files nil arg))

;;;;; TODO org-odt-convert

;; ;; M-x org-odt-convert RET
;; (defun outshine-odt-convert(&optional arg)
;;   "Call outorg to trigger `org-odt-convert'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-odt-convert nil arg))

;;;;; TODO org-odt-export-as-odf

;; ;; M-x org-odt-export-as-odf RET
;; (defun outshine-odt-export-as-odf(&optional arg)
;;   "Call outorg to trigger `org-odt-export-as-odf'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-odt-export-as-odf nil arg))

;;;;; TODO org-odt-export-as-odf-and-open

;; ;; M-x org-odt-export-as-odf-and-open RET
;; (defun outshine-odt-export-as-odf-and-open(&optional arg)
;;   "Call outorg to trigger `org-odt-export-as-odf-and-open'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-odt-export-as-odf-and-open nil arg))

;;;;; TODO org-odt-export-to-odt

;; ;; M-x org-odt-export-to-odt RET
;; (defun outshine-odt-export-to-odt(&optional arg)
;;   "Call outorg to trigger `org-odt-export-to-odt'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-odt-export-to-odt nil arg))

;;;;; TODO org-open-at-mouse

;; ;; M-x org-open-at-mouse RET
;; (defun outshine-open-at-mouse(&optional arg)
;;   "Call outorg to trigger `org-open-at-mouse'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-open-at-mouse nil arg))

;;;;; DONE org-open-at-point
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:18]

;; C-c C-o (org-open-at-point)
(defun outshine-open-at-point (&optional whole-buffer-p arg reference-buffer)
  "Call outorg to trigger `org-open-at-point'.
With one prefix argument, use whole buffer, with two prefix
arguments, prompt user for function args WHOLE-BUFFER-P, ARG and
REFERENCE-BUFFER."
  (interactive
   (cond
    ((equal current-prefix-arg '(16))
     (list (y-or-n-p "Use whole buffer ")
	   (y-or-n-p "Provide ARG ")
	   (read-buffer "Reference-buffer: ")))
    (current-prefix-arg (list t))
    (t nil)))
  (outshine-use-outorg
   'org-open-at-point whole-buffer-p nil arg reference-buffer))

;;;;; TODO org-open-at-point-global

;; ;; M-x org-open-at-point-global RET
;; (defun outshine-open-at-point-global(&optional arg)
;;   "Call outorg to trigger `org-open-at-point-global'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-open-at-point-global nil arg))

;;;;; TODO org-open-line

;; ;; C-o, <insertline> (org-open-line)
;; (defun outshine-open-line(&optional arg)
;;   "Call outorg to trigger `org-open-line'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-open-line nil arg))

;;;;; TODO org-open-link-from-string

;; ;; M-x org-open-link-from-string RET
;; (defun outshine-open-link-from-string(&optional arg)
;;   "Call outorg to trigger `org-open-link-from-string'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-open-link-from-string nil arg))

;;;;; TODO org-org-export-as-org

;; ;; M-x org-org-export-as-org RET
;; (defun outshine-org-export-as-org(&optional arg)
;;   "Call outorg to trigger `org-org-export-as-org'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-org-export-as-org nil arg))

;;;;; TODO org-org-export-to-org

;; ;; M-x org-org-export-to-org RET
;; (defun outshine-org-export-to-org(&optional arg)
;;   "Call outorg to trigger `org-org-export-to-org'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-org-export-to-org nil arg))

;;;;; TODO org-org-menu

;; ;; M-x org-org-menu RET
;; (defun outshine-org-menu(&optional arg)
;;   "Call outorg to trigger `org-org-menu'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-org-menu nil arg))

;;;;; TODO org-outdent-item

;; ;; M-x org-outdent-item RET
;; (defun outshine-outdent-item(&optional arg)
;;   "Call outorg to trigger `org-outdent-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-outdent-item nil arg))

;;;;; TODO org-outdent-item-tree

;; ;; M-x org-outdent-item-tree RET
;; (defun outshine-outdent-item-tree(&optional arg)
;;   "Call outorg to trigger `org-outdent-item-tree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-outdent-item-tree nil arg))

;;;;; TODO org-overview

;; ;; M-x org-overview RET
;; (defun outshine-overview(&optional arg)
;;   "Call outorg to trigger `org-overview'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-overview nil arg))

;;;;; TODO org-paste-special

;; ;; C-c C-x C-y, <menu-bar> <Org> <Edit Structure> <Paste Subtree>, <menu-bar> <Tbl> <Rectangle> <Paste Rectangle> (org-paste-special)
;; (defun outshine-paste-special(&optional arg)
;;   "Call outorg to trigger `org-paste-special'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-paste-special nil arg))

;;;;; TODO org-paste-subtree

;; ;; M-x org-paste-subtree RET
;; (defun outshine-paste-subtree(&optional arg)
;;   "Call outorg to trigger `org-paste-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-paste-subtree nil arg))

;;;;; TODO org-plot/gnuplot :plot/gnuplot:

;; ;; 
;; (defun outshine-plot/gnuplot :plot/gnuplot:(&optional arg)
;;   "Call outorg to trigger `org-plot/gnuplot :plot/gnuplot:'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-plot/gnuplot :plot/gnuplot: nil arg))

;;;;; TODO org-preview-latex-fragment

;; ;; M-x org-preview-latex-fragment RET;
;; ;;  its alias C-c C-x C-l (org-toggle-latex-fragment)
;; (defun outshine-preview-latex-fragment(&optional arg)
;;   "Call outorg to trigger `org-preview-latex-fragment'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-preview-latex-fragment nil arg))

;;;;; TODO org-previous-block

;; ;; C-c M-b (org-previous-block)
;; (defun outshine-previous-block(&optional arg)
;;   "Call outorg to trigger `org-previous-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-previous-block nil arg))

;;;;; TODO org-previous-item

;; ;; M-x org-previous-item RET
;; (defun outshine-previous-item(&optional arg)
;;   "Call outorg to trigger `org-previous-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-previous-item nil arg))

;;;;; DONE org-previous-link
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:50]

;; reimplementation
;; C-c C-x C-p (org-previous-link)
(defun outshine-previous-link ()
  "Similar semantics to `org-previous-link'."
  (interactive)
  (re-search-backward org-link-re-with-space nil t 1)
  (goto-char (match-beginning 0)))

;;;;; TODO org-previous-visible-heading

;; ;; C-c C-p, <menu-bar> <Org> <Navigate Headings> <Previous> (org-previous-visible-heading)
;; (defun outshine-previous-visible-heading(&optional arg)
;;   "Call outorg to trigger `org-previous-visible-heading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-previous-visible-heading nil arg))

;;;;; DONE org-priority
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:28]

;; C-c , (org-priority)

(defun outshine-priority ()
  "Call outorg to trigger `org-priority'."
  (interactive)
  (outshine-use-outorg 'org-priority))

;;;;; TODO org-priority-down

;; ;; M-x org-priority-down RET
;; (defun outshine-priority-down(&optional arg)
;;   "Call outorg to trigger `org-priority-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-priority-down nil arg))

;;;;; TODO org-priority-up

;; ;; M-x org-priority-up RET
;; (defun outshine-priority-up(&optional arg)
;;   "Call outorg to trigger `org-priority-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-priority-up nil arg))

;;;;; TODO org-promote-subtree

;; ;; C-c C-< (org-promote-subtree)
;; (defun outshine-promote-subtree(&optional arg)
;;   "Call outorg to trigger `org-promote-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-promote-subtree nil arg))

;;;;; TODO org-property-action

;; ;; M-x org-property-action RET
;; (defun outshine-property-action(&optional arg)
;;   "Call outorg to trigger `org-property-action'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-property-action nil arg))

;;;;; TODO org-property-next-allowed-value

;; ;; M-x org-property-next-allowed-value RET
;; (defun outshine-property-next-allowed-value(&optional arg)
;;   "Call outorg to trigger `org-property-next-allowed-value'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-property-next-allowed-value nil arg))

;;;;; TODO org-property-previous-allowed-value

;; ;; M-x org-property-previous-allowed-value RET
;; (defun outshine-property-previous-allowed-value(&optional arg)
;;   "Call outorg to trigger `org-property-previous-allowed-value'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-property-previous-allowed-value nil arg))

;;;;; TODO org-publish

;; ;; M-x org-publish RET;
;; ;;  its alias M-x org-publish-project RET
;; (defun outshine-publish(&optional arg)
;;   "Call outorg to trigger `org-publish'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-publish nil arg))

;;;;; TODO org-publish-all

;; ;; M-x org-publish-all RET
;; (defun outshine-publish-all(&optional arg)
;;   "Call outorg to trigger `org-publish-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-publish-all nil arg))

;;;;; TODO org-publish-current-file

;; ;; M-x org-publish-current-file RET
;; (defun outshine-publish-current-file(&optional arg)
;;   "Call outorg to trigger `org-publish-current-file'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-publish-current-file nil arg))

;;;;; TODO org-publish-current-project

;; ;; M-x org-publish-current-project RET
;; (defun outshine-publish-current-project(&optional arg)
;;   "Call outorg to trigger `org-publish-current-project'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-publish-current-project nil arg))

;;;;; TODO org-publish-project

;; ;; M-x org-publish-project RET;
;; ;;  its alias M-x org-publish RET
;; (defun outshine-publish-project(&optional arg)
;;   "Call outorg to trigger `org-publish-project'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-publish-project nil arg))

;;;;; TODO org-redisplay-inline-images

;; ;; C-c C-x C-M-v (org-redisplay-inline-images)
;; (defun outshine-redisplay-inline-images(&optional arg)
;;   "Call outorg to trigger `org-redisplay-inline-images'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-redisplay-inline-images nil arg))

;;;;; TODO org-refile

;; ;; C-c C-w, <menu-bar> <Org> <Edit Structure> <Refile Subtree> (org-refile)
;; (defun outshine-refile(&optional arg)
;;   "Call outorg to trigger `org-refile'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-refile nil arg))

;;;;; TODO org-refile-goto-last-stored

;; ;; M-x org-refile-goto-last-stored RET
;; (defun outshine-refile-goto-last-stored(&optional arg)
;;   "Call outorg to trigger `org-refile-goto-last-stored'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-refile-goto-last-stored nil arg))

;;;;; TODO org-reftex-citation

;; ;; C-c C-x [, <menu-bar> <Org> <LaTeX> <Insert citation> (org-reftex-citation)
;; (defun outshine-reftex-citation(&optional arg)
;;   "Call outorg to trigger `org-reftex-citation'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-reftex-citation nil arg))

;;;;; TODO org-reload

;; ;; C-c C-x !, <menu-bar> <Org> <Refresh/Reload> <Reload Org (after update)> (org-reload)
;; (defun outshine-reload(&optional arg)
;;   "Call outorg to trigger `org-reload'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-reload nil arg))

;;;;; TODO org-remove-file

;; ;; <menu-bar> <Org> <File List for Agenda> <Remove Current File from List> (org-remove-file)
;; (defun outshine-remove-file(&optional arg)
;;   "Call outorg to trigger `org-remove-file'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-remove-file nil arg))

;;;;; TODO org-remove-inline-images

;; ;; M-x org-remove-inline-images RET
;; (defun outshine-remove-inline-images(&optional arg)
;;   "Call outorg to trigger `org-remove-inline-images'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-remove-inline-images nil arg))

;;;;; TODO org-remove-occur-highlights

;; ;; M-x org-remove-occur-highlights RET
;; (defun outshine-remove-occur-highlights(&optional arg)
;;   "Call outorg to trigger `org-remove-occur-highlights'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-remove-occur-highlights nil arg))

;;;;; TODO org-require-autoloaded-modules

;; ;; M-x org-require-autoloaded-modules RET
;; (defun outshine-require-autoloaded-modules(&optional arg)
;;   "Call outorg to trigger `org-require-autoloaded-modules'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-require-autoloaded-modules nil arg))

;;;;; TODO org-reset-checkbox-state-subtree

;; ;; M-x org-reset-checkbox-state-subtree RET
;; (defun outshine-reset-checkbox-state-subtree(&optional arg)
;;   "Call outorg to trigger `org-reset-checkbox-state-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-reset-checkbox-state-subtree nil arg))

;;;;; TODO org-resolve-clocks

;; ;; C-c C-x C-z (org-resolve-clocks)
;; (defun outshine-resolve-clocks(&optional arg)
;;   "Call outorg to trigger `org-resolve-clocks'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-resolve-clocks nil arg))

;;;;; TODO org-return

;; ;; RET, <menu-bar> <Tbl> <Next Row> (org-return)
;; (defun outshine-return(&optional arg)
;;   "Call outorg to trigger `org-return'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-return nil arg))

;;;;; TODO org-return-indent

;; ;; C-j (org-return-indent)
;; (defun outshine-return-indent(&optional arg)
;;   "Call outorg to trigger `org-return-indent'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-return-indent nil arg))

;;;;; TODO org-reveal

;; ;; C-c C-r, <menu-bar> <Org> <Show/Hide> <Reveal Context> (org-reveal)
;; (defun outshine-reveal(&optional arg)
;;   "Call outorg to trigger `org-reveal'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-reveal nil arg))

;;;;; TODO org-revert-all-org-buffers

;; ;; M-x org-revert-all-org-buffers RET
;; (defun outshine-revert-all-org-buffers(&optional arg)
;;   "Call outorg to trigger `org-revert-all-org-buffers'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-revert-all-org-buffers nil arg))

;;;;; TODO org-save-all-org-buffers

;; ;; M-x org-save-all-org-buffers RET
;; (defun outshine-save-all-org-buffers(&optional arg)
;;   "Call outorg to trigger `org-save-all-org-buffers'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-save-all-org-buffers nil arg))

;;;;; DONE org-schedule
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:21]

;; C-c C-s (org-schedule)
(defun outshine-schedule (&optional arg)
  "Call outorg to trigger `org-schedule'."
  (interactive "P")
  (outshine-use-outorg
   (lambda ()
     (interactive)
     (let ((current-prefix-arg arg))
       (call-interactively 'org-schedule)))))

;;;;; TODO org-search-view

;; ;; M-x org-search-view RET
;; (defun outshine-search-view(&optional arg)
;;   "Call outorg to trigger `org-search-view'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-search-view nil arg))

;;;;; TODO org-self-insert-command

;; ;; SPC..~, ..\377 (org-self-insert-command)
;; (defun outshine-self-insert-command(&optional arg)
;;   "Call outorg to trigger `org-self-insert-command'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-self-insert-command nil arg))

;;;;; DONE org-set-effort
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:11]

;; C-c C-x e (org-set-effort)
(defun outshine-set-effort (&optional arg)
  "Call outorg to trigger `org-set-effort'."
  (interactive "p")
  (outshine-use-outorg
   'org-set-effort nil arg))

;;;;; DONE org-set-property
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:13]

;; C-c C-x p (org-set-property)
(defun outshine-set-property ()
  "Call outorg to trigger `org-set-property'."
  (interactive)
  (outshine-use-outorg 'org-set-property))

;;;;; DONE org-set-property-and-value
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:09]

;; C-c C-x P (org-set-property-and-value)
(defun outshine-set-property-and-value ()
  "Call outorg to trigger `org-set-property-and-value'."
  (interactive)
  (outshine-use-outorg 'org-set-property-and-value))

;;;;; TODO org-set-tags

;; ;; M-x org-set-tags RET
;; (defun outshine-set-tags(&optional arg)
;;   "Call outorg to trigger `org-set-tags'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-set-tags nil arg))

;;;;; DONE org-set-tags-command
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:20]

;; C-c C-q (org-set-tags-command)
(defun outshine-set-tags-command ()
  "Call outorg to trigger `org-set-tags-command'."
  (interactive)
  (outshine-use-outorg 'org-set-tags-command))

;;;;; TODO org-set-tags-to

;; ;; M-x org-set-tags-to RET
;; (defun outshine-set-tags-to(&optional arg)
;;   "Call outorg to trigger `org-set-tags-to'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-set-tags-to nil arg))

;;;;; TODO org-set-visibility-according-to-property

;; ;; M-x org-set-visibility-according-to-property RET
;; (defun outshine-set-visibility-according-to-property(&optional arg)
;;   "Call outorg to trigger `org-set-visibility-according-to-property'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-set-visibility-according-to-property nil arg))

;;;;; TODO org-setup-comments-handling

;; ;; M-x org-setup-comments-handling RET
;; (defun outshine-setup-comments-handling(&optional arg)
;;   "Call outorg to trigger `org-setup-comments-handling'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-setup-comments-handling nil arg))

;;;;; TODO org-shiftcontroldown

;; ;; <C-S-down> (org-shiftcontroldown)
;; (defun outshine-shiftcontroldown(&optional arg)
;;   "Call outorg to trigger `org-shiftcontroldown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftcontroldown nil arg))

;;;;; TODO org-shiftcontrolleft

;; ;; M-S--, C-c C-x <left> (org-shiftcontrolleft)
;; (defun outshine-shiftcontrolleft(&optional arg)
;;   "Call outorg to trigger `org-shiftcontrolleft'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftcontrolleft nil arg))

;;;;; TODO org-shiftcontrolright

;; ;; M-S-+, C-c C-x <right>, <menu-bar> <Org> <TODO Lists> <Select keyword> <Next keyword set>, <menu-bar> <Org> <TODO Lists> <Select keyword> <Previous keyword set> (org-shiftcontrolright)
;; (defun outshine-shiftcontrolright(&optional arg)
;;   "Call outorg to trigger `org-shiftcontrolright'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftcontrolright nil arg))

;;;;; TODO org-shiftcontrolup

;; ;; <C-S-up> (org-shiftcontrolup)
;; (defun outshine-shiftcontrolup(&optional arg)
;;   "Call outorg to trigger `org-shiftcontrolup'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftcontrolup nil arg))

;;;;; TODO org-shiftdown

;; ;; M-n, C-c <down>, <menu-bar> <Org> <TODO Lists> <Priority Down>, <menu-bar> <Org> <Dates and Scheduling> <Change Date> <1 ... Earlier> (org-shiftdown)
;; (defun outshine-shiftdown(&optional arg)
;;   "Call outorg to trigger `org-shiftdown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftdown nil arg))

;;;;; TODO org-shiftleft

;; ;; M--, <menu-bar> <Org> <TODO Lists> <Select keyword> <Previous keyword>, <menu-bar> <Org> <Dates and Scheduling> <Change Date> <1 Day Earlier> (org-shiftleft)
;; (defun outshine-shiftleft(&optional arg)
;;   "Call outorg to trigger `org-shiftleft'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftleft nil arg))

;;;;; TODO org-shiftmetadown

;; ;; <M-S-down>, ESC <S-down>, C-c C-x D, <menu-bar> <Tbl> <Row> <Insert Row> (org-shiftmetadown)
;; (defun outshine-shiftmetadown(&optional arg)
;;   "Call outorg to trigger `org-shiftmetadown'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftmetadown nil arg))

;;;;; TODO org-shiftmetaleft

;; ;; <M-S-left>, ESC <S-left>, C-c C-x L, <menu-bar> <Org> <Edit Structure> <Promote Subtree>, <menu-bar> <Tbl> <Column> <Delete Column> (org-shiftmetaleft)
;; (defun outshine-shiftmetaleft(&optional arg)
;;   "Call outorg to trigger `org-shiftmetaleft'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftmetaleft nil arg))

;;;;; TODO org-shiftmetaright

;; ;; <M-S-right>, ESC <S-right>, C-c C-x R, <menu-bar> <Org> <Edit Structure> <Demote Subtree>, <menu-bar> <Tbl> <Column> <Insert Column> (org-shiftmetaright)
;; (defun outshine-shiftmetaright(&optional arg)
;;   "Call outorg to trigger `org-shiftmetaright'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftmetaright nil arg))

;;;;; TODO org-shiftmetaup

;; ;; <M-S-up>, ESC <S-up>, C-c C-x U, <menu-bar> <Tbl> <Row> <Delete Row> (org-shiftmetaup)
;; (defun outshine-shiftmetaup(&optional arg)
;;   "Call outorg to trigger `org-shiftmetaup'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftmetaup nil arg))

;;;;; TODO org-shiftright

;; ;; M-+, <menu-bar> <Org> <TODO Lists> <Select keyword> <Next keyword>, <menu-bar> <Org> <Dates and Scheduling> <Change Date> <1 Day Later> (org-shiftright)
;; (defun outshine-shiftright(&optional arg)
;;   "Call outorg to trigger `org-shiftright'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftright nil arg))

;;;;; TODO org-shifttab

;; ;; <backtab>, <S-tab>, <S-iso-lefttab>, <menu-bar> <Tbl> <Previous Field>, <menu-bar> <Org> <Show/Hide> <Cycle Global Visibility> (org-shifttab)
;; (defun outshine-shifttab(&optional arg)
;;   "Call outorg to trigger `org-shifttab'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shifttab nil arg))

;;;;; TODO org-shiftup

;; ;; M-p, C-c <up>, <menu-bar> <Org> <TODO Lists> <Priority Up>, <menu-bar> <Org> <Dates and Scheduling> <Change Date> <1 ... Later> (org-shiftup)
;; (defun outshine-shiftup(&optional arg)
;;   "Call outorg to trigger `org-shiftup'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-shiftup nil arg))

;;;;; TODO org-show-block-all

;; ;; M-x org-show-block-all RET
;; (defun outshine-show-block-all(&optional arg)
;;   "Call outorg to trigger `org-show-block-all'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-show-block-all nil arg))

;;;;; TODO org-show-children

;; ;; C-c TAB (org-show-children)
;; (defun outshine-show-children(&optional arg)
;;   "Call outorg to trigger `org-show-children'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-show-children nil arg))

;;;;; TODO org-show-entry

;; ;; M-x org-show-entry RET
;; (defun outshine-show-entry(&optional arg)
;;   "Call outorg to trigger `org-show-entry'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-show-entry nil arg))

;;;;; TODO org-show-priority

;; ;; M-x org-show-priority RET
;; (defun outshine-show-priority(&optional arg)
;;   "Call outorg to trigger `org-show-priority'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-show-priority nil arg))

;;;;; TODO org-show-subtree

;; ;; M-x org-show-subtree RET
;; (defun outshine-show-subtree(&optional arg)
;;   "Call outorg to trigger `org-show-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-show-subtree nil arg))

;;;;; TODO org-show-todo-tree

;; ;; <menu-bar> <Org> <TODO Lists> <Show TODO Tree>, <menu-bar> <Org> <Special views current file> <TODO Tree> (org-show-todo-tree)
;; (defun outshine-show-todo-tree(&optional arg)
;;   "Call outorg to trigger `org-show-todo-tree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-show-todo-tree nil arg))

;;;;; NEXT org-sort

;; FIXME handle markers for sorting regions
;; C-c ^ (org-sort)
(defun outshine-sort (&optional arg)
  "Call outorg to trigger `org-sort'.
With prefix ARG, use whole buffer."
  (interactive "P")
  (outshine-use-outorg 'org-sort-entries arg))

;;;;; TODO org-sort-entries

;; ;; M-x org-sort-entries RET
;; (defun outshine-sort-entries(&optional arg)
;;   "Call outorg to trigger `org-sort-entries'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-sort-entries nil arg))

;;;;; TODO org-sort-list

;; ;; M-x org-sort-list RET
;; (defun outshine-sort-list(&optional arg)
;;   "Call outorg to trigger `org-sort-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-sort-list nil arg))

;;;;; TODO org-sparse-tree

;; ;; C-c /, <menu-bar> <Org> <Show/Hide> <Sparse Tree...> (org-sparse-tree)
;; (defun outshine-sparse-tree(&optional arg)
;;   "Call outorg to trigger `org-sparse-tree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-sparse-tree nil arg))

;;;;; TODO org-speed-command-help

;; ;; M-x org-speed-command-help RET
;; (defun outshine-speed-command-help(&optional arg)
;;   "Call outorg to trigger `org-speed-command-help'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-speed-command-help nil arg))

;;;;; TODO org-speed-move-safe

;; ;; M-x org-speed-move-safe RET
;; (defun outshine-speed-move-safe(&optional arg)
;;   "Call outorg to trigger `org-speed-move-safe'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-speed-move-safe nil arg))

;;;;; TODO org-speedbar-set-agenda-restriction

;; ;; M-x org-speedbar-set-agenda-restriction RET
;; (defun outshine-speedbar-set-agenda-restriction(&optional arg)
;;   "Call outorg to trigger `org-speedbar-set-agenda-restriction'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-speedbar-set-agenda-restriction nil arg))

;; FIXME
;; ;; C-c C-x >	org-agenda-remove-restriction-lock
(defun outshine-agenda-remove-restriction-lock (&optional
  include-org-p)
  "Call `outshine-agenda' without restriction.
Use `outshine-agenda-files'. When INCLUDE-ORG-P is non-nil or prefix-arg is given, include `org-agenda-files'."
  (interactive "P")
  (outshine-agenda nil include-org-p))


;;;;; TODO org-src-associate-babel-session

;; ;; M-x org-src-associate-babel-session RET
;; (defun outshine-src-associate-babel-session(&optional arg)
;;   "Call outorg to trigger `org-src-associate-babel-session'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-src-associate-babel-session nil arg))

;;;;; TODO org-src-do-key-sequence-at-code-block

;; ;; M-x org-src-do-key-sequence-at-code-block RET
;; (defun outshine-src-do-key-sequence-at-code-block(&optional arg)
;;   "Call outorg to trigger `org-src-do-key-sequence-at-code-block'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-src-do-key-sequence-at-code-block nil arg))

;;;;; TODO org-src-mode

;; ;; M-x org-src-mode RET
;; (defun outshine-src-mode(&optional arg)
;;   "Call outorg to trigger `org-src-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-src-mode nil arg))

;;;;; TODO org-store-agenda-views

;; ;; M-x org-store-agenda-views RET
;; (defun outshine-store-agenda-views(&optional arg)
;;   "Call outorg to trigger `org-store-agenda-views'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-store-agenda-views nil arg))

;;;;; TODO org-store-link

;; ;; <menu-bar> <Org> <Hyperlinks> <Store Link (Global)> (org-store-link)
;; (defun outshine-store-link(&optional arg)
;;   "Call outorg to trigger `org-store-link'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-store-link nil arg))

;;;;; TODO org-submit-bug-report

;; ;; <menu-bar> <Org> <Send bug report> (org-submit-bug-report)
;; (defun outshine-submit-bug-report(&optional arg)
;;   "Call outorg to trigger `org-submit-bug-report'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-submit-bug-report nil arg))

;;;;; TODO org-switchb

;; ;; M-x org-switchb RET;
;; ;;  its alias M-x org-iswitchb RET;
;; ;;  its alias M-x org-ido-switchb RET
;; (defun outshine-switchb(&optional arg)
;;   "Call outorg to trigger `org-switchb'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-switchb nil arg))

;;;;; TODO org-table-align

;; ;; M-x org-table-align RET
;; (defun outshine-table-align(&optional arg)
;;   "Call outorg to trigger `org-table-align'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-align nil arg))

;;;;; TODO org-table-beginning-of-field

;; ;; M-x org-table-beginning-of-field RET
;; (defun outshine-table-beginning-of-field(&optional arg)
;;   "Call outorg to trigger `org-table-beginning-of-field'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-beginning-of-field nil arg))

;;;;; TODO org-table-blank-field

;; ;; C-c SPC, <menu-bar> <Tbl> <Blank Field> (org-table-blank-field)
;; (defun outshine-table-blank-field(&optional arg)
;;   "Call outorg to trigger `org-table-blank-field'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-blank-field nil arg))

;;;;; TODO org-table-calc-current-TBLFM

;; ;; M-x org-table-calc-current-TBLFM RET
;; (defun outshine-table-calc-current-TBLFM(&optional arg)
;;   "Call outorg to trigger `org-table-calc-current-TBLFM'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-calc-current-TBLFM nil arg))

;;;;; TODO org-table-convert

;; ;; M-x org-table-convert RET
;; (defun outshine-table-convert(&optional arg)
;;   "Call outorg to trigger `org-table-convert'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-convert nil arg))

;;;;; TODO org-table-convert-region

;; ;; <menu-bar> <Tbl> <Convert Region> (org-table-convert-region)
;; (defun outshine-table-convert-region(&optional arg)
;;   "Call outorg to trigger `org-table-convert-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-convert-region nil arg))

;;;;; TODO org-table-copy-down

;; ;; <S-return>, <menu-bar> <Tbl> <Copy Field from Above> (org-table-copy-down)
;; (defun outshine-table-copy-down(&optional arg)
;;   "Call outorg to trigger `org-table-copy-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-copy-down nil arg))

;;;;; TODO org-table-copy-region

;; ;; M-x org-table-copy-region RET
;; (defun outshine-table-copy-region(&optional arg)
;;   "Call outorg to trigger `org-table-copy-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-copy-region nil arg))

;;;;; TODO org-table-create

;; ;; <menu-bar> <Tbl> <Create> (org-table-create)
;; (defun outshine-table-create(&optional arg)
;;   "Call outorg to trigger `org-table-create'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-create nil arg))

;;;;; TODO org-table-create-or-convert-from-region

;; ;; C-c | (org-table-create-or-convert-from-region)
;; (defun outshine-table-create-or-convert-from-region(&optional arg)
;;   "Call outorg to trigger `org-table-create-or-convert-from-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-create-or-convert-from-region nil arg))

;;;;; TODO org-table-create-with-table.el

;; ;; C-c ~, <menu-bar> <Tbl> <Create/Convert from/to table.el> (org-table-create-with-table.el)
;; (defun outshine-table-create-with-table.el(&optional arg)
;;   "Call outorg to trigger `org-table-create-with-table.el'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-create-with-table.el nil arg))

;;;;; TODO org-table-current-column

;; ;; <menu-bar> <Tbl> <Calculate> <Which Column?> (org-table-current-column)
;; (defun outshine-table-current-column(&optional arg)
;;   "Call outorg to trigger `org-table-current-column'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-current-column nil arg))

;;;;; TODO org-table-current-dline

;; ;; M-x org-table-current-dline RET
;; (defun outshine-table-current-dline(&optional arg)
;;   "Call outorg to trigger `org-table-current-dline'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-current-dline nil arg))

;;;;; TODO org-table-cut-region

;; ;; M-x org-table-cut-region RET
;; (defun outshine-table-cut-region(&optional arg)
;;   "Call outorg to trigger `org-table-cut-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-cut-region nil arg))

;;;;; TODO org-table-delete-column

;; ;; M-x org-table-delete-column RET
;; (defun outshine-table-delete-column(&optional arg)
;;   "Call outorg to trigger `org-table-delete-column'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-delete-column nil arg))

;;;;; TODO org-table-edit-field

;; ;; C-c `, <menu-bar> <Tbl> <Edit Field> (org-table-edit-field)
;; (defun outshine-table-edit-field(&optional arg)
;;   "Call outorg to trigger `org-table-edit-field'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-edit-field nil arg))

;;;;; TODO org-table-edit-formulas

;; ;; M-x org-table-edit-formulas RET
;; (defun outshine-table-edit-formulas(&optional arg)
;;   "Call outorg to trigger `org-table-edit-formulas'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-edit-formulas nil arg))

;;;;; TODO org-table-end-of-field

;; ;; M-x org-table-end-of-field RET
;; (defun outshine-table-end-of-field(&optional arg)
;;   "Call outorg to trigger `org-table-end-of-field'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-end-of-field nil arg))

;;;;; TODO org-table-eval-formula

;; ;; C-c =, <menu-bar> <Tbl> <Calculate> <Set Column Formula> (org-table-eval-formula)
;; (defun outshine-table-eval-formula(&optional arg)
;;   "Call outorg to trigger `org-table-eval-formula'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-eval-formula nil arg))

;;;;; TODO org-table-export

;; ;; <menu-bar> <Tbl> <Export to File> (org-table-export)
;; (defun outshine-table-export(&optional arg)
;;   "Call outorg to trigger `org-table-export'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-export nil arg))

;;;;; TODO org-table-fedit-abort

;; ;; M-x org-table-fedit-abort RET
;; (defun outshine-table-fedit-abort(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-abort'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-abort nil arg))

;;;;; TODO org-table-fedit-finish

;; ;; M-x org-table-fedit-finish RET
;; (defun outshine-table-fedit-finish(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-finish'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-finish nil arg))

;;;;; TODO org-table-fedit-line-down

;; ;; M-x org-table-fedit-line-down RET
;; (defun outshine-table-fedit-line-down(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-line-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-line-down nil arg))

;;;;; TODO org-table-fedit-line-up

;; ;; M-x org-table-fedit-line-up RET
;; (defun outshine-table-fedit-line-up(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-line-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-line-up nil arg))

;;;;; TODO org-table-fedit-lisp-indent

;; ;; M-x org-table-fedit-lisp-indent RET
;; (defun outshine-table-fedit-lisp-indent(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-lisp-indent'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-lisp-indent nil arg))

;;;;; TODO org-table-fedit-menu

;; ;; M-x org-table-fedit-menu RET
;; (defun outshine-table-fedit-menu(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-menu'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-menu nil arg))

;;;;; TODO org-table-fedit-ref-down

;; ;; M-x org-table-fedit-ref-down RET
;; (defun outshine-table-fedit-ref-down(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-ref-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-ref-down nil arg))

;;;;; TODO org-table-fedit-ref-left

;; ;; M-x org-table-fedit-ref-left RET
;; (defun outshine-table-fedit-ref-left(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-ref-left'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-ref-left nil arg))

;;;;; TODO org-table-fedit-ref-right

;; ;; M-x org-table-fedit-ref-right RET
;; (defun outshine-table-fedit-ref-right(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-ref-right'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-ref-right nil arg))

;;;;; TODO org-table-fedit-ref-up

;; ;; M-x org-table-fedit-ref-up RET
;; (defun outshine-table-fedit-ref-up(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-ref-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-ref-up nil arg))

;;;;; TODO org-table-fedit-scroll

;; ;; M-x org-table-fedit-scroll RET
;; (defun outshine-table-fedit-scroll(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-scroll'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-scroll nil arg))

;;;;; TODO org-table-fedit-scroll-down

;; ;; M-x org-table-fedit-scroll-down RET
;; (defun outshine-table-fedit-scroll-down(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-scroll-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-scroll-down nil arg))

;;;;; TODO org-table-fedit-toggle-coordinates

;; ;; M-x org-table-fedit-toggle-coordinates RET
;; (defun outshine-table-fedit-toggle-coordinates(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-toggle-coordinates'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-toggle-coordinates nil arg))

;;;;; TODO org-table-fedit-toggle-ref-type

;; ;; M-x org-table-fedit-toggle-ref-type RET
;; (defun outshine-table-fedit-toggle-ref-type(&optional arg)
;;   "Call outorg to trigger `org-table-fedit-toggle-ref-type'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-fedit-toggle-ref-type nil arg))

;;;;; TODO org-table-field-info

;; ;; C-c ? (org-table-field-info)
;; (defun outshine-table-field-info(&optional arg)
;;   "Call outorg to trigger `org-table-field-info'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-field-info nil arg))

;;;;; TODO org-table-follow-field-mode

;; ;; M-x org-table-follow-field-mode RET
;; (defun outshine-table-follow-field-mode(&optional arg)
;;   "Call outorg to trigger `org-table-follow-field-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-follow-field-mode nil arg))

;;;;; TODO org-table-goto-column

;; ;; M-x org-table-goto-column RET
;; (defun outshine-table-goto-column(&optional arg)
;;   "Call outorg to trigger `org-table-goto-column'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-goto-column nil arg))

;;;;; TODO org-table-hline-and-move

;; ;; M-x org-table-hline-and-move RET
;; (defun outshine-table-hline-and-move(&optional arg)
;;   "Call outorg to trigger `org-table-hline-and-move'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-hline-and-move nil arg))

;;;;; TODO org-table-import

;; ;; <menu-bar> <Tbl> <Import from File> (org-table-import)
;; (defun outshine-table-import(&optional arg)
;;   "Call outorg to trigger `org-table-import'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-import nil arg))

;;;;; TODO org-table-insert-column

;; ;; M-x org-table-insert-column RET
;; (defun outshine-table-insert-column(&optional arg)
;;   "Call outorg to trigger `org-table-insert-column'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-insert-column nil arg))

;;;;; TODO org-table-insert-hline

;; ;; M-x org-table-insert-hline RET
;; (defun outshine-table-insert-hline(&optional arg)
;;   "Call outorg to trigger `org-table-insert-hline'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-insert-hline nil arg))

;;;;; TODO org-table-insert-row

;; ;; M-x org-table-insert-row RET
;; (defun outshine-table-insert-row(&optional arg)
;;   "Call outorg to trigger `org-table-insert-row'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-insert-row nil arg))

;;;;; TODO org-table-iterate

;; ;; M-x org-table-iterate RET
;; (defun outshine-table-iterate(&optional arg)
;;   "Call outorg to trigger `org-table-iterate'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-iterate nil arg))

;;;;; TODO org-table-iterate-buffer-tables

;; ;; M-x org-table-iterate-buffer-tables RET
;; (defun outshine-table-iterate-buffer-tables(&optional arg)
;;   "Call outorg to trigger `org-table-iterate-buffer-tables'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-iterate-buffer-tables nil arg))

;;;;; TODO org-table-kill-row

;; ;; M-x org-table-kill-row RET
;; (defun outshine-table-kill-row(&optional arg)
;;   "Call outorg to trigger `org-table-kill-row'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-kill-row nil arg))

;;;;; TODO org-table-maybe-recalculate-line

;; ;; M-x org-table-maybe-recalculate-line RET
;; (defun outshine-table-maybe-recalculate-line(&optional arg)
;;   "Call outorg to trigger `org-table-maybe-recalculate-line'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-maybe-recalculate-line nil arg))

;;;;; TODO org-table-move-column

;; ;; M-x org-table-move-column RET
;; (defun outshine-table-move-column(&optional arg)
;;   "Call outorg to trigger `org-table-move-column'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-move-column nil arg))

;;;;; TODO org-table-move-column-left

;; ;; M-x org-table-move-column-left RET
;; (defun outshine-table-move-column-left(&optional arg)
;;   "Call outorg to trigger `org-table-move-column-left'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-move-column-left nil arg))

;;;;; TODO org-table-move-column-right

;; ;; M-x org-table-move-column-right RET
;; (defun outshine-table-move-column-right(&optional arg)
;;   "Call outorg to trigger `org-table-move-column-right'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-move-column-right nil arg))

;;;;; TODO org-table-move-row

;; ;; M-x org-table-move-row RET
;; (defun outshine-table-move-row(&optional arg)
;;   "Call outorg to trigger `org-table-move-row'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-move-row nil arg))

;;;;; TODO org-table-move-row-down

;; ;; M-x org-table-move-row-down RET
;; (defun outshine-table-move-row-down(&optional arg)
;;   "Call outorg to trigger `org-table-move-row-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-move-row-down nil arg))

;;;;; TODO org-table-move-row-up

;; ;; M-x org-table-move-row-up RET
;; (defun outshine-table-move-row-up(&optional arg)
;;   "Call outorg to trigger `org-table-move-row-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-move-row-up nil arg))

;;;;; TODO org-table-next-field

;; ;; M-x org-table-next-field RET
;; (defun outshine-table-next-field(&optional arg)
;;   "Call outorg to trigger `org-table-next-field'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-next-field nil arg))

;;;;; TODO org-table-next-row

;; ;; M-x org-table-next-row RET
;; (defun outshine-table-next-row(&optional arg)
;;   "Call outorg to trigger `org-table-next-row'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-next-row nil arg))

;;;;; TODO org-table-overlay-coordinates

;; ;; M-x org-table-overlay-coordinates RET
;; (defun outshine-table-overlay-coordinates(&optional arg)
;;   "Call outorg to trigger `org-table-overlay-coordinates'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-overlay-coordinates nil arg))

;;;;; TODO org-table-paste-rectangle

;; ;; M-x org-table-paste-rectangle RET
;; (defun outshine-table-paste-rectangle(&optional arg)
;;   "Call outorg to trigger `org-table-paste-rectangle'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-paste-rectangle nil arg))

;;;;; TODO org-table-previous-field

;; ;; M-x org-table-previous-field RET
;; (defun outshine-table-previous-field(&optional arg)
;;   "Call outorg to trigger `org-table-previous-field'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-previous-field nil arg))

;;;;; TODO org-table-recalculate

;; ;; <menu-bar> <Tbl> <Calculate> <Recalculate line> (org-table-recalculate)
;; (defun outshine-table-recalculate(&optional arg)
;;   "Call outorg to trigger `org-table-recalculate'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-recalculate nil arg))

;;;;; TODO org-table-recalculate-buffer-tables

;; ;; M-x org-table-recalculate-buffer-tables RET
;; (defun outshine-table-recalculate-buffer-tables(&optional arg)
;;   "Call outorg to trigger `org-table-recalculate-buffer-tables'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-recalculate-buffer-tables nil arg))

;;;;; TODO org-table-rotate-recalc-marks

;; ;; C-#, <menu-bar> <Tbl> <Calculate> <Toggle Recalculate Mark> (org-table-rotate-recalc-marks)
;; (defun outshine-table-rotate-recalc-marks(&optional arg)
;;   "Call outorg to trigger `org-table-rotate-recalc-marks'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-rotate-recalc-marks nil arg))

;;;;; TODO org-table-show-reference

;; ;; M-x org-table-show-reference RET
;; (defun outshine-table-show-reference(&optional arg)
;;   "Call outorg to trigger `org-table-show-reference'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-show-reference nil arg))

;;;;; TODO org-table-sort-lines

;; ;; <menu-bar> <Tbl> <Row> <Sort lines in region> (org-table-sort-lines)
;; (defun outshine-table-sort-lines(&optional arg)
;;   "Call outorg to trigger `org-table-sort-lines'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-sort-lines nil arg))

;;;;; TODO org-table-sum

;; ;; C-c +, <menu-bar> <Tbl> <Calculate> <Sum Column/Rectangle> (org-table-sum)
;; (defun outshine-table-sum(&optional arg)
;;   "Call outorg to trigger `org-table-sum'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-sum nil arg))

;;;;; TODO org-table-toggle-coordinate-overlays

;; ;; C-c }, <menu-bar> <Tbl> <Show Col/Row Numbers> (org-table-toggle-coordinate-overlays)
;; (defun outshine-table-toggle-coordinate-overlays(&optional arg)
;;   "Call outorg to trigger `org-table-toggle-coordinate-overlays'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-toggle-coordinate-overlays nil arg))

;;;;; TODO org-table-toggle-formula-debugger

;; ;; C-c {, <menu-bar> <Tbl> <Debug Formulas> (org-table-toggle-formula-debugger)
;; (defun outshine-table-toggle-formula-debugger(&optional arg)
;;   "Call outorg to trigger `org-table-toggle-formula-debugger'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-toggle-formula-debugger nil arg))

;;;;; TODO org-table-transpose-table-at-point

;; ;; M-x org-table-transpose-table-at-point RET
;; (defun outshine-table-transpose-table-at-point(&optional arg)
;;   "Call outorg to trigger `org-table-transpose-table-at-point'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-transpose-table-at-point nil arg))

;;;;; TODO org-table-wrap-region

;; ;; <menu-bar> <Tbl> <Rectangle> <Fill Rectangle> (org-table-wrap-region)
;; (defun outshine-table-wrap-region(&optional arg)
;;   "Call outorg to trigger `org-table-wrap-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-table-wrap-region nil arg))

;;;;; TODO org-tags-sparse-tree

;; ;; M-x org-tags-sparse-tree RET;
;; ;;  its alias C-c \, <menu-bar> <Org> <Special views current file> <Tags/Property tree> (org-match-sparse-tree)
;; (defun outshine-tags-sparse-tree(&optional arg)
;;   "Call outorg to trigger `org-tags-sparse-tree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-tags-sparse-tree nil arg))

;;;;; TODO org-tags-view

;; ;; M-x org-tags-view RET
;; (defun outshine-tags-view(&optional arg)
;;   "Call outorg to trigger `org-tags-view'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-tags-view nil arg))

;;;;; TODO org-taskjuggler-export

;; ;; M-x org-taskjuggler-export RET
;; (defun outshine-taskjuggler-export(&optional arg)
;;   "Call outorg to trigger `org-taskjuggler-export'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-taskjuggler-export nil arg))

;;;;; TODO org-taskjuggler-export-and-process

;; ;; M-x org-taskjuggler-export-and-process RET
;; (defun outshine-taskjuggler-export-and-process(&optional arg)
;;   "Call outorg to trigger `org-taskjuggler-export-and-process'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-taskjuggler-export-and-process nil arg))

;;;;; TODO org-taskjuggler-export-process-and-open

;; ;; M-x org-taskjuggler-export-process-and-open RET
;; (defun outshine-taskjuggler-export-process-and-open(&optional arg)
;;   "Call outorg to trigger `org-taskjuggler-export-process-and-open'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-taskjuggler-export-process-and-open nil arg))

;;;;; TODO org-tbl-menu

;; ;; M-x org-tbl-menu RET
;; (defun outshine-tbl-menu(&optional arg)
;;   "Call outorg to trigger `org-tbl-menu'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-tbl-menu nil arg))

;;;;; TODO org-texinfo-convert-region-to-texinfo

;; ;; M-x org-texinfo-convert-region-to-texinfo RET
;; (defun outshine-texinfo-convert-region-to-texinfo(&optional arg)
;;   "Call outorg to trigger `org-texinfo-convert-region-to-texinfo'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-texinfo-convert-region-to-texinfo nil arg))

;;;;; DONE org-time-stamp
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:29]

;; C-c . (org-time-stamp)
(defun outshine-time-stamp (&optional arg)
  "Call outorg to trigger `org-time-stamp'."
  (interactive "P")
  (outshine-use-outorg
   (lambda ()
     (interactive)
     (if (not (org-on-heading-p))
	 (if arg (org-time-stamp arg) (org-time-stamp nil))
       (or
	(and
	 (re-search-forward org-element--timestamp-regexp nil t)
	 (ignore-errors (goto-char (match-beginning 0))))
	(and
	 (re-search-forward org-complex-heading-regexp nil t)
	 (ignore-errors (goto-char (match-end 4)))))
       (insert-char ? )
       	 (if arg (org-time-stamp arg) (org-time-stamp nil))))))

;; (defun outshine-time-stamp(&optional arg)
;;   "Call outorg to trigger `org-time-stamp'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-time-stamp nil arg))

;;;;; DONE org-time-stamp-inactive
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:27]

;; C-c ! (org-time-stamp-inactive)
(defun outshine-time-stamp-inactive (&optional arg)
  "Call outorg to trigger `org-time-stamp-inactive'."
  (interactive "P")
  (outshine-use-outorg
   (lambda ()
     (interactive)
     (if (not (org-on-heading-p))
	 	 (if arg
		     (org-time-stamp-inactive arg)
		   (org-time-stamp-inactive))
       (or
	(and
	 (re-search-forward org-element--timestamp-regexp nil t)
	 (ignore-errors (goto-char (match-beginning 0))))
	(and
	 (re-search-forward org-complex-heading-regexp nil t)
	 (ignore-errors (goto-char (match-end 4)))))
       (insert-char ? )
       (if arg
	   (org-time-stamp-inactive arg)
	 (org-time-stamp-inactive))))))

;; (defun outshine-time-stamp-inactive(&optional arg)
;;   "Call outorg to trigger `org-time-stamp-inactive'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-time-stamp-inactive nil arg))

;;;;; DONE org-timer
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:58]

;; C-c C-x . (org-timer)
(defun outshine-timer ()
  "Call outorg to trigger `org-timer'."
  (interactive)
  (outshine-use-outorg 'org-timer))

;;;;; TODO org-timer-change-times-in-region

;; ;; M-x org-timer-change-times-in-region RET
;; (defun outshine-timer-change-times-in-region(&optional arg)
;;   "Call outorg to trigger `org-timer-change-times-in-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timer-change-times-in-region nil arg))

;;;;; DONE org-timer-item
;;     - State "DONE"       from "NEXT"       [2016-02-07 So 19:56]

(defun outshine-timer-item()
  "Call outorg to trigger `org-timer-item'."
  (interactive "P")
  (outshine-use-outorg 'org-timer-item))

;;;;; DONE org-timer-set-timer
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:02]

;; C-c C-x ;	org-timer-set-timer
(defun outshine-timer-set-timer ()
  "Call outorg to trigger `org-timer-set-timer'."
  (interactive)
  (outshine-use-outorg 'org-timer-set-timer))

;; ;; FIXME obsolete?
;; ;; C-c C-x ; (org-timer-set-timer)
;; (defun outshine-timer-pause-or-continue (&optional arg)
;;   "Call outorg to trigger `org-timer-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timer-pause-or-continue nil arg))

;;;;; DONE org-timer-start
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:59]

;; C-c C-x 0 (org-timer-start)
(defun outshine-timer-start ()
  "Call outorg to trigger `org-timer-start'."
  (interactive)
  (outshine-use-outorg 'org-timer-start))

;;;;; TODO org-timestamp-down

;; ;; M-x org-timestamp-down RET
;; (defun outshine-timestamp-down(&optional arg)
;;   "Call outorg to trigger `org-timestamp-down'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timestamp-down nil arg))

;;;;; TODO org-timestamp-down-day

;; ;; M-x org-timestamp-down-day RET
;; (defun outshine-timestamp-down-day(&optional arg)
;;   "Call outorg to trigger `org-timestamp-down-day'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timestamp-down-day nil arg))

;;;;; TODO org-timestamp-up

;; ;; M-x org-timestamp-up RET
;; (defun outshine-timestamp-up(&optional arg)
;;   "Call outorg to trigger `org-timestamp-up'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timestamp-up nil arg))

;;;;; TODO org-timestamp-up-day

;; ;; M-x org-timestamp-up-day RET
;; (defun outshine-timestamp-up-day(&optional arg)
;;   "Call outorg to trigger `org-timestamp-up-day'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timestamp-up-day nil arg))

;;;;; DONE org-todo
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:23]

;; C-c C-t (org-todo)
(defun outshine-todo (&optional arg)
  "Call outorg to trigger `org-todo'."
  (interactive "P")
  (outshine-use-outorg 'org-todo nil arg))

;;;;; TODO org-todo-list

;; ;; <menu-bar> <Org> <TODO Lists> <Global TODO list> (org-todo-list)
;; (defun outshine-todo-list(&optional arg)
;;   "Call outorg to trigger `org-todo-list'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-todo-list nil arg))

;;;;; TODO org-todo-yesterday

;; ;; M-x org-todo-yesterday RET
;; (defun outshine-todo-yesterday(&optional arg)
;;   "Call outorg to trigger `org-todo-yesterday'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-todo-yesterday nil arg))

;;;;; DONE org-toggle-archive-tag
;;     - State "DONE"       from "TODO"       [2016-02-07 So 20:10]

;; C-c C-x a (org-toggle-archive-tag)
(defun outshine-toggle-archive-tag ()
  "Call outorg to trigger `org-toggle-archive-tag'."
  (interactive)
  (outshine-use-outorg 'org-toggle-archive-tag))

;;;;; DONE org-toggle-checkbox
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:42]

;; C-c C-x C-b (org-toggle-checkbox)
(defun outshine-toggle-checkbox (&optional arg)
  "Call outorg to trigger `org-toggle-checkbox'."
  (interactive "P")
  (outshine-use-outorg 'org-toggle-checkbox nil arg))

;;;;; DONE org-toggle-comment
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:33]

;; C-c ; (org-toggle-comment)
(defun outshine-toggle-comment ()
  "Call outorg to trigger `org-toggle-comment'."
  (interactive)
  (outshine-use-outorg 'org-toggle-comment))

;;;;; TODO org-toggle-custom-properties-visibility

;; ;; M-x org-toggle-custom-properties-visibility RET
;; (defun outshine-toggle-custom-properties-visibility(&optional arg)
;;   "Call outorg to trigger `org-toggle-custom-properties-visibility'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-custom-properties-visibility nil arg))

;;;;; DONE org-toggle-fixed-width
;;     - State "DONE"       from "TODO"       [2016-02-07 So 19:32]

;; C-c : (org-toggle-fixed-width)
(defun outshine-toggle-fixed-width ()
  "Call outorg to trigger `org-toggle-fixed-width'."
  (interactive)
  (outshine-use-outorg 'org-toggle-fixed-width))

;;;;; TODO org-toggle-heading

;; ;; M-x org-toggle-heading RET
;; (defun outshine-toggle-heading(&optional arg)
;;   "Call outorg to trigger `org-toggle-heading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-heading nil arg))

;;;;; TODO org-toggle-inline-images

;; ;; C-c C-x C-v (org-toggle-inline-images)
;; (defun outshine-toggle-inline-images(&optional arg)
;;   "Call outorg to trigger `org-toggle-inline-images'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-inline-images nil arg))

;;;;; TODO org-toggle-item

;; ;; M-x org-toggle-item RET
;; (defun outshine-toggle-item(&optional arg)
;;   "Call outorg to trigger `org-toggle-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-item nil arg))

;;;;; TODO org-toggle-latex-fragment

;; ;; C-c C-x C-l (org-toggle-latex-fragment);
;; ;;  its alias M-x org-preview-latex-fragment RET
;; (defun outshine-toggle-latex-fragment(&optional arg)
;;   "Call outorg to trigger `org-toggle-latex-fragment'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-latex-fragment nil arg))

;;;;; TODO org-toggle-link-display

;; ;; <menu-bar> <Org> <Hyperlinks> <Descriptive Links>, <menu-bar> <Org> <Hyperlinks> <Literal Links> (org-toggle-link-display)
;; (defun outshine-toggle-link-display(&optional arg)
;;   "Call outorg to trigger `org-toggle-link-display'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-link-display nil arg))

;;;;; TODO org-toggle-ordered-property

;; ;; C-c C-x o, <menu-bar> <Org> <TODO Lists> <Do Children sequentially>, <menu-bar> <Org> <TODO Lists> <Do Children parallel> (org-toggle-ordered-property)
;; (defun outshine-toggle-ordered-property(&optional arg)
;;   "Call outorg to trigger `org-toggle-ordered-property'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-ordered-property nil arg))

;;;;; TODO org-toggle-pretty-entities

;; ;; C-c C-x \ (org-toggle-pretty-entities)
;; (defun outshine-toggle-pretty-entities(&optional arg)
;;   "Call outorg to trigger `org-toggle-pretty-entities'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-pretty-entities nil arg))

;;;;; TODO org-toggle-sticky-agenda

;; ;; M-x org-toggle-sticky-agenda RET
;; (defun outshine-toggle-sticky-agenda(&optional arg)
;;   "Call outorg to trigger `org-toggle-sticky-agenda'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-sticky-agenda nil arg))

;;;;; TODO org-toggle-tags-groups

;; ;; C-c C-x q (org-toggle-tags-groups)
;; (defun outshine-toggle-tags-groups(&optional arg)
;;   "Call outorg to trigger `org-toggle-tags-groups'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-tags-groups nil arg))

;;;;; TODO org-toggle-time-stamp-overlays

;; ;; C-c C-x C-t, <menu-bar> <Org> <Dates and Scheduling> <Custom time format> (org-toggle-time-stamp-overlays)
;; (defun outshine-toggle-time-stamp-overlays(&optional arg)
;;   "Call outorg to trigger `org-toggle-time-stamp-overlays'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-time-stamp-overlays nil arg))

;;;;; TODO org-toggle-timestamp-type

;; ;; M-x org-toggle-timestamp-type RET
;; (defun outshine-toggle-timestamp-type(&optional arg)
;;   "Call outorg to trigger `org-toggle-timestamp-type'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-timestamp-type nil arg))

;;;;; TODO org-transpose-element

;; ;; C-M-t (org-transpose-element)
;; (defun outshine-transpose-element(&optional arg)
;;   "Call outorg to trigger `org-transpose-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-transpose-element nil arg))

;;;;; TODO org-transpose-words

;; ;; M-t (org-transpose-words)
;; (defun outshine-transpose-words(&optional arg)
;;   "Call outorg to trigger `org-transpose-words'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-transpose-words nil arg))

;;;;; TODO org-tree-to-indirect-buffer

;; ;; C-c C-x b, <menu-bar> <Org> <Show/Hide> <Subtree to indirect buffer> (org-tree-to-indirect-buffer)
;; (defun outshine-tree-to-indirect-buffer(&optional arg)
;;   "Call outorg to trigger `org-tree-to-indirect-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-tree-to-indirect-buffer nil arg))

;;;;; TODO org-unescape-code-in-region

;; ;; M-x org-unescape-code-in-region RET
;; (defun outshine-unescape-code-in-region(&optional arg)
;;   "Call outorg to trigger `org-unescape-code-in-region'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-unescape-code-in-region nil arg))

;;;;; TODO org-unindent-buffer

;; ;; M-x org-unindent-buffer RET
;; (defun outshine-unindent-buffer(&optional arg)
;;   "Call outorg to trigger `org-unindent-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-unindent-buffer nil arg))

;;;;; TODO org-up-element

;; ;; C-c C-^ (org-up-element)
;; (defun outshine-up-element(&optional arg)
;;   "Call outorg to trigger `org-up-element'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-up-element nil arg))

;;;;; TODO org-update-all-dblocks

;; ;; M-x org-update-all-dblocks RET
;; (defun outshine-update-all-dblocks(&optional arg)
;;   "Call outorg to trigger `org-update-all-dblocks'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-update-all-dblocks nil arg))

;;;;; TODO org-update-checkbox-count

;; ;; M-x org-update-checkbox-count RET
;; (defun outshine-update-checkbox-count(&optional arg)
;;   "Call outorg to trigger `org-update-checkbox-count'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-update-checkbox-count nil arg))

;;;;; TODO org-update-dblock

;; ;; M-x org-update-dblock RET
;; (defun outshine-update-dblock(&optional arg)
;;   "Call outorg to trigger `org-update-dblock'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-update-dblock nil arg))

;;;;; TODO org-update-radio-target-regexp

;; ;; M-x org-update-radio-target-regexp RET
;; (defun outshine-update-radio-target-regexp(&optional arg)
;;   "Call outorg to trigger `org-update-radio-target-regexp'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-update-radio-target-regexp nil arg))

;;;;; TODO org-update-statistics-cookies

;; ;; C-c # (org-update-statistics-cookies)
;; (defun outshine-update-statistics-cookies(&optional arg)
;;   "Call outorg to trigger `org-update-statistics-cookies'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-update-statistics-cookies nil arg))

;;;;; TODO org-version

;; ;; <menu-bar> <Org> <Documentation> <Show Version> (org-version)
;; (defun outshine-version(&optional arg)
;;   "Call outorg to trigger `org-version'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-version nil arg))

;;;;; TODO org-w3m-copy-for-org-mode

;; ;; M-x org-w3m-copy-for-org-mode RET
;; (defun outshine-w3m-copy-for-org-mode(&optional arg)
;;   "Call outorg to trigger `org-w3m-copy-for-org-mode'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-w3m-copy-for-org-mode nil arg))

;;;;; TODO org-watchdoc-add-target

;; ;; M-x org-watchdoc-add-target RET
;; (defun outshine-watchdoc-add-target(&optional arg)
;;   "Call outorg to trigger `org-watchdoc-add-target'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-watchdoc-add-target nil arg))

;;;;; TODO org-watchdoc-propagate-changes

;; ;; M-x org-watchdoc-propagate-changes RET
;; (defun outshine-watchdoc-propagate-changes(&optional arg)
;;   "Call outorg to trigger `org-watchdoc-propagate-changes'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-watchdoc-propagate-changes nil arg))

;;;;; TODO org-watchdoc-remove-target

;; ;; M-x org-watchdoc-remove-target RET
;; (defun outshine-watchdoc-remove-target(&optional arg)
;;   "Call outorg to trigger `org-watchdoc-remove-target'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-watchdoc-remove-target nil arg))

;;;;; TODO org-watchdoc-set-md5

;; ;; M-x org-watchdoc-set-md5 RET
;; (defun outshine-watchdoc-set-md5(&optional arg)
;;   "Call outorg to trigger `org-watchdoc-set-md5'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-watchdoc-set-md5 nil arg))

;;;;; TODO org-yank

;; ;; C-y (org-yank)
;; (defun outshine-yank(&optional arg)
;;   "Call outorg to trigger `org-yank'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-yank nil arg))
;;; Key Bindings
;;;; Other Keybindings

;;;;; [Prefix]

;; Put this in your init.el. The prefix can only be changed before
;; outline (minor) mode is loaded!

;; #+begin_example
;;  (defvar outline-minor-mode-prefix "\M-#")
;; #+end_example

;;;;; [Subprefix]

;; Set the outline-minor-mode-prefix key in your init-file
;; before loading outline-mode
(let ((map (lookup-key outline-minor-mode-map outline-minor-mode-prefix)))
  ;; define sub-prefix
  ;; (define-key map (kbd "C-v") nil)
  (define-key map (kbd "M-+") nil)
  ;; (define-key map (kbd "C-x") nil)
  (define-key map (kbd "M-#") nil)

;;;;; [M-# Punctuation]

  (define-key map (kbd "#") 'outorg-edit-as-org)
  (define-key map (kbd "SPC") 'outshine-table-blank-field)
  (define-key map (kbd "!") 'outshine-time-stamp-inactive)
  (define-key map (kbd "$") 'outshine-archive-subtree)
  (define-key map (kbd "%") 'outshine-mark-ring-push)
  (define-key map (kbd "&") 'outshine-mark-ring-goto)
  (define-key map (kbd "'") 'outshine-edit-special)
  (define-key map (kbd "*") 'outshine-ctrl-c-star)
  (define-key map (kbd "+") 'outshine-table-sum)
  (define-key map (kbd ",") 'outshine-priority)
  (define-key map (kbd "-") 'outshine-ctrl-c-minus)
  (define-key map (kbd ".") 'outshine-time-stamp)
  ;; (define-key map (kbd "/") 'outshine-sparse-tree)
  (define-key map (kbd ":") 'outshine-toggle-fixed-width)
  (define-key map (kbd ";") 'outshine-toggle-comment)
  (define-key map (kbd "<") 'outshine-date-from-calendar)
  (define-key map (kbd "=") 'outshine-table-eval-formula)
  (define-key map (kbd ">") 'outshine-goto-calendar)
  (define-key map (kbd "?") 'outshine-table-field-info)
  (define-key map (kbd "@") 'outshine-mark-subtree)
  (define-key map (kbd "\\") 'outshine-match-sparse-tree)
  (define-key map (kbd "^") 'outshine-sort-entries)
  (define-key map (kbd "`") 'outshine-table-edit-field)
  (define-key map (kbd "{") 'outshine-table-toggle-formula-debugger)
  (define-key map (kbd "|")
    'outshine-table-create-or-convert-from-region)
  (define-key map (kbd "}")
    'outshine-table-toggle-coordinate-overlays)
  (define-key map (kbd "~") 'outshine-table-create-with-table.el)

;;;;; [M-# Letter]

  ;; (outshine-define-key-with-fallback
  ;;  outline-minor-mode-map (kbd "J")
  ;;  (outline-hide-more) (outline-on-heading-p))
  ;; (outshine-define-key-with-fallback
  ;;  outline-minor-mode-map (kbd "L")
  ;;  (outline-show-more) (outline-on-heading-p))
  ;; (define-key map (kbd "I") 'outline-previous-visible-heading)
  ;; (define-key map (kbd "K") 'outline-next-visible-heading)

;;;;; [M-# letter]


;;;;; [M-# M-Punctuation]

  ;; (define-key map (kbd "C-^") 'outshine-up-element)
  ;; (define-key map (kbd "M-^") 'outshine-up-element)

  ;; (define-key map (kbd "C-_") 'outshine-down-element)
  ;; (define-key map (kbd "M-_") 'outshine-down-element)


  ;; (define-key map (kbd "C-x C-M-v")
  ;;   'outshine-redisplay-inline-images)
  (define-key map (kbd "M-# C-M-v")
    'outshine-redisplay-inline-images)
  ;; (define-key map (kbd "C-x RET g") 'outshine-mobile-pull)
  (define-key map (kbd "M-# RET g") 'outshine-mobile-pull)
  ;; (define-key map (kbd "C-x RET p") 'outshine-mobile-push)
  (define-key map (kbd "M-# RET p") 'outshine-mobile-push)
  ;; (define-key map (kbd "C-c C-x RET g") 'outshine-mobile-pull)
  ;; (define-key map (kbd "C-c C-x RET p") 'outshine-mobile-push)


;;;;; [M-# M-letter]

  ;; (define-key map (kbd "C-t") 'hide-body)
  (define-key map (kbd "M-t") 'hide-body)
  ;; (define-key map (kbd "C-a") 'show-all)
  (define-key map (kbd "M-a") 'show-all)
  ;; (define-key map (kbd "C-c") 'hide-entry)
  (define-key map (kbd "M-c") 'hide-entry)
  ;; (define-key map (kbd "C-e") 'show-entry)
  (define-key map (kbd "M-e") 'show-entry)
  ;; (define-key map (kbd "C-l") 'hide-leaves)
  (define-key map (kbd "M-l") 'hide-leaves)
  ;; (define-key map (kbd "C-k") 'show-branches)
  (define-key map (kbd "M-k") 'show-branches)
  ;; (define-key map (kbd "C-q") 'outline-hide-sublevels)
  (define-key map (kbd "M-q") 'outline-hide-sublevels)
  ;; (define-key map (kbd "C-o") 'outline-hide-other)
  (define-key map (kbd "M-o") 'outline-hide-other)
  ;; (define-key map (kbd "C-u") 'outline-up-heading)
  (define-key map (kbd "M-u") 'outline-up-heading)
  ;; (define-key map (kbd "C-+") 'outshine-imenu-with-navi-regexp)
  ;; (define-key map (kbd "M-+") 'outshine-imenu-with-navi-regexp)
  ;; (define-key map (kbd "C-p") 'outshine-imenu)
  (define-key map (kbd "M-p") 'outshine-imenu)
  ;; USE OUTORG TO CALL ORG
  ;; 1st binding for 'C-c' prefix, 2nd for 'M-#' prefix
  ;; (define-key map (kbd "C-j") 'outshine-goto)
  ;; (define-key map (kbd "M-j") 'outshine-goto)
  (define-key map (kbd "M-j") 'outshine-imenu)
  ;; (define-key map (kbd "C-o") 'outshine-open-at-point)
  (define-key map (kbd "M-o") 'outshine-open-at-point)
  ;; (define-key map (kbd "C-a") 'outshine-attach)
  (define-key map (kbd "M-a") 'outshine-attach)
  ;; (define-key map (kbd "C-c") 'outshine-ctrl-c-ctrl-c)
  (define-key map (kbd "M-c") 'outshine-ctrl-c-ctrl-c)
  ;; (define-key map (kbd "C-d") 'outshine-deadline)
  (define-key map (kbd "M-d") 'outshine-deadline)
  ;; (define-key map (kbd "C-e") 'outshine-export-dispatch)
  (define-key map (kbd "M-e") 'outshine-export-dispatch)
  ;; (define-key map (kbd "C-k")
  ;;   'outshine-kill-note-or-show-branches)
  (define-key map (kbd "M-k") 'outshine-kill-note-or-show-branches)
  ;; (define-key map (kbd "C-l") 'outshine-insert-link)
  (define-key map (kbd "M-l") 'outshine-insert-link) ; FIXME
  ;; (define-key map (kbd "RET") 'outshine-ctrl-c-ret)
  ;; (define-key map (kbd "C-q") 'outshine-set-tags-command)
  (define-key map (kbd "M-q") 'outshine-set-tags-command)
  ;; (define-key map (kbd "C-r") 'outshine-reveal)
  (define-key map (kbd "M-r") 'outshine-reveal)
  ;; (define-key map (kbd "C-s") 'outshine-schedule)
  (define-key map (kbd "M-s") 'outshine-schedule)
  ;; (define-key map (kbd "C-t") 'outshine-todo)
  (define-key map (kbd "M-t") 'outshine-todo)
  ;; (define-key map (kbd "C-v") 'Prefix Command)
  ;; (define-key map (kbd "C-w") 'outshine-refile)
  ;; (define-key map (kbd "M-w") 'outshine-refile)
  (define-key map (kbd "M-w") 'outshine-imenu)
  ;; (define-key map (kbd "C-x") 'Prefix Command)
  ;; (define-key map (kbd "C-y") 'outshine-evaluate-time-range)
  (define-key map (kbd "M-y") 'outshine-evaluate-time-range)
  ;; (define-key map (kbd "C-z") 'outshine-add-note)
  (define-key map (kbd "M-z") 'outshine-add-note)
  ;; (define-key map (kbd "ESC") 'Prefix Command)
  ;; (define-key map (kbd "C-*") 'outshine-list-make-subtree)
  (define-key map (kbd "M-*") 'outshine-list-make-subtree)
  (define-key map (kbd "C-M-l") 'outshine-insert-all-links)
  (define-key map (kbd "M-b") 'outshine-previous-block)
  (define-key map (kbd "M-f") 'outshine-next-block)
  ;; FIXME overrides keybinding
  (define-key map (kbd "M-l") 'outshine-insert-last-stored-link)
  ;; C-c M-o		tj/mail-subtree
  (define-key map (kbd "M-w") 'outshine-copy)

  ;; (define-key map (kbd "C-b")
  ;;   'outshine-backward-heading-same-level)
  ;; (define-key map (kbd "M-b")
  ;;   'outshine-backward-heading-same-level)

  ;; (define-key map (kbd "C-f")
  ;;   'outshine-forward-heading-same-level)
  ;; (define-key map (kbd "M-f")
  ;;   'outshine-forward-heading-same-level)


;;;;; [M-# M-# Punctuation]

  (define-key map (kbd "M-# #") 'outshine-update-statistics-cookies)
  (define-key map (kbd "M-# +")
    'outorg-edit-comments-and-propagate-changes)
  ;; (define-key map (kbd "C-x !") 'outshine-reload)
  (define-key map (kbd "M-# !") 'outshine-reload)
  ;; (define-key map (kbd "C-x [") 'outshine-reftex-citation)
  (define-key map (kbd "M-# [") 'outshine-reftex-citation)
  ;; (define-key map (kbd "C-x \\")
  ;;   'outshine-toggle-pretty-entities)
  (define-key map (kbd "M-# \\") 'outshine-toggle-pretty-entities)
  ;; (define-key map (kbd "C-x _") 'outshine-timer-stop)
  (define-key map (kbd "M-# _") 'outshine-timer-stop)
  ;; (define-key map (kbd "C-x ,")
  ;;   'outshine-timer-pause-or-continue)
  (define-key map (kbd "M-# ,") 'outshine-timer-pause-or-continue)
  ;; (define-key map (kbd "C-x -") 'outshine-timer-item)
  (define-key map (kbd "M-# -") 'outshine-timer-item)
  ;; (define-key map (kbd "C-x .") 'outshine-timer)
  (define-key map (kbd "M-# .") 'outshine-timer)
  ;; (define-key map (kbd "C-x 0") 'outshine-timer-start)
  (define-key map (kbd "M-# 0") 'outshine-timer-start)
  ;; (define-key map (kbd "C-x :") 'outshine-timer-cancel-timer)
  (define-key map (kbd "M-# :") 'outshine-timer-cancel-timer)
  ;; (define-key map (kbd "C-x ;") 'outshine-timer-set-timer)
  (define-key map (kbd "M-# ;") 'outshine-timer-set-timer)
  ;; (define-key map (kbd "C-x <")
  ;;   'outshine-agenda-set-restriction-lock)
  (define-key map (kbd "M-# <")
    'outshine-agenda-set-restriction-lock)
  ;; (define-key map (kbd "C-x >")
  ;;   'outshine-agenda-remove-restriction-lock)
  (define-key map (kbd "M-# >")
    'outshine-agenda-remove-restriction-lock)
  ;; (define-key map (kbd "C-x TAB") 'outshine-clock-in)
  (define-key map (kbd "M-# TAB") 'outshine-clock-in)

;;;;; [M-# M-# Letter]

  ;; (define-key map (kbd "C-x A")
  ;;   'outshine-archive-to-archive-sibling)
  (define-key map (kbd "M-# A")
    'outshine-archive-to-archive-sibling)
  ;; (define-key map (kbd "C-x D") 'outshine-shiftmetadown)
  (define-key map (kbd "M-# D") 'outshine-shiftmetadown)
  ;; (define-key map (kbd "C-x E") 'outshine-inc-effort)
  (define-key map (kbd "M-# E") 'outshine-inc-effort)
  ;; (define-key map (kbd "C-x G") 'outshine-feed-goto-inbox)
  (define-key map (kbd "M-# G") 'outshine-feed-goto-inbox)
  ;; (define-key map (kbd "C-x L") 'outshine-shiftmetaleft)
  (define-key map (kbd "M-# L") 'outshine-shiftmetaleft)
  ;; (define-key map (kbd "C-x M") 'outshine-insert-todo-heading)
  (define-key map (kbd "M-# M") 'outshine-insert-todo-heading)
  ;; (define-key map (kbd "C-x P") 'outshine-set-property-and-value)
  (define-key map (kbd "M-# P") 'outshine-set-property-and-value)
  ;; (define-key map (kbd "C-x R") 'outshine-shiftmetaright)
  (define-key map (kbd "M-# R") 'outshine-shiftmetaright)
  ;; (define-key map (kbd "C-x U") 'outshine-shiftmetaup)
  (define-key map (kbd "M-# U") 'outshine-shiftmetaup)

;;;;; [M-# M-# letter]

  ;; (define-key map (kbd "C-x a") 'outshine-toggle-archive-tag)
  (define-key map (kbd "M-# a") 'outshine-toggle-archive-tag)
  ;; (define-key map (kbd "C-x b")
  ;;   'outshine-tree-to-indirect-buffer)
  (define-key map (kbd "M-# b") 'outshine-tree-to-indirect-buffer)
  ;; (define-key map (kbd "C-x c")
  ;;   'outshine-clone-subtree-with-time-shift)
  (define-key map (kbd "M-# c") 'outshine-clone-subtree-with-time-shift)
  ;; (define-key map (kbd "C-x d") 'outshine-insert-drawer)
  (define-key map (kbd "M-# d") 'outshine-insert-drawer)
  ;; (define-key map (kbd "C-x e") 'outshine-set-effort)
  (define-key map (kbd "M-# e") 'outshine-set-effort)
  ;; (define-key map (kbd "C-x f") 'outshine-footnote-action)
  (define-key map (kbd "M-# f") 'outshine-footnote-action)
  ;; (define-key map (kbd "C-x g") 'outshine-feed-update-all)
  (define-key map (kbd "M-# g") 'outshine-feed-update-all)
  ;; (define-key map (kbd "C-x i") 'outshine-insert-columns-dblock)
  (define-key map (kbd "M-# i") 'outshine-insert-columns-dblock)
  ;; (define-key map (kbd "C-x l") 'outshine-metaleft)
  (define-key map (kbd "M-# l") 'outshine-metaleft)
  ;; (define-key map (kbd "C-x m") 'outshine-meta-return)
  (define-key map (kbd "M-# m") 'outshine-meta-return)
  ;; (define-key map (kbd "C-x o")
  ;;   'outshine-toggle-ordered-property)
  (define-key map (kbd "M-# o") 'outshine-toggle-ordered-property)
  ;; (define-key map (kbd "C-x p") 'outshine-set-property)
  (define-key map (kbd "M-# p") 'outshine-set-property)
  ;; (define-key map (kbd "C-x q") 'outshine-toggle-tags-groups)
  (define-key map (kbd "M-# q") 'outshine-toggle-tags-groups)
  ;; (define-key map (kbd "C-x r") 'outshine-metaright)
  (define-key map (kbd "M-# r") 'outshine-metaright)
  ;; (define-key map (kbd "C-x u") 'outshine-metaup)
  (define-key map (kbd "M-# u") 'outshine-metaup)
  ;; (define-key map (kbd "C-x v") 'outshine-copy-visible)
  (define-key map (kbd "M-# v") 'outshine-copy-visible)

;;;;; [M-# M-# M-letter]

  ;; (define-key map (kbd "C-x C-a")
  ;;   'outshine-archive-subtree-default)
  (define-key map (kbd "M-# M-a") 'outshine-archive-subtree-default)
  ;; (define-key map (kbd "C-x C-b") 'outshine-toggle-checkbox)
  (define-key map (kbd "M-# M-b") 'outshine-toggle-checkbox)
  ;; (define-key map (kbd "C-x C-c") 'outshine-columns)
  (define-key map (kbd "M-# M-c") 'outshine-columns)
  ;; (define-key map (kbd "C-x C-d") 'outshine-clock-display)
  (define-key map (kbd "M-# M-d") 'outshine-clock-display)
  ;; (define-key map (kbd "C-x C-f") 'org-emphasize)
  (define-key map (kbd "M-# M-f") 'org-emphasize)
  ;; (define-key map (kbd "C-x C-j") 'outshine-clock-goto)
  (define-key map (kbd "M-# M-j") 'outshine-clock-goto)
  ;; (define-key map (kbd "C-x C-l")
  ;;   'outshine-preview-latex-fragment)
  (define-key map (kbd "M-# M-l") 'outshine-preview-latex-fragment)
  ;; (define-key map (kbd "C-x C-n") 'outshine-next-link)
  (define-key map (kbd "M-# M-n") 'outshine-next-link)
  ;; (define-key map (kbd "C-x C-o") 'outshine-clock-out)
  (define-key map (kbd "M-# M-o") 'outshine-clock-out)
  ;; (define-key map (kbd "C-x C-p") 'outshine-previous-link)
  (define-key map (kbd "M-# M-p") 'outshine-previous-link)
  ;; (define-key map (kbd "C-x C-q") 'outshine-clock-cancel)
  (define-key map (kbd "M-# M-q") 'outshine-clock-cancel)
  ;; (define-key map (kbd "C-x C-r") 'outshine-clock-report)
  (define-key map (kbd "M-# M-r") 'outshine-clock-report)
  ;; (define-key map (kbd "C-x C-s")
  ;;   'outshine-advertized-archive-subtree)
  (define-key map (kbd "M-# M-s")
    'outshine-advertized-archive-subtree)
  ;; (define-key map (kbd "C-x C-t")
  ;;   'outshine-toggle-time-stamp-overlays)
  (define-key map (kbd "M-# M-t")
    'outshine-toggle-time-stamp-overlays)
  ;; (define-key map (kbd "C-x C-u") 'outshine-dblock-update)
  (define-key map (kbd "M-# M-u") 'outshine-dblock-update)
  ;; (define-key map (kbd "C-x C-v") 'outshine-toggle-inline-images)
  (define-key map (kbd "M-# M-v") 'outshine-toggle-inline-images)
  ;; (define-key map (kbd "C-x C-k") 'outshine-cut-special)
  (define-key map (kbd "M-# M-k") 'outshine-cut-special)
  ;; (define-key map (kbd "C-x M-w") 'outshine-copy-special)
  (define-key map (kbd "M-# M-w") 'outshine-copy-special)
  ;; (define-key map (kbd "C-x C-x") 'outshine-clock-in-last)
  (define-key map (kbd "M-# M-x") 'outshine-clock-in-last)
  ;; (define-key map (kbd "C-x C-y") 'outshine-paste-special)
  (define-key map (kbd "M-# M-y") 'outshine-paste-special)
  ;; (define-key map (kbd "C-x C-z") 'outshine-resolve-clocks)
  (define-key map (kbd "M-# M-z") 'outshine-resolve-clocks)

;;;;; [M-# M-+ Punctuation]

  ;; (define-key map (kbd "C-v TAB")
  ;;   'outshine-babel-view-src-block-info)
  (define-key map (kbd "M-+ TAB")
    'outshine-babel-view-src-block-info)

;;;;; [M-# M-+ Letter]

  ;; (define-key map (kbd "C-v I") 'outshine-babel-view-src-block-info)
  (define-key map (kbd "M-+ I") 'outshine-babel-view-src-block-info)

;;;;; [M-# M-+ letter]

  ;; (define-key map (kbd "C-v a") 'outshine-babel-sha1-hash)
  (define-key map (kbd "M-+ a") 'outshine-babel-sha1-hash)
  ;; (define-key map (kbd "C-v b") 'outshine-babel-execute-buffer)
  (define-key map (kbd "M-+ b") 'outshine-babel-execute-buffer)
  ;; (define-key map (kbd "C-v c") 'outshine-babel-check-src-block)
  (define-key map (kbd "M-+ c") 'outshine-babel-check-src-block)
  ;; (define-key map (kbd "C-v d") 'outshine-babel-demarcate-block)
  (define-key map (kbd "M-+ d") 'outshine-babel-demarcate-block)
  ;; (define-key map (kbd "C-v e") 'outshine-babel-execute-maybe)
  (define-key map (kbd "M-+ e") 'outshine-babel-execute-maybe)
  ;; (define-key map (kbd "C-v f") 'outshine-babel-tangle-file)
  (define-key map (kbd "M-+ f") 'outshine-babel-tangle-file)
  ;; (define-key map (kbd "C-v g") 'outshine-babel-goto-named-src-block)
  (define-key map (kbd "M-+ g") 'outshine-babel-goto-named-src-block)
  ;; (define-key map (kbd "C-v h") 'outshine-babel-describe-bindings)
  (define-key map (kbd "M-+ h") 'outshine-babel-describe-bindings)
  ;; (define-key map (kbd "C-v i") 'outshine-babel-lob-ingest)
  (define-key map (kbd "M-+ i") 'outshine-babel-lob-ingest)
  ;; (define-key map (kbd "C-v j") 'outshine-babel-insert-header-arg)
  (define-key map (kbd "M-+ j") 'outshine-babel-insert-header-arg)
  ;; (define-key map (kbd "C-v k") 'outshine-babel-remove-result-one-or-many)
  (define-key map (kbd "M-+ k") 'outshine-babel-remove-result-one-or-many)
  ;; (define-key map (kbd "C-v l") 'outshine-babel-load-in-session)
  (define-key map (kbd "M-+ l") 'outshine-babel-load-in-session)
  ;; (define-key map (kbd "C-v n") 'outshine-babel-next-src-block)
  (define-key map (kbd "M-+ n") 'outshine-babel-next-src-block)
  ;; (define-key map (kbd "C-v o") 'outshine-babel-open-src-block-result)
  (define-key map (kbd "M-+ o") 'outshine-babel-open-src-block-result)
  ;; (define-key map (kbd "C-v p") 'outshine-babel-previous-src-block)
  (define-key map (kbd "M-+ p") 'outshine-babel-previous-src-block)
  ;; (define-key map (kbd "C-v r") 'outshine-babel-goto-named-result)
  (define-key map (kbd "M-+ r") 'outshine-babel-goto-named-result)
  ;; (define-key map (kbd "C-v s") 'outshine-babel-execute-subtree)
  (define-key map (kbd "M-+ s") 'outshine-babel-execute-subtree)
  ;; (define-key map (kbd "C-v t") 'outshine-babel-tangle)
  (define-key map (kbd "M-+ t") 'outshine-babel-tangle)
  ;; (define-key map (kbd "C-v u") 'outshine-babel-goto-src-block-head)
  (define-key map (kbd "M-+ u") 'outshine-babel-goto-src-block-head)
  ;; (define-key map (kbd "C-v v") 'outshine-babel-expand-src-block)
  (define-key map (kbd "M-+ v") 'outshine-babel-expand-src-block)
  ;; (define-key map (kbd "C-v x") 'outshine-babel-do-key-sequence-in-edit-buffer)
  (define-key map (kbd "M-+ x") 'outshine-babel-do-key-sequence-in-edit-buffer)
  ;; (define-key map (kbd "C-v z") 'outshine-babel-switch-to-session-with-code)
  (define-key map (kbd "M-+ z") 'outshine-babel-switch-to-session-with-code)

;;;;; [M-# M-+ M-Punctuation]

  ;; (define-key map (kbd "C-v '")
  ;;   'outorg-edit-comments-and-propagate-changes)
  (define-key map (kbd "M-# M-+")
    'outorg-edit-comments-and-propagate-changes)

;;;;; [M-# M-+ M-letter]

  ;; (define-key map (kbd "C-v C-a") 'outshine-babel-sha1-hash)
  (define-key map (kbd "M-+ M-a") 'outshine-babel-sha1-hash)
  ;; (define-key map (kbd "C-v C-b") 'outshine-babel-execute-buffer)
  (define-key map (kbd "M-+ M-b") 'outshine-babel-execute-buffer)
  ;; (define-key map (kbd "C-v C-c")
  ;;   'outshine-babel-check-src-block)
  (define-key map (kbd "M-+ M-c") 'outshine-babel-check-src-block)
  ;; (define-key map (kbd "C-v C-d")
  ;;   'outshine-babel-demarcate-block)
  (define-key map (kbd "M-+ M-d") 'outshine-babel-demarcate-block)
  ;; (define-key map (kbd "C-v C-e") 'outshine-babel-execute-maybe)
  (define-key map (kbd "M-+ M-e") 'outshine-babel-execute-maybe)
  ;; (define-key map (kbd "C-v C-f") 'outshine-babel-tangle-file)
  (define-key map (kbd "M-+ M-f") 'outshine-babel-tangle-file)
  ;; (define-key map (kbd "C-v C-j")
  ;;  'outshine-babel-insert-header-arg)
  (define-key map (kbd "M-+ M-j") 'outshine-babel-insert-header-arg)
  ;; (define-key map (kbd "C-v C-l") 'outshine-babel-load-in-session)
  (define-key map (kbd "M-+ M-l") 'outshine-babel-load-in-session)
  ;; (define-key map (kbd "C-v C-n") 'outshine-babel-next-src-block)
  (define-key map (kbd "M-+ M-n") 'outshine-babel-next-src-block)
  ;; (define-key map (kbd "C-v C-o") 'outshine-babel-open-src-block-result)
  (define-key map (kbd "M-+ M-o") 'outshine-babel-open-src-block-result)
  ;; (define-key map (kbd "C-v C-p") 'outshine-babel-previous-src-block)
  (define-key map (kbd "M-+ M-p") 'outshine-babel-previous-src-block)
  ;; (define-key map (kbd "C-v C-r") 'outshine-babel-goto-named-result)
  (define-key map (kbd "M-+ M-r") 'outshine-babel-goto-named-result)
  ;; (define-key map (kbd "C-v C-s") 'outshine-babel-execute-subtree)
  (define-key map (kbd "M-+ M-s") 'outshine-babel-execute-subtree)
  ;; (define-key map (kbd "C-v C-t") 'outshine-babel-tangle)
  (define-key map (kbd "M-+ M-t") 'outshine-babel-tangle)
  ;; (define-key map (kbd "C-v C-u") 'outshine-babel-goto-src-block-head)
  (define-key map (kbd "M-+ M-u") 'outshine-babel-goto-src-block-head)
  ;; (define-key map (kbd "C-v C-v") 'outshine-babel-expand-src-block)
  (define-key map (kbd "M-+ M-v") 'outshine-babel-expand-src-block)
  ;; (define-key map (kbd "C-v C-x") 'outshine-babel-do-key-sequence-in-edit-buffer)
  (define-key map (kbd "M-+ M-x") 'outshine-babel-do-key-sequence-in-edit-buffer)
  ;; (define-key map (kbd "C-v C-z") 'outshine-babel-switch-to-session)
  (define-key map (kbd "M-+ M-z") 'outshine-babel-switch-to-session)

  ;; (define-key map (kbd "C-v C-M-h") 'outshine-babel-mark-block)
  (define-key map (kbd "M-+ C-M-h") 'outshine-babel-mark-block)

)

;; (define-key map (kbd "<up>") 'outshine-shiftup)
;; (define-key map (kbd "<down>") 'outshine-shiftdown)
;; C-c C-x <left>	org-shiftcontrolleft
;; C-c C-x <right>      org-shiftcontrolright

;;; Run Hooks and Provide
(provide 'outshine-org-cmds)

;; Local Variables:
;; coding: utf-8
;; ispell-local-dictionary: "en_US"
;; indent-tabs-mode: nil
;; End:

;;; outshine-org-cmds.el ends here
