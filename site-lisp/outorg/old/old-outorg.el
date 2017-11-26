;; * outorg.el --- Org-style outline navigation and comment editing

;; ** Copyright

;; Copyright (C) 2013 Thorsten Jolitz
;; This file is not (yet) part of GNU Emacs

;; Author: Thorsten Jolitz  (format "tjolitz%sgmail%s" "@" ".com")

;; ** Credits

;; This library is based on, or rather an extension of, Per Abrahamsen's
;; 'out-xtra.el' (http://tinyurl.com/aql9p97), and may replace it many cases.
;; Some new ideas were taken from Fabrice Niessen's '.emacs'
;; (http://www.mygooglest.com/fni/dot-emacs.html#sec-2), and some inspiration
;; from Eric Schulte's and Dan Davidson's 'Org-babel'
;; (http://orgmode.org/worg/org-contrib/babel/).

;; ** Commentary

;; This file provides (almost) the same nice extra features for outline minor
;; mode like Per Abrahamsen's 'out-xtra':

;; - Change default minor mode key prefix to `C-c'.
;; - Complete keybindings and menu support.
;; - Add command to show top level headers.
;; - Add command to hide all other entries than the one containing point.

;; `outorg' follows a different idea than `out-xtra': it consists of generic
;; functionality that that calculates the adequate outline-regexp and
;; outline-level for the active major-mode, rather than defining several blocks
;; of major-mode specific functionality.

;; New features of `outorg' are:

;; 1. Generic functionality that should work whereever `comment-region' and
;; `uncomment-region' work. 

;; 2. Fontification of headlines (copied from Fabrice Niessen's
;; '.emacs')

;; 3. Toggling between editing in Lisp mode and in Org mode, similar to the
;; editing of source-code blocks in Org-mode.

;; It is highly recommended to use `outorg' together with `outline-magic' for
;; the Org-style `outline-cycle' command.

;; ** Emacs Version

;; `outorg.el' works with [GNU Emacs 24.2.1 (x86_64-unknown-linux-gnu, GTK+
;; Version 3.6.4) of 2013-01-20 on eric]. No attempts of testing with older
;; versions or other types of Emacs have be made (yet).

;; ** Installation

;; Insert
  ;; (require 'outorg)
;; in your .emacs file to install.  If you want a different prefix
;; key, insert first
  ;; (defvar outline-minor-mode-prefix "\C-c")
;; or whatever.  The prefix can only be changed before outline (minor)
;; mode is loaded.

;; ** ChangeLog

;; | date            | author(s)       | version |
;; |-----------------+-----------------+---------|
;; | <2013-02-11 Mo> | Thorsten Jolitz |     0.9 |

;; ** Bugs

;; `outorg' is line-based, it only works with 'one-line' comments, i.e. with
;; comment-sections like those produced by `comment-region' (a command that
;; comments or uncomments each line in the region). Those special multi-line
;; comments found in many programming languages are not recognized and lead to
;; undefined behaviour.

;; * Requires

(require 'outline)
(require 'org)

;; * Variables

;; ** Consts

(defconst outorg-version "0.9"
  "outorg version number.")

;; ** Vars

(defvar outline-minor-mode-prefix "\C-c"
  "New outline-minor-mode prefix.")

(defvar outorg-edit-whole-buffer-p nil
  "Non-nil if the whole code-buffer is edited.")

(defvar outorg-initial-window-config nil
  "Initial window-configuration when editing as Org.") 

;; ** Hooks

(defvar outorg-hook nil
  "Functions to run after `outorg' is loaded.")

;; ** Customs

;; *** Custom Groups

;; (defgroup outorg nil
;;   "Library for outline navigation and Org-mode editing in Lisp buffers."
;;   :prefix "outorg-"
;;   :group 'lisp 'outlines
;;   :link '(url-link "http://emacswiki.org/emacs/OutlineMinorMode"))


;; *** Custom Vars

;; * Functions

;; ** Non-interactive Functions

;; *** Get buffer major mode

(defun outorg-get-buffer-mode (buffer-or-string)
  "Return major mode of BUFFER-OR-STRING."
  (with-current-buffer buffer-or-string
     major-mode))


;; *** Calculate the outline-regexp

(defun outorg-calc-outline-regexp ()
  "Calculate the outline regexp for the current mode."
  (let* ((comment-start-no-space
          (replace-regexp-in-string
           "[[:space:]]+" "" comment-start))
         (comment-start-region
          (if (and
               comment-end
               (not (string-equal "" comment-end)))
              comment-start-no-space
            (concat
             comment-start-no-space comment-start-no-space))))
    ;; the "^" not needed by outline, but by outorg (?)
    (concat "^" comment-start-region " [*]+ ")))

;; *** Calculate the outline-level

(defun outorg-calc-outline-level ()
  "Calculate the right outline level for the outorg-outline-regexp"
  (save-excursion
    (save-match-data
      (let ((len (- (match-end 0) (match-beginning 0))))
        (- len (+ 2 (* 2 (length (format "%s" comment-start))))))))) 


;; *** Fontify the headlines

;; Org-style highlighting of the headings
(defun outorg-fontify-headlines (outline-regexp)
  ;; (interactive)
  ;; (setq outline-regexp (tj/outline-regexp))

  ;; highlight the headings
  ;; see http://www.gnu.org/software/emacs/manual/html_node/emacs/Font-Lock.html
  ;; use `M-x customize-apropos-faces' to customize faces
  ;; to find the corresponding face for each outline level, see
  ;; `org-faces.el'

  ;; Added `\n?', after having read the following chunk of code (from org.el):
  ;; `(,(if org-fontify-whole-heading-line
  ;;        "^\\(\\**\\)\\(\\* \\)\\(.*\n?\\)"
  ;;      "^\\(\\**\\)\\(\\* \\)\\(.*\\)")

  (let ((org-fontify-whole-heading-line "") ; "\n?")
        (heading-1-regexp
         (concat (substring outline-regexp 0 -1) 
                 "\\{1\\} \\(.*" org-fontify-whole-heading-line "\\)"))
        (heading-2-regexp
         (concat (substring outline-regexp 0 -1)
                 "\\{2\\} \\(.*" org-fontify-whole-heading-line "\\)"))
        (heading-3-regexp
         (concat (substring outline-regexp 0 -1)
                 "\\{3\\} \\(.*" org-fontify-whole-heading-line "\\)"))
        (heading-4-regexp
         (concat (substring outline-regexp 0 -1)
                 "\\{4,\\} \\(.*" org-fontify-whole-heading-line "\\)"))
         (heading-5-regexp
         (concat (substring outline-regexp 0 -1)
                 "\\{5\\} \\(.*" org-fontify-whole-heading-line "\\)")))
    (font-lock-add-keywords
     nil
     `((,heading-1-regexp 1 'org-level-1 t)
       (,heading-2-regexp 1 'org-level-2 t)
       (,heading-3-regexp 1 'org-level-3 t)
       (,heading-4-regexp 1 'org-level-4 t)
       (,heading-5-regexp 1 'org-level-5 t)))))

;; *** Set outline-regexp und outline-level

(defun outorg-set-local-outline-regexp-and-level (regexp &optional fun)
   "Set `outline-regexp' locally to REGEXP and `outline-level' to FUN."
	(make-local-variable 'outline-regexp)
	(setq outline-regexp regexp)
	(and fun
             (make-local-variable 'outline-level)
             (setq outline-level fun)))

;; *** Outorg hook-functions

(defun outorg-hook-function ()
  "Add this function to outline-minor-mode-hook"
  (let ((out-regexp (outorg-calc-outline-regexp)))
    (outorg-set-local-outline-regexp-and-level
     out-regexp 'outorg-calc-outline-level)
    (outorg-fontify-headlines out-regexp)))

(add-hook 'outline-minor-mode-hook 'outorg-hook-function)

;; ** Commands

;; *** Edit as Org 

(defun outorg-edit-as-org (arg)
  "Convert and copy to temporary Org buffer
With ARG, edit the whole buffer, otherwise the current subtree."
  (interactive "P")
  (setq outorg-code-buffer-marker (point-marker))
  (and arg (setq outorg-edit-whole-buffer-p t))
  (setq outorg-initial-window-config
        (current-window-configuration))
  (outorg-copy-and-convert))

(defun outorg-save-edits ()
  "Replace code-buffer content with (converted) edit-buffer content and
  kill edit-buffer"
  (interactive)
  (widen)
  (funcall
   (outorg-get-buffer-mode
    (marker-buffer outorg-code-buffer-marker)))
  (outorg-convert-back-to-code)
  (outorg-replace-code-with-edits)
  (kill-buffer
   (marker-buffer outorg-edit-buffer-marker))
  (set-window-configuration
   outorg-initial-window-config)
  ;; (switch-to-buffer
  ;;  (marker-buffer outorg-code-buffer-marker))
  ;; (goto-char
  ;;  (marker-position outorg-code-buffer-marker))
  (outorg-reset-global-vars))

;; *** Additional outline commands (from `out-xtra').

(defun outline-hide-sublevels (keep-levels)
  "Hide everything except the first KEEP-LEVEL headers."
  (interactive "p")
  (if (< keep-levels 1)
      (error "Must keep at least one level of headers"))
  (setq keep-levels (1- keep-levels))
  (save-excursion
    (goto-char (point-min))
    (hide-subtree)
    (show-children keep-levels)
    (condition-case err
      (while (outline-get-next-sibling)
	(hide-subtree)
	(show-children keep-levels))
      (error nil))))

(defun outline-hide-other ()
  "Hide everything except for the current body and the parent headings."
  (interactive)
  (outline-hide-sublevels 1)
  (let ((last (point))
	(pos (point)))
    (while (save-excursion
	     (and (re-search-backward "[\n\r]" nil t)
		  (eq (following-char) ?\r)))
      (save-excursion
	(beginning-of-line)
	(if (eq last (point))
	    (progn
	      (outline-next-heading)
	      (outline-flag-region last (point) ?\n))
	  (show-children)
	  (setq last (point)))))))


;; *** Edit as Org-file

(defun outorg-copy-and-convert ()
  "Copy code buffer content to tmp-buffer and convert it to Org syntax.
If WHOLE-BUFFER-P is non-nil, copy the whole buffer, otherwise
  the current subtree."
  (let* ((edit-buffer
          (get-buffer-create "*outorg-edit-buffer*")))
    (save-restriction
      (with-current-buffer edit-buffer (erase-buffer))
      (widen)
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
    (and outorg-edit-whole-buffer-p
         (goto-char
          (marker-position outorg-code-buffer-marker)))
    (setq outorg-edit-buffer-marker (point-marker)))
  ;; activate programming language major mode and convert to org
  (funcall (outorg-get-buffer-mode
            (marker-buffer outorg-code-buffer-marker)))
  (outorg-convert-to-org)
  ;; change major mode to org-mode
  (org-mode)
  (if outorg-edit-whole-buffer-p
      (progn
        (org-first-headline-recenter)
        (hide-sublevels 3)
        (goto-char
         (marker-position outorg-edit-buffer-marker))
        (show-subtree))
    (goto-char
     (marker-position outorg-edit-buffer-marker))
    (show-all)))

(defun outorg-convert-to-org ()
  "Convert file content to Org Syntax"
  (let* ((last-line-comment-p nil)
         (mode-name
          (format
           "%S" (with-current-buffer
                    (marker-buffer outorg-code-buffer-marker)
                  major-mode)))
         (splitted-mode-name
          (split-string mode-name "-mode"))
         (language-name
          (if (> (length splitted-mode-name) 1)
              (car splitted-mode-name)
            (car (split-string mode-name "\\."))))
         (in-org-babel-load-languages-p
          (assq
           (intern language-name)
           org-babel-load-languages)))
    (goto-char (point-min))
    (while (not (eobp))
      (cond
       ;; empty line (do nothing)
       ((looking-at "^[[:space:]]*$"))
       ;; comment line after comment line or at
       ;; beginning of buffer
       ((and
         (save-excursion
           (eq (comment-on-line-p) (point-at-bol)))
         (or (bobp) last-line-comment-p))
        (uncomment-region (point-at-bol) (point-at-eol))
        (setq last-line-comment-p t))
       ;; line of code after comment line
       ((and
         (save-excursion
           (not (eq (comment-on-line-p) (point-at-bol))))
         last-line-comment-p)
        (newline)
        (forward-line -1)
        (insert
         (if in-org-babel-load-languages-p
             (concat "#+begin_src " language-name)
           "#+begin_example"))
        (forward-line)
        (setq last-line-comment-p nil))
       ;; comment line after line of code
       ((and
         (save-excursion
           (eq (comment-on-line-p) (point-at-bol)))
         (not last-line-comment-p))
        (uncomment-region (point-at-bol) (point-at-eol))
        (save-excursion
          (forward-line -1)
          (unless (looking-at "^[[:space:]]*$")
            (newline))
          (if in-org-babel-load-languages-p
              (insert "#+end_src")
            (insert "#+end_example"))
          (newline))
        (setq last-line-comment-p t))
       ;; last line after line of code
       ((and
         (eq (line-number-at-pos)
             (1- (count-lines (point-min) (point-max))))
         (not last-line-comment-p))
        ;; (unless (looking-at "^[[:space:]]*$")
        (forward-line)
        (newline)
        (if in-org-babel-load-languages-p
            (insert "#+end_src")
          (insert "#+end_example"))
        (newline))
       ;; line of code after line of code
       (t (setq last-line-comment-p nil)))
      (forward-line))))

(defun outorg-convert-back-to-code ()
  "Convert edit-buffer content back to programming language syntax.
Assume that edit-buffer major-mode has been set back to the
  programming-language major-mode of the associated code-buffer
  before this function is called."
  (let* ((inside-code-or-example-block-p nil))
    (goto-char (point-min))
    (while (not (eobp))
      (cond
       ;; empty line (do nothing)
       ((looking-at "^[[:space:]]*$"))
       ;; begin code/example block
       ((looking-at "^[ \t]*#\\+begin_?")
        (kill-whole-line)
        (forward-line -1)
        (setq inside-code-or-example-block-p t))
       ;; end code/example block
       ((looking-at "^[ \t]*#\\+end_?")
        (kill-whole-line)
        (forward-line -1)
        (setq inside-code-or-example-block-p nil))
       ;; line inside code/example block (do nothing)
       (inside-code-or-example-block-p)
       ;; not-empty line outside code/example block
       (t (comment-region (point-at-bol) (point-at-eol))))
      (forward-line))))

(defun outorg-replace-code-with-edits ()
  "Replace code-buffer contents with edits."
  (let* ((edit-buf (marker-buffer outorg-edit-buffer-marker))
         (code-buf (marker-buffer outorg-code-buffer-marker))
         (edit-buf-point-min
          (with-current-buffer edit-buf
            (point-min)))
         (edit-buf-point-max
          (with-current-buffer edit-buf
            (goto-char (point-max))
            (unless (and (bolp) (looking-at "^$"))
              (newline))
            (point))))
    (with-current-buffer code-buf
      (if outorg-edit-whole-buffer-p
          (progn
            (erase-buffer)
            (insert-buffer-substring-no-properties
             edit-buf edit-buf-point-min edit-buf-point-max)
            ;; (goto-char (marker-position outorg-edit-buffer-marker))
            )
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
           edit-buf edit-buf-point-min edit-buf-point-max)))
      ;; (save-buffer) 
      )))

(defun outorg-reset-global-vars ()
  "Reset some global vars defined by outorg to initial values."
  (set-marker outorg-code-buffer-marker nil)
  (set-marker outorg-edit-buffer-marker nil)
  (setq outorg-edit-whole-buffer-p nil)
  (setq outorg-initial-window-config nil))

;; * Keybindings.

;; We provide bindings for all keys.
;; FIXME: very old stuff from `out-xtra' - still necesary?

(if (fboundp 'eval-after-load)
    ;; FSF Emacs 19.
    (eval-after-load "outline"
      '(let ((map (lookup-key outline-minor-mode-map
			      outline-minor-mode-prefix)))
	 (define-key map "\C-t" 'hide-body)
	 (define-key map "\C-a" 'show-all)
	 (define-key map "\C-c" 'hide-entry)
	 (define-key map "\C-e" 'show-entry)
	 (define-key map "\C-l" 'hide-leaves)
	 (define-key map "\C-k" 'show-branches)
	 (define-key map "\C-q" 'outline-hide-sublevels)
	 (define-key map "\C-o" 'outline-hide-other)
          ;; TODO differentiate between called in code or edit buffer
         (define-key map "'" 'outorg-edit-as-org)
         ;; TODO add these keybindings to org-mode keymap (all?)
         ;; (define-key map "\C-s" 'outorg-save-edits)
         ;; (define-key map "\C-c" 'outorg-save-edits)
         ;; (define-key map "'" 'outorg-save-edits)

	 (define-key outline-minor-mode-map [menu-bar hide hide-sublevels]
	   '("Hide Sublevels" . outline-hide-sublevels))
	 (define-key outline-minor-mode-map [menu-bar hide hide-other]
	   '("Hide Other" . outline-hide-other))
	 (if (fboundp 'update-power-keys)
	     (update-power-keys outline-minor-mode-map))))

  (if (string-match "Lucid" emacs-version)
      (progn				;; Lucid Emacs 19
	(defconst outline-menu
	  '(["Up" outline-up-heading t]
	    ["Next" outline-next-visible-heading t]
	    ["Previous" outline-previous-visible-heading t]
	    ["Next Same Level" outline-forward-same-level t]
	    ["Previous Same Level" outline-backward-same-level t]
	    "---"
	    ["Show All" show-all t]
	    ["Show Entry" show-entry t]
	    ["Show Branches" show-branches t]
	    ["Show Children" show-children t]
	    ["Show Subtree" show-subtree t]
	    "---"
	    ["Hide Leaves" hide-leaves t]
	    ["Hide Body" hide-body t]
	    ["Hide Entry" hide-entry t]
	    ["Hide Subtree" hide-subtree t]
	    ["Hide Other" outline-hide-other t]
	    ["Hide Sublevels" outline-hide-sublevels t]))

        (defun outline-add-menu ()
	  (set-buffer-menubar (copy-sequence current-menubar))
	  (add-menu nil "Outline" outline-menu))

	(add-hook 'outline-minor-mode-hook 'outline-add-menu)
	(add-hook 'outline-mode-hook 'outline-add-menu)
	(add-hook 'outline-minor-mode-off-hook
                  (function (lambda () (delete-menu-item '("Outline")))))))

  ;; Lucid Emacs or Emacs 18.
  (require 'outln-18)
  (let ((map (lookup-key outline-minor-mode-map outline-minor-mode-prefix)))
    ;; Should add a menu here.
    (define-key map "\C-t" 'hide-body)
    (define-key map "\C-a" 'show-all)
    (define-key map "\C-c" 'hide-entry)
    (define-key map "\C-e" 'show-entry)
    (define-key map "\C-l" 'hide-leaves)
    (define-key map "\C-k" 'show-branches)
    (define-key map "\C-q" 'outline-hide-sublevels)
    (define-key map "\C-o" 'outline-hide-other)))


;; * Run hooks and provide

(run-hooks 'outorg-hook)

(provide 'outorg)

;; Local Variables:
;; coding: utf-8
;; ispell-local-dictionary: "en_US"
;; End:

;; outorg.el ends here
