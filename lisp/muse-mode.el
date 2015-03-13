;;; muse-mode.el --- mode for editing Muse files; has font-lock support

;; Copyright (C) 2004, 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; The Emacs Muse major mode is basically a hyped-up text-mode which
;; knows a lot more about the apparent structure of the document.

;;; Contributors:

;; Andrea Riciputi (ariciputi AT pito DOT com) gave an initial
;; implementation for tag completion by means of the `muse-insert-tag'
;; function.

;; Per B. Sederberg (per AT med DOT upenn DOT edu) contributed the
;; insertion of relative links and list items, backlink searching, and
;; other things as well.

;; Stefan Schlee (stefan_schlee AT yahoo DOT com) fixed a bug in
;; muse-next-reference and muse-previous-reference involving links
;; that begin at point 1.

;; Gregory Collins (greg AT gregorycollins DOT net) fixed a bug with
;; paragraph separation and headings when filling.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Emacs Muse Major Mode
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'muse-mode)

(require 'muse)
(require 'muse-regexps)
(require 'muse-project)

(autoload 'muse-use-font-lock "muse-colors")
(autoload 'muse-publish-this-file "muse-publish")
(autoload 'muse-publish-get-style "muse-publish")
(autoload 'muse-publish-output-file "muse-publish")

(require 'derived)
(eval-when-compile
  (condition-case nil
      (require 'pcomplete)              ; load if available
    (error nil)))

;;; Options:

(defgroup muse-mode nil
  "Options controlling the behavior of the Muse editing Mode."
  :group 'muse)

(defcustom muse-mode-highlight-p t
  "If non-nil, highlight the content of Muse buffers."
  :type 'boolean
  :require 'muse-colors
  :group 'muse-mode)

(defcustom muse-mode-auto-p nil
  "If non-nil, automagically determine when Muse mode should be activated."
  :type 'boolean
  :set (function
        (lambda (sym value)
          (if value
              (add-hook 'find-file-hooks 'muse-mode-maybe)
            (remove-hook 'find-file-hooks 'muse-mode-maybe))
          (set sym value)))
  :group 'muse-mode)

(defun muse-mode-maybe-after-init ()
  (when muse-mode-auto-p
    (add-hook 'find-file-hooks 'muse-mode-maybe)))

;; If the user sets this value in their init file, make sure that
;; it takes effect
(add-hook 'after-init-hook 'muse-mode-maybe-after-init)

(defcustom muse-mode-intangible-links nil
  "If non-nil, use the intangible property on links.
This can cause problems with flyspell (and potentially fill-mode),
so only enable this if you don't use either of these."
  :type 'boolean
  :group 'muse-mode)

(defcustom muse-mode-hook nil
  "A hook that is run when Muse mode is entered."
  :type 'hook
  :options '(flyspell-mode footnote-mode turn-on-auto-fill
             highlight-changes-mode)
  :group 'muse-mode)

(defcustom muse-grep-command
  "find %D -type f ! -name '*~' | xargs -I {} echo \\\"{}\\\" | xargs egrep -n -e \"%W\""
  "The command to use when grepping for backlinks and other
searches through the muse projects.  The string %D is replaced by
the directories from muse-project-alist, space-separated.  The
string %W is replaced with the name of the muse page or whatever
else you are searching for.  This command has been modified to
handle spaces in filenames, which were giving egrep a problem.

Note: We highly recommend using glimpse to search large projects.
To use glimpse, install and edit a file called .glimpse_exclude
in your home directory.  Put a list of glob patterns in that file
to exclude Emacs backup files, etc.  Then, run the indexer using:

  glimpseindex -o <list of Wiki directories>

Once that's completed, customize this variable to have the
following value:

  glimpse -nyi \"%W\"

Your searches will go much, much faster, especially for very
large projects.  Don't forget to add a user cronjob to update the
index at intervals."
  :type 'string
  :group 'muse-mode)

(defvar muse-insert-map
  (let ((map (make-sparse-keymap)))
    (define-key map "l" 'muse-insert-relative-link-to-file)
    (define-key map "t" 'muse-insert-tag)
    (define-key map "u" 'muse-insert-url)

    map))

;;; Muse mode

(defvar muse-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(control ?c) (control ?a)] 'muse-index)
    (define-key map [(control ?c) (control ?e)] 'muse-edit-link-at-point)
    (define-key map [(control ?c) (control ?l)] 'font-lock-mode)
    (define-key map [(control ?c) (control ?t)]
      'muse-project-publish-this-file)
    (define-key map [(control ?c) (control ?T)] 'muse-publish-this-file)
    (define-key map [(control ?c) (meta control ?t)] 'muse-publish-this-file)
    (define-key map [(control ?c) (control ?v)] 'muse-browse-result)

    (define-key map [(control ?c) ?=]           'muse-what-changed)

    (define-key map [tab] 'muse-next-reference)
    (define-key map [(control ?i)] 'muse-next-reference)

    (if (featurep 'xemacs)
        (progn
          (define-key map [(button2)] 'muse-follow-name-at-mouse)
          (define-key map [(shift button2)]
            'muse-follow-name-at-mouse-other-window))
      (define-key map [(shift control ?m)]
        'muse-follow-name-at-point-other-window)
      (define-key map [mouse-2] 'muse-follow-name-at-mouse)
      (define-key map [(shift mouse-2)]
        'muse-follow-name-at-mouse-other-window))

    (define-key map [(shift tab)] 'muse-previous-reference)
    (unless (featurep 'xemacs)
      (define-key map [(shift iso-lefttab)] 'muse-previous-reference)
      (define-key map [(shift control ?i)] 'muse-previous-reference))

    (define-key map [(control ?c) (control ?f)] 'muse-project-find-file)
    (define-key map [(control ?c) (control ?p)] 'muse-project-publish)

    (define-key map [(control ?c) (control ?i)] 'muse-insert-thing)
    (define-key map [(control ?c) tab] 'muse-insert-thing)

    ;; Searching functions
    (define-key map [(control ?c) (control ?b)] 'muse-find-backlinks)
    (define-key map [(control ?c) (control ?s)] 'muse-search)

    ;; Enhanced list functions
    (define-key map [(meta return)] 'muse-insert-list-item)
    (define-key map [(control ?>)] 'muse-increase-list-item-indentation)
    (define-key map [(control ?<)] 'muse-decrease-list-item-indentation)

    (when (featurep 'pcomplete)
      (define-key map [(meta tab)] 'pcomplete)
      (define-key map [(meta control ?i)] 'pcomplete))

    map)
  "Keymap used by Emacs Muse mode.")

;;;###autoload
(define-derived-mode muse-mode text-mode "Muse"
  "Muse is an Emacs mode for authoring and publishing documents.
\\{muse-mode-map}"
  ;; Since we're not inheriting from normal-mode, we need to
  ;; explicitly run file variables.
  (condition-case err
      (hack-local-variables)
    (error (message "File local-variables error: %s"
                    (prin1-to-string err))))
  ;; Avoid lock-up caused by use of the 'intangible' text property
  ;; with flyspell.
  (unless muse-mode-intangible-links
    (set (make-local-variable 'inhibit-point-motion-hooks) t))
  (setq muse-current-project (muse-project-of-file))
  (muse-project-set-variables)
  ;; Make fill not split up links
  (when (boundp 'fill-nobreak-predicate)
    (make-local-variable 'fill-nobreak-predicate)
    ;; Work around annoying inconsistency in fill handling between
    ;; Emacs 21 and 22.
    (if (< emacs-major-version 22)
        (setq fill-nobreak-predicate 'muse-mode-fill-nobreak-p)
      (add-to-list 'fill-nobreak-predicate
                   'muse-mode-fill-nobreak-p)))
  ;; Make fill work nicely with item lists
  (let ((regexp (concat "\\s-+\\(-\\|[0-9]+\\.\\)\\s-+"
                        "\\|\\[[0-9]+\\]\\s-*"
                        "\\|.*\\s-*::\\s-+"
                        "\\|\\*+\\s-+")))
    (set (make-local-variable 'adaptive-fill-regexp)
         (concat regexp "\\|\\s-*"))
    (set (make-local-variable 'paragraph-start)
         (concat paragraph-start "\\|" regexp))
    (set (make-local-variable 'paragraph-separate)
         (concat paragraph-separate "\\|\\*+\\s-+")))
  (set (make-local-variable 'fill-paragraph-function)
       'muse-mode-fill-paragraph)

  ;; Comment syntax is `; comment'
  (set (make-local-variable 'comment-start)
       "; ")
  (set (make-local-variable 'comment-start-skip)
       "^;\\s-+")
  (set (make-local-variable 'indent-line-function)
       #'ignore)
  ;; If we're using Emacs21, this makes flyspell work like it should
  (when (boundp 'flyspell-generic-check-word-p)
    (set (make-local-variable 'flyspell-generic-check-word-p)
         'muse-mode-flyspell-p))
  ;; If pcomplete is available, set it up
  (when (featurep 'pcomplete)
    (set (make-local-variable 'pcomplete-default-completion-function)
         'muse-mode-completions)
    (set (make-local-variable 'pcomplete-command-completion-function)
         'muse-mode-completions)
    (set (make-local-variable 'pcomplete-parse-arguments-function)
         'muse-mode-current-word))
  ;; Initialize any auto-generated variables
  (run-hooks 'muse-update-values-hook)
  (when muse-mode-highlight-p
    (muse-use-font-lock)))

(put 'muse-mode
     'flyspell-mode-predicate
     'muse-mode-flyspell-p)

(defun muse-mode-fill-nobreak-p ()
  "Return nil if we should allow a fill to occur at point.
Otherwise return non-nil.

This is used to keep long explicit links from being mangled by
fill mode."
  (save-excursion
    (save-match-data
      (and (re-search-backward "\\[\\[\\|\\]\\]"
                               (line-beginning-position) t)
           (string= (or (match-string 0) "")
                    "[[")))))

(defun muse-mode-fill-paragraph (arg)
  "If a definition list is at point, use special filling rules for it.
Otherwise return nil to let the normal filling function take care
of things.

ARG is passed to `fill-paragraph'."
  (let ((count 2))
    (and (not (muse-mode-fill-nobreak-p))
         (save-excursion
           (beginning-of-line)
           (and (looking-at muse-dl-term-regexp)
                (prog1 t
                  ;; Take initial whitespace into account
                  (when (looking-at (concat "[" muse-regexp-blank "]+"))
                    (setq count (+ count (length (match-string 0))))))))
         (let ((fill-prefix (make-string count ?\ ))
               (fill-paragraph-function nil))
           (prog1 t
             (fill-paragraph arg))))))

(defun muse-mode-flyspell-p ()
  "Return non-nil if we should allow spell-checking to occur at point.
Otherwise return nil.

This is used to keep links from being improperly colorized by flyspell."
  (let ((pos (if (bobp) (point) (1- (point)))))
    (and (not (get-text-property pos 'muse-no-flyspell))
         (not (get-text-property pos 'muse-link))
         (save-match-data
           (null (muse-link-at-point))))))

;;;###autoload
(defun muse-mode-choose-mode ()
  "Turn the proper Emacs Muse related mode on for this file."
  (let ((project (muse-project-of-file)))
    (funcall (or (and project (muse-get-keyword :major-mode (cadr project) t))
                 'muse-mode))))

(defun muse-mode-maybe ()
  "Maybe turn Emacs Muse mode on for this file."
  (let ((project (muse-project-of-file)))
    (and project
         (funcall (or (muse-get-keyword :major-mode (cadr project) t)
                      'muse-mode)))))

;;; Enhanced list editing

(defun muse-on-blank-line ()
  "See if point is on a blank line"
  (save-excursion
    (beginning-of-line)
    (looking-at (concat "[" muse-regexp-blank "]*$"))))

(defun muse-get-paragraph-start ()
  "Return the start of the current paragraph. This function will
return nil if there are no prior paragraphs and the beginning of
the line if point is on a blank line."
  (let ((para-start (concat "^[" muse-regexp-blank "]*$")))
    ;; search back to start of paragraph
    (save-excursion
      (save-match-data
        (if (not (muse-on-blank-line))
            (re-search-backward para-start nil t)
          (line-beginning-position))))))

(defun muse-insert-thing ()
  "Prompt for something to insert into the current buffer."
  (interactive)
  (message "Insert:\nl  link\nt  Muse tag\nu  URL")
  (let (key cmd)
    (let ((overriding-local-map muse-insert-map))
      (setq key (read-key-sequence nil)))
    (if (commandp (setq cmd (lookup-key muse-insert-map key)))
        (progn (message "")
               (call-interactively cmd))
      (message "Not inserting anything"))))

;;;###autoload
(defun muse-insert-list-item ()
  "Insert a list item at the current point, taking into account
your current list type and indentation level."
  (interactive)
  (let ((newitem " - ")
        (itemno nil)
        (pstart (muse-get-paragraph-start))
        (list-item (format muse-list-item-regexp
                           (concat "[" muse-regexp-blank "]*"))))
    ;; search backwards for start of current item
    (save-excursion
      (when (re-search-backward list-item pstart t)
        ;; save the matching item
        (setq newitem (match-string 0))
        ;; see what type it is
        (if (string-match "::" (match-string 0))
            ;; is a definition, replace the term
            (setq newitem (concat " "
                                  (read-string "Term: ")
                                  " :: "))
          ;; see if it's a numbered list
          (when (string-match "[0-9]+" newitem)
            ;; is numbered, so increment
            (setq itemno (1+
                          (string-to-number
                           (match-string 0 newitem))))
            (setq newitem (replace-match
                           (number-to-string itemno)
                           nil nil newitem))))))
    ;; insert the new item
    (insert (concat "\n" newitem))))

(defun muse-alter-list-item-indentation (operation)
  "Alter the indentation of the current list item.
Valid values of OPERATION are 'increase and 'decrease."
  (let ((pstart (muse-get-paragraph-start))
        (list-item (format muse-list-item-regexp
                           (concat "[" muse-regexp-blank "]*")))
        beg move-func indent)
    ;; search backwards until start of paragraph to see if we are on a
    ;; current item
    (save-excursion
      (if (or (progn (goto-char (muse-line-beginning-position))
                     ;; we are on an item
                     (looking-at list-item))
              ;; not on item, so search backwards
              (re-search-backward list-item pstart t))
          (let ((beg (point)))
            ;; we are on an item
            (setq indent (buffer-substring (match-beginning 0)
                                           (match-beginning 1)))
            (muse-forward-list-item (muse-list-item-type (match-string 1))
                                    (concat "[" muse-regexp-blank "]*")
                                    t)
            (save-restriction
              (narrow-to-region beg (point))
              (goto-char (point-min))
              (let ((halt nil))
                (while (< (point) (point-max))
                  ;; increase or decrease the indentation
                  (unless halt
                    (cond ((eq operation 'increase)
                           (insert "  "))
                          ((eq operation 'decrease)
                           (if (looking-at "  ")
                               ;; we have enough space, so delete it
                               (delete-region (match-beginning 0)
                                              (match-end 0))
                             (setq halt t)))))
                  (forward-line 1)))))
        ;; we are not on an item, so warn
        (message "You are not on a list item.")))))

;;;###autoload
(defun muse-increase-list-item-indentation ()
  "Increase the indentation of the current list item."
  (interactive)
  (muse-alter-list-item-indentation 'increase))

;;;###autoload
(defun muse-decrease-list-item-indentation ()
  "Decrease the indentation of the current list item."
  (interactive)
  (muse-alter-list-item-indentation 'decrease))

;;; Support page name completion using pcomplete

(defun muse-mode-completions ()
  "Return a list of possible completions names for this buffer."
  (let ((project (muse-project-of-file)))
    (if project
        (while (pcomplete-here
                (mapcar 'car (muse-project-file-alist project)))))))

(defun muse-mode-current-word ()
  (let ((end (point)))
    (save-excursion
      (save-restriction
        (skip-chars-backward (concat "^\\[\n" muse-regexp-blank))
        (narrow-to-region (point) end))
      (pcomplete-parse-buffer-arguments))))

;;; Navigate/visit links or URLs.  Use TAB, S-TAB and RET (or mouse-2).

(defun muse-link-at-point (&optional pos)
  "Return link text if a URL or link is at point."
  (let ((case-fold-search nil)
        (inhibit-point-motion-hooks t)
        (here (or pos (point))))
    ;; if we are using muse-colors, we can just use link properties to
    ;; determine whether we are on a link
    (if (featurep 'muse-colors)
        (when (get-text-property here 'muse-link)
          (save-excursion
            (when (and (not (bobp))
                       (get-text-property (1- here) 'muse-link))
              (goto-char (or (previous-single-property-change here 'muse-link)
                             (point-min))))
            (if (looking-at muse-explicit-link-regexp)
                (progn
                  (goto-char (match-beginning 1))
                  (muse-handle-explicit-link))
              (muse-handle-implicit-link))))
      ;; use fallback method to find a link
      (when (or (null pos)
                (and (char-after pos)
                     (not (eq (char-syntax (char-after pos)) ?\ ))))
        (save-excursion
          (goto-char here)
          ;; check for explicit link here or before point
          (if (or (looking-at muse-explicit-link-regexp)
                  (and
                   (re-search-backward "\\[\\[\\|\\]\\]"
                                       (muse-line-beginning-position)
                                       t)
                   (string= (or (match-string 0) "") "[[")
                   (looking-at muse-explicit-link-regexp)))
              (progn
                (goto-char (match-beginning 1))
                (muse-handle-explicit-link))
            (goto-char here)
            ;; check for bare URL or other link type
            (skip-chars-backward (concat "^'\"<>{}(\n" muse-regexp-blank))
            (and (looking-at muse-implicit-link-regexp)
                 (muse-handle-implicit-link))))))))

(defun muse-make-link (link &optional desc)
  "Return a link to LINK with DESC as the description."
  (when (string-match muse-explicit-link-regexp link)
    (unless desc (setq desc (muse-get-link-desc link)))
    (setq link (muse-get-link link)))
  (if (and desc
           link
           (not (string= desc ""))
           (not (string= link desc)))
      (concat "[[" (muse-link-escape link) "][" (muse-link-escape desc) "]]")
    (concat "[[" (or (muse-link-escape link) "") "]]")))

;;;###autoload
(defun muse-insert-relative-link-to-file ()
  "Insert a relative link to a file, with optional description, at point."
  ;; Perhaps the relative location should be configurable, so that the
  ;; file search would start in the publishing directory and then
  ;; insert the link relative to the publishing directory
  (interactive)
  (insert
   (muse-make-link (file-relative-name (read-file-name "Link: "))
                   (read-string "Text: "))))

(defcustom muse-insert-url-initial-input "http://"
  "The string to insert before reading a URL interactively.
This is used by the `muse-insert-url' command."
  :type 'string
  :group 'muse-mode)

(defun muse-insert-url ()
  "Insert a URL, with optional description, at point."
  (interactive)
  (insert
   (muse-make-link (read-string "URL: " muse-insert-url-initial-input)
                   (read-string "Text: "))))

;;;###autoload
(defun muse-edit-link-at-point ()
  "Edit the current link.
Do not rename the page originally referred to."
  (interactive)
  (if (muse-link-at-point)
      (let ((link (muse-link-unescape (muse-get-link)))
            (desc (muse-link-unescape (muse-get-link-desc))))
        (replace-match
         (save-match-data
           (muse-make-link
            (read-string "Link: " link)
            (read-string "Text: " desc)))
         t t))
    (error "There is no valid link at point")))

(defun muse-visit-link-default (link &optional other-window)
  "Visit the URL or link named by LINK.
If ANCHOR is specified, search for it after opening LINK.

This is the default function to call when visiting links; it is
used by `muse-visit-link' if you have not specified :visit-link
in `muse-project-alist'."
  (if (string-match muse-url-regexp link)
      (muse-browse-url link)
    (let (anchor
          base-buffer)
      (when (string-match "#" link)
        (setq anchor (substring link (match-beginning 0))
              link (if (= (match-beginning 0) 0)
                       ;; If there is an anchor but no link, default
                       ;; to the current page.
                       nil
                     (substring link 0 (match-beginning 0)))))
      (when link
        (setq base-buffer (get-buffer link))
        (if (and base-buffer (not (buffer-file-name base-buffer)))
            ;; If file is temporary (no associated file), just switch to
            ;; the buffer
            (if other-window
                (switch-to-buffer-other-window base-buffer)
              (switch-to-buffer base-buffer))
          (let ((project (muse-project-of-file)))
            (if project
                (muse-project-find-file link project
                                        (and other-window
                                             'find-file-other-window))
              (if other-window
                  (find-file-other-window link)
                (find-file link))))))
      (when anchor
        (let ((pos (point))
              (regexp (concat "^\\W*" (regexp-quote anchor) "\\b"))
              last)
          (goto-char (point-min))
          (while (and (setq last (re-search-forward regexp nil t))
                      (muse-link-at-point)))
          (unless last
            (goto-char pos)
            (message "Could not find anchor `%s'" anchor)))))))

(defun muse-visit-link (link &optional other-window)
  "Visit the URL or link named by LINK."
  (let ((visit-link-function
         (muse-get-keyword :visit-link (cadr (muse-project-of-file)) t)))
    (if visit-link-function
        (funcall visit-link-function link other-window)
      (muse-visit-link-default link other-window))))

;;;###autoload
(defun muse-browse-result (style &optional other-window)
  "Visit the current page's published result."
  (interactive
   (list (muse-project-get-applicable-style buffer-file-name
                                            (cddr muse-current-project))
         current-prefix-arg))
  (setq style (muse-style style))
  (muse-project-publish-this-file nil style)
  (let* ((output-dir (muse-style-element :path style))
         (output-suffix (muse-style-element :osuffix style))
         (output-path (muse-publish-output-file buffer-file-name output-dir
                                                style))
         (target (if output-suffix
                     (concat (muse-path-sans-extension output-path)
                             output-suffix)
                   output-path))
         (muse-current-output-style (list :base (car style)
                                          :path output-dir)))
    (if (not (file-readable-p target))
        (error "Cannot open output file '%s'" target)
      (if other-window
          (find-file-other-window target)
        (let ((func (muse-style-element :browser style t)))
          (if func
              (funcall func target)
            (message "The %s publishing style does not support browsing."
                     style)))))))

;;;###autoload
(defun muse-follow-name-at-point (&optional other-window)
  "Visit the link at point."
  (interactive "P")
  (let ((link (muse-link-at-point)))
    (if link
        (muse-visit-link link other-window)
      (error "There is no valid link at point"))))

;;;###autoload
(defun muse-follow-name-at-point-other-window ()
  "Visit the link at point in other window."
  (interactive)
  (muse-follow-name-at-point t))

(defun muse-follow-name-at-mouse (event &optional other-window)
  "Visit the link at point, or yank text if none is found."
  (interactive "eN")
  (unless
      (save-excursion
        (cond ((fboundp 'event-window)      ; XEmacs
               (set-buffer (window-buffer (event-window event)))
               (and (funcall (symbol-function 'event-point) event)
                    (goto-char (funcall (symbol-function 'event-point)
                                        event))))
              ((fboundp 'posn-window)       ; Emacs
               (set-buffer (window-buffer (posn-window (event-start event))))
               (goto-char (posn-point (event-start event)))))
        (let ((link (muse-link-at-point)))
          (when link
            (muse-visit-link link other-window)
            t)))
    ;; Fall back to normal binding for this event
    (call-interactively
     (lookup-key (current-global-map) (this-command-keys)))))

(defun muse-follow-name-at-mouse-other-window (event)
  "Visit the link at point"
  (interactive "e")
  ;; throw away the old window position, since other-window will
  ;; change it anyway
  (select-window (car (cadr event)))
  (muse-follow-name-at-mouse event t))

;;;###autoload
(defun muse-next-reference ()
  "Move forward to next Muse link or URL, cycling if necessary."
  (interactive)
  (let ((pos))
    (save-excursion
      (when (get-text-property (point) 'muse-link)
        (goto-char (or (next-single-property-change (point) 'muse-link)
                       (point-max))))

      (setq pos (next-single-property-change (point) 'muse-link))

      (when (not pos)
        (if (get-text-property (point-min) 'muse-link)
            (setq pos (point-min))
          (setq pos (next-single-property-change (point-min) 'muse-link)))))

    (when pos
      (goto-char pos))))

;;;###autoload
(defun muse-previous-reference ()
  "Move backward to the next Muse link or URL, cycling if necessary.
In case of Emacs x <= 21 and ignoring of intangible properties (see
`muse-mode-intangible-links').

This function is not entirely accurate, but it's close enough."
  (interactive)
  (let ((pos))
    (save-excursion

      ;; Hack: The user perceives the two cases of point ("|")
      ;; position (1) "|[[" and (2) "[[|" or "][|" as "point is at
      ;; start of link".  But in the sense of the function
      ;; "previous-single-property-change" these two cases are
      ;; different.  The following code aligns these two cases.  Emacs
      ;; 21: If the intangible property is ignored case (2) is more
      ;; complicate and this hack only solves the problem partially.
      ;;
      (when (and (get-text-property (point) 'muse-link)
                 (muse-looking-back "\\[\\|\\]"))
        (goto-char (or (previous-single-property-change (point) 'muse-link)
                       (point-min))))

      (when (eq (point) (point-min))
        (goto-char (point-max)))

      (setq pos (previous-single-property-change (point) 'muse-link))

      (when (not pos)
        (if (get-text-property (point-min) 'muse-link)
            (setq pos (point-min))
          (setq pos (previous-single-property-change (point-max)
                                                     'muse-link)))))

    (when pos
      (if (get-text-property pos 'muse-link)
          (goto-char pos)
        (goto-char (or (previous-single-property-change pos 'muse-link)
                       (point-min)))))))

;;;###autoload
(defun muse-what-changed ()
  "Show the unsaved changes that have been made to the current file."
  (interactive)
  (diff-backup buffer-file-name))


;;; Find text in project pages, or pages referring to the current page

(defvar muse-search-history nil)

(defun muse-grep (string &optional grep-command-no-shadow)
  "Grep for STRING in the project directories.
GREP-COMMAND if passed will supplant `muse-grep-command'."
  ;; careful - grep-command leaks into compile, so we call it
  ;; -no-shadow instead
  (require 'compile)
  (let* ((str (or grep-command-no-shadow muse-grep-command))
         (muse-directories (mapcar
                            (lambda (thing)
                              (car (cadr thing)))
                            muse-project-alist))
         (dirs (mapconcat (lambda (dir)
                            (shell-quote-argument
                             (expand-file-name dir)))
                          muse-directories " ")))
    (if (string= dirs "")
        (muse-display-warning
         "No directories were found in the current project; aborting search")
      (while (string-match "%W" str)
        (setq str (replace-match string t t str)))
      (while (string-match "%D" str)
        (setq str (replace-match dirs t t str)))
      (if (fboundp 'compilation-start)
          (compilation-start str nil (lambda (&rest args) "*search*")
                             grep-regexp-alist)
        (and (fboundp 'compile-internal)
             (compile-internal str "No more search hits" "search"
                               nil grep-regexp-alist))))))

;;;###autoload
(defun muse-search-with-command (text)
  "Search for the given TEXT string in the project directories
using the specified command."
  (interactive
   (list (let ((str (concat muse-grep-command)) pos)
           (when (string-match "%W" str)
             (setq pos (match-beginning 0))
             (unless (featurep 'xemacs)
               (setq pos (1+ pos)))
             (setq str (replace-match "" t t str)))
           (read-from-minibuffer "Search command: "
                                 (cons str pos) nil nil
                                 'muse-search-history))))
  (muse-grep nil text))

;;;###autoload
(defun muse-search ()
  "Search for the given TEXT using the default grep command."
  (interactive)
  (muse-grep (read-string "Search: ")))

;;;###autoload
(defun muse-find-backlinks ()
  "Grep for the current pagename in all the project directories."
  (interactive)
  (muse-grep (muse-page-name)))


;;; Generate an index of all known Muse pages

(defun muse-generate-index (&optional as-list exclude-private)
  "Generate an index of all Muse pages."
  (let ((index (muse-index-as-string as-list exclude-private)))
    (with-current-buffer (get-buffer-create "*Muse Index*")
      (erase-buffer)
      (insert index)
      (current-buffer))))

;;;###autoload
(defun muse-index ()
  "Display an index of all known Muse pages."
  (interactive)
  (message "Generating Muse index...")
  (let ((project (muse-project)))
    (with-current-buffer (muse-generate-index)
      (goto-char (point-min))
      (muse-mode)
      (setq muse-current-project project)
      (pop-to-buffer (current-buffer))))
  (message "Generating Muse index...done"))

(defun muse-index-as-string (&optional as-list exclude-private exclude-current)
  "Generate an index of all Muse pages.
If AS-LIST is non-nil, insert a dash and spaces before each item.
If EXCLUDE-PRIVATE is non-nil, exclude files that have private permissions.
If EXCLUDE-CURRENT is non-nil, exclude the current file from the output."
  (let ((files (sort (copy-alist (muse-project-file-alist))
                     (function
                      (lambda (l r)
                        (string-lessp (car l) (car r)))))))
    (when (and exclude-current (muse-page-name))
      (setq files (delete (assoc (muse-page-name) files) files)))
    (with-temp-buffer
      (while files
        (unless (and exclude-private
                     (muse-project-private-p (cdar files)))
          (insert (if as-list " - " "") "[[" (caar files) "]]\n"))
        (setq files (cdr files)))
      (buffer-string))))

;;; Insert tags interactively on C-c TAB t

(defvar muse-tag-history nil
  "List of recently-entered tags; used by `muse-insert-tag'.
If you want a tag to start as the default, you may manually set
this variable to a list.")

(defvar muse-custom-tags nil
  "Keep track of any new tags entered in `muse-insert-tag'.
If there are (X)HTML tags that you use frequently with that
function, you might want to set this manually.")

;;;###autoload
(defun muse-insert-tag (tag)
  "Insert a tag interactively with a blank line after it."
  (interactive
   (list
    (funcall
     muse-completing-read-function
     (concat "Tag: "
             (when muse-tag-history
               (concat "(default: " (car muse-tag-history) ") ")))
     (progn
       (require 'muse-publish)
       (mapcar 'list (nconc (mapcar 'car muse-publish-markup-tags)
                            muse-custom-tags)))
     nil nil nil 'muse-tag-history
     (car muse-tag-history))))
  (when (equal tag "")
    (setq tag (car muse-tag-history)))
  (unless (interactive-p)
    (require 'muse-publish))
  (let ((tag-entry (assoc tag muse-publish-markup-tags))
        (options ""))
    ;; Add to custom list if no entry exists
    (unless tag-entry
      (add-to-list 'muse-custom-tags tag))
    ;; Get option
    (when (nth 2 tag-entry)
      (setq options (read-string "Option: ")))
    (unless (equal options "")
      (setq options (concat " " options)))
    ;; Insert the tag, closing if necessary
    (when tag (insert (concat "<" tag options ">")))
    (when (nth 1 tag-entry)
      (insert (concat "\n\n</" tag ">\n"))
      (forward-line -2))))

;;; Muse list edit minor mode

(defvar muse-list-edit-minor-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [(meta return)] 'muse-l-e-m-m-insert-list-item)
    (define-key map [(control ?>)] 'muse-l-e-m-m-increase-list-item-indent)
    (define-key map [(control ?<)] 'muse-l-e-m-m-decrease-list-item-indent)

    map)
  "Keymap used by Muse list edit minor mode.")

(defvar muse-l-e-m-m-list-item-regexp
  (concat "^%s\\(\\([^\n" muse-regexp-blank "].*?\\)?::"
          "\\(?:[" muse-regexp-blank "]+\\|$\\)"
          "\\|[" muse-regexp-blank "]?[-*+][" muse-regexp-blank "]*"
          "\\|[" muse-regexp-blank "][0-9]+\\.[" muse-regexp-blank "]*\\)")
  "Regexp used to match the beginning of a list item.
This is used by `muse-list-edit-minor-mode'.
The '%s' will be replaced with a whitespace regexp when publishing.")

(defun muse-l-e-m-m-insert-list-item ()
  "Insert a list item at the current point, taking into account
your current list type and indentation level."
  (interactive)
  (let ((muse-list-item-regexp muse-l-e-m-m-list-item-regexp))
    (call-interactively 'muse-insert-list-item)))

(defun muse-l-e-m-m-increase-list-item-indent ()
  "Increase the indentation of the current list item."
  (interactive)
  (let ((muse-list-item-regexp muse-l-e-m-m-list-item-regexp))
    (call-interactively 'muse-increase-list-item-indentation)))

(defun muse-l-e-m-m-decrease-list-item-indent ()
  "Decrease the indentation of the current list item."
  (interactive)
  (let ((muse-list-item-regexp muse-l-e-m-m-list-item-regexp))
    (call-interactively 'muse-decrease-list-item-indentation)))

(defvar muse-l-e-m-m-data nil
  "A list of data that was changed by Muse list edit minor mode.")
(make-variable-buffer-local 'muse-l-e-m-m-data)

;;;###autoload
(define-minor-mode muse-list-edit-minor-mode
  "This is a global minor mode for editing files with lists.
It is meant to be used with other major modes, and not with Muse mode.

Interactively, with no prefix argument, toggle the mode.
With universal prefix ARG turn mode on.
With zero or negative ARG turn mode off.

This minor mode provides the Muse keybindings for editing lists,
and support for filling lists properly.

It recognizes not only Muse-style lists, which use the \"-\"
character or numbers, but also lists that use asterisks or plus
signs.  This should make the minor mode generally useful.

Definition lists and footnotes are also recognized.

Note that list items may omit leading spaces, for compatibility
with modes that set `left-margin', such as
`debian-changelog-mode'.

\\{muse-list-edit-minor-mode-map}"
  :init-value nil
  :lighter ""
  :keymap muse-list-edit-minor-mode-map
  :global nil
  :group 'muse-mode
  (if (not muse-list-edit-minor-mode)
      ;; deactivate
      (when muse-l-e-m-m-data
        (setq adaptive-fill-regexp (cdr (assoc "a-f-r" muse-l-e-m-m-data))
              paragraph-start (cdr (assoc "p-s" muse-l-e-m-m-data))
              fill-prefix (cdr (assoc "f-p" muse-l-e-m-m-data)))
        (setq muse-l-e-m-m-data nil))
    ;; activate
    (unless muse-l-e-m-m-data
      ;; save previous fill-related data so we can restore it later
      (setq muse-l-e-m-m-data
            (list (cons "a-f-r" adaptive-fill-regexp)
                  (cons "p-s" paragraph-start)
                  (cons "f-p" fill-prefix))))
    ;; make fill work nicely with item lists
    (let ((regexp (concat "\\s-*\\([-*+]\\|[0-9]+\\.\\)\\s-+"
                          "\\|\\[[0-9]+\\]\\s-*"
                          "\\|.*\\s-*::\\s-+")))
      (set (make-local-variable 'adaptive-fill-regexp)
           (concat regexp "\\|\\s-*"))
      (set (make-local-variable 'paragraph-start)
           (concat paragraph-start "\\|" regexp)))
    ;; force fill-prefix to be nil, because if it is a string that has
    ;; initial spaces, it messes up fill-paragraph's algorithm
    (set (make-local-variable 'fill-prefix) nil)))

(defun turn-on-muse-list-edit-minor-mode ()
  "Unconditionally turn on Muse list edit minor mode."
  (muse-list-edit-minor-mode 1))

(defun turn-off-muse-list-edit-minor-mode ()
  "Unconditionally turn off Muse list edit minor mode."
  (muse-list-edit-minor-mode -1))

;;; muse-mode.el ends here
