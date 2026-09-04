;;; org-ql-help.el --- Cheatsheet for Org QL query syntax -*- lexical-binding: t; -*-

;; Copyright (C) 2025  Karthik Chikmagalur

;; Author: Karthik Chikmagalur <karthikchikmagalur@gmail.com>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; Pop-up cheatsheet for Org QL queries.  When entering a query in
;; the minibuffer for any Org QL command (org-ql-search,
;; org-ql-sparse-tree, org-ql-find, org-ql-refile, ...), press "?" to
;; toggle a help window at the bottom of the frame showing the
;; available query predicates with examples.  The sheet shown matches
;; the syntax being typed: sexp queries like (and (todo) (priority
;; "A")) get the sexp sheet, everything else gets the string-syntax
;; sheet (todo:NEXT tags:book, ...).

;; No Org QL functions are called: detection is the same string
;; heuristic org-ql itself uses, so this library has no dependencies
;; beyond Emacs 29.

;;; Code:

(require 'cl-lib)

;;;; Variables

(defvar org-ql-help-buffer-name "*org-ql query help*"
  "Name of the Org QL query help buffer.")

(defvar org-ql-help-commands
  '(org-ql-search org-ql-sparse-tree org-ql-find
    org-ql-find-in-agenda org-ql-find-in-org-directory
    org-ql-find-path org-ql-refile org-ql-open-link)
  "Commands that read an Org QL query in the minibuffer.
Identified by THIS-COMMAND in `org-ql-help--minibuffer-setup'.  As
a fallback, minibuffers whose prompt starts with \"Query: \" also
get the help keymap (this covers transient readers and
`org-ql-view-refresh').")

(defvar org-ql-help--active nil
  "Set buffer-locally in query minibuffers where help is bound.")

(defvar org-ql-help--sexp nil
  "Which sheet the help buffer shows: sexp syntax (t) or string syntax (nil).
Buffer-local in the help buffer, set by `org-ql-help--fill'.")

(defvar org-ql-help--saved-scroll-window nil
  "Previous value of `minibuffer-scroll-window' in the query minibuffer.
Buffer-local there; used to restore it when the help is dismissed.")

(defvar-keymap org-ql-help-map
  :doc "Keymap for Org QL query minibuffers.  Binds ?."
  "?" #'org-ql-help-show)

;;;; Help sheets

(defconst org-ql-help--string-sheet
  ;; Modeled on `w-search--filter-help-string' in wombag-search.el.
  (cl-labels ((spc (to) (propertize " " 'display `(space :align-to ,to)))
              (key (text) (propertize text 'face 'help-key-binding))
              (box (text) (propertize text 'face '(:underline t :weight semi-bold)))
              (note (text) (propertize text 'face 'shadow))
              (row (k1 d1 k2 d2)
                (concat
                 (unless (string-empty-p k1) (key k1))
                 (unless (string-empty-p d1) (concat (spc 26) d1))
                 (unless (string-empty-p k2) (concat (spc 50) (key k2)))
                 (unless (string-empty-p d2) (concat (spc 72) d2))
                 "\n")))
    (concat
     (propertize "Org QL Query Syntax" 'face '(inherit shadow :height 1.1))
     (spc 54) (note "[terms are AND-combined; ? toggles this help]")
     (propertize "\n\n" 'face '(inherit :height 0.8))
     (box "Text") (spc 50) (box "Todo / Tags") "\n"
     (row "word" "entry or outline path" "todo:" "any undone TODO keyword")
     (row "\"two words\"" "quoted arg (spaces ok)" "todo:NEXT,WAITING" "either of these keywords")
     (row "!word" "negation (only !, not -)" "done:" "any done keyword")
     (row "heading:foo" "words in heading (h:)" "tags:book,books" "any of these tags")
     (row "heading-regexp:re" "regexp in heading (h*:)" "tags-all:book,read" "all of these (tags&:)")
     (row "regexp:re" "regexp in entry (r:)" "tags-local:x" "local tags (tags-l:)")
     (row "category:work" "category (c:)" "tags-inherited:x" "inherited (tags-i:)")
     (row "" "" "tags-regexp:book" "tags by regexp (tags*:)")
     "\n"
     (box "Properties") (spc 50) (box "Timestamps") "\n"
     (row "priority:A,B" "A or B (no comparators)" "ts:" "any timestamp")
     (row "level:2" "outline level 2" "ts:on=today" "timestamp on today")
     (row "effort:0:15" "effort equal to 0:15" "ts-active:from=-7" "active ts in last 7 days")
     (row "property:Effort,0:15" "property with value" "ts-active:from=a,to=b" "ts within date range")
     (row "path:lisp/" "buffer file path" "ts-inactive:" "inactive only (ts-i:)")
     (row "habit:" "habits" "scheduled:" "scheduled (to=3: within 3d)")
     (row "blocked:" "blocked entries" "deadline:" "deadline (auto: soon)")
     "\n"
     (box "Planning") (spc 50) (box "More") "\n"
     (row "planning:" "sched/deadline/closed" "src:lang=elisp,defun" "babel source blocks")
     (row "closed:from=-30" "closed in last 30 days" "link:gnu.org" "links matching text/target")
     (row "clocked:on=-1" "clocked yesterday" "olp:Music,Rock" "outline path matches")
     (row "created:from=-30" "CREATED prop in range" "olps:Music,Rock" "path segment matches")
     "\n"
     (note "Dates: today, -7 (7 days ago), \"2025-06-01\"; commas separate args; k=v keyword args.")))
  "Cheatsheet for Org QL non-sexp (string) query syntax.")

(defconst org-ql-help--sexp-sheet
  ;; Modeled on `w-search--filter-help-string' in wombag-search.el.
  (cl-labels ((spc (to) (propertize " " 'display `(space :align-to ,to)))
              (key (text) (propertize text 'face 'help-key-binding))
              (box (text) (propertize text 'face '(:underline t :weight semi-bold)))
              (note (text) (propertize text 'face 'shadow))
              (row (k1 d1 k2 d2)
                (concat
                 (unless (string-empty-p k1) (key k1))
                 (unless (string-empty-p d1) (concat (spc 34) d1))
                 (unless (string-empty-p k2) (concat (spc 66) (key k2)))
                 (unless (string-empty-p d2) (concat (spc 100) d2))
                 "\n")))
    (concat
     (propertize "Org QL Query Syntax" 'face '(inherit shadow :height 1.1))
     (spc 54) (note "[sexp form; ? toggles this help]")
     (propertize "\n\n" 'face '(inherit :height 0.8))
     (box "Combining") (spc 66) (box "Containers (nestable)") "\n"
     (row "(and ...) (or ...)" "boolean logic, nestable" "(ancestors (todo))" "an ancestor matches")
     (row "\"string\"" "bare string = (rifle \"s\")" "(descendants (todo))" "a descendant matches")
     (row "" "" "(children (not (done)))" "a direct child matches")
     (row "" "" "(parent (tags \"proj\"))" "the parent matches")
     "\n"
     (box "Entries") (spc 66) (box "Timestamps (days from today)") "\n"
     (row "(todo) (todo \"NEXT\")" "undone / one of keywords" "(ts) (ts :on today)" "any ts / on today")
     (row "(done)" "any done keyword" "(ts-active :from -7 :to 0)" "active ts in range (ts-a)")
     (row "(heading \"a phrase\")" "words in heading (h)" "(ts-inactive :from \"2025-01-01\")" "inactive ts (ts-i)")
     (row "(heading-regexp \"re\")" "regexp in heading (h*)" "(scheduled :to 3)" "scheduled within 3 days")
     (row "(regexp \"re\")" "regexp in entry (r)" "(deadline) (deadline auto)" "deadline / due soon")
     (row "(rifle \"w1\" \"w2\")" "entry or path (smart)" "(planning :on today)" "sched, deadline or closed")
     (row "(category \"work\")" "category (c)" "(closed :from -30)" "closed in last 30 days")
     (row "(level 2) (level 1 3)" "level, range; also >=, <" "(clocked :from -30)" "clocked in last 30 days")
     (row "(priority \"A\" \"B\")" "A or B; >= \"B\" for higher" "(created :from -30)" "CREATED prop in range")
     (row "(habit) (blocked)" "habits / blocked entries" "" "")
     "\n"
     (box "Properties / files") (spc 66) (box "Tags") "\n"
     (row "(property \"Effort\" \"0:15\")" "property = value" "(tags \"book\" \"read\")" "any of these tags")
     (row "(effort \"0:05\" \"0:30\")" "effort range; also >=" "(tags-all \"a\" \"b\")" "all of them (tags&)")
     (row "(path \"lisp/\")" "buffer file path" "(tags-local \"x\")" "local only (tags-l)")
     (row "(src :lang \"elisp\")" "src blocks (:regexps too)" "(tags-inherited \"x\")" "inherited (tags-i)")
     (row "(link \"gnu.org\")" "link text or target" "(tags-regexp \"re\")" "by regexp (tags*)")
     (row "(olp \"Music\" \"Rock\")" "outline path contains" "" "")
     (row "(olps \"Music\" \"Rock\")" "as contiguous segment" "" "")
     "\n"
     (note "String syntax also accepted: todo:NEXT tags:book ts-active:from=-7")))
  "Cheatsheet for Org QL sexp query syntax.")

;;;; Displaying help

(defun org-ql-help--sexp-query-p (s)
  "Return non-nil if query string S starts a sexp query.
Uses the same heuristic as `org-ql-search'."
  (string-match-p (rx bos (0+ blank) (or "(" "\"")) s))

(defun org-ql-help--fill (buffer sexp)
  "Fill BUFFER with the cheatsheet for SEXP (non-nil) or string syntax."
  (with-current-buffer buffer
    ;; Change the major mode first: `special-mode' kills non-permanent
    ;; local variables, which would wipe `org-ql-help--sexp' otherwise.
    (special-mode)
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert (if sexp org-ql-help--sexp-sheet org-ql-help--string-sheet)))
    ;; Leave point at the top: a window newly displaying this buffer
    ;; starts at the buffer's point.
    (goto-char (point-min))
    (setq truncate-lines t
          mode-line-format nil)
    (setq-local org-ql-help--sexp sexp)))

;;;###autoload
(defun org-ql-help-show ()
  "Pop up a cheatsheet of Org QL query predicates with examples.
The sheet matches the query syntax being typed in the minibuffer:
sexp queries like (todo \"NEXT\") get the sexp sheet, everything
else the string-syntax sheet (todo:NEXT ...).  Pressing ? again
closes the window.  While it is shown, C-M-v in the minibuffer
scrolls it."
  (interactive)
  (let* ((input (if (minibufferp) (minibuffer-contents-no-properties) ""))
         (sexp (org-ql-help--sexp-query-p input))
         (buffer (get-buffer-create org-ql-help-buffer-name))
         (window (get-buffer-window buffer)))
    (cond
     ((not (window-live-p window))
      ;; Show it.
      (org-ql-help--fill buffer sexp)
      (display-buffer buffer
                      '((display-buffer-in-side-window display-buffer-at-bottom)
                        (side . bottom) (slot . -20)))
      (when (minibufferp)
        ;; Make C-M-v in the minibuffer page the help buffer.
        (setq-local org-ql-help--saved-scroll-window minibuffer-scroll-window
                    minibuffer-scroll-window (get-buffer-window buffer)))
      (fit-window-to-buffer (get-buffer-window buffer)
                            (max 8 (/ (frame-height) 2))))
     ((eq sexp (buffer-local-value 'org-ql-help--sexp buffer))
      ;; Dismiss it.
      (quit-window nil window)
      (when (minibufferp)
        (setq minibuffer-scroll-window org-ql-help--saved-scroll-window)))
     (t
      ;; Switch sheets.
      (org-ql-help--fill buffer sexp)
      (set-window-point window (point-min))
      (fit-window-to-buffer window (max 8 (/ (frame-height) 2)))))))

;;;; Minibuffer integration

(defun org-ql-help--minibuffer-setup ()
  "Bind ? in query minibuffers of Org QL commands."
  (when (or (memq this-command org-ql-help-commands)
            (string-match-p "\\`Query: " (minibuffer-prompt)))
    (setq-local org-ql-help--active t)
    (use-local-map (make-composed-keymap org-ql-help-map (current-local-map)))))

(defun org-ql-help--minibuffer-exit ()
  "Close the query help window when leaving a query minibuffer."
  (when (and (local-variable-p 'org-ql-help--active)
             (window-live-p (get-buffer-window org-ql-help-buffer-name)))
    (quit-window nil (get-buffer-window org-ql-help-buffer-name))))

(add-hook 'minibuffer-setup-hook #'org-ql-help--minibuffer-setup)
(add-hook 'minibuffer-exit-hook #'org-ql-help--minibuffer-exit)

(provide 'org-ql-help)
;;; org-ql-help.el ends here
