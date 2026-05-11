;;; org-indicators.el --- Property indicators on Org headlines -*- lexical-binding: t -*-

;; Copyright (C) 2026 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 10 May 2026
;; Version: 1.0
;; Keywords: org outline overlay
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; View-only decoration of Org headlines (both in Org buffers and the
;; agenda) with a small fixed-width block of indicator letters that
;; reveal properties of the entry at a glance:
;;
;;   ꜰ — has file attachment(s)
;;   ᴜ — has a URL property
;;   ɴ — has body text or log notes (inside or outside LOGBOOK)
;;   ᴛ — has CLOCK entries
;;
;; The block sits in the alignment whitespace between the title and
;; the tags, anchored at a fixed column derived from the tag-column
;; right edge so blocks align vertically across headings whose tags
;; differ in length.  When the title is too long to leave room, the
;; block for that line is silently skipped, so tags never get pushed
;; out of their column.

;; Usage:
;;
;;   ;; In Org buffers
;;   (add-hook 'org-mode-hook #'org-indicators-mode)
;;
;;   ;; In agenda buffers
;;   (add-hook 'org-agenda-finalize-hook #'org-indicators-apply-agenda)

;;; Code:

(require 'org)
(require 'org-agenda)
(require 'outline)

(defgroup org-indicators nil
  "Visual indicators displayed on Org headlines."
  :group 'org)

(defcustom org-indicators-chars
  '((file    . "ꜰ")
    (url     . "ᴜ")
    (note    . "ɴ")
    (timelog . "ᴛ"))
  "Alist mapping indicator symbols to display strings.
Each entry maps a symbol from `org-indicators-types' to the glyph
used to represent that indicator.  The default uses Unicode
small-cap letters so the glyphs share the width and height of
ordinary characters."
  :type '(alist :key-type symbol :value-type string)
  :group 'org-indicators)

(defcustom org-indicators-types
  '(file url note timelog)
  "Indicator types displayed by `org-indicators-mode'.
Each element must be a key present in `org-indicators-chars' and
defines a slot in the indicator block (in this order):

  `file'    -- the entry has an attachment;
  `url'     -- the entry has a URL property;
  `note'    -- the entry has body text or log notes (state
               changes, captured notes), inside or outside a
               LOGBOOK drawer;
  `timelog' -- the entry has CLOCK entries."
  :type '(set (const file) (const url) (const note) (const timelog))
  :group 'org-indicators)

(defcustom org-indicators-tag-margin 14
  "Columns reserved for the tag string when positioning indicators.
The indicator block's right edge is placed this many columns
before the tag column's right edge, so the block aligns
vertically across headings whose tag strings have different
lengths.  Lines whose tag string is wider than this margin fall
back to a flush placement immediately before the tags."
  :type 'integer
  :group 'org-indicators)

(defface org-indicators
  '((t :inherit font-lock-keyword-face :weight bold))
  "Face used to render headline indicator characters.
Defaults to a bold variant of `font-lock-keyword-face' so the
small-cap indicators stand out against the heading text."
  :group 'org-indicators)

(defconst org-indicators--tag-line-re
  "[^ \t\n]\\([ \t]+\\):\\(?:[[:alnum:]_@#%]+:\\)+[ \t]*$"
  "Regexp matching trailing tag string on a heading or agenda line.
Group 1 captures all whitespace between the title and the tags.
The leading `[^ \\t\\n]' anchor forces the match to start at the
end of the title text so the greedy whitespace group spans the
full alignment padding.")

(defun org-indicators--heading-has-body-p (subtree-end)
  "Return non-nil if heading at point has body text before SUBTREE-END.
Body text excludes the planning line, property/log/other drawers,
and blank lines.  Point is preserved."
  (save-excursion
    (forward-line 1)
    (when (looking-at "^[ \t]*\\(?:DEADLINE\\|SCHEDULED\\|CLOSED\\):")
      (forward-line 1))
    (while (looking-at "^[ \t]*:[A-Za-z][A-Za-z0-9_-]*:[ \t]*$")
      (if (re-search-forward "^[ \t]*:END:[ \t]*$" subtree-end t)
          (forward-line 1)
        (goto-char subtree-end)))
    (while (and (< (point) subtree-end)
                (looking-at "^[ \t]*$"))
      (forward-line 1))
    (and (< (point) subtree-end)
         (not (looking-at "^\\*+ ")))))

(defun org-indicators--has-log-entries-p (subtree-end)
  "Return non-nil if heading at point has log entries before SUBTREE-END.
A log entry is a list item line of the form \"- ...\" inside the
LOGBOOK drawer (state changes, captured notes, reschedules, etc.)."
  (save-excursion
    (forward-line 1)
    (when (re-search-forward "^[ \t]*:LOGBOOK:[ \t]*$" subtree-end t)
      (let ((drawer-end (save-excursion
                          (if (re-search-forward "^[ \t]*:END:[ \t]*$"
                                                 subtree-end t)
                              (match-beginning 0)
                            subtree-end))))
        (re-search-forward "^[ \t]*- " drawer-end t)))))

(defun org-indicators--has-clock-entries-p (subtree-end)
  "Return non-nil if heading at point has CLOCK entries before SUBTREE-END."
  (save-excursion
    (forward-line 1)
    (re-search-forward "^[ \t]*CLOCK:" subtree-end t)))

(defun org-indicators--has-attachment-p ()
  "Return non-nil if heading at point has an attachment."
  (or (member "ATTACH" (org-get-tags nil t))
      (and (featurep 'org-attach)
           (let ((dir (ignore-errors (org-attach-dir))))
             (and dir (file-directory-p dir))))))

(defun org-indicators--at-point ()
  "Return the indicator symbols applicable to the headline at point.
Returns a list of symbols (a subset of `org-indicators-types') in
display order, or nil if point is not on a heading."
  (when (org-at-heading-p)
    (let ((subtree-end (save-excursion
                         (outline-next-heading)
                         (point)))
          result)
      (when (and (memq 'file org-indicators-types)
                 (org-indicators--has-attachment-p))
        (push 'file result))
      (when (and (memq 'url org-indicators-types)
                 (org-entry-get nil "URL"))
        (push 'url result))
      (when (and (memq 'note org-indicators-types)
                 (or (org-indicators--heading-has-body-p subtree-end)
                     (org-indicators--has-log-entries-p subtree-end)))
        (push 'note result))
      (when (and (memq 'timelog org-indicators-types)
                 (org-indicators--has-clock-entries-p subtree-end))
        (push 'timelog result))
      (nreverse result))))

(defun org-indicators--block (indicators)
  "Build a fixed-width indicator block for INDICATORS.
Every type in `org-indicators-types' contributes one slot to the
block, in order; slots whose type is not present in INDICATORS
render as a space, so the block has the same column width
regardless of which indicators are active.  Slots are joined by
single spaces.  The active glyphs are faced with `org-indicators'."
  (let* ((face 'org-indicators)
         (slots
          (mapcar
           (lambda (type)
             (if (memq type indicators)
                 (propertize
                  (or (cdr (assq type org-indicators-chars)) " ")
                  'face face)
               " "))
           org-indicators-types)))
    (mapconcat #'identity slots " ")))

(defun org-indicators--apply-on-line (indicators)
  "Place an indicator overlay for INDICATORS on the current line.

If the line ends with `:tag1:tag2:' tags, the indicator block is
placed in the alignment whitespace, with its right edge anchored
at `(tag-end-col - org-indicators-tag-margin)' so the block
aligns vertically across headings whose tags differ in length.
If the tag string is too wide to leave room there, the block
falls back to a flush placement immediately before the tags.  If
the title is too long to fit the block at all, no overlay is
created and tags stay where Org placed them.

If the line has no tags, the block is appended after the title,
left-padded so it falls at the same column as on tagged rows."
  (when indicators
    (let* ((bol (line-beginning-position))
           (eol (line-end-position))
           (block (org-indicators--block indicators))
           (block-width (string-width block)))
      (save-excursion
        (goto-char eol)
        (cond
         ;; Has tags: place in alignment whitespace before them.
         ((re-search-backward org-indicators--tag-line-re bol t)
          (let* ((space-beg (match-beginning 1))
                 (space-end (match-end 1))
                 (padding-width (- space-end space-beg))
                 (title-end-col (- space-beg bol))
                 (tag-start-col (- space-end bol))
                 (tag-end-col (save-excursion
                                (goto-char eol)
                                (skip-chars-backward " \t" bol)
                                (- (point) bol)))
                 ;; Preferred block right-edge: a fixed margin
                 ;; before the tag column's right edge.
                 (desired-end-col (- tag-end-col
                                     org-indicators-tag-margin))
                 ;; The latest column the block may end at while
                 ;; still leaving a single space before the tags.
                 (max-end-col (- tag-start-col 2))
                 (block-end-col (min desired-end-col max-end-col))
                 (block-start-col (1+ (- block-end-col block-width))))
            (when (and (>= padding-width (1+ block-width))
                       (>= block-start-col title-end-col))
              (let* ((spaces-before (- block-start-col title-end-col))
                     (spaces-after (- tag-start-col block-end-col 1))
                     (display (concat
                               (make-string spaces-before ?\s)
                               block
                               (make-string spaces-after ?\s)))
                     (ov (make-overlay space-beg space-end)))
                (overlay-put ov 'org-indicators t)
                (overlay-put ov 'display display)
                (overlay-put ov 'evaporate t)))))
         ;; No tags: append after the title content.  Use a
         ;; zero-length overlay with `after-string'; do not set
         ;; `evaporate' since that would delete the empty overlay
         ;; immediately.  Align block to the same column as
         ;; tagged lines by padding with leading spaces.
         (t
          (goto-char eol)
          (skip-chars-backward " \t" bol)
          (let* ((pos (point))
                 (title-end-col (- pos bol))
                 (target-tag-end-col
                  (cond ((< org-tags-column 0) (- org-tags-column))
                        ((> org-tags-column 0) org-tags-column)
                        (t (+ title-end-col 1 block-width))))
                 (desired-end-col (- target-tag-end-col
                                     org-indicators-tag-margin))
                 (block-start-col (1+ (- desired-end-col block-width)))
                 (leading (max 1 (- block-start-col title-end-col))))
            (when (> pos bol)
              (let ((ov (make-overlay pos pos))
                    (after (concat (make-string leading ?\s) block)))
                (overlay-put ov 'org-indicators t)
                (overlay-put ov 'after-string after))))))))))

(defun org-indicators--remove (start end)
  "Remove indicator overlays between START and END."
  (dolist (ov (overlays-in start end))
    (when (overlay-get ov 'org-indicators)
      (delete-overlay ov))))

(defun org-indicators--fontify (start end)
  "Apply indicator overlays to Org headings in [START, END].
Used as a `jit-lock-register' fontification function.  Errors on
a single heading are swallowed so they do not disable jit-lock
for the whole buffer."
  (save-excursion
    (goto-char start)
    (forward-line 0)
    (setq start (point))
    (goto-char end)
    (forward-line 1)
    (setq end (point)))
  (org-indicators--remove start end)
  (save-excursion
    (goto-char start)
    (while (re-search-forward "^\\*+ " end t)
      (save-excursion
        (forward-line 0)
        (condition-case _err
            (org-indicators--apply-on-line
             (org-indicators--at-point))
          (error nil))))))

;;;###autoload
(define-minor-mode org-indicators-mode
  "Toggle Unicode property indicators on Org headlines.

When enabled, decorates Org headlines with a small fixed-width
block of indicator letters placed in the alignment whitespace
between the title and the tags, so that the column at which tags
start is not disturbed.  Each slot is either the glyph for an
active indicator or a space, so the block has the same column
width regardless of which indicators apply:

  ꜰ — has file attachment(s)
  ᴜ — has a URL property
  ɴ — has body text or log notes (in or out of a LOGBOOK drawer)
  ᴛ — has CLOCK entries

If the title leaves insufficient room before the tags, the
indicators for that line are silently skipped.  Glyphs are
customizable via `org-indicators-chars'; the slot order via
`org-indicators-types'; the face via `org-indicators'.

For Org agenda buffers, add `org-indicators-apply-agenda' to
`org-agenda-finalize-hook' instead of enabling this mode there."
  :init-value nil
  :lighter " ɪ"
  (cond
   (org-indicators-mode
    (when (derived-mode-p 'org-mode)
      (jit-lock-register #'org-indicators--fontify)
      (org-indicators--fontify (point-min) (point-max))))
   (t
    (when (derived-mode-p 'org-mode)
      (jit-lock-unregister #'org-indicators--fontify))
    (org-indicators--remove (point-min) (point-max)))))

;;;###autoload
(defun org-indicators-apply-agenda ()
  "Apply indicator overlays to the current Org agenda buffer.
Intended for use with `org-agenda-finalize-hook'.  For each line
that refers to a source headline (via the `org-hd-marker' or
`org-marker' text property), the indicators are computed from
the source buffer and placed in the trailing whitespace before
tags (or appended after the title text when no tags are
present).  Errors on individual lines are swallowed."
  (when (derived-mode-p 'org-agenda-mode)
    (org-indicators--remove (point-min) (point-max))
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (condition-case _err
            (let ((marker (or (get-text-property (point) 'org-hd-marker)
                              (get-text-property (point) 'org-marker))))
              (when (and (markerp marker)
                         (marker-buffer marker)
                         (buffer-live-p (marker-buffer marker))
                         (marker-position marker))
                (let ((indicators
                       (with-current-buffer (marker-buffer marker)
                         (save-excursion
                           (goto-char (marker-position marker))
                           (and (derived-mode-p 'org-mode)
                                (org-indicators--at-point))))))
                  (when indicators
                    (org-indicators--apply-on-line indicators)))))
          (error nil))
        (forward-line 1)))))

(provide 'org-indicators)

;;; org-indicators.el ends here
