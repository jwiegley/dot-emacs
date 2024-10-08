;;; org-agenda-overlay --- Code to overlay entries in org-agenda

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 7 Oct 2024
;; Version: 1.0
;; Keywords: org capture task todo context
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

(require 'cl-lib)
(require 'org)

(defun org-agenda-overlay-filetags ()
  (save-excursion
    (goto-char (point-min))
    (when (re-search-forward "^#\\+filetags: :\\(.+\\):" 4096 t)
      (split-string (match-string-no-properties 1) ":"))))

(defun compare-lists-up-to-shortest (list1 list2)
  "Compare LIST1 and LIST2 up to the length of the shortest list."
  (not (cl-some 'null (cl-mapcar 'equal list1 list2))))

(defcustom org-agenda-overlay-by-filetag nil
  "Mapping of tags to overlay properties.
Example: ((\"Work\" face (:background \"#fdfdeb\")))"
  :group 'org-agenda-overlay
  :type '(repeat
          (cons string sexp)))

(defcustom org-agenda-overlay-by-olp nil
  "Mapping of outline paths (given as lists) to overlay properties.
Example: (((\"Work\") face (:background \"#fdfdeb\")))"
  :group 'org-agenda-overlay
  :type '(repeat
          (cons (repeat string) sexp)))

(defcustom org-agenda-overlay-use-properties nil
  "If non-nil, also use OVERLAY entry and file properties.
This is nil by default because it can be very slow."
  :group 'org-agenda-overlay
  :type 'boolean)

(defun org-agenda-overlay-add (&optional line)
  "Add overlays found in OVERLAY properties to agenda items.
Note that habitual items are excluded, as they already
extensively use text properties to draw the habits graph.

For example, for work tasks I like to use a subtle, yellow
background color; for tasks involving other people, green; and
for tasks concerning only myself, blue.  This way I know at a
glance how different responsibilities are divided for any given
day.

To achieve this, I have the following in my todo file:

  * Work
  :PROPERTIES:
  :CATEGORY: Work
  :OVERLAY:  (face (:background \"#fdfdeb\"))
  :END:
  ** TODO Task
  * Family
  :PROPERTIES:
  :CATEGORY: Personal
  :OVERLAY:  (face (:background \"#e8f9e8\"))
  :END:
  ** TODO Task
  * Personal
  :PROPERTIES:
  :CATEGORY: Personal
  :OVERLAY:  (face (:background \"#e8eff9\"))
  :END:
  ** TODO Task

To use this function, add it to `org-agenda-finalize-hook':

  (add-hook 'org-agenda-finalize-hook 'org-agenda-overlay-add)"
  (let ((inhibit-read-only t)
        (buffer-invisibility-spec '(org-link)))
    (save-excursion
      (goto-char (if line (line-beginning-position) (point-min)))
      (while (not (eobp))
        (let ((org-marker (get-text-property (point) 'org-marker))
              (type-prop (get-text-property (point) 'type)))
          (when (and org-marker
                     type-prop
                     (string-match "\\(sched\\|dead\\|todo\\)" type-prop)
                     (null (overlays-at (point)))
                     (not (get-text-property (point) 'org-habit-p)))
            (let ((overlays
                   (or (and org-agenda-overlay-use-properties
                            (org-entry-get org-marker "OVERLAY" t))
                       (with-current-buffer (marker-buffer org-marker)
                         (or (and org-agenda-overlay-use-properties
                                  (org-get-global-property "OVERLAY"))
                             (catch 'found
                               (dolist (mapping org-agenda-overlay-by-filetag)
                                 (dolist (tag (org-agenda-overlay-filetags))
                                   (when (string= (car mapping) tag)
                                     (throw 'found (cdr mapping))))))
                             (catch 'found
                               (dolist (mapping org-agenda-overlay-by-olp)
                                 (when (compare-lists-up-to-shortest
                                        (car mapping)
                                        (save-excursion
                                          (goto-char org-marker)
                                          (org-get-outline-path)))
                                   (throw 'found (cdr mapping))))))))))
              (when overlays
                (goto-char (line-end-position))
                (let ((rest (- (window-width) (current-column))))
                  (if (> rest 0)
                      (insert (make-string rest ? ))))
                (let ((ol (make-overlay (line-beginning-position)
                                        (line-end-position)))
                      (proplist (if (stringp overlays)
                                    (read overlays)
                                  overlays)))
                  (while proplist
                    (overlay-put ol (car proplist) (cadr proplist))
                    (setq proplist (cddr proplist))))))))
        (forward-line)))))

(provide 'org-agenda-overlay)

;;; org-agenda-overlay.el ends here
