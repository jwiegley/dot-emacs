;;; loccur.el --- Perform an occur-like folding in current buffer -*- lexical-binding: t; -*-

;; Copyright (C) 2009-2016 Free Software Foundation, Inc
;;
;; Author: Alexey Veretennikov <alexey.veretennikov@gmail.com>
;;
;; Created: 2009-09-08
;; Version: 1.2.2
;; Package-Requires: ((cl-lib "0"))
;; Keywords: matching
;; URL: https://github.com/fourier/loccur
;; Compatibility: GNU Emacs 23.x, GNU Emacs 24.x
;;
;; This file is part of GNU Emacs.
;;
;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Commentary:
;;
;; Add the following to your .emacs file:
;; 
;; (require 'loccur)
;; ;; defines shortcut for loccur of the current word
;; (define-key global-map [(control o)] 'loccur-current)
;; ;; defines shortcut for the interactive loccur command
;; (define-key global-map [(control meta o)] 'loccur)
;; ;; defines shortcut for the loccur of the previously found word
;; (define-key global-map [(control shift o)] 'loccur-previous-match)
;;
;;; Issues:
;; Using with smooth-scrolling.el sometimes
;; gives unexpected jumps in loccur mode
;;
;;; TODO:
;; 
;;; Change Log:
;;
;; 2015-12-27 (1.2.2)
;;    + Preparation for GNU ELPA submission. Removed contributions
;;    without signed papers
;;    + added loccur-face - face to highlight text, by default isearch
;; 
;; 2013-10-22 (1.2.1)
;;    + Added custom option loccur-jump-beginning-of-line; removed some
;;    of cl dependencies
;;
;; 2010-03-07 (1.1.1)
;;    + Default value is taken from prompt instead of an edit area
;;    (thanks to Nathaniel Flath)
;;
;; 2009-10-05 (1.1.0)
;;    + Added highlighting of the matched strings
;;    + Now inserts selected region to the prompt
;;    + Added defun for applying last found regexp(loccur-previous-match)
;;    + Added intangible property together with invisibility
;;
;; 2009-09-08 (1.0.0)
;;    Initial Release.
;;
;;; Code:

(require 'cl-lib)

(defgroup loccur nil
  "Perform an occur-like folding in current buffer."
  :group 'tools)

;; should be defined before define-minor-mode
(defvar loccur-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") '(lambda () (interactive) (loccur nil)))
    ;; redefine Ctrl+Up/Down to Up/Down, since it looks like some problem
    ;; with backward-paragraph and forward-paragraph with invisible overlays
    (define-key map (kbd "<C-up>") 'previous-line)
    (define-key map (kbd "<C-down>") 'next-line)
    map)
  "Keymap for the variable `loccur-mode'.")

;;;###autoload
(define-minor-mode loccur-mode
  "Minor mode for navigating through the file.
Hides all lines without matches like `occur' does, but without opening
a new window."
  :lighter " loccur"
  (if loccur-mode
      (loccur-1 loccur-current-search)
    (loccur-remove-overlays)
    (recenter)))

(defface loccur-face
  '((t (:inherit isearch)))
  "Loccur face")


(defconst loccur-overlay-invisible-property-name 'loccur-invisible-overlay
  "Property name of the overlay for all invisible text.")

(defconst loccur-overlay-visible-property-name 'loccur-visible-overlay
  "Property name of the overlay for all visible text.")

(defcustom loccur-jump-beginning-of-line nil
  "Set cursor to the beginning of the line when the loccur function is called.
Default: nil"
  :type '(boolean)
  :group 'loccur)

(defcustom loccur-highlight-matching-regexp t
  "If set to nil, do not highlight matching words.
Default: t"
  :type '(boolean)
  :group 'loccur)

(defvar loccur-history nil
  "History of previously searched expressions for the prompt.")

(defvar-local loccur-last-match nil
  "Last match found.")

(defvar-local loccur-overlay-list nil
  "A list of currently active overlays.")

(defvar-local loccur-current-search nil
  "The expression to search in the current active mode.")

(defun loccur-current ()
  "Call `loccur' for the current word."
  (interactive)
  (loccur (current-word)))


(defun loccur-previous-match ()
  "Call `loccur' for the previously found word."
  (interactive)
  (loccur loccur-last-match))

(defun loccur-no-highlight (regex)
  "Perform search like loccur, but temporary removing match highlight.
REGEX is regexp to search"
  (interactive
   (if loccur-mode
       nil
     (list (read-string "Loccur: " (loccur-prompt) 'loccur-history))))
  (let ((loccur-highlight-matching-regexp nil))
    (loccur regex)))

(defun loccur-toggle-highlight ()
  "Toggle the highlighting of the match."
  (interactive)
  (setq loccur-highlight-matching-regexp (not loccur-highlight-matching-regexp))
  (when loccur-mode
    (dolist (ovl loccur-overlay-list)
      (when (overlay-get ovl loccur-overlay-visible-property-name)
        (overlay-put ovl 'face (if loccur-highlight-matching-regexp 'loccur-face nil))))))

(defun loccur (regex)
  "Perform a simple grep in current buffer.

This command hides all lines from the current buffer except those
containing the regular expression REGEX.  A second call of the function
unhides lines again"
  (interactive
   (if loccur-mode
       (list nil)
     (list (read-string "Loccur: " (loccur-prompt) 'loccur-history))))
  (if (or loccur-mode
          (= (length regex) 0))
      (progn
        ;; remove current search and turn off loccur mode
        ;; to allow to call `loccur' multiple times
        (setf loccur-current-search nil)
        (loccur-mode 0))
    ;; otherwise do as usual
    ;; if the regex argument is not equal to previous search
    (when (not (string-equal regex loccur-current-search))
      (cl-pushnew regex loccur-history)
      (setf loccur-current-search regex)
      (loccur-mode)
      (when loccur-jump-beginning-of-line
        (beginning-of-line))))) ; optionally jump to the beginning of line


(defun loccur-prompt ()
  "Return the default value of the prompt.

Default value for prompt is a current word or active region(selection),
if its size is 1 line"
  (let ((prompt
         (if (and transient-mark-mode
                  mark-active)
             (let ((pos1 (region-beginning))
                   (pos2 (region-end)))
               ;; Check if the start and the end of an active region is on
               ;; the same line
               (when (save-excursion
                       (goto-char pos1)
                       (<= pos2 (line-end-position)))
                   (buffer-substring-no-properties pos1 pos2)))
           (current-word))))
    prompt))


(defun loccur-1 (regex)
  "Implementation of the `loccur' functionality.

REGEX is an argument to `loccur'."
  (let* ((buffer-matches (loccur-find-matches regex))
         (ovl-bounds (loccur-create-overlay-bounds-btw-lines buffer-matches)))
    (setq loccur-overlay-list
          (loccur-create-invisible-overlays ovl-bounds))

    (setq loccur-overlay-list
          (append loccur-overlay-list
                  (loccur-create-highlighted-overlays buffer-matches)))
    (setq loccur-last-match regex)
    (recenter)))

(defun loccur-create-highlighted-overlays (buffer-matches)
  "Create the list of overlays for BUFFER-MATCHES."
  (let ((overlays
         (mapcar (lambda (match)
                   (make-overlay
                    (nth 1 match)
                    (nth 2 match)
                    (current-buffer) t nil))
                 buffer-matches)))
    (mapc (lambda (ovl)
            (overlay-put ovl loccur-overlay-visible-property-name t)
            (when loccur-highlight-matching-regexp
              (overlay-put ovl 'face 'loccur-face)))
          overlays)))


(defun loccur-create-invisible-overlays (ovl-bounds)
  "Create a list of invisible overlays by given OVL-BOUNDS."
  (let ((overlays
         (mapcar (lambda (bnd)
                   (make-overlay
                    (car bnd)
                    (cadr bnd)
                    (current-buffer) t nil))
                 ovl-bounds)))
    (mapc (lambda (ovl)
            (overlay-put ovl loccur-overlay-invisible-property-name t)
            (overlay-put ovl 'invisible t)
            ;; force intangible property if invisible property
            ;; does not automatically set it
            (overlay-put ovl 'intangible t))
          overlays)))


(defun loccur-remove-overlays ()
  "Remove all overlays."
  (remove-overlays (point-min) (point-max) loccur-overlay-visible-property-name t)
  (remove-overlays (point-min) (point-max) loccur-overlay-invisible-property-name t)
  (setq loccur-overlay-list nil))


(defun loccur-create-overlay-bounds-btw-lines (buffer-matches)
  "Create a list of overlays between matched lines BUFFER-MATCHES."
  (let ((prev-end (point-min))
        (overlays (list)))
    (when buffer-matches
      (mapc (lambda (line)
              (let ((beginning (car line)))
                (unless ( = (- beginning prev-end) 1)
                  (let ((ovl-end  (1- beginning)))
                    (push (list prev-end ovl-end) overlays)))
                (setq prev-end (nth 3 line))))
            buffer-matches)
      (push (list (1+ prev-end) (point-max)) overlays)
      (setq overlays (nreverse overlays)))))


(defun loccur-find-matches (regex)
  "Find all occurences in the current buffer for given REGEX.

Returns a list of 4-number tuples, specifying begnning of the line,
1st match begin of a line, 1st match end of a line, end of a line
containing match"
  (save-excursion
    ;; Go to the beginnig of buffer
    (goto-char (point-min))
    ;; Set initial values for variables
    (let ((endpoint nil)
          (lines (list)))
      ;; Search loop
      (while (not (eobp))
        ;; if something found
        (when (setq endpoint (re-search-forward regex nil t))
          (save-excursion
            (let ((found-begin (match-beginning 0))
                  (found-end (match-end 0)))
              ;; Get the start and the and of the matching line
              ;; and store it to the overlays array
              (goto-char found-begin)
              (setq endpoint (line-end-position))
              (push (list (line-beginning-position)
                          found-begin
                          found-end
                          endpoint) lines)))
          ;; maybe add some code to highlight matches like in occur-mode?
          ;; goto the end of line for any case
          (goto-char endpoint))
        (forward-line 1))
      (setq lines (nreverse lines)))))

        
    


(provide 'loccur)
;;; loccur.el ends here
