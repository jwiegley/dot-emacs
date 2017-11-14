;;; org-autolist.el --- Improved list management in org-mode

;; Copyright (C) 2014 Calvin Young

;; Author: Calvin Young
;; Keywords: lists, checklists, org-mode
;; Homepage: https://github.com/calvinwyoung/org-autolist
;; Version: 0.12

;; This file is not part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; `org-autolist` makes org-mode lists behave more like lists in non-programming
;; editors such as Google Docs, MS Word, and OS X Notes.
;;
;; When editing a list item, pressing "Return" will insert a new list item
;; automatically. This works for both bullet points and checkboxes, so there's
;; no need to think about whether to use `M-<return>` or `M-S-<return>`. Similarly,
;; pressing "Backspace" at the beginning of a list item deletes the bullet /
;; checkbox, and moves the cursor to the end of the previous line.
;;
;; To enable org-autolist mode in the current buffer:
;;
;;   (org-autolist-mode)
;;
;; To enable it whenever you open an org file, add this to your init.el:
;;
;;   (add-hook 'org-mode-hook (lambda () (org-autolist-mode)))

;;; Code:
(require 'org)
(require 'org-element)

(defun org-autolist-beginning-of-item-after-bullet ()
  "Returns the position before the first character after the
bullet of the current list item.

This function uses the same logic as `org-beginning-of-line' when
`org-special-ctrl-a/e' is enabled"
  (save-excursion
    (beginning-of-line 1)
    (when (looking-at org-list-full-item-re)
      ;; Find the first white space character after bullet, and check-box, if
      ;; any. That point should be the return value of this function if found.
      (let ((box (match-end 3)))
        (if (not box) (match-end 1)
          (let ((after (char-after box)))
            (if (and after (= after ? )) (1+ box) box)))))))

(defun org-autolist-at-empty-item-description-p ()
  "Is point at an *empty* description list item?"
  (message "evaluating...")
  (org-list-at-regexp-after-bullet-p "\\(\\s-*\\)::\\(\\s-*$\\)"))

(defadvice org-return (around org-autolist-return)
  "Wraps the org-return function to allow the Return key to
automatically insert new list items.

- Pressing Return at the end of a list item inserts a new list item.
- Pressing Return at the end of a checkbox inserts a new checkbox.
- Pressing return at the beginning of an empty list or checkbox item
  outdents the item, or clears it if it's already at the outermost
  indentation level."
  ;; We should only invoke our custom logic if we're in a list item.
  (if (org-at-item-p)
      ;; If we're at the beginning of an empty list item, then try to outdent
      ;; it. If it can't be outdented (b/c it's already at the outermost
      ;; indentation level), then delete it.
      (if (and (eolp)
               (<= (point) (org-autolist-beginning-of-item-after-bullet)))
          (condition-case nil
              (call-interactively 'org-outdent-item)
            ('error (delete-region (line-beginning-position)
                                   (line-end-position))))

        ;; Now we can insert a new list item. The logic here is a little tricky
        ;; depending on the type of list we're dealing with.
        (cond
         ;; If we're on a checkbox item, then insert a new checkbox
         ((org-at-item-checkbox-p)
          (org-insert-todo-heading nil))

         ;; If we're in a description list, and the point is between the start
         ;; of the list (after the bullet) and the end of the list, then we
         ;; should simply insert a newline. This is a bit weird and inconsistent
         ;; w/ the UX for other list types, but we do this b/c `org-meta-return'
         ;; has some very strange behavior when executed in the middle of a
         ;; description list.
         ((and (org-at-item-description-p)
               (> (point) (org-autolist-beginning-of-item-after-bullet))
               (< (point) (line-end-position)))
          (newline))

         ;; Otherwise just let org-mode figure it out it.
         (t
          (org-meta-return))))
    ad-do-it))

(defadvice org-delete-backward-char (around org-autolist-delete-backward-char)
  "Wraps the org-delete-backward-char function to allow the Backspace
key to automatically delete list prefixes.

- Pressing backspace at the beginning of a list item deletes it and
  moves the cursor to the previous line.
- If the previous line is blank, then delete the previous line, and
  move the current list item up one line."
  ;; We should only invoke our custom logic if we're at the beginning of a list
  ;; item right after the bullet character.
  (if (and (org-at-item-p)
           (<= (point) (org-autolist-beginning-of-item-after-bullet)))
      ;; If the previous line is empty, then just delete the previous line (i.e.,
      ;; shift the list up by one line).
      (if (org-previous-line-empty-p)
          (delete-region (line-beginning-position)
                         (save-excursion (forward-line -1)
                                         (line-beginning-position)))

        ;; Otherwise we should delete to the end of the previous line.
        (progn
          ;; We should ensure that the cursor starts at the point after the
          ;; bullet. This allows us to delete a full checkbox if the cursor is
          ;; initially positioned in the middle of the checkbox.
          (goto-char (org-autolist-beginning-of-item-after-bullet))

          ;; For most lines, we want to delete from bullet point to the end of
          ;; the previous line. There are, however a few exceptions.
          (cond
           ;; If we're on the first line in the buffer, then we should just
           ;; delete the bullet point.n
           ((= 1 (line-number-at-pos))
            (delete-region (point) (line-beginning-position)))

           ;; If we're on a line with an empty description list, then
           ;; we should delete the full line since there's not point leaving it
           ;; around.
           ((org-autolist-at-empty-item-description-p)
            (delete-region (line-end-position)
                           (save-excursion (forward-line -1)
                                           (line-end-position))))

           ;; Otherwise we should delete to the end of the previous line by
           ;; default.
           (t
            (delete-region (point)
                           (save-excursion (forward-line -1)
                                           (line-end-position)))))))
    ad-do-it))

;;;###autoload
(define-minor-mode org-autolist-mode
  "Enables improved list management in org-mode."
  nil " Autolist" nil
  (cond
   ;; If enabling org-autolist-mode, then add our advice functions.
   (org-autolist-mode
    (ad-activate 'org-return)
    (ad-activate 'org-delete-backward-char))
   ;; Be sure to clean up after ourselves when org-autolist-mode gets disabled.
   (t
    (ad-deactivate 'org-return)
    (ad-deactivate 'org-delete-backward-char))))

(provide 'org-autolist)
;;; org-autolist.el ends here
