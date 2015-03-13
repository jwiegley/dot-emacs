;;; smart-forward.el --- Semantic navigatioin

;; Copyright (C) 2011 Magnar Sveen

;; Author: Magnar Sveen <magnars@gmail.com>
;; Keywords: navigation
;; Version: 1.0.0
;; Package-Requires: ((expand-region "0.8.0"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; smart-forward gives you semantic navigation, building on
;; [expand-region](https://github.com/magnars/expand-region.el). It is most easily
;; explained by example:

;;    function test() {
;;      return "semantic navigation";
;;    }

;; With point at the start of the quotes,

;;  * `smart-forward` would go to the end of the quotes
;;  * `smart-backward` would go to the start of `return`, then to the `{`.
;;  * `smart-up` would go to the `{`
;;  * `smart-down` would go to the `}`

;; I use M-up/down/left/right arrows for this.

;; ## Installation

;; Start by installing
;; [expand-region](https://github.com/magnars/expand-region.el).

;;     (require 'smart-forward)
;;     (global-set-key (kbd "M-<up>") 'smart-up)
;;     (global-set-key (kbd "M-<down>") 'smart-down)
;;     (global-set-key (kbd "M-<left>") 'smart-backward)
;;     (global-set-key (kbd "M-<right>") 'smart-forward)

;; ## Contribute

;; smart-forward is a thin wrapper around expand-region. Most fixes to
;; smart-forward belong there.

;;; Code:

(require 'expand-region)

(defun smart--name-contains-inside-p (f)
  (string-match-p "\\(inside\\|inner\\)" (format "%S" f)))

(defun smart--er-try-list-without-inside ()
  (remove-if 'smart--name-contains-inside-p er/try-expand-list))

(defun smart--only-letters-in-region ()
  (string-match-p "^\\s'*\\(\\s_\\|\\sw\\)+$" (buffer-substring (region-beginning)
                                                                (region-end))))

;; er mange expansions som matcher word ... method-call, for eksempel
;; må heller expande videre dersom det som er selecta matcher en word-regexp

(defun smart-forward ()
  (interactive)
  (when (= (point) (point-max))
    (error "End of buffer"))
  (let ((expand-region-fast-keys-enabled nil)
        (_mark (set-marker (make-marker) (mark)))
        (mark-ring mark-ring)
        (mark-active mark-active)
        (p (point)))
    (deactivate-mark)
    (flet ((message (&rest args) nil))
      (er/expand-region 1)
      (while (or (<= (mark) p)
                 (smart--only-letters-in-region))
        (er/expand-region 1)))
    (exchange-point-and-mark)
    (set-marker (mark-marker) _mark)))

(defun smart-backward ()
  (interactive)
  (when (= (point) (point-min))
    (error "Beginning of buffer"))
  (let ((expand-region-fast-keys-enabled nil)
        (_mark (set-marker (make-marker) (mark)))
        (mark-ring mark-ring)
        (mark-active mark-active)
        (p (point)))
    (deactivate-mark)
    (flet ((message (&rest args) nil))
      (er/expand-region 1)
      (while (or (>= (point) p)
                 (smart--only-letters-in-region))
        (er/expand-region 1)))
    (deactivate-mark)
    (set-marker (mark-marker) _mark)))

(defun smart-down ()
  (interactive)
  (when (= (point) (point-max))
    (error "End of buffer"))
  (if (= (line-number-at-pos) (line-number-at-pos (point-max)))
      (goto-char (point-max))
    (let ((expand-region-fast-keys-enabled nil)
          (_mark (set-marker (make-marker) (mark)))
          (mark-ring mark-ring)
          (mark-active mark-active)
          (l (line-number-at-pos))
          (er/try-expand-list (smart--er-try-list-without-inside)))
      (deactivate-mark)
      (flet ((message (&rest args) nil))
        (er/expand-region 1)
        (while (<= (line-number-at-pos (mark)) l)
          (er/expand-region 1)))
      (exchange-point-and-mark)
      (deactivate-mark)
      (set-marker (mark-marker) _mark))))

(defun smart-up ()
  (interactive)
  (when (= (point) (point-min))
    (error "Beginning of buffer"))
  (if (= (line-number-at-pos) (line-number-at-pos (point-min)))
      (goto-char (point-min))
    (let ((expand-region-fast-keys-enabled nil)
          (_mark (set-marker (make-marker) (mark)))
          (mark-ring mark-ring)
          (mark-active mark-active)
          (l (line-number-at-pos))
          (er/try-expand-list (smart--er-try-list-without-inside)))
      (deactivate-mark)
      (flet ((message (&rest args) nil))
        (er/expand-region 1)
        (while (>= (line-number-at-pos) l)
          (er/expand-region 1)))
      (deactivate-mark)
      (set-marker (mark-marker) _mark))))

(provide 'smart-forward)

;;; smart-forward.el ends here
