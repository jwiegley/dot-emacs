;;; popup-pos-tip.el -- pos-tip.el wrapper library for programs using popup.el

;; Copyright (C) 2010  S. Irie

;; Author: S. Irie
;; Maintainer: S. Irie
;; Keywords: Tooltip

(defconst popup-pos-tip-version "0.1.2")

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

;; This program provides some functions which are compatible with the
;; ones provided by popup.el. User can easily replace popup.el's tooltip
;; functions by defining advice (see below).

;; Settings:
;;
;; Save this file as popup-pos-tip.el in a directory which is listed
;; in load-path, and add the following in your .emacs file:
;;
;; (require 'popup-pos-tip)
;; (defadvice popup-tip
;;   (around popup-pos-tip-wrapper (string &rest args) activate)
;;   (if (eq window-system 'x)
;;       (apply 'popup-pos-tip string args)
;;     ad-do-it))

;; History:
;; 2010-04-29  S. Irie
;;         * Changed `popup-pos-tip' to hide tooltip after waiting key event
;;         * Fixed incorrect tooltip width for multibyte character string
;;         * Added constant `popup-pos-tip-version'
;;         * Version 0.1.2
;;
;; 2010-04-16  S. Irie
;;         * Changed `popup-pos-tip' not to fill paragraph unless exceeding :width
;;         * Version 0.1.1
;;
;; 2010-03-29  S. Irie
;;         * First release
;;         * Version 0.1.0

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'popup)
(require 'pos-tip)

(defun* popup-pos-tip (string
                       &key
                       point
                       (around t)
                       width
                       (height 15) ; dummy
                       min-height  ; dummy
                       truncate    ; dummy
                       margin
                       margin-left
                       margin-right
                       scroll-bar  ; dummy
                       parent
                       parent-offset
                       nowait
                       prompt
                       &aux rows)
  (if (bufferp string)
      (setq string (with-current-buffer string (buffer-string))))

  (or width (setq width popup-tip-max-width))
  (and (eq margin t) (setq margin 1))
  (or margin-left (setq margin-left (or margin 0)))
  (or margin-right (setq margin-right (or margin 0)))
  (and (null point) parent
       (setq point (popup-child-point parent parent-offset)))

  (setq rows (pos-tip-split-string string
                                   (+ margin-left width)
                                   margin-left
                                   (and (> (car (pos-tip-string-width-height string))
                                           width)
                                        'none))
        string (let ((rmargin-str (make-string margin-right ?\s)))
                 (propertize (concat (mapconcat 'identity
                                                rows
                                                (concat rmargin-str "\n"))
                                     rmargin-str)
                             'face 'pos-tip-temp))
        width (+ (apply 'max (mapcar 'string-width rows))
                 margin-right)
        height (length rows))

  (face-spec-reset-face 'pos-tip-temp)
  (set-face-font 'pos-tip-temp (frame-parameter nil 'font))

  (pos-tip-show-no-propertize string
                              'popup-tip-face
                              point nil 0
                              (pos-tip-tooltip-width width
                                                     (frame-char-width))
                              (pos-tip-tooltip-height height
                                                      (frame-char-height))
                              nil
                              (- (* margin-left (frame-char-width)))
                              (and (not around) 0))

  (unless nowait
    (clear-this-command-keys)
    (unwind-protect
        (push (read-event prompt) unread-command-events)
      (pos-tip-hide))
    t))

(defun popup-pos-tip-show-quick-help (menu &optional item &rest args)
  (let* ((point (plist-get args :point))
         (around nil)
         (parent-offset (popup-offset menu))
         (doc (popup-menu-documentation menu item)))
    (when (stringp doc)
      (if (popup-hidden-p menu)
          (setq around t
                menu nil
                parent-offset nil)
        (setq point nil))
      (apply 'popup-pos-tip
             doc
             :point point
             :around around
             :parent menu
             :parent-offset parent-offset
             args))))

(provide 'popup-pos-tip)

;;;
;;; popup-pos-tip.el ends Here
