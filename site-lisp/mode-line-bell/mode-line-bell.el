;;; mode-line-bell.el --- Flash the mode line instead of ringing the bell  -*- lexical-binding: t; -*-

;; Copyright (C) 2018  Steve Purcell

;; Author: Steve Purcell <steve@sanityinc.com>
;; Keywords: convenience

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

;; Enable the global minor mode `mode-line-bell-mode' to set
;; `ring-bell-function' to a function that will briefly flash the mode
;; line when the bell is rung.

;;; Code:

;;;###autoload
(defun mode-line-bell-flash ()
  "Flash the mode line momentarily."
  (invert-face 'mode-line)
  (run-with-timer 0.05 nil 'invert-face 'mode-line))


;;;###autoload
(define-minor-mode mode-line-bell-mode
  "Flash the mode line instead of ringing the bell."
  :lighter nil
  :global t
  (setq-default ring-bell-function (when mode-line-bell-mode
                                     'mode-line-bell-flash)))


(provide 'mode-line-bell)
;;; mode-line-bell.el ends here
