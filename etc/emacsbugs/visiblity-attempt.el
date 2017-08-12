;;; visiblity-attempt.el --- Test area for invisibility

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Proof General is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; Proof General is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Proof General. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Test area for invisibility
;;

;;; Code:

(defvar vis nil)

(overlay-put (make-overlay 18 22) 'invisible 'smaller)
(overlay-put (make-overlay 9 43) 'invisible 'larger)

(defun toggle-invis ()
  (interactive)
  (if vis 
      (add-to-invisibility-spec '(larger . t))
    (remove-from-invisibility-spec '(larger . t)))
  (setq vis (not vis)))


;; In this buffer:

;;    M-x eval-buffer RET
;;    M-x toggle-invis

;; The smaller area remains visible, although there is a surrounding
;; overlay which has an invisibility spec which should cover the
;; revealed characters.  Arguably a bug.






