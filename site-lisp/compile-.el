;;; compile-.el --- Extensions to `compile.el'.
;;
;; Filename: compile-.el
;; Description: Extensions to `compile.el'
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2004-2015, Drew Adams, all rights reserved.
;; Created: Tue Nov 16 17:04:11 2004
;; Version: 0
;; Package-Requires: ()
;; Last-Updated: Thu Jan  1 10:29:52 2015 (-0800)
;;           By: dradams
;;     Update #: 120
;; URL: http://www.emacswiki.org/compile-.el
;; Doc URL: http://www.emacswiki.org/GrepPlus
;; Doc URL: http://www.emacswiki.org/CompilationMode
;; Keywords: tools, processes
;; Compatibility: GNU Emacs: 21.x, 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `avoid', `fit-frame', `frame-fns'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Extensions to `compile.el'.
;;
;;  See also the companion file `compile+.el', if you are using Emacs
;;  22 or later.
;;
;;        `compile-.el' should be loaded before `compile.el'.
;;        `compile+.el' should be loaded after `compile.el'.
;;
;;  Put this in your initialization file (`~/.emacs'):
;;
;;    (require 'compile-)
;;
;;  Face suggestion (what I use):
;;
;;    `next-error': SkyBlue background, no inheritance
;;
;;
;;  New face defined here:
;;
;;  `compilation-mouseover' - Use instead of highlight for mouse-face.
;;
;;  Function `fit-1-window-frames-on' (defined in `fit-frame.el') is
;;  added here to `compilation-finish-functions'.
;;
;;
;;  ***** NOTE: The following variable defined in `compile.el'
;;              has been REDEFINED HERE:
;;
;;  `compilation-message-face' -
;;     We set the default value to nil, to get rid of underlining.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2011/08/30 dadams
;;     Do not change next-error face - just suggest changes.
;; 2011/01/03 dadams
;;     Added autoload cookie for the defcustom.  Corrected install instructions.
;; 2006/04/02 dadams
;;     Added defcustom of compilation-message-face (nil) to get rid of underlining.
;; 2005/12/26 dadams
;;     Updated parent groups.
;; 2005/12/16 dadams
;;     Added: compilation-mouseover.
;;     Removed: compile-regexp-face.  Use next-error face, not compile-regexp-face.
;; 2004/11/26 dadams
;;     Require frame-fns.el[c].
;; 2004/11/16 dadams
;;     New version for Emacs 21.  Old version renamed to compile-20.el.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'fit-frame nil t) ;; (no error if not found): fit-frame
(require 'frame-fns nil t) ;; 1-window-frames-on

;;;;;;;;;;;;;;;;;;;;;;;;;


;; Use nil, not `underline', to turn off underlining.
;;;###autoload
(defcustom compilation-message-face nil
  "*Face name to use for whole messages.
Faces `compilation-error-face', `compilation-warning-face',
`compilation-info-face', `compilation-line-face' and
`compilation-column-face' get prepended to this, when applicable."
  :type 'face :group 'compilation :version "22.1")

;; Instead of `highlight', which is hard-coded in `compile.el'.
;;;###autoload
(defface compilation-mouseover '((t (:underline t)))
  "*Face used to highlight text the mouse is over."
  :group 'compilation :group 'font-lock-highlighting-faces)

(unless (facep 'next-error)
  (defface next-error '((t (:background "SkyBlue")))
    "Face used to highlight next error locus."
    :group 'next-error))
                                   

;; Resize frame to fit buffer - hook `compilation-finish-functions'.
(when (and (fboundp 'fit-frame) (fboundp '1-window-frames-on))
  (defun fit-1-window-frames-on (buf &optional ignored)
    "Resize buffer BUF's one-window frame(s) to fit the buffer.
Usable, e.g., as a member of `compilation-finish-functions'."
    ;; Optional arg IGNORED is ignored.
    ;; It is for compatibility with `compilation-finish-functions'.
    (let ((frs (1-window-frames-on buf)))
      (while frs
        (fit-frame (car frs))           ; Defined in `fit-frame.el'.
        (setq frs (cdr frs)))))
  (add-hook 'compilation-finish-functions 'fit-1-window-frames-on))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'compile-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile-.el ends here
