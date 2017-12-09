;;; js3-mode.el --- An improved JavaScript editing mode
;;;

;;; js3-head.el

;; Author:  Thom Blake (webmaster@thomblake.com)
;; Authors of historical versions:
;;  (espresso-mode) Karl Landstrom <karl.landstrom@brgeight.se>
;;  (js2-mode)      Steve Yegge (steve.yegge@gmail.com)
;;  (js-mode)       Daniel Colascione <dan.colascione@gmail.com>
;; With some code from: https://github.com/mooz/js2-mode/
;;
;; Keywords:  javascript languages

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.

;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA

;;; Commentary:

;; This JavaScript editing mode supports:
;;
;;  - the full JavaScript language through version 1.8
;;  - support for most Rhino and SpiderMonkey extensions from 1.5 to 1.8
;;  - accurate syntax highlighting using a recursive-descent parser
;;  - syntax-error and strict-mode warning reporting
;;  - smart line-wrapping within comments (Emacs 22+) and strings
;;  - code folding:
;;    - show some or all function bodies as {...}
;;    - show some or all block comments as /*...*/
;;  - context-sensitive menu bar and popup menus
;;  - code browsing using the `imenu' package
;;  - typing helpers (e.g. inserting matching braces/parens)
;;  - many customization options
;;
;; It is only compatible with GNU Emacs versions 21 and higher (not XEmacs).
;;
;; Installation:
;;
;;  - put `js3.el' somewhere in your emacs load path
;;  - M-x byte-compile-file RET <path-to-js3.el> RET
;;    Note:  it will refuse to run unless byte-compiled
;;  - add these lines to your .emacs file:
;;    (autoload 'js3-mode "js3" nil t)
;;    (add-to-list 'auto-mode-alist '("\\.js$" . js3-mode))
;;
;; To customize how it works:
;;   M-x customize-group RET js3-mode RET
;;
;; The variable `js3-mode-version' is a date stamp.  When you upgrade
;; to a newer version, you must byte-compile the file again.
;;
;; Notes:
;;
;; This mode is different in many ways from standard Emacs language editing
;; modes, inasmuch as it attempts to be more like an IDE.  If this drives
;; you crazy, it IS possible to customize it to be more like other Emacs
;; editing modes.  Please customize the group `js3-mode' to see all of the
;; configuration options.
;;
;; Some of the functionality does not work in Emacs 21 -- upgrading to
;; Emacs 22 or higher will get you better results.  If you byte-compiled
;; js3.el with Emacs 21, you should re-compile it for Emacs 22.
;;
;; This mode does not yet work with "multi-mode" modes such as mmm-mode
;; and mumamo, although it could possibly be made to do so with some effort.
;; This means that js3-mode is currently only useful for editing JavaScript
;; files, and not for editing JavaScript within <script> tags or templates.
;;
;; Please submit bug reports to github at https://github.com/thomblake/js3-mode

;;; Code:

;;; js3-head.el ends here
