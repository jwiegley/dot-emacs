;;; x-symbol-site.el --- sample customization of package x-symbol

;; Copyright (C) 1996-1998 Free Software Foundation, Inc.
;;
;; Author: Christoph Wedler <wedler@users.sourceforge.net>
;; Maintainer: (Please use `M-x x-symbol-package-bug' to contact the maintainer)
;; Version: 3.4
;; Keywords: WYSIWYG, LaTeX, HTML, wp, math, internationalization
;; X-URL: http://x-symbol.sourceforge.net/

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;; If you want to use package x-symbol, please visit the URL (use
;; \\[x-symbol-package-web]) and read the info (use \\[x-symbol-package-info]).

;; This file contains the elisp code for the installation of package x-symbol.
;; Copy the first lines of the code, which are also mentioned in the
;; installation instructions, into your `~/.emacs' or `default.el'.  The direct
;; use of this file via `(load "x-symbol-site")' is deprecated.

;;; Code:

;;(setq x-symbol-data-directory (expand-file-name "~/.xemacs/etc/x-symbol/"))
(unless (featurep 'mule) (setq x-symbol-compose-key '(multi-key)))
(require 'x-symbol-hooks)
(x-symbol-initialize)

;; Use GNUs make for creation of executables:
;;(defvar x-symbol-exec-compile-command "gmake -k")

;; Do not expand \FROM to \TO if we have an abbreviation from FROM to TO:
;;(custom-set-variables '(words-include-escapes t))

;; Set this if your normal font does not have registry iso8859-1:
;;(setq x-symbol-default-coding 'iso-8859-2) ; but not with Mule!

;; If you run x-symbol on tty, but never use \usepackage[latinN]{inputenc}
;; where N does not correspond to your "normal" font (e.g., if you only use
;; \usepackage[latin1]{inputenc}):
;;(setq x-symbol-latin-force-use nil)

;; If you would use XEmacs/Mule just for package X-Symbol
;;(setq x-symbol-mule-change-default-face t)

;; psgml-html:
;;(setq html-auto-sgml-entity-conversion nil) ; the default

;; If you `isearch' for x-symbol characters, it is a good idea to remove any
;; font property from the `isearch' face (the same for highlight), this could
;; be a problem with B/W monitors: -------------------------------------------
(remove-specifier (get (get-face 'isearch) 'font))
(set-face-foreground 'isearch "white" nil '(mono))
(set-face-background 'isearch "black" nil '(mono))
(remove-specifier (get (get-face 'highlight) 'font))
(set-face-underline-p 'highlight t nil '(mono))
;; Check also the faces `primary-selection', `secondary-selection',
;; `underline', `paren-match', `paren-blink-off', `paren-mismatch'.  Thanks to
;; Solofo Ramangalahy <solofo@mpi-sb.mpg.de> for this list.

;;; Local IspellPersDict: .ispell_xsymb
;;; x-symbol-site.el ends here
