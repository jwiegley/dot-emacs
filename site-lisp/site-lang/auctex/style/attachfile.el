;;; attachfile.el --- AUCTeX style for `attachfile.sty' (v1.6)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-04-11
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for `attachfile.sty' (v1.6) from 2015/04/04.
;; `attachfile.sty' is part of TeXLive.

;;; Code:
(defvar LaTeX-attachfile-key-val-options
  '(("appearance" ("true" "false"))
    ("author")
    ("color")
    ("created")
    ("date")
    ("description")
    ("icon" ("Graph" "Paperclip" "PushPin" "Tag"))
    ;; This can only be a small excerpt:
    ("mimetype"
     ("application/javascript"
      "application/pdf"
      "application/postscript"
      "application/vnd.ms-excel"
      "application/vnd.ms-powerpoint"
      "application/zip"
      "audio/mpeg"
      "audio/ogg"
      "image/jpeg"
      "image/png"
      "image/tiff"
      "text/csv"
      "text/plain"
      "video/H264"
      "video/mp4"))
    ("modified")
    ("print" ("true" "false"))
    ("size")
    ("subject")
    ("timezone")
    ("zoom"  ("true" "false")))
  "Key=value options for attachfile macros.")

(TeX-add-style-hook
 "attachfile"
 (lambda ()
   ;; Run style hook for packages loaded by attachfile; both packages
   ;; are required for running LaTeX, but not necessary within AUCTeX
   (TeX-run-style-hooks "hyperref" "color")

   (TeX-add-symbols
    ;; \attachfile[<options>]{<filename>}
    '("attachfile"
      [TeX-arg-key-val LaTeX-attachfile-key-val-options]
      (TeX-arg-eval
       (lambda ()
	 (let ((atfi (file-relative-name
		      (read-file-name "File to attach: "))))
	   (format "%s" atfi)))))

    ;; \noattachfile[<options>]
    '("noattachfile"
      [TeX-arg-key-val LaTeX-attachfile-key-val-options] )

    ;; \textattachfile[<options>]{<filename>}{<text>}
    '("textattachfile"
      [TeX-arg-key-val LaTeX-attachfile-key-val-options]
      (TeX-arg-eval
       (lambda ()
	 (let ((atfi (file-relative-name
		      (read-file-name "File to attach: "))))
	   (format "%s" atfi))))
      t)

    ;; \notextattachfile[<options>]{<text>}
    '("notextattachfile"
      [TeX-arg-key-val LaTeX-attachfile-key-val-options] t)

    ;; \attachfilesetup{<options>}
    '("attachfilesetup"
      (TeX-arg-key-val LaTeX-attachfile-key-val-options)))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("attachfilesetup"  "{")
				("attachfile"       "[{")
				("noattachfile"     "[")
				("textattachfile"   "[{{")
				("notextattachfile" "[{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-attachfile-package-options nil
  "Prompt for package options for the attachfile package.")

;;; attachfile.el ends here
