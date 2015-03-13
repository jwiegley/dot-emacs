;; muse-latex2png.el --- generate PNG images from inline LaTeX code

;; Copyright (C) 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: Michael Olson <mwolson@gnu.org>
;; Created: 12-Oct-2005

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This was taken from latex2png.el, by Ganesh Swami <ganesh AT
;; iamganesh DOT com>, which was made for emacs-wiki.  It has since
;; been extensively rewritten for Muse.

;;; To do

;; Remove stale image files.  This could be done by making a function
;; for `muse-before-publish-hook' that deletes according to
;; (muse-page-name).

;;; Code

(require 'muse-publish)

(defgroup muse-latex2png nil
  "Publishing LaTeX formulas as PNG files."
  :group 'muse-publish)

(defcustom muse-latex2png-img-dest "./latex"
  "The folder where the generated images will be placed.
This is relative to the current publishing directory."
  :type 'string
  :group 'muse-latex2png)

(defcustom muse-latex2png-scale-factor 2.5
  "The scale factor to be used for sizing the resulting LaTeX output."
  :type 'number
  :group 'muse-latex2png)

(defcustom muse-latex2png-fg "Black"
  "The foreground color."
  :type 'string
  :group 'muse-latex2png)

(defcustom muse-latex2png-bg "Transparent"
  "The background color."
  :type 'string
  :group 'muse-latex2png)

(defcustom muse-latex2png-template
  "\\documentclass{article}
\\usepackage{fullpage}
\\usepackage{amssymb}
\\usepackage[usenames]{color}
\\usepackage{amsmath}
\\usepackage{latexsym}
\\usepackage[mathscr]{eucal}
%preamble%
\\pagestyle{empty}
\\begin{document}
{%code%}
\\end{document}\n"
  "The LaTeX template to use."
  :type 'string
  :group 'muse-latex2png)

(defun muse-latex2png-move2pubdir (file prefix pubdir)
  "Move FILE to the PUBDIR folder.

This is done so that the resulting images do not clutter your
main publishing directory.

Old files with PREFIX in the name are deleted."
  (when file
    (if (file-exists-p file)
        (progn
          (unless (file-directory-p pubdir)
            (message "Creating latex directory %s" pubdir)
            (make-directory pubdir))
          (copy-file file (expand-file-name (file-name-nondirectory file)
                                            pubdir)
                     t)
          (delete-file file)
          (concat muse-latex2png-img-dest "/" (file-name-nondirectory file)))
      (message "Cannot find %s!" file))))

(defun muse-latex2png (code prefix preamble)
  "Convert the LaTeX CODE into a png file beginning with PREFIX.
PREAMBLE indicates extra packages and definitions to include."
  (unless preamble
    (setq preamble ""))
  (unless prefix
    (setq prefix "muse-latex2png"))
  (let* ((tmpdir (cond ((boundp 'temporary-file-directory)
                        temporary-file-directory)
                       ((fboundp 'temp-directory)
                        (temp-directory))
                       (t "/tmp")))
         (texfile (expand-file-name
                   (concat prefix "__"  (format "%d" (abs (sxhash code))))
                   tmpdir))
         (defalt-directory default-directory))
    (with-temp-file (concat texfile ".tex")
      (insert muse-latex2png-template)
      (goto-char (point-min))
      (while (search-forward "%preamble%" nil t)
        (replace-match preamble nil t))
      (goto-char (point-min))
      (while (search-forward "%code%" nil t)
        (replace-match code nil t)))
    (setq default-directory tmpdir)
    (call-process "latex" nil nil nil texfile)
    (if (file-exists-p (concat texfile ".dvi"))
        (progn
          (call-process
           "dvipng" nil nil nil
           "-E"
           "-fg" muse-latex2png-fg
           "-bg" muse-latex2png-bg
           "-T" "tight"
           "-x" (format  "%s" (* muse-latex2png-scale-factor 1000))
           "-y" (format  "%s" (* muse-latex2png-scale-factor 1000))
           "-o" (concat texfile ".png")
           (concat texfile ".dvi"))
          (if (file-exists-p (concat texfile ".png"))
              (progn
                (delete-file (concat texfile ".dvi"))
                (delete-file (concat texfile ".tex"))
                (delete-file (concat texfile ".aux"))
                (delete-file (concat texfile ".log"))
                (concat texfile ".png"))
            (message "Failed to create png file")
            nil))
      (message (concat "Failed to create dvi file " texfile))
      nil)))

(defun muse-latex2png-region (beg end attrs)
  "Generate an image for the Latex code between BEG and END.
If a Muse page is currently being published, replace the given
region with the appropriate markup that displays the image.
Otherwise, just return the path of the generated image.

Valid keys for the ATTRS alist are as follows.

prefix: The prefix given to the image file.
preamble: Extra text to add to the Latex preamble.
inline: Display image as inline, instead of a block."
  (let ((end-marker (set-marker (make-marker) (1+ end)))
        (pubdir (expand-file-name
                 muse-latex2png-img-dest
                 (file-name-directory muse-publishing-current-output-path))))
    (save-restriction
      (narrow-to-region beg end)
      (let* ((text (buffer-substring-no-properties beg end))
             ;; the prefix given to the image file.
             (prefix (cdr (assoc "prefix" attrs)))
             ;; preamble (for extra options)
             (preamble (cdr (assoc "preamble" attrs)))
             ;; display inline or as a block
             (display (car (assoc "inline" attrs))))
        (when muse-publishing-p
          (delete-region beg end)
          (goto-char (point-min)))
        (unless (file-directory-p pubdir)
          (make-directory pubdir))
        (let ((path (muse-latex2png-move2pubdir
                     (muse-latex2png text prefix preamble)
                     prefix pubdir)))
          (when path
            (when muse-publishing-p
              (muse-insert-markup
               (if (muse-style-derived-p "html")
                   (concat "<img src=\"" path
                           "\" alt=\"latex2png equation\" "
                           (if display (concat "class=\"latex-inline\"")
                             (concat "class=\"latex-display\""))
                           (if (muse-style-derived-p "xhtml")
                               " />"
                             ">")
                           (muse-insert-markup "<!-- " text "-->"))
                 (let ((ext (or (file-name-extension path) ""))
                       (path (muse-path-sans-extension path)))
                   (muse-markup-text 'image path ext))))
              (goto-char (point-max)))
            path))))))

(defun muse-publish-latex-tag (beg end attrs)
  "If the current style is not Latex-based, generate an image for the
given Latex code.  Otherwise, don't do anything to the region.
See `muse-latex2png-region' for valid keys for ATTRS."
  (unless (assoc "prefix" attrs)
    (setq attrs (cons (cons "prefix"
                            (concat "latex2png-" (muse-page-name)))
                      attrs)))
  (if (or (muse-style-derived-p "latex") (muse-style-derived-p "context"))
      (muse-publish-mark-read-only beg end)
    (muse-latex2png-region beg end attrs)))

(put 'muse-publish-latex-tag 'muse-dangerous-tag t)

(defun muse-publish-math-tag (beg end)
  "Surround the given region with \"$\" characters.  Then, if the
current style is not Latex-based, generate an image for the given
Latex math code.

If 6 or more spaces come before the tag, and the end of the tag
is at the end of a line, then surround the region with the
equivalent of \"$$\" instead.  This causes the region to be
centered in the published output, among other things."
  (let* ((centered (and (re-search-backward
                         (concat "^[" muse-regexp-blank "]\\{6,\\}\\=")
                         nil t)
                        (save-excursion
                          (save-match-data
                            (goto-char end)
                            (looking-at (concat "[" muse-regexp-blank "]*$"))))
                        (prog1 t
                          (replace-match "")
                          (when (and (or (muse-style-derived-p "latex")
                                         (muse-style-derived-p "context"))
                                     (not (bobp)))
                            (backward-char 1)
                            (if (bolp)
                                (delete-char 1)
                              (forward-char 1)))
                          (setq beg (point)))))
         (tag-beg (if centered
                      (if (muse-style-derived-p "context")
                          "\\startformula " "\\[ ")
                    "$"))
         (tag-end (if centered
                      (if (muse-style-derived-p "context")
                          " \\stopformula" " \\]")
                    "$"))
         (attrs (nconc (list (cons "prefix"
                                   (concat "latex2png-" (muse-page-name))))
                       (if centered nil
                         '(("inline" . t))))))
    (goto-char beg)
    (muse-insert-markup tag-beg)
    (goto-char end)
    (muse-insert-markup tag-end)
    (if (or (muse-style-derived-p "latex") (muse-style-derived-p "context"))
        (muse-publish-mark-read-only beg (point))
      (muse-latex2png-region beg (point) attrs))))

(put 'muse-publish-math-tag 'muse-dangerous-tag t)

;;; Insinuate with muse-publish

(add-to-list 'muse-publish-markup-tags
             '("latex" t t nil muse-publish-latex-tag)
             t)

(add-to-list 'muse-publish-markup-tags
             '("math" t nil nil muse-publish-math-tag)
             t)

(provide 'muse-latex2png)
;;; muse-latex2png.el ends here
