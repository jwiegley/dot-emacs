;;; muse-blosxom.el --- publish a document tree for serving by (py)Blosxom

;; Copyright (C) 2004, 2005, 2006, 2007, 2008, 2009, 2010
;;   Free Software Foundation, Inc.

;; Author: Michael Olson <mwolson@gnu.org>
;; Date: Wed, 23 March 2005

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

;; The Blosxom publishing style publishes a tree of categorised files
;; to a mirrored tree of stories to be served by blosxom.cgi or
;; pyblosxom.cgi.
;;
;; Serving entries with (py)blosxom
;; --------------------------------
;;
;; Each Blosxom file must include `#date yyyy-mm-dd', or optionally
;; the longer `#date yyyy-mm-dd-hh-mm', a title (using the `#title'
;; directive) plus whatever normal content is desired.
;;
;; The date directive is not used directly by (py)blosxom or this
;; program.  You need to find two additional items to make use of this
;; feature.
;;
;;  1. A script to gather date directives from the entire blog tree
;;     into a single file.  The file must associate a blog entry with
;;     a date.
;;
;;  2. A plugin for (py)blosxom that reads this file.
;;
;; These 2 things are provided for pyblosxom in the contrib/pyblosxom
;; subdirectory.  `getstamps.py' provides the 1st service, while
;; `hardcodedates.py' provides the second service.  Eventually it is
;; hoped that a blosxom plugin and script will be found/written.
;;
;; Alternately, the pyblosxom metadate plugin may be used.  On the
;; plus side, there is no need to run a script to gather the date.  On
;; the downside, each entry is read twice rather than once when the
;; page is rendered.  Set the value of muse-blosxom-use-metadate to
;; non-nil to enable adding a #postdate directive to all published
;; files.  You can do this by:
;;
;; M-x customize-variable RET muse-blosxom-use-metadate RET
;;
;; With the metadate plugin installed in pyblosxom, the date set in
;; this directive will be used instead of the file's modification
;; time.  The plugin is included with Muse at
;; contrib/pyblosxom/metadate.py.
;;
;; Generating a Muse project entry
;; -------------------------------
;;
;; Muse-blosxom has some helper functions to make specifying
;; muse-blosxom projects a lot easier.  An example follows.
;;
;; (setq muse-project-alist
;;       `(("blog"
;;          (,@(muse-project-alist-dirs "~/path/to/blog-entries")
;;           :default "index")
;;          ,@(muse-project-alist-styles "~/path/to/blog-entries"
;;                                       "~/public_html/blog"
;;                                       "blosxom-xhtml")
;;         )))
;;
;; Note that we need a backtick instead of a single quote on the
;; second line of this example.
;;
;; Creating new blog entries
;; -------------------------
;;
;; There is a function called `muse-blosxom-new-entry' that will
;; automate the process of making a new blog entry.  To make use of
;; it, do the following.
;;
;;  - Customize `muse-blosxom-base-directory' to the location that
;;    your blog entries are stored.
;;
;;  - Assign the `muse-blosxom-new-entry' function to a key sequence.
;;    I use the following code to assign this function to `C-c p l'.
;;
;;    (global-set-key "\C-cpl" 'muse-blosxom-new-entry)
;;
;;  - You should create your directory structure ahead of time under
;;    your base directory.  These directories, which correspond with
;;    category names, may be nested.
;;
;;  - When you enter this key sequence, you will be prompted for the
;;    category of your entry and its title.  Upon entering this
;;    information, a new file will be created that corresponds with
;;    the title, but in lowercase letters and having special
;;    characters converted to underscores.  The title and date
;;    directives will be inserted automatically.
;;
;; Using tags
;; ----------
;;
;; If you wish to keep all of your blog entries in one directory and
;; use tags to classify your entries, set `muse-blosxom-use-tags' to
;; non-nil.
;;
;; For this to work, you will need to be using the PyBlosxom plugin at
;; http://pyblosxom.sourceforge.net/blog/registry/meta/Tags.

;;; Contributors:

;; Gary Vaughan (gary AT gnu DOT org) is the original author of
;; `emacs-wiki-blosxom.el', which is the ancestor of this file.

;; Brad Collins (brad AT chenla DOT org) ported this file to Muse.

;; Björn Lindström (bkhl AT elektrubadur DOT se) made many valuable
;; suggestions.

;; Sasha Kovar (sasha AT arcocene DOT org) fixed
;; muse-blosxom-new-entry when using tags and also implemented support
;; for the #postdate directive.

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Blosxom Publishing
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse-project)
(require 'muse-publish)
(require 'muse-html)

(defgroup muse-blosxom nil
  "Options controlling the behavior of Muse Blosxom publishing.
See `muse-blosxom' for more information."
  :group 'muse-publish)

(defcustom muse-blosxom-extension ".txt"
  "Default file extension for publishing Blosxom files."
  :type 'string
  :group 'muse-blosxom)

(defcustom muse-blosxom-header
  "<lisp>(concat (muse-publishing-directive \"title\") \"\\n\"
  (when muse-blosxom-use-metadate
    (let ((date (muse-publishing-directive \"date\")))
      (when date (concat \"#postdate \"
                         (muse-blosxom-format-date date) \"\\n\"))))
  (when muse-blosxom-use-tags
    (let ((tags (muse-publishing-directive \"tags\")))
      (when tags (concat \"#tags \" tags \"\\n\")))))</lisp>"
  "Header used for publishing Blosxom files.  This may be text or a filename."
  :type 'string
  :group 'muse-blosxom)

(defcustom muse-blosxom-footer ""
  "Footer used for publishing Blosxom files.  This may be text or a filename."
  :type 'string
  :group 'muse-blosxom)

(defcustom muse-blosxom-base-directory "~/Blog"
  "Base directory of blog entries.
This is the top-level directory where your Muse blog entries may be found."
  :type 'directory
  :group 'muse-blosxom)

(defcustom muse-blosxom-use-tags nil
  "Determine whether or not to enable use of the #tags directive.

If you wish to keep all of your blog entries in one directory and
use tags to classify your entries, set `muse-blosxom-use-tags' to
non-nil.

For this to work, you will need to be using the PyBlosxom plugin
at http://pyblosxom.sourceforge.net/blog/registry/meta/Tags."
  :type 'boolean
  :group 'muse-blosxom)

(defcustom muse-blosxom-use-metadate nil
  "Determine whether or not to use the #postdate directive.

If non-nil, published entries include the original date (as specified
in the muse #date line) which can be read by the metadate PyBlosxom
plugin.

For this to work, you will need to be using the PyBlosxom plugin
at http://pyblosxom.sourceforge.net/blog/registry/date/metadate."
  :type 'boolean
  :group 'muse-blosxom)

;; Maintain (published-file . date) alist, which will later be written
;; to a timestamps file; not implemented yet.

(defvar muse-blosxom-page-date-alist nil)

(defun muse-blosxom-update-page-date-alist ()
  "Add a date entry to `muse-blosxom-page-date-alist' for this page."
  (when muse-publishing-current-file
    ;; Make current file be relative to base directory
    (let ((rel-file
           (concat
            (file-name-as-directory
             (or (muse-publishing-directive "category")
                 (file-relative-name
                  (file-name-directory
                   (expand-file-name muse-publishing-current-file))
                  (file-truename muse-blosxom-base-directory))))
            (file-name-nondirectory muse-publishing-current-file))))
      ;; Strip the file extension
      (when muse-ignored-extensions-regexp
        (setq rel-file (save-match-data
                         (and (string-match muse-ignored-extensions-regexp
                                            rel-file)
                              (replace-match "" t t rel-file)))))
      ;; Add to page-date alist
      (add-to-list
       'muse-blosxom-page-date-alist
       `(,rel-file . ,(muse-publishing-directive "date"))))))

;; Enter a new blog entry

(defun muse-blosxom-title-to-file (title)
  "Derive a file name from the given TITLE.

Feel free to overwrite this if you have a different concept of what
should be allowed in a filename."
  (muse-replace-regexp-in-string (concat "[^-." muse-regexp-alnum "]")
                                 "_" (downcase title)))

(defun muse-blosxom-format-date (date)
  "Convert a date string to PyBlosxom metadate plugin format."
  (apply #'format "%s-%s-%s %s:%s" (split-string date "-")))

;;;###autoload
(defun muse-blosxom-new-entry (category title)
  "Start a new blog entry with given CATEGORY.
The filename of the blog entry is derived from TITLE.
The page will be initialized with the current date and TITLE."
  (interactive
   (list
    (if muse-blosxom-use-tags
        (let ((tag "foo")
              (tags nil))
          (while (progn (setq tag (read-string "Tag (RET to continue): "))
                        (not (string= tag "")))
            (add-to-list 'tags tag t))
          tags)
      (funcall muse-completing-read-function
               "Category: "
               (mapcar 'list (muse-project-recurse-directory
                              muse-blosxom-base-directory))))
    (read-string "Title: ")))
  (let ((file (muse-blosxom-title-to-file title)))
    (muse-project-find-file
     file "blosxom" nil
     (if muse-blosxom-use-tags
         (directory-file-name muse-blosxom-base-directory)
       (concat (directory-file-name muse-blosxom-base-directory)
               "/" category))))
  (goto-char (point-min))
  (insert "#date " (format-time-string "%Y-%m-%d-%H-%M")
          "\n#title " title)
  (if muse-blosxom-use-tags
      (if (> (length category) 0)
          (insert (concat "\n#tags " (mapconcat #'identity category ","))))
    (unless (string= category "")
      (insert (concat "\n#category " category))))
  (insert "\n\n")
  (forward-line 2))

;;; Register the Muse Blosxom Publisher

(muse-derive-style "blosxom-html" "html"
                   :suffix    'muse-blosxom-extension
                   :link-suffix 'muse-html-extension
                   :header    'muse-blosxom-header
                   :footer    'muse-blosxom-footer
                   :after     'muse-blosxom-update-page-date-alist
                   :browser   'find-file)

(muse-derive-style "blosxom-xhtml" "xhtml"
                   :suffix    'muse-blosxom-extension
                   :link-suffix 'muse-xhtml-extension
                   :header    'muse-blosxom-header
                   :footer    'muse-blosxom-footer
                   :after     'muse-blosxom-update-page-date-alist
                   :browser   'find-file)

(provide 'muse-blosxom)

;;; muse-blosxom.el ends here
