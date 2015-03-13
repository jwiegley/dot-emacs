;;; muse-mathml.el --- provide MathML support for Muse

;; Copyright (C) 2004, 2005, 2006 Free Software Foundation, Inc.

;; Author: Li Daobing (lidaobing AT gmail DOT com)
;; Keywords: Muse mathml hypermedia

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

;;;_* Commentary

;;;_ + Startup

;; 1. Get a copy of itex2MML and install it to `/usr/bin' or
;;    `/usr/local/bin'.
;;
;;    You can get a copy from
;;    `http://pear.math.pitt.edu/mathzilla/itex2mml.tar.gz'.

;; 2. Copy `itex2MML.py' to `/usr/bin' or `/usr/local/bin', if you
;;    do not have this file, create it and do a `chmod a+x itex2MML.py'.
;;    Its content is the following.

;; #!/usr/bin/env python
;; """A wrap for itex2MML
;;
;; Delete the extra blank line.
;;
;; You can use it as itex2MML.
;;
;; For example:
;;
;; echo '$a_b$' | itex2MML.py
;; """
;;
;; import sys
;; import os
;;
;; def main():
;;     fin, fo = os.popen2('itex2MML')
;;     fin.write(sys.stdin.read())
;;     fin.close()
;;     for line in fo:
;;         line = line.strip()
;;         if line:
;;             print line
;;
;; if __name__ == '__main__':
;;     main()

;; 3. Put `muse-math.el' into your `load-path'.

;; 4. Add the following to your .emacs file.
;;
;;    (require 'muse-mathml)

(require 'muse-html)
(require 'muse-publish)

(defgroup muse-mathml nil
  "Options controlling the behavior of Muse XHTML+MathML publishing.
See `muse-html' for more information."
  :group 'muse-publish)

(defcustom muse-mathml-extension ".xhtml"
  "Default file extension for publishing XHTML+MathML files."
  :type 'string
  :group 'muse-mathml)

(defcustom muse-mathml-style-sheet muse-xhtml-style-sheet
  "Store your stylesheet definitions here.
This is used in `muse-mathml-header'.
You can put raw CSS in here or a <link> tag to an external stylesheet.
This text may contain <lisp> markup tags.

An example of using <link> is as follows.

<link rel=\"stylesheet\" type=\"text/css\" charset=\"utf-8\" media=\"all\" href=\"/default.css\" />"
  :type 'string
  :group 'muse-mathml)

(defcustom muse-mathml-header
  "<?xml version=\"1.0\" encoding=\"<lisp>
  (muse-html-encoding)</lisp>\"?>
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.1 plus MathML 2.0//EN\"
    \"http://www.w3.org/TR/MathML2/dtd/xhtml-math11-f.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\"
xmlns:xlink=\"http://www.w3.org/1999/xlink\">
  <head>
    <title><lisp>
  (concat (muse-publishing-directive \"title\")
          (let ((author (muse-publishing-directive \"author\")))
            (if (not (string= author (user-full-name)))
                (concat \" (by \" author \")\"))))</lisp></title>
    <meta name=\"generator\" content=\"muse.el\" />
    <meta http-equiv=\"<lisp>muse-html-meta-http-equiv</lisp>\"
          content=\"<lisp>muse-html-meta-content-type</lisp>\" />
    <lisp>
      (let ((maintainer (muse-style-element :maintainer)))
        (when maintainer
          (concat \"<link rev=\\\"made\\\" href=\\\"\" maintainer \"\\\" />\")))
    </lisp>
    <lisp>muse-xhtml-style-sheet</lisp>
  </head>
  <body>
    <h1><lisp>
  (concat (muse-publishing-directive \"title\")
          (let ((author (muse-publishing-directive \"author\")))
            (if (not (string= author (user-full-name)))
                (concat \" (by \" author \")\"))))</lisp></h1>
    <!-- Page published by Emacs Muse begins here -->\n"
  "Header used for publishing XHTML+MathML files.
This may be text or a filename."
  :type 'string
  :group 'muse-mathml)

(defcustom muse-mathml-footer "
<!-- Page published by Emacs Muse ends here -->
  </body>
</html>\n"
  "Footer used for publishing XHTML+MathML files.
This may be text or a filename."
  :type 'string
  :group 'muse-mathml)

(defcustom muse-mathml-command
  (if (or (featurep 'executable)
          (load "executable" t t))
      (executable-find "itex2MML.py"))
  "Program to use to convert Latex text to MathML."
  :type 'string
  :group 'muse-mathml)

(defun muse-publish-mathml-tag (beg end)
  (if muse-mathml-command
      (muse-publish-command-tag
       beg end (list (cons "interp" muse-mathml-command)))
    (muse-publish-example-tag beg end)))

;; Add the <mathml> tag

(add-to-list 'muse-publish-markup-tags
             '("mathml" t nil muse-publish-mathml-tag)
             t)

;; Register the Muse MathML Publisher

(muse-derive-style "mathml" "xhtml"
                   :suffix    'muse-mathml-extension
                   :header    'muse-mathml-header
                   :footer    'muse-mathml-footer)

(provide 'muse-mathml)
;;; muse-mathml.el ends here
