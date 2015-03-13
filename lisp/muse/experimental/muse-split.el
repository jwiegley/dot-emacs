;;; muse-split.el --- split published Muse files

;; Copyright (C) 2006 Free Software Foundation, Inc.

;; Author: Phillip Lord <phillip.lord@newcastle.ac.uk>

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

;;; Status:

;; This works now, except that anchors will get broken, as they may
;; well point to the wrong thing.

;; Anchors are mostly working, some crashes in caching code. Have
;; realised that could just circumvent the anchors problem by always
;; pointing toward the full length entry which all of my split
;; functions generate now. Given the complexity that this has
;; introduced taht might not have been a bad idea.

;; These functions directly over-write the original versions in
;; muse-publish.

(require 'muse-publish)
(require 'assoc)
(eval-when-compile
  (require 'cl))

;; this code duplicates that in muse-publish-markup-regexps and should
;; be factored out. I use this style to pull directives from the front
;; of file.
(defvar muse-publish-presplit-markup-regexps
  `(
    ;; Handle any leading #directives
    (1200 "\\`#\\([a-zA-Z-]+\\)\\s-+\\(.+\\)\n+" 0 directive)
    ;; define anchor points
    (1500 "^\\(\\W*\\)#\\(\\S-+\\)\\s-*" 0 anchor)))

(defvar muse-publish-presplit-functions
  '((directive . muse-publish-presplit-directive)
    (anchor . muse-publish-presplit-anchor)))

;; oh dear, this function used to be so simple and now has got so
;; nasty. I'm sure I can amalgamate some of the let bindings and
;; lambda function.
(defun muse-publish-file (file style &optional output-dir force)
  "Publish the given file in list FILES.
If the argument FORCE is nil, each file is only published if it is
newer than the published version.  If the argument FORCE is non-nil,
the file is published no matter what."
  (interactive (cons (read-file-name "Publish file: ")
                     (muse-publish-get-info)))
  (setq style (muse-style style))
  (let* ((output-path (muse-publish-output-file file output-dir style))
         (output-suffix (muse-style-element :osuffix style))
         (muse-publishing-current-file file)
         (muse-publishing-style-in-use style)
         (muse-publish-split-file-split-values nil)
         (muse-publish-presplit-directive-store "")
         (muse-publish-presplit-anchor-location nil)
         (muse-publishing-targets-alist
          (muse-publish-split-file file))
         (target-list
          (mapcar
           (lambda(elem)
             (if output-suffix
                 (concat (file-name-sans-extension
                          (cdr (car elem)))
                         output-suffix)
               output-path))
           muse-publishing-targets-alist)))

    (when (or force
              ;; update if any of the files are out of date.
              (let ((outofdate nil))
                (mapc
                 (lambda(elem)
                   (if (file-newer-than-file-p file
                                               (car elem))
                       (setq outofdate t)))
                 muse-publishing-targets-alist)
                outofdate))

      (if (and muse-publish-report-threshhold
               (> (nth 7 (file-attributes file))
                  muse-publish-report-threshhold))
          (message "Publishing %s ..." file)
        ;; need to grab the directives.
        (muse-publish-presplit-publish file)
        ;; start a temp buffer for main data
        (muse-with-temp-buffer
          (muse-insert-file-contents file)
          (let ((mainbuffer (current-buffer))
                (subcontents))
            (mapc
             (lambda(elem)
               (muse-with-temp-buffer
                 ;; not handling the directives yet.
                 (save-excursion
                   (set-buffer mainbuffer)
                   (setq subcontents
                         (buffer-substring-no-properties
                          (cadr elem) (caddr elem))))
                 ;; insert the directives afresh.
                 (insert muse-publish-presplit-directive-store)
                 (insert subcontents)
                 (muse-publish-markup-buffer (muse-page-name file) style)
                 (let* ((backup-inhibited t))
                   (write-file (muse-publish-output-file (car elem)
                                                         output-dir style)))
                 (muse-style-run-hooks :final style file (car elem))))
             muse-publishing-targets-alist)))
        t))))

(defun muse-publish-presplit-publish(file)
  (muse-with-temp-buffer
    (muse-insert-file-contents file)
    (let ((muse-publish-markup-regexps muse-publish-presplit-markup-regexps)
          (muse-publish-markup-functions muse-publish-presplit-functions)
          (muse-publishing-styles)
          (muse-publish-presplit-splitting-file file))
      ;; great an empty style. The name is just wierd, so that
      ;; it won't preexist (which makes muse crash). The let
      ;; binding should mean that it disappears.
      (muse-define-style "ThePurposeIsNotToDescribeTheWorldButToChangeIt")
      (muse-publish-markup-buffer
       (muse-page-name "temp")
       "ThePurposeIsNotToDescribeTheWorldButToChangeIt"))))

(defun muse-publish-prepare-url (target &rest ignored)
  "Transform anchors and get published name, if TARGET is a page."
  (save-match-data
    (unless (or (string-match muse-url-regexp target)
                (string-match muse-image-regexp target)
                (string-match muse-file-regexp target))
      (setq target (if (string-match "#" target)
                       ;; is this a simple anchor, we need to check
                       ;; where it will be published.
                       (if (eq (aref target 0) ?\#)
                           (concat
                            (muse-publish-link-name
                             (muse-publish-split-file-for-anchor
                              muse-publishing-current-file
                              (substring target 1)))
                            target)
                         ;; it's not anchor simple anchor, so we need to
                         ;; put in the extension
                         (let
                             ((file (substring target 0 (match-beginning 0)))
                              (anchor (substring target (match-end 0))))
                           (concat (muse-publish-link-name
                                    (muse-publish-split-file-for-anchor
                                     (concat (file-name-directory
                                              muse-publishing-current-file)
                                             file "." muse-file-extension)
                                     anchor))
                                   "#" anchor)))
                     ;; it's not an anchor at all.
                     (muse-publish-link-name target))))
    target))

;; these are support functions

;; we currently have to store a lot of state to get this to work,
;; which is rather dissatisfying. All of it is let bound from
;; muse-publish-file. Wey hey for dynamic scoping.
(defvar muse-publish-presplit-directive-store nil
  "Stores directives from main file during splitting")

(defvar muse-publish-presplit-anchor-location nil
  "Stores anchors during publishing.")

(defvar muse-publish-split-file-split-values nil
  "Cache the values of split locations in files, during publish")

(defvar muse-publishing-targets-alist nil
  "Stores the targets to be published to.

Changing this will cause bad things to happen. ")

(defvar muse-publishing-style-in-use nil
  "Stores the style currently being published")

(defvar muse-publish-presplit-splitting-file nil
  "The file that we are current publishing for presplit")


(defun muse-publish-no-split-function (file)
  (muse-with-temp-buffer
    (muse-insert-file-contents file)
    (list `(,(file-name-sans-extension file) . (1 ,(point-max))))))

(defun muse-publish-split-file (file)
  "Calculate where to split the FILE.

FILE is the file to be split

This should return an alist of form (position . output-file)
where position is the last position that should appear in output-file"
  (let* ((split-function
          (muse-get-keyword
           :split muse-publishing-style-in-use t))
         (split-alist
          (if (not split-function)
              (muse-publish-no-split-function file)
            (funcall split-function file))))
    (aput 'muse-publish-split-file-split-values
          file split-alist)
    split-alist))

(defun muse-publish-presplit-directive (&optional name value)
  (unless name (setq name (match-string 1)))
  (unless value (setq value (match-string 2)))
  ;; store the directives.
  (setq muse-publish-presplit-directive-store
        (format "%s#%s %s\n"
                muse-publish-presplit-directive-store
                name value)))

(defun muse-publish-presplit-anchor()
  "Stores the location and names of anchors"
  (let ((alist (aget muse-publish-presplit-anchor-location
                     muse-publish-presplit-splitting-file)))

    (add-to-list 'alist
                 `(,(match-string 2) . ,(match-beginning 2)))
    (aput 'muse-publish-presplit-anchor-location
          muse-publish-presplit-splitting-file
          alist)))


;; ;;(setq muse-publish-split-file-split-values nil)
;; (setq muse-publish-split-file-split-values
;;       '(("d:/home/src/ht/home_website/journal-split/journal.muse"
;;          ("d:/home/src/ht/home_website/journal-split/journal-20060226" 875 1592)
;;          ("d:/home/src/ht/home_website/journal-split/journal-20060228" 417 874)
;;          ("d:/home/src/ht/home_website/journal-split/journal-20060303" 27 416)
;;          ("d:/home/src/ht/home_website/journal-split/journal-20060220" 1593 2957)
;;          ("d:/home/src/ht/home_website/journal-split/journal-all" 1 2957)
;;          ("d:/home/src/ht/home_website/journal-split/journal" 1 2957))))

;; ;; muse-publish-presplit-anchor-location's value is shown below.
;; ;; Value:
;; ;; (setq muse-publish-presplit-anchor-location nil)
;; (setq muse-publish-presplit-anchor-location
;;       '(("d:/home/src/ht/home_website/journal-split/journal.muse"
;;          ("semantic_enrichment" 1642)
;;          ("title" 2))
;;         ("d:/home/src/ht/home_website/journal-split/simple.muse"
;;          ("anchor7" 189)
;;          ("anchor3" 173)
;;          ("anchor2" 162)
;;          ("simple_anchor" 15))))

;; get the anchor locations
;;        (muse-publish-presplit-publish file)
;; get the split locations

;;          (muse-publish-split-file file))

(defun test1()
  (interactive)
  (message "%s" (muse-publish-split-file-for-anchor
                 "d:/home/src/ht/home_website/journal-split/journal.muse"
                 "semantic_enrichment")))

(defun muse-publish-split-file-for-anchor (base-file anchor)
  "Given a base file and an anchor, return the file into which
the anchor will be output"
  (let* (
         ;; this should be an alist, keyed on the anchor, valued on
         ;; either numbers, or file-locations
         (anchor-alist
          (or
           (aget muse-publish-presplit-anchor-location
                 base-file)
           (progn
             (muse-publish-presplit-publish base-file)
             (aget muse-publish-presplit-anchor-location
                   base-file))))

         ;; this should be a list of triples: file, start, stop.
         (split-list
          (or (aget muse-publish-split-file-split-values
                    base-file)
              (muse-publish-split-file base-file)))
         ;; this should be either the position of the anchor in a
         ;; buffer as an int, or a output file location
         (anchor-position-or-location
          (aget anchor-alist anchor))
         ;; this should definately be the output file location
         (anchor-output
          (if (stringp anchor-position-or-location)
              anchor-position-or-location
            (car
             (delete nil
                     (mapcar
                      (lambda(elem)
                        (if (and
                             (> anchor-position-or-location
                                (cadr elem))
                             (< anchor-position-or-location
                                (caddr elem)))
                            (car elem)))
                      split-list))))))

    ;; ensure that we put the location back into the stored list so
    ;; that we don't have to work it out next time
    (aput
     'anchor-alist anchor anchor-output)

    (aput 'muse-publish-presplit-anchor-location
          base-file anchor-alist)

    (file-name-nondirectory anchor-output)))


;; this is an example of why I would want to use the code.
(muse-derive-style "journal-html-by-day" "journal-html"
                   :split 'muse-journal-split-by-entry)

(muse-derive-style "journal-html-by-month" "journal-html"
                   :split 'muse-journal-split-by-month)


(defun muse-journal-split-by-entry (file)
  "Split a muse journal file into days"
  (muse-with-temp-buffer
    (muse-insert-file-contents file)
    (let* ((split-alist)
           (root-name (file-name-sans-extension file))
           (split-regexp "^\\* \\([0-9]\\{8\\}\\)")
           (current-position
            (if (re-search-forward split-regexp nil t)
                (- (match-beginning 0) 1)))
           (entry-name (match-string 1))
           (entry-location (match-beginning 0)))
      (while (re-search-forward split-regexp nil t)
        (setq entry-location (match-beginning 0))
        (add-to-list 'split-alist
                     `(,(concat root-name "-" entry-name)
                       ,current-position
                       ,(- entry-location 1)))
        (setq current-position entry-location
              entry-name (match-string 1)))

      (add-to-list 'split-alist
                   `(,(concat root-name "-" entry-name)
                     ,current-position
                     ,(point-max))
                   t)

      (add-to-list 'split-alist
                   `(,root-name
                     ,(cadr (car (last split-alist)))
                     ,(caddr (car (last split-alist))))
                   t)

      (add-to-list 'split-alist
                   `(,(concat root-name "-all")
                     1 ,(point-max))
                   t))))

(defun muse-journal-split-by-month (file)
  "Split a muse journal file into months.

This function makes the assumption that the entries are sorted. If
it isn't then it some of the entries will appear not to be published."
  (muse-with-temp-buffer
    (muse-insert-file-contents file)
    (let* ((split-alist)
           (root-name (file-name-sans-extension file))
           (split-regexp (concat "^\\* \\([0-9]\\{4\\}\\)\\([0-9]\\{2\\}\\)"
                                 "\\([0-9]\\{2\\}\\)"))
           (current-position
            (if (re-search-forward split-regexp nil t)
                (- (match-beginning 0) 1)))
           (entry-name (muse-journal-split-by-month-name))
           (entry-location (match-beginning 0)))

      ;; for a new entry, if the name has changed
      (while (and (re-search-forward split-regexp nil t)
                  (not (equal entry-name
                              (muse-journal-split-by-month-name))))
        (setq entry-location (match-beginning 0))
        (add-to-list 'split-alist
                     `(,(concat root-name "-" entry-name)
                       ,current-position
                       ,(- entry-location 1)))

        (setq current-position entry-location
              entry-name (muse-journal-split-by-month-name)))

      ;; add last entry
      (add-to-list 'split-alist
                   `(,(concat root-name "-" entry-name)
                     ,current-position
                     ,(point-max)))

      ;; add some duplicate entries in. Add these last, so that
      ;; anchors go to one of the others.
      ;;

      ;; duplicate last entry as current
      (add-to-list 'split-alist
                   `(,root-name
                     ,(cadr (car (last split-alist)))
                     ,(caddr (car (last split-alist))))
                   t)

      ;; add all entry
      (add-to-list 'split-alist
                   `(,(concat root-name "-all")
                     1 ,(point-max))
                   t))))

(defun muse-journal-split-by-month-name()
  (concat (match-string 1)
          (match-string 2)))


(defun test2()
  (interactive)
  (message "%s" (muse-journal-split-by-entry "journal.muse")))


(provide 'muse-split)
;; muse-split.el ends here
