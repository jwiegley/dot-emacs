;;; muse-protocol-iw.el --- implement an interwiki protocol handler

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

;; This defines a new url type, which is like the interwiki support of
;; muse-wiki. You can also publish to a different directory structure
;; from the file space (which I do for historical reasons). So a link
;; like

;; [[iw:home\emacs][hello]] will work from any of the individual muse
;; projects that I have.

(require 'muse-protocols)

(add-to-list 'muse-url-protocols
             '("iw:" muse-browse-url-iw muse-resolve-url-iw))

(defvar muse-interwiki-protocol-alist
      '(("home" "/" "~/src/ht/home_website")
        ("silly" "/silly/" "~/src/ht/home_website/silly")
        ("energy" "/energy/" "~/src/ht/home_website/energy")
        ("journal" "/journal/" "~/src/ht/home_website/journal")))

(defun muse-resolve-url-iw (url)
  (when (string-match "\\`iw:\\([a-zA-Z]*\\)\\\\\\(.+\\)" url)
    (let* ((wiki-resolve
            (assoc (match-string 1 url)
                   muse-interwiki-protocol-alist))
           (publish-resolve
            (nth 1 wiki-resolve)))
      (concat publish-resolve (match-string 2 url)))))

;; this doesn't handle anchors properly yet.
(defun muse-browse-url-iw (url)
  (when (string-match "\\`iw:\\([a-zA-Z]*\\)\\\\\\(.+\\)#?\\(.*\\)" url)
    (let* ((wiki-resolve
            (assoc (match-string 1 url)
                   muse-interwiki-protocol-alist))
           (browse-resolve
            (or (nth 2 wiki-resolve)
                (nth 1 wiki-resolve))))
      (find-file
       (concat browse-resolve "/"
               (match-string 2 url)
               ".muse")))))


(provide 'muse-protocol-iw)
;; muse-protocol-iw.el ends here
