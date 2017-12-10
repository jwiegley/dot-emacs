;;; bm-sync.el --- Synchronize bm.el bookmarks with standard Emacs bookmarks

;; Copyright (C) 2016  Jo Odland

;; Author: Jo Odland <jo.odland(at)gmail.com>
;; Keywords: bookmark
;; URL: https://github.com/joodland/bm


;; This file is *NOT* part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING. If not, write to the
;; Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


;;; Description:
;;
;; Create/remove a standard Emacs bookmark everytime you toggle a
;; bm.el bookmark. This code is experimental.
;;
;; This code is related to a GitHub issue,
;; https://github.com/joodland/bm/issues/18

;;; Installation:
;;
;;   To use bm-sync.el, put it in your load-path and add the following
;;   to your .emacs. It also requires bm.el to be present.
;;
;;   (require 'bm-sync)
;;


;;; Code:
;;
(require 'bm)


(defun bm-bookmark-add--sync (&optional annotation time temporary-bookmark)
  "Add a standard Emacs bookmarks when setting a bm-bookmark."
  ;; create a unique name for the bookmark
  (let ((name (concat (buffer-name)     
                      " l:" (int-to-string
                             (count-lines (point-min) (point))))))
    ;; store the bookmark name as an annotation
    (bm-bookmark-annotate (bm-bookmark-at (point)) name)
    (bookmark-set name)))

(advice-add 'bm-bookmark-add :after #'bm-bookmark-add--sync)


(defun bm-bookmark-remove--sync (&optional bookmark)
  "Remove a standard Emacs bookmarks when setting a bm-bookmark."
  (if (null bookmark)
      (setq bookmark (bm-bookmark-at (point))))

  (if (bm-bookmarkp bookmark)
      ;; delete bookmark by name (from annotation)
      (bookmark-delete (overlay-get bookmark 'annotation))))

(advice-add 'bm-bookmark-remove :before #'bm-bookmark-remove--sync)


(provide 'bm-sync)
;;; bm-sync.el ends here
