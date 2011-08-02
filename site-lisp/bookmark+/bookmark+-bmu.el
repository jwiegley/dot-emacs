;;; bookmark+-bmu.el --- Bookmark+ code for the `*Bookmark List*' (bmenu).
;; 
;; Filename: bookmark+-bmu.el
;; Description: Bookmark+ code for the `*Bookmark List*' (bmenu).
;; Author: Drew Adams, Thierry Volpiatto
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2011, Drew Adams, all rights reserved.
;; Copyright (C) 2009, Thierry Volpiatto, all rights reserved.
;; Created: Mon Jul 12 09:05:21 2010 (-0700)
;; Last-Updated: Fri Jul  1 14:51:29 2011 (-0700)
;;           By: dradams
;;     Update #: 771
;; URL: http://www.emacswiki.org/cgi-bin/wiki/bookmark+-bmu.el
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search, info, url, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   `bookmark', `bookmark+-mac', `pp'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary: 
;;
;;    This library contains code for buffer `*Bookmark List*' (mode
;;    `bookmark-bmenu-mode').
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (this file)
;;    `bookmark+-1.el'   - other required code (non-bmenu) 
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc.el' - documentation (comment-only file)
;;    `bookmark+-chg.el' - change log (comment-only file)
;;
;;    The documentation (in `bookmark+-doc.el') includes how to
;;    byte-compile and install Bookmark+.  The documentation is also
;;    available in these ways:
;;
;;    1. From the bookmark list (`C-x r l'):
;;       Use `?' to show the current bookmark-list status and general
;;       help, then click link `Doc in Commentary' or link `Doc on the
;;       Web'.
;;
;;    2. From the Emacs-Wiki Web site:
;;       http://www.emacswiki.org/cgi-bin/wiki/BookmarkPlus.
;;    
;;    3. From the Bookmark+ group customization buffer:
;;       `M-x customize-group bookmark-plus', then click link
;;       `Commentary'.
;;
;;    (The commentary links in #1 and #3 work only if you have library
;;    `bookmark+-doc.el' in your `load-path'.)
 
;;(@> "Index")
;;
;;  Index
;;  -----
;;
;;  If you have library `linkd.el' and Emacs 22 or later, load
;;  `linkd.el' and turn on `linkd-mode' now.  It lets you easily
;;  navigate around the sections of this doc.  Linkd mode will
;;  highlight this Index, as well as the cross-references and section
;;  headings throughout this file.  You can get `linkd.el' here:
;;  http://dto.freeshell.org/notebook/Linkd.html.
;;
;;  (@> "Things Defined Here")
;;  (@> "Faces (Customizable)")
;;  (@> "User Options (Customizable)")
;;  (@> "Internal Variables")
;;  (@> "Compatibility Code for Older Emacs Versions")
;;  (@> "Menu List Replacements (`bookmark-bmenu-*')")
;;  (@> "Bookmark+ Functions (`bmkp-*')")
;;    (@> "Menu-List (`*-bmenu-*') Filter Commands")
;;    (@> "Menu-List (`*-bmenu-*') Commands Involving Marks")
;;    (@> "Omitted Bookmarks")
;;    (@> "Search-and-Replace Locations of Marked Bookmarks")
;;    (@> "Tags")
;;    (@> "General Menu-List (`-*bmenu-*') Commands and Functions")
;;    (@> "Sorting - Commands")
;;    (@> "Other Bookmark+ Functions (`bmkp-*')")
;;  (@> "Keymaps")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Commands defined here:
;;
;;    `bmkp-bmenu-add-tags', `bmkp-bmenu-add-tags-to-marked',
;;    `bmkp-bmenu-change-sort-order',
;;    `bmkp-bmenu-change-sort-order-repeat', `bmkp-bmenu-copy-tags',
;;    `bmkp-bmenu-define-command',
;;    `bmkp-bmenu-define-full-snapshot-command',
;;    `bmkp-bmenu-define-jump-marked-command',
;;    `bmkp-bmenu-delete-marked', `bmkp-bmenu-describe-marked',
;;    `bmkp-bmenu-describe-this+move-down',
;;    `bmkp-bmenu-describe-this+move-up',
;;    `bmkp-bmenu-describe-this-bookmark',`bmkp-bmenu-dired-marked',
;;    `bmkp-bmenu-edit-bookmark', `bmkp-edit-tags-send',
;;    `bmkp-bmenu-filter-annotation-incrementally',
;;    `bmkp-bmenu-filter-bookmark-name-incrementally',
;;    `bmkp-bmenu-filter-file-name-incrementally',
;;    `bmkp-bmenu-filter-tags-incrementally',
;;    `bmkp-bmenu-isearch-marked-bookmarks' (Emacs 23+),
;;    `bmkp-bmenu-isearch-marked-bookmarks-regexp' (Emacs 23+),
;;    `bmkp-bmenu-make-sequence-from-marked', `bmkp-bmenu-mark-all',
;;    `bmkp-bmenu-mark-autofile-bookmarks',
;;    `bmkp-bmenu-mark-bookmark-file-bookmarks',
;;    `bmkp-bmenu-mark-bookmarks-satisfying',
;;    `bmkp-bmenu-mark-bookmarks-tagged-all',
;;    `bmkp-bmenu-mark-bookmarks-tagged-none',
;;    `bmkp-bmenu-mark-bookmarks-tagged-not-all',
;;    `bmkp-bmenu-mark-bookmarks-tagged-regexp',
;;    `bmkp-bmenu-mark-bookmarks-tagged-some',
;;    `bmkp-bmenu-mark-desktop-bookmarks',
;;    `bmkp-bmenu-mark-dired-bookmarks',
;;    `bmkp-bmenu-mark-file-bookmarks',
;;    `bmkp-bmenu-mark-gnus-bookmarks',
;;    `bmkp-bmenu-mark-info-bookmarks',
;;    `bmkp-bmenu-mark-lighted-bookmarks',
;;    `bmkp-bmenu-mark-man-bookmarks',
;;    `bmkp-bmenu-mark-non-file-bookmarks',
;;    `bmkp-bmenu-mark-region-bookmarks',
;;    `bmkp-bmenu-mark-specific-buffer-bookmarks',
;;    `bmkp-bmenu-mark-specific-file-bookmarks',
;;    `bmkp-bmenu-mark-url-bookmarks',
;;    `bmkp-bmenu-mark-w3m-bookmarks', `bmkp-bmenu-mouse-3-menu',
;;    `bmkp-bmenu-mode-status-help', `bmkp-bmenu-omit',
;;    `bmkp-bmenu-omit-marked', `bmkp-bmenu-omit/unomit-marked',
;;    `bmkp-bmenu-paste-add-tags',
;;    `bmkp-bmenu-paste-add-tags-to-marked',
;;    `bmkp-bmenu-paste-replace-tags',
;;    `bmkp-bmenu-paste-replace-tags-for-marked',
;;    `bmkp-bmenu-query-replace-marked-bookmarks-regexp',
;;    `bmkp-bmenu-quit', `bmkp-bmenu-refresh-menu-list',
;;    `bmkp-bmenu-regexp-mark', `bookmark-bmenu-relocate' (Emacs 20,
;;    21), `bmkp-bmenu-remove-all-tags', `bmkp-bmenu-remove-tags',
;;    `bmkp-bmenu-remove-tags-from-marked',
;;    `bmkp-bmenu-search-marked-bookmarks-regexp',
;;    `bmkp-bmenu-set-tag-value',
;;    `bmkp-bmenu-set-tag-value-for-marked', `bmkp-bmenu-show-all',
;;    `bmkp-bmenu-show-only-autofiles',
;;    `bmkp-bmenu-show-only-autonamed.',
;;    `bmkp-bmenu-show-only-bookmark-files',
;;    `bmkp-bmenu-show-only-desktops', `bmkp-bmenu-show-only-dired',
;;    `bmkp-bmenu-show-only-files', `bmkp-bmenu-show-only-gnus',
;;    `bmkp-bmenu-show-only-info-nodes',
;;    `bmkp-bmenu-show-only-man-pages',
;;    `bmkp-bmenu-show-only-non-files',
;;    `bmkp-bmenu-show-only-omitted', `bmkp-bmenu-show-only-regions',
;;    `bmkp-bmenu-show-only-specific-buffer',
;;    `bmkp-bmenu-show-only-specific-file',
;;    `bmkp-bmenu-show-only-tagged', `bmkp-bmenu-show-only-urls',
;;    `bmkp-bmenu-show-only-variable-lists',
;;    `bmkp-bmenu-show-only-w3m-urls',
;;    `bmkp-bmenu-sort-by-bookmark-name',
;;    `bmkp-bmenu-sort-by-bookmark-visit-frequency',
;;    `bmkp-bmenu-sort-by-creation-time',
;;    `bmkp-bmenu-sort-by-file-name',
;;    `bmkp-bmenu-sort-by-Gnus-thread',
;;    `bmkp-bmenu-sort-by-Info-location',
;;    `bmkp-bmenu-sort-by-last-bookmark-access',
;;    `bmkp-bmenu-sort-by-last-buffer-or-file-access',
;;    `bmkp-bmenu-sort-by-last-local-file-access',
;;    `bmkp-bmenu-sort-by-last-local-file-update',
;;    `bmkp-bmenu-sort-by-local-file-size',
;;    `bmkp-bmenu-sort-by-local-file-type', `bmkp-bmenu-sort-by-url',
;;    `bmkp-bmenu-sort-marked-before-unmarked',
;;    `bmkp-bmenu-toggle-marks', `bmkp-bmenu-toggle-show-only-marked',
;;    `bmkp-bmenu-toggle-show-only-unmarked', `bmkp-bmenu-unmark-all',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-all',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-none',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-not-all',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-regexp',
;;    `bmkp-bmenu-unmark-bookmarks-tagged-some',
;;    `bmkp-bmenu-unomit-marked', `bmkp-bmenu-w32-open',
;;    `bmkp-bmenu-w32-open-select', `bmkp-bmenu-w32-open-with-mouse',
;;    `bmkp-define-tags-sort-command'.
;;
;;  Faces defined here:
;;
;;    `bmkp->-mark', `bmkp-a-mark', `bmkp-bad-bookmark',
;;    `bmkp-bookmark-file', `bmkp-bookmark-list', `bmkp-buffer',
;;    `bmkp-D-mark', `bmkp-desktop', `bmkp-function', `bmkp-gnus',
;;    `bmkp-heading', `bmkp-info', `bmkp-local-directory',
;;    `bmkp-local-file-with-region', `bmkp-local-file-without-region',
;;    `bmkp-man', `bmkp-non-file', `bmkp-remote-file',
;;    `bmkp-sequence', `bmkp-su-or-sudo', `bmkp-t-mark', `bmkp-url',
;;    `bmkp-variable-list'.
;;
;;  User options defined here:
;;
;;    `bmkp-bmenu-commands-file', `bmkp-bmenu-omitted-bookmarks',
;;    `bmkp-bmenu-state-file', `bmkp-propertize-bookmark-names-flag',
;;    `bmkp-sort-orders-alist', `bmkp-sort-orders-for-cycling-alist'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkp-bmenu-barf-if-not-in-menu-list',
;;    `bmkp-bmenu-cancel-incremental-filtering',
;;    `bmkp-bmenu-filter-alist-by-annotation-regexp',
;;    `bmkp-bmenu-filter-alist-by-bookmark-name-regexp',
;;    `bmkp-bmenu-filter-alist-by-file-name-regexp',
;;    `bmkp-bmenu-filter-alist-by-tags-regexp',
;;    `bmkp-bmenu-get-marked-files', `bmkp-bmenu-goto-bookmark-named',
;;    `bmkp-bmenu-list-1',
;;    `bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none',
;;    `bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all',
;;    `bmkp-bmenu-propertize-item', `bmkp-bmenu-read-filter-input',
;;    `bmkp-maybe-unpropertize-bookmark-names',
;;    `bmkp-reverse-multi-sort-order', `bmkp-reverse-sort-order'.
;;
;;  Internal variables defined here:
;;
;;    `bmkp-bmenu-before-hide-marked-alist',
;;    `bmkp-bmenu-before-hide-unmarked-alist',
;;    `bmkp-bmenu-define-command-menu', `bmkp-bmenu-filter-function',
;;    `bmkp-bmenu-filter-pattern', `bmkp-bmenu-filter-prompt',
;;    `bmkp-bmenu-filter-timer', `bmkp-bmenu-first-time-p',
;;    `bmkp-bmenu-header-lines', `bmkp-bmenu-highlight-menu',
;;    `bmkp-bmenu-line-overlay', `bmkp-bmenu-mark-menu',
;;    `bmkp-bmenu-marked-bookmarks', `bmkp-bmenu-marks-width',
;;    `bmkp-bmenu-menubar-menu', `bmkp-bmenu-omit-menu',
;;    `bmkp-bmenu-show-menu', `bmkp-bmenu-sort-menu',
;;    `bmkp-bmenu-tags-menu', `bmkp-bmenu-title',
;;    `bmkp-bookmark-file-history', `bmkp-bookmark-list-history',
;;    `bmkp-current-bookmark-file', `bmkp-current-nav-bookmark',
;;    `bmkp-desktop-history', `bmkp-dired-history',
;;    `bmkp-file-history', `bmkp-gnus-history', `bmkp-highlight-menu',
;;    `bmkp-info-history', `bmkp-isearch-bookmarks' (Emacs 23+),
;;    `bmkp-jump-display-function', `bmkp-jump-map', `bmkp-jump-menu',
;;    `bmkp-jump-other-window-map', `bmkp-last-bmenu-bookmark'.
;;
;;
;;  ***** NOTE: The following commands defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-bmenu-execute-deletions', `bookmark-bmenu-list',
;;    `bookmark-bmenu-mark', `bookmark-bmenu-1-window',
;;    `bookmark-bmenu-2-window', `bookmark-bmenu-other-window',
;;    `bookmark-bmenu-other-window-with-mouse',
;;    `bookmark-bmenu-this-window', `bookmark-bmenu-rename',
;;    `bookmark-bmenu-show-annotation',
;;    `bookmark-bmenu-switch-other-window', `bookmark-bmenu-unmark'.
;;
;;
;;  ***** NOTE: The following non-interactive functions defined in
;;              `bookmark.el' have been REDEFINED HERE:
;;
;;    `bookmark-bmenu-bookmark', `bookmark-bmenu-check-position',
;;    `bookmark-bmenu-delete', `bookmark-bmenu-ensure-position' (Emacs
;;    23.2+), `bookmark-bmenu-hide-filenames', `bookmark-bmenu-mode',
;;    `bookmark-bmenu-show-filenames',
;;    `bookmark-bmenu-surreptitiously-rebuild-list',
;;    `bookmark-bmenu-switch-other-window' (Emacs 20-22).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;

(eval-when-compile (require 'cl)) ;; case

(require 'bookmark)
;; bookmark-alist, bookmark-bmenu-file-column,
;; bookmark-bmenu-hidden-bookmarks, bookmark-bmenu-mode-map,
;; bookmark-bmenu-select, bookmark-bmenu-toggle-filenames,
;; bookmark-get-annotation, bookmark-get-bookmark,
;; bookmark-get-filename, bookmark-get-handler, bookmark-kill-line,
;; bookmark-maybe-load-default-file, bookmark-name-from-full-record,
;; bookmark-name-from-record, bookmark-prop-get,
;; bookmark-show-annotation, bookmark-store

;;; Fix incompatibility introduced by gratuitous Emacs name change.
(cond ((and (fboundp 'bookmark-name-from-record) (not (fboundp 'bookmark-name-from-full-record)))
       (defalias 'bookmark-name-from-full-record 'bookmark-name-from-record))
      ((and (fboundp 'bookmark-name-from-full-record) (not (fboundp 'bookmark-name-from-record)))
       (defalias 'bookmark-name-from-record 'bookmark-name-from-full-record)))

(require 'bookmark+-mac) ;; bmkp-define-sort-command

;; (eval-when-compile (require 'bookmark+-1))
;; bmkp-add-tags, bmkp-alpha-p, bmkp-bookmark-creation-cp,
;; bmkp-bookmark-description, bmkp-bookmark-file-bookmark-p,
;; bmkp-bookmark-last-access-cp, bmkp-bookmark-list-bookmark-p,
;; bmkp-buffer-last-access-cp, bmkp-completing-read-buffer-name,
;; bmkp-completing-read-file-name, bmkp-current-bookmark-file,
;; bmkp-current-sort-order, bmkp-describe-bookmark,
;; bmkp-describe-bookmark-internals, bmkp-desktop-bookmark-p,
;; bmkp-edit-bookmark, bmkp-face-prop, bmkp-file-alpha-cp,
;; bmkp-file-remote-p, bmkp-function-bookmark-p, bmkp-get-buffer-name,
;; bmkp-get-tags, bmkp-gnus-bookmark-p, bmkp-gnus-cp, bmkp-handler-cp,
;; bmkp-incremental-filter-delay, bmkp-info-bookmark-p, bmkp-info-cp,
;; bmkp-isearch-bookmarks, bmkp-isearch-bookmarks-regexp, bmkp-jump-1,
;; bmkp-last-bookmark-file, bmkp-last-specific-buffer,
;; bmkp-last-specific-file, bmkp-latest-bookmark-alist,
;; bmkp-local-file-bookmark-p, bmkp-local-file-type-cp,
;; bmkp-local-file-accessed-more-recently-cp,
;; bmkp-local-file-updated-more-recently-cp, bmkp-man-bookmark-p,
;; bmkp-marked-bookmark-p, bmkp-marked-bookmarks-only, bmkp-marked-cp,
;; bmkp-msg-about-sort-order, bmkp-non-file-filename,
;; bmkp-read-tag-completing, bmkp-read-tags-completing,
;; bmkp-refresh-menu-list, bmkp-region-bookmark-p,
;; bmkp-remove-all-tags, bmkp-remove-if, bmkp-remove-tags,
;; bmkp-repeat-command, bmkp-reverse-multi-sort-p,
;; bmkp-reverse-sort-p, bmkp-root-or-sudo-logged-p, bmkp-same-file-p,
;; bmkp-save-menu-list-state, bmkp-sequence-bookmark-p,
;; bmkp-set-tag-value, bmkp-set-tag-value-for-bookmarks,
;; bmkp-set-union, bmkp-some, bmkp-some-marked-p,
;; bmkp-some-unmarked-p, bmkp-sort-omit, bmkp-sort-comparer, bmkp-sorted-alist,
;; bmkp-sort-orders-for-cycling-alist, bmkp-su-or-sudo-regexp,
;; bmkp-tag-name, bmkp-tags-list, bmkp-url-bookmark-p, bmkp-url-cp,
;; bmkp-unmarked-bookmarks-only, bmkp-variable-list-bookmark-p,
;; bmkp-visited-more-cp

;; (eval-when-compile (require 'bookmark+-lit nil t))
;; bmkp-get-lighting

;;;;;;;;;;;;;;;;;;;;;;;

;; Quiet the byte-compiler
(defvar dired-re-mark)                      ; Defined in `dired.el'.
(defvar tramp-file-name-regexp)             ; Defined in `tramp.el'.

(defvar bmkp-sort-orders-alist)             ; Defined in `bookmark+-1.el'.
(defvar bmkp-sort-orders-for-cycling-alist) ; Defined in `bookmark+-1.el'.
 
;;(@* "Faces (Customizable)")
;;; Faces (Customizable) ---------------------------------------------

(defgroup bookmark-plus nil
  "Bookmark enhancements."
  :prefix "bmkp-" :group 'bookmark
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark+ bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
  :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
  :link '(emacs-commentary-link :tag "Commentary" "bookmark+"))

(defface bmkp->-mark '((((background dark)) (:foreground "Yellow"))
                       (t (:foreground "Blue")))
  ;; (:foreground "Magenta2" :box (:line-width 1 :style pressed-button))))
  "*Face used for a `>' mark in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-a-mark '((((background dark)) (:background "SaddleBrown"))
                       (t (:background "SkyBlue")))
  "*Face used for an annotation mark (`a') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-bad-bookmark '((t (:foreground "Red" :background "Chartreuse1")))
  "*Face used for a bookmark that seems to be bad: e.g., nonexistent file."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-bookmark-file
    '((((background dark))
       (:foreground "#00005A5AFFFF" :background "#FFFF9B9BFFFF")) ; ~ blue, ~ pink
      (t (:foreground "Orange" :background "DarkGreen")))
  "*Face used for a bookmark-file bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-bookmark-list
    '((((background dark)) (:foreground "#7474FFFFFFFF" :background "DimGray")) ; ~ cyan
      (t (:foreground "DarkRed" :background "LightGray")))
  "*Face used for a bookmark-list bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-buffer
    '((((background dark)) (:foreground "#FFFF9B9BFFFF")) ; ~ pink
      (t (:foreground "DarkGreen")))
  "*Face used for a bookmarked existing buffer not associated with a file."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-D-mark '((t (:foreground "Yellow" :background "Red")))
  "*Face used for a deletion mark (`D') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-desktop
    '((((background dark)) (:foreground "Orange" :background "DarkSlateBlue"))
      (t (:foreground "DarkBlue" :background "PaleGoldenrod")))
  "*Face used for a bookmarked desktop."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-function
    '((((background dark)) (:foreground "#0000EBEB6C6C")) ; ~ green
      (t (:foreground "DeepPink1")))
  "*Face used for a function bookmark: a bookmark that invokes a function."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-gnus
    '((((background dark)) (:foreground "Gold"))
      (t (:foreground "DarkBlue")))
  "*Face used for a gnus bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-info
    '((((background dark)) (:foreground "#7474FFFFFFFF")) ; ~ light cyan
      (t (:foreground "DarkRed")))
  "*Face used for a bookmarked Info node."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-local-directory
    '((((background dark))
       (:foreground "Pink" :background "DarkBlue"))
      (t (:foreground "DarkBlue" :background "HoneyDew2")))
  "*Face used for a bookmarked local directory."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-local-file-without-region
    '((((background dark)) (:foreground "White"))
      (t (:foreground "Black")))
  "*Face used for a bookmarked local file (without a region)."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-local-file-with-region
    '((((background dark)) (:foreground "Yellow"))
      (t (:foreground "Blue")))
  "*Face used for a region bookmark in a local file."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-man
    '((((background dark)) (:foreground "Orchid"))
      (t (:foreground "Orange4")))
  "*Face used for a `man' page bookmark."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-non-file
    '((t (:foreground "gray60")))
  "*Face used for a bookmark not associated with an existing file or buffer."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-remote-file
    '((((background dark)) (:foreground "#6B6BFFFF2C2C")) ; ~ green
      (t (:foreground "DarkViolet")))
  "*Face used for a bookmarked tramp remote file (/ssh:)."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-sequence
    '((((background dark)) (:foreground "DeepSkyBlue"))
      (t (:foreground "DarkOrange2")))
  "*Face used for a sequence bookmark: one composed of other bookmarks."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-su-or-sudo '((t (:foreground "Red")))
  "*Face used for a bookmarked tramp file (/su: or /sudo:)."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-t-mark '((t (:foreground "Red")))
  "*Face used for a tags mark (`t') in the bookmark list."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-url
    '((((background dark)) (:foreground "#7474FFFF7474")) ; ~ green
      (t (:foreground "DarkMagenta")))
  "*Face used for a bookmarked URL."
  :group 'bookmark-plus :group 'faces)

(defface bmkp-variable-list
    '((((background dark)) (:foreground "#FFFF74747474")) ; ~ salmon
      (t (:foreground "DarkCyan")))
  "*Face used for a bookmarked list of variables."
  :group 'bookmark-plus :group 'faces)

;; $$$$$$ Not used now - using `bmkp-url' instead.
;; (defface bmkp-w3m
;;     '((((background dark)) (:foreground "yellow"))
;;       (t (:foreground "DarkMagenta")))
;;   "*Face used for a bookmarked w3m url."
;;   :group 'bookmark-plus :group 'faces)

;; Instead of vanilla `bookmark-menu-heading' (defined in Emacs 22+), to use a better default.
(defface bmkp-heading '((((background dark)) (:foreground "Yellow"))
                        (t (:foreground "Blue")))
  "*Face used to highlight the headings in various Bookmark+ buffers."
  :group 'bookmark-plus :version "22.1" :group 'faces)
 
;;(@* "User Options (Customizable)")
;;; User Options (Customizable) --------------------------------------

;;;###autoload
(defcustom bmkp-bmenu-omitted-bookmarks ()
  "*List of names of omitted bookmarks.
They are generally not available for display in the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-show-only-omitted]' to see them.
You can then mark some of them and use `\\[bmkp-bmenu-omit/unomit-marked]'
 to make those that are marked available again for the bookmark list."
  :type '(repeat (string :tag "Bookmark name")) :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-bmenu-commands-file (convert-standard-filename "~/.emacs-bmk-bmenu-commands.el")
  "*File for saving user-defined bookmark-list commands.
This must be an absolute file name (possibly containing `~') or nil
\(it is not expanded).

You can use `\\[bmkp-list-defuns-in-commands-file]' to list the
commands defined in the file and how many times each is defined.

NOTE: Each time you define a command using \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-define-command]', `\\[bmkp-bmenu-define-full-snapshot-command]', \
`\\[bmkp-bmenu-define-jump-marked-command], or `\\[bmkp-define-tags-sort-command]',
it is saved in the file.  The new definition is simply appended to the
file - old definitions of the same command are not overwritten.  So
you might want to clean up the file occasionally, to remove any old,
unused definitions.  This is especially advisable if you used \
`\\[bmkp-bmenu-define-full-snapshot-command]',
because such command definitions can be very large."
  :type '(file  :tag "File for saving menu-list state") :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-bmenu-state-file (convert-standard-filename "~/.emacs-bmk-bmenu-state.el")
  "*File for saving `*Bookmark List*' state when you quit bookmark list.
This must be an absolute file name (possibly containing `~') or nil
\(it is not expanded).

The state is also saved when you quit Emacs, even if you don't quit
the bookmark list first (using \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-quit]').

Set this to nil if you do not want to restore the bookmark list as it
was the last time you used it."
  :type '(choice
          (const :tag "Do not save and restore menu-list state" nil)
          (file  :tag "File for saving menu-list state"))
  :group 'bookmark-plus)

;; This is a general option.  It is in this file because it is used mainly by the bmenu code.
(when (> emacs-major-version 20)
  (defcustom bmkp-sort-orders-alist ()
    "*Alist of all available sort functions.
This is a pseudo option - you probably do NOT want to customize this.
Instead:

 * To add a new sort function to this list, use macro
   `bmkp-define-sort-command'.  It defines a new sort function
   and automatically adds it to this list.

 * To have fewer sort orders available for cycling by \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-change-sort-order-repeat]'...,
   customize option `bmkp-sort-orders-for-cycling-alist'.

Each alist element has the form (SORT-ORDER . COMPARER):

 SORT-ORDER is a short string or symbol describing the sort order.
 Examples: \"by last access time\", \"by bookmark name\".

 COMPARER compares two bookmarks.  It must be acceptable as a value of
 `bmkp-sort-comparer'."
    :type '(alist
            :key-type (choice :tag "Sort order" string symbol)
            :value-type (choice
                         (const    :tag "None (do not sort)" nil)
                         (function :tag "Sorting Predicate")
                         (list     :tag "Sorting Multi-Predicate"
                          (repeat (function :tag "Component Predicate"))
                          (choice
                           (const    :tag "None" nil)
                           (function :tag "Final Predicate")))))
    :group 'bookmark-plus))

(unless (> emacs-major-version 20)      ; Emacs 20: custom type `alist' doesn't exist.
  (defcustom bmkp-sort-orders-alist ()
    "*Alist of all available sort functions.
This is a pseudo option - you probably do NOT want to customize this.
Instead:

 * To add a new sort function to this list, use macro
   `bmkp-define-sort-command'.  It defines a new sort function
   and automatically adds it to this list.

 * To have fewer sort orders available for cycling by \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-change-sort-order-repeat]'...,
   customize option `bmkp-sort-orders-for-cycling-alist'.

Each alist element has the form (SORT-ORDER . COMPARER):

 SORT-ORDER is a short string or symbol describing the sort order.
 Examples: \"by last access time\", \"by bookmark name\".

 COMPARER compares two bookmarks.  It must be acceptable as a value of
 `bmkp-sort-comparer'."
    :type '(repeat
            (cons
             (choice :tag "Sort order" string symbol)
             (choice
              (const    :tag "None (do not sort)" nil)
              (function :tag "Sorting Predicate")
              (list     :tag "Sorting Multi-Predicate"
               (repeat (function :tag "Component Predicate"))
               (choice
                (const    :tag "None" nil)
                (function :tag "Final Predicate"))))))
    :group 'bookmark-plus))

(defcustom bmkp-propertize-bookmark-names-flag (> emacs-major-version 20)
  "*Non-nil means to propertize bookmark names to hold full bookmark data.
This means that you can effectively have more than one bookmark with
the same name.

Emacs 20 users: If you need to use your bookmarks with Emacs 20 then
set this to nil.  In particular, if your bookmark file was written
with this as non-nil, then it contains propertized strings which are
unreadable by Emacs 20.  To convert the file to be usable with Emacs
20 you must, in Emacs 21 or later, set this to nil and then do `M-x
bookmark-save'."
  :type 'boolean :group 'bookmark-plus)
 
;;(@* "Internal Variables")
;;; Internal Variables -----------------------------------------------

(defconst bmkp-bmenu-header-lines 2
  "Number of lines used for the `*Bookmark List*' header.")

(defconst bmkp-bmenu-marks-width 4
  "Number of columns (chars) used for the `*Bookmark List*' marks columns.")

(defvar bmkp-bmenu-marked-bookmarks ()
  "Names of the marked bookmarks.
This includes possibly omitted bookmarks, that is, bookmarks listed in
`bmkp-bmenu-omitted-bookmarks'.")

(defvar bmkp-bmenu-before-hide-unmarked-alist ()
  "Copy of `bookmark-alist' made before hiding unmarked bookmarks.")

(defvar bmkp-bmenu-before-hide-marked-alist ()
  "Copy of `bookmark-alist' made before hiding marked bookmarks.")

(defvar bmkp-bmenu-filter-function  nil "Latest filtering function for `*Bookmark List*' display.")

(defvar bmkp-bmenu-title "" "Latest title for `*Bookmark List*' display.")

(defvar bmkp-bmenu-filter-pattern "" "Regexp for incremental filtering.")

(defvar bmkp-bmenu-filter-prompt "Pattern: " "Prompt for `bmkp-bmenu-filter-incrementally'.")

(defvar bmkp-bmenu-filter-timer nil "Timer used for incremental filtering.")

(defvar bmkp-bmenu-first-time-p t
  "Non-nil means bookmark list has not yet been shown after quitting it.
Quitting the list or the Emacs session resets this to t.
The first time the list is displayed, it is set to nil.")

;; This is a general variable.  It is in this file because it is used only in the bmenu code.
(defvar bmkp-last-bmenu-bookmark nil "The name of the last bookmark current in the bookmark list.")
 
;;(@* "Compatibility Code for Older Emacs Versions")
;;; Compatibility Code for Older Emacs Versions ----------------------

(when (< emacs-major-version 22)
  (defun bookmark-bmenu-relocate ()
    "Change the file path of the bookmark on the current line,
  prompting with completion for the new path."
    (interactive)
    (let ((bmk        (bookmark-bmenu-bookmark))
          (thispoint  (point)))
      (bookmark-relocate bmk)
      (goto-char thispoint))))
 
;;(@* "Menu List Replacements (`bookmark-bmenu-*')")
;;; Menu List Replacements (`bookmark-bmenu-*') ----------------------



;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Return t.  Value doesn't mean anything (didn't anyway), but must be non-nil for vanilla Emacs.
;; 2. Do not count lines.  Just make sure we're on a bookmark line.
;;
(defalias 'bookmark-bmenu-check-position 'bookmark-bmenu-ensure-position)
(defun bookmark-bmenu-ensure-position ()
  "Move to the beginning of the nearest bookmark line."
  (beginning-of-line)
  (unless (bookmark-bmenu-bookmark)
    (if (and (bolp) (eobp))
        (beginning-of-line 0)
      (goto-char (point-min))
      (forward-line bmkp-bmenu-header-lines)))
  t)                                    ; Older vanilla bookmark code depends on non-nil value.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add bookmark to `bmkp-bmenu-marked-bookmarks'.
;; 2. Don't call `bookmark-bmenu-ensure-position' again at end.
;; 3. Raise error if not in `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-mark ()           ; Bound to `m' in bookmark list
  "Mark the bookmark on this line, using mark `>'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (beginning-of-line)
  (let ((inhibit-read-only  t))
    (push (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks)
    (delete-char 1) (insert ?>) (put-text-property (1- (point)) (point) 'face 'bmkp->-mark)
    (forward-line 1)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Remove bookmark from `bmkp-bmenu-marked-bookmarks'.
;; 2. Use `bmkp-delete-bookmark-name-from-list', not `delete'.
;; 3. Don't call `bookmark-bmenu-ensure-position' again at end.
;; 4. Raise error if not in `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-unmark (&optional backup) ; Bound to `u' in bookmark list
  "Unmark the bookmark on this line, then move down to the next.
Optional BACKUP means move up instead."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (beginning-of-line)
  (let ((inhibit-read-only  t))
    (delete-char 1) (insert " ")
    (setq bmkp-bmenu-marked-bookmarks  (bmkp-delete-bookmark-name-from-list
                                        (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks)))
  (forward-line (if backup -1 1)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Do not use `bookmark-bmenu-ensure-position' as a test - it always returns non-nil anyway.
;;    And don't call it at again the end.
;; 2. Use `bmkp-delete-bookmark-name-from-list', not `delete'.
;; 3. Use face `bmkp-bad-bookmark' on the `D' flag.
;; 4. Raise error if not in buffer `*Bookmark List*'.
;; 5. Remove bookmark from `bmkp-bmenu-marked-bookmarks'.
;;
;;;###autoload
(defun bookmark-bmenu-delete ()         ; Bound to `d', `k' in bookmark list
  "Flag this bookmark for deletion, using mark `D'.
Use `\\<bookmark-bmenu-mode-map>\\[bookmark-bmenu-execute-deletions]' to carry out \
the deletions."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (beginning-of-line)
  (bookmark-bmenu-ensure-position)
  (let ((inhibit-read-only  t))
    (delete-char 1) (insert ?D) (put-text-property (1- (point)) (point) 'face 'bmkp-D-mark))
  (setq bmkp-bmenu-marked-bookmarks  (bmkp-delete-bookmark-name-from-list
                                      (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks))
  (forward-line 1))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Rebuild the menu list using the last filtered alist in use, `bmkp-latest-bookmark-alist'.
;; 2. Update the menu-list title.
;;
(defun bookmark-bmenu-surreptitiously-rebuild-list ()
  "Rebuild the bookmark list, if it exists."
  (when (get-buffer "*Bookmark List*")
    (save-excursion (save-window-excursion (let ((bookmark-alist  bmkp-latest-bookmark-alist))
                                             (bookmark-bmenu-list 'filteredp))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added args TITLE, FILTEREDP, DONT-TOGGLE-FILENAMES-P.
;; 2. Handles also region bookmarks and buffer (non-file) bookmarks.
;; 3. Uses `pop-to-buffer', not `switch-to-buffer', so we respect `special-display-*'
;;    (but keep `one-window-p' if that's the case).
;; 4. If option `bmkp-bmenu-state-file' is non-nil, then the first time since the last quit
;;     (or the last Emacs session) restores the last menu-list state.
;; 5. If option `bmkp-bmenu-commands-file' is non-nil, then read that file, which contains
;;    user-defined `*Bookmark List*' commands.
;;
;;;###autoload
(defalias 'list-bookmarks 'bookmark-bmenu-list)
;;;###autoload
(defun bookmark-bmenu-list (&optional filteredp) ; Bound to `C-x r l'
  "Display a list of existing bookmarks, in buffer `*Bookmark List*'.
The leftmost column of a bookmark entry shows `D' if the bookmark is
 flagged for deletion, or `>' if it is marked normally.
The second column shows `t' if the bookmark has tags.
The third  column shows `a' if the bookmark has an annotation.

The following faces are used for the list entries.
Use `customize-face' if you want to change the appearance.

 `bmkp-bad-bookmark', `bmkp-bookmark-list', `bmkp-buffer',
 `bmkp-desktop', `bmkp-function', `bmkp-gnus', `bmkp-info',
 `bmkp-local-directory', `bmkp-local-file-without-region',
 `bmkp-local-file-with-region', `bmkp-man', `bmkp-non-file',
 `bmkp-remote-file', `bmkp-sequence', `bmkp-su-or-sudo', `bmkp-url',
 `bmkp-variable-list'.

If option `bmkp-bmenu-state-file' is non-nil then the state of the
displayed bookmark-list is saved when you quit it, and it is restored
when you next use this command.  That saved state is not restored,
however, if it represents a different file from the current bookmark
file.

If you call this interactively when buffer `*Bookmark List*' exists,
that buffer is refreshed to show all current bookmarks, and any
markings are removed.  If you instead want to show the buffer in its
latest state then just do that: use `C-x b' or similar.  If you want
to refresh the displayed buffer, to show the latest state, reflecting
any additions, deletions, renamings, and so on, use \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-refresh-menu-list]'.

In Lisp code, non-nil optional argument FILTEREDP means the bookmark
list has been filtered, which means:
 * Use `bmkp-bmenu-title' not the default menu-list title.
 * Do not reset `bmkp-latest-bookmark-alist' to `bookmark-alist'."
  (interactive)
  (bookmark-maybe-load-default-file)
  (when (and bmkp-bmenu-first-time-p bmkp-bmenu-commands-file
             (file-readable-p bmkp-bmenu-commands-file))
    (with-current-buffer (let ((enable-local-variables  ())
                               (emacs-lisp-mode-hook    nil))
                           (find-file-noselect bmkp-bmenu-commands-file))
      (goto-char (point-min))
      (while (not (eobp)) (condition-case nil (eval (read (current-buffer))) (error nil)))
      (kill-buffer (current-buffer))))
  (cond ((and bmkp-bmenu-first-time-p  bmkp-bmenu-state-file ; Restore from state file.
              (file-readable-p bmkp-bmenu-state-file))
         (let ((state  ()))
           (with-current-buffer (let ((enable-local-variables  nil)
                                      (emacs-lisp-mode-hook    nil))
                                  (find-file-noselect bmkp-bmenu-state-file))
             (goto-char (point-min))
             (setq state  (condition-case nil (read (current-buffer)) (error nil)))
             (kill-buffer (current-buffer)))
           (let ((last-bookmark-file-from-state  (cdr (assq 'last-bookmark-file state))))
             (when (and (consp state)
                        ;; If bookmark file has changed, then do not use state saved from other file.
                        (or (not last-bookmark-file-from-state)
                            (bmkp-same-file-p last-bookmark-file-from-state
                                              bmkp-current-bookmark-file)))
               (setq bmkp-sort-comparer                (cdr (assq 'last-sort-comparer           state))
                     bmkp-reverse-sort-p               (cdr (assq 'last-reverse-sort-p          state))
                     bmkp-reverse-multi-sort-p         (cdr (assq 'last-reverse-multi-sort-p    state))
                     bmkp-latest-bookmark-alist        (cdr (assq 'last-latest-bookmark-alist   state))
                     bmkp-bmenu-omitted-bookmarks      (cdr (assq 'last-bmenu-omitted-bookmarks state))
                     bmkp-bmenu-marked-bookmarks       (cdr (assq 'last-bmenu-marked-bookmarks  state))
                     bmkp-bmenu-filter-function        (cdr (assq 'last-bmenu-filter-function   state))
                     bmkp-bmenu-filter-pattern
                     (or (cdr (assq 'last-bmenu-filter-pattern   state)) "")
                     bmkp-bmenu-title                  (cdr (assq 'last-bmenu-title             state))
                     bmkp-last-bmenu-bookmark          (cdr (assq 'last-bmenu-bookmark          state))
                     bmkp-last-specific-buffer         (cdr (assq 'last-specific-buffer         state))
                     bmkp-last-specific-file           (cdr (assq 'last-specific-file           state))
                     bookmark-bmenu-toggle-filenames   (cdr (assq 'last-bmenu-toggle-filenames  state))
                     bmkp-last-bookmark-file           bmkp-current-bookmark-file
                     bmkp-current-bookmark-file        last-bookmark-file-from-state
                     bmkp-bmenu-before-hide-marked-alist
                     (cdr (assq 'last-bmenu-before-hide-marked-alist   state))
                     bmkp-bmenu-before-hide-unmarked-alist
                     (cdr (assq 'last-bmenu-before-hide-unmarked-alist state))))))
         (setq bmkp-bmenu-first-time-p  nil)
         (let ((bookmark-alist  (or bmkp-latest-bookmark-alist bookmark-alist)))
           (bmkp-bmenu-list-1 'filteredp nil (interactive-p)))
         (when bmkp-last-bmenu-bookmark
           (with-current-buffer (get-buffer "*Bookmark List*")
             (bmkp-bmenu-goto-bookmark-named bmkp-last-bmenu-bookmark))))
        (t
         (setq bmkp-bmenu-first-time-p  nil)
         (bmkp-bmenu-list-1 filteredp
                            (or (interactive-p) (not (get-buffer "*Bookmark List*")))
                            (interactive-p)))))

(defun bmkp-bmenu-list-1 (filteredp reset-marked-p interactivep)
  "Helper for `bookmark-bmenu-list'.
See `bookmark-bmenu-list' for the description of FILTEREDP.
Non-nil RESET-MARKED-P resets `bmkp-bmenu-marked-bookmarks'.
Non-nil INTERACTIVEP means `bookmark-bmenu-list' was called
 interactively, so pop to the bookmark list and communicate the sort
 order."
  (when reset-marked-p (setq bmkp-bmenu-marked-bookmarks  ()))
  (unless filteredp (setq bmkp-latest-bookmark-alist  bookmark-alist))
  (if interactivep
      (let ((one-win-p  (one-window-p)))
        (pop-to-buffer (get-buffer-create "*Bookmark List*"))
        (when one-win-p (delete-other-windows)))
    (set-buffer (get-buffer-create "*Bookmark List*")))
  (let* ((inhibit-read-only  t)
         (title              (if (and filteredp bmkp-bmenu-title (not (equal "" bmkp-bmenu-title)))
				 bmkp-bmenu-title
			       "All Bookmarks")))
    (erase-buffer)
    (insert (format "%s\n%s\n" title (make-string (length title) ?-)))
    (add-text-properties (point-min) (point) (bmkp-face-prop 'bmkp-heading))
    (let ((max-width  0)
          name markedp tags annotation start)
      (setq bmkp-sorted-alist  (bmkp-sort-omit bookmark-alist
                                               (and (not (eq bmkp-bmenu-filter-function
                                                             'bmkp-omitted-alist-only))
                                                    bmkp-bmenu-omitted-bookmarks)))
      (dolist (bmk  bmkp-sorted-alist)
        (setq max-width  (max max-width (length (bookmark-name-from-full-record bmk)))))
      (setq max-width  (+ max-width bmkp-bmenu-marks-width))
      (dolist (bmk  bmkp-sorted-alist)
        (setq name        (bookmark-name-from-full-record bmk)
              markedp     (bmkp-marked-bookmark-p bmk)
              tags        (bmkp-get-tags bmk)
              annotation  (bookmark-get-annotation bmk)
              start       (+ bmkp-bmenu-marks-width (point)))
        (if (not markedp)
            (insert " ")
          (insert ">") (put-text-property (1- (point)) (point) 'face 'bmkp->-mark))
        (if (null tags)
            (insert " ")
          (insert "t") (put-text-property (1- (point)) (point) 'face 'bmkp-t-mark))
        (if (not (and annotation (not (string-equal annotation ""))))
            (insert " ")
          (insert "a") (put-text-property (1- (point)) (point) 'face 'bmkp-a-mark))
        (insert " ")
        (when (and (featurep 'bookmark+-lit) (bmkp-get-lighting bmk)) ; Highlight highlight overrides.
          (put-text-property (1- (point)) (point) 'face 'bmkp-light-mark))
        (insert name)
        (move-to-column max-width t)
        (bmkp-bmenu-propertize-item bmk start (point))
        (insert "\n")))
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (bookmark-bmenu-mode)
    (when bookmark-bmenu-toggle-filenames (bookmark-bmenu-toggle-filenames t))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
      (fit-frame-if-one-window)))
  (when (and interactivep bmkp-sort-comparer)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Redefined.  
;; 1. Get name of the current bookmark from text property `bmkp-bookmark-name'.
;; 2. Added optional arg FULL, to return full bookmark record.
;; 3. Use `condition-case' in case we're at eob (so cannot advance).
;;
(defun bookmark-bmenu-bookmark (&optional full)
  "Return the name of the bookmark on this line.
Normally, the string returned is propertized with property
`bmkp-full-record', which records the full bookmark record.
Non-nil optional FULL means return the bookmark record, not the name."
  (condition-case nil
      (let ((name  (save-excursion (forward-line 0) (forward-char (1+ bmkp-bmenu-marks-width))
                                   (get-text-property (point) 'bmkp-bookmark-name))))
        (if full
            (get-text-property 0 'bmkp-full-record name)
          name))
    (error nil)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Only the doc string is different.
;;
(defun bookmark-bmenu-mode ()
  "Major mode for editing a list of bookmarks.
Each line represents an Emacs bookmark.\\<bookmark-bmenu-mode-map>

More bookmarking help below.  Keys without prefix `C-x' are available
only in buffer `*Bookmark List*'.  Others are available everywhere.


Help (Describe)
---------------

\\[bmkp-bmenu-describe-this-bookmark]\t- Show information about this bookmark (`C-u': \
internal form)
\\[bmkp-bmenu-describe-this+move-down]\t- Show the info, then move to next bookmark
\\[bmkp-bmenu-describe-this+move-up]\t- Show the info, then move to previous bookmark
\\[bmkp-bmenu-describe-marked]\t- Show info about the marked bookmarks (`C-u': internal form)
\\[bookmark-bmenu-locate]\t- Show the location of this bookmark in the minibuffer
\\[bookmark-bmenu-show-annotation]\t- Show this bookmark's annotation
\\[bookmark-bmenu-show-all-annotations]\t- Show the annotations of all annotated bookmarks
\\[bookmark-bmenu-toggle-filenames]\t- Toggle showing filenames next to bookmarks

\\[bmkp-list-defuns-in-commands-file]
\t- List the commands defined in `bmkp-bmenu-commands-file'


General
-------

\\[bmkp-bmenu-refresh-menu-list]\t- Refresh (revert) to up-to-date bookmark list
\\[bmkp-bmenu-quit]\t- Quit (`*Bookmark List*')
\\[bmkp-bmenu-dired-marked]\t- Open Dired for the marked files and directories

\\[bookmark-bmenu-load]\t- Add bookmarks from a different bookmark file (extra load)
\\[bmkp-switch-bookmark-file]\t- Switch to a different bookmark file      (overwrite load)
C-u \\[bmkp-switch-bookmark-file]\t- Switch back to the last bookmark file    (overwrite load)
\\[bmkp-set-bookmark-file-bookmark]\t- Create a bookmark to a bookmark file \
\(`\\[bmkp-bookmark-file-jump]' to load)

\\[bmkp-toggle-saving-bookmark-file]\t- Toggle autosaving the bookmark file
\\[bmkp-toggle-saving-menu-list-state]\t- Toggle autosaving bookmark-list display state (this list)
\\[bookmark-bmenu-save]\t- Save bookmarks (`C-u': prompt for the bookmark file to use)
\\[bmkp-save-menu-list-state]\t- Save bookmark-list display state

\\[bmkp-choose-navlist-of-type]\t- Set the navlist to the bookmarks of a type you choose
\\[bmkp-choose-navlist-from-bookmark-list]\t- Set the navlist to the bookmarks of a \
bookmark-list bookmark
\\[bmkp-navlist-bmenu-list]\t- Open `*Bookmark List*' for bookmarks in navlist
\\[bmkp-this-buffer-bmenu-list]\t- Open `*Bookmark List*' for bookmarks in current buffer
\\[bmkp-delete-bookmarks]\t- Delete some bookmarks at point or all in buffer

\\[bmkp-toggle-bookmark-set-refreshes]
\t- Toggle whether `bookmark-set' refreshes the bookmark list
\\[bmkp-make-function-bookmark]
\t- Create a function bookmark
\\[bmkp-bmenu-make-sequence-from-marked]
\t- Create a sequence bookmark from the marked bookmarks


Create/Set
----------

\\[bmkp-toggle-autonamed-bookmark-set/delete]\t- Set/delete an autonamed bookmark here
\\[bmkp-autofile-set]\t- Set and autoname a bookmark for a file
\\[bmkp-file-target-set]\t- Set a bookmark for a file
\\[bmkp-url-target-set]\t- Set a bookmark for a URL
\\[bookmark-set]\t- Set a bookmark here
\\[bmkp-set-desktop-bookmark]\t- Set a bookmark for the current desktop
\\[bmkp-set-bookmark-file-bookmark]\t- Set a bookmark for a bookmark file


Jump to (Visit)
---------------

\\[bookmark-bmenu-select]\t- This bookmark and also visit bookmarks marked `>'
\\[bookmark-bmenu-this-window]\t- This bookmark in the same window
\\[bookmark-bmenu-other-window]\t- This bookmark in another window
\\[bookmark-bmenu-switch-other-window]\t- This bookmark in other window, without selecting it
\\[bookmark-bmenu-1-window]\t- This bookmark in a full-frame window
\\[bookmark-bmenu-2-window]\t- This bookmark and last-visited bookmark

\\[bookmark-jump]\t- Bookmark by name
\\[bmkp-jump-to-type]\t- Bookmark by type
\\[bmkp-jump-in-navlist]\t- Bookmark in the navigation list
\\[bmkp-lighted-jump]\t- Highlighted bookmark
\\[bmkp-desktop-jump]\t- Desktop bookmark
\\[bmkp-bookmark-list-jump]\t- Bookmark-list bookmark
\\[bmkp-bookmark-file-jump]\t- Bookmark-file bookmark
\\[bmkp-dired-jump]\t- Dired bookmark
\\[bmkp-file-jump]\t- File or directory bookmark
\\[bmkp-dired-this-dir-jump]\t- Dired bookmark for this dir
\\[bmkp-file-this-dir-jump]\t- Bookmark for a file or subdir in this dir
\\[bmkp-local-file-jump]\t- Local-file bookmark
\\[bmkp-remote-file-jump]\t- Remote-file bookmark
\\[bmkp-region-jump]\t- Region bookmark
\\[bmkp-info-jump]\t- Info bookmark
\\[bmkp-man-jump]\t- `man'-page bookmark
\\[bmkp-non-file-jump]\t- Non-file (buffer) bookmark
\\[bmkp-gnus-jump]\t- Gnus bookmark
\\[bmkp-url-jump]\t- URL bookmark
\\[bmkp-variable-list-jump]\t- Variable-list bookmark
\\[bmkp-autonamed-jump]\t- Autonamed bookmark
\\[bmkp-autonamed-this-buffer-jump]\t- Autonamed bookmark in buffer
\\[bmkp-some-tags-jump]\t- Bookmark having some tags you specify
\\[bmkp-all-tags-jump]\t- Bookmark having each tag you specify
\\[bmkp-some-tags-regexp-jump]\t- Bookmark having a tag that matches a regexp
\\[bmkp-all-tags-regexp-jump]\t- Bookmark having all its tags match a regexp
\\[bmkp-file-some-tags-jump]\t- File bookmark having some tags you specify
\\[bmkp-file-all-tags-jump]\t- File bookmark having each tag you specify
\\[bmkp-file-some-tags-regexp-jump]\t- File bookmark having a tag that matches a regexp
\\[bmkp-file-all-tags-regexp-jump]\t- File bookmark having all its tags match a regexp
\\[bmkp-file-this-dir-some-tags-jump]\t- File in this dir having some tags you specify
\\[bmkp-file-this-dir-all-tags-jump]\t- File in this dir having each tag you specify
\\[bmkp-file-this-dir-some-tags-regexp-jump]\t- File in this dir having a tag that matches a regexp
\\[bmkp-file-this-dir-all-tags-regexp-jump]\t- File in this dir having all its tags match a regexp


Cycle Bookmarks and Autonamed Bookmarks
---------------------------------------

\\[bmkp-toggle-autonamed-bookmark-set/delete]\t- Create/delete autonamed bookmark at point
\\[bmkp-autonamed-jump]\t- Jump to an autonamed bookmark
\\[bmkp-autonamed-this-buffer-jump]\t- Jump to an autonamed bookmark in buffer
C-x p n n ...\t- Next     bookmark in buffer  (C-x p C-n, C-x p down)
C-x p p p ...\t- Previous bookmark in buffer  (C-x p C-p, C-x p up)
C-x p f f ...\t- Next     bookmark in navlist (C-x p C-f, C-x p right)
C-x p b b ...\t- Previous bookmark in navlist (C-x p C-b, C-x p left)
C-x p next  ...\t- MS Windows `Open' next     bookmark in navlist
C-x p prior ...\t- MS Windows `Open' previous bookmark in navlist
C-x C-down  ...\t- Next     highlighted bookmark in buffer
C-x C-up    ...\t- Previous highlighted bookmark in buffer

\\[bmkp-delete-all-autonamed-for-this-buffer]
\t- Delete all autonamed bookmarks in current buffer


Search-and-Replace Targets (in sort order)
--------------------------

M-s a C-s\t- Isearch the marked bookmarks (Emacs 23+)
M-s a C-M-s\t- Regexp-isearch the marked bookmarks (Emacs 23+)
\\[bmkp-bmenu-search-marked-bookmarks-regexp]\t- Regexp-search the marked file bookmarks
\\[bmkp-bmenu-query-replace-marked-bookmarks-regexp]\t\t- Query-replace the marked file \
bookmarks


Mark/Unmark
-----------

\(Mark means `>'.  Flag means `D'.   See also `Tags', below.)

\\[bookmark-bmenu-delete]\t- Flag this bookmark `D' for deletion, then move down
\\[bookmark-bmenu-delete-backwards]\t- Flag this bookmark `D' for deletion, then move up

\\[bookmark-bmenu-mark]\t- Mark this bookmark
\\[bookmark-bmenu-unmark]\t- Unmark this bookmark (`C-u': move up one line)
\\[bookmark-bmenu-backup-unmark]\t- Unmark previous bookmark (move up, then unmark)

\\[bmkp-bmenu-mark-all]\t- Mark all bookmarks
\\[bmkp-bmenu-regexp-mark]\t- Mark all bookmarks whose names match a regexp
\\[bmkp-bmenu-unmark-all]\t- Unmark all bookmarks (`C-u': interactive query)
\\[bmkp-bmenu-toggle-marks]\t- Toggle marks: unmark the marked and mark the unmarked

\\[bmkp-bmenu-mark-autofile-bookmarks]\t- Mark autofile bookmarks
\\[bmkp-bmenu-mark-non-file-bookmarks]\t- Mark non-file (i.e. buffer) bookmarks
\\[bmkp-bmenu-mark-dired-bookmarks]\t- Mark Dired bookmarks
\\[bmkp-bmenu-mark-file-bookmarks]\t- Mark file & directory bookmarks (`C-u': local only)
\\[bmkp-bmenu-mark-gnus-bookmarks]\t- Mark Gnus bookmarks
\\[bmkp-bmenu-mark-lighted-bookmarks]\t- Mark the highlighted bookmarks
\\[bmkp-bmenu-mark-info-bookmarks]\t- Mark Info bookmarks
\\[bmkp-bmenu-mark-desktop-bookmarks]\t- Mark desktop bookmarks
\\[bmkp-bmenu-mark-bookmark-file-bookmarks]\t- Mark bookmark-file bookmarks
\\[bmkp-bmenu-mark-man-bookmarks]\t- Mark `man' page bookmarks (that's `M' twice, not Meta-M)
\\[bmkp-bmenu-mark-region-bookmarks]\t- Mark region bookmarks
\\[bmkp-bmenu-mark-url-bookmarks]\t- Mark URL bookmarks
\\[bmkp-bmenu-mark-w3m-bookmarks]\t- Mark W3M (URL) bookmarks


Modify
------

\(See also `Tags', next.)

\\[bookmark-bmenu-edit-annotation]\t- Edit this bookmark's annotation
\\[bmkp-bmenu-edit-bookmark]\t- Rename and relocate this bookmark
\\[bookmark-bmenu-rename]\t- Rename this bookmark
\\[bookmark-bmenu-relocate]\t- Relocate this bookmark (change file)
\\[bmkp-bmenu-edit-tags]\t- Edit this bookmark's tags
\\[bookmark-bmenu-execute-deletions]\t- Delete (visible) bookmarks flagged `D'
\\[bmkp-bmenu-delete-marked]\t- Delete (visible) bookmarks marked `>'


Tags
----

\\[bmkp-add-tags]\t- Add some tags to a bookmark
\\[bmkp-remove-tags]\t- Remove some tags from a bookmark
\\[bmkp-remove-all-tags]\t- Remove all tags from a bookmark
\\[bmkp-remove-tags-from-all]\t- Remove some tags from all bookmarks
\\[bmkp-rename-tag]\t- Rename a tag in all bookmarks
\\[bmkp-list-all-tags]\t- List all tags used in any bookmarks (`C-u': show tag values)
\\[bmkp-bmenu-edit-tags]\t- Edit this bookmark's tags
\\[bmkp-bmenu-set-tag-value]\t- Set the value of a tag (as attribute)

\\[bmkp-bmenu-add-tags-to-marked]\t- Add some tags to the marked bookmarks
\\[bmkp-bmenu-remove-tags-from-marked]\t- Remove some tags from the marked bookmarks

\\[bmkp-bmenu-mark-bookmarks-tagged-regexp]\t- Mark bookmarks having at least one \
tag that matches a regexp
\\[bmkp-bmenu-mark-bookmarks-tagged-some]\t- Mark bookmarks having at least one tag \
in a set    (OR)
\\[bmkp-bmenu-mark-bookmarks-tagged-all]\t- Mark bookmarks having all of the tags \
in a set     (AND)
\\[bmkp-bmenu-mark-bookmarks-tagged-none]\t- Mark bookmarks not having any of the tags \
in a set (NOT OR)
\\[bmkp-bmenu-mark-bookmarks-tagged-not-all]\t- Mark bookmarks not having all of the \
tags in a set (NOT AND)

\\[bmkp-bmenu-unmark-bookmarks-tagged-regexp]\t- Unmark bookmarks having at least one \
tag that matches a regexp
\\[bmkp-bmenu-unmark-bookmarks-tagged-some]\t- Unmark bookmarks having at least one \
tag in a set  (OR)
\\[bmkp-bmenu-unmark-bookmarks-tagged-all]\t- Unmark bookmarks having all of the tags \
in a set   (AND)
\\[bmkp-bmenu-unmark-bookmarks-tagged-none]\t- Unmark bookmarks not having any tags \
in a set      (NOT OR)
\\[bmkp-bmenu-unmark-bookmarks-tagged-not-all]\t- Unmark bookmarks not having all tags \
in a set      (NOT AND)


Bookmark Highlighting
---------------------

\\[bmkp-bmenu-show-only-lighted]\t- Show only the highlighted bookmarks
\\[bmkp-bmenu-set-lighting]\t- Set highlighting for this bookmark
\\[bmkp-bmenu-set-lighting-for-marked]\t- Set highlighting for marked bookmarks
\\[bmkp-bmenu-light]\t- Highlight this bookmark
\\[bmkp-bmenu-unlight]\t- Unhighlight this bookmark
\\[bmkp-bmenu-mark-lighted-bookmarks]\t- Mark the highlighted bookmarks
\\[bmkp-bmenu-light-marked]\t- Highlight the marked bookmarks
\\[bmkp-bmenu-unlight-marked]\t- Unhighlight the marked bookmarks
\\[bmkp-light-bookmark-this-buffer]\t- Highlight a bookmark in current buffer
\\[bmkp-unlight-bookmark-this-buffer]\t- Unhighlight a bookmark in current buffer
\\[bmkp-light-bookmarks]\t- Highlight bookmarks (see prefix arg)
\\[bmkp-unlight-bookmarks]\t- Unhighlight bookmarks (see prefix arg)
\\[bmkp-bookmarks-lighted-at-point]\t- List bookmarks highlighted at point
\\[bmkp-unlight-bookmark-here]\t- Unhighlight a bookmark at point or on same line


Sort
----

\(Repeat to cycle normal/reversed/off, except as noted.)

\\[bmkp-bmenu-sort-marked-before-unmarked]\t- Sort marked bookmarks first
\\[bmkp-bmenu-sort-by-last-buffer-or-file-access]\t- Sort by last buffer or file \
access
\\[bmkp-bmenu-sort-by-Gnus-thread]\t- Sort by Gnus thread: group, article, message
\\[bmkp-bmenu-sort-by-Info-location]\t- Sort by Info manual, node, position
\\[bmkp-bmenu-sort-by-bookmark-type]\t- Sort by bookmark type
\\[bmkp-bmenu-sort-by-bookmark-name]\t- Sort by bookmark name
\\[bmkp-bmenu-sort-by-creation-time]\t- Sort by bookmark creation time
\\[bmkp-bmenu-sort-by-last-bookmark-access]\t- Sort by last bookmark access time
\\[bmkp-bmenu-sort-by-bookmark-visit-frequency]\t- Sort by bookmark visit frequency
\\[bmkp-bmenu-sort-by-url]\t- Sort by URL

\\[bmkp-bmenu-sort-by-local-file-type]\t- Sort by local file type: file, symlink, dir
\\[bmkp-bmenu-sort-by-file-name]\t- Sort by file name
\\[bmkp-bmenu-sort-by-local-file-size]\t- Sort by local file size
\\[bmkp-bmenu-sort-by-last-local-file-access]\t- Sort by last local file access
\\[bmkp-bmenu-sort-by-last-local-file-update]\t- Sort by last local file update (edit)

\\[bmkp-reverse-sort-order]\t- Reverse current sort direction       (repeat to toggle)
\\[bmkp-reverse-multi-sort-order]\t- Complement sort predicate decisions  (repeat \
to toggle)
\\[bmkp-bmenu-change-sort-order-repeat]\t- Cycle sort orders                    (repeat \
to cycle)


Hide/Show
---------

\\[bmkp-bmenu-show-all]\t- Show all bookmarks
\\[bmkp-bmenu-toggle-show-only-marked]\t- Toggle showing only marked bookmarks
\\[bmkp-bmenu-toggle-show-only-unmarked]\t- Toggle showing only unmarked bookmarks
\\[bmkp-bmenu-show-only-autofiles]\t- Show only autofile bookmarks
\\[bmkp-bmenu-show-only-autonamed]\t- Show only autonamed bookmarks
\\[bmkp-bmenu-show-only-non-files]\t- Show only non-file (i.e. buffer) bookmarks
\\[bmkp-bmenu-show-only-dired]\t- Show only Dired bookmarks
\\[bmkp-bmenu-show-only-files]\t- Show only file & directory bookmarks (`C-u': local only)
\\[bmkp-bmenu-show-only-gnus]\t- Show only Gnus bookmarks
\\[bmkp-bmenu-show-only-info-nodes]\t- Show only Info bookmarks
\\[bmkp-bmenu-show-only-desktops]\t- Show only desktop bookmarks
\\[bmkp-bmenu-show-only-bookmark-files]\t- Show only bookmark-file bookmarks
\\[bmkp-bmenu-show-only-man-pages]\t- Show only `man' page bookmarks
\\[bmkp-bmenu-show-only-regions]\t- Show only region bookmarks
\\[bmkp-bmenu-show-only-variable-lists]\t- Show only variable-list bookmarks
\\[bmkp-bmenu-show-only-urls]\t- Show only URL bookmarks
\\[bmkp-bmenu-show-only-w3m-urls]\t- Show only W3M (URL) bookmarks
\\[bmkp-bmenu-filter-bookmark-name-incrementally]\t- Incrementally show only bookmarks \
whose names match a regexp
\\[bmkp-bmenu-filter-file-name-incrementally]\t- Incrementally show only bookmarks whose \
files match a regexp
\\[bmkp-bmenu-filter-annotation-incrementally]\t- Incrementally show only bookmarks whose \
annotations match a regexp
\\[bmkp-bmenu-filter-tags-incrementally]\t- Incrementally show only bookmarks whose tags \
match a regexp
\\[bmkp-bmenu-show-only-tagged]\t- Show only bookmarks that have tags


Omit/Un-omit
------------

\\[bmkp-bmenu-show-only-omitted]\t- Show (only) the omitted bookmarks
\\[bmkp-bmenu-show-all]\t- Show the un-omitted bookmarks (all)
\\[bmkp-bmenu-omit/unomit-marked]\t- Omit the marked bookmarks; un-omit them if after \
`\\[bmkp-bmenu-show-only-omitted]'
\\[bmkp-unomit-all]\t- Un-omit all omitted bookmarks


Define Commands for `*Bookmark List*'
-------------------------------------

\\[bmkp-bmenu-define-command]\t- Define a command to restore the current sort order & filter
\\[bmkp-bmenu-define-full-snapshot-command]\t- Define a command to restore the current \
bookmark-list state
\\[bmkp-define-tags-sort-command]\t- Define a command to sort bookmarks by tags
\\[bmkp-bmenu-define-jump-marked-command]\t- Define a command to jump to a bookmark that is \
now marked


Options for `*Bookmark List*'
-----------------------------

bookmark-bmenu-file-column       - Bookmark width if files are shown
bookmark-bmenu-toggle-filenames  - Show filenames initially?

bmkp-bmenu-omitted-bookmarks     - List of omitted bookmarks
bmkp-bmenu-state-file            - File to save bookmark-list state
                                   (\"home\") nil: do not save/restore
bmkp-sort-comparer               - Initial sort
bmkp-sort-orders-for-cycling-alist
\t - Sort orders that `\\[bmkp-bmenu-change-sort-order-repeat]'... cycles


Other Options
-------------

bookmark-automatically-show-annotations  - Show annotation when visit?
bookmark-completion-ignore-case  - Case-sensitive completion?
bookmark-default-file            - File to save bookmarks in
bookmark-menu-length             - Max size of bookmark-name menu item
bookmark-save-flag               - Whether and when to save
bookmark-use-annotations         - Query for annotation when saving?
bookmark-version-control         - Numbered backups of bookmark file?

bmkp-autoname-format        - Format of autonamed bookmark name
bmkp-crosshairs-flag        - Highlight position when visit?
bmkp-menu-popup-max-length  - Use menus to choose bookmarks?
bmkp-save-new-location-flag - Save if bookmark relocated?
bmkp-sequence-jump-display-function - How to display a sequence
bmkp-sort-comparer          - Predicates for sorting bookmarks
bmkp-su-or-sudo-regexp      - Bounce-show each end of region?
bmkp-this-buffer-cycle-sort-comparer -  This-buffer cycling sort
bmkp-use-region             - Activate saved region when visit?"
  (kill-all-local-variables)
  (use-local-map bookmark-bmenu-mode-map)
  (setq truncate-lines    t
        buffer-read-only  t
        major-mode        'bookmark-bmenu-mode
        mode-name         "Bookmark Menu")
  (if (fboundp 'run-mode-hooks)
      (run-mode-hooks 'bookmark-bmenu-mode-hook)
    (run-hooks 'bookmark-bmenu-mode-hook)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Put `mouse-face' on whole line, with the same help-echo as for the bookmark name.
;; 2. Fit one-window frame.
;; 3. Added doc string.
;;
(defun bookmark-bmenu-show-filenames (&optional force)
  "Show file names."
  (if (and (not force) bookmark-bmenu-toggle-filenames)
      nil                               ; Already shown, so do nothing.
    (save-excursion
      (save-window-excursion
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (setq bookmark-bmenu-hidden-bookmarks  ())
        (let ((inhibit-read-only  t))
          (while (< (point) (point-max))
            (let ((bmk  (bookmark-bmenu-bookmark)))
              (setq bookmark-bmenu-hidden-bookmarks  (cons bmk bookmark-bmenu-hidden-bookmarks))
	      (let ((start  (save-excursion (end-of-line) (point))))
		(move-to-column bookmark-bmenu-file-column t))
	      (delete-region (point) (progn (end-of-line) (point)))
              (insert "  ")
              (bookmark-insert-location bmk t) ; Pass the NO-HISTORY arg.
              (when (if (fboundp 'display-color-p) ; Emacs 21+.
                        (and (display-color-p) (display-mouse-p))
                      window-system)
                (let ((help  (get-text-property (+ bmkp-bmenu-marks-width
                                                   (line-beginning-position)) 'help-echo)))
                  (put-text-property (+ bmkp-bmenu-marks-width (line-beginning-position))
                                     (point) 'mouse-face 'highlight)
                  (when help  (put-text-property (+ bmkp-bmenu-marks-width (line-beginning-position))
                                                 (point) 'help-echo help))))
              (forward-line 1))))))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
      (fit-frame-if-one-window))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add text properties when hiding filenames.
;; 2. Do not set or use `bookmark-bmenu-bookmark-column' - use `bmkp-bmenu-marks-width' always.
;; 3. Fit one-window frame.
;; 4. Added doc string.
;;
(defun bookmark-bmenu-hide-filenames (&optional force)
  "Hide filenames in bookmark-list buffer.
If either optional arg FORCE or `bookmark-bmenu-toggle-filenames' is
non-nil, then do nothing."
  (when (and (not force)  bookmark-bmenu-toggle-filenames)
    (save-excursion
      (save-window-excursion
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (setq bookmark-bmenu-hidden-bookmarks  (nreverse bookmark-bmenu-hidden-bookmarks))
        (let ((max-width  0))
          (dolist (name  bookmark-bmenu-hidden-bookmarks)
            (setq max-width  (max max-width (length name))))
          (setq max-width  (+ max-width bmkp-bmenu-marks-width))
          (save-excursion
            (let ((inhibit-read-only  t))
              (while bookmark-bmenu-hidden-bookmarks
                (move-to-column bmkp-bmenu-marks-width t)
                (bookmark-kill-line)
                (let ((name   (car bookmark-bmenu-hidden-bookmarks))
                      (start  (point))
                      end)
                  (insert name)
                  (move-to-column max-width t)
                  (setq end  (point))
                  (bmkp-bmenu-propertize-item name start end))
                (setq bookmark-bmenu-hidden-bookmarks  (cdr bookmark-bmenu-hidden-bookmarks))
                (forward-line 1)))))))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
      (fit-frame-if-one-window))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-1-window (&optional use-region-p) ; Bound to `1' in bookmark list
  "Select this line's bookmark, alone, in full frame.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-jump-1 (bookmark-bmenu-bookmark) 'pop-to-buffer use-region-p)
  (bury-buffer (other-buffer))
  (delete-other-windows))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-2-window (&optional use-region-p) ; Bound to `2' in bookmark list
  "Select this line's bookmark, with previous buffer in second window.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name   (bookmark-bmenu-bookmark))
        (menu            (current-buffer))
        (pop-up-windows  t))
    (delete-other-windows)
    (switch-to-buffer (other-buffer))
    ;; (let ((bookmark-automatically-show-annotations nil)) ; $$$$$$ Needed?
    (bmkp-jump-1 bookmark-name 'pop-to-buffer use-region-p)
    (bury-buffer menu)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-this-window (&optional use-region-p) ; Bound to `RET' in bookmark list
  "Select this line's bookmark in this window.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name  (bookmark-bmenu-bookmark)))
    (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `pop-to-buffer', not `switch-to-buffer-other-window'.
;; 2. Prefix arg reverses `bmkp-use-region'.
;; 3. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-other-window (&optional use-region-p) ; Bound to `o' in bookmark list
  "Select this line's bookmark in other window.  Show `*Bookmark List*' still.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name  (bookmark-bmenu-bookmark)))
    ;; (bookmark-automatically-show-annotations  t)) ; $$$$$$ Needed?
    (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-switch-other-window (&optional use-region-p) ; Bound to `C-o' in bookmark list
  "Make the other window select this line's bookmark.
The current window remains selected.
See `bookmark-jump' for info about the prefix arg."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark-name             (bookmark-bmenu-bookmark))
        (pop-up-windows            t)
        (same-window-buffer-names  ())
        (same-window-regexps       ()))
    ;; (bookmark-automatically-show-annotations t)) ; $$$$$$ Needed?
    (bmkp-jump-1 bookmark-name 'display-buffer use-region-p)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg reverses `bmkp-use-region'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-other-window-with-mouse (event &optional use-region-p)
  "Select clicked bookmark in other window.  Show `*Bookmark List*' still."
  (interactive "e\nP")
  (with-current-buffer (window-buffer (posn-window (event-end event)))
    (save-excursion (goto-char (posn-point (event-end event)))
                    (bookmark-bmenu-other-window use-region-p))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg MSGP.
;; 2. Call `bookmark-show-annotation' with arg MSGP.
;; 3. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-show-annotation (msgp)
  "Show the annotation for the current bookmark in another window."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark  (bookmark-bmenu-bookmark)))
    (bookmark-show-annotation bookmark msgp)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg MARKEDP: handle bookmarks marked `>', not just those flagged `D'.
;; 2. Use `bookmark-bmenu-surreptitiously-rebuild-list', instead of using
;;    `bookmark-bmenu-list', updating the modification count, and saving.
;; 3. Update `bmkp-latest-bookmark-alist' to reflect the deletions.
;; 4. Pass full bookmark, not name, to `delete' (and do not use `assoc').
;; 5. Use `bmkp-bmenu-goto-bookmark-named'.
;; 6. Added status messages.
;; 7. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-execute-deletions (&optional markedp) ; Bound to `x' in bookmark list
  "Delete (visible) bookmarks flagged `D'.
With a prefix argument, delete the bookmarks marked `>' instead, after
confirmation."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (or (not markedp) (yes-or-no-p "Delete bookmarks marked `>' (not `D') "))
      (let* ((mark-type  (if markedp "^>" "^D"))
             (o-str      (and (not (looking-at mark-type)) (bookmark-bmenu-bookmark)))
             (o-point    (point))
             (count      0))
        (message "Deleting bookmarks...")
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (while (re-search-forward mark-type (point-max) t)
          (let* ((bmk-name  (bookmark-bmenu-bookmark))
                 (bmk       (bookmark-get-bookmark bmk-name)))
            (bookmark-delete bmk-name 'batch)
            (setq count                       (1+ count)
                  bmkp-latest-bookmark-alist  (delete bmk bmkp-latest-bookmark-alist))))
        (if (<= count 0)
            (message (if markedp "No marked bookmarks" "No bookmarks flagged for deletion"))
          (bookmark-bmenu-surreptitiously-rebuild-list)
          (message "Deleted %d bookmarks" count))
        (if o-str
            (bmkp-bmenu-goto-bookmark-named o-str)
          (goto-char o-point)
          (beginning-of-line)))
    (message "OK, nothing deleted")))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Do not call `bookmark-bmenu-list' (it was already called).
;; 2. Raise error if not in buffer `*Bookmark List*'.
;; 3. Use `bmkp-bmenu-goto-bookmark-named' instead of just searching for name.
;;
;;;###autoload
(defun bookmark-bmenu-rename ()         ; Bound to `r' in bookmark list
  "Rename bookmark on current line.  Prompts for a new name."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((newname  (bookmark-rename (bookmark-bmenu-bookmark))))
    (bmkp-bmenu-goto-bookmark-named newname)))
 
;;(@* "Bookmark+ Functions (`bmkp-*')")
;;; Bookmark+ Functions (`bmkp-*') -----------------------------------


;;(@* "Menu-List (`*-bmenu-*') Filter Commands")
;;  *** Menu-List (`*-bmenu-*') Filter Commands ***

;;;###autoload
(defun bmkp-bmenu-show-only-autofiles (&optional arg) ; Bound to `A S' in bookmark list
  "Display (only) the autofile bookmarks.
This means bookmarks whose names are the same as their (non-directory)
file names.  But with a prefix arg you are prompted for a prefix that
each bookmark name must have."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  (if (not arg)
                                        'bmkp-autofile-alist-only
                                      (let ((prefix  (read-string "Prefix for bookmark names: "
                                                                  nil nil "")))      
                                        `(lambda () (bmkp-autofile-alist-only ,prefix))))
        bmkp-bmenu-title            "Autofile Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only autofile bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-autonamed () ; Bound to `# S' in bookmark list
  "Display (only) the autonamed bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-autonamed-alist-only
        bmkp-bmenu-title            "Autonamed Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only autonamed bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-bookmark-files () ; Bound to `X S' in bookmark list
  "Display (only) the bookmark-file bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-bookmark-file-alist-only
        bmkp-bmenu-title            "Bookmark-File Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only bookmark-file bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-desktops () ; Bound to `K S' in bookmark list
  "Display (only) the desktop bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-desktop-alist-only
        bmkp-bmenu-title            "Desktop Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only desktop bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-dired ()    ; Bound to `M-d M-s' in bookmark list
  "Display (only) the Dired bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-dired-alist-only
        bmkp-bmenu-title            "Dired Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only Dired bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-files (arg) ; Bound to `F S' in bookmark list
  "Display a list of file and directory bookmarks (only).
With a prefix argument, do not include remote files or directories."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  (if arg 'bmkp-local-file-alist-only 'bmkp-file-alist-only)
        bmkp-bmenu-title            (if arg
                                        "Local File and Directory Bookmarks"
                                      "File and Directory Bookmarks"))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only file bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-non-files () ; Bound to `B S' in bookmark list
  "Display (only) the non-file bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-non-file-alist-only
        bmkp-bmenu-title            "Non-File Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only non-file bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-gnus ()     ; Bound to `G S' in bookmark list
  "Display (only) the Gnus bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-gnus-alist-only
        bmkp-bmenu-title            "Gnus Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only Gnus bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-info-nodes () ; Bound to `I S' in bookmark list
  "Display (only) the Info bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-info-alist-only
        bmkp-bmenu-title            "Info Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only Info bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-man-pages () ; Bound to `M S' in bookmark list
  "Display (only) the `man' page bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-man-alist-only
        bmkp-bmenu-title            "`man' Page Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only `man' page bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-regions ()  ; Bound to `R S' in bookmark list
  "Display (only) the bookmarks that record a region."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-region-alist-only
        bmkp-bmenu-title            "Region Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only bookmarks with regions are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-variable-lists () ; Bound to `V S' in bookmark list
  "Display (only) the variable-list bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-variable-list-alist-only
        bmkp-bmenu-title            "Variable-list Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only variable-list bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-specific-buffer (&optional buffer) ; Bound to `= b S' in bookmark list
  "Display (only) the bookmarks for BUFFER.
Interactively, read the BUFFER name.
If BUFFER is non-nil, set `bmkp-last-specific-buffer' to it."
  (interactive (list (bmkp-completing-read-buffer-name)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when buffer (setq bmkp-last-specific-buffer  buffer))
  (setq bmkp-bmenu-filter-function  'bmkp-last-specific-buffer-alist-only
        bmkp-bmenu-title            (format "Buffer `%s' Bookmarks" bmkp-last-specific-buffer))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                               (format "Only bookmarks for buffer `%s' are shown"
                                       bmkp-last-specific-buffer))))

;;;###autoload
(defun bmkp-bmenu-show-only-specific-file (&optional file) ; Bound to `= f S' in bookmark list
  "Display (only) the bookmarks for FILE, an absolute file name.
Interactively, read the FILE name.
If FILE is non-nil, set `bmkp-last-specific-file' to it."
  (interactive (list (bmkp-completing-read-file-name)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when file (setq bmkp-last-specific-file  file))
  (setq bmkp-bmenu-filter-function  'bmkp-last-specific-file-alist-only
        bmkp-bmenu-title            (format "File `%s' Bookmarks" bmkp-last-specific-file))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                               (format "Only bookmarks for file `%s' are shown"
                                       bmkp-last-specific-file))))

;;;###autoload
(defun bmkp-bmenu-show-only-urls ()     ; Bound to `M-u M-s' in bookmark list
  "Display (only) the URL bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-url-alist-only
        bmkp-bmenu-title            "URL Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only URL bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-only-w3m-urls () ; Bound to `W S' in bookmark list
  "Display (only) the W3M URL bookmarks."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-w3m-alist-only
        bmkp-bmenu-title            "W3M Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only W3M bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-show-all ()           ; Bound to `.' in bookmark list
  "Show all bookmarks known to the bookmark list (aka \"menu list\").
Omitted bookmarks are not shown, however.
Also, this does not revert the bookmark list, to bring it up to date.
To revert the list, use `\\<bookmark-bmenu-mode-map>\\[bmkp-bmenu-refresh-menu-list]'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  nil
        bmkp-bmenu-title            "All Bookmarks"
        bmkp-latest-bookmark-alist  bookmark-alist)
  (bookmark-bmenu-list)
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "All bookmarks are shown")))

;;;###autoload
(defun bmkp-bmenu-refresh-menu-list ()  ; Bound to `g' in bookmark list
  "Refresh (revert) the bookmark list (\"menu list\").
This brings the displayed list up to date.  It does not change the
current filtering or sorting of the displayed list.

If you want setting a bookmark to refresh the list automatically, you
can use command `bmkp-toggle-bookmark-set-refreshes'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-refresh-menu-list (bookmark-bmenu-bookmark)))

;;;###autoload
(defun bmkp-bmenu-filter-bookmark-name-incrementally () ; Bound to `P B' in bookmark list
  "Incrementally filter bookmarks by bookmark name using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-timer 0 bmkp-incremental-filter-delay
                                    #'bmkp-bmenu-filter-alist-by-bookmark-name-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-bookmark-name-regexp ()
  "Filter bookmarks by bookmark name, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-bookmark-name-alist-only
        bmkp-bmenu-title            (format "Bookmarks with Names Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload
(defun bmkp-bmenu-filter-file-name-incrementally () ; Bound to `P F' in bookmark list
  "Incrementally filter bookmarks by file name using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-timer 0 bmkp-incremental-filter-delay
                                    #'bmkp-bmenu-filter-alist-by-file-name-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-file-name-regexp ()
  "Filter bookmarks by file name, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-file-name-alist-only
        bmkp-bmenu-title            (format "Bookmarks with File Names Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload
(defun bmkp-bmenu-filter-annotation-incrementally () ; Bound to `P A' in bookmark list
  "Incrementally filter bookmarks by their annotations using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-timer 0 bmkp-incremental-filter-delay
                                    #'bmkp-bmenu-filter-alist-by-annotation-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-annotation-regexp ()
  "Filter bookmarks by annoation, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-annotation-alist-only
        bmkp-bmenu-title            (format "Bookmarks with Annotations Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload
(defun bmkp-bmenu-filter-tags-incrementally () ; Bound to `P T' in bookmark list
  "Incrementally filter bookmarks by tags using a regexp."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bmkp-bmenu-filter-timer
                    (run-with-timer 0 bmkp-incremental-filter-delay
                                    #'bmkp-bmenu-filter-alist-by-tags-regexp))
              (bmkp-bmenu-read-filter-input))
    (bmkp-bmenu-cancel-incremental-filtering)))

(defun bmkp-bmenu-filter-alist-by-tags-regexp ()
  "Filter bookmarks by tags, then refresh the bookmark list."
  (setq bmkp-bmenu-filter-function  'bmkp-regexp-filtered-tags-alist-only
        bmkp-bmenu-title            (format "Bookmarks with Tags Matching Regexp `%s'"
                                            bmkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

(defun bmkp-bmenu-read-filter-input ()
  "Read input and add it to `bmkp-bmenu-filter-pattern'."
  (setq bmkp-bmenu-filter-pattern  "")
  (let ((tmp-list  ())
        char)
    (catch 'bmkp-bmenu-read-filter-input-1
      (while t
        (catch 'bmkp-bmenu-read-filter-input-2
          (condition-case nil
              (setq char  (read-char (concat bmkp-bmenu-filter-prompt bmkp-bmenu-filter-pattern)))
            (error (throw 'bmkp-bmenu-read-filter-input-1 nil)))
          (case char
            ((?\e ?\r) (throw 'bmkp-bmenu-read-filter-input-1 nil)) ; Break and exit.
            (?\d
             (pop tmp-list)             ; Delete last char of `bmkp-bmenu-filter-pattern'.
             (setq bmkp-bmenu-filter-pattern  (mapconcat 'identity (reverse tmp-list) ""))
             (throw 'bmkp-bmenu-read-filter-input-2 nil))
            (t
             (push (text-char-description char) tmp-list)
             (setq bmkp-bmenu-filter-pattern  (mapconcat 'identity (reverse tmp-list) ""))
             (throw 'bmkp-bmenu-read-filter-input-2 nil))))))))

(defun bmkp-bmenu-cancel-incremental-filtering ()
  "Cancel timer used for incrementally filtering bookmarks."
  (cancel-timer bmkp-bmenu-filter-timer)
  (setq bmkp-bmenu-filter-timer  nil))

;;;###autoload
(defun bmkp-bmenu-toggle-show-only-unmarked () ; Bound to `<' in bookmark list
  "Hide all marked bookmarks.  Repeat to toggle, showing all."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (or (bmkp-some-marked-p bmkp-latest-bookmark-alist)
          (bmkp-some-marked-p bmkp-bmenu-before-hide-marked-alist))
      (let ((bookmark-alist  bmkp-latest-bookmark-alist)
            status)
        (if bmkp-bmenu-before-hide-marked-alist
            (setq bookmark-alist                       bmkp-bmenu-before-hide-marked-alist
                  bmkp-bmenu-before-hide-marked-alist  ()
                  bmkp-latest-bookmark-alist           bookmark-alist
                  status                               'shown)
          (setq bmkp-bmenu-before-hide-marked-alist  bmkp-latest-bookmark-alist
                bookmark-alist                       (bmkp-unmarked-bookmarks-only)
                bmkp-latest-bookmark-alist           bookmark-alist
                status                               'hidden))
        (bookmark-bmenu-surreptitiously-rebuild-list)
        (cond ((eq status 'hidden)
               (bookmark-bmenu-ensure-position)
               (message "Marked bookmarks are now hidden"))
              (t
               (goto-char (point-min))
               (when (re-search-forward "^>" (point-max) t)  (forward-line 0))
               (message "Marked bookmarks no longer hidden"))))
    (message "No marked bookmarks to hide"))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload
(defun bmkp-bmenu-toggle-show-only-marked () ; Bound to `>' in bookmark list
  "Hide all unmarked bookmarks.  Repeat to toggle, showing all."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (or (bmkp-some-unmarked-p bmkp-latest-bookmark-alist)
          (bmkp-some-unmarked-p bmkp-bmenu-before-hide-unmarked-alist))
      (let ((bookmark-alist  bmkp-latest-bookmark-alist)
            status)
        (if bmkp-bmenu-before-hide-unmarked-alist
            (setq bookmark-alist                         bmkp-bmenu-before-hide-unmarked-alist
                  bmkp-bmenu-before-hide-unmarked-alist  ()
                  bmkp-latest-bookmark-alist             bookmark-alist
                  status                                 'shown)
          (setq bmkp-bmenu-before-hide-unmarked-alist  bmkp-latest-bookmark-alist
                bookmark-alist                         (bmkp-marked-bookmarks-only)
                bmkp-latest-bookmark-alist             bookmark-alist
                status                                 'hidden))
        (bookmark-bmenu-surreptitiously-rebuild-list)
        (cond ((eq status 'hidden)
               (bookmark-bmenu-ensure-position)
               (message "Unmarked bookmarks are now hidden"))
              (t
               (goto-char (point-min))
               (when (re-search-forward "^>" (point-max) t)  (forward-line 0))
               (message "Unmarked bookmarks no longer hidden"))))
    (message "No unmarked bookmarks to hide"))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))


;;(@* "Menu-List (`*-bmenu-*') Commands Involving Marks")
;;  *** Menu-List (`*-bmenu-*') Commands Involving Marks ***

;;;###autoload
(defun bmkp-bmenu-mark-all ()           ; Bound to `M-m' in bookmark list
  "Mark all bookmarks, using mark `>'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (save-excursion  
    (let ((count  0))
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (while (not (eobp)) (bookmark-bmenu-mark) (setq count  (1+ count)))
      (message "Marked: %d" count))))

;; This is similar to `dired-unmark-all-files'.
;;;###autoload
(defun bmkp-bmenu-unmark-all (mark &optional arg) ; Bound to `M-DEL', `U' in bookmark list
  "Remove a mark from each bookmark.
Hit the mark character (`>' or `D') to remove those marks,
 or hit `RET' to remove all marks (both `>' and `D').
With a prefix arg, you are queried to unmark each marked bookmark.
Use `\\[help-command]' during querying for help."
  (interactive "cRemove marks (RET means all): \nP")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (require 'dired-aux)
  (save-excursion
    (let* ((count              0)
           (inhibit-read-only  t)
           (case-fold-search   nil)
           (query              nil)
           (string             (format "\n%c" mark))
           (help-form          "Type SPC or `y' to unmark one bookmark, DEL or `n' to skip to next,
`!' to unmark all remaining bookmarks with no more questions."))
      (goto-char (point-min))
      (forward-line (if (eq mark ?\r)
                        bmkp-bmenu-header-lines
                      (1- bmkp-bmenu-header-lines))) ; Because STRING starts with a newline.
      (while (and (not (eobp))
                  (if (eq mark ?\r)
                      (re-search-forward dired-re-mark nil t)
                    (let ((case-fold-search  t)) ; Treat `d' the same as `D'.
                      (search-forward string nil t))))
        (when (or (not arg)  (let ((bmk  (bookmark-bmenu-bookmark)))
                               (and bmk (dired-query 'query "Unmark bookmark `%s'? " bmk))))
          (bookmark-bmenu-unmark) (forward-line -1)
          (setq count  (1+ count))))
      (if (= 1 count) (message "1 mark removed") (message "%d marks removed" count)))))

;;;###autoload
(defun bmkp-bmenu-regexp-mark (regexp)  ; Bound to `% m' in bookmark list
  "Mark bookmarks that match REGEXP.
The entire bookmark line is tested: bookmark name and possibly file name."
  (interactive "sRegexp: ")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (let ((count  0))
      (while (and (not (eobp)) (re-search-forward regexp (point-max) t))
        (bookmark-bmenu-mark)
        (setq count  (1+ count)))
      (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload
(defun bmkp-bmenu-mark-autofile-bookmarks (&optional arg) ; Bound to `A M' in bookmark list
  "Mark autofile bookmarks: those whose names are the same as their files.
With a prefix arg you are prompted for a prefix that each bookmark
name must have."
  (interactive "P")
  (if (not arg)
      (bmkp-bmenu-mark-bookmarks-satisfying #'bmkp-autofile-bookmark-p)
    (let ((prefix  (read-string "Prefix for bookmark names: " nil nil "")))
      (bmkp-bmenu-mark-bookmarks-satisfying #'(lambda (bb) (bmkp-autofile-bookmark-p bb prefix))))))

;;;###autoload
(defun bmkp-bmenu-mark-bookmark-file-bookmarks () ; Bound to `X M' in bookmark list
  "Mark bookmark-file bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-bookmark-file-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-desktop-bookmarks () ; Bound to `K M' in bookmark list
  "Mark desktop bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-desktop-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-dired-bookmarks () ; Bound to `M-d M-m' in bookmark list
  "Mark Dired bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-dired-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-file-bookmarks (arg) ; Bound to `F M' in bookmark list
  "Mark file bookmarks.
With a prefix argument, do not mark remote files or directories."
  (interactive "P")
  (bmkp-bmenu-mark-bookmarks-satisfying
   (if arg 'bmkp-local-file-bookmark-p 'bmkp-file-bookmark-p)))

;;;###autoload
(defun bmkp-bmenu-mark-gnus-bookmarks () ; Bound to `G M' in bookmark list
  "Mark Gnus bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-gnus-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-info-bookmarks () ; Bound to `I M' in bookmark list
  "Mark Info bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-info-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-man-bookmarks () ; Bound to `M M' in bookmark list
  "Mark `man' page bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-man-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-non-file-bookmarks () ; Bound to `B M' in bookmark list
  "Mark non-file bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-non-file-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-region-bookmarks () ; Bound to `R M' in bookmark list
  "Mark bookmarks that record a region."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-region-bookmark-p))

(when (featurep 'bookmark+-lit)
  (defun bmkp-bmenu-mark-lighted-bookmarks () ; Bound to `H M' in bookmark list
    "Mark the highlighted bookmarks."
    (interactive)
    (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-lighted-p)))

;;;###autoload
(defun bmkp-bmenu-mark-specific-buffer-bookmarks (&optional buffer) ; `= b M' in bookmark list
  "Mark bookmarks for BUFFER.
Interactively, read the name of the buffer.
If BUFFER is non-nil, set `bmkp-last-specific-buffer' to it."
  (interactive (list (bmkp-completing-read-buffer-name)))
  (when buffer (setq bmkp-last-specific-buffer  buffer))
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-last-specific-buffer-p))

;;;###autoload
(defun bmkp-bmenu-mark-specific-file-bookmarks (&optional file) ; Bound to `= f M' in bookmark list
  "Mark bookmarks for FILE, an absolute file name.
Interactively, read the file name.
If FILE is non-nil, set `bmkp-last-specific-file' to it."
  (interactive (list (bmkp-completing-read-file-name)))
  (when file (setq bmkp-last-specific-file  file))
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-last-specific-file-p))

;;;###autoload
(defun bmkp-bmenu-mark-url-bookmarks () ; Bound to `M-u M-m' in bookmark list
  "Mark URL bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-url-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-w3m-bookmarks () ; Bound to `W M' in bookmark list
  "Mark W3M (URL) bookmarks."
  (interactive)
  (bmkp-bmenu-mark-bookmarks-satisfying 'bmkp-w3m-bookmark-p))

;;;###autoload
(defun bmkp-bmenu-mark-bookmarks-satisfying (pred) ; Not bound
  "Mark bookmarks that satisfy predicate PRED.
If you use this interactively, you are responsible for entering a
symbol that names a unnary predicate.  The function you provide is not
checked - it is simply applied to each bookmark to test it."
  (interactive "aPredicate: ")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (let ((count  0)
          bmk)
      (while (not (eobp))
        (setq bmk  (bookmark-bmenu-bookmark))
        (if (not (funcall pred bmk))
            (forward-line 1)
          (bookmark-bmenu-mark)
          (setq count  (1+ count))))
      (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload
(defun bmkp-bmenu-toggle-marks ()       ; Bound to `t' in bookmark list
  "Toggle marks: Unmark all marked bookmarks; mark all unmarked bookmarks.
This affects only the `>' mark, not the `D' flag."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked-count    0)
        (unmarked-count  0))
    (save-excursion
      (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
      (if (not (bmkp-some-marked-p bmkp-latest-bookmark-alist))
          (bmkp-bmenu-mark-all)
        (while (not (eobp))
          (cond ((bmkp-bookmark-name-member (bookmark-bmenu-bookmark) bmkp-bmenu-marked-bookmarks)
                 (bookmark-bmenu-unmark)
                 (setq unmarked-count  (1+ unmarked-count)))
                (t
                 (bookmark-bmenu-mark)
                 (setq marked-count  (1+ marked-count)))))
        (message "Marked: %d, unmarked: %d" marked-count unmarked-count)))))

;;;###autoload
(defun bmkp-bmenu-dired-marked (dirbufname) ; Bound to `M-d >' in bookmark list
  "Dired in another window for the marked file and directory bookmarks.

Absolute file names are used for the entries in the Dired buffer.
The only entries are for the marked files and directories.  These can
be located anywhere.  (In Emacs versions prior to release 23.2, remote
bookmarks are ignored, because of Emacs bug #5478.)

You are prompted for the Dired buffer name.  The `default-directory'
of the buffer is the same as that of buffer `*Bookmark List*'."
  (interactive (list (read-string "Dired buffer name: ")))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((files  ())
        file)
    (dolist (bmk  (bmkp-sort-omit (bmkp-marked-bookmarks-only)))
      (when (or (bmkp-local-file-bookmark-p bmk)
                (> emacs-major-version 23)
                (and (= emacs-major-version 23) (> emacs-minor-version 1)))
        (setq file  (bookmark-get-filename bmk))
        (unless (file-name-absolute-p file) (setq file (expand-file-name file))) ; Should not happen.
        (push file files)))
    (dired-other-window (cons dirbufname files))))

;;;###autoload
(defun bmkp-bmenu-delete-marked ()      ; Bound to `D' in bookmark list
  "Delete all (visible) bookmarks that are marked `>', after confirmation."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-execute-deletions 'marked))

;;;###autoload
(defun bmkp-bmenu-make-sequence-from-marked (bookmark-name &optional dont-omit-p) ; Not bound
  "Create or update a sequence bookmark from the visible marked bookmarks.
The bookmarks that are currently marked are recorded as a sequence, in
their current order in buffer `*Bookmark List*'.
When you \"jump\" to the sequence bookmark, the bookmarks in the
sequence are processed in order.

By default, omit the marked bookmarks, after creating the sequence.
With a prefix arg, do not omit them.

If a bookmark with the specified name already exists, it is
overwritten.  If a sequence bookmark with the name already exists,
then you are prompted whether to add the marked bookmarks to the
beginning of the existing sequence (or simply replace it).

Note that another existing sequence bookmark can be marked, and thus
included in the sequence bookmark created or updated.  That is, you
can include other sequences within a sequence bookmark.

Returns the bookmark (internal record) created or updated."
  (interactive "sName of sequence bookmark: \nP")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked-bmks  ())
        (count        0))
    (message "Making sequence from marked bookmarks...")
    (save-excursion
      (with-current-buffer "*Bookmark List*"
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (while (re-search-forward "^>" (point-max) t)
          (push (bookmark-bmenu-bookmark) marked-bmks)
          (setq count  (1+ count)))))
    (when (zerop count) (error "No marked bookmarks"))
    (let ((new-seq  (nreverse marked-bmks))
          (bmk      (bookmark-get-bookmark bookmark-name 'noerror)))
      (when (and bmk (bmkp-sequence-bookmark-p bmk))
        (if (y-or-n-p (format "ADD marked to existing sequence `%s' (otherwise, REPLACES it)? "
                              bookmark-name))
            (setq new-seq  (nconc new-seq (bookmark-prop-get bmk 'sequence)))
          "OK, existing sequence will be replaced"))
      (bookmark-store bookmark-name `((filename . ,bmkp-non-file-filename)
                                      (position . 0)
                                      (sequence ,@new-seq)
                                      (handler  . bmkp-jump-sequence))
                      nil)))
  (let ((new  (bookmark-get-bookmark bookmark-name 'noerror)))
    (unless (memq new bmkp-latest-bookmark-alist)
      (setq bmkp-latest-bookmark-alist  (cons new bmkp-latest-bookmark-alist)))
    (unless dont-omit-p
      (bmkp-bmenu-omit-marked)
      (message "Marked bookmarks now OMITTED - use `bmkp-bmenu-show-only-omitted' to show"))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (bmkp-bmenu-goto-bookmark-named bookmark-name)
    new))


;;(@* "Omitted Bookmarks")
;;  *** Omitted Bookmarks ***

;;;###autoload
(defun bmkp-bmenu-omit ()               ; Not bound
  "Omit this bookmark."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (setq bmkp-bmenu-omitted-bookmarks  (cons (bookmark-bmenu-bookmark) bmkp-bmenu-omitted-bookmarks))
  (bookmark-bmenu-surreptitiously-rebuild-list)
  (message "Omitted 1 bookmark"))

;;;###autoload
(defun bmkp-bmenu-omit/unomit-marked () ; Bound to `O >' in bookmark list
  "Omit all marked bookmarks or, if showing only omitted ones, unomit."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (eq bmkp-bmenu-filter-function  'bmkp-omitted-alist-only)
      (bmkp-bmenu-unomit-marked)
    (bmkp-bmenu-omit-marked)))

;;;###autoload
(defun bmkp-bmenu-omit-marked ()        ; Bound to `O >' in bookmark list
  "Omit all marked bookmarks.
They will henceforth be invisible to the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>`\\[bmkp-bmenu-show-only-omitted]' to see them.
You can then mark some of them and use `\\[bmkp-bmenu-omit/unomit-marked]' to make those marked
 available again for the bookmark list."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((o-str    (and (not (looking-at "^>")) (bookmark-bmenu-bookmark)))
        (o-point  (point))
        (count    0))
    (message "Omitting marked bookmarks...")
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (setq bmkp-bmenu-omitted-bookmarks  (cons (bookmark-bmenu-bookmark) bmkp-bmenu-omitted-bookmarks)
            count                    (1+ count)))
    (if (<= count 0)
        (message "No marked bookmarks")
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (message "Omitted %d bookmarks" count))
    (if o-str
        (bmkp-bmenu-goto-bookmark-named o-str)
      (goto-char o-point)
      (beginning-of-line)))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload
(defun bmkp-bmenu-unomit-marked ()      ; `O >' in bookmark list when showing omitted bookmarks
  "Remove all marked bookmarks from the list of omitted bookmarks.
They will henceforth be available for display in the bookmark list.
\(In order to see and then mark omitted bookmarks you must use \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-show-only-omitted]'.)"
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unless bmkp-bmenu-omitted-bookmarks (error "No omitted bookmarks to UN-omit"))
  (unless (eq bmkp-bmenu-filter-function  'bmkp-omitted-alist-only)
    (error "You must use command `bmkp-bmenu-show-only-omitted' first"))
  (let ((count    0))
    (message "UN-omitting marked bookmarks...")
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (let ((bmk-name  (bookmark-bmenu-bookmark)))
        (when (bmkp-bookmark-name-member bmk-name bmkp-bmenu-omitted-bookmarks)
          (setq bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
                                               bmk-name bmkp-bmenu-omitted-bookmarks)
                count                         (1+ count)))))
    (if (<= count 0)
        (message "No marked bookmarks")
      (setq bmkp-bmenu-filter-function  nil
            bmkp-bmenu-title            "All Bookmarks"
            bmkp-latest-bookmark-alist  bookmark-alist)
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (message "UN-omitted %d bookmarks" count)))
  (when (and (fboundp 'fit-frame-if-one-window)
             (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*") 0)))
    (fit-frame-if-one-window)))

;;;###autoload
(defun bmkp-bmenu-show-only-omitted ()  ; Bound to `O S' in bookmark list to show only omitted
  "Show only the omitted bookmarks.
You can then mark some of them and use `bmkp-bmenu-unomit-marked' to
 make those that are marked available again for the bookmark list."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (unless bmkp-bmenu-omitted-bookmarks (error "No omitted bookmarks"))
  (setq bmkp-bmenu-filter-function  'bmkp-omitted-alist-only
        bmkp-bmenu-title            "Omitted Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only omitted bookmarks are shown now")))


;;(@* "Search-and-Replace Locations of Marked Bookmarks")
;;  *** Search-and-Replace Locations of Marked Bookmarks ***

(when (> emacs-major-version 22)
  (defun bmkp-bmenu-isearch-marked-bookmarks () ; Bound to `M-s a C-s' in bookmark list
    "Isearch the marked bookmark locations, in their current order."
    (interactive)
    (bmkp-bmenu-barf-if-not-in-menu-list)
    (let ((bookmarks        (mapcar #'car (bmkp-sort-omit (bmkp-marked-bookmarks-only))))
          (bmkp-use-region  nil))  ; Suppress region handling.
      (bmkp-isearch-bookmarks bookmarks))) ; Defined in `bookmark+-1.el'.

  (defun bmkp-bmenu-isearch-marked-bookmarks-regexp () ; Bound to `M-s a M-C-s' in bookmark list
    "Regexp Isearch the marked bookmark locations, in their current order."
    (interactive)
    (bmkp-bmenu-barf-if-not-in-menu-list)
    (let ((bookmarks        (mapcar #'car (bmkp-sort-omit (bmkp-marked-bookmarks-only))))
          (bmkp-use-region  nil))  ; Suppress region handling.
      (bmkp-isearch-bookmarks-regexp bookmarks)))) ; Defined in `bookmark+-1.el'.

;;;###autoload
(defun bmkp-bmenu-search-marked-bookmarks-regexp (regexp) ; Bound to `M-s a M-s' in bookmark list
  "Search the marked file bookmarks, in their current order, for REGEXP.
Use `\\[tags-loop-continue]' to advance among the search hits.
Marked directory and non-file bookmarks are ignored."
  (interactive "sSearch marked file bookmarks (regexp): ")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (tags-search regexp '(let ((files  ())
                             file)
                        (dolist (bmk  (bmkp-sort-omit (bmkp-marked-bookmarks-only)))
                          (setq file  (bookmark-get-filename bmk))
                          (when (and (not (equal bmkp-non-file-filename file))
                                     (not (file-directory-p file)))
                            (push file files)))
                        (setq files  (nreverse files)))))

;;;###autoload
(defun bmkp-bmenu-query-replace-marked-bookmarks-regexp (from to ; Bound to `M-q' in bookmark list
                                                         &optional delimited)
  "`query-replace-regexp' FROM with TO, for all marked file bookmarks.
DELIMITED (prefix arg) means replace only word-delimited matches.
If you exit (`\\[keyboard-quit]', `RET' or `q'), you can use \
`\\[tags-loop-continue]' to resume where
you left off."
  (interactive (let ((common  (query-replace-read-args "Query replace regexp in marked files" t t)))
                 (list (nth 0 common) (nth 1 common) (nth 2 common))))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (tags-query-replace from to delimited
		      '(let ((files  ())
                             file)
                        (dolist (bmk  (bmkp-sort-omit (bmkp-marked-bookmarks-only)))
                          (setq file  (bookmark-get-filename bmk))
                          (let ((buffer  (get-file-buffer file)))
                            (when (and buffer  (with-current-buffer buffer buffer-read-only))
                              (error "File `%s' is visited read-only" file)))
                          (when (and (not (equal bmkp-non-file-filename file))
                                     (not (file-directory-p file)))
                            (push file files)))
                        (setq files  (nreverse files)))))


;;(@* "Tags")
;;  *** Tags ***

;;;###autoload
(defun bmkp-bmenu-show-only-tagged ()   ; Bound to `T S' in bookmark list
  "Display (only) the bookmarks that have tags."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-bmenu-filter-function  'bmkp-some-tags-alist-only
        bmkp-bmenu-title            "Tagged Bookmarks")
  (let ((bookmark-alist  (funcall bmkp-bmenu-filter-function)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order) "Only tagged bookmarks are shown")))

;; Not bound, but `T 0' is `bmkp-remove-all-tags'.
;;;###autoload
(defun bmkp-bmenu-remove-all-tags (&optional must-confirm-p)
  "Remove all tags from this bookmark.
Interactively, you are required to confirm."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark  (bookmark-bmenu-bookmark)))
    (when (and must-confirm-p (null (bmkp-get-tags bookmark)))
      (error "Bookmark has no tags to remove"))
    (when (or (not must-confirm-p) (y-or-n-p "Remove all tags from this bookmark? "))
      (bmkp-remove-all-tags bookmark))))

;;;###autoload
(defun bmkp-bmenu-add-tags ()           ; Only on `mouse-3' menu in bookmark list.
  "Add some tags to this bookmark."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-add-tags (bookmark-bmenu-bookmark) (bmkp-read-tags-completing)))

;;;###autoload
(defun bmkp-bmenu-set-tag-value ()      ; Bound to `T v' in bookmark list
  "Set the value of one of this bookmark's tags."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((this-bmk  (bookmark-bmenu-bookmark)))
    (bmkp-set-tag-value
     this-bmk
     (bmkp-read-tag-completing "Tag: " (mapcar 'bmkp-full-tag (bmkp-get-tags this-bmk)))
     (read (read-string "Value: "))
     'msg)))

;;;###autoload
(defun bmkp-bmenu-set-tag-value-for-marked (tag value &optional msgp) ; `T > v' in bookmark list
  "Set the value of TAG to VALUE, for each of the marked bookmarks.
If any of the bookmarks has no tag named TAG, then add one with VALUE."
  (interactive (list (bmkp-read-tag-completing) (read (read-string "Value: ")) 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (when msgp (message "Setting tag values..."))
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (when msgp (message "Setting tag values..."))
    (bmkp-set-tag-value-for-bookmarks marked tag value))
  (when (and msgp tag) (message "Setting tag values...done")))

;;;###autoload
(defun bmkp-bmenu-remove-tags (&optional msgp) ; Only on `mouse-3' menu in bookmark list.
  "Remove some tags from this bookmark."
  (interactive "p")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bmk  (bookmark-bmenu-bookmark)))
    (bmkp-remove-tags bmk
                      (bmkp-read-tags-completing (mapcar 'bmkp-full-tag (bmkp-get-tags bmk)) t)
                      msgp)))

;;;###autoload
(defun bmkp-bmenu-add-tags-to-marked (tags &optional msgp) ; Bound to `T > +' in bookmark list
  "Add TAGS to each of the marked bookmarks.
TAGS is a list of strings.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag, but you are not limited to
choosing existing tags."
  (interactive (list (bmkp-read-tags-completing) 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (when msgp (message "Adding tags..."))
    (dolist (bmk  (mapcar #'car marked)) (bmkp-add-tags bmk tags nil 'NO-CACHE-UPDATE)))
  (bmkp-tags-list)                      ; Update the tags cache (only once, at end).
  (when (and msgp tags) (message "Tags added: %S" tags)))

;;;###autoload
(defun bmkp-bmenu-remove-tags-from-marked (tags &optional msgp) ; Bound to `T > -' in bookmark list
  "Remove TAGS from each of the marked bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag."
  (interactive (let ((cand-tags  ()))
                 (dolist (bmk  (bmkp-marked-bookmarks-only))
                   (setq cand-tags  (bmkp-set-union cand-tags (bmkp-get-tags bmk))))
                 (unless cand-tags (error "No tags to remove"))
                 (list (bmkp-read-tags-completing cand-tags t) 'msg)))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (when msgp (message "Removing tags..."))
    (dolist (bmk  (mapcar #'car marked)) (bmkp-remove-tags bmk tags nil 'NO-CACHE-UPDATE)))
  (bmkp-tags-list)                      ; Update the tags cache (only once, at end).
  (when (and msgp tags) (message "Tags removed: %S" tags)))

;;;###autoload
(defun bmkp-bmenu-mark-bookmarks-tagged-regexp (regexp &optional notp) ; `T m %' in bookmark list
  "Mark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but have no matching tags."
  (interactive "sRegexp: \nP")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (let ((count  0)
          tags anyp)
      (while (not (eobp))
        (setq tags  (bmkp-get-tags (bookmark-bmenu-bookmark))
              anyp  (and tags (bmkp-some (lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                         tags)))
        (if (not (and tags (if notp (not anyp) anyp)))
            (forward-line 1)
          (bookmark-bmenu-mark)
          (setq count  (1+ count))))
      (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload
(defun bmkp-bmenu-mark-bookmarks-tagged-all (tags &optional none-p msgp) ; `T m *' in bookmark list
  "Mark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all (i.e., at least one tag).

With a prefix arg, mark all that are *not* tagged with *any* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags none-p nil msgp))

;;;###autoload
(defun bmkp-bmenu-mark-bookmarks-tagged-none (tags &optional allp msgp) ; `T m ~ +' in bookmark list
  "Mark all visible bookmarks that are not tagged with *any* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *each* tag in TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags (not allp) nil msgp))

;;;###autoload
(defun bmkp-bmenu-mark-bookmarks-tagged-some (tags &optional somenotp msgp) ; `T m +' in bookmark list
  "Mark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all.

With a prefix arg, mark all that are *not* tagged with *all* TAGS.

Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags somenotp nil msgp))

;;;###autoload
(defun bmkp-bmenu-mark-bookmarks-tagged-not-all (tags &optional somep msgp) ; `T m ~ *' in bmk list
  "Mark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *some* tag in TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags (not somep) nil msgp))

;;;###autoload
(defun bmkp-bmenu-unmark-bookmarks-tagged-regexp (regexp &optional notp) ; `T u %' in bookmark list
  "Unmark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but have no matching tags."
  (interactive "sRegexp: \nP")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
    (let ((count  0)
          tags anyp)
      (while (not (eobp))
        (setq tags  (bmkp-get-tags (bookmark-bmenu-bookmark))
              anyp  (and tags (bmkp-some (lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                         tags)))
        (if (not (and tags (if notp (not anyp) anyp)))
            (forward-line 1)
          (bookmark-bmenu-unmark)
          (setq count  (1+ count))))
      (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload
(defun bmkp-bmenu-unmark-bookmarks-tagged-all (tags &optional none-p msgp) ; `T u *' in bookmark list
  "Unmark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *any* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags none-p 'UNMARK msgp))

;;;###autoload
(defun bmkp-bmenu-unmark-bookmarks-tagged-none (tags &optional allp msgp) ; `T u ~ +' in bookmark list
  "Unmark all visible bookmarks that are *not* tagged with *any* TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
no tags at all.

With a prefix arg, unmark all that are tagged with *each* tag in TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags (not allp) 'UNMARK msgp))

;;;###autoload
(defun bmkp-bmenu-unmark-bookmarks-tagged-some (tags &optional somenotp msgp) ; `T u +' in bmk list
  "Unmark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *all* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags somenotp 'UNMARK msgp))

;;;###autoload
(defun bmkp-bmenu-unmark-bookmarks-tagged-not-all (tags &optional somep msgp) ; `T u ~ *' in bmk list
  "Unmark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
no tags at all.

With a prefix arg, unmark all that are tagged with *some* TAGS."
  (interactive (list (bmkp-read-tags-completing) current-prefix-arg 'msg))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags (not somep) 'UNMARK msgp))

(defun bmkp-bmenu-mark/unmark-bookmarks-tagged-all/none (tags &optional none-p unmarkp msgp)
  "Mark or unmark visible bookmarks tagged with all or none of TAGS.
TAGS is a list of strings, the tag names.
NONEP non-nil means mark/unmark bookmarks that have none of the TAGS.
UNMARKP non-nil means unmark; nil means mark.
MSGP means display a status message.

As a special case, if TAGS is empty, then mark or unmark the bookmarks
that have any tags at all, or if NONEP is non-nil then mark or unmark
those that have no tags at all."
  (with-current-buffer "*Bookmark List*"
    (save-excursion  
      (let ((count  0)
            bmktags presentp)
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (while (not (eobp))
          (setq bmktags  (bmkp-get-tags (bookmark-bmenu-bookmark)))
          (if (not (if (null tags)
                       (if none-p (not bmktags) bmktags)
                     (and bmktags  (catch 'bmkp-b-mu-b-t-an
                                     (dolist (tag  tags)
                                       (setq presentp  (assoc-default tag bmktags nil t))
                                       (unless (if none-p (not presentp) presentp)
                                         (throw 'bmkp-b-mu-b-t-an nil)))
                                     t))))
              (forward-line 1)
            (if unmarkp (bookmark-bmenu-unmark) (bookmark-bmenu-mark))
            (setq count  (1+ count))))
        (when msgp (if (= 1 count)
                       (message "1 bookmark matched")
                     (message "%d bookmarks matched" count)))))))

(defun bmkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all (tags &optional notallp unmarkp msgp)
  "Mark or unmark visible bookmarks tagged with any or not all of TAGS.
TAGS is a list of strings, the tag names.
NOTALLP non-nil means mark/unmark bookmarks that do not have all TAGS.
UNMARKP non-nil means unmark; nil means mark.
MSGP means display a status message.

As a special case, if TAGS is empty, then mark or unmark the bookmarks
that have any tags at all, or if NOTALLP is non-nil then mark or
unmark those that have no tags at all."
  (with-current-buffer "*Bookmark List*"
    (save-excursion  
      (let ((count  0)
            bmktags presentp)
        (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
        (while (not (eobp))
          (setq bmktags  (bmkp-get-tags (bookmark-bmenu-bookmark)))
          (if (not (if (null tags)
                       (if notallp (not bmktags) bmktags)
                     (and bmktags  (catch 'bmkp-b-mu-b-t-sna
                                     (dolist (tag  tags)
                                       (setq presentp  (assoc-default tag bmktags nil t))
                                       (when (if notallp (not presentp) presentp)
                                         (throw 'bmkp-b-mu-b-t-sna t)))
                                     nil))))
              (forward-line 1)
            (if unmarkp (bookmark-bmenu-unmark) (bookmark-bmenu-mark))
            (setq count  (1+ count))))
        (when msgp
          (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))))

;;;###autoload
(defun bmkp-bmenu-copy-tags (&optional msgp) ; `T c', `T M-w', `mouse-3' menu in bookmark list.
  "Copy tags from this bookmark, so you can paste them to another bookmark."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-copy-tags (bookmark-bmenu-bookmark) msgp))

;;;###autoload
(defun bmkp-bmenu-paste-add-tags (&optional msgp) ; `T p', `T C-y', `mouse-3' menu in bookmark list.
  "Add tags to this bookmark that were copied from another bookmark."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-paste-add-tags (bookmark-bmenu-bookmark) msgp))

;;;###autoload
(defun bmkp-bmenu-paste-replace-tags (&optional msgp) ; `T q', `mouse-3' menu.
  "Replace tags for this bookmark with those copied from another bookmark."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-paste-replace-tags (bookmark-bmenu-bookmark) msgp))

;;;###autoload
(defun bmkp-bmenu-paste-add-tags-to-marked (&optional msgp) ; `T > p', `T > C-y'
  "Add tags that were copied from another bookmark to the marked bookmarks."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (when msgp (message "Adding tags..."))
    (dolist (bmk  marked) (bmkp-paste-add-tags bmk nil 'NO-CACHE-UPDATE))
    (bmkp-tags-list)                    ; Update the tags cache (only once, at end).
    (when msgp (message "Tags added: %S" bmkp-copied-tags))))

;;;###autoload
(defun bmkp-bmenu-paste-replace-tags-for-marked (&optional msgp) ; `T > q'
  "Replace tags for the marked bookmarks with tags copied previously."
  (interactive (list 'MSG))
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let ((marked  (bmkp-marked-bookmarks-only)))
    (unless marked (error "No marked bookmarks"))
    (when msgp (message "Replacing tags..."))
    (dolist (bmk  marked) (bmkp-paste-replace-tags bmk nil 'NO-CACHE-UPDATE))
    (bmkp-tags-list)                    ; Update the tags cache (only once, at end).
    (when msgp (message "Replacement tags: %S" bmkp-copied-tags))))


;;(@* "General Menu-List (`-*bmenu-*') Commands and Functions")
;;  *** General Menu-List (`-*bmenu-*') Commands and Functions ***

;;;###autoload
(defun bmkp-bmenu-w32-open ()           ; Bound to `M-RET' in bookmark list.
  "Use `w32-browser' to open this bookmark."
  (interactive) (let ((bmkp-use-w32-browser-p  t))  (bookmark-bmenu-this-window)))

;;;###autoload
(defun bmkp-bmenu-w32-open-with-mouse (event) ; Bound to `M-mouse-2' in bookmark list.
  "Use `w32-browser' to open the bookmark clicked."
  (interactive "e")
  (save-excursion
    (with-current-buffer (window-buffer (posn-window (event-end event)))
      (save-excursion (goto-char (posn-point (event-end event)))
                      (let ((bmkp-use-w32-browser-p  t))  (bookmark-bmenu-other-window))))))

;;;###autoload
(defun bmkp-bmenu-w32-open-select ()    ; Bound to `M-o' in bookmark-list.
  "Use `w32-browser' to open this bookmark and all marked bookmarks."
  (interactive) (let ((bmkp-use-w32-browser-p  t))  (bookmark-bmenu-select)))

;;;###autoload
(defun bmkp-bmenu-mode-status-help ()   ; Bound to `C-h m' and `?' in bookmark list
  "`describe-mode' + current status of `*Bookmark List*' + face legend."
  (interactive)
  (unless (string= (buffer-name) "*Help*") (bmkp-bmenu-barf-if-not-in-menu-list))
  (with-current-buffer (get-buffer-create "*Help*")
    (with-output-to-temp-buffer "*Help*"
      (let ((buffer-read-only  nil)
            top)
        (erase-buffer)
        (save-excursion
          (let ((standard-output  (current-buffer)))
            (if (> emacs-major-version 21)
                (describe-function-1 'bookmark-bmenu-mode)
              (describe-function-1 'bookmark-bmenu-mode nil t)))
          (help-setup-xref (list #'bmkp-bmenu-mode-status-help) (interactive-p))
          (goto-char (point-min))
          ;; This text must be the same as the last line of `bookmark-bmenu-mode' doc string.
          (search-forward "Each line represents an Emacs bookmark.\n\n\n" nil t)
          (delete-region (point-min) (point)) ; Get rid of intro from `describe-function'.
          (insert "*************************** Bookmark List ***************************\n\n")
          (insert "Major mode for editing a list of bookmarks.\n")
          (insert "Each line represents an Emacs bookmark.\n\n")
          (setq top  (point))
          ;; Add buttons to access help and Customize.
          ;; Not for Emacs 21.3 - its `help-insert-xref-button' signature is different.
          (when (and (> emacs-major-version 21) ; In `help-mode.el'.
                     (condition-case nil (require 'help-mode nil t) (error nil))
                     (fboundp 'help-insert-xref-button))
            (help-insert-xref-button "[Doc in Commentary]" 'bmkp-commentary-button)
            (insert "           ")
            (help-insert-xref-button "[Doc on the Web]" 'bmkp-help-button)
            (insert "           ")
            (help-insert-xref-button "[Customize]" 'bmkp-customize-button)
            (insert "\n\n")
            (setq top  (point))
            (goto-char (point-max))
            (insert "\nSend a Bookmark+ bug report: `\\[icicle-send-bug-report]'.\n\n")
            (help-insert-xref-button "[Doc in Commentary]" 'bmkp-commentary-button)
            (insert "           ")
            (help-insert-xref-button "[Doc on the Web]" 'bmkp-help-button)
            (insert "           ")
            (help-insert-xref-button "[Customize]" 'bmkp-customize-button)
            (insert "\n\n")
            (goto-char (point-min))
            (forward-line 2))
          (goto-char top)
          (insert (format
                   "\nCurrent Status\n-------------------------------\n
Sorted:\t\t%s\nFiltering:\t%s\nMarked:\t\t%d\nOmitted:\t%d\nBookmark file:\t%s\n\n\n"
                   (if (not bmkp-sort-comparer)
                       "no"
                     (format "%s%s" (bmkp-current-sort-order)
                             ;; Code essentially the same as found in `bmkp-msg-about-sort-order'.
                             (if (not (and (consp bmkp-sort-comparer) ; Ordinary single predicate
                                           (consp (car bmkp-sort-comparer))))
                                 (if bmkp-reverse-sort-p "; reversed" "")
                               (if (not (cadr (car bmkp-sort-comparer)))
                                   ;; Single PRED.
                                   (if (or (and bmkp-reverse-sort-p (not bmkp-reverse-multi-sort-p))
                                           (and bmkp-reverse-multi-sort-p (not bmkp-reverse-sort-p)))
                                       "; reversed"
                                     "")
                                 ;; In case we want to distinguish:
                                 ;; (if (and bmkp-reverse-sort-p
                                 ;;          (not bmkp-reverse-multi-sort-p))
                                 ;;     "; reversed"
                                 ;;   (if (and bmkp-reverse-multi-sort-p
                                 ;;            (not bmkp-reverse-sort-p))
                                 ;;       "; reversed +"
                                 ;;     ""))
                                 
                                 ;; At least two PREDs.
                                 (cond ((and bmkp-reverse-sort-p (not bmkp-reverse-multi-sort-p))
                                        "; reversed")
                                       ((and bmkp-reverse-multi-sort-p (not bmkp-reverse-sort-p))
                                        "; each predicate group reversed")
                                       ((and bmkp-reverse-multi-sort-p bmkp-reverse-sort-p)
                                        "; order of predicate groups reversed")
                                       (t ""))))))
                   (or (and bmkp-bmenu-filter-function (downcase bmkp-bmenu-title)) "None")
                   (length bmkp-bmenu-marked-bookmarks)
                   (length bmkp-bmenu-omitted-bookmarks)
                   bmkp-current-bookmark-file))
          ;; Add face legend.
          (let ((gnus             "Gnus\n")
                (info             "Info node\n")
                (man              "Man page\n")
                (url              "URL\n")
                (local-no-region  "Local file with no region\n")
                (local-w-region   "Local file with a region\n")
                (buffer           "Buffer\n")
                (no-buf           "No current buffer\n")
                (bad              "Possibly invalid bookmark\n")
                (remote           "Remote file or directory\n")
                (sudo             "Remote accessed by `su' or `sudo'\n")
                (local-dir        "Local directory\n")
                (bookmark-list    "*Bookmark List*\n")
                (bookmark-file    "Bookmark file\n")
                (desktop          "Desktop\n")
                (sequence         "Sequence\n")
                (variable-list    "Variable list\n")
                (function         "Function\n"))
            (put-text-property 0 (1- (length gnus))     'face 'bmkp-gnus         gnus)
            (put-text-property 0 (1- (length info))     'face 'bmkp-info         info)
            (put-text-property 0 (1- (length man))      'face 'bmkp-man          man)
            (put-text-property 0 (1- (length url))      'face 'bmkp-url          url)
            (put-text-property 0 (1- (length local-no-region))
                               'face 'bmkp-local-file-without-region             local-no-region)
            (put-text-property 0 (1- (length local-w-region))
                               'face 'bmkp-local-file-with-region                local-w-region)
            (put-text-property 0 (1- (length buffer))   'face 'bmkp-buffer       buffer)
            (put-text-property 0 (1- (length no-buf))   'face 'bmkp-non-file     no-buf)
            (put-text-property 0 (1- (length bad))      'face 'bmkp-bad-bookmark bad)
            (put-text-property 0 (1- (length remote))   'face 'bmkp-remote-file  remote)
            (put-text-property 0 (1- (length sudo))     'face 'bmkp-su-or-sudo   sudo)
            (put-text-property 0 (1- (length local-dir))
                               'face 'bmkp-local-directory                       local-dir)
            (put-text-property 0 (1- (length bookmark-list))
                               'face 'bmkp-bookmark-list                         bookmark-list)
            (put-text-property 0 (1- (length bookmark-file))
                               'face 'bmkp-bookmark-file                         bookmark-file)
            (put-text-property 0 (1- (length desktop))       'face 'bmkp-desktop       desktop)
            (put-text-property 0 (1- (length sequence))      'face 'bmkp-sequence      sequence)
            (put-text-property 0 (1- (length variable-list)) 'face 'bmkp-variable-list variable-list)
            (put-text-property 0 (1- (length function))      'face 'bmkp-function      function)
            (insert "Face Legend for Bookmark Types\n------------------------------\n\n")
            (insert gnus) (insert info) (insert man) (insert url) (insert local-no-region)
            (insert local-w-region) (insert buffer) (insert no-buf) (insert bad) (insert remote)
            (insert sudo) (insert local-dir) (insert bookmark-list) (insert bookmark-file)
            (insert desktop) (insert sequence) (insert variable-list) (insert function)
            (insert "\n\n")))))))

(when (and (> emacs-major-version 21)
           (condition-case nil (require 'help-mode nil t) (error nil))
           (get 'help-xref 'button-category-symbol)) ; In `button.el'
  (define-button-type 'bmkp-help-button
      :supertype 'help-xref
      'help-function #'(lambda () (browse-url "http://www.emacswiki.org/emacs/BookmarkPlus"))
      'help-echo
      (purecopy "mouse-2, RET: Bookmark+ documentation on the Emacs Wiki (requires Internet access)"))
  (define-button-type 'bmkp-commentary-button
      :supertype 'help-xref
      'help-function #'(lambda ()
                         (message "Getting Bookmark+ doc from file commentary...")
                         (finder-commentary "bookmark+-doc")
                         (when (condition-case nil (require 'linkd nil t) (error nil)) (linkd-mode 1))
                         (when (condition-case nil (require 'fit-frame nil t) (error nil))
                           (fit-frame)))
      'help-echo (purecopy "mouse-2, RET: Bookmark+ documentation (no Internet needed)"))
  (define-button-type 'bmkp-customize-button
      :supertype 'help-xref
      'help-function #'(lambda () (customize-group-other-window 'bookmark-plus))
      'help-echo (purecopy "mouse-2, RET: Customize/Browse Bookmark+ Options & Faces")))

;;;###autoload
(defun bmkp-bmenu-define-jump-marked-command () ; Bound to `M-c' in bookmark list
  "Define a command to jump to a bookmark that is one of those now marked.
The bookmarks marked now will be those that are completion candidates
for the command (but omitted bookmarks are excluded).
Save the command definition in `bmkp-bmenu-commands-file'."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (let* ((cands  (mapcar #'list
                         (bmkp-remove-if #'(lambda (bmk)
                                             (bmkp-bookmark-name-member bmk
                                                                        bmkp-bmenu-omitted-bookmarks))
                                         bmkp-bmenu-marked-bookmarks)))
         (fn     (intern (read-string "Define command to jump to a bookmark now marked: " nil
                                      'bmkp-bmenu-define-command-history)))
         (def    `(defun ,fn (bookmark-name &optional use-region-p)
                   (interactive (list (bmkp-read-bookmark-for-type nil ',cands t) current-prefix-arg))
                   (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))))
    (eval def)
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bmkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (message "Command `%s' defined and saved in file `%s'" fn bmkp-bmenu-commands-file)))

;;;###autoload
(defun bmkp-bmenu-define-command ()     ; Bound to `c' in bookmark list
  "Define a command to use the current sort order, filter, and omit list.
Prompt for the command name.  Save the command definition in
`bmkp-bmenu-commands-file'.

The current sort order, filter function, omit list, and title for
buffer `*Bookmark List*' are encapsulated as part of the command.
Use the command at any time to restore them."
  (interactive)
  (let* ((fn   (intern (read-string "Define sort+filter command: " nil
                                    'bmkp-bmenu-define-command-history)))
         (def  `(defun ,fn ()
                 (interactive)
                 (setq
                  bmkp-sort-comparer               ',bmkp-sort-comparer
                  bmkp-reverse-sort-p              ',bmkp-reverse-sort-p
                  bmkp-reverse-multi-sort-p        ',bmkp-reverse-multi-sort-p
                  bmkp-bmenu-filter-function       ',bmkp-bmenu-filter-function
                  bmkp-bmenu-filter-pattern        ',bmkp-bmenu-filter-pattern
                  bmkp-bmenu-omitted-bookmarks     ',(bmkp-maybe-unpropertize-bookmark-names
                                                      bmkp-bmenu-omitted-bookmarks)
                  bmkp-bmenu-title                 ',bmkp-bmenu-title
                  bookmark-bmenu-toggle-filenames  ',bookmark-bmenu-toggle-filenames)
                 (bmkp-bmenu-refresh-menu-list)
                 (when (interactive-p)
                   (bmkp-msg-about-sort-order
                    (car (rassoc bmkp-sort-comparer bmkp-sort-orders-alist)))))))
    (eval def)
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bmkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (message "Command `%s' defined and saved in file `%s'" fn bmkp-bmenu-commands-file)))

;;;###autoload
(defun bmkp-bmenu-define-full-snapshot-command () ; Bound to `C' in bookmark list
  "Define a command to restore the current bookmark-list state.
Prompt for the command name.  Save the command definition in
`bmkp-bmenu-commands-file'.

Be aware that the command definition can be quite large, since it
copies the current bookmark list and accessory lists (hidden
bookmarks, marked bookmarks, etc.).  For a lighter weight command, use
`bmkp-bmenu-define-full-snapshot-command' instead.  That records only
the omit list and the sort & filter information."
  (interactive)
  (let* ((fn   (intern (read-string "Define restore-snapshot command: " nil
                                    'bmkp-bmenu-define-command-history)))
         (def  `(defun ,fn ()
                 (interactive)
                 (setq
                  bmkp-sort-comparer                     ',bmkp-sort-comparer
                  bmkp-reverse-sort-p                    ',bmkp-reverse-sort-p
                  bmkp-reverse-multi-sort-p              ',bmkp-reverse-multi-sort-p
                  bmkp-latest-bookmark-alist             ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-latest-bookmark-alist)
                  bmkp-bmenu-omitted-bookmarks           ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-omitted-bookmarks)
                  bmkp-bmenu-marked-bookmarks            ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-marked-bookmarks)
                  bmkp-bmenu-filter-function             ',bmkp-bmenu-filter-function
                  bmkp-bmenu-filter-pattern              ',bmkp-bmenu-filter-pattern
                  bmkp-bmenu-title                       ',bmkp-bmenu-title
                  bmkp-last-bmenu-bookmark               ',(and (get-buffer "*Bookmark List*")
                                                                (with-current-buffer
                                                                    (get-buffer "*Bookmark List*")
                                                                  (bookmark-bmenu-bookmark)))
                  bmkp-last-specific-buffer              ',bmkp-last-specific-buffer
                  bmkp-last-specific-file                ',bmkp-last-specific-file
                  bookmark-bmenu-toggle-filenames        ',bookmark-bmenu-toggle-filenames
                  bmkp-bmenu-before-hide-marked-alist    ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-before-hide-marked-alist)
                  bmkp-bmenu-before-hide-unmarked-alist  ',(bmkp-maybe-unpropertize-bookmark-names
                                                            bmkp-bmenu-before-hide-unmarked-alist)
                  bmkp-last-bookmark-file                ',bmkp-last-bookmark-file
                  bmkp-current-bookmark-file             ',bmkp-current-bookmark-file)
                 ;;(bmkp-bmenu-refresh-menu-list)
                 (let ((bookmark-alist  (or bmkp-latest-bookmark-alist bookmark-alist)))
                   (bmkp-bmenu-list-1 'filteredp nil (interactive-p)))
                 (when bmkp-last-bmenu-bookmark
                   (with-current-buffer (get-buffer "*Bookmark List*")
                     (bmkp-bmenu-goto-bookmark-named bmkp-last-bmenu-bookmark)))
                 (when (interactive-p)
                   (bmkp-msg-about-sort-order
                    (car (rassoc bmkp-sort-comparer bmkp-sort-orders-alist)))))))
    (eval def)
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil)
            (print-circle  t))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bmkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (message "Command `%s' defined and saved in file `%s'" fn bmkp-bmenu-commands-file)))

(defun bmkp-maybe-unpropertize-bookmark-names (list)
  "Strip properties from the bookmark names in a copy of LIST.
LIST is a bookmark alist or a list of bookmark names (strings).
Return the updated copy.

Note, however, that this is a shallow copy, so the names are also
stripped within any alist elements of the original LIST.

We do this because Emacs 20 has no `print-circle'. and otherwise
property `bmkp-full-record' would make the state file unreadable.

Do nothing in Emacs 21 or later or if
`bmkp-propertize-bookmark-names-flag' is nil.  In these cases, just
return the list."
  (if (and (> emacs-major-version 20)   ; Emacs 21+.  Cannot just use (boundp 'print-circle).
           bmkp-propertize-bookmark-names-flag)
      list
    (let ((new-list  (copy-sequence list)))
      (dolist (bmk  new-list)
        (when (and (consp bmk) (stringp (car bmk))) (setq bmk  (car bmk)))
        (when (stringp bmk) (set-text-properties 0 (length bmk) nil bmk)))
      new-list)))

;; This is a general command.  It is in this file because it uses macro `bmkp-define-sort-command'
;; and it is used mainly in the bookmark list display.
;;;###autoload
(defun bmkp-define-tags-sort-command (tags &optional msgp) ; Bound to `T s' in bookmark list
  "Define a command to sort bookmarks in the bookmark list by tags.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.

The new command sorts first by the first tag in TAGS, then by the
second, and so on.

Besides sorting for these specific tags, any bookmark that has a tag
sorts before one that has no tags.  Otherwise, sorting is by bookmark
name, alphabetically.

The name of the new command is `bmkp-bmenu-sort-' followed by the
specified tags, in order, separated by hyphens (`-').  E.g., for TAGS
\(\"alpha\" \"beta\"), the name is `bmkp-bmenu-sort-alpha-beta'."
  (interactive (list (bmkp-read-tags-completing) 'msg))
  (let ((sort-order  (concat "tags-" (mapconcat #'identity tags "-")))
        (doc-string  (read-string "Doc string for command: "))
        (comparer    ())
        def)
    (dolist (tag  tags)
      (push `(lambda (b1 b2)
              (let ((tags1  (bmkp-get-tags b1))
                    (tags2  (bmkp-get-tags b2)))
                (cond ((and (assoc-default ,tag tags1 nil t)
                            (assoc-default ,tag tags2 nil t))  nil)
                      ((assoc-default ,tag tags1 nil t)        '(t))
                      ((assoc-default ,tag tags2 nil t)        '(nil))
                      ((and tags1 tags2)                       nil)
                      (tags1                                   '(t))
                      (tags2                                   '(nil))
                      (t                                       nil))))
            comparer))
    (setq comparer  (nreverse comparer)
          comparer  (list comparer 'bmkp-alpha-p))
    (eval (setq def  (macroexpand `(bmkp-define-sort-command ,sort-order ,comparer ,doc-string))))
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bmkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bmkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (when msgp (message "Defined and saved command `%s'"
                        (concat "bmkp-bmenu-sort-" sort-order)))))

;;;###autoload
(defun bmkp-bmenu-edit-bookmark (&optional internalp) ; Bound to `E' in bookmark list
  "Edit the bookmark under the cursor: its name and file name.
With a prefix argument, edit the complete bookmark record (the
internal, Lisp form)."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bmk-name  (bookmark-bmenu-bookmark)))
    (if internalp
        (bmkp-edit-bookmark-record bmk-name)
      (let* ((new-data  (bmkp-edit-bookmark bmk-name))
             (new-name  (car new-data)))
        (if (not new-data)
            (message "No changes made")
          (bmkp-refresh-menu-list new-name))))))

;;;###autoload
(defun bmkp-bmenu-edit-tags ()          ; Bound to `T e' in bookmark list
  "Edit the tags of the bookmark under the cursor.
The edited value must be a list each of whose elements is either a
string or a cons whose key is a string."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bmkp-edit-tags (bookmark-bmenu-bookmark)))

(defun bmkp-bmenu-propertize-item (bookmark start end)
  "Propertize buffer from START to END, indicating bookmark types.
This propertizes the name of BOOKMARK.
Also give this region the property `bmkp-bookmark-name' with as value
the name of BOOKMARK as a propertized string.

The propertized string has property `bmkp-full-record' with value
BOOKMARK, which is the full bookmark record, with the string as its
car.

Return the propertized string (the bookmark name)."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let* ((bookmark-name  (bookmark-name-from-full-record bookmark))
         (buffp          (bmkp-get-buffer-name bookmark))

         (filep          (bookmark-get-filename bookmark))
         (sudop          (and filep  (boundp 'tramp-file-name-regexp)
                              (string-match tramp-file-name-regexp filep)
                              (string-match bmkp-su-or-sudo-regexp filep))))
    ;; Put the full bookmark itself on string `bookmark-name' as property `bmkp-full-record'.
    ;; Then put that string on the name in the buffer text as property `bmkp-bookmark-name'.
    (put-text-property 0 (length bookmark-name) 'bmkp-full-record bookmark bookmark-name)
    (put-text-property start end 'bmkp-bookmark-name bookmark-name)
    ;; Add faces, mouse face, and tooltips, to characterize the bookmark type.
    (add-text-properties
     start  end
     (cond ((bmkp-sequence-bookmark-p bookmark) ; Sequence bookmark
            (append (bmkp-face-prop 'bmkp-sequence)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke the bookmarks in this sequence")))
           ((bmkp-function-bookmark-p bookmark) ; Function bookmark
            (append (bmkp-face-prop 'bmkp-function)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke this function bookmark")))
           ((bmkp-variable-list-bookmark-p bookmark) ; Variable-list bookmark
            (append (bmkp-face-prop 'bmkp-variable-list)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke this variable-list bookmark")))
           ((bmkp-bookmark-list-bookmark-p bookmark) ; Bookmark-list bookmark
            (append (bmkp-face-prop 'bmkp-bookmark-list)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Invoke this bookmark-list bookmark")))
           ((bmkp-desktop-bookmark-p bookmark) ; Desktop bookmark
            (append (bmkp-face-prop 'bmkp-desktop)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this desktop bookmark")))
           ((bmkp-bookmark-file-bookmark-p bookmark) ; Bookmark-file bookmark
            (append (bmkp-face-prop 'bmkp-bookmark-file)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Load this bookmark's bookmark file")))
           ((bmkp-info-bookmark-p bookmark) ; Info bookmark
            (append (bmkp-face-prop 'bmkp-info)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this Info bookmark")))
           ((bmkp-man-bookmark-p bookmark) ; Man bookmark
            (append (bmkp-face-prop 'bmkp-man)
                    '(mouse-face highlight follow-link t
                      help-echo (format "mouse-2 Goto `man' page"))))
           ((bmkp-gnus-bookmark-p bookmark) ; Gnus bookmark
            (append (bmkp-face-prop 'bmkp-gnus)
                    '(mouse-face highlight follow-link t
                      help-echo "mouse-2: Jump to this Gnus bookmark")))
           ((bmkp-url-bookmark-p bookmark) ; URL bookmark
            (append (bmkp-face-prop 'bmkp-url)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to URL `%s'" ,filep))))
           ((and sudop (not (bmkp-root-or-sudo-logged-p))) ; Root/sudo not logged in
            (append (bmkp-face-prop 'bmkp-su-or-sudo)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) file `%s'" ,filep))))
           ;; Test for remoteness before any other tests of the file itself
           ;; (e.g. `file-exists-p'), so we don't prompt for a password etc.
           ((and filep (bmkp-file-remote-p filep) (not sudop)) ; Remote file (ssh, ftp)
            (append (bmkp-face-prop 'bmkp-remote-file)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) remote file `%s'" ,filep))))
           ((and filep (file-directory-p filep)) ; Local directory
            (append (bmkp-face-prop 'bmkp-local-directory)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Dired directory `%s'" ,filep))))
           ((and filep (file-exists-p filep) ; Local file with region
                 (bmkp-region-bookmark-p bookmark))
            (append (bmkp-face-prop 'bmkp-local-file-with-region)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Activate region in file `%s'" ,filep))))
           ((and filep (file-exists-p filep)) ; Local file without region
            (append (bmkp-face-prop 'bmkp-local-file-without-region)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) file `%s'" ,filep))))
           ((and buffp (get-buffer buffp) (equal filep bmkp-non-file-filename)) ; Buffer
            (append (bmkp-face-prop 'bmkp-buffer)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to buffer `%s'" ,buffp))))
           ((and buffp  (or (not filep) (equal filep bmkp-non-file-filename)
                            (not (file-exists-p filep)))) ; Buffer bookmark, but no buffer.
            (append (bmkp-face-prop 'bmkp-non-file)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to buffer `%s'" ,buffp))))
           (t (append (bmkp-face-prop 'bmkp-bad-bookmark)
                      `(mouse-face highlight follow-link t
                        help-echo (format "BAD BOOKMARK (maybe): `%s'" ,filep))))))
    bookmark-name))

;;;###autoload
(defun bmkp-bmenu-quit ()               ; Bound to `q' in bookmark list
  "Quit the bookmark list (aka \"menu list\").
If `bmkp-bmenu-state-file' is non-nil, then save the state, to be
restored the next time the bookmark list is shown.  Otherwise, reset
the internal lists that record menu-list markings."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if (not bmkp-bmenu-state-file)
      (setq bmkp-bmenu-marked-bookmarks            ()
            bmkp-bmenu-before-hide-marked-alist    ()
            bmkp-bmenu-before-hide-unmarked-alist  ())
    (bmkp-save-menu-list-state)
    (setq bmkp-bmenu-first-time-p  t))
  (quit-window))

(defun bmkp-bmenu-goto-bookmark-named (name)
  "Go to the first bookmark whose name matches NAME (a string).  
If NAME has non-nil property `bmkp-full-record' then go to the
bookmark it indicates.  Otherwise, just go to the first bookmark with
the same name."
  (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
  (let ((full  (get-text-property 0 'bmkp-full-record name)))
    (while (and (not (eobp))
                (not (if full
                         (equal full (get-text-property 0 'bmkp-full-record (bookmark-bmenu-bookmark)))
                       (equal name (bookmark-bmenu-bookmark)))))
      (forward-line 1)))
  (bookmark-bmenu-ensure-position))     ; Just in case we fall off the end.

;; This is a general function.  It is in this file because it is used only by the bmenu code.
(defun bmkp-bmenu-barf-if-not-in-menu-list ()
  "Raise an error if current buffer is not `*Bookmark List*'."
  (unless (equal (buffer-name (current-buffer)) "*Bookmark List*")
    (error "You can only use this command in buffer `*Bookmark List*'")))


;;(@* "Sorting - Commands")
;;  *** Sorting - Commands ***

;;;###autoload
(defun bmkp-bmenu-change-sort-order-repeat (arg) ; Bound to `s s'... in bookmark list
  "Cycle to the next sort order.
With a prefix arg, reverse current sort order.
This is a repeatable version of `bmkp-bmenu-change-sort-order'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-bmenu-change-sort-order))

;;;###autoload
(defun bmkp-bmenu-change-sort-order (&optional arg)
  "Cycle to the next sort order.
With a prefix arg, reverse the current sort order."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-sort-orders-for-cycling-alist  (delq nil bmkp-sort-orders-for-cycling-alist))
  (if arg
      (bmkp-reverse-sort-order)
    (let ((current-bmk  (bookmark-bmenu-bookmark))
          next-order)
      (let ((orders  (mapcar #'car bmkp-sort-orders-for-cycling-alist)))
        (setq next-order          (or (cadr (member (bmkp-current-sort-order) orders))  (car orders))
              bmkp-sort-comparer  (cdr (assoc next-order bmkp-sort-orders-for-cycling-alist))))
      (message "Sorting...")
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (when current-bmk                 ; Put cursor back on the right line.
        (bmkp-bmenu-goto-bookmark-named current-bmk))
      (when (interactive-p) (bmkp-msg-about-sort-order next-order)))))

;; This is a general command.  It is in this file because it is used only by the bmenu code.
;;;###autoload
(defun bmkp-reverse-sort-order ()       ; Bound to `s r' in bookmark list
  "Reverse the current bookmark sort order.
If you combine this with \\<bookmark-bmenu-mode-map>\
`\\[bmkp-reverse-multi-sort-order]', then see the doc for that command."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-reverse-sort-p  (not bmkp-reverse-sort-p))
  (let ((current-bmk  (bookmark-bmenu-bookmark)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (when current-bmk                   ; Put cursor back on the right line.
      (bmkp-bmenu-goto-bookmark-named current-bmk)))
  (when (interactive-p) (bmkp-msg-about-sort-order (bmkp-current-sort-order))))

;; This is a general command.  It is in this file because it is used only by the bmenu code.
;;;###autoload
(defun bmkp-reverse-multi-sort-order () ; Bound to `s C-r' in bookmark list
  "Reverse the application of multi-sorting predicates.
These are the PRED predicates described for option
`bmkp-sort-comparer'.

This reverses the order in which the predicates are tried, and it
also complements the truth value returned by each predicate.

For example, if the list of multi-sorting predicates is (p1 p2 p3),
then the predicates are tried in the order: p3, p2, p1.  And if a
predicate returns true, `(t)', then the effect is as if it returned
false, `(nil)', and vice versa.

The use of multi-sorting predicates tends to group bookmarks, with the
first predicate corresponding to the first bookmark group etc.

The effect of \\<bookmark-bmenu-mode-map>`\\[bmkp-reverse-multi-sort-order]' is \
roughly as follows:

 - without also `\\[bmkp-reverse-sort-order]', it reverses the bookmark order in each \
group

 - combined with `\\[bmkp-reverse-sort-order]', it reverses the order of the bookmark
   groups, but not the bookmarks within a group

This is a rough description.  The actual behavior can be complex,
because of how each predicate is defined.  If this description helps
you, fine.  If not, just experiment and see what happens. \;-)

Remember that ordinary `\\[bmkp-reverse-sort-order]' reversal on its own is \
straightforward.
If you find `\\[bmkp-reverse-multi-sort-order]' confusing or not helpful, then do not \
use it."
  (interactive)
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (setq bmkp-reverse-multi-sort-p  (not bmkp-reverse-multi-sort-p))
  (let ((current-bmk  (bookmark-bmenu-bookmark)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (when current-bmk                   ; Put cursor back on the right line.
      (bmkp-bmenu-goto-bookmark-named current-bmk)))
  (when (interactive-p) (bmkp-msg-about-sort-order (bmkp-current-sort-order))))



;; The ORDER of the macro calls here defines the REVERSE ORDER of
;; `bmkp-sort-orders-alist'.  The first here is thus also the DEFAULT sort order.
;; Entries are traversed by `s s'..., in `bmkp-sort-orders-alist' order.

(bmkp-define-sort-command               ; Bound to `s k' in bookmark list (`k' for "kind")
 "by bookmark type"                     ; `bmkp-bmenu-sort-by-bookmark-type'
 ((bmkp-info-cp bmkp-url-cp bmkp-gnus-cp bmkp-local-file-type-cp bmkp-handler-cp)
  bmkp-alpha-p)
 "Sort bookmarks by type: Info, URL, Gnus, files, other.")

(bmkp-define-sort-command               ; Bound to `s u' in bookmark list
 "by url"                           ; `bmkp-bmenu-sort-by-url'
 ((bmkp-url-cp) bmkp-alpha-p)
 "Sort URL bookmarks alphabetically by their URL/filename.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

;; $$$$$$ Not used now.
;; (bmkp-define-sort-command               ; Bound to `s w' in bookmark list
;;  "by w3m url"                           ; `bmkp-bmenu-sort-by-w3m-url'
;;  ((bmkp-w3m-cp) bmkp-alpha-p)
;;  "Sort W3M bookmarks alphabetically by their URL/filename.
;; When two bookmarks are not comparable this way, compare them by
;; bookmark name.")

(bmkp-define-sort-command               ; Bound to `s g' in bookmark list
 "by Gnus thread"                       ; `bmkp-bmenu-sort-by-Gnus-thread'
 ((bmkp-gnus-cp) bmkp-alpha-p)
 "Sort Gnus bookmarks by group, then by article, then by message.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s i' in bookmark list
 "by Info location"                     ; `bmkp-bmenu-sort-by-Info-location'
 ((bmkp-info-cp) bmkp-alpha-p)
 "Sort Info bookmarks by file name, then node name, then position.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f u' in bookmark list
 "by last local file update"            ; `bmkp-bmenu-sort-by-last-local-file-update'
 ((bmkp-local-file-updated-more-recently-cp) bmkp-alpha-p)
 "Sort bookmarks by last local file update time.
Sort a local file before a remote file, and a remote file before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f t' in bookmark list
 "by last local file access"            ; `bmkp-bmenu-sort-by-last-local-file-access'
 ((bmkp-local-file-accessed-more-recently-cp) bmkp-alpha-p)
 "Sort bookmarks by last local file access time.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f s' in bookmark list
 "by local file size"                   ; `bmkp-bmenu-sort-by-local-file-size'
 ((bmkp-local-file-size-cp) bmkp-alpha-p)
 "Sort bookmarks by local file size.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f n' in bookmark list
 "by file name"                         ; `bmkp-bmenu-sort-by-file-name'
 ((bmkp-file-alpha-cp) bmkp-alpha-p)
 "Sort bookmarks by file name.
When two bookmarks are not comparable by file name, compare them by
bookmark name.")

(bmkp-define-sort-command               ; Bound to `s f d' in bookmark list (`d' for "directory")
 "by local file type"                   ; `bmkp-bmenu-sort-by-local-file-type'
 ((bmkp-local-file-type-cp) bmkp-alpha-p)
 "Sort bookmarks by local file type: file, symlink, directory.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s >' in bookmark list
 "marked before unmarked"               ; `bmkp-bmenu-sort-marked-before-unmarked'
 ((bmkp-marked-cp) bmkp-alpha-p)
 "Sort bookmarks by putting marked before unmarked.
Otherwise alphabetize by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s b' in bookmark list
 "by last buffer or file access"        ; `bmkp-bmenu-sort-by-last-buffer-or-file-access'
 ((bmkp-buffer-last-access-cp bmkp-local-file-accessed-more-recently-cp)
  bmkp-alpha-p)
 "Sort bookmarks by last buffer access or last local file access.
Sort a bookmark accessed more recently before one accessed less
recently or not accessed.  Sort a bookmark to an existing buffer
before a local file bookmark.  When two bookmarks are not comparable
by such critera, sort them by bookmark name.  (In particular, sort
remote-file bookmarks by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s v' in bookmark list
 "by bookmark visit frequency"          ; `bmkp-bmenu-sort-by-bookmark-visit-frequency'
 ((bmkp-visited-more-cp) bmkp-alpha-p)
 "Sort bookmarks by the number of times they were visited as bookmarks.
When two bookmarks are not comparable by visit frequency, compare them
by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s t' in bookmark list
 "by last bookmark access"              ; `bmkp-bmenu-sort-by-last-bookmark-access'
 ((bmkp-bookmark-last-access-cp) bmkp-alpha-p)
 "Sort bookmarks by the time of their last visit as bookmarks.
When two bookmarks are not comparable by visit time, compare them
by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s 0' in bookmark list
 "by creation time"                     ; `bmkp-bmenu-sort-by-creation-time'
 ((bmkp-bookmark-creation-cp) bmkp-alpha-p)
 "Sort bookmarks by the time of their creation.
When one or both of the bookmarks does not have a `created' entry),
compare them by bookmark name.")

(bmkp-define-sort-command               ; Bound to `s n' in bookmark list
 "by bookmark name"                     ; `bmkp-bmenu-sort-by-bookmark-name'
 bmkp-alpha-p
 "Sort bookmarks by bookmark name, respecting `case-fold-search'.")

;; This is a general option.  It is in this file because it is used mainly by the bmenu code.
;; Its definitions MUST COME AFTER the calls to macro `bmkp-define-sort-command'.
;; Otherwise, they won't pick up a populated `bmkp-sort-orders-alist'.
(when (> emacs-major-version 20)
  (defcustom bmkp-sort-orders-for-cycling-alist (copy-sequence bmkp-sort-orders-alist)
    "*Alist of sort orders used for cycling via `s s'...
This is a subset of the complete list of available sort orders,
`bmkp-sort-orders-alist'.  This lets you cycle among fewer sort
orders, if there are some that you do not use often.

See the doc for `bmkp-sort-orders-alist', for the structure of
this value."
    :type '(alist
            :key-type (choice :tag "Sort order" string symbol)
            :value-type (choice
                         (const :tag "None (do not sort)" nil)
                         (function :tag "Sorting Predicate")
                         (list :tag "Sorting Multi-Predicate"
                          (repeat (function :tag "Component Predicate"))
                          (choice
                           (const :tag "None" nil)
                           (function :tag "Final Predicate")))))
    :group 'bookmark-plus))

(unless (> emacs-major-version 20)      ; Emacs 20: custom type `alist' doesn't exist.
  (defcustom bmkp-sort-orders-for-cycling-alist (copy-sequence bmkp-sort-orders-alist)
    "*Alist of sort orders used for cycling via `s s'...
This is a subset of the complete list of available sort orders,
`bmkp-sort-orders-alist'.  This lets you cycle among fewer sort
orders, if there are some that you do not use often.

See the doc for `bmkp-sort-orders-alist', for the structure of this
value."
    :type '(repeat
            (cons
             (choice :tag "Sort order" string symbol)
             (choice
              (const :tag "None (do not sort)" nil)
              (function :tag "Sorting Predicate")
              (list :tag "Sorting Multi-Predicate"
               (repeat (function :tag "Component Predicate"))
               (choice
                (const :tag "None" nil)
                (function :tag "Final Predicate"))))))
    :group 'bookmark-plus))


;;(@* "Other Bookmark+ Functions (`bmkp-*')")
;;  *** Other Bookmark+ Functions (`bmkp-*') ***

;;;###autoload
(defun bmkp-bmenu-describe-this+move-down (&optional defn) ; Bound to `C-down' in bookmark list
  "Describe bookmark of current line, then move down to the next bookmark.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bmkp-bmenu-describe-this-bookmark) (forward-line 1))

;;;###autoload
(defun bmkp-bmenu-describe-this+move-up (&optional defn) ; Bound to `C-up' in bookmark list
  "Describe bookmark of current line, then move down to the next bookmark.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bmkp-bmenu-describe-this-bookmark) (forward-line -1))

;;;###autoload
(defun bmkp-bmenu-describe-this-bookmark (&optional defn) ; Bound to `C-h RET' in bookmark list
  "Describe bookmark of current line.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (if defn
      (bmkp-describe-bookmark-internals (bookmark-bmenu-bookmark))
    (bmkp-describe-bookmark (bookmark-bmenu-bookmark))))

;;;###autoload
(defun bmkp-bmenu-describe-marked (&optional defn) ; Bound to `C-h >' in bookmark list
  "Describe the marked bookmarks.
With a prefix argument, show the internal definitions."
  (interactive "P")
  (bmkp-bmenu-barf-if-not-in-menu-list)
  (help-setup-xref (list #'bmkp-describe-bookmark-marked) (interactive-p))
  (with-output-to-temp-buffer "*Help*"
    (dolist (bmk  (bmkp-marked-bookmarks-only))
      (if defn
          (let* ((bname      (bookmark-name-from-full-record bmk))
                 (help-text  (format "%s\n%s\n\n%s" bname (make-string (length bname) ?-)
                                     (pp-to-string bmk))))
            (princ help-text) (terpri))
        (princ (bmkp-bookmark-description bmk)) (terpri)))))

(defun bmkp-bmenu-get-marked-files ()
  "Return a list of the file names of the marked bookmarks.
Marked bookmarks that have no associated file are ignored."
  (let ((files  ()))
    (dolist (bmk  bmkp-bmenu-marked-bookmarks)
      (when (bmkp-file-bookmark-p bmk) (push (bookmark-get-filename bmk) files)))
    files))
 
;;(@* "Keymaps")
;;; Keymaps ----------------------------------------------------------

;; `bookmark-bmenu-mode-map'

(when (< emacs-major-version 21)
  (define-key bookmark-bmenu-mode-map (kbd "RET")          'bookmark-bmenu-this-window))
(define-key bookmark-bmenu-mode-map "."                    'bmkp-bmenu-show-all)
(define-key bookmark-bmenu-mode-map ">"                    'bmkp-bmenu-toggle-show-only-marked)
(define-key bookmark-bmenu-mode-map "<"                    'bmkp-bmenu-toggle-show-only-unmarked)
(define-key bookmark-bmenu-mode-map (kbd "M-<DEL>")        'bmkp-bmenu-unmark-all)
(define-key bookmark-bmenu-mode-map "="                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "=bM"                  'bmkp-bmenu-mark-specific-buffer-bookmarks)
(define-key bookmark-bmenu-mode-map "=fM"                  'bmkp-bmenu-mark-specific-file-bookmarks)
(define-key bookmark-bmenu-mode-map "=bS"                  'bmkp-bmenu-show-only-specific-buffer)
(define-key bookmark-bmenu-mode-map "=fS"                  'bmkp-bmenu-show-only-specific-file)
(define-key bookmark-bmenu-mode-map "%"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "%m"                   'bmkp-bmenu-regexp-mark)
(define-key bookmark-bmenu-mode-map "*"                    nil) ; For Emacs 20
(when (< emacs-major-version 21)
  (define-key bookmark-bmenu-mode-map "*m"                 'bookmark-bmenu-mark))
(define-key bookmark-bmenu-mode-map "#"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "#S"                   'bmkp-bmenu-show-only-autonamed)
;; `A' is `bookmark-bmenu-show-all-annotations' in vanilla Emacs.
(define-key bookmark-bmenu-mode-map "\M-a"                 'bookmark-bmenu-show-all-annotations)
(define-key bookmark-bmenu-mode-map "A"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "AM"                   'bmkp-bmenu-mark-autofile-bookmarks)
(define-key bookmark-bmenu-mode-map "AS"                   'bmkp-bmenu-show-only-autofiles)
(define-key bookmark-bmenu-mode-map "B"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "BM"                   'bmkp-bmenu-mark-non-file-bookmarks)
(define-key bookmark-bmenu-mode-map "BS"                   'bmkp-bmenu-show-only-non-files)
(define-key bookmark-bmenu-mode-map "c"                    'bmkp-bmenu-define-command)
(define-key bookmark-bmenu-mode-map "C"                    'bmkp-bmenu-define-full-snapshot-command)
(define-key bookmark-bmenu-mode-map "\M-c"                 'bmkp-bmenu-define-jump-marked-command)
(define-key bookmark-bmenu-mode-map "D"                    'bmkp-bmenu-delete-marked)
(define-key bookmark-bmenu-mode-map "\M-d"                 nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "\M-d>"                'bmkp-bmenu-dired-marked)
(define-key bookmark-bmenu-mode-map "\M-d\M-m"             'bmkp-bmenu-mark-dired-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-d\M-s"             'bmkp-bmenu-show-only-dired)
(define-key bookmark-bmenu-mode-map "E"                    'bmkp-bmenu-edit-bookmark)
(define-key bookmark-bmenu-mode-map "F"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "FM"                   'bmkp-bmenu-mark-file-bookmarks)
(define-key bookmark-bmenu-mode-map "FS"                   'bmkp-bmenu-show-only-files)
(define-key bookmark-bmenu-mode-map "g"                    'bmkp-bmenu-refresh-menu-list)
(define-key bookmark-bmenu-mode-map "G"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "GM"                   'bmkp-bmenu-mark-gnus-bookmarks)
(define-key bookmark-bmenu-mode-map "GS"                   'bmkp-bmenu-show-only-gnus)
(if (fboundp 'command-remapping)
    (define-key bookmark-bmenu-mode-map [remap describe-mode] 'bmkp-bmenu-mode-status-help)
  ;; In Emacs < 22, the `substitute-...' affects only `?', not `C-h m', so we add it separately.
  (substitute-key-definition 'describe-mode 'bmkp-bmenu-mode-status-help bookmark-bmenu-mode-map)
  (define-key bookmark-bmenu-mode-map "\C-hm"              'bmkp-bmenu-mode-status-help))
(define-key bookmark-bmenu-mode-map (kbd "C-h >")          'bmkp-bmenu-describe-marked)
(define-key bookmark-bmenu-mode-map (kbd "C-h RET")        'bmkp-bmenu-describe-this-bookmark)
(define-key bookmark-bmenu-mode-map (kbd "C-h C-<return>") 'bmkp-bmenu-describe-this-bookmark)
(define-key bookmark-bmenu-mode-map (kbd "C-<down>")       'bmkp-bmenu-describe-this+move-down)
(define-key bookmark-bmenu-mode-map (kbd "C-<up>")         'bmkp-bmenu-describe-this+move-up)
(define-key bookmark-bmenu-mode-map (kbd "M-<return>")     'bmkp-bmenu-w32-open)
(define-key bookmark-bmenu-mode-map [M-mouse-2]            'bmkp-bmenu-w32-open-with-mouse)
(when (featurep 'bookmark+-lit)
  (define-key bookmark-bmenu-mode-map "H"                  nil) ; For Emacs 20
  (define-key bookmark-bmenu-mode-map "H+"                 'bmkp-bmenu-set-lighting)
  (define-key bookmark-bmenu-mode-map "H>+"                'bmkp-bmenu-set-lighting-for-marked)
  (define-key bookmark-bmenu-mode-map "H>H"                'bmkp-bmenu-light-marked)
  (define-key bookmark-bmenu-mode-map "HH"                 'bmkp-bmenu-light)
  (define-key bookmark-bmenu-mode-map "HM"                 'bmkp-bmenu-mark-lighted-bookmarks)
  (define-key bookmark-bmenu-mode-map "HS"                 'bmkp-bmenu-show-only-lighted)
  (define-key bookmark-bmenu-mode-map "H>U"                'bmkp-bmenu-unlight-marked)
  (define-key bookmark-bmenu-mode-map "HU"                 'bmkp-bmenu-unlight))
(define-key bookmark-bmenu-mode-map "I"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "IM"                   'bmkp-bmenu-mark-info-bookmarks)
(define-key bookmark-bmenu-mode-map "IS"                   'bmkp-bmenu-show-only-info-nodes)
(define-key bookmark-bmenu-mode-map "K"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "KM"                   'bmkp-bmenu-mark-desktop-bookmarks)
(define-key bookmark-bmenu-mode-map "KS"                   'bmkp-bmenu-show-only-desktops)
(define-key bookmark-bmenu-mode-map "L"                    'bmkp-switch-bookmark-file)
(define-key bookmark-bmenu-mode-map "M"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "MM"                   'bmkp-bmenu-mark-man-bookmarks)
(define-key bookmark-bmenu-mode-map "MS"                   'bmkp-bmenu-show-only-man-pages)
(define-key bookmark-bmenu-mode-map "\M-m"                 'bmkp-bmenu-mark-all)
(define-key bookmark-bmenu-mode-map "O"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "O>"                   'bmkp-bmenu-omit/unomit-marked)
(define-key bookmark-bmenu-mode-map "OS"                   'bmkp-bmenu-show-only-omitted)
(define-key bookmark-bmenu-mode-map "OU"                   'bmkp-unomit-all)
(define-key bookmark-bmenu-mode-map "P"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "PA"                  'bmkp-bmenu-filter-annotation-incrementally)
(define-key bookmark-bmenu-mode-map "PB"               'bmkp-bmenu-filter-bookmark-name-incrementally)
(define-key bookmark-bmenu-mode-map "PF"                   'bmkp-bmenu-filter-file-name-incrementally)
(define-key bookmark-bmenu-mode-map "PT"                   'bmkp-bmenu-filter-tags-incrementally)
(define-key bookmark-bmenu-mode-map "q"                    'bmkp-bmenu-quit)
(define-key bookmark-bmenu-mode-map "\M-q"          'bmkp-bmenu-query-replace-marked-bookmarks-regexp)
(define-key bookmark-bmenu-mode-map "R"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "RM"                   'bmkp-bmenu-mark-region-bookmarks)
(define-key bookmark-bmenu-mode-map "RS"                   'bmkp-bmenu-show-only-regions)
(define-key bookmark-bmenu-mode-map "\M-r"                 'bookmark-bmenu-relocate) ; `R' in Emacs
(define-key bookmark-bmenu-mode-map "S"                    'bookmark-bmenu-save) ; `s' in Emacs
(define-key bookmark-bmenu-mode-map "s"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "s>"                   'bmkp-bmenu-sort-marked-before-unmarked)
(define-key bookmark-bmenu-mode-map "s0"                   'bmkp-bmenu-sort-by-creation-time)
(define-key bookmark-bmenu-mode-map "sb"               'bmkp-bmenu-sort-by-last-buffer-or-file-access)
(define-key bookmark-bmenu-mode-map "sfd"                  'bmkp-bmenu-sort-by-local-file-type)
(define-key bookmark-bmenu-mode-map "sfn"                  'bmkp-bmenu-sort-by-file-name)
(define-key bookmark-bmenu-mode-map "sfs"                  'bmkp-bmenu-sort-by-local-file-size)
(define-key bookmark-bmenu-mode-map "sft"                  'bmkp-bmenu-sort-by-last-local-file-access)
(define-key bookmark-bmenu-mode-map "sfu"                  'bmkp-bmenu-sort-by-last-local-file-update)
(define-key bookmark-bmenu-mode-map "sg"                   'bmkp-bmenu-sort-by-Gnus-thread)
(define-key bookmark-bmenu-mode-map "si"                   'bmkp-bmenu-sort-by-Info-location)
(define-key bookmark-bmenu-mode-map "sk"                   'bmkp-bmenu-sort-by-bookmark-type)
(define-key bookmark-bmenu-mode-map "sn"                   'bmkp-bmenu-sort-by-bookmark-name)
(define-key bookmark-bmenu-mode-map "sr"                   'bmkp-reverse-sort-order)
(define-key bookmark-bmenu-mode-map "s\C-r"                'bmkp-reverse-multi-sort-order)
(define-key bookmark-bmenu-mode-map "ss"                   'bmkp-bmenu-change-sort-order-repeat)
(define-key bookmark-bmenu-mode-map "st"                   'bmkp-bmenu-sort-by-last-bookmark-access)
(define-key bookmark-bmenu-mode-map "su"                   'bmkp-bmenu-sort-by-url)
(define-key bookmark-bmenu-mode-map "sv"                 'bmkp-bmenu-sort-by-bookmark-visit-frequency)
;; ;; (define-key bookmark-bmenu-mode-map "sw"                   'bmkp-bmenu-sort-by-w3m-url)
(when (> emacs-major-version 22)        ; Emacs 23+
 (define-key bookmark-bmenu-mode-map (kbd "M-s a C-s")     'bmkp-bmenu-isearch-marked-bookmarks)
 (define-key bookmark-bmenu-mode-map (kbd "M-s a M-C-s") 'bmkp-bmenu-isearch-marked-bookmarks-regexp))
(define-key bookmark-bmenu-mode-map (kbd "M-s a M-s")      'bmkp-bmenu-search-marked-bookmarks-regexp)
(define-key bookmark-bmenu-mode-map "T"                    nil) ; For Emacs20
(define-key bookmark-bmenu-mode-map "T>+"                  'bmkp-bmenu-add-tags-to-marked)
(define-key bookmark-bmenu-mode-map "T>-"                  'bmkp-bmenu-remove-tags-from-marked)
(define-key bookmark-bmenu-mode-map "T>p"                  'bmkp-bmenu-paste-add-tags-to-marked)
(define-key bookmark-bmenu-mode-map "T>q"                  'bmkp-bmenu-paste-replace-tags-for-marked)
(define-key bookmark-bmenu-mode-map "T>v"                  'bmkp-bmenu-set-tag-value-for-marked)
(define-key bookmark-bmenu-mode-map "T>\C-y"               'bmkp-bmenu-paste-add-tags-to-marked)
(define-key bookmark-bmenu-mode-map "T0"                   'bmkp-remove-all-tags)
(define-key bookmark-bmenu-mode-map "T+"                   'bmkp-add-tags)
(define-key bookmark-bmenu-mode-map "T-"                   'bmkp-remove-tags)
(define-key bookmark-bmenu-mode-map "Tc"                   'bmkp-bmenu-copy-tags)
(define-key bookmark-bmenu-mode-map "Td"                   'bmkp-remove-tags-from-all)
(define-key bookmark-bmenu-mode-map "Te"                   'bmkp-bmenu-edit-tags)
(define-key bookmark-bmenu-mode-map "Tl"                   'bmkp-list-all-tags)
(define-key bookmark-bmenu-mode-map "Tm*"                  'bmkp-bmenu-mark-bookmarks-tagged-all)
(define-key bookmark-bmenu-mode-map "Tm%"                  'bmkp-bmenu-mark-bookmarks-tagged-regexp)
(define-key bookmark-bmenu-mode-map "Tm+"                  'bmkp-bmenu-mark-bookmarks-tagged-some)
(define-key bookmark-bmenu-mode-map "Tm~*"                 'bmkp-bmenu-mark-bookmarks-tagged-not-all)
(define-key bookmark-bmenu-mode-map "Tm~+"                 'bmkp-bmenu-mark-bookmarks-tagged-none)
(define-key bookmark-bmenu-mode-map "Tp"                   'bmkp-bmenu-paste-add-tags)
(define-key bookmark-bmenu-mode-map "Tq"                   'bmkp-bmenu-paste-replace-tags)
(define-key bookmark-bmenu-mode-map "Tr"                   'bmkp-rename-tag)
(define-key bookmark-bmenu-mode-map "Ts"                   'bmkp-define-tags-sort-command)
(define-key bookmark-bmenu-mode-map "TS"                   'bmkp-bmenu-show-only-tagged)
(define-key bookmark-bmenu-mode-map "Tu*"                  'bmkp-bmenu-unmark-bookmarks-tagged-all)
(define-key bookmark-bmenu-mode-map "Tu%"                  'bmkp-bmenu-unmark-bookmarks-tagged-regexp)
(define-key bookmark-bmenu-mode-map "Tu+"                  'bmkp-bmenu-unmark-bookmarks-tagged-some)
(define-key bookmark-bmenu-mode-map "Tu~*"                'bmkp-bmenu-unmark-bookmarks-tagged-not-all)
(define-key bookmark-bmenu-mode-map "Tu~+"                 'bmkp-bmenu-unmark-bookmarks-tagged-none)
(define-key bookmark-bmenu-mode-map "Tv"                   'bmkp-bmenu-set-tag-value)
(define-key bookmark-bmenu-mode-map "T\M-w"                'bmkp-bmenu-copy-tags)
(define-key bookmark-bmenu-mode-map "T\C-y"                'bmkp-bmenu-paste-add-tags)
(define-key bookmark-bmenu-mode-map "\M-l"                 'bmkp-toggle-saving-menu-list-state)
(define-key bookmark-bmenu-mode-map "\M-~"                 'bmkp-toggle-saving-bookmark-file)
(define-key bookmark-bmenu-mode-map "\M-t"            'bookmark-bmenu-toggle-filenames) ; `t' in Emacs
(define-key bookmark-bmenu-mode-map "t"                    'bmkp-bmenu-toggle-marks)
(define-key bookmark-bmenu-mode-map "U"                    'bmkp-bmenu-unmark-all)
(define-key bookmark-bmenu-mode-map "\M-u"                 nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "\M-u\M-m"             'bmkp-bmenu-mark-url-bookmarks)
(define-key bookmark-bmenu-mode-map "\M-u\M-s"             'bmkp-bmenu-show-only-urls)
(define-key bookmark-bmenu-mode-map "V"                    nil) ; For Emacs20
(define-key bookmark-bmenu-mode-map "VS"                   'bmkp-bmenu-show-only-variable-lists)
(define-key bookmark-bmenu-mode-map "\M-o"                 'bmkp-bmenu-w32-open-select)
(define-key bookmark-bmenu-mode-map "W"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "WM"                   'bmkp-bmenu-mark-w3m-bookmarks)
(define-key bookmark-bmenu-mode-map "WS"                   'bmkp-bmenu-show-only-w3m-urls)
(define-key bookmark-bmenu-mode-map "X"                    nil) ; For Emacs 20
(define-key bookmark-bmenu-mode-map "XM"                   'bmkp-bmenu-mark-bookmark-file-bookmarks)
(define-key bookmark-bmenu-mode-map "XS"                   'bmkp-bmenu-show-only-bookmark-files)


;;; `Bookmark+' menu-bar menu in `*Bookmark List*'

(defvar bmkp-bmenu-menubar-menu (make-sparse-keymap "Bookmark+") "`Boomark+' menu-bar menu.")
(define-key bookmark-bmenu-mode-map [menu-bar bmkp]
  (cons "Bookmark+" bmkp-bmenu-menubar-menu))

;; Top level
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-quit]
  '(menu-item "Quit" bmkp-bmenu-quit
    :help "Quit the bookmark list, saving its state and the current set of bookmarks"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-describe-marked]
  '(menu-item "Describe Marked Bookmarks" bmkp-bmenu-describe-marked
    :help "Describe the marked bookmarks.  With `C-u' show internal format."))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-describe-this-bookmark]
  '(menu-item "Describe This Bookmark" bmkp-bmenu-describe-this-bookmark
    :help "Describe this line's bookmark.  With `C-u' show internal format."))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-mode-status-help]
  '(menu-item "Current Status, Mode Help" bmkp-bmenu-mode-status-help :keys "?"
    :help "Describe `*Bookmark List*' and show its current status"))
(define-key bmkp-bmenu-menubar-menu [top-sep2] '("--"))
(define-key bmkp-bmenu-menubar-menu [bmkp-toggle-saving-menu-list-state]
  '(menu-item "Toggle Autosaving Display State" bmkp-toggle-saving-menu-list-state
    :help "Toggle the value of option `bmkp-bmenu-state-file'"))
(define-key bmkp-bmenu-menubar-menu [bmkp-toggle-saving-bookmark-file]
  '(menu-item "Toggle Autosaving Bookmark File" bmkp-toggle-saving-bookmark-file
    :help "Toggle the value of option `bookmark-save-flag'"))
(define-key bmkp-bmenu-menubar-menu [bmkp-switch-bookmark-file]
  '(menu-item "Switch to Bookmark File..." bmkp-switch-bookmark-file
    :help "Switch to a different bookmark file, *replacing* the current set of bookmarks"))
(define-key bmkp-bmenu-menubar-menu [bookmark-bmenu-load]
  '(menu-item "Add Bookmarks from File..." bookmark-bmenu-load
    :help "Load additional bookmarks from a bookmark file"))
(define-key bmkp-bmenu-menubar-menu [bmkp-empty-file]
  '(menu-item "New (Empty) Bookmark File..." bmkp-empty-file
    :help "Create a new, empty bookmark file, or empty an existing bookmark file"))
(define-key bmkp-bmenu-menubar-menu [bookmark-write]
  '(menu-item "Save As..." bookmark-write
    :help "Write the current set of bookmarks to a file whose name you enter"))
(define-key bmkp-bmenu-menubar-menu [bookmark-bmenu-save]
  '(menu-item "Save" bookmark-bmenu-save
    :help "Save the current set of bookmarks to the current bookmark file"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-refresh-menu-list]
  '(menu-item "Refresh (Revert)" bmkp-bmenu-refresh-menu-list
    :help "Update the displayed bookmark list to reflect the currently defined bookmarks"))
(define-key bmkp-bmenu-menubar-menu [top-sep1] '("--"))

(define-key bmkp-bmenu-menubar-menu [bmkp-make-function-bookmark]
  '(menu-item "New Function Bookmark..." bmkp-make-function-bookmark
    :help "Create a bookmark that will invoke FUNCTION when \"jumped\" to"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-make-sequence-from-marked]
  '(menu-item "New Sequence Bookmark from Marked..." bmkp-bmenu-make-sequence-from-marked
    :help "Create or update a sequence bookmark from the visible marked bookmarks"))
(define-key bmkp-bmenu-menubar-menu [bmkp-choose-navlist-from-bookmark-list]
  '(menu-item "Set Navlist from Bookmark-List Bookmark..." bmkp-choose-navlist-from-bookmark-list
    :help "Set the navigation list from a bookmark-list bookmark"))
(define-key bmkp-bmenu-menubar-menu [bmkp-choose-navlist-of-type]
  '(menu-item "Set Navlist to Bookmarks of Type..." bmkp-choose-navlist-of-type
    :help "Set the navigation list to the bookmarks of a certain type"))
(define-key bmkp-bmenu-menubar-menu [bmkp-list-defuns-in-commands-file]
  '(menu-item "List User-Defined Bookmark Commands" bmkp-list-defuns-in-commands-file
    :help "List the functions defined in `bmkp-bmenu-commands-file'"))

(defvar bmkp-bmenu-define-command-menu (make-sparse-keymap "Define Command")
    "`Define Command' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [define-command]
  (cons "Define Command" bmkp-bmenu-define-command-menu))

(define-key bmkp-bmenu-define-command-menu [bmkp-bmenu-define-full-snapshot-command]
  '(menu-item "To Restore Full Bookmark-List State..." bmkp-bmenu-define-full-snapshot-command
    :help "Define a command to restore the current bookmark-list state"))
(define-key bmkp-bmenu-define-command-menu [bmkp-bmenu-define-command]
  '(menu-item "To Restore Current Order and Filter..." bmkp-bmenu-define-command
    :help "Define a command to use the current sort order, filter, and omit list"))
(define-key bmkp-bmenu-define-command-menu [bmkp-define-tags-sort-command]
  '(menu-item "To Sort by Specific Tags..." bmkp-define-tags-sort-command
    :help "Define a command to sort bookmarks in the bookmark list by certain tags"))
(define-key bmkp-bmenu-define-command-menu [bmkp-bmenu-define-jump-marked-command]
  '(menu-item "To Jump to a Bookmark Now Marked..." bmkp-bmenu-define-jump-marked-command
    :help "Define a command to jump to one of the bookmarks that is now marked"
    :enable bmkp-bmenu-marked-bookmarks))

(when (featurep 'bookmark+-lit)
  (defvar bmkp-bmenu-highlight-menu (make-sparse-keymap "Highlight")
    "`Highlight' submenu for menu-bar `Bookmark+' menu.")
  (define-key bmkp-bmenu-menubar-menu [highlight] (cons "Highlight" bmkp-bmenu-highlight-menu))

  (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-show-only-lighted]
    '(menu-item "Show Only Highlighted" bmkp-bmenu-show-only-lighted
      :help "Display (only) highlighted bookmarks"))
  (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-set-lighting-for-marked]
    '(menu-item "Set Highlighting for Marked" bmkp-bmenu-set-lighting-for-marked
      :help "Set specific highlighting for the marked bookmarks"
      :enable bmkp-bmenu-marked-bookmarks))
  (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-unlight-marked]
    '(menu-item "Unhighlight Marked" bmkp-bmenu-unlight-marked
      :help "Unhighlight the marked bookmarks"
      :enable bmkp-bmenu-marked-bookmarks))
  (define-key bmkp-bmenu-highlight-menu [bmkp-bmenu-light-marked]
    '(menu-item "Highlight Marked" bmkp-bmenu-light-marked
      :help "Highlight the marked bookmarks"
      :enable bmkp-bmenu-marked-bookmarks)))

(defvar bmkp-bmenu-tags-menu (make-sparse-keymap "Tags")
    "`Tags' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [tags] (cons "Tags" bmkp-bmenu-tags-menu))

(define-key bmkp-bmenu-tags-menu [bmkp-list-all-tags]
  '(menu-item "List All Tags" bmkp-list-all-tags :help "List all tags used for any bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-purge-notags-autofiles]
  '(menu-item "Purge Autofiles with No Tags..." bmkp-purge-notags-autofiles
    :help "Delete all autofile bookmarks that have no tags"))
(define-key bmkp-bmenu-tags-menu [bmkp-untag-a-file]
  '(menu-item "Untag a File (Remove Some)..." bmkp-untag-a-file
    :help "Remove some tags from autofile bookmark for a file"))
(define-key bmkp-bmenu-tags-menu [bmkp-tag-a-file]
  '(menu-item "Tag a File (Add Some)..." bmkp-tag-a-file
    :help "Add some tags to the autofile bookmark for a file"))
(define-key bmkp-bmenu-tags-menu [bmkp-rename-tag]
  '(menu-item "Rename Tag..." bmkp-rename-tag
    :help "Rename a tag in all bookmarks, even those not showing"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-set-tag-value-for-marked]
  '(menu-item "Set Tag Value for Marked..." bmkp-bmenu-set-tag-value-for-marked
    :help "Set the value of a tag, for each of the marked bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-remove-tags-from-all]
  '(menu-item "Remove Some Tags from All..." bmkp-remove-tags-from-all
    :help "Remove a set of tags from all bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-remove-tags-from-marked]
  '(menu-item "Remove Some Tags from Marked..." bmkp-bmenu-remove-tags-from-marked
    :help "Remove a set of tags from each of the marked bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-add-tags-to-marked]
  '(menu-item "Add Some Tags to Marked..." bmkp-bmenu-add-tags-to-marked
    :help "Add a set of tags to each of the marked bookmarks"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-paste-replace-tags-for-marked]
  '(menu-item "Paste Tags to Marked (Replace)..." bmkp-bmenu-paste-replace-tags-for-marked
    :help "Replace tags for the marked bookmarks with tags copied previously"))
(define-key bmkp-bmenu-tags-menu [bmkp-bmenu-paste-add-tags-to-marked]
  '(menu-item "Paste Tags to Marked (Add)..." bmkp-bmenu-paste-add-tags-to-marked
    :help "Add tags copied from another bookmark to the marked bookmarks"))

(defvar bmkp-bmenu-sort-menu (make-sparse-keymap "Sort")
    "`Sort' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [sort] (cons "Sort" bmkp-bmenu-sort-menu))

(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-url]
  '(menu-item "By URL" bmkp-bmenu-sort-by-url
    :help "Sort URL bookmarks alphabetically by their URL/filename"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-Gnus-thread]
  '(menu-item "By Gnus Thread" bmkp-bmenu-sort-by-Gnus-thread
    :help "Sort Gnus bookmarks by group, then by article, then by message"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-Info-location]
  '(menu-item "By Info Node" bmkp-bmenu-sort-by-Info-location
    :help "Sort Info bookmarks by file name, then node name, then position"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-last-local-file-update]
  '(menu-item "By Last Local File Update" bmkp-bmenu-sort-by-last-local-file-update
    :help "Sort bookmarks by last local file update time"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-last-buffer-or-file-access]
  '(menu-item "By Last Buffer/File Access" bmkp-bmenu-sort-by-last-buffer-or-file-access
    :help "Sort bookmarks by time of last buffer access or local-file access"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-local-file-size]
  '(menu-item "By Local File Size" bmkp-bmenu-sort-by-local-file-size
    :help "Sort bookmarks by local file size"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-local-file-type]
  '(menu-item "By Local File Type" bmkp-bmenu-sort-by-local-file-type
    :help "Sort bookmarks by local file type: file, symlink, directory"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-bookmark-type]
  '(menu-item "By Type" bmkp-bmenu-sort-by-bookmark-type
    :help "Sort bookmarks by type: Info, URL, Gnus, files, other"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-file-name]
  '(menu-item "By File Name" bmkp-bmenu-sort-by-file-name :help "Sort bookmarks by file name"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-bookmark-name]
  '(menu-item "By Bookmark Name" bmkp-bmenu-sort-by-bookmark-name
    :help "Sort bookmarks by bookmark name, respecting `case-fold-search'"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-creation-time]
  '(menu-item "By Creation Time" bmkp-bmenu-sort-by-creation-time
    :help "Sort bookmarks by the time of their creation"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-last-bookmark-access]
  '(menu-item "By Last Bookmark Access" bmkp-bmenu-sort-by-last-bookmark-access
    :help "Sort bookmarks by the time of their last visit as bookmarks"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-by-bookmark-visit-frequency]
  '(menu-item "By Bookmark Use" bmkp-bmenu-sort-by-bookmark-visit-frequency
    :help "Sort bookmarks by the number of times they were visited as bookmarks"))
(define-key bmkp-bmenu-sort-menu [bmkp-bmenu-sort-marked-before-unmarked]
  '(menu-item "Marked Before Unmarked" bmkp-bmenu-sort-marked-before-unmarked
    :help "Sort bookmarks by putting marked before unmarked"))
(define-key bmkp-bmenu-sort-menu [bmkp-reverse-sort-order]
  '(menu-item "Reverse" bmkp-reverse-sort-order :help "Reverse the current bookmark sort order"))

(defvar bmkp-bmenu-show-menu (make-sparse-keymap "Show")
    "`Show' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [show] (cons "Show" bmkp-bmenu-show-menu))

(define-key bmkp-bmenu-show-menu [bookmark-bmenu-show-all-annotations]
  '(menu-item "Show Annotations" bookmark-bmenu-show-all-annotations
    :help "Show the annotations for all bookmarks (in another window)"))
(define-key bmkp-bmenu-show-menu [bookmark-bmenu-toggle-filenames]
  '(menu-item "Show/Hide File Names" bookmark-bmenu-toggle-filenames
    :help "Toggle whether filenames are shown in the bookmark list"))
(define-key bmkp-bmenu-show-menu [show-sep1] '("--"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-all]
  '(menu-item "Show All" bmkp-bmenu-show-all
    :help "Show all bookmarks currently known to the bookmark list"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-tags-incrementally]
  '(menu-item "Show Only Tag Matches..." bmkp-bmenu-filter-tags-incrementally
    :help "Incrementally filter bookmarks by tags using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-annotation-incrementally]
  '(menu-item "Show Only Annotation Matches..." bmkp-bmenu-filter-annotation-incrementally
    :help "Incrementally filter bookmarks by annotation using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-file-name-incrementally]
  '(menu-item "Show Only File Name Matches..." bmkp-bmenu-filter-file-name-incrementally
    :help "Incrementally filter bookmarks by file name using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-filter-bookmark-name-incrementally]
  '(menu-item "Show Only Name Matches..." bmkp-bmenu-filter-bookmark-name-incrementally
    :help "Incrementally filter bookmarks by bookmark name using a regexp"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-specific-file]
  '(menu-item "Show Only for Specific File" bmkp-bmenu-show-only-specific-file
    :help "Display (only) the bookmarks for a specific file"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-specific-buffer]
  '(menu-item "Show Only for Specific Buffer" bmkp-bmenu-show-only-specific-buffer
    :help "Display (only) the bookmarks for a specific buffer"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-urls]
  '(menu-item "Show Only URLs" bmkp-bmenu-show-only-urls
    :help "Display (only) the URL bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-gnus]
  '(menu-item "Show Only Gnus Messages" bmkp-bmenu-show-only-gnus
    :help "Display (only) the Gnus bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-man-pages]
  '(menu-item "Show Only UNIX Manual Pages" bmkp-bmenu-show-only-man-pages
    :help "Display (only) the `man' page bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-info-nodes]
  '(menu-item "Show Only Info Nodes" bmkp-bmenu-show-only-info-nodes
    :help "Display (only) the Info bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-dired]
  '(menu-item "Show Only Dired Buffers" bmkp-bmenu-show-only-dired
    :help "Display (only) the Dired bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-bookmark-files]
  '(menu-item "Show Only Bookmark Files" bmkp-bmenu-show-only-bookmark-files
    :help "Display (only) the bookmark-file bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-desktops]
  '(menu-item "Show Only Desktops" bmkp-bmenu-show-only-desktops
    :help "Display (only) the desktop bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-regions]
  '(menu-item "Show Only Regions" bmkp-bmenu-show-only-regions
    :help "Display (only) the bookmarks that record a region"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-non-files]
  '(menu-item "Show Only Non-Files (Buffers)" bmkp-bmenu-show-only-non-files
    :help "Display (only) the non-file bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-files]
  '(menu-item "Show Only Files" bmkp-bmenu-show-only-files
    :help "Display (only) the file and directory bookmarks"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-autofiles]
  '(menu-item "Show Only Autofiles" bmkp-bmenu-show-only-autofiles
    :help "Display (only) the autofile bookmarks: those named the same as their files"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-autonamed]
  '(menu-item "Show Only Autonamed" bmkp-bmenu-show-only-autonamed
    :help "Display (only) the autonamed bookmarks"))
(when (featurep 'bookmark+-lit)
  (define-key bmkp-bmenu-show-menu [bmkp-bmenu-show-only-lighted]
    '(menu-item "Show Only Highlighted" bmkp-bmenu-show-only-lighted
      :help "Display (only) highlighted bookmarks")))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-toggle-show-only-unmarked]
  '(menu-item "Show Only Unmarked" bmkp-bmenu-toggle-show-only-unmarked
    :help "Hide all marked bookmarks.  Repeat to toggle, showing all"))
(define-key bmkp-bmenu-show-menu [bmkp-bmenu-toggle-show-only-marked]
  '(menu-item "Show Only Marked" bmkp-bmenu-toggle-show-only-marked
    :help "Hide all unmarked bookmarks.  Repeat to toggle, showing all"))

(defvar bmkp-bmenu-omit-menu (make-sparse-keymap "Omit")
  "`Omit' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [omitting] (cons "Omit" bmkp-bmenu-omit-menu))

(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-show-all]
  '(menu-item "Show All" bmkp-bmenu-show-all
    :visible (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only)
    :help "Show all bookmarks (except omitted)"))
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-show-only-omitted]
  '(menu-item "Show Only Omitted" bmkp-bmenu-show-only-omitted
    :visible (not (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only))
    :enable bmkp-bmenu-omitted-bookmarks :help "Show only the omitted bookmarks"))
(define-key bmkp-bmenu-omit-menu [bmkp-unomit-all]
  '(menu-item "Un-Omit All" bmkp-unomit-all
    :visible bmkp-bmenu-omitted-bookmarks :help "Un-omit all omitted bookmarks"))
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-unomit-marked]
  '(menu-item "Un-Omit Marked" bmkp-bmenu-unomit-marked
    :visible (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only)
    :enable (and bmkp-bmenu-omitted-bookmarks
             (save-excursion (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
                             (re-search-forward "^>" (point-max) t)))
    :help "Un-omit the marked bookmarks" :keys "\\[bmkp-bmenu-omit/unomit-marked]"))
(define-key bmkp-bmenu-omit-menu [bmkp-bmenu-omit-marked]
  '(menu-item "Omit Marked" bmkp-bmenu-omit-marked
    :visible (not (eq bmkp-bmenu-filter-function 'bmkp-omitted-alist-only))
    :enable (and (save-excursion (goto-char (point-min)) (forward-line bmkp-bmenu-header-lines)
                                 (re-search-forward "^>" (point-max) t)))
    :help "Omit the marked bookmarks" :keys "\\[bmkp-bmenu-omit/unomit-marked]"))

(defvar bmkp-bmenu-mark-menu (make-sparse-keymap "Mark")
    "`Mark' submenu for menu-bar `Bookmark+' menu.")
(define-key bmkp-bmenu-menubar-menu [marking] (cons "Mark" bmkp-bmenu-mark-menu))

(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-not-all]
  '(menu-item "Unmark If Not Tagged with All..." bmkp-bmenu-unmark-bookmarks-tagged-not-all
    :help "Unmark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-none]
  '(menu-item "Unmark If Tagged with None..." bmkp-bmenu-unmark-bookmarks-tagged-none
    :help "Unmark all visible bookmarks that are *not* tagged with *any* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-all]
  '(menu-item "Unmark If Tagged with All..." bmkp-bmenu-unmark-bookmarks-tagged-all
    :help "Unmark all visible bookmarks that are tagged with *each* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-some]
  '(menu-item "Unmark If Tagged with Some..." bmkp-bmenu-unmark-bookmarks-tagged-some
    :help "Unmark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-bookmarks-tagged-regexp]
  '(menu-item "Unmark If Tagged Matching Regexp..." bmkp-bmenu-unmark-bookmarks-tagged-regexp
    :help "Unmark bookmarks any of whose tags match a regexp you enter"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-not-all]
  '(menu-item "Mark If Not Tagged with All..." bmkp-bmenu-mark-bookmarks-tagged-not-all
    :help "Mark all visible bookmarks that are *not* tagged with *all* tags you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-none]
  '(menu-item "Mark If Tagged with None..." bmkp-bmenu-mark-bookmarks-tagged-none
    :help "Mark all visible bookmarks that are not tagged with *any* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-all]
  '(menu-item "Mark If Tagged with All..." bmkp-bmenu-mark-bookmarks-tagged-all
    :help "Mark all visible bookmarks that are tagged with *each* tag you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-some]
  '(menu-item "Mark If Tagged with Some..." bmkp-bmenu-mark-bookmarks-tagged-some
    :help "Mark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmarks-tagged-regexp]
  '(menu-item "Mark If Tagged Matching Regexp..." bmkp-bmenu-mark-bookmarks-tagged-regexp
    :help "Mark bookmarks any of whose tags match a regexp you enter"))
(define-key bmkp-bmenu-mark-menu [mark-sep1] '("--"))
(when (featurep 'bookmark+-lit)
  (define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-lighted-bookmarks]
    '(menu-item "Mark Highlighted" bmkp-bmenu-mark-lighted-bookmarks
      :help "Mark highlighted bookmarks")))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-specific-file-bookmarks]
  '(menu-item "Mark for Specific File" bmkp-bmenu-mark-specific-file-bookmarks
    :help "Mark bookmarks for a specific file"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-specific-buffer-bookmarks]
  '(menu-item "Mark for Specific Buffer" bmkp-bmenu-mark-specific-buffer-bookmarks
    :help "Mark bookmarks for a specific buffer"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-url-bookmarks]
  '(menu-item "Mark URLs" bmkp-bmenu-mark-url-bookmarks :help "Mark URL bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-gnus-bookmarks]
  '(menu-item "Mark Gnus Messages" bmkp-bmenu-mark-gnus-bookmarks :help "Mark Gnus bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-man-bookmarks]
  '(menu-item "Mark UNIX Manual Pages" bmkp-bmenu-mark-man-bookmarks
    :help "Mark `man' page bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-info-bookmarks]
  '(menu-item "Mark Info Nodes" bmkp-bmenu-mark-info-bookmarks :help "Mark Info bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-dired-bookmarks]
  '(menu-item "Mark Dired Buffers" bmkp-bmenu-mark-dired-bookmarks :help "Mark Dired bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-bookmark-file-bookmarks]
  '(menu-item "Mark Bookmark Files" bmkp-bmenu-mark-bookmark-file-bookmarks
    :help "Mark the bookmark-file bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-desktop-bookmarks]
  '(menu-item "Mark Desktops" bmkp-bmenu-mark-desktop-bookmarks
    :help "Mark desktop bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-region-bookmarks]
  '(menu-item "Mark Regions" bmkp-bmenu-mark-region-bookmarks
    :help "Mark bookmarks that record a region"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-non-file-bookmarks]
  '(menu-item "Mark Non-Files (Buffers)" bmkp-bmenu-mark-non-file-bookmarks
    :help "Mark non-file bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-autofile-bookmarks]
  '(menu-item "Mark Autofiles" bmkp-bmenu-mark-autofile-bookmarks
    :help "Mark autofile bookmarks: those whose names are the same as their files"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-file-bookmarks]
  '(menu-item "Mark Files" bmkp-bmenu-mark-file-bookmarks :help "Mark file bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-unmark-all]
  '(menu-item "Unmark All" bmkp-bmenu-unmark-all
    :help "Remove a mark you specify (> or D) from each bookmark (RET to remove both kinds)"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-mark-all]
  '(menu-item "Mark All" bmkp-bmenu-mark-all :help "Mark all bookmarks, using mark `>'"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-toggle-marks]
  '(menu-item "Toggle Marked/Unmarked" bmkp-bmenu-toggle-marks
    :help "Unmark all marked bookmarks; mark all unmarked bookmarks"))
(define-key bmkp-bmenu-mark-menu [bmkp-bmenu-regexp-mark]
  '(menu-item "Mark Regexp Matches..." bmkp-bmenu-regexp-mark
    :help "Mark bookmarks that match a regexp that you enter"))

(define-key bmkp-bmenu-menubar-menu [bookmark-bmenu-execute-deletions]
  '(menu-item "Delete Flagged (D)" bookmark-bmenu-execute-deletions
    :help "Delete the (visible) bookmarks flagged `D'"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-delete-marked]
  '(menu-item "Delete Marked (>)" bmkp-bmenu-delete-marked
    :help "Delete all (visible) bookmarks marked `>', after confirmation"))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-query-replace-marked-bookmarks-regexp]
  '(menu-item "Query-Replace Marked..." bmkp-bmenu-query-replace-marked-bookmarks-regexp
    :help "`query-replace-regexp' over all files whose bookmarks are marked"))
(when (fboundp 'bmkp-bmenu-isearch-marked-bookmarks)
  (define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-isearch-marked-bookmarks-regexp]
    '(menu-item "Regexp-Isearch Marked..." bmkp-bmenu-isearch-marked-bookmarks-regexp
      :help "Regexp Isearch the marked bookmark locations, in their current order"))
  (define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-isearch-marked-bookmarks]
    '(menu-item "Isearch Marked..." bmkp-bmenu-isearch-marked-bookmarks
      :help "Isearch the marked bookmark locations, in their current order")))
(define-key bmkp-bmenu-menubar-menu [bmkp-bmenu-search-marked-bookmarks-regexp]
  '(menu-item "Search Marked..." bmkp-bmenu-search-marked-bookmarks-regexp
    :help "Regexp-search the files whose bookmarks are marked, in their current order"))
(define-key bmkp-bmenu-menubar-menu [bookmark-bmenu-select]
  '(menu-item "Jump to Marked" bookmark-bmenu-select
    :help "Jump to this line's bookmark.  Also visit each bookmark marked with `>'"))



;;; Mouse-3 menu binding.

(defvar bmkp-bmenu-line-overlay nil
  "Overlay to highlight the current line for `bmkp-bmenu-mouse-3-menu'.")
(define-key bookmark-bmenu-mode-map [mouse-3] 'bmkp-bmenu-mouse-3-menu)

;;;###autoload
(defun bmkp-bmenu-mouse-3-menu (event)
  "Pop-up menu on `mouse-3' for a bookmark listed in `*Bookmark List*'."
  (interactive "e")
  (let* ((mouse-pos                  (event-start event))
         (inhibit-field-text-motion  t) ; Just in case.
         bol eol
         (bmk-name                   (save-excursion
                                       (with-current-buffer (window-buffer (posn-window mouse-pos))
                                         (save-excursion
                                           (goto-char (posn-point mouse-pos))
                                           (save-excursion
                                             (setq bol  (progn (beginning-of-line) (point))
                                                   eol  (progn (end-of-line) (point))))
                                           (if bmkp-bmenu-line-overlay ; Don't recreate.
                                               (move-overlay bmkp-bmenu-line-overlay bol eol
                                                             (current-buffer))
                                             (setq bmkp-bmenu-line-overlay  (make-overlay bol eol))
                                             (overlay-put bmkp-bmenu-line-overlay 'face 'region))
                                           (bookmark-bmenu-bookmark))))))
    (sit-for 0)
    (let ((menu-choice
           (x-popup-menu event
                         (list "This Bookmark"
                               (if bmk-name
                                   (list bmk-name
                                         (if (bmkp-bookmark-name-member bmk-name
                                                                        bmkp-bmenu-marked-bookmarks)
                                             '("Unmark" . bookmark-bmenu-unmark)
                                           '("Mark" . bookmark-bmenu-mark))
                                         (save-excursion
                                           (goto-char (posn-point mouse-pos))
                                           (beginning-of-line)
                                           (if (looking-at "^D")
                                               '("Unmark" . bookmark-bmenu-unmark)
                                             '("Flag for Deletion" . bookmark-bmenu-delete)))
                                         '("Omit" . bmkp-bmenu-omit)
                                         '("--") ; ----------------------------------------
                                         '("Jump To" . bookmark-bmenu-this-window)
                                         '("Jump To in Other Window" . bookmark-bmenu-other-window)
                                         '("--") ; ----------------------------------------
                                         '("Copy Tags" . bmkp-bmenu-copy-tags)
                                         '("Paste Tags (Add)" . bmkp-bmenu-paste-add-tags)
                                         '("Paste Tags (Replace)" . bmkp-bmenu-paste-replace-tags)
                                         '("Add Some Tags..." . bmkp-bmenu-add-tags)
                                         '("Remove Some Tags..." . bmkp-bmenu-remove-tags)
                                         '("Remove All Tags..." . bmkp-bmenu-remove-all-tags)
                                         '("Rename..." . bmkp-rename-tag)
                                         '("Set Tag Value..." . bmkp-bmenu-set-tag-value)
                                         (and (featurep 'bookmark+-lit)
                                              '("--")) ; ----------------------------------------
                                         (and (featurep 'bookmark+-lit)
                                              '("Highlight"   . bmkp-bmenu-light))
                                         (and (featurep 'bookmark+-lit)
                                              '("Unhighlight" . bmkp-bmenu-unlight))
                                         (and (featurep 'bookmark+-lit)
                                              '("Set Lighting" . bmkp-bmenu-set-lighting))
                                         '("--") ; ----------------------------------------
                                         '("Show Annotation" . bookmark-bmenu-show-annotation)
                                         '("Edit Annotation..." . bookmark-bmenu-edit-annotation)
                                         '("Edit Name, File Name..." . bmkp-bmenu-edit-bookmark)
                                         '("Rename..." . bookmark-bmenu-rename)
                                         '("Relocate..." . bookmark-bmenu-relocate)
                                         '("--") ; ----------------------------------------
                                         '("Describe" . bmkp-bmenu-describe-this-bookmark))
                                 '("" (""))))))) ; No menu: not on a bookmark line.
      (when bmkp-bmenu-line-overlay (delete-overlay bmkp-bmenu-line-overlay))
      (and menu-choice  (save-excursion (goto-char (posn-point mouse-pos))
                                        (call-interactively menu-choice))))))

;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+-bmu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-bmu.el ends here
