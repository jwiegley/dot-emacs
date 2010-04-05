;;; bookmark+.el - Bookmark+: extensions to standard library `bookmark.el'.
;;
;; Filename: bookmark+.el
;; Description: Bookmark+: extensions to standard library `bookmark.el'.
;; Author: Drew Adams, Thierry Volpiatto
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2010, Drew Adams, all rights reserved.
;; Copyright (C) 2009, Thierry Volpiatto, all rights reserved.
;; Created: Fri Sep 15 07:58:41 2000
;; Last-Updated: Tue Mar 30 13:47:20 2010 (-0700)
;;           By: dradams
;;     Update #: 11876
;; URL: http://www.emacswiki.org/cgi-bin/wiki/bookmark+.el
;; Keywords: bookmarks, placeholders, annotations, search, info, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   `bookmark', `ffap', `pp'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Bookmark+: extensions to standard library `bookmark.el'.
;;
;;    The documentation and change history for Bookmark+ are in the
;;    separate, comment-only file `bookmark+-doc.el'.  That
;;    documentation is also available in these ways:
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
;;  (@> "Macros")
;;  (@> "Faces (Customizable)")
;;  (@> "User Options (Customizable)")
;;  (@> "Internal Variables")
;;  (@> "Compatibility Code for Older Emacs Versions")
;;  (@> "Core Replacements (`bookmark-*' except `bookmark-bmenu-*')")
;;  (@> "Menu List Replacements (`bookmark-bmenu-*')")
;;  (@> "Bookmark+ Functions (`bookmarkp-*')")
;;    (@> "Menu-List (`*-bmenu-*') Filter Commands")
;;    (@> "Menu-List (`*-bmenu-*') Commands Involving Marks")
;;    (@> "Search-and-Replace Locations of Marked Bookmarks")
;;    (@> "Omitted Bookmarks")
;;    (@> "Tags")
;;    (@> "General Menu-List (`-*bmenu-*') Commands and Functions")
;;    (@> "Bookmark Predicates")
;;    (@> "Filter Functions")
;;    (@> "General Utility Functions")
;;    (@> "Bookmark Entry Access Functions")
;;    (@> "Sorting - General Functions")
;;    (@> "Sorting - Commands")
;;    (@> "Sorting - General Predicates")
;;    (@> "Sorting - File-Name Predicates")
;;    (@> "Other Bookmark+ Functions (`bookmarkp-*')")
;;  (@> "Keymaps")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Commands defined here:
;;
;;    `bookmarkp-add-tags', `bookmarkp-bmenu-add-tags-to-marked',
;;    `bookmarkp-all-tags-jump',
;;    `bookmarkp-all-tags-jump-other-window',
;;    `bookmarkp-all-tags-regexp-jump',
;;    `bookmarkp-all-tags-regexp-jump-other-window',
;;    `bookmarkp-bmenu-add-tags', `bookmarkp-bmenu-change-sort-order',
;;    `bookmarkp-bmenu-change-sort-order-repeat',
;;    `bookmarkp-bmenu-define-command',
;;    `bookmarkp-bmenu-define-full-snapshot-command',
;;    `bookmarkp-bmenu-define-jump-marked-command',
;;    `bookmarkp-bmenu-delete-marked',
;;    `bookmarkp-bmenu-describe-this-bookmark',
;;    `bookmarkp-bmenu-describe-this+move-down',
;;    `bookmarkp-bmenu-describe-this+move-up',
;;    `bookmarkp-bmenu-dired-marked', `bookmarkp-bmenu-edit-bookmark',
;;    `bookmarkp-bmenu-filter-bookmark-name-incrementally',
;;    `bookmarkp-bmenu-filter-file-name-incrementally',
;;    `bookmarkp-bmenu-filter-tags-incrementally',
;;    `bookmarkp-bmenu-isearch-marked-bookmarks' (Emacs 23+),
;;    `bookmarkp-bmenu-isearch-marked-bookmarks-regexp' (Emacs 23+),
;;    `bookmarkp-bmenu-make-sequence-from-marked',
;;    `bookmarkp-bmenu-mark-all',
;;    `bookmarkp-bmenu-mark-bookmarks-satisfying',
;;    `bookmarkp-bmenu-mark-bookmarks-tagged-all',
;;    `bookmarkp-bmenu-mark-bookmarks-tagged-none',
;;    `bookmarkp-bmenu-mark-bookmarks-tagged-not-all',
;;    `bookmarkp-bmenu-mark-bookmarks-tagged-regexp',
;;    `bookmarkp-bmenu-mark-bookmarks-tagged-some',
;;    `bookmarkp-bmenu-mark-desktop-bookmarks',
;;    `bookmarkp-bmenu-mark-dired-bookmarks',
;;    `bookmarkp-bmenu-mark-file-bookmarks',
;;    `bookmarkp-bmenu-mark-gnus-bookmarks',
;;    `bookmarkp-bmenu-mark-info-bookmarks',
;;    `bookmarkp-bmenu-mark-man-bookmarks',
;;    `bookmarkp-bmenu-mark-non-file-bookmarks',
;;    `bookmarkp-bmenu-mark-region-bookmarks',
;;    `bookmarkp-bmenu-mark-w3m-bookmarks',
;;    `bookmarkp-bmenu-mouse-3-menu', `bookmarkp-bmenu-omit-marked',
;;    `bookmarkp-bmenu-omit', `bookmarkp-bmenu-omit/unomit-marked',
;;    `bookmarkp-bmenu-query-replace-marked-bookmarks-regexp',
;;    `bookmarkp-bmenu-quit', `bookmarkp-bmenu-refresh-menu-list',
;;    `bookmarkp-bmenu-regexp-mark',
;;    `bookmarkp-bmenu-remove-all-tags',
;;    `bookmarkp-bmenu-remove-tags',
;;    `bookmarkp-bmenu-remove-tags-from-marked',
;;    `bookmarkp-bmenu-set-tag-value', `bookmarkp-bmenu-show-all',
;;    `bookmarkp-bmenu-show-only-desktops',
;;    `bookmarkp-bmenu-show-only-dired',
;;    `bookmarkp-bmenu-show-only-files',
;;    `bookmarkp-bmenu-show-only-gnus',
;;    `bookmarkp-bmenu-show-only-info-nodes',
;;    `bookmarkp-bmenu-show-only-man-pages',
;;    `bookmarkp-bmenu-show-only-non-files',
;;    `bookmarkp-bmenu-show-only-omitted',
;;    `bookmarkp-bmenu-show-only-regions',
;;    `bookmarkp-bmenu-show-only-w3m-urls',
;;    `bookmarkp-bmenu-sort-by-bookmark-name',
;;    `bookmarkp-bmenu-sort-by-bookmark-visit-frequency',
;;    `bookmarkp-bmenu-sort-by-creation-time',
;;    `bookmarkp-bmenu-sort-by-file-name',
;;    `bookmarkp-bmenu-sort-by-Gnus-thread',
;;    `bookmarkp-bmenu-sort-by-Info-location',
;;    `bookmarkp-bmenu-sort-by-last-bookmark-access',
;;    `bookmarkp-bmenu-sort-by-last-buffer-or-file-access',
;;    `bookmarkp-bmenu-sort-by-last-local-file-access',
;;    `bookmarkp-bmenu-sort-by-last-local-file-update',
;;    `bookmarkp-bmenu-sort-by-local-file-size',
;;    `bookmarkp-bmenu-sort-by-local-file-type',
;;    `bookmarkp-bmenu-sort-by-w3m-url',
;;    `bookmarkp-bmenu-sort-marked-before-unmarked',
;;    `bookmarkp-bmenu-mode-status-help',
;;    `bookmarkp-bmenu-toggle-marks',
;;    `bookmarkp-bmenu-toggle-show-only-marked',
;;    `bookmarkp-bmenu-toggle-show-only-unmarked',
;;    `bookmarkp-bmenu-unmark-all',
;;    `bookmarkp-bmenu-unmark-bookmarks-tagged-all',
;;    `bookmarkp-bmenu-unmark-bookmarks-tagged-none',
;;    `bookmarkp-bmenu-unmark-bookmarks-tagged-not-all',
;;    `bookmarkp-bmenu-unmark-bookmarks-tagged-some',
;;    `bookmarkp-bmenu-unomit-marked', `bookmarkp-bmenu-w32-open',
;;    `bookmarkp-bmenu-w32-open-select',
;;    `bookmarkp-bmenu-w32-open-with-mouse',
;;    `bookmarkp-bookmark-list-jump',
;;    `bookmarkp-define-tags-sort-command',
;;    `bookmarkp-describe-bookmark',
;;    `bookmarkp-describe-bookmark-internals',
;;    `bookmarkp-desktop-change-dir', `bookmarkp-desktop-delete',
;;    `bookmarkp-desktop-jump', `bookmarkp-desktop-read',
;;    `bookmarkp-dired-jump', `bookmarkp-dired-jump-current',
;;    `bookmarkp-dired-jump-current-other-window',
;;    `bookmarkp-dired-jump-other-window', `bookmarkp-file-jump',
;;    `bookmarkp-file-jump-other-window', `bookmarkp-gnus-jump',
;;    `bookmarkp-gnus-jump-other-window', `bookmarkp-info-jump',
;;    `bookmarkp-info-jump-other-window', `bookmarkp-jump-to-type',
;;    `bookmarkp-jump-to-type-other-window',
;;    `bookmarkp-list-all-tags',
;;    `bookmarkp-list-defuns-in-commands-file',
;;    `bookmarkp-local-file-jump',
;;    `bookmarkp-local-file-jump-other-window',
;;    `bookmarkp-make-function-bookmark', `bookmarkp-man-jump',
;;    `bookmarkp-man-jump-other-window',
;;    `bookmarkp-menu-jump-other-window' (Emacs 20, 21),
;;    `bookmarkp-non-file-jump',
;;    `bookmarkp-non-file-jump-other-window',
;;    `bookmarkp-read-bookmark-for-type', `bookmarkp-region-jump',
;;    `bookmarkp-region-jump-other-window',
;;    `bookmarkp-remote-file-jump',
;;    `bookmarkp-remote-file-jump-other-window',
;;    `bookmarkp-remove-all-tags', `bookmarkp-remove-tags',
;;    `bookmarkp-remove-tags-from-all', `bookmarkp-rename-tag',
;;    `bookmarkp-reverse-multi-sort-order',
;;    `bookmarkp-reverse-sort-order', `bookmarkp-send-bug-report',
;;    `bookmarkp-set-desktop-bookmark', `bookmarkp-set-tag-value',
;;    `bookmarkp-some-tags-jump',
;;    `bookmarkp-some-tags-jump-other-window',
;;    `bookmarkp-some-tags-regexp-jump',
;;    `bookmarkp-some-tags-regexp-jump-other-window',
;;    `bookmarkp-switch-bookmark-file',
;;    `bookmarkp-toggle-saving-bookmark-file',
;;    `bookmarkp-toggle-saving-menu-list-state',
;;    `bookmarkp-toggle-bookmark-set-refreshes',
;;    `bookmarkp-unomit-all', `bookmarkp-version',
;;    `bookmarkp-w3m-jump', `bookmarkp-w3m-jump-other-window',
;;    `old-bookmark-insert', `old-bookmark-relocate'.
;;
;;  User options defined here:
;;
;;    `bookmarkp-bmenu-commands-file', `bookmarkp-bmenu-omitted-list',
;;    `bookmarkp-bmenu-state-file',
;;    `bookmarkp-bookmark-name-length-max',
;;    `bookmarkp-desktop-no-save-vars',
;;    `bookmarkp-handle-region-function',
;;    `bookmarkp-incremental-filter-delay',
;;    `bookmarkp-menu-popup-max-length',
;;    `bookmarkp-region-search-size',
;;    `bookmarkp-save-new-location-flag',
;;    `bookmarkp-sequence-jump-display-function',
;;    `bookmarkp-show-end-of-region', `bookmarkp-sort-comparer',
;;    `bookmarkp-sort-orders-alist',
;;    `bookmarkp-sort-orders-for-cycling-alist',
;;    `bookmarkp-su-or-sudo-regexp', `bookmarkp-use-region-flag',
;;    `bookmarkp-w3m-allow-multi-tabs'.
;;
;;  Faces defined here:
;;
;;    `bookmarkp->-mark', `bookmarkp-a-mark',
;;    `bookmarkp-bad-bookmark', `bookmarkp-bookmark-list',
;;    `bookmarkp-buffer', `bookmarkp-D-mark', `bookmarkp-desktop',
;;    `bookmarkp-function', `bookmarkp-gnus', `bookmarkp-heading',
;;    `bookmarkp-info', `bookmarkp-local-directory',
;;    `bookmarkp-local-file-without-region',
;;    `bookmarkp-local-file-with-region', `bookmarkp-man',
;;    `bookmarkp-non-file', `bookmarkp-remote-file',
;;    `bookmarkp-sequence', `bookmarkp-su-or-sudo',
;;    `bookmarkp-t-mark', `bookmarkp-w3m'.
;;
;;  Macros defined here:
;;
;;    `bookmarkp-define-file-sort-predicate',
;;    `bookmarkp-define-sort-command'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkext-jump-gnus', `bmkext-jump-man', `bmkext-jump-w3m',
;;    `bmkext-jump-woman', `bookmarkp-alpha-cp', `bookmarkp-alpha-p',
;;    `bookmarkp-assoc-delete-all',
;;    `bookmarkp-barf-if-not-in-menu-list',
;;    `bookmarkp-bmenu-cancel-incremental-filtering',
;;    `bookmarkp-bmenu-filter-alist-by-bookmark-name-regexp',
;;    `bookmarkp-bmenu-filter-alist-by-file-name-regexp',
;;    `bookmarkp-bmenu-filter-alist-by-tags-regexp',
;;    `bookmarkp-bmenu-goto-bookmark-named', `bookmarkp-bmenu-list-1',
;;    `bookmarkp-bmenu-mark/unmark-bookmarks-tagged-all/none',
;;    `bookmarkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all',
;;    `bookmarkp-bmenu-propertize-item',
;;    `bookmarkp-bmenu-read-filter-input',
;;    `bookmarkp-bookmark-creation-cp',
;;    `bookmarkp-bookmark-last-access-cp',
;;    `bookmarkp-bookmark-list-alist-only',
;;    `bookmarkp-bookmark-list-bookmark-p',
;;    `bookmarkp-buffer-last-access-cp', `bookmarkp-cp-not',
;;    `bookmarkp-current-sort-order', `bookmarkp-desktop-alist-only',
;;    `bookmarkp-desktop-bookmark-p', `bookmarkp-desktop-kill',
;;    `bookmarkp-dired-alist-only', `bookmarkp-dired-bookmark-p',
;;    `bookmarkp-dired-subdirs', `bookmarkp-edit-bookmark',
;;    `bookmarkp-end-position-post-context',
;;    `bookmarkp-end-position-pre-context', `bookmarkp-every',
;;    `bookmarkp-face-prop', `bookmarkp-file-alist-only',
;;    `bookmarkp-file-alpha-cp', `bookmarkp-file-attribute-0-cp',
;;    `bookmarkp-file-attribute-1-cp',
;;    `bookmarkp-file-attribute-2-cp',
;;    `bookmarkp-file-attribute-3-cp',
;;    `bookmarkp-file-attribute-4-cp',
;;    `bookmarkp-file-attribute-5-cp',
;;    `bookmarkp-file-attribute-6-cp',
;;    `bookmarkp-file-attribute-7-cp',
;;    `bookmarkp-file-attribute-8-cp',
;;    `bookmarkp-file-attribute-9-cp',
;;    `bookmarkp-file-attribute-10-cp',
;;    `bookmarkp-file-attribute-11-cp', `bookmarkp-file-bookmark-p',
;;    `bookmarkp-file-remote-p', `bookmarkp-float-time',
;;    `bookmarkp-full-tag', `bookmarkp-function-bookmark-p',
;;    `bookmarkp-get-buffer-name', `bookmarkp-get-end-position',
;;    `bookmarkp-get-tag-value', `bookmarkp-get-tags',
;;    `bookmarkp-get-visit-time', `bookmarkp-get-visits-count',
;;    `bookmarkp-gnus-alist-only', `bookmarkp-gnus-bookmark-p',
;;    `bookmarkp-gnus-cp', `bookmarkp-goto-position',
;;    `bookmarkp-handler-cp', `bookmarkp-handle-region-default',
;;    `bookmarkp-has-tag-p', `bookmarkp-info-alist-only',
;;    `bookmarkp-info-bookmark-p', `bookmarkp-info-cp',
;;    `bookmarkp-isearch-bookmarks' (Emacs 23+),
;;    `bookmarkp-isearch-bookmarks-regexp' (Emacs 23+),
;;    `bookmarkp-isearch-next-bookmark-buffer' (Emacs 23+),
;;    `bookmarkp-jump-1', `bookmarkp-jump-bookmark-list',
;;    `bookmarkp-jump-desktop', `bookmarkp-jump-dired',
;;    `bookmarkp-jump-function', `bookmarkp-jump-gnus',
;;    `bookmarkp-jump-man', `bookmarkp-jump-sequence',
;;    `bookmarkp-jump-w3m', `bookmarkp-jump-w3m-new-session',
;;    `bookmarkp-jump-w3m-only-one-tab', `bookmarkp-jump-woman',
;;    `bookmarkp-line-number-at-pos',
;;    `bookmarkp-local-directory-bookmark-p',
;;    `bookmarkp-local-file-accessed-more-recently-cp',
;;    `bookmarkp-local-file-alist-only',
;;    `bookmarkp-local-file-bookmark-p',
;;    `bookmarkp-local-file-size-cp', `bookmarkp-local-file-type-cp',
;;    `bookmarkp-local-file-updated-more-recently-cp',
;;    `bookmarkp-make-bookmark-list-record',
;;    `bookmarkp-make-desktop-record', `bookmarkp-make-dired-record',
;;    `bookmarkp-make-gnus-record', `bookmarkp-make-man-record',
;;    `bookmarkp-make-plain-predicate', `bookmarkp-make-w3m-record',
;;    `bookmarkp-make-woman-record' (Emacs 21+),
;;    `bookmarkp-man-alist-only', `bookmarkp-man-bookmark-p',
;;    `bookmarkp-marked-bookmark-p',
;;    `bookmarkp-marked-bookmarks-only', `bookmarkp-marked-cp',
;;    `bookmarkp-maybe-save-bookmarks',
;;    `bookmarkp-msg-about-sort-order', `bookmarkp-multi-sort',
;;    `bookmarkp-non-file-alist-only',
;;    `bookmarkp-non-file-bookmark-p', `bookmarkp-omitted-alist-only',
;;    `bookmarkp-position-after-whitespace',
;;    `bookmarkp-position-before-whitespace',
;;    `bookmarkp-position-post-context',
;;    `bookmarkp-position-post-context-region',
;;    `bookmarkp-position-pre-context',
;;    `bookmarkp-position-pre-context-region', `bookmarkp-read-tags',
;;    `bookmarkp-read-tag-completing',
;;    `bookmarkp-read-tags-completing', `bookmarkp-record-visit',
;;    `bookmarkp-refresh-latest-bookmark-list',
;;    `bookmarkp-regexp-filtered-bookmark-name-alist-only',
;;    `bookmarkp-regexp-filtered-file-name-alist-only',
;;    `bookmarkp-regexp-filtered-tags-alist-only',
;;    `bookmarkp-region-alist-only', `bookmarkp-region-bookmark-p',
;;    `bookmarkp-remote-file-alist-only',
;;    `bookmarkp-remote-file-bookmark-p',
;;    `bookmarkp-remove-assoc-dups', `bookmarkp-remove-dups',
;;    `bookmarkp-remove-if', `bookmarkp-remove-if-not',
;;    `bookmarkp-repeat-command',
;;    `bookmarkp-replace-regexp-in-string',
;;    `bookmarkp-root-or-sudo-logged-p', `bookmarkp-same-file-p',
;;    `bookmarkp-save-menu-list-state',
;;    `bookmarkp-save-new-region-location',
;;    `bookmarkp-sequence-bookmark-p', `bookmarkp-set-union',
;;    `bookmarkp-some', `bookmarkp-some-marked-p',
;;    `bookmarkp-some-unmarked-p' `bookmarkp-sort-and-remove-dups',
;;    `bookmarkp-tag-name', `bookmarkp-unmarked-bookmarks-only',
;;    `bookmarkp-upcase', `bookmarkp-visited-more-cp',
;;    `bookmarkp-w3m-alist-only', `bookmarkp-w3m-bookmark-p',
;;    `bookmarkp-w3m-cp', `bookmarkp-w3m-set-new-buffer-name'.
;;
;;  Internal variables defined here:
;;
;;    `bookmarkp-after-set-hook',
;;    `bookmarkp-bmenu-before-hide-marked-alist',
;;    `bookmarkp-bmenu-before-hide-unmarked-alist',
;;    `bookmarkp-bmenu-define-command-menu',
;;    `bookmarkp-bmenu-filter-function',
;;    `bookmarkp-bmenu-filter-pattern',
;;    `bookmarkp-bmenu-filter-prompt', `bookmarkp-bmenu-filter-timer',
;;    `bookmarkp-bmenu-first-time-p', `bookmarkp-bmenu-header-lines',
;;    `bookmarkp-bmenu-jump-menu', `bookmarkp-bmenu-marked-bookmarks',
;;    `bookmarkp-bmenu-mark-menu', `bookmarkp-bmenu-marks-width',
;;    `bookmarkp-bmenu-menubar-menu', `bookmarkp-bmenu-show-menu',
;;    `bookmarkp-bmenu-sort-menu', `bookmarkp-bmenu-tags-menu',
;;    `bookmarkp-bmenu-title', `bookmarkp-bookmark-list-history',
;;    `bookmarkp-current-bookmark-file', `bookmarkp-desktop-history',
;;    `bookmarkp-dired-history', `bookmarkp-file-history',
;;    `bookmarkp-gnus-history', `bookmarkp-info-history',
;;    `bookmarkp-local-file-history', `bookmarkp-man-history',
;;    `bookmarkp-non-file-history', `bookmarkp-region-history',
;;    `bookmarkp-remote-file-history', `bookmarkp-w3m-history',
;;    `bookmarkp-isearch-bookmarks' (Emacs 23+),
;;    `bookmarkp-jump-display-function', `bookmarkp-jump-map',
;;    `bookmarkp-jump-other-window-map',
;;    `bookmarkp-last-bmenu-bookmark',
;;    `bookmarkp-last-bmenu-state-file',
;;    `bookmarkp-last-save-flag-value',
;;    `bookmarkp-latest-bookmark-alist',
;;    `bookmarkp-non-file-filename', `bookmarkp-reverse-multi-sort-p',
;;    `bookmarkp-reverse-sort-p', `bookmarkp-sorted-alist',
;;    `bookmarkp-tag-history', `bookmarkp-tags-list',
;;    `bookmarkp-types-alist', `bookmarkp-use-w32-browser-p',
;;    `bookmarkp-version-number'.
;;
;;
;;  ***** NOTE: The following commands defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-bmenu-execute-deletions', `bookmark-bmenu-list',
;;    `bookmark-bmenu-mark', `bookmark-bmenu-other-window',
;;    `bookmark-bmenu-rename', `bookmark-bmenu-show-annotation',
;;    `bookmark-bmenu-unmark', `bookmark-delete', `bookmark-insert',
;;    `bookmark-insert-location', `bookmark-jump',
;;    `bookmark-jump-other-window' (Emacs 20-21), `bookmark-load',
;;    `bookmark-relocate', `bookmark-rename', `bookmark-save',
;;    `bookmark-send-edited-annotation', `bookmark-set',
;;    `bookmark-yank-word'.
;;
;;
;;  ***** NOTE: The following non-interactive functions defined in
;;              `bookmark.el' have been REDEFINED HERE:
;;
;;    `bookmark--jump-via', `bookmark-all-names',
;;    `bookmark-bmenu-bookmark', `bookmark-bmenu-check-position',
;;    `bookmark-bmenu-delete', `bookmark-bmenu-ensure-position' (Emacs
;;    23.2+), `bookmark-bmenu-hide-filenames', `bookmark-bmenu-mode',
;;    `bookmark-bmenu-show-filenames',
;;    `bookmark-bmenu-surreptitiously-rebuild-list',
;;    `bookmark-bmenu-switch-other-window' (Emacs 20-22),
;;    `bookmark-completing-read', `bookmark-default-handler',
;;    `bookmark-exit-hook-internal', `bookmark-get-bookmark' (Emacs
;;    20-22), `bookmark-get-bookmark-record' (Emacs 20-22),
;;    `bookmark-get-handler' (Emacs 20-22),
;;    `bookmark-handle-bookmark', `bookmark-jump-noselect' (Emacs
;;    20-22), `bookmark-location', `bookmark-make-record' (Emacs
;;    20-22), `bookmark-make-record-default', `bookmark-maybe-message'
;;    (Emacs 20-21), `bookmark-prop-get' (Emacs 20-22),
;;    `bookmark-prop-set', `bookmark-show-annotation',
;;    `bookmark-show-all-annotations', `bookmark-store' (Emacs 20-22),
;;    `bookmark-write-file'.
;;
;;
;;  ***** NOTE: The following variables defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-alist' (doc string only),
;;    `bookmark-make-record-function' (Emacs 20-22).
;;
;;
;;  ***** NOTE: The following functions defined in `info.el'
;;              have been REDEFINED HERE:
;;
;;    `Info-bookmark-jump' (Emacs 20-22), `Info-bookmark-make-record'
;;    (Emacs 20-22).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;

;;; Code:

(require 'bookmark)
(unless (fboundp 'file-remote-p) (require 'ffap)) ;; ffap-file-remote-p
(eval-when-compile (require 'gnus)) ;; mail-header-id (really in `nnheader.el')
(eval-when-compile (require 'cl)) ;; case


(defconst bookmarkp-version-number "2.7.2")

(defun bookmarkp-version ()
  "Show version number of library `bookmark+.el'."
  (interactive)
  (message "Bookmark+, version %s" bookmarkp-version-number))


;; Quiet the byte-compiler
(defvar bookmark-make-record-function)  ; Defined in `bookmark.el'.
(defvar desktop-buffer-args-list)       ; Defined in `desktop.el'.
(defvar desktop-delay-hook)             ; Defined in `desktop.el'.
(defvar desktop-dirname)                ; Defined in `desktop.el'.
(defvar desktop-file-modtime)           ; Defined in `desktop.el'.
(defvar desktop-globals-to-save)        ; Defined in `desktop.el'.
(defvar desktop-save-mode)              ; Defined in `desktop.el'.
(defvar desktop-save)                   ; Defined in `desktop.el'.
(defvar dired-buffers)                  ; Defined in `dired.el'.
(defvar gnus-article-current)           ; Defined in `gnus-sum.el'.
(defvar Info-current-node)              ; Defined in `info.el'.
(defvar Info-current-file)              ; Defined in `info.el'.
(defvar Man-arguments)                  ; Defined in `man.el'.
(defvar Man-mode-map)                   ; Defined in `man.el'.
(defvar woman-last-file-name)           ; Defined in `woman.el'.
(defvar woman-menu)                     ; Defined in `woman.el'.
(defvar woman-mode-map)                 ; Defined in `woman.el'.
(defvar tramp-file-name-regexp)         ; Defined in `tramp.el'.
(defvar w3m-current-title)              ; Defined in `w3m.el'.
(defvar w3m-current-url)                ; Defined in `w3m.el'.
(defvar w3m-minor-mode-map)             ; Defined in `w3m.el'.
(defvar w3m-mode-map)                   ; Defined in `w3m.el'.

;;;;;;;;;;;;;;;;;;;;;;
 
;;(@* "Macros")
;;; Macros -----------------------------------------------------------

(defmacro bookmarkp-define-sort-command (sort-order comparer doc-string)
  "Define a command to sort bookmarks in the bookmark list by SORT-ORDER.
SORT-ORDER is a short string or symbol describing the sorting method.
Examples: \"by last access time\", \"by bookmark name\".

The new command is named by replacing any spaces in SORT-ORDER with
hyphens (`-') and then adding the prefix `bookmarkp-bmenu-sort-'.
Example: `bookmarkp-bmenu-sort-by-bookmark-name', for SORT-ORDER `by
bookmark name'.

COMPARER compares two bookmarks, returning non-nil if and only if the
first bookmark sorts before the second.  It must be acceptable as a
value of `bookmarkp-sort-comparer'.  That is, it is either nil, a
predicate, or a list ((PRED...) FINAL-PRED).  See the doc for
`bookmarkp-sort-comparer'.

DOC-STRING is the doc string of the new command."
  (unless (stringp sort-order) (setq sort-order  (symbol-name sort-order)))
  (let ((command  (intern (concat "bookmarkp-bmenu-sort-" (bookmarkp-replace-regexp-in-string
                                                           "\\s-+" "-" sort-order)))))
    `(progn
      (setq bookmarkp-sort-orders-alist
       (bookmarkp-assoc-delete-all ,sort-order (copy-sequence bookmarkp-sort-orders-alist)))
      (push (cons ,sort-order ',comparer) bookmarkp-sort-orders-alist)
      (defun ,command ()
        ,(concat doc-string "\nRepeating this command cycles among normal sort, reversed \
sort, and unsorted.")
        (interactive)
        (bookmarkp-barf-if-not-in-menu-list)
        (cond (;; Not this sort order - make it this sort order.
               (not (equal bookmarkp-sort-comparer ',comparer))
               (setq bookmarkp-sort-comparer   ',comparer
                     bookmarkp-reverse-sort-p  nil))
              (;; This sort order reversed.  Change to unsorted.
               bookmarkp-reverse-sort-p
               (setq bookmarkp-sort-comparer   nil))
              (t;; This sort order - reverse it.
               (setq bookmarkp-reverse-sort-p  t)))
        (message "Sorting...")
        (bookmark-bmenu-ensure-position)
        (let ((current-bmk  (bookmark-bmenu-bookmark)))
          (bookmark-bmenu-surreptitiously-rebuild-list)
          (bookmarkp-bmenu-goto-bookmark-named current-bmk)) ; Put cursor back on right line.
        (when (interactive-p)
          (bookmarkp-msg-about-sort-order
           ,sort-order
           nil
           (cond ((and (not bookmarkp-reverse-sort-p)
                       (equal bookmarkp-sort-comparer ',comparer)) "(Repeat: reverse)")
                 ((equal bookmarkp-sort-comparer ',comparer)       "(Repeat: unsorted)")
                 (t                                                "(Repeat: sort)"))))))))

(defmacro bookmarkp-define-file-sort-predicate (att-nb)
  "Define a predicate for sorting bookmarks by file attribute ATT-NB.
See function `file-attributes' for the meanings of the various file
attribute numbers.

String attribute values sort alphabetically; numerical values sort
numerically; nil sorts before t.

For ATT-NB 0 (file type), a file sorts before a symlink, which sorts
before a directory.

For ATT-NB 2 or 3 (uid, gid), a numerical value sorts before a string
value.

A bookmark that has file attributes sorts before a bookmark that does
not.  A file bookmark sorts before a non-file bookmark.  Only local
files are tested for attributes - remote-file bookmarks are treated
here like non-file bookmarks."
  `(defun ,(intern (format "bookmarkp-file-attribute-%d-cp" att-nb)) (b1 b2)
    ,(format "Sort file bookmarks by attribute %d.
B1 and B2 are bookmarks or bookmark names.
Sort bookmarks with file attributes before those without attributes
Sort file bookmarks before non-file bookmarks.
Treat remote file bookmarks like non-file bookmarks."
             att-nb)
    (setq b1  (bookmark-get-bookmark b1))
    (setq b2  (bookmark-get-bookmark b2))
    (let (a1 a2)
      (cond (;; Both are file bookmarks.
             (and (bookmarkp-file-bookmark-p b1)
                  (bookmarkp-file-bookmark-p b2))
             (setq a1  (file-attributes (bookmark-get-filename b1))
                   a2  (file-attributes (bookmark-get-filename b2)))
             (cond (;; Both have attributes.
                    (and a1 a2)
                    (setq a1  (nth ,att-nb a1)
                          a2  (nth ,att-nb a2))
                    ;; Convert times and maybe inode number to floats.
                    ;; The inode conversion is kludgy, but is probably OK in practice.
                    (when (consp a1) (setq a1  (bookmarkp-float-time a1)))
                    (when (consp a2) (setq a2  (bookmarkp-float-time a2)))
                    (cond (;; (1) links, (2) maybe uid, (3) maybe gid, (4, 5, 6) times
                           ;; (7) size, (10) inode, (11) device.
                           (numberp a1)
                           (cond ((< a1 a2) '(t))
                                 ((> a1 a2) '(nil))
                                 (t nil)))
                          ((= 0 ,att-nb) ; (0) file (nil) < symlink (string) < dir (t)
                           (cond ((and a2 (not a1)) '(t)) ; file vs (symlink or dir)
                                 ((and a1 (not a2)) '(nil))
                                 ((and (eq t a2) (not (eq t a1))) '(t)) ; symlink vs dir
                                 ((and (eq t a1) (not (eq t a2))) '(t))
                                 ((and (stringp a1) (stringp a2))
                                  (if (string< a1 a2) '(t) '(nil)))
                                 (t nil)))
                          ((stringp a1) ; (2, 3) string uid/gid, (8) modes
                           (cond ((string< a1 a2) '(t))
                                 ((string< a2 a1) '(nil))
                                 (t nil)))
                          ((eq ,att-nb 9) ; (9) gid would change if re-created. nil < t
                           (cond ((and a2 (not a1)) '(t))
                                 ((and a1 (not a2)) '(nil))
                                 (t nil)))))
                   (;; First has attributes, but not second.
                    a1
                    '(t))
                   (;; Second has attributes, but not first.
                    a2
                    '(nil))
                   (;; Neither has attributes.
                    t
                    nil)))
            (;; First is a file, second is not.
             (bookmarkp-local-file-bookmark-p b1)
             '(t))
            (;; Second is a file, first is not.
             (bookmarkp-local-file-bookmark-p b2)
             '(nil))
            (t;; Neither is a file.
             nil)))))
 
;;(@* "Faces (Customizable)")
;;; Faces (Customizable) ---------------------------------------------

(defface bookmarkp->-mark
    '((t (:background "PaleGreen")))
  "*Face used for a `>' mark in the bookmark list."
  :group 'bookmark-plus)

(defface bookmarkp-a-mark
    '((t (:background "SkyBlue")))
  "*Face used for an annotation mark (`a') in the bookmark list."
  :group 'bookmark-plus)

(defface bookmarkp-bad-bookmark
    '((t (:foreground "Red" :background "Chartreuse1")))
  "*Face used for a bookmark that seems to be bad: e.g., nonexistent file."
  :group 'bookmark-plus)

(defface bookmarkp-bookmark-list
    '((((background dark)) (:foreground "LightGray" :background "DarkRed"))
      (t (:foreground "DarkRed" :background "LightGray")))
  "*Face used for a bookmark-list bookmark."
  :group 'bookmark-plus)

(defface bookmarkp-buffer
    '((((background dark)) (:foreground "green"))
      (t (:foreground "DarkGreen")))
  "*Face used for a bookmarked existing buffer not associated with a file."
  :group 'bookmark-plus)

(defface bookmarkp-D-mark
    '((t (:foreground "Yellow" :background "Red")))
  "*Face used for a deletion mark (`D') in the bookmark list."
  :group 'bookmark-plus)

(defface bookmarkp-desktop
    '((((background dark)) (:foreground "PaleGoldenrod" :background "DarkBlue"))
      (t (:foreground "DarkBlue" :background "PaleGoldenrod")))
  "*Face used for a bookmarked desktop."
  :group 'bookmark-plus)

(defface bookmarkp-function
    '((((background dark)) (:foreground "DeepPink1"))
      (t (:foreground "DeepPink1")))
  "*Face used for a function bookmark: a bookmark that invokes a function."
  :group 'bookmark-plus)

(defface bookmarkp-gnus
    '((((background dark)) (:foreground "Magenta"))
      (t (:foreground "DarkBlue")))
  "*Face used for a gnus bookmark."
  :group 'bookmark-plus)

(defface bookmarkp-info
    '((((background dark)) (:foreground "Green"))
      (t (:foreground "DarkRed")))
  "*Face used for a bookmarked Info node."
  :group 'bookmark-plus)

(defface bookmarkp-local-directory
    '((((background dark)) (:foreground "HoneyDew2" :background "DarkBlue"))
      (t (:foreground "DarkBlue" :background "HoneyDew2")))
  "*Face used for a bookmarked local directory."
  :group 'bookmark-plus)

(defface bookmarkp-local-file-without-region
    '((((background dark)) (:foreground "Blue"))
      (t (:foreground "Black")))
  "*Face used for a bookmarked local file (without a region)."
  :group 'bookmark-plus)

(defface bookmarkp-local-file-with-region
    '((((background dark)) (:foreground "Indianred2"))
      (t (:foreground "Blue")))
  "*Face used for a region bookmark in a local file."
  :group 'bookmark-plus)

(defface bookmarkp-man
    '((((background dark)) (:foreground "Orange4"))
      (t (:foreground "Orange4")))
  "*Face used for a `man' page bookmark."
  :group 'bookmark-plus)

(defface bookmarkp-non-file
    '((((background dark)) (:foreground "gray40"))
      (t (:foreground "gray60")))
  "*Face used for a bookmark not associated with an existing file or buffer."
  :group 'bookmark-plus)

(defface bookmarkp-remote-file
    '((((background dark)) (:foreground "pink"))
      (t (:foreground "DarkViolet")))
  "*Face used for a bookmarked tramp remote file (/ssh:)."
  :group 'bookmark-plus)

(defface bookmarkp-sequence
    '((((background dark)) (:foreground "DarkOrange2"))
      (t (:foreground "DarkOrange2")))
  "*Face used for a sequence bookmark: one composed of other bookmarks."
  :group 'bookmark-plus)

(defface bookmarkp-su-or-sudo
    '((t (:foreground "Red")))
  "*Face used for a bookmarked tramp file (/su: or /sudo:)."
  :group 'bookmark-plus)

(defface bookmarkp-t-mark
    '((t (:background "Pink")))
  "*Face used for a tags mark (`t') in the bookmark list."
  :group 'bookmark-plus)

(defface bookmarkp-w3m
    '((((background dark)) (:foreground "yellow"))
      (t (:foreground "DarkMagenta")))
  "*Face used for a bookmarked w3m url."
  :group 'bookmark-plus)

;; Instead of vanilla `bookmark-menu-heading' (defined in Emacs 22+), to use a better default.
(defface bookmarkp-heading
    '((t (:foreground "Blue")))
  "*Face used to highlight the headings in various Bookmark+ buffers."
  :group 'bookmark-plus :version "22.1")
 
;;(@* "User Options (Customizable)")
;;; User Options (Customizable) --------------------------------------

(defgroup bookmark-plus nil
  "Bookmark enhancements."
  :prefix "bookmarkp-" :group 'bookmark
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
bookmark+.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Download" "http://www.emacswiki.org/bookmark+.el")
  :link '(url-link :tag "Description" "http://www.emacswiki.org/BookmarkPlus")
  :link '(emacs-commentary-link :tag "Commentary" "bookmark+"))

;;;###autoload
(defcustom bookmarkp-bmenu-omitted-list ()
  "List of names of omitted bookmarks.
They are generally not available for display in the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-bmenu-show-only-omitted]' to see them.
You can then mark some of them and use `\\[bookmarkp-bmenu-omit/unomit-marked]'
 to make those that are marked available again for the bookmark list."
  :type '(repeat (string :tag "Bookmark name")) :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-bmenu-commands-file (convert-standard-filename "~/.emacs-bmk-bmenu-commands.el")
  "*File for saving user-defined bookmark-list commands.
This must be an absolute file name or nil (it is not expanded).

You can use `\\[bookmarkp-list-defuns-in-commands-file]' to list the
commands defined in the file and how many times each is defined.

NOTE: Each time you define a command using \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-bmenu-define-command]', `\\[bookmarkp-bmenu-define-full-snapshot-command]', \
`\\[bookmarkp-bmenu-define-jump-marked-command], or `\\[bookmarkp-define-tags-sort-command]',
it is saved in the file.  The new definition is simply appended to the
file - old definitions of the same command are not overwritten.  So
you might want to clean up the file occasionally, to remove any old,
unused definitions.  This is especially advisable if you used \
`\\[bookmarkp-bmenu-define-full-snapshot-command]',
because such command definitions can be very large."
  :type '(file  :tag "File for saving menu-list state") :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-bmenu-state-file (convert-standard-filename "~/.emacs-bmk-bmenu-state.el")
  "*File for saving `*Bookmark List*' state when you quit bookmark list.
This must be an absolute file name or nil (it is not expanded).

The state is also saved when you quit Emacs, even if you don't quit
the bookmark list first (using \\<bookmark-bmenu-mode-map>`\\[bookmarkp-bmenu-quit]').

Set this to nil if you do not want to restore the bookmark list as it
was the last time you used it."
  :type '(choice
          (const :tag "Do not save and restore menu-list state" nil)
          (file  :tag "File for saving menu-list state"))
  :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-desktop-no-save-vars '(search-ring regexp-search-ring kill-ring)
  "List of variables not to save when creating a desktop bookmark.
They are removed from `desktop-globals-to-save' for the duration of
the save (only)."
  :type '(repeat (variable :tag "Variable")) :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-use-region-flag t
  "*Non-nil means visiting a bookmark activates its recorded region."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-region-search-size 40
  "*Same as `bookmark-search-size', but specialized for bookmark regions."
  :type 'integer :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-save-new-location-flag t
  "*Non-nil means save relocated bookmarks.
If nil, then the new bookmark location is visited, but it is not saved
as part of the bookmark definition."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-handle-region-function 'bookmarkp-handle-region-default
  "*Function to handle a bookmarked region."
  :type 'function :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-sequence-jump-display-function 'pop-to-buffer
  "*Function used to display the bookmarks in a bookmark sequence."
  :type 'function :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-su-or-sudo-regexp "\\(/su:\\|/sudo:\\)"
  "*Regexp to recognize `su' or `sudo' Tramp bookmarks."
  :type 'regexp :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-w3m-allow-multi-tabs t
  "*Non-nil means jump to W3M bookmarks in a new session."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-show-end-of-region t
  "*Show end of region with `exchange-point-and-mark' when activating a region.
If nil show only beginning of region."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-bookmark-name-length-max 70
  "*Max number of chars for default name for a bookmark with a region."
  :type 'integer :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-incremental-filter-delay 0.6
  "*Seconds to wait before updating display when filtering bookmarks."
  :type 'integer :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-menu-popup-max-length 20
  "*Max number bookmarks for `bookmark-completing-read' to use a menu.
When choosing a bookmark from a list of bookmarks using
`bookmark-completing-read', this controls whether to use a menu or
minibuffer input with completion.
If t, then always use a menu.
If nil, then never use a menu.
If an integer, then use a menu only if there are fewer bookmark
 choices than the value."
  :type '(choice
          (integer :tag "Use a menu if there are fewer bookmark choices than this" 20)
          (const   :tag "Always use a menu to choose a bookmark" t)
          (const   :tag "Never use a menu to choose a bookmark" nil))
  :group 'bookmark-plus)

;;;###autoload
(defcustom bookmarkp-sort-comparer '((bookmarkp-info-cp bookmarkp-gnus-cp
                                      bookmarkp-w3m-cp bookmarkp-local-file-type-cp)
                                     bookmarkp-alpha-p) ; This corresponds to `s k'.
  ;; $$$$$$ An alternative default value: `bookmarkp-alpha-p', which corresponds to `s n'.
  "*Predicate or predicates for sorting (comparing) bookmarks.
This defines the default sort for bookmarks in the bookmark list.

Various sorting commands, such as \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-bmenu-sort-by-bookmark-visit-frequency]', change the value of this
option dynamically (but they do not save the changed value).

The value must be one of the following:

* nil, meaning do not sort

* a predicate that takes two bookmarks as args

* a list of the form ((PRED...) FINAL-PRED), where each PRED and
  FINAL-PRED are predicates that take two bookmarks as args

If the value is a list of predicates, then each PRED is tried in turn
until one returns a non-nil value.  In that case, the result is the
car of that value.  If no non-nil value is returned by any PRED, then
FINAL-PRED is used and its value is the result.

Each PRED should return `(t)' for true, `(nil)' for false, or nil for
undecided.  A nil value means that the next PRED decides (or
FINAL-PRED, if there is no next PRED).

Thus, a PRED is a special kind of predicate that indicates either a
boolean value (as a singleton list) or \"I cannot decide - let the
next guy else decide\".  (Essentially, each PRED is a hook function
that is run using `run-hook-with-args-until-success'.)

Examples:

 nil           - No sorting.

 string-lessp  - Single predicate that returns nil or non-nil.

 ((p1 p2))     - Two predicates `p1' and `p2', which each return
                 (t) for true, (nil) for false, or nil for undecided.

 ((p1 p2) string-lessp)
               - Same as previous, except if both `p1' and `p2' return
                 nil, then the return value of `string-lessp' is used.

Note that these two values are generally equivalent, in terms of their
effect (*):

 ((p1 p2))
 ((p1) p2-plain) where p2-plain is (bookmarkp-make-plain-predicate p2)

Likewise, these three values generally act equivalently (*):

 ((p1))
 (() p1-plain)
 p1-plain        where p1-plain is (bookmarkp-make-plain-predicate p1)

The PRED form lets you easily combine predicates: use `p1' unless it
cannot decide, in which case try `p2', and so on.  The value ((p2 p1))
tries the predicates in the opposite order: first `p2', then `p1' if
`p2' returns nil.

Using a single predicate or FINAL-PRED makes it easy to reuse an
existing predicate that returns nil or non-nil.

You can also convert a PRED-type predicate (which returns (t), (nil),
or nil) into an ordinary predicate, by using function
`bookmarkp-make-plain-predicate'.  That lets you reuse elsewhere, as
ordinary predicates, any PRED-type predicates you define.

For example, this defines a plain predicate to compare by W3M URL:
 (defalias 'bookmarkp-w3m-p
           (bookmarkp-make-plain-predicate 'bookmarkp-w3m-cp))

Note: As a convention, predefined Bookmark+ PRED-type predicate names
have the suffix `-cp' (for \"component predicate\") instead of `-p'.

--
* If you use `\\[bookmarkp-reverse-multi-sort-order]', then there is a difference in \
behavior between

   (a) using a plain predicate as FINAL-PRED and
   (b) using the analogous PRED-type predicate (and no FINAL-PRED).

  In the latter case, `\\[bookmarkp-reverse-multi-sort-order]' affects when the predicate \
is tried and
  its return value.  See `bookmarkp-reverse-multi-sort-order'."
  :type '(choice
          (const    :tag "None (do not sort)" nil)
          (function :tag "Sorting Predicate")
          (list     :tag "Sorting Multi-Predicate"
           (repeat (function :tag "Component Predicate"))
           (choice
            (const    :tag "None" nil)
            (function :tag "Final Predicate"))))
  :group 'bookmark-plus)

;;;###autoload
(when (> emacs-major-version 20)
  (defcustom bookmarkp-sort-orders-alist ()
    "*Alist of all available sort functions.
This is a pseudo option - you probably do NOT want to customize this.
Instead:

 * To add a new sort function to this list, use macro
   `bookmarkp-define-sort-command'.  It defines a new sort function
   and automatically adds it to this list.

 * To have fewer sort orders available for cycling by \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-bmenu-change-sort-order-repeat]'...,
   customize option `bookmarkp-sort-orders-for-cycling-alist'.

Each alist element has the form (SORT-ORDER . COMPARER):

 SORT-ORDER is a short string or symbol describing the sort order.
 Examples: \"by last access time\", \"by bookmark name\".

 COMPARER compares two bookmarks.  It must be acceptable as a value of
 `bookmarkp-sort-comparer'."
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

;;;###autoload
(unless (> emacs-major-version 20)      ; Emacs 20: custom type `alist' doesn't exist.
  (defcustom bookmarkp-sort-orders-alist ()
    "*Alist of all available sort functions.
This is a pseudo option - you probably do NOT want to customize this.
Instead:

 * To add a new sort function to this list, use macro
   `bookmarkp-define-sort-command'.  It defines a new sort function
   and automatically adds it to this list.

 * To have fewer sort orders available for cycling by \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-bmenu-change-sort-order-repeat]'...,
   customize option `bookmarkp-sort-orders-for-cycling-alist'.

Each alist element has the form (SORT-ORDER . COMPARER):

 SORT-ORDER is a short string or symbol describing the sort order.
 Examples: \"by last access time\", \"by bookmark name\".

 COMPARER compares two bookmarks.  It must be acceptable as a value of
 `bookmarkp-sort-comparer'."
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
 
;;(@* "Internal Variables")
;;; Internal Variables --------------------------------------------------

(defconst bookmarkp-non-file-filename "   - no file -"
  "Name to use for `filename' entry, for non-file bookmarks.")

(defconst bookmarkp-bmenu-header-lines 2
  "Number of lines used for the `*Bookmark List*' header.")

(defconst bookmarkp-bmenu-marks-width 4
  "Number of columns (chars) used for the `*Bookmark List*' marks columns.")

(defconst bookmarkp-types-alist '(("bookmark-list" . bookmarkp-bookmark-list-history)
                                  ("desktop"       . bookmarkp-desktop-history)
                                  ("dired"         . bookmarkp-dired-history)
                                  ("file"          . bookmarkp-file-history)
                                  ("gnus"          . bookmarkp-gnus-history)
                                  ("info"          . bookmarkp-info-history)
                                  ("local-file"    . bookmarkp-local-file-history)
                                  ("man"           . bookmarkp-man-history)
                                  ("non-file"      . bookmarkp-non-file-history)
                                  ("region"        . bookmarkp-region-history)
                                  ("remote-file"   . bookmarkp-remote-file-history)
                                  ("w3m"           . bookmarkp-w3m-history))
  "Alist of bookmark types.
Keys are bookmark type names.  Values are corresponding history variables.")

(defvar bookmarkp-bookmark-list-history () "History for bookmark-list bookmarks.")
(defvar bookmarkp-desktop-history ()       "History for desktop bookmarks.")
(defvar bookmarkp-dired-history ()         "History for Dired bookmarks.")
(defvar bookmarkp-file-history ()          "History for file bookmarks.")
(defvar bookmarkp-gnus-history ()          "History for Gnus bookmarks.")
(defvar bookmarkp-info-history ()          "History for Info bookmarks.")
(defvar bookmarkp-local-file-history ()    "History for local-file bookmarks.")
(defvar bookmarkp-man-history ()           "History for `man'-page bookmarks.")
(defvar bookmarkp-non-file-history ()      "History for buffer (non-file) bookmarks.")
(defvar bookmarkp-region-history ()        "History for bookmarks that activate the region.")
(defvar bookmarkp-remote-file-history ()   "History for remote-file bookmarks.")
(defvar bookmarkp-w3m-history ()           "History for W3M bookmarks.")

(defvar bookmarkp-after-set-hook nil
  "Hook run after `bookmark-set' sets a bookmark.")

(defvar bookmarkp-current-bookmark-file bookmark-default-file
  "Current bookmark file.
When you start Emacs, this is the same as `bookmark-default-file'.
When you load bookmarks using `bookmarkp-switch-bookmark-file', this
is set to the file you load.  When you save bookmarks using
`bookmark-save' with no prefix arg, they are saved to this file.

Note: The value of `bookmark-default-file' is never changed, except by
your customizations.  Each Emacs session uses `bookmark-default-file'
for the initial set of bookmarks.")

(defvar bookmarkp-jump-display-function nil
  "Function used currently to display a bookmark.")

(defvar bookmarkp-reverse-sort-p nil
  "Non-nil means the sort direction is reversed.")

(defvar bookmarkp-reverse-multi-sort-p nil
  "Non-nil means the truth values returned by predicates are complemented.
This changes the order of the sorting groups, but it does not in
general reverse that order.  The order within each group is unchanged
\(not reversed).")

(defvar bookmarkp-use-w32-browser-p nil
  "Non-nil means use `w32-browser' in the default bookmark handler.
That is, use the default Windows application for the bookmarked file.
This has no effect if `w32-browser' is not defined.")

(defvar bookmarkp-latest-bookmark-alist ()
  "Copy of `bookmark-alist' as last filtered.")

(defvar bookmarkp-bmenu-marked-bookmarks ()
  "Names of the marked bookmarks.
This includes possibly omitted bookmarks, that is, bookmarks listed in
`bookmarkp-bmenu-omitted-list'.")

(defvar bookmarkp-bmenu-before-hide-unmarked-alist ()
  "Copy of `bookmark-alist' made before hiding unmarked bookmarks.")

(defvar bookmarkp-bmenu-before-hide-marked-alist ()
  "Copy of `bookmark-alist' made before hiding marked bookmarks.")

(defvar bookmarkp-bmenu-filter-function  nil
  "Latest filtering function for `*Bookmark List*' display.")

(defvar bookmarkp-bmenu-title ""
  "Latest title for `*Bookmark List*' display.")

(defvar bookmarkp-bmenu-filter-pattern ""
  "Regexp for incremental filtering.")

(defvar bookmarkp-bmenu-filter-prompt "Pattern: "
  "Prompt for `bookmarkp-bmenu-filter-incrementally'.")

(defvar bookmarkp-bmenu-filter-timer nil
  "Timer used for incremental filtering.")

(defvar bookmarkp-bmenu-first-time-p t
  "Non-nil means bookmark list has not yet been shown after quitting it.
Quitting the list or the Emacs session resets this to t.
The first time the list is displayed, it is set to nil.")

(defvar bookmarkp-last-bmenu-bookmark nil
  "The name of the last bookmark current in the bookmark list.")

(defvar bookmarkp-last-bmenu-state-file nil
  "Last value of option `bookmarkp-bmenu-state-file'.")

(defvar bookmarkp-last-save-flag-value nil
  "Last value of option `bookmark-save-flag'.")

(defvar bookmarkp-sorted-alist ()
  "Copy of current bookmark alist, as sorted for buffer `*Bookmark List*'.
Has the same structure as `bookmark-alist'.")

(defvar bookmarkp-tag-history ()
  "History of tags read from the user.")

(defvar bookmarkp-tags-alist ()         
  "Alist of all tags, from all bookmarks.
Each entry is a cons whose car is a tag name, a string.
This is set by function `bookmarkp-tags-list'.
Use that function to update the value.")


;; REPLACES ORIGINAL DOC STRING in `bookmark.el'.
;;
;; Doc string reflects Bookmark+ enhancements.
;;
(put 'bookmark-alist 'variable-documentation
     "Association list of bookmarks and their records.
Bookmark functions update the value automatically.
You probably do not want to change the value yourself.

The value is an alist with entries of the form
 (BOOKMARK-NAME . PARAM-ALIST)
or the deprecated form (BOOKMARK-NAME PARAM-ALIST).

 BOOKMARK-NAME is the name you gave to the bookmark when creating it.
 PARAM-ALIST is an alist of bookmark information.  The order of the
  entries in PARAM-ALIST is not important.  The possible entries are
  described below.  An entry with a key but null value means the entry
  is not used.

Bookmarks created using vanilla Emacs (`bookmark.el'):

 (filename . FILENAME)
 (position . POS)
 (front-context-string . STR-AFTER-POS)
 (rear-context-string  . STR-BEFORE-POS)
 (handler . HANDLER)
 (annotation . ANNOTATION)

 FILENAME names the bookmarked file.
 POS is the bookmarked buffer position (position in the file).
 STR-AFTER-POS is buffer text that immediately follows POS.
 STR-BEFORE-POS is buffer text that immediately precedes POS.
 ANNOTATION is a string that you can provide to identify the bookmark.
  See options `bookmark-use-annotations' and
  `bookmark-automatically-show-annotations'.
 HANDLER is a function that provides the bookmark-jump behavior
  for a specific kind of bookmark.  This is the case for Info
  bookmarks, for instance (starting with Emacs 23).

Bookmarks created using Bookmark+ are the same as for vanilla Emacs,
except for the following differences.

1. Visit information is recorded, using entries `visits' and `time':

 (visits . NUMBER-OF-VISITS)
 (time . TIME-LAST-VISITED)

 NUMBER-OF-VISITS is a whole-number counter.

 TIME-LAST-VISITED is an Emacs time representation, such as is
 returned by function `current-time'.

2. Bookmarks can be tagged by users.  The tag information is recorded
using entry `tags':

 (tags . TAGS-ALIST)

 TAGS-ALIST is an alist with string keys. 

3. If no file is associated with the bookmark, then FILENAME is
   `   - no file -'.

4. The following additional entries are used to record region
information.  The values are non-nil only when a region is bookmarked.
When a region is bookmarked, POS represents the region start position.

 (buffer-name . BUFFER-NAME)
 (end-position . END-POS)
 (front-context-region-string . STR-BEFORE-END-POS)
 (rear-context-region-string . STR-AFTER-END-POS))

 BUFFER-NAME is the name of a bookmarked buffer, which might not be
  associated with any file (see #1).
 END-POS is the region end position.
 STR-BEFORE-END-POS is buffer text that precedes END-POS.
 STR-AFTER-END-POS is buffer text that follows END-POS.

 NOTE: The relative locations of `front-context-region-string' and
 `rear-context-region-string' are reversed from those of
 `front-context-string' and `rear-context-string'.  For example,
 `front-context-string' is the text that *follows* `position', but
 `front-context-region-string' that *precedes* `end-position'.

5. The following additional entries are used for a Dired bookmark.

 (dired-marked . MARKED-FILES)
 (dired-switches . SWITCHES)

 MARKED-FILES is the list of files that were marked.
 SWITCHES is the string of `dired-listing-switches'.

6. The following additional entries are used for a Gnus bookmark.

 (group . GNUS-GROUP-NAME)
 (article . GNUS-ARTICLE-NUMBER)
 (message-id . GNUS-MESSAGE-ID)

 GNUS-GROUP-NAME is the name of a Gnus group.
 GNUS-ARTICLE-NUMBER is the number of a Gnus article.
 GNUS-MESSAGE-ID is the identifier of a Gnus message.

7. For a W3M bookmark, FILENAME is a W3M URL.

8. A sequence bookmark has this additional entry:

 (sequence . COMPONENT-BOOKMARKS)

 COMPONENT-BOOKMARKS is the list of component bookmark names.

9. A function bookmark has this additional entry, which records the
FUNCTION:

 (function . FUNCTION)

10. A bookmark-list bookmark has this additional entry, which records
the state of buffer `*Bookmark List*' at the time it is created:

 (bookmark-list . STATE)

 STATE records the sort order, filter function, omit list, and title.")
 
;;(@* "Compatibility Code for Older Emacs Versions")
;;; Compatibility Code for Older Emacs Versions ----------------------

;;;###autoload
(when (< emacs-major-version 23)

  ;; These definitions are for Emacs versions prior to Emacs 23.
  ;; They are the same as the vanilla Emacs 23+ definitions, except as noted.
  ;; They let older versions of Emacs handle bookmarks created with Emacs 23.

  ;; 1. Handle the shouldn't-happen case of non-string, non-cons.
  ;; 2. Document NOERROR in doc string.
  (defun bookmark-get-bookmark (bookmark &optional noerror)
    "Return the bookmark record corresponding to BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If BOOKMARK is already a bookmark record, just return it.
Otherwise look for the corresponding bookmark in `bookmark-alist'.

Non-nil optional arg NOERROR means return nil if BOOKMARK
is not a valid bookmark - do not raise an error."
    (cond ((consp bookmark) bookmark)
          ((stringp bookmark)
           (or (if (fboundp 'assoc-string) ; Emacs 22+.
                   (assoc-string bookmark bookmark-alist bookmark-completion-ignore-case)
                 (assoc bookmark bookmark-alist))
               (unless noerror (error "Invalid bookmark: `%s'" bookmark))))
          (t (unless noerror (error "Invalid bookmark: `%s'" bookmark)))))

  (defun bookmark-get-bookmark-record (bookmark)
    "Return the guts of the entry for BOOKMARK in `bookmark-alist'.
That is, all information but the name.
BOOKMARK is a bookmark name or a bookmark record."
    (let ((alist  (cdr (bookmark-get-bookmark bookmark))))
      ;; The bookmark objects can either look like (NAME ALIST) or
      ;; (NAME . ALIST), so we have to distinguish the two here.
      (if (and (null (cdr alist)) (consp (caar alist)))
          (car alist)
        alist)))

  (defun Info-bookmark-make-record ()
    "Create an Info bookmark record."
    `(,Info-current-node
      ,@(bookmark-make-record-default 'point-only)
      (filename . ,Info-current-file)
      (info-node . ,Info-current-node)
      (handler . Info-bookmark-jump)))

  ;; Requires `info.el' explicitly (not autoloaded for `Info-find-node'.
  (defun Info-bookmark-jump (bookmark)
    "Jump to Info bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
    (require 'info)
    ;; Implements the `handler' for the record type returned by `Info-bookmark-make-record'.
    (let* ((file       (bookmark-prop-get bookmark 'filename))
           (info-node  (bookmark-prop-get bookmark 'info-node))
           (buf        (save-window-excursion ; VANILLA EMACS FIXME: doesn't work with frames!
                         (Info-find-node file info-node) (current-buffer))))
      ;; Use `bookmark-default-handler' to move to appropriate location within Info node.
      (bookmark-default-handler
       `("" (buffer . ,buf) . ,(bookmark-get-bookmark-record bookmark)))))

  (add-hook 'Info-mode-hook (lambda () (set (make-local-variable 'bookmark-make-record-function)
                                            'Info-bookmark-make-record)))

  (defvar bookmark-make-record-function 'bookmark-make-record-default
    "Function called with no arguments, to create a bookmark record.
It should return the new record, which should be a cons cell of the
form (NAME . ALIST) or just ALIST, where ALIST is as described in
`bookmark-alist'.  If it cannot construct the record, then it should
raise an error.

NAME is a string that names the new bookmark.  NAME can be nil, in
which case a default name is used.

ALIST can contain an entry (handler . FUNCTION) which sets the handler
to FUNCTION, which is then used instead of `bookmark-default-handler'.
FUNCTION must accept the same arguments as `bookmark-default-handler'.

You can set this variable buffer-locally to enable bookmarking of
locations that should be treated specially, such as Info nodes, news
posts, images, pdf documents, etc.")

  (defun bookmark-make-record ()
    "Return a new bookmark record (NAME . ALIST) for the current location."
    (let ((record  (funcall bookmark-make-record-function)))
      ;; Set up default name.
      (if (stringp (car record))
          record                        ; The function already provided a default name.
        (when (car record) (push nil record))
        (setcar record  (or bookmark-current-bookmark (bookmark-buffer-name)))
        record)))

  (defun bookmark-store (bookmark-name alist no-overwrite)
    "Store the bookmark named BOOKMARK-NAME, giving it data ALIST.
If NO-OVERWRITE is non-nil and another bookmark of the same name already
exists in `bookmark-alist', then record the new bookmark but do not
discard the old one."
    (bookmark-maybe-load-default-file)
    (let ((stripped-name  (copy-sequence bookmark-name)))
      (unless (featurep 'xemacs)
        (set-text-properties 0 (length stripped-name) () stripped-name))
      (if (and (not no-overwrite) (bookmark-get-bookmark stripped-name 'noerror))
          ;; Existing bookmark under that name and no prefix arg means just overwrite old.
          ;; Use the new (NAME . ALIST) format.
          (setcdr (bookmark-get-bookmark stripped-name) alist)
        (push (cons stripped-name alist) bookmark-alist))
      (bookmarkp-maybe-save-bookmarks)
      (setq bookmark-current-bookmark  stripped-name)
      (bookmark-bmenu-surreptitiously-rebuild-list)))

  (defun bookmark-prop-get (bookmark prop)
    "Return property PROP of BOOKMARK, or nil if no such property.
BOOKMARK is a bookmark name or a bookmark record."
    (cdr (assq prop (bookmark-get-bookmark-record bookmark))))

  (defun bookmark-get-handler (bookmark)
    "Return the `handler' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
    (bookmark-prop-get bookmark 'handler))

  (defun bookmark-jump-noselect (bookmark)
    "Return the location recorded for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
The return value has the form (BUFFER . POINT), where BUFFER is a
buffer and POINT is the location within BUFFER."
    (save-excursion (bookmark-handle-bookmark bookmark) (cons (current-buffer) (point)))))

;;;###autoload
(when (< emacs-major-version 22)

  ;; These definitions are for Emacs versions prior to Emacs 22.
  ;; They are the same as the vanilla Emacs 22+ definitions, except as noted.

  ;; Emacs 22+ just uses `bookmark-jump-other-window' for the menu also.
  (defun bookmarkp-menu-jump-other-window (event)
    "Jump to BOOKMARK (a point in some file) in another window.
See `bookmark-jump-other-window'."
    (interactive "e")
    (bookmark-popup-menu-and-apply-function 'bookmark-jump-other-window
                                            "Jump to Bookmark (Other Window)" event))

  (defun bookmark-maybe-message (fmt &rest args)
    "Apply `message' to FMT and ARGS, but only if the display is fast enough."
    (when (>= baud-rate 9600) (apply 'message fmt args))))

;;;###autoload
(when (< emacs-major-version 23)
  (defun bookmark-bmenu-switch-other-window ()
    "Make the other window select this line's bookmark.
The current window remains selected."
    (interactive)
    (let ((bookmark (bookmark-bmenu-bookmark))
          (pop-up-windows t)
          same-window-buffer-names
          same-window-regexps)
      (bookmark-bmenu-check-position)
      (let ((bookmark-automatically-show-annotations  t)) ; VANILLA Emacs FIXME: needed?
        (bookmark--jump-via bookmark 'display-buffer)))))
 
;;(@* "Core Replacements (`bookmark-*' except `bookmark-bmenu-*')")
;;; Core Replacements (`bookmark-*' except `bookmark-bmenu-*') -------


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. BUG fix: Put point back where it was (on the bookmark just annotated).
;; 2. Refresh menu list, to pick up the `a' marker.
;;
(defun bookmark-send-edited-annotation ()
  "Use buffer contents as annotation for a bookmark.
Lines beginning with `#' are ignored."
  (interactive)
  (unless (eq major-mode 'bookmark-edit-annotation-mode)
    (error "Not in bookmark-edit-annotation-mode"))
  (goto-char (point-min))
  (while (< (point) (point-max))
    (if (looking-at "^#")
        (bookmark-kill-line t)
      (forward-line 1)))
  (let ((annotation  (buffer-substring-no-properties (point-min) (point-max)))
	(bookmark    bookmark-annotation-name))
    (bookmark-set-annotation bookmark annotation)
    (setq bookmark-alist-modification-count
          (1+ bookmark-alist-modification-count))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (kill-buffer (current-buffer))
    (pop-to-buffer "*Bookmark List*")
    (bookmarkp-refresh-menu-list bookmark))) ; So the `a' marker is displayed (updated).


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Added optional arg ALIST.
;;
(defun bookmark-all-names (&optional alist)
  "Return a list of all bookmark names.
The names are those of the bookmarks in ALIST or, if nil,
`bookmark-alist'."
  (bookmark-maybe-load-default-file)
  (mapcar (lambda (bmk) (bookmark-name-from-full-record bmk)) (or alist bookmark-alist)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional args ALIST and PRED.
;; 2. Bind `icicle-delete-candidate-object' to `bookmark-delete'.
;;
(defun bookmark-completing-read (prompt &optional default alist pred hist)
  "Read a bookmark name, prompting with PROMPT.
PROMPT is automatically suffixed with \": \", so do not include that.

Optional arg DEFAULT is a string to return if the user enters the
 empty string.
The alist argument used for completion is ALIST or, if nil,
 `bookmark-alist'.
Optional arg PRED is a predicate used for completion.
Optional arg HIST is a history variable for completion.  Default is
 `bookmark-history'.

If you access this function from a menu, then, depending on the value
of option `bookmarkp-menu-popup-max-length' and the number of
bookmarks in ALIST, you choose the bookmark using a menu or using
completion.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (bookmark-maybe-load-default-file)
  (setq alist  (or alist bookmark-alist))
  (if (and (listp last-nonmenu-event)
           (or (eq t bookmarkp-menu-popup-max-length)
               (and (integerp bookmarkp-menu-popup-max-length)
                    (< (length alist) bookmarkp-menu-popup-max-length))))
      (bookmark-menu-popup-paned-menu
       t prompt
       (if bookmarkp-sort-comparer      ; Test whether to sort, but always use `string-lessp'.
           (sort (bookmark-all-names alist) 'string-lessp)
         (bookmark-all-names alist)))
    (let* ((icicle-delete-candidate-object  'bookmark-delete) ; For `S-delete'.
           (completion-ignore-case          bookmark-completion-ignore-case)
           (default                         default)
           (prompt                          (if default
                                                (concat prompt (format " (%s): " default))
                                              (concat prompt ": ")))
           (str                             (completing-read prompt alist pred 0 nil
                                                             (or hist 'bookmark-history))))
      (if (string-equal "" str) default str))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Handles also regions and non-file buffers.
;;
(defun bookmark-make-record-default (&optional point-only)
  "Return the record describing the location of a new bookmark.
Point must be where the bookmark is to be set.
If POINT-ONLY is non-nil, return only the subset of the record that
pertains to the location within the buffer."
  (let* ((dired-p  (and (boundp 'dired-buffers) (car (rassq (current-buffer) dired-buffers))))
         (buf      (buffer-name))
         (ctime    (current-time))

         ;; Begin `let*' dependencies.
         (regionp  (and transient-mark-mode mark-active (not (eq (mark) (point)))))
         (beg      (if regionp (region-beginning) (point)))
         (end      (if regionp (region-end) (point)))
         (fcs      (if regionp
                       (bookmarkp-position-post-context-region beg end)
                     (bookmarkp-position-post-context beg)))
         (rcs      (if regionp
                       (bookmarkp-position-pre-context-region beg)
                     (bookmarkp-position-pre-context beg)))
         (fcrs     (when regionp (bookmarkp-end-position-pre-context beg end)))
         (ecrs     (when regionp (bookmarkp-end-position-post-context end))))
    `(,@(unless point-only `((filename . ,(cond ((buffer-file-name (current-buffer))
                                                 (bookmark-buffer-file-name))
                                                (dired-p  nil)
                                                (t        bookmarkp-non-file-filename)))))
      (buffer-name                 . ,buf)
      (front-context-string        . ,fcs)
      (rear-context-string         . ,rcs)
      (front-context-region-string . ,fcrs)
      (rear-context-region-string  . ,ecrs)
      (visits                      . 0)
      (time                        . ,ctime)
      (created                     . ,ctime)
      (position                    . ,beg)
      (end-position                . ,end))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `bookmark-make-record'.
;; 2. Use special default prompts for active region, W3M, and Gnus.
;;
(defun bookmark-set (&optional name parg) ; `C-x r m'
  "Set a bookmark named NAME, then run `bookmarkp-after-set-hook'.
If the region is active (`transient-mark-mode') and nonempty, then
record the region limits in the bookmark.

If NAME is nil, then prompt for the bookmark name.  The default name
for prompting is as follows (in order of priority):

 * If the region is active and nonempty, then the buffer name followed
   by \": \" and the region prefix (up to
   `bookmarkp-bookmark-name-length-max' chars).

 * If in W3M mode, then the current W3M title.

 * If in Gnus Summary mode, then the Gnus summary article header.

 * If on a `man' page, then the page name (command and section).

 * Otherwise, the current buffer name.

While entering a bookmark name at the prompt:

 * You can use `C-w' to yank words from the buffer to the minibuffer.
   Repeating `C-w' yanks successive words.

 * You can use `C-u' to insert the name of the last bookmark used in
   the buffer.  This can be useful as an aid to track your progress
   through a large file.  (If no bookmark has yet been used, then
   `C-u' inserts the name of the visited file.)

With a prefix argument, do not overwrite a bookmark that has the same
name as NAME, if such a bookmark already exists.  Instead, push the
new bookmark onto the bookmark alist.

The most recently set bookmark named NAME is thus the one in effect at
any given time, but any others named NAME are still available, should
you decide to delete the most recent one.

Use `\\[bookmark-delete]' to remove bookmarks (you give it a name, and it removes
only the first instance of a bookmark with that name from the list of
bookmarks)."
  (interactive (list nil current-prefix-arg))
  (bookmark-maybe-load-default-file)
  (setq bookmark-current-point   (point)
        bookmark-current-buffer  (current-buffer))
  (save-excursion (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
  (let* ((record   (bookmark-make-record))
         (regionp  (and transient-mark-mode mark-active (not (eq (mark) (point)))))
         (regname  (concat (buffer-name) ": "
                           (buffer-substring (if regionp (region-beginning) (point))
                                             (if regionp
                                                 (region-end)
                                               (save-excursion (end-of-line) (point))))))
         (defname  (bookmarkp-replace-regexp-in-string
                    "\n" " "
                    (cond (regionp
                           (save-excursion
                             (goto-char (region-beginning))
                             (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
                           (substring regname 0 (min bookmarkp-bookmark-name-length-max
                                                     (length regname))))
                          ((eq major-mode 'w3m-mode) w3m-current-title)
                          ((eq major-mode 'gnus-summary-mode) (elt (gnus-summary-article-header) 1))
                          ((memq major-mode '(Man-mode woman-mode))
                           (buffer-substring (point-min) (save-excursion
                                                           (goto-char (point-min))
                                                           (skip-syntax-forward "^ ")
                                                           (point))))
                          (t (car record)))))
         (doc-cmd  "`\\<minibuffer-local-map>\\[next-history-element]' \ for default")
         (bname    (or name
                       (read-from-minibuffer
                        (format "Set bookmark (%s): " (if (> emacs-major-version 21)
                                                          (substitute-command-keys doc-cmd)
                                                        defname))
                        nil
                        (let ((map  (copy-keymap minibuffer-local-map)))
                          (define-key map "\C-w" 'bookmark-yank-word)
                          (define-key map "\C-u" 'bookmark-insert-current-bookmark)
                          map)
                        nil nil defname))))
    (when (string-equal bname "") (setq bname  defname))
    (bookmark-store bname (cdr record) parg)
    (run-hooks 'bookmarkp-after-set-hook)
    (if bookmark-use-annotations
        (bookmark-edit-annotation bname)
      (goto-char bookmark-current-point))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Prevent adding a newline in a bookmark name when yanking.
;; 
;;;###autoload
(defun bookmark-yank-word ()            ; `C-w' in minibuffer when setting bookmark.
  "Yank the word at point in `bookmark-current-buffer'.
Repeat to yank subsequent words from the buffer, appending them.
Newline characters are stripped out."
  (interactive)
  (let ((string  (with-current-buffer bookmark-current-buffer
                   (goto-char bookmark-yank-point)
                   (buffer-substring-no-properties
                    (point)
                    (progn (forward-word 1) (setq bookmark-yank-point  (point)))))))
    (setq string  (bookmarkp-replace-regexp-in-string "\n" "" string))
    (insert string)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Save DISPLAY-FUNCTION to `bookmarkp-jump-display-function' before calling
;; `bookmark-handle-bookmark'.
;;
(defun bookmark--jump-via (bookmark display-function)
  "Display BOOKMARK using DISPLAY-FUNCTION.
Then run `bookmark-after-jump-hook' and show annotations for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmarkp-record-visit bookmark 'batch)
  (setq bookmarkp-jump-display-function  display-function)
  (bookmark-handle-bookmark bookmark)
  (let ((win  (get-buffer-window (current-buffer) 0)))
    (when win (set-window-point win (point))))
  ;; VANILLA EMACS FIXME: we used to only run `bookmark-after-jump-hook' in
  ;; `bookmark-jump' itself, but in none of the other commands.
  (run-hooks 'bookmark-after-jump-hook)
  (let ((jump-fn  (bookmarkp-get-tag-value bookmark "bookmarkp-jump")))
    (when jump-fn (funcall jump-fn)))
  (when bookmark-automatically-show-annotations (bookmark-show-annotation bookmark)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add to beginning, not end, of bookmark record.
;; 2. Do not use `nconc'.
;; 3. Respect both old and new bookmark formats.
;;
(defun bookmark-prop-set (bookmark prop val)
  "Set the property PROP of BOOKMARK to VAL."
  (let* ((bmk   (bookmark-get-bookmark bookmark))
         (cell  (assq prop (bookmark-get-bookmark-record bmk))))
    (if cell
        (setcdr cell val)
      (if (consp (car (cadr bmk)))      ; Old format: ("name" ((filename . "f")...))
          (setcdr bmk (list (cons (cons prop val) (cadr bmk))))
        (setcdr bmk (cons (cons prop val) (cdr bmk))))))) ; New: ("name" (filename . "f")...)


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg USE-REGION-P.
;; 2. Use `bookmarkp-default-bookmark-name' as default when interactive.
;; 3. Use `bookmarkp-jump-1'.
;; 4. Added note about Icicles `S-delete' to doc string.
;;
;;;###autoload
(defun bookmark-jump (bookmark-name &optional use-region-p) ; `C-x j j', `C-x r b', `C-x p g'
  "Jump to the bookmark named BOOKMARK-NAME.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If the file pointed to by BOOKMARK-NAME no longer exists, you are
asked if you wish to give the bookmark a new location.  If so,
`bookmark-jump' jumps to the new location and saves it.

If the bookmark defines a region, then the region is activated if
`bookmarkp-use-region-flag' is not-nil or it is nil and you use a
prefix argument.  A prefix arg temporarily flips the value of
`bookmarkp-use-region-flag'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Jump to bookmark" (bookmarkp-default-bookmark-name))
                     current-prefix-arg))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg USE-REGION-P.
;; 2. Use `bookmarkp-default-bookmark-name' as default when interactive.
;; 3. Use `bookmarkp-jump-1'.
;;
;;;###autoload
(defun bookmark-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j j', `C-x p o'
  "Jump to the bookmark named BOOKMARK-NAME, in another window.
See `bookmark-jump', in particular for info about using a prefix arg."
  (interactive (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                               (bookmarkp-default-bookmark-name))
                     current-prefix-arg))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Different relocation message for non-file bookmark.
;;
(defun bookmark-handle-bookmark (bookmark)
  "Call BOOKMARK's handler, or `bookmark-default-handler' if it has none.
Changes the current buffer and point.
Returns nil or signals a `file-error'.
BOOKMARK can be a bookmark record used internally by some Emacs-Lisp
 package, or the name of a bookmark in `bookmark-alist'."
  (condition-case err
      (funcall (or (bookmark-get-handler bookmark) 'bookmark-default-handler)
               (bookmark-get-bookmark bookmark))
    (file-error
     ;; We were unable to find the marked file, so ask if user wants to
     ;; relocate the bookmark, else remind them to consider deletion.
     (when (stringp bookmark)
       ;; BOOKMARK can be either a bookmark name (found in `bookmark-alist') or a bookmark
       ;; object.  If an object, assume it's a bookmark used internally by some other package.
       (let ((file  (bookmark-get-filename bookmark)))
         (when file                     ; Don't know how to relocate if file doesn't exist.
           (unless (string= file bookmarkp-non-file-filename) (setq file  (expand-file-name file)))
           (ding)
           (cond ((y-or-n-p (if (and (string= file bookmarkp-non-file-filename)
                                     (bookmarkp-get-buffer-name bookmark))
                                "Bookmark's buffer doesn't exist.  Re-create it? "
                              (concat (file-name-nondirectory file) " nonexistent.  Relocate \""
                                      bookmark "\"? ")))
                  (if (string= file bookmarkp-non-file-filename)
                      ;; This is not likely the right way to get the correct buffer, but it's
                      ;; better than nothing, and it gives the user a chance to DTRT.
                      (pop-to-buffer (bookmarkp-get-buffer-name bookmark)) ; Create buffer.
                    (bookmark-relocate bookmark)) ; Relocate to file.
                  (funcall (or (bookmark-get-handler bookmark) 'bookmark-default-handler)
                           (bookmark-get-bookmark bookmark))) ; Try again
                 (t
                  (message "Bookmark not relocated \(%s\)" bookmark)
                  (signal (car err) (cdr err)))))))))
  (when (stringp bookmark) (setq bookmark-current-bookmark  bookmark))
  nil)                                  ; Return nil if no error.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Support regions and buffer names.
;; 2. Handles w32 `Open' command if `bookmarkp-use-w32-browser-p' and if `w32-browser' is defined.
;;
(defun bookmark-default-handler (bookmark)
  "Default handler to jump to the location of BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If BOOKMARK records a nonempty region, and `bookmarkp-use-region-flag'
 is non-nil, then activate the region.

Non-nil `bookmarkp-use-w32-browser-p' means just call `w32-browser'
 (if defined).  That is, use the default MS Windows application for
 the bookmarked file.

Return nil or signal `file-error'."
  (let* ((bmk            (bookmark-get-bookmark bookmark))
         (file           (bookmark-get-filename bmk))
         (buf            (bookmark-prop-get bmk 'buffer))
         (bufname        (bookmarkp-get-buffer-name bmk))
         (pos            (bookmark-get-position bmk))
         (end-pos        (bookmarkp-get-end-position bmk))
         (old-info-node  (and (not (bookmark-get-handler bookmark))
                              (bookmark-prop-get bmk 'info-node))))
    (if (and bookmarkp-use-w32-browser-p (fboundp 'w32-browser) file)
        (w32-browser file)
      (if old-info-node                 ; Emacs 20-21 Info bookmarks - no handler entry.
          (progn (require 'info) (Info-find-node file old-info-node) (goto-char pos))
        (if (not (and bookmarkp-use-region-flag end-pos (/= pos end-pos)))
            ;; Single-position bookmark (no region).  Go to it.
            (bookmarkp-goto-position file buf bufname pos
                                     (bookmark-get-front-context-string bmk)
                                     (bookmark-get-rear-context-string bmk))
          ;; Bookmark with a region.  Go to it and activate the region.
          (if (and file (file-readable-p file) (not (buffer-live-p buf)))
              (with-current-buffer (find-file-noselect file) (setq buf  (buffer-name)))
            ;; No file found.  If no buffer either, then signal that file doesn't exist.
            (unless (or (and buf (get-buffer buf))
                        (and bufname (get-buffer bufname) (not (string= buf bufname))))
              (signal 'file-error `("Jumping to bookmark" "No such file or directory"
                                    (bookmark-get-filename bmk)))))
          (set-buffer (or buf bufname))
          (when bookmarkp-jump-display-function
            (save-current-buffer (funcall bookmarkp-jump-display-function (current-buffer)))
            (raise-frame))
          (goto-char (min pos (point-max)))
          (when (> pos (point-max)) (error "Bookmark position is beyond buffer end"))
          ;; Activate region.  Relocate it if it moved.  Save relocated bookmark if confirm.
          (funcall bookmarkp-handle-region-function bmk))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Added note about `S-delete' to doc string.
;; 3. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;; 4. Refresh menu list, to show new location.
;;
(or (fboundp 'old-bookmark-relocate)
(fset 'old-bookmark-relocate (symbol-function 'bookmark-relocate)))

;;;###autoload
(defun bookmark-relocate (bookmark-name)
  "Relocate the bookmark named BOOKMARK-NAME to another file.
You are prompted for the new file name.
Changes the file associated with the bookmark.
Useful when a file has been renamed after a bookmark was set in it.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Bookmark to relocate"
                                               (bookmarkp-default-bookmark-name))))
  (old-bookmark-relocate bookmark-name)
  (when (and (get-buffer-window (get-buffer-create "*Bookmark List*"))
             bookmark-bmenu-toggle-filenames)
    (bookmarkp-refresh-menu-list bookmark-name))) ; So the new location is displayed.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Do not add any text properties here.  That's done in `bookmarkp-bmenu-propertize-item'.
;; 3. Added note about `S-delete' to doc string.
;; 4. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;;
;;;###autoload
(defun bookmark-insert-location (bookmark-name &optional no-history) ; `C-x p f'
  "Insert file or buffer name for the bookmark named BOOKMARK-NAME.
If a file is bookmarked, insert the recorded file name.
If a non-file buffer is bookmarked, insert the recorded buffer name.

Optional second arg NO-HISTORY means do not record this in the
minibuffer history list `bookmark-history'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (if (> emacs-major-version 21)
                   (list (bookmark-completing-read "Insert bookmark location"
                                                   (bookmarkp-default-bookmark-name)))
                 (bookmark-completing-read "Insert bookmark location"
                                           (bookmarkp-default-bookmark-name))))
  (or no-history (bookmark-maybe-historicize-string bookmark-name))
  (insert (bookmark-location bookmark-name))) ; Return the line inserted.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Location returned can be a buffer name, instead of a file name.
;;
(defun bookmark-location (bookmark)
  "Return the name of the file or buffer associated with BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Return \"\" if no such name can be found." ; $$$$$$
  (bookmark-maybe-load-default-file)
  (or (bookmark-get-filename bookmark) (bookmarkp-get-buffer-name bookmark)
      (bookmark-prop-get bookmark 'buffer)
      ""))
      ;; $$$$$$ (error "Bookmark has no file or buffer name: %S" bookmark)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Added note about `S-delete' to doc string.
;; 3. Added BATCH arg.
;; 4. Refresh menu list, to show new name.
;;
;;;###autoload
(defun bookmark-rename (old &optional new batch) ; `C-x p r'
  "Change bookmark's name from OLD to NEW.
Interactively:
 If called from the keyboard, then prompt for OLD.
 If called from the menubar, select OLD from a menu.
If NEW is nil, then prompt for its string value.

If BATCH is non-nil, then do not rebuild the bookmark list.

While the user enters the new name, repeated `C-w' inserts consecutive
words from the buffer into the new bookmark name.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Old bookmark name"
                                               (bookmarkp-default-bookmark-name))))
  (bookmark-maybe-historicize-string old)
  (bookmark-maybe-load-default-file)
  (setq bookmark-current-point  (point))
  (save-excursion (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
  (setq bookmark-current-buffer  (current-buffer))
  (let ((newname  (or new  (read-from-minibuffer
                            "New name: " nil
                            (let ((now-map  (copy-keymap minibuffer-local-map)))
                              (define-key now-map  "\C-w" 'bookmark-yank-word)
                              now-map)
                            nil 'bookmark-history))))
    (bookmark-set-name old newname)
    (setq bookmark-current-bookmark  newname)
    (unless batch
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (when (get-buffer-window (get-buffer-create "*Bookmark List*"))
        (bookmarkp-refresh-menu-list newname))) ; So the new name is displayed.
    (bookmarkp-maybe-save-bookmarks)
    newname))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Added note about `S-delete' to doc string.
;; 3. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;;
(or (fboundp 'old-bookmark-insert)
(fset 'old-bookmark-insert (symbol-function 'bookmark-insert)))

;;;###autoload
(defun bookmark-insert (bookmark-name)  ; `C-x p i'
  "Insert the text of a bookmarked file.
BOOKMARK-NAME is the name of the bookmark.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Insert bookmark contents"
                                               (bookmarkp-default-bookmark-name))))
  (old-bookmark-insert bookmark-name))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added note about `S-delete' to doc string.
;; 2. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;; 3. Use `bookmarkp-default-bookmark-name' as default when interactive.
;; 4. Update `bookmarkp-latest-bookmark-alist' and `bookmarkp-bmenu-omitted-list'.
;; 5. Increment `bookmark-alist-modification-count' even when using `batch' arg.
;;
;;;###autoload
(defun bookmark-delete (bookmark-name &optional batch) ; `C-x p d'
  "Delete the bookmark named BOOKMARK-NAME from the bookmark list.
Removes only the first instance of a bookmark with that name.
If there are other bookmarks with the same name, they are not deleted.
Defaults to the \"current\" bookmark (that is, the one most recently
used in this file), if it exists.  Optional second arg BATCH means do
not update the bookmark list buffer (probably because we were called
from there).

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.  In this way, you can delete multiple bookmarks."
  (interactive
   (list (bookmark-completing-read "Delete bookmark" (bookmarkp-default-bookmark-name))))
  (bookmark-maybe-historicize-string bookmark-name)
  (bookmark-maybe-load-default-file)
  (let ((bmk  (bookmark-get-bookmark bookmark-name 'noerror)))
    (setq bookmark-alist                   (delq bmk bookmark-alist)
          bookmarkp-latest-bookmark-alist  (delq bmk bookmarkp-latest-bookmark-alist)
          bookmarkp-bmenu-omitted-list     (delete bookmark-name bookmarkp-bmenu-omitted-list)))
  ;; Added by DB.  `bookmark-current-bookmark' should be nil if last occurrence was deleted.
  (unless (bookmark-get-bookmark bookmark-current-bookmark 'noerror)
    (setq bookmark-current-bookmark  nil))
  ;; Don't rebuild the list when using `batch' arg
  (unless batch (bookmark-bmenu-surreptitiously-rebuild-list))
  (bookmarkp-maybe-save-bookmarks))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Use `bookmarkp-current-bookmark-file', not `bookmark-default-file'.
;;
;;;###autoload
(defun bookmark-save (&optional parg file)
  "Save currently defined bookmarks.
Save by default in the file named by variable
`bookmarkp-current-bookmark-file'.  With a prefix arg, you are
prompted for the file to save to.

To load bookmarks from a specific file, use `\\[bookmark-load]'
\(`bookmark-load').

If called from Lisp:
 Witn nil PARG, use file `bookmarkp-current-bookmark-file'.
 With non-nil PARG and non-nil FILE, use file FILE.
 With non-nil PARG and nil FILE, prompt the user for the file to use."
  (interactive "P")
  (bookmark-maybe-load-default-file)
  (cond ((and (not parg) (not file)) (bookmark-write-file bookmarkp-current-bookmark-file))
        ((and (not parg) file) (bookmark-write-file file))
        ((and parg (not file))
         (let ((file  (read-file-name "File to save bookmarks in: ")))  (bookmark-write-file file)))
        (t (bookmark-write-file file)))
  ;; Indicate by the count that we have synced the current bookmark file.
  ;; If an error has already occurred somewhere, the count will not be set, which is what we want.
  (setq bookmark-alist-modification-count 0))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg ALT-MSG.
;; 2. Insert code piecewise, to improve performance when saving `bookmark-alist'.
;;    (Do not let `pp' parse all of `bookmark-alist' at once.)
;; 3. Remove any text properties from bookmark title and file name.
;; 4. Use `case', not `cond'.
;;
(defun bookmark-write-file (file &optional alt-msg)
  "Write `bookmark-alist' to FILE.
Non-nil ALT-MSG is a message format string to use in place of the
default, \"Saving bookmarks to file `%s'...\".  The string must
contain a `%s' construct, so that it can be passed along with FILE to
`format'.  At the end, \"done\" is appended to the message."
  (let ((msg  (or alt-msg "Saving bookmarks to file `%s'..." file)))
    (bookmark-maybe-message (or alt-msg "Saving bookmarks to file `%s'...") file)
    (with-current-buffer (get-buffer-create " *Bookmarks*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil)
            bname fname last-fname)
        (bookmark-insert-file-format-version-stamp)
        (insert "(")
        (dolist (bmk  bookmark-alist)
          (setq bname  (car bmk)
                fname  (bookmark-get-filename bmk))
          (set-text-properties 0 (length bname) () bname)
          (when fname (set-text-properties 0 (length fname) () fname))
          (setcar bmk bname)
          (when (setq last-fname  (assq 'filename bmk)) (setcdr last-fname fname))
          (pp bmk (current-buffer)))
        (insert ")")
        (let ((version-control  (case bookmark-version-control
                                  ((nil)      nil)
                                  (never      'never)
                                  (nospecial  version-control)
                                  (t          t))))
          (condition-case nil
              (write-region (point-min) (point-max) file)
            (file-error (message "Cannot write file `%s'" file)))
          (kill-buffer (current-buffer))
          (bookmark-maybe-message (concat msg "done") file))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Prefix arg means OVERWRITE.
;; 2. Update `bookmarkp-current-bookmark-file' if OVERWRITE is non-nil.
;; 3. New doc string.
;; 4. Call `bookmarkp-bmenu-refresh-menu-list' at end.
;;
;;;###autoload
(defun bookmark-load (file &optional overwrite no-msg)
  "Load bookmarks from FILE (which must be in the standard format).
Without a prefix argument (argument OVERWRITE is nil), add the newly
loaded bookmarks to those already current.  They will be saved to the
current bookmark file when bookmarks are saved.  If you have never
switched bookmark files, then this is the default file,
`bookmark-default-file'.

If you do not use a prefix argument, then no existing bookmarks are
overwritten.  If you load some bookmarks that have the same names as
bookmarks already defined in your Emacs session, numeric suffixes
\"<2>\", \"<3>\",... are appended as needed to the names of those new
bookmarks to distinguish them.

With a prefix argument, switch the bookmark file currently used,
*replacing* all currently existing bookmarks with the newly loaded
bookmarks.  The value of `bookmarkp-current-bookmark-file' is changed
to FILE, so bookmarks will subsequently be saved to FILE.  The value
`bookmark-default-file' is unaffected, so your next Emacs session will
still use the same default set of bookmarks.

When called from Lisp, non-nil NO-MSG means do not display any
messages while loading.

You do not need to manually load your default bookmark file
\(`bookmark-default-file') - it is loaded automatically by Emacs the
first time you use bookmarks in a session.  Use `bookmark-load' only
to load extra bookmarks (with no prefix arg) or an alternative set of
bookmarks (with a prefix arg).

If you use `bookmark-load' to load a file that does not contain a
proper bookmark alist, then when bookmarks are saved the current
bookmark file will likely become corrupted.  You should load only
bookmark files that were created using the bookmark functions."
  (interactive
   (list (read-file-name
          (if current-prefix-arg "Switch to bookmark file: " "Add bookmarks from file: ")
          "~/" bookmark-default-file 'confirm)))
  (setq file  (expand-file-name file))
  (unless (file-readable-p file) (error "Cannot read bookmark file `%s'" file))
  (unless no-msg (bookmark-maybe-message "Loading bookmarks from `%s'..." file))
  (with-current-buffer (let ((enable-local-variables nil)) (find-file-noselect file))
    (goto-char (point-min))
    (bookmark-maybe-upgrade-file-format)
    (let ((blist  (bookmark-alist-from-buffer)))
      (unless (listp blist) (error "Invalid bookmark list in `%s'" file))
      (if overwrite
          (setq bookmarkp-current-bookmark-file    file
                bookmark-alist                     blist
                bookmark-alist-modification-count  0)
        (bookmark-import-new-list blist)
        (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count)))
      (when (string-equal (expand-file-name bookmark-default-file) file)
        (setq bookmarks-already-loaded  t))
      (bookmark-bmenu-surreptitiously-rebuild-list))
    (kill-buffer (current-buffer)))
  (unless no-msg (bookmark-maybe-message "Loading bookmarks from `%s'...done" file))
  (let ((bmklistbuf  (get-buffer "*Bookmark List*")))
    (when bmklistbuf (with-current-buffer bmklistbuf (bookmarkp-bmenu-refresh-menu-list)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Added optional arg MSGP.  Show message if no annotation.
;; Name buffer after the bookmark.
;; Do not `save-excursion' (makes no sense, since we `pop-to-buffer').
;; Raise error if no annotation.
;; Use `view-mode'.  `q' uses `quit-window'.
;; Fit frame to buffer if `one-windowp'.
;;
(defun bookmark-show-annotation (bookmark &optional msgp)
  "Display the annotation for BOOKMARK."
  (let* ((bmk       (bookmark-get-bookmark bookmark))
         (bmk-name  (bookmark-name-from-full-record bmk))
         (ann       (bookmark-get-annotation bmk)))
    (if (not (and ann (not (string-equal ann ""))))
        (when msgp (message "Bookmark has no annotation"))
      (pop-to-buffer (get-buffer-create (format "*`%s' Annotation*" bmk-name)) t)
      (delete-region (point-min) (point-max))
      (insert (concat "Annotation for bookmark '" bmk-name "':\n\n"))
      (put-text-property (line-beginning-position -1) (line-end-position 1) 'face 'bookmarkp-heading)
      (insert ann)
      (goto-char (point-min))
      (view-mode-enter (cons (selected-window) (cons nil 'quit-window)))
      (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Do not `save-selected-window' (makes no sense, since we `pop-to-buffer').
;; Use name `*Bookmark Annotations*', not `*Bookmark Annotation*'.
;; Don't list bookmarks with no annotation.
;; Highlight bookmark names.  Don't indent annotations.  Add a blank line after each annotation.
;; Use `view-mode'.  `q' uses `quit-window'.
;; Fit frame to buffer if `one-windowp'.
;;
(defun bookmark-show-all-annotations ()
  "Display the annotations for all bookmarks."
  (pop-to-buffer (get-buffer-create "*Bookmark Annotations*") t)
  (setq buffer-read-only  nil)
  (delete-region (point-min) (point-max))
  (dolist (full-record  bookmark-alist)
    (let ((ann  (bookmark-get-annotation full-record)))
      (when (and ann (not (string-equal ann "")))
        (insert (concat (bookmark-name-from-full-record full-record) ":\n"))
        (put-text-property (line-beginning-position 0) (line-end-position 0) 'face 'bookmarkp-heading)
        (insert ann) (unless (bolp) (insert "\n\n")))))
  (goto-char (point-min))
  (view-mode-enter (cons (selected-window) (cons nil 'quit-window)))
  (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))
 
;;(@* "Menu List Replacements (`bookmark-bmenu-*')")
;;; Menu List Replacements (`bookmark-bmenu-*') ----------------------


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Return t.  Value doesn't mean anything (didn't anyway), but must be non-nil for vanilla Emacs.
;; 2. Don't count lines.  Just make sure we're on a bookmark line.
;;
(defalias 'bookmark-bmenu-check-position 'bookmark-bmenu-ensure-position)
(defun bookmark-bmenu-ensure-position ()
  "Move to the beginning of the nearest bookmark line."
  (beginning-of-line)
  (unless (bookmark-bmenu-bookmark)
    (if (and (bolp) (eobp))
        (beginning-of-line 0)
      (goto-char (point-min))
      (forward-line bookmarkp-bmenu-header-lines)))
  t)                                    ; Older vanilla bookmark code depends on non-nil value.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add bookmark to `bookmarkp-bmenu-marked-bookmarks'.
;; 2. Don't call `bookmark-bmenu-ensure-position' again at end.
;; 3. Raise error if not in `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-mark ()           ; `m' in bookmark list
  "Mark the bookmark on this line, using mark `>'."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (beginning-of-line)
  (let ((inhibit-read-only  t))
    (push (bookmark-bmenu-bookmark) bookmarkp-bmenu-marked-bookmarks)
    (delete-char 1) (insert ?>)
    (put-text-property (1- (point)) (point) 'face 'bookmarkp->-mark)
    (forward-line 1)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Remove bookmark from `bookmarkp-bmenu-marked-bookmarks'.
;; 2. Don't call `bookmark-bmenu-ensure-position' again at end.
;; 3. Raise error if not in `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-unmark (&optional backup) ; `u' in bookmark list
  "Unmark the bookmark on this line, then move down to the next.
Optional BACKUP means move up instead."
  (interactive "P")
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (beginning-of-line)
  (let ((inhibit-read-only  t))
    (delete-char 1) (insert " ")
    (setq bookmarkp-bmenu-marked-bookmarks  (delete (bookmark-bmenu-bookmark)
                                                    bookmarkp-bmenu-marked-bookmarks)))
  (forward-line (if backup -1 1)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Do not use `bookmark-bmenu-ensure-position' as a test - it always returns non-nil anyway.
;;    And don't call it at again the end.
;; 2. Use face `bookmarkp-bad-bookmark' on the `D' flag.
;; 3. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-delete ()         ; `d', `k'
  "Flag this bookmark for deletion, using mark `D'.
Use `\\<bookmark-bmenu-mode-map>\\[bookmark-bmenu-execute-deletions]' to carry out \
the deletions."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (beginning-of-line)
  (bookmark-bmenu-ensure-position)
  (let ((inhibit-read-only  t))
    (delete-char 1) (insert ?D)
    (put-text-property (1- (point)) (point) 'face 'bookmarkp-D-mark)
    (setq bookmarkp-bmenu-marked-bookmarks  (delete (bookmark-bmenu-bookmark)
                                                    bookmarkp-bmenu-marked-bookmarks))
    (forward-line 1)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Rebuild the menu list using the last filtered alist in use, `bookmarkp-latest-bookmark-alist'.
;; 2. Update the menu-list title.
;;
(defun bookmark-bmenu-surreptitiously-rebuild-list ()
  "Rebuild the bookmark list, if it exists.
Optional arg DONT-TOGGLE-FILENAMES-P is passed to
`bookmark-bmenu-list'."
  (when (get-buffer "*Bookmark List*")
    (save-excursion
      (save-window-excursion
        (let ((bookmark-alist  bookmarkp-latest-bookmark-alist))
          (bookmark-bmenu-list 'filteredp))))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added args TITLE, FILTEREDP, DONT-TOGGLE-FILENAMES-P.
;; 2. Handles also region bookmarks and buffer (non-file) bookmarks.
;; 3. Uses `pop-to-buffer', not `switch-to-buffer', so we respect `special-display-*'
;;    (but keep `one-window-p' if that's the case).
;; 4. If option `bookmarkp-bmenu-state-file' is non-nil, then the first time since the last quit
;;     (or the last Emacs session) restores the last menu-list state.
;; 5. If option `bookmarkp-bmenu-commands-file' is non-nil, then read that file, which contains
;;    user-defined `*Bookmark List*' commands.
;;
(defalias 'list-bookmarks 'bookmark-bmenu-list)
;;;###autoload
(defun bookmark-bmenu-list (&optional filteredp) ; `C-x r l'
  "Display a list of existing bookmarks, in buffer `*Bookmark List*'.
The leftmost column of a bookmark entry shows `D' if the bookmark is
 flagged for deletion, or `>' if it is marked normally.
The second column shows `a' if the bookmark has an annotation.

The following faces are used for the list entries.
Use `customize-face' if you want to change the appearance.

 `bookmarkp-bad-bookmark', `bookmarkp-bookmark-list',
 `bookmarkp-buffer', `bookmarkp-desktop', `bookmarkp-function',
 `bookmarkp-gnus', `bookmarkp-info', `bookmarkp-local-directory',
 `bookmarkp-local-file-without-region',
 `bookmarkp-local-file-with-region', `bookmarkp-man',
 `bookmarkp-non-file', `bookmarkp-remote-file', `bookmarkp-sequence',
 `bookmarkp-su-or-sudo', `bookmarkp-w3m'.

Non-nil FILTEREDP means the bookmark list has been filtered, so:
 * Use `bookmarkp-bmenu-title' not the default menu-list title.
 * Do not reset `bookmarkp-latest-bookmark-alist' to `bookmark-alist'."
  (interactive)
  (bookmark-maybe-load-default-file)
  (when (and bookmarkp-bmenu-first-time-p bookmarkp-bmenu-commands-file
             (file-readable-p bookmarkp-bmenu-commands-file))
    (with-current-buffer (let ((enable-local-variables  ())
                               (emacs-lisp-mode-hook    nil))
                           (find-file-noselect bookmarkp-bmenu-commands-file))
      (goto-char (point-min))
      (while (not (eobp)) (condition-case nil (eval (read (current-buffer))) (error nil)))
      (kill-buffer (current-buffer))))
  (cond ((and bookmarkp-bmenu-first-time-p  bookmarkp-bmenu-state-file ; Restore from state file.
              (file-readable-p bookmarkp-bmenu-state-file))
         (let ((state  ()))
           (with-current-buffer (let ((enable-local-variables  nil)
                                      (emacs-lisp-mode-hook    nil))
                                  (find-file-noselect bookmarkp-bmenu-state-file))
             (goto-char (point-min))
             (setq state  (condition-case nil (read (current-buffer)) (error nil)))
             (kill-buffer (current-buffer)))
           (when (consp state)
             (setq bookmarkp-sort-comparer           (cdr (assq 'last-sort-comparer          state))
                   bookmarkp-reverse-sort-p          (cdr (assq 'last-reverse-sort-p         state))
                   bookmarkp-reverse-multi-sort-p    (cdr (assq 'last-reverse-multi-sort-p   state))
                   bookmarkp-latest-bookmark-alist   (cdr (assq 'last-latest-bookmark-alist  state))
                   bookmarkp-bmenu-omitted-list      (cdr (assq 'last-omitted-list           state))
                   bookmarkp-bmenu-marked-bookmarks  (cdr (assq 'last-bmenu-marked-bookmarks state))
                   bookmarkp-bmenu-filter-function   (cdr (assq 'last-bmenu-filter-function  state))
                   bookmarkp-bmenu-title             (cdr (assq 'last-bmenu-title            state))
                   bookmarkp-last-bmenu-bookmark     (cdr (assq 'last-bmenu-bookmark         state))
                   bookmark-bmenu-toggle-filenames   (cdr (assq 'last-bmenu-toggle-filenames state))
                   bookmarkp-bmenu-before-hide-marked-alist
                   (cdr (assq 'last-bmenu-before-hide-marked-alist   state))
                   bookmarkp-bmenu-before-hide-unmarked-alist
                   (cdr (assq 'last-bmenu-before-hide-unmarked-alist state)))
             (let ((last-bookmark-file  (cdr (assq 'last-bookmark-file state))))
               (unless (or (not last-bookmark-file)
                           (bookmarkp-same-file-p last-bookmark-file bookmarkp-current-bookmark-file))
                 (if (y-or-n-p
                      (format "Saved bookmark-list state does not match the current bookmark \
file.  Switch to the last file used, `%s'? " last-bookmark-file))
                     (setq bookmarkp-current-bookmark-file  last-bookmark-file)
                   (message (substitute-command-keys "INTENTIONAL MISMATCH acknowledged.  Use \
`\\[bookmarkp-switch-bookmark-file]' if you want to switch files."))
                   (sit-for 4))))))
         (setq bookmarkp-bmenu-first-time-p  nil)
         (let ((bookmark-alist  (or bookmarkp-latest-bookmark-alist bookmark-alist)))
           (bookmarkp-bmenu-list-1 'filteredp nil (interactive-p)))
         (when bookmarkp-last-bmenu-bookmark
           (with-current-buffer (get-buffer "*Bookmark List*")
             (bookmarkp-bmenu-goto-bookmark-named bookmarkp-last-bmenu-bookmark))))
        (t
         (setq bookmarkp-bmenu-first-time-p  nil)
         (bookmarkp-bmenu-list-1
          filteredp  (or (interactive-p) (not (get-buffer "*Bookmark List*")))  (interactive-p)))))

(defun bookmarkp-bmenu-list-1 (filteredp reset-marked-p interactivep)
  "Helper for `bookmark-bmenu-list'.
See `bookmark-bmenu-list' for the description of FILTEREDP.
Non-nil RESET-MARKED-P resets `bookmarkp-bmenu-marked-bookmarks'.
Non-nil INTERACTIVEP means `bookmark-bmenu-list' was called
 interactively, so pop to the bookmark list and communicate the sort
 order."
  (when reset-marked-p (setq bookmarkp-bmenu-marked-bookmarks  ()))
  (unless filteredp (setq bookmarkp-latest-bookmark-alist  bookmark-alist))
  (if interactivep
      (let ((one-win-p  (one-window-p)))
        (pop-to-buffer (get-buffer-create "*Bookmark List*"))
        (when one-win-p (delete-other-windows)))
    (set-buffer (get-buffer-create "*Bookmark List*")))
  (let* ((inhibit-read-only  t)
         (title              (if (and filteredp bookmarkp-bmenu-title)
				 bookmarkp-bmenu-title
			       "All Bookmarks")))
    (erase-buffer)
    (insert (format "%s\n%s\n" title (make-string (length title) ?-)))
    (add-text-properties (point-min) (point) (bookmarkp-face-prop 'bookmarkp-heading))
    (let ((max-width     0)
          name markedp taggedp annotation start)
      (setq bookmarkp-sorted-alist  (bookmarkp-sort-and-remove-dups
                                     bookmark-alist
                                     (and (not (eq bookmarkp-bmenu-filter-function
                                                   'bookmarkp-omitted-alist-only))
                                          bookmarkp-bmenu-omitted-list)))
      (dolist (bmk  bookmarkp-sorted-alist)
        (setq max-width  (max max-width (length (bookmark-name-from-full-record bmk)))))
      (setq max-width  (+ max-width bookmarkp-bmenu-marks-width))
      (dolist (bmk  bookmarkp-sorted-alist)
        (setq name        (bookmark-name-from-full-record bmk)
              markedp     (bookmarkp-marked-bookmark-p bmk)
              taggedp     (bookmarkp-get-tags bmk)
              annotation  (bookmark-get-annotation bmk)
              start       (+ bookmarkp-bmenu-marks-width (point)))
        (if (not markedp)
            (insert " ")
          (insert ">") (put-text-property (1- (point)) (point) 'face 'bookmarkp->-mark))
        (if (not taggedp)
            (insert " ")
          (insert "t") (put-text-property (1- (point)) (point) 'face 'bookmarkp-t-mark))
        (if (not (and annotation (not (string-equal annotation ""))))
            (insert " ")
          (insert "a") (put-text-property (1- (point)) (point) 'face 'bookmarkp-a-mark))
        (insert " " name)
        (move-to-column max-width t)
        (bookmarkp-bmenu-propertize-item name start (point))
        (insert "\n")))
    (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
    (bookmark-bmenu-mode)
    (when bookmark-bmenu-toggle-filenames (bookmark-bmenu-toggle-filenames t))
    (when (and (fboundp 'fit-frame-if-one-window)
               (eq (selected-window) (get-buffer-window (get-buffer-create "*Bookmark List*"))))
      (fit-frame-if-one-window)))
  (when (and interactivep bookmarkp-sort-comparer)
    (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Redefined.  Get name of the current bookmark from text property `bookmarkp-bookmark-name'.
;; Use `condition-case' in case we're at eob (so cannot advance).
;;
(defun bookmark-bmenu-bookmark ()
  "Return the name of the bookmark on this line."
  (condition-case nil
      (save-excursion (forward-line 0) (forward-char (1+ bookmarkp-bmenu-marks-width))
                      (get-text-property (point) 'bookmarkp-bookmark-name))
    (error nil)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Add text properties when hiding filenames.
;; 2. Do not set or use `bookmark-bmenu-bookmark-column' - use `bookmarkp-bmenu-marks-width' always.
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
        (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
        (setq bookmark-bmenu-hidden-bookmarks  (nreverse bookmark-bmenu-hidden-bookmarks))
        (let ((max-width  0))
          (dolist (name  bookmark-bmenu-hidden-bookmarks)
            (setq max-width  (max max-width (length name))))
          (setq max-width  (+ max-width bookmarkp-bmenu-marks-width))
          (save-excursion
            (let ((inhibit-read-only  t))
              (while bookmark-bmenu-hidden-bookmarks
                (move-to-column bookmarkp-bmenu-marks-width t)
                (bookmark-kill-line)
                (let ((name   (car bookmark-bmenu-hidden-bookmarks))
                      (start  (point))
                      end)
                  (insert name)
                  (move-to-column max-width t)
                  (setq end  (point))
                  (bookmarkp-bmenu-propertize-item name start end))
                (setq bookmark-bmenu-hidden-bookmarks  (cdr bookmark-bmenu-hidden-bookmarks))
                (forward-line 1)))))))
    (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))))


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
        (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
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
                (let ((help  (get-text-property (+ bookmarkp-bmenu-marks-width
                                                   (line-beginning-position)) 'help-echo)))
                  (put-text-property (+ bookmarkp-bmenu-marks-width (line-beginning-position))
                                     (point) 'mouse-face 'highlight)
                  (when help
                    (put-text-property (+ bookmarkp-bmenu-marks-width (line-beginning-position))
                                       (point) 'help-echo help))))
              (forward-line 1))))))
    (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `pop-to-buffer', not `switch-to-buffer-other-window'.
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
(defun bookmark-bmenu-other-window ()   ; `o' in bookmark list
  "Select this line's bookmark in other window, leaving bookmark menu visible."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark                                 (bookmark-bmenu-bookmark))
        (bookmark-automatically-show-annotations  t)) ; FIXME: needed?
    (bookmark--jump-via bookmark 'pop-to-buffer)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Added optional arg MSGP.
;; Call `bookmark-show-annotation' with arg MSGP.
;;
(defun bookmark-bmenu-show-annotation (msgp)
  "Show the annotation for the current bookmark in another window."
  (interactive "p")
  (let ((bookmark  (bookmark-bmenu-bookmark)))
    (bookmark-show-annotation bookmark msgp)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg MARKEDP: handle bookmarks marked `>', not just those flagged `D'.
;; 2. Use `bookmark-bmenu-surreptitiously-rebuild-list', instead of using
;;    `bookmark-bmenu-list', updating the modification count, and saving.
;; 3. Update `bookmarkp-latest-bookmark-alist' to reflect the deletions.
;; 4. Use `bookmarkp-bmenu-goto-bookmark-named'.
;; 5. Added status messages.
;; 6. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-execute-deletions (&optional markedp) ; `x' in bookmark list
  "Delete (visible) bookmarks flagged `D'.
With a prefix argument, delete the bookmarks marked `>' instead, after
confirmation."
  (interactive "P")
  (bookmarkp-barf-if-not-in-menu-list)
  (if (or (not markedp) (yes-or-no-p "Delete bookmarks marked `>' (not `D') "))
      (let* ((mark-type  (if markedp "^>" "^D"))
             (o-str      (and (not (looking-at mark-type)) (bookmark-bmenu-bookmark)))
             (o-point    (point))
             (count      0))
        (message "Deleting bookmarks...")
        (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
        (while (re-search-forward mark-type (point-max) t)
          (let ((bmk  (bookmark-bmenu-bookmark)))
            (bookmark-delete bmk 'batch)
            (setq count                            (1+ count)
                  bookmarkp-latest-bookmark-alist  (delete
                                                    (assoc bmk bookmarkp-latest-bookmark-alist)
                                                    bookmarkp-latest-bookmark-alist))))
        (if (<= count 0)
            (message (if markedp "No marked bookmarks" "No bookmarks flagged for deletion"))
          (bookmark-bmenu-surreptitiously-rebuild-list)
          (message "Deleted %d bookmarks" count))
        (if o-str
            (bookmarkp-bmenu-goto-bookmark-named o-str)
          (goto-char o-point)
          (beginning-of-line)))
    (message "OK, nothing deleted")))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Do not call `bookmark-bmenu-list' (it was already called).
;; 2. Raise error if not in buffer `*Bookmark List*'.
;;
;;;###autoload
(defun bookmark-bmenu-rename ()         ; `r' in bookmark list
  "Rename bookmark on current line.  Prompts for a new name."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((new-name  (bookmark-rename (bookmark-bmenu-bookmark))))
    (when (or (search-forward new-name (point-max) t) (search-backward new-name (point-min) t))
      (beginning-of-line))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Save menu-list state to `bookmarkp-bmenu-state-file'.
;;
(defun bookmark-exit-hook-internal ()
  "Save currently defined bookmarks and perhaps bookmark menu-list state.
Run `bookmark-exit-hook', then save bookmarks if they were updated.
Then save menu-list state to file `bookmarkp-bmenu-state-file', but
only if that option is non-nil."
  (run-hooks 'bookmark-exit-hook)
  (when (and bookmark-alist (bookmark-time-to-save-p t)) (bookmark-save))
  (bookmarkp-save-menu-list-state))
 
;;(@* "Bookmark+ Functions (`bookmarkp-*')")
;;; Bookmark+ Functions (`bookmarkp-*') ------------------------------

(defun bookmarkp-jump-1 (bookmark-name display-function use-region-p)
  "Helper function for `bookmark-jump' commands."
  (unless bookmark-name (error "No bookmark specified"))
  (bookmark-maybe-historicize-string bookmark-name)
  (let ((bookmarkp-use-region-flag  (if use-region-p
                                        (not bookmarkp-use-region-flag)
                                      bookmarkp-use-region-flag)))
    (bookmark--jump-via bookmark-name display-function)))

(defun bookmarkp-maybe-save-bookmarks ()
  "Increment save counter and maybe save `bookmark-alist'."
  (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count))
  (when (bookmark-time-to-save-p) (bookmark-save)))

(defun bookmarkp-edit-bookmark (bookmark-name)
  "Edit bookmark's name and file name, and maybe save them.
BOOKMARK-NAME is the current (old) name of the bookmark."
  (let* ((bookmark-filename  (bookmark-get-filename bookmark-name))
         (new-bmk-name       (read-from-minibuffer "New bookmark name: " nil nil nil nil
                                                   bookmark-name))
         (new-filename       (read-from-minibuffer "New file name: " nil nil nil nil
                                                   bookmark-filename)))
    (when (and (not (equal new-bmk-name "")) (not (equal new-filename ""))
               (y-or-n-p "Save changes? "))
      (bookmark-rename bookmark-name new-bmk-name 'batch)
      (bookmark-set-filename new-bmk-name new-filename)
      (bookmarkp-maybe-save-bookmarks)
      (list new-bmk-name new-filename))))

(defun bookmarkp-record-visit (bookmark &optional batch)
  "Update the data recording a visit to BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
This increments the `visits' entry and sets the `time' entry to the
current time.  If either an entry is not present, it is added (with 0
value for `visits')."
  (let ((vis  (bookmark-prop-get bookmark 'visits)))
    (if vis
        (bookmark-prop-set bookmark 'visits (1+ vis))
      (bookmark-prop-set bookmark 'visits 0))
    (bookmark-prop-set bookmark 'time (current-time))
    (unless batch (bookmark-bmenu-surreptitiously-rebuild-list))
    (let ((bookmark-save-flag  nil))  (bookmarkp-maybe-save-bookmarks))))

(defun bookmarkp-default-bookmark-name (&optional alist)
  "Default bookmark name.
If in buffer `*Bookmark List*' then the current line's bookmark.
Otherwise, the last-used bookmark in the current buffer.

Non-nil ALIST means return nil unless the default names a bookmark in
ALIST."
  (let ((name  (if (equal (buffer-name (current-buffer)) "*Bookmark List*")
                   (bookmark-bmenu-bookmark)
                 bookmark-current-bookmark)))
    (when alist (setq name  (car (assoc name alist))))
    name))

;;;###autoload
(defun bookmarkp-send-bug-report ()
  "Send a bug report about a Bookmark+ problem."
  (interactive)
  (browse-url (format (concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark+ bug: \
&body=Describe bug below, using a precise recipe that starts with `emacs -Q' or `emacs -q'.  \
Be sure to mention the `Update #' from the `bookmark+.el' file header.%%0A%%0AEmacs version: %s")
                      (emacs-version))))

;;;###autoload
(defun bookmarkp-toggle-bookmark-set-refreshes ()
  (interactive)
  "Toggle `bookmark-set' refreshing `bookmarkp-latest-bookmark-alist'.
Add/remove `bookmarkp-refresh-latest-bookmark-list' to/from
`bookmarkp-after-set-hook'."
  (if (member 'bookmarkp-refresh-latest-bookmark-list bookmarkp-after-set-hook)
      (remove-hook 'bookmarkp-after-set-hook 'bookmarkp-refresh-latest-bookmark-list)
    (add-hook 'bookmarkp-after-set-hook 'bookmarkp-refresh-latest-bookmark-list)))

(defun bookmarkp-refresh-latest-bookmark-list ()
  "Refresh `bookmarkp-latest-bookmark-alist' to reflect `bookmark-alist'."
  (setq bookmarkp-latest-bookmark-alist  (if bookmarkp-bmenu-filter-function
                                             (funcall bookmarkp-bmenu-filter-function)
                                           bookmark-alist)))

;;;###autoload
(defun bookmarkp-toggle-saving-menu-list-state () ; `M-l' in bookmark list
  "Toggle the value of option `bookmarkp-bmenu-state-file'.
Tip: You can use this before quitting Emacs, to not save the state.
If the initial value of `bookmarkp-bmenu-state-file' is nil, then
this command has no effect."
  (interactive)
  (unless (or bookmarkp-last-bmenu-state-file bookmarkp-bmenu-state-file)
    (error "Cannot toggle: initial value of `bookmarkp-bmenu-state-file' is nil"))
  (setq bookmarkp-last-bmenu-state-file
        (prog1 bookmarkp-bmenu-state-file
          (setq bookmarkp-bmenu-state-file  bookmarkp-last-bmenu-state-file)))
  (message (if bookmarkp-bmenu-state-file
               "Autosaving of bookmark list state is now ON"
             "Autosaving of bookmark list state is now OFF")))

;;;###autoload
(defun bookmarkp-toggle-saving-bookmark-file () ; `M-~' in bookmark list
  "Toggle the value of option `bookmark-save-flag'.
If the initial value of `bookmark-save-flag' is nil, then this
command has no effect."
  (interactive)
  (unless (or bookmarkp-last-save-flag-value bookmark-save-flag)
    (error "Cannot toggle: initial value of `bookmark-save-flag' is nil"))
  (setq bookmarkp-last-save-flag-value
        (prog1 bookmark-save-flag
          (setq bookmark-save-flag  bookmarkp-last-save-flag-value)))
  (message (if bookmark-save-flag
               "Autosaving of current bookmark file is now ON"
             "Autosaving of current bookmark file is now OFF")))

;;;###autoload
(defun bookmarkp-make-function-bookmark (bookmark-name function)
  "Create a bookmark that will invoke FUNCTION when \"jumped\" to.
You are prompted for the bookmark name and the name of the function.
Returns the new bookmark (internal record)."
  (interactive (list (read-string "Bookmark: ") (completing-read "Function: " obarray 'functionp)))
  (bookmark-store bookmark-name `((filename . ,bookmarkp-non-file-filename)
                                  (position . 0)
                                  (function . ,(read function))
                                  (handler  . bookmarkp-jump-function))
                  nil)
  (let ((new  (bookmark-get-bookmark bookmark-name 'noerror)))
    (unless (memq new bookmarkp-latest-bookmark-alist)
      (setq bookmarkp-latest-bookmark-alist  (cons new bookmarkp-latest-bookmark-alist)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    new))

;;;###autoload
(defun bookmarkp-switch-bookmark-file (file &optional no-msg)
  "Switch to a different bookmark file, FILE.
Replace all currently existing bookmarks with the newly loaded
bookmarks.  Change the value of `bookmarkp-current-bookmark-file' to
FILE, so bookmarks will subsequently be saved to FILE.
  
`bookmark-default-file' is unaffected, so your next Emacs session will
still use `bookmark-default-file' for the initial set of bookmarks."
  (interactive
   (list (read-file-name
          "Switch to bookmark file: " "~/"
          ;; Default file as default choice, unless it's already current.
          (and (not (bookmarkp-same-file-p bookmark-default-file bookmarkp-current-bookmark-file))
               bookmark-default-file)
          'confirm)))
  (bookmark-load file t no-msg))


;;(@* "Menu-List (`*-bmenu-*') Filter Commands")
;;  *** Menu-List (`*-bmenu-*') Filter Commands ***

;;;###autoload
(defun bookmarkp-bmenu-show-only-desktops () ; `K S' in bookmark list
  "Display (only) the desktop bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-desktop-alist-only
        bookmarkp-bmenu-title            "Desktop Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only desktop bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-dired () ; `M-d M-s' in bookmark list
  "Display (only) the Dired bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-dired-alist-only
        bookmarkp-bmenu-title            "Dired Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only Dired bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-files (arg) ; `F S' in bookmark list
  "Display a list of file and directory bookmarks (only).
With a prefix argument, do not include remote files or directories."
  (interactive "P")
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  (if arg
                                             'bookmarkp-local-file-alist-only
                                           'bookmarkp-file-alist-only)
        bookmarkp-bmenu-title            (if arg
                                             "Local File and Directory Bookmarks"
                                           "File and Directory Bookmarks"))
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only file bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-non-files () ; `B S' in bookmark list
  "Display (only) the non-file bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-non-file-alist-only
        bookmarkp-bmenu-title            "Non-File Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only non-file bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-gnus () ; `G S' in bookmark list
  "Display (only) the Gnus bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-gnus-alist-only
        bookmarkp-bmenu-title            "Gnus Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only Gnus bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-info-nodes () ; `I S' in bookmark list
  "Display (only) the Info bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-info-alist-only
        bookmarkp-bmenu-title            "Info Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only Info bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-man-pages () ; `M S' in bookmark list
  "Display (only) the `man' page bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-man-alist-only
        bookmarkp-bmenu-title            "`man' Page Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only `man' page bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-regions () ; `R S' in bookmark list
  "Display (only) the bookmarks that record a region."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-region-alist-only
        bookmarkp-bmenu-title            "Region Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                    "Only bookmarks with regions are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-only-w3m-urls () ; `W S' in bookmark list
  "Display (only) the w3m bookmarks."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-w3m-alist-only
        bookmarkp-bmenu-title            "W3M Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                                        "Only W3M bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-show-all ()      ; `.' in bookmark list
  "Show all bookmarks known to the bookmark list (aka \"menu list\").
Omitted bookmarks are not shown, however.
Also, this does not revert the bookmark list, to bring it up to date.
To revert the list, use `\\<bookmark-bmenu-mode-map>\\[bookmarkp-bmenu-refresh-menu-list]'."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-bmenu-filter-function  nil
        bookmarkp-bmenu-title            "All Bookmarks"
        bookmarkp-latest-bookmark-alist  bookmark-alist)
  (bookmark-bmenu-list)
  (when (interactive-p)
    (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order) "All bookmarks are shown")))

;;;###autoload
(defun bookmarkp-bmenu-refresh-menu-list () ; `g' in bookmark list
  "Refresh (revert) the bookmark list (\"menu list\").
This brings the displayed list up to date.  It does not change the
current filtering or sorting of the displayed list.

If you want setting a bookmark to refresh the list automatically, you
can use command `bookmarkp-toggle-bookmark-set-refreshes'."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (let ((bmk-name  (bookmark-bmenu-bookmark)))
    (bookmarkp-refresh-menu-list bmk-name)))

(defun bookmarkp-refresh-menu-list (&optional bookmark)
  "Refresh (revert) the bookmark list (\"menu list\").
This brings the displayed list up to date.  It does not change the
current filtering or sorting of the displayed list.
Non-nil optional arg BOOKMARK means move cursor to BOOKMARK's line."
  (let ((bookmark-alist  (if bookmarkp-bmenu-filter-function
                             (funcall bookmarkp-bmenu-filter-function)
                           bookmark-alist)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)
    (when bookmark (with-current-buffer (get-buffer "*Bookmark List*")
                     (bookmarkp-bmenu-goto-bookmark-named bookmark)))))

;;;###autoload
(defun bookmarkp-bmenu-filter-bookmark-name-incrementally () ; `P B' in bookmark list
  "Incrementally filter bookmarks by bookmark name using a regexp."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bookmarkp-bmenu-filter-timer
                    (run-with-timer 0 bookmarkp-incremental-filter-delay
                                    #'bookmarkp-bmenu-filter-alist-by-bookmark-name-regexp))
              (bookmarkp-bmenu-read-filter-input))
    (bookmarkp-bmenu-cancel-incremental-filtering)))

(defun bookmarkp-bmenu-filter-alist-by-bookmark-name-regexp ()
  "Filter bookmarks by bookmark name, then refresh the bookmark list."
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-regexp-filtered-bookmark-name-alist-only
        bookmarkp-bmenu-title            (format "Bookmarks with Names Matching Regexp `%s'"
                                                 bookmarkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload
(defun bookmarkp-bmenu-filter-file-name-incrementally () ; `P F' in bookmark list
  "Incrementally filter bookmarks by file name using a regexp."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bookmarkp-bmenu-filter-timer
                    (run-with-timer 0 bookmarkp-incremental-filter-delay
                                    #'bookmarkp-bmenu-filter-alist-by-file-name-regexp))
              (bookmarkp-bmenu-read-filter-input))
    (bookmarkp-bmenu-cancel-incremental-filtering)))

(defun bookmarkp-bmenu-filter-alist-by-file-name-regexp ()
  "Filter bookmarks by file name, then refresh the bookmark list."
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-regexp-filtered-file-name-alist-only
        bookmarkp-bmenu-title            (format "Bookmarks with File Names Matching Regexp `%s'"
                                                 bookmarkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

;;;###autoload
(defun bookmarkp-bmenu-filter-tags-incrementally () ; `P T' in bookmark list
  "Incrementally filter bookmarks by tags using a regexp."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (unwind-protect
       (progn (setq bookmarkp-bmenu-filter-timer
                    (run-with-timer 0 bookmarkp-incremental-filter-delay
                                    #'bookmarkp-bmenu-filter-alist-by-tags-regexp))
              (bookmarkp-bmenu-read-filter-input))
    (bookmarkp-bmenu-cancel-incremental-filtering)))

(defun bookmarkp-bmenu-filter-alist-by-tags-regexp ()
  "Filter bookmarks by tags, then refresh the bookmark list."
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-regexp-filtered-tags-alist-only
        bookmarkp-bmenu-title            (format "Bookmarks with Tags Matching Regexp `%s'"
                                                 bookmarkp-bmenu-filter-pattern))
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)))

(defun bookmarkp-bmenu-read-filter-input ()
  "Read input and add it to `bookmarkp-bmenu-filter-pattern'."
  (setq bookmarkp-bmenu-filter-pattern  "")
  (let ((tmp-list  ())
        char)
    (catch 'bookmarkp-bmenu-read-filter-input-1
      (while t
        (catch 'bookmarkp-bmenu-read-filter-input-2
          (condition-case nil
              (setq char  (read-char (concat bookmarkp-bmenu-filter-prompt
                                             bookmarkp-bmenu-filter-pattern)))
            (error (throw 'bookmarkp-bmenu-read-filter-input-1 nil)))
          (case char
            ((?\e ?\r) (throw 'bookmarkp-bmenu-read-filter-input-1 nil)) ; Break and exit.
            (?\d
             (pop tmp-list)             ; Delete last char of `bookmarkp-bmenu-filter-pattern'.
             (setq bookmarkp-bmenu-filter-pattern  (mapconcat 'identity (reverse tmp-list) ""))
             (throw 'bookmarkp-bmenu-read-filter-input-2 nil))
            (t
             (push (text-char-description char) tmp-list)
             (setq bookmarkp-bmenu-filter-pattern  (mapconcat 'identity (reverse tmp-list) ""))
             (throw 'bookmarkp-bmenu-read-filter-input-2 nil))))))))

(defun bookmarkp-bmenu-cancel-incremental-filtering ()
  "Cancel timer used for incrementally filtering bookmarks."
  (cancel-timer bookmarkp-bmenu-filter-timer)
  (setq bookmarkp-bmenu-filter-timer  nil))

;;;###autoload
(defun bookmarkp-bmenu-toggle-show-only-unmarked () ; `<' in bookmark list
  "Hide all marked bookmarks.  Repeat to toggle, showing all."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (if (or (bookmarkp-some-marked-p bookmarkp-latest-bookmark-alist)
          (bookmarkp-some-marked-p bookmarkp-bmenu-before-hide-marked-alist))
      (let ((bookmark-alist  bookmarkp-latest-bookmark-alist)
            status)
        (if bookmarkp-bmenu-before-hide-marked-alist
            (setq bookmark-alist                            bookmarkp-bmenu-before-hide-marked-alist
                  bookmarkp-bmenu-before-hide-marked-alist  ()
                  bookmarkp-latest-bookmark-alist           bookmark-alist
                  status                                    'shown)
          (setq bookmarkp-bmenu-before-hide-marked-alist  bookmarkp-latest-bookmark-alist
                bookmark-alist                            (bookmarkp-unmarked-bookmarks-only)
                bookmarkp-latest-bookmark-alist           bookmark-alist
                status                                    'hidden))
        (bookmark-bmenu-surreptitiously-rebuild-list)
        (cond ((eq status 'hidden)
               (bookmark-bmenu-ensure-position)
               (message "Marked bookmarks are now hidden"))
              (t
               (goto-char (point-min))
               (when (re-search-forward "^>" (point-max) t)  (forward-line 0))
               (message "Marked bookmarks no longer hidden"))))
    (message "No marked bookmarks to hide"))
  (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))

;;;###autoload
(defun bookmarkp-bmenu-toggle-show-only-marked () ; `>' in bookmark list
  "Hide all unmarked bookmarks.  Repeat to toggle, showing all."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (if (or (bookmarkp-some-unmarked-p bookmarkp-latest-bookmark-alist)
          (bookmarkp-some-unmarked-p bookmarkp-bmenu-before-hide-unmarked-alist))
      (let ((bookmark-alist  bookmarkp-latest-bookmark-alist)
            status)
        (if bookmarkp-bmenu-before-hide-unmarked-alist
            (setq bookmark-alist
                  bookmarkp-bmenu-before-hide-unmarked-alist

                  bookmarkp-bmenu-before-hide-unmarked-alist  ()
                  bookmarkp-latest-bookmark-alist             bookmark-alist
                  status                                      'shown)
          (setq bookmarkp-bmenu-before-hide-unmarked-alist  bookmarkp-latest-bookmark-alist
                bookmark-alist                              (bookmarkp-marked-bookmarks-only)
                bookmarkp-latest-bookmark-alist             bookmark-alist
                status                                      'hidden))
        (bookmark-bmenu-surreptitiously-rebuild-list)
        (cond ((eq status 'hidden)
               (bookmark-bmenu-ensure-position)
               (message "Unmarked bookmarks are now hidden"))
              (t
               (goto-char (point-min))
               (when (re-search-forward "^>" (point-max) t)  (forward-line 0))
               (message "Unmarked bookmarks no longer hidden"))))
    (message "No unmarked bookmarks to hide"))
  (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))


;;(@* "Menu-List (`*-bmenu-*') Commands Involving Marks")
;;  *** Menu-List (`*-bmenu-*') Commands Involving Marks ***

;;;###autoload
(defun bookmarkp-bmenu-mark-all ()      ; `M-m' in bookmark list
  "Mark all bookmarks, using mark `>'."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (save-excursion  
    (let ((count  0))
      (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
      (while (not (eobp)) (bookmark-bmenu-mark) (setq count  (1+ count)))
      (message "Marked: %d" count))))

;; This is similar to `dired-unmark-all-files'.
;;;###autoload
(defun bookmarkp-bmenu-unmark-all (mark &optional arg) ; `M-DEL', `U' in bookmark list
  "Remove a mark from each bookmark.
Hit the mark character (`>' or `D') to remove those marks,
 or hit `RET' to remove all marks (both `>' and `D').
With a prefix arg, you are queried to unmark each marked bookmark.
Use `\\[help-command]' during querying for help."
  (interactive "cRemove marks (RET means all): \nP")
  (bookmarkp-barf-if-not-in-menu-list)
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
                        bookmarkp-bmenu-header-lines
                      (1- bookmarkp-bmenu-header-lines))) ; Because STRING starts with a newline.
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
(defun bookmarkp-bmenu-regexp-mark (regexp) ; `% m' in bookmark list
  "Mark bookmarks that match REGEXP.
The entire bookmark line is tested: bookmark name and possibly file name."
  (interactive "sRegexp: ")
  (bookmarkp-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
    (let ((count  0))
      (while (and (not (eobp)) (re-search-forward regexp (point-max) t))
        (bookmark-bmenu-mark)
        (setq count  (1+ count)))
      (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload
(defun bookmarkp-bmenu-mark-desktop-bookmarks () ; `K M' in bookmark list
  "Mark desktop bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-desktop-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-dired-bookmarks () ; `M-d M-m' in bookmark list
  "Mark Dired bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-dired-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-file-bookmarks (arg) ; `F M' in bookmark list
  "Mark file bookmarks.
With a prefix argument, do not mark remote files or directories."
  (interactive "P")
  (bookmarkp-bmenu-mark-bookmarks-satisfying
   (if arg 'bookmarkp-local-file-bookmark-p 'bookmarkp-file-bookmark-p)))

;;;###autoload
(defun bookmarkp-bmenu-mark-gnus-bookmarks () ; `G M' in bookmark list
  "Mark Gnus bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-gnus-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-info-bookmarks () ; `I M' in bookmark list
  "Mark Info bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-info-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-man-bookmarks () ; `M M' in bookmark list
  "Mark `man' page bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-man-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-non-file-bookmarks () ; `B M' in bookmark list
  "Mark non-file bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-non-file-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-region-bookmarks () ; `R M' in bookmark list
  "Mark bookmarks that record a region."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-region-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-w3m-bookmarks () ; `W M' in bookmark list
  "Mark W3M (URL) bookmarks."
  (interactive)
  (bookmarkp-bmenu-mark-bookmarks-satisfying 'bookmarkp-w3m-bookmark-p))

;;;###autoload
(defun bookmarkp-bmenu-mark-bookmarks-satisfying (pred)
  "Mark bookmarks that satisfy predicate PRED.
If you use this interactively, you are responsible for entering a
symbol that names a unnary predicate.  The function you provide is not
checked - it is simply applied to each bookmark to test it."
  (interactive "aPredicate: ")
  (bookmarkp-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
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
(defun bookmarkp-bmenu-toggle-marks ()  ; `t' in bookmark list
  "Toggle marks: Unmark all marked bookmarks; mark all unmarked bookmarks.
This affects only the `>' mark, not the `D' flag."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (let ((marked-count    0)
        (unmarked-count  0))
    (save-excursion
      (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
      (if (not (bookmarkp-some-marked-p bookmarkp-latest-bookmark-alist))
          (bookmarkp-bmenu-mark-all)
        (while (not (eobp))
          (cond ((member (bookmark-bmenu-bookmark) bookmarkp-bmenu-marked-bookmarks)
                 (bookmark-bmenu-unmark)
                 (setq unmarked-count  (1+ unmarked-count)))
                (t
                 (bookmark-bmenu-mark)
                 (setq marked-count  (1+ marked-count)))))
        (message "Marked: %d, unmarked: %d" marked-count unmarked-count)))))

;;;###autoload
(defun bookmarkp-bmenu-dired-marked (dirbufname) ; `M-d >' in bookmark list
  "Dired in another window for the marked file and directory bookmarks.

Absolute file names are used for the entries in the Dired buffer.
The only entries are for the marked files and directories.  These can
be located anywhere.  (In Emacs versions prior to release 23.2, remote
bookmarks are ignored, because of Emacs bug #5478.)

You are prompted for the Dired buffer name.  The `default-directory'
of the buffer is the same as that of buffer `*Bookmark List*'."
  (interactive (list (read-string "Dired buffer name: ")))
  (bookmarkp-barf-if-not-in-menu-list)
  (let ((files  ())
        file)
    (dolist (bmk  (bookmarkp-sort-and-remove-dups (bookmarkp-marked-bookmarks-only)))
      (when (or (bookmarkp-local-file-bookmark-p bmk)
                (> emacs-major-version 23)
                (and (= emacs-major-version 23) (> emacs-minor-version 1)))
        (setq file  (bookmark-get-filename bmk))
        (unless (file-name-absolute-p file) (setq file (expand-file-name file))) ; Should not happen.
        (push file files)))
    (dired-other-window (cons dirbufname files))))

;;;###autoload
(defun bookmarkp-bmenu-delete-marked () ; `D' in bookmark list
  "Delete all (visible) bookmarks that are marked `>', after confirmation."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-execute-deletions 'marked))

;;;###autoload
(defun bookmarkp-bmenu-make-sequence-from-marked (bookmark-name &optional dont-omit-p)
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
  (bookmarkp-barf-if-not-in-menu-list)
  (unless (get-buffer "*Bookmark List*") (bookmark-bmenu-list))
  (let ((marked-bmks  ())
        (count        0))
    (message "Making sequence from marked bookmarks...")
    (save-excursion
      (with-current-buffer "*Bookmark List*"
        (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
        (while (re-search-forward "^>" (point-max) t)
          (push (bookmark-bmenu-bookmark) marked-bmks)
          (setq count  (1+ count)))))
    (when (zerop count) (error "No marked bookmarks"))
    (let ((new-seq  (nreverse marked-bmks))
          (bmk      (bookmark-get-bookmark bookmark-name 'noerror)))
      (when (and bmk (bookmarkp-sequence-bookmark-p bmk))
        (if (y-or-n-p (format "ADD marked to existing sequence `%s' (otherwise, REPLACES it)? "
                              bookmark-name))
            (setq new-seq  (nconc new-seq (bookmark-prop-get bmk 'sequence)))
          "OK, existing sequence will be replaced"))
      (bookmark-store bookmark-name
                      `((filename . ,bookmarkp-non-file-filename)
                        (position . 0)
                        (sequence ,@new-seq)
                        (handler  . bookmarkp-jump-sequence))
                      nil)))
  (let ((new  (bookmark-get-bookmark bookmark-name 'noerror)))
    (unless (memq new bookmarkp-latest-bookmark-alist)
      (setq bookmarkp-latest-bookmark-alist  (cons new bookmarkp-latest-bookmark-alist)))
    (unless dont-omit-p
      (bookmarkp-bmenu-omit-marked)
      (message "Marked bookmarks now OMITTED - use `bookmarkp-bmenu-show-only-omitted' to show"))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (bookmarkp-bmenu-goto-bookmark-named bookmark-name)
    new))


;;(@* "Omitted Bookmarks")
;;  *** Omitted Bookmarks ***

;;;###autoload
(defun bookmarkp-bmenu-omit ()
  "Omit this bookmark."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (setq bookmarkp-bmenu-omitted-list  (cons (bookmark-bmenu-bookmark) bookmarkp-bmenu-omitted-list))
  (bookmark-bmenu-surreptitiously-rebuild-list)
  (message "Omitted 1 bookmark"))

;;;###autoload
(defun bookmarkp-bmenu-omit/unomit-marked () ; `O >' in bookmark list
  "Omit all marked bookmarks or, if showing only omitted ones, unomit."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (if (eq bookmarkp-bmenu-filter-function  'bookmarkp-omitted-alist-only)
      (bookmarkp-bmenu-unomit-marked)
    (bookmarkp-bmenu-omit-marked)))

;;;###autoload
(defun bookmarkp-bmenu-omit-marked () ; `O >' in bookmark list
  "Omit all marked bookmarks.
They will henceforth be invisible to the bookmark list.
You can, however, use \\<bookmark-bmenu-mode-map>`\\[bookmarkp-bmenu-show-only-omitted]' to see them.
You can then mark some of them and use `\\[bookmarkp-bmenu-omit/unomit-marked]' to make those marked
 available again for the bookmark list."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (let ((o-str    (and (not (looking-at "^>")) (bookmark-bmenu-bookmark)))
        (o-point  (point))
        (count    0))
    (message "Omitting marked bookmarks...")
    (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (setq bookmarkp-bmenu-omitted-list  (cons (bookmark-bmenu-bookmark)
                                                bookmarkp-bmenu-omitted-list)
            count                         (1+ count)))
    (if (<= count 0)
        (message "No marked bookmarks")
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (message "Omitted %d bookmarks" count))
    (if o-str
        (bookmarkp-bmenu-goto-bookmark-named o-str)
      (goto-char o-point)
      (beginning-of-line)))
  (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))

;;;###autoload
(defun bookmarkp-bmenu-unomit-marked () ; `O >' in bookmark list when showing omitted bookmarks
  "Remove all marked bookmarks from the list of omitted bookmarks.
They will henceforth be available for display in the bookmark list.
\(In order to see and then mark omitted bookmarks you must use \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-bmenu-show-only-omitted]'.)"
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (unless bookmarkp-bmenu-omitted-list (error "No omitted bookmarks to UN-omit"))
  (unless (eq bookmarkp-bmenu-filter-function  'bookmarkp-omitted-alist-only)
    (error "You must use command `bookmarkp-bmenu-show-only-omitted' first"))
  (let ((count    0))
    (message "UN-omitting marked bookmarks...")
    (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
    (while (re-search-forward "^>" (point-max) t)
      (let ((bmk-name  (bookmark-bmenu-bookmark)))
        (when (member bmk-name bookmarkp-bmenu-omitted-list)
          (setq bookmarkp-bmenu-omitted-list  (delete bmk-name bookmarkp-bmenu-omitted-list)
                count                         (1+ count)))))
    (if (<= count 0)
        (message "No marked bookmarks")
      (setq bookmarkp-bmenu-filter-function  nil
            bookmarkp-bmenu-title            "All Bookmarks"
            bookmarkp-latest-bookmark-alist  bookmark-alist)
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (message "UN-omitted %d bookmarks" count)))
  (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))

;;;###autoload
(defun bookmarkp-unomit-all ()          ; `O U' in bookmark list
  "Remove all bookmarks from the list of omitted bookmarks.
All bookmarks will henceforth be available for display."
  (interactive)
  (unless bookmarkp-bmenu-omitted-list (error "No omitted bookmarks to UN-omit"))
  (message "UN-omitting ALL omitted bookmarks...")
  (let ((count  0))
    (dolist (bmk-name  bookmarkp-bmenu-omitted-list)
      (setq bookmarkp-bmenu-omitted-list  (delete bmk-name bookmarkp-bmenu-omitted-list)
            count                         (1+ count)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (message "UN-omitted %d bookmarks" count))
  (when (equal (buffer-name (current-buffer)) "*Bookmark List*") (bookmarkp-bmenu-show-all))
  (when (and (fboundp 'fit-frame-if-one-window)
             (equal (buffer-name (current-buffer)) "*Bookmark List*"))
    (fit-frame-if-one-window)))

;;;###autoload
(defun bookmarkp-bmenu-show-only-omitted () ; `O S' in bookmark list to show only omitted
  "Show only the omitted bookmarks.
You can then mark some of them and use `bookmarkp-bmenu-unomit-marked'
 to make those that are marked available again for the bookmark list."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (unless bookmarkp-bmenu-omitted-list (error "No omitted bookmarks"))
  (setq bookmarkp-bmenu-filter-function  'bookmarkp-omitted-alist-only
        bookmarkp-bmenu-title            "Omitted Bookmarks")
  (let ((bookmark-alist  (funcall bookmarkp-bmenu-filter-function)))
    (setq bookmarkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order)
                                    "Only omitted bookmarks are shown now")))

(defun bookmarkp-omitted-alist-only ()
  "`bookmark-alist', filtered to retain only the omitted bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-omitted-bookmark-p bookmark-alist))

(defun bookmarkp-omitted-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an omitted bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (unless (stringp bookmark) (setq bookmark  (car bookmark)))
  (member bookmark bookmarkp-bmenu-omitted-list))


;;(@* "Search-and-Replace Locations of Marked Bookmarks")
;;  *** Search-and-Replace Locations of Marked Bookmarks ***

;;;###autoload
(when (> emacs-major-version 22)

  (defvar bookmarkp-isearch-bookmarks nil)

  (defun bookmarkp-isearch-next-bookmark-buffer (&optional bookmark wrap)
    "Return the next buffer in a series of bookmark buffers.
Used as a value for `multi-isearch-next-buffer-function', for Isearch
of multiple bookmarks.

Variable `bookmarkp-isearch-bookmarks' is a list of bookmark names.
Each bookmark in that list is visited by `bookmark--jump-via', and the
corresponding bookmark buffer is returned."
    (let ((bookmarks  (if isearch-forward
                          bookmarkp-isearch-bookmarks
                        (reverse bookmarkp-isearch-bookmarks))))
      (bookmark--jump-via
       (if wrap
           (car bookmarks)
         (let ((this-bmk  (catch 'bookmarkp-isearch-next-bookmark-buffer
                            (dolist (bmk  bookmarks)
                              (when (if (bookmarkp-get-buffer-name bmk)
                                        (equal (bookmarkp-get-buffer-name bmk) (buffer-name))
                                      (equal (bookmark-get-filename bmk) (buffer-file-name)))
                                (throw 'bookmarkp-isearch-next-bookmark-buffer bmk)))
                            (car bookmarks))))
           (cadr (member this-bmk bookmarks))))
       'ignore)
      (current-buffer)))

  (defun bookmarkp-isearch-bookmarks (bookmarks)
    "Start multi-bookmark Isearch on BOOKMARKS."
    (let ((multi-isearch-next-buffer-function  'bookmarkp-isearch-next-bookmark-buffer)
          (bookmarkp-isearch-bookmarks         bookmarks))
      (bookmark-jump (car bookmarks))
      (goto-char (if isearch-forward (point-min) (point-max)))
      (isearch-forward)))

  (defun bookmarkp-isearch-bookmarks-regexp (bookmarks)
    "Start multi-bookmark regexp Isearch on BOOKMARKS."
    (let ((multi-isearch-next-buffer-function  'bookmarkp-isearch-next-bookmark-buffer)
          (bookmarkp-isearch-bookmarks         bookmarks))
      (bookmark-jump (car bookmarks))
      (goto-char (if isearch-forward (point-min) (point-max)))
      (isearch-forward-regexp)))

  (defun bookmarkp-bmenu-isearch-marked-bookmarks () ; `M-s a C-s' in bookmark list
    "Isearch the marked bookmark locations, in their current order."
    (interactive)
    (bookmarkp-barf-if-not-in-menu-list)
    (let ((bookmarks                  (mapcar #'car (bookmarkp-sort-and-remove-dups
                                                     (bookmarkp-marked-bookmarks-only))))
          (bookmarkp-use-region-flag  nil)) ; Suppress region handling.
      (bookmarkp-isearch-bookmarks bookmarks)))

  (defun bookmarkp-bmenu-isearch-marked-bookmarks-regexp () ; `M-s a M-C-s' in bookmark list
    "Regexp Isearch the marked bookmark locations, in their current order."
    (interactive)
    (bookmarkp-barf-if-not-in-menu-list)
    (let ((bookmarks                  (mapcar #'car (bookmarkp-sort-and-remove-dups
                                                     (bookmarkp-marked-bookmarks-only))))
          (bookmarkp-use-region-flag  nil)) ; Suppress region handling.
      (bookmarkp-isearch-bookmarks-regexp bookmarks))))

(defun bookmarkp-bmenu-search-marked-bookmarks-regexp (regexp) ; `M-a' in bookmark list
  "Search the marked file bookmarks, in their current order, for REGEXP.
Use `\\[tags-loop-continue]' to advance among the search hits.
Marked directory and non-file bookmarks are ignored."
  (interactive "sSearch marked file bookmarks (regexp): ")
  (bookmarkp-barf-if-not-in-menu-list)
  (tags-search regexp '(let ((files  ())
                             file)
                        (dolist (bmk  (bookmarkp-sort-and-remove-dups
                                       (bookmarkp-marked-bookmarks-only)))
                          (setq file  (bookmark-get-filename bmk))
                          (when (and (not (equal bookmarkp-non-file-filename file))
                                     (not (file-directory-p file)))
                            (push file files)))
                        (setq files  (nreverse files)))))

(defun bookmarkp-bmenu-query-replace-marked-bookmarks-regexp (from to ; `M-q' in bookmark list
                                                              &optional delimited)
  "`query-replace-regexp' FROM with TO, for all marked file bookmarks.
DELIMITED (prefix arg) means replace only word-delimited matches.
If you exit (`\\[keyboard-quit]', `RET' or `q'), you can use \
`\\[tags-loop-continue]' to resume where
you left off."
  (interactive (let ((common  (query-replace-read-args "Query replace regexp in marked files" t t)))
                 (list (nth 0 common) (nth 1 common) (nth 2 common))))
  (bookmarkp-barf-if-not-in-menu-list)
  (tags-query-replace from to delimited
		      '(let ((files  ())
                             file)
                        (dolist (bmk  (bookmarkp-sort-and-remove-dups
                                       (bookmarkp-marked-bookmarks-only)))
                          (setq file  (bookmark-get-filename bmk))
                          (let ((buffer  (get-file-buffer file)))
                            (when (and buffer  (with-current-buffer buffer buffer-read-only))
                              (error "File `%s' is visited read-only" file)))
                          (when (and (not (equal bookmarkp-non-file-filename file))
                                     (not (file-directory-p file)))
                            (push file files)))
                        (setq files  (nreverse files)))))


;;(@* "Tags")
;;  *** Tags ***

(defun bookmarkp-get-tags (bookmark)
  "Return the `tags' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'tags))

(defun bookmarkp-get-tag-value (bookmark tag &optional msgp)
  "Return value of BOOKMARK's tag TAG.
BOOKMARK is a bookmark name or a bookmark record.
TAG is a string.
Return nil if BOOKMARK has no such TAG or if TAG has no value."
  (assoc-default tag (bookmarkp-get-tags bookmark)))

(defun bookmarkp-has-tag-p (bookmark tag &optional msgp)
  "Return non-nil if BOOKMARK is tagged with TAG.
BOOKMARK is a bookmark name or a bookmark record.
TAG is a string."
  (assoc-default tag (bookmarkp-get-tags bookmark) nil t))

;; NOT USED currently - we use `bookmarkp-read-tags-completing' instead.
(defun bookmarkp-read-tags ()
  "Read tags one by one, and return them as a list."
  (let ((tag    (read-string "Tag (RET for each, empty input to finish): "))
        (btags  ()))
    (while (not (string= "" tag))
      (push tag btags)
      (setq tag  (read-string "Tag: ")))
    btags))

(defun bookmarkp-read-tag-completing (&optional prompt candidate-tags require-match
                                      update-tags-alist-p)
  "Read a tag with completion, and return it as a string.
PROMPT is the prompt string.  If nil, then use \"Tag: \".
CANDIDATE-TAGS is an alist of tags used for completion.
 If nil, then all tags from all bookmarks are used for completion.
 The set of all tags is taken from variable `bookmarkp-tags-alist'.
REQUIRE-MATCH is passed to `completing-read'.
Non-nil UPDATE-TAGS-ALIST-P means update var `bookmarkp-tags-alist'."
  (bookmark-maybe-load-default-file)
  (let ((cand-tags  (copy-sequence      ; $$$$$$$ Maybe need `copy-alist'?
                     (or candidate-tags
                         (and (not update-tags-alist-p) bookmarkp-tags-alist) ; Use cached list.
                         (bookmarkp-tags-list))))) ; Update the cache.
    (completing-read (or prompt "Tag: ") cand-tags nil require-match nil 'bookmarkp-tag-history)))

(defun bookmarkp-read-tags-completing (&optional candidate-tags require-match update-tags-alist-p)
  "Read tags with completion, and return them as a list of strings.
Reads tags one by one, until you hit `RET' twice consecutively.
CANDIDATE-TAGS is an alist of tags used for completion.
 If nil, then all tags from all bookmarks are used for completion.
 The set of all tags is taken from variable `bookmarkp-tags-alist'.
REQUIRE-MATCH is passed to `completing-read'.
Non-nil UPDATE-TAGS-ALIST-P means update var `bookmarkp-tags-alist'."
  (bookmark-maybe-load-default-file)
  (let* ((cand-tags  (copy-sequence     ; $$$$$$$ Maybe need `copy-alist'?
                      (or candidate-tags
                          (and (not update-tags-alist-p) bookmarkp-tags-alist) ; Use cached list.
                          (bookmarkp-tags-list)))) ; Update the cache.
         (tag        (completing-read "Tag (RET for each, empty input to finish): "
                                      cand-tags nil require-match nil 'bookmarkp-tag-history))
         (btags      ())
         old-tag)
    (while (setq old-tag  (or (assoc tag cand-tags) (member tag cand-tags))) ; Remove existing.
      (setq cand-tags  (delete old-tag cand-tags)))
    (while (not (string= "" tag))
      (push tag btags)
      (setq tag  (completing-read "Tag: " cand-tags nil require-match nil 'bookmarkp-tag-history))
      (while (setq old-tag  (or (assoc tag cand-tags) (member tag cand-tags)))
        (setq cand-tags  (delete old-tag cand-tags))))
    (nreverse btags)))

;;;###autoload
(defun bookmarkp-list-all-tags (fullp)  ; `T l' in bookmark list
  "List all tags used for any bookmarks.
With a prefix argument, list the full alist of tags.
Otherwise, list only the tag names.

Note that when the full alist is shown, the same tag name will appear
once for each of its different values.

Show list in minibuffer or, if not enough space, buffer `*All Tags*'."
  (interactive "P")
  (require 'pp)
  (pp-display-expression (bookmarkp-tags-list (not fullp)) "*All Tags"))
  
(defun bookmarkp-tags-list (&optional names-only-p)
  "Current list of all tags, from all bookmarks.
Non-nil NAMES-ONLY-P means return a list of only the tag names.
Otherwise, return an alist of the full tags and set variable
`bookmarkp-tags-alist' to that alist, as a cache."
  (bookmark-maybe-load-default-file)
  (let ((tags  ())
        bmk-tags)
    (dolist (bmk  bookmark-alist)
      (setq bmk-tags  (bookmarkp-get-tags bmk))
      (dolist (tag  bmk-tags)
        (add-to-list 'tags (if names-only-p (bookmarkp-tag-name tag) (bookmarkp-full-tag tag)))))
    (unless names-only-p (setq bookmarkp-tags-alist  tags))
    tags))

(defun bookmarkp-tag-name (tag)
  "Name of TAG.  If TAG is an atom, then TAG, else (car TAG)."
  (if (atom tag) tag (car tag)))

(defun bookmarkp-full-tag (tag)
  "Full cons entry for TAG.  If TAG is a cons, then TAG, else (list TAG)."
  (if (consp tag) tag (list tag)))

;;;###autoload
(defun bookmarkp-remove-all-tags (bookmark &optional msgp) ; `T 0' in bookmark list
  "Remove all tags from BOOKMARK.
Non-nil optional arg MSGP means display a message about the removal."
  (interactive (list (bookmark-completing-read "Bookmark" (bookmarkp-default-bookmark-name)) 'msg))
  (when (and msgp (null (bookmarkp-get-tags bookmark))) (error "Bookmark has no tags to remove"))
  (let ((nb-removed  (and (interactive-p) (length (bookmarkp-get-tags bookmark)))))
    (bookmark-prop-set bookmark 'tags ())
    (bookmarkp-maybe-save-bookmarks)
    (when (and msgp nb-removed) (message "%d tags removed" nb-removed)))
  (when (get-buffer-window (get-buffer-create "*Bookmark List*"))
    (bookmarkp-refresh-menu-list bookmark))) ; So the `t' markers are removed.

;;;###autoload
(defun bookmarkp-bmenu-remove-all-tags (&optional must-confirm-p)
  "Remove all tags from this bookmark.
Interactively, you are required to confirm."
  (interactive "p")
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bookmark  (bookmark-bmenu-bookmark)))
    (when (and must-confirm-p (null (bookmarkp-get-tags bookmark)))
      (error "Bookmark has no tags to remove"))
    (when (or (not must-confirm-p) (y-or-n-p "Remove all tags from this bookmark? "))
      (bookmarkp-remove-all-tags bookmark))))

;;;###autoload
(defun bookmarkp-add-tags (bookmark tags &optional msgp no-cache-update-p) ; `T +' in bookmark list
  "Add TAGS to BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
Completion for the bookmark name is strict.
Completion for tags is lax: you are not limited to existing tags.

TAGS is a list of strings.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bookmarkp-tags-alist'.
Return the number of tags added."
  (interactive (list (bookmark-completing-read "Bookmark" (bookmarkp-default-bookmark-name))
                     (bookmarkp-read-tags-completing)
                     'msg))
  (let* ((newtags  (copy-alist (bookmarkp-get-tags bookmark)))
         (olen     (length newtags)))
    (dolist (tag  tags)  (unless (or (assoc tag newtags) (member tag newtags))  (push tag newtags)))
    (bookmark-prop-set bookmark 'tags newtags)
    (unless no-cache-update-p (bookmarkp-tags-list)) ; Update the tags cache.
    (bookmarkp-maybe-save-bookmarks)
    (when (get-buffer-window (get-buffer-create "*Bookmark List*"))
      (bookmarkp-refresh-menu-list bookmark)) ; So the `t' markers are displayed (updated).
    (let ((nb-added  (- (length newtags) olen)))
      (when msgp (message "%d tags added. Now: %S" nb-added ; Echo just the tag names.
                          (let ((ts  (mapcar #'bookmarkp-tag-name newtags)))
                            (setq ts (sort ts #'string<)))))
      nb-added)))

;;;###autoload
(defun bookmarkp-bmenu-add-tags ()
  "Add some tags to this bookmark."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (bookmarkp-add-tags (bookmark-bmenu-bookmark) (bookmarkp-read-tags-completing)))

;;;###autoload
(defun bookmarkp-set-tag-value (bookmark tag value &optional msgp)
  "For BOOKMARK's TAG, set the value to VALUE.
If BOOKMARK has no tag named TAG, then add one with value VALUE."
  (interactive
   (let* ((bmk  (bookmark-completing-read "Bookmark" (bookmarkp-default-bookmark-name)))
          (tag  (bookmarkp-read-tag-completing "Tag: " (mapcar 'bookmarkp-full-tag
                                                               (bookmarkp-get-tags bmk)))))
     (list bmk tag (read (read-string "Value: ")) 'msg)))
  (unless (bookmarkp-has-tag-p bookmark tag) (bookmarkp-add-tags bookmark (list tag)))
  (let* ((newtags     (copy-alist (bookmarkp-get-tags bookmark)))
         (assoc-tag   (assoc tag newtags))
         (member-tag  (and (not assoc-tag) (member tag newtags))))
    (if assoc-tag
        (setcdr assoc-tag value)
      (setcar member-tag (cons (car member-tag) value)))
    (bookmark-prop-set bookmark 'tags newtags))
  (when msgp "Tag value added"))

;;;###autoload
(defun bookmarkp-bmenu-set-tag-value ()
  "Set the value of one of this bookmark's tags."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((this-bmk  (bookmark-bmenu-bookmark)))
    (bookmarkp-set-tag-value this-bmk
                             (bookmarkp-read-tag-completing
                              "Tag: " (mapcar 'bookmarkp-full-tag (bookmarkp-get-tags this-bmk)))
                             (read (read-string "Value: "))
                             'msg)))

;;;###autoload
(defun bookmarkp-remove-tags (bookmark tags &optional msgp no-cache-update-p) ; `T -' in bookmark list
  "Remove TAGS from BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

TAGS is a list of strings.  The corresponding tags are removed.
Non-nil MSGP means display messages.
Non-nil NO-CACHE-UPDATE-P means do not update `bookmarkp-tags-alist'."
  (interactive (let ((bmk  (bookmark-completing-read "Bookmark" (bookmarkp-default-bookmark-name))))
                 (list bmk  (bookmarkp-read-tags-completing
                             (mapcar 'bookmarkp-full-tag (bookmarkp-get-tags bmk))
                             t)
                       'msg)))
  (let* ((newtags  (copy-alist (bookmarkp-get-tags bookmark)))
         (olen     (length newtags)))
    (if (null newtags)
        (when msgp (message "Bookmark has no tags to remove")) ; Do nothing if bookmark has no tags.
      (setq newtags  (bookmarkp-remove-if
                      #'(lambda (tt) (if (atom tt) (member tt tags) (member (car tt) tags)))
                      newtags))
      (bookmark-prop-set bookmark 'tags newtags)
      (unless no-cache-update-p (bookmarkp-tags-list)) ; Update the tags cache.
      (bookmarkp-maybe-save-bookmarks)
      (when (get-buffer-window (get-buffer-create "*Bookmark List*"))
        (bookmarkp-refresh-menu-list bookmark)) ; So the `t' markers are removed.
      (let ((nb-removed  (- olen (length newtags))))
        (when msgp (message "%d tags removed. Now: %S" nb-removed ; Echo just the tag names.
                            (let ((ts  (mapcar #'bookmarkp-tag-name newtags)))
                              (setq ts (sort ts #'string<)))))
        nb-removed))))

;;;###autoload
(defun bookmarkp-bmenu-remove-tags (&optional msgp)
  "Remove some tags from this bookmark."
  (interactive "p")
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let ((bmk  (bookmark-bmenu-bookmark)))
    (bookmarkp-remove-tags bmk (bookmarkp-read-tags-completing
                                (mapcar 'bookmarkp-full-tag (bookmarkp-get-tags bmk))
                                t)
                           msgp)))

;;;###autoload
(defun bookmarkp-remove-tags-from-all (tags &optional msgp) ; `T d'
  "Remove TAGS from all bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.
This affects all bookmarks, even those not showing in bookmark list.

TAGS is a list of strings.  The corresponding tags are removed.
Non-nil optional arg MSGP means display a message about the deletion."
  (interactive
   (if (not (y-or-n-p
             "Delete the tags you specify from ALL bookmarks, even those not shown? "))
       (error "Deletion cancelled")
     (list (bookmarkp-read-tags-completing nil t)  'MSG)))
  (dolist (bmk  (bookmark-all-names)) (bookmarkp-remove-tags bmk tags nil 'NO-CACHE-UPDATE))
  (bookmarkp-tags-list)                ; Update the tags cache (only once, at end).
  (when msgp (message "Tags removed from all bookmarks: %S" tags)))

;;;###autoload
(defun bookmarkp-rename-tag (tag newname &optional msgp) ; `T r'
  "Rename TAG to NEWNAME in all bookmarks, even those not showing.
Non-nil optional arg MSGP means display a message about the deletion."
  (interactive (list (bookmarkp-read-tag-completing "Tag (old name): ")
                     (bookmarkp-read-tag-completing "New name: ")
                     'MSG))
  (let ((tag-exists-p  nil))
    (dolist (bmk  (bookmark-all-names))
      (let ((newtags  (copy-alist (bookmarkp-get-tags bmk))))
        (when newtags
          (let* ((assoc-tag   (assoc tag newtags))
                 (member-tag  (and (not assoc-tag) (member tag newtags))))
            (cond (assoc-tag  (setcar assoc-tag newname))
                  (member-tag (setcar member-tag newname)))
            (when (or assoc-tag member-tag)
              (setq tag-exists-p  t)
              (bookmark-prop-set bmk 'tags newtags))))))
    (if tag-exists-p
        (bookmarkp-tags-list)           ; Update the tags cache.
      (error "No such tag: `%s'" tag))
    (when msgp (message "Renamed"))))

;;;###autoload
(defun bookmarkp-bmenu-add-tags-to-marked (tags &optional msgp) ; `T > +' in bookmark list
  "Add TAGS to each of the marked bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag, but you are not limited to
choosing existing tags."
  (interactive (list (bookmarkp-read-tags-completing) 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (when msgp (message "Adding tags..."))
  (dolist (bmk  (mapcar #'car (bookmarkp-marked-bookmarks-only)))
    (bookmarkp-add-tags bmk tags nil 'NO-CACHE-UPDATE))
  (bookmarkp-tags-list)                 ; Update the tags cache (only once, at end).
  (when msgp (message "Tags added: %S" tags)))

;;;###autoload
(defun bookmarkp-bmenu-remove-tags-from-marked (tags &optional msgp) ; `T > -' in bookmark list
  "Remove TAGS from each of the marked bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag."
  (interactive (let ((cand-tags  ()))
                 (dolist (bmk  (bookmarkp-marked-bookmarks-only))
                   (setq cand-tags  (bookmarkp-set-union cand-tags (bookmarkp-get-tags bmk))))
                 (list (bookmarkp-read-tags-completing cand-tags t) 'msg)))
  (bookmarkp-barf-if-not-in-menu-list)
  (when msgp (message "Removing tags..."))
  (dolist (bmk  (mapcar #'car (bookmarkp-marked-bookmarks-only)))
    (bookmarkp-remove-tags bmk tags nil 'NO-CACHE-UPDATE))
  (bookmarkp-tags-list)                 ; Update the tags cache (only once, at end).
  (when msgp (message "Tags removed: %S" tags)))

;;;###autoload
(defun bookmarkp-bmenu-mark-bookmarks-tagged-regexp (regexp &optional notp) ; `T m %' in menu
  "Mark bookmarks any of whose tags match REGEXP.
With a prefix arg, mark all that are tagged but with no tags that match."
  (interactive "sRegexp: \nP")
  (bookmarkp-barf-if-not-in-menu-list)
  (save-excursion
    (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
    (let ((count  0)
          tags anyp)
      (while (not (eobp))
        (setq tags  (bookmarkp-get-tags (bookmark-bmenu-bookmark))
              anyp  (and tags (bookmarkp-some (lambda (tag)
                                                (string-match regexp (bookmarkp-tag-name tag)))
                                              tags)))
        (if (not (and tags (if notp (not anyp) anyp)))
            (forward-line 1)
          (bookmark-bmenu-mark)
          (setq count  (1+ count))))
      (if (= 1 count) (message "1 bookmark matched") (message "%d bookmarks matched" count)))))

;;;###autoload
(defun bookmarkp-bmenu-mark-bookmarks-tagged-all (tags ; `T m *' in bookmark list
                                                  &optional nonep msgp)
  "Mark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all (i.e., at least one tag).

With a prefix arg, mark all that are *not* tagged with *any* TAGS."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags nonep nil msgp))

;;;###autoload
(defun bookmarkp-bmenu-mark-bookmarks-tagged-none (tags ; `T m ~ +' in bookmark list
                                                   &optional allp msgp)
  "Mark all visible bookmarks that are not tagged with *any* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *each* tag in TAGS."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags (not allp) nil msgp))

;;;###autoload
(defun bookmarkp-bmenu-mark-bookmarks-tagged-some (tags ; `T m +' in bookmark list
                                                   &optional somenotp msgp)
  "Mark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all.

With a prefix arg, mark all that are *not* tagged with *all* TAGS.

Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags somenotp nil msgp))

;;;###autoload
(defun bookmarkp-bmenu-mark-bookmarks-tagged-not-all (tags ; `T m ~ *' in bookmark list
                                                      &optional somep msgp)
  "Mark all visible bookmarks that are *not* tagged with *all* TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.

With a prefix arg, mark all that are tagged with *some* tag in TAGS."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags (not somep) nil msgp))

;;;###autoload
(defun bookmarkp-bmenu-unmark-bookmarks-tagged-all (tags ; `T u *' in bookmark list
                                                    &optional nonep msgp)
  "Unmark all visible bookmarks that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *any* TAGS."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags nonep 'unmark msgp))

;;;###autoload
(defun bookmarkp-bmenu-unmark-bookmarks-tagged-none (tags ; `T u ~ +' in bookmark list
                                                     &optional allp msgp)
  "Unmark all visible bookmarks that are *not* tagged with *any* TAGS.
With a prefix arg, unmark all that are tagged with *each* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-all/none tags (not allp) 'unmark msgp))

;;;###autoload
(defun bookmarkp-bmenu-unmark-bookmarks-tagged-some (tags ; `T u +' in bookmark list
                                                     &optional somenotp msgp)
  "Unmark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then unmark the bookmarks that have
any tags at all.

With a prefix arg, unmark all that are *not* tagged with *all* TAGS."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags somenotp 'unmark msgp))

;;;###autoload
(defun bookmarkp-bmenu-unmark-bookmarks-tagged-not-all (tags ; `T u ~ *' in bookmark list
                                                        &optional somep msgp)
  "Unmark all visible bookmarks that are tagged with *some* tag in TAGS.
As a special case, if TAGS is empty, then mark the bookmarks that have
no tags at all.
With a prefix arg, unmark all that are *not* tagged with *all* TAGS."
  (interactive (list (bookmarkp-read-tags-completing) current-prefix-arg 'msg))
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmarkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all tags (not somep) 'unmark msgp))

(defun bookmarkp-bmenu-mark/unmark-bookmarks-tagged-all/none (tags &optional nonep unmarkp msgp)
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
        (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
        (while (not (eobp))
          (setq bmktags  (bookmarkp-get-tags (bookmark-bmenu-bookmark)))
          (if (not (if (null tags)
                       (if nonep (not bmktags) bmktags)
                     (and bmktags  (catch 'bookmarkp-b-mu-b-t-an
                                     (dolist (tag  tags)
                                       (setq presentp  (assoc-default tag bmktags nil t))
                                       (unless (if nonep (not presentp) presentp)
                                         (throw 'bookmarkp-b-mu-b-t-an nil)))
                                     t))))
              (forward-line 1)
            (if unmarkp (bookmark-bmenu-unmark) (bookmark-bmenu-mark))
            (setq count  (1+ count))))
        (when msgp (if (= 1 count)
                       (message "1 bookmark matched")
                     (message "%d bookmarks matched" count)))))))

(defun bookmarkp-bmenu-mark/unmark-bookmarks-tagged-some/not-all (tags &optional notallp
                                                                  unmarkp msgp)
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
        (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
        (while (not (eobp))
          (setq bmktags  (bookmarkp-get-tags (bookmark-bmenu-bookmark)))
          (if (not (if (null tags)
                       (if notallp (not bmktags) bmktags)
                     (and bmktags  (catch 'bookmarkp-b-mu-b-t-sna
                                     (dolist (tag  tags)
                                       (setq presentp  (assoc-default tag bmktags nil t))
                                       (when (if notallp (not presentp) presentp)
                                         (throw 'bookmarkp-b-mu-b-t-sna t)))
                                     nil))))
              (forward-line 1)
            (if unmarkp (bookmark-bmenu-unmark) (bookmark-bmenu-mark))
            (setq count  (1+ count))))
        (when msgp (if (= 1 count)
                       (message "1 bookmark matched")
                     (message "%d bookmarks matched" count)))))))


;;(@* "General Menu-List (`-*bmenu-*') Commands and Functions")
;;  *** General Menu-List (`-*bmenu-*') Commands and Functions ***

;;;###autoload
(defun bookmarkp-empty-file (file)
  "Empty the bookmark file FILE, or create FILE (empty) if it does not exist.
In either case, FILE will become an empty bookmark file.

NOTE: If FILE already exists and you confirm emptying it, no check is
      made that it is in fact a bookmark file before emptying it.
      It is simply replaced by an empty bookmark file and saved.

This does NOT also make FILE the current bookmark file.  To do that,
use `\\[bookmarkp-switch-bookmark-file]' (`bookmarkp-switch-bookmark-file')."
  (interactive (list (read-file-name "Create empty bookmark file: " "~/")))
  (bookmark-maybe-load-default-file)
  (when (and (file-exists-p file)
             (not (y-or-n-p (format "CONFIRM: Empty the existing file `%s'? " file))))
    (error "OK, cancelled"))
  (let ((bookmark-alist  ()))
    (bookmark-write-file file (if (file-exists-p file)
                                  "Emptying bookmark file `%s'..."
                                "Creating new, empty bookmark file `%s'..."))))

;;;###autoload
(defun bookmarkp-bmenu-w32-open ()      ; `M-RET' in bookmark list.
  "Use `w32-browser' to open this bookmark."
  (interactive)
  (let ((bookmarkp-use-w32-browser-p  t))
    (bookmark-bmenu-this-window)))

;;;###autoload
(defun bookmarkp-bmenu-w32-open-with-mouse (event) ; `M-mouse-2' in bookmark list.
  "Use `w32-browser' to open the bookmark clicked."
  (interactive "e")
  (save-excursion
    (set-buffer (window-buffer (posn-window (event-end event))))
    (save-excursion
      (goto-char (posn-point (event-end event)))
      (let ((bookmarkp-use-w32-browser-p  t))
        (bookmark-bmenu-other-window)))))

;;;###autoload
(defun bookmarkp-bmenu-w32-open-select () ; `V' in bookmark-list.
  "Use `w32-browser' to open this bookmark and all marked bookmarks."
  (interactive)
  (let ((bookmarkp-use-w32-browser-p  t))
    (bookmark-bmenu-select)))

;;;###autoload
(defun bookmarkp-bmenu-mode-status-help () ; `C-h m' and `?' in bookmark list
  "`describe-mode' + current status of `*Bookmark List*' + face legend."
  (interactive)
  (unless (string= (buffer-name) "*Help*") (bookmarkp-barf-if-not-in-menu-list))
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
          (help-setup-xref (list #'bookmarkp-bmenu-mode-status-help) (interactive-p))
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
                     (require 'help-mode nil t) (fboundp 'help-insert-xref-button))
            (help-insert-xref-button "[Doc in Commentary]" 'bookmarkp-commentary-button)
            (insert "           ")
            (help-insert-xref-button "[Doc on the Web]" 'bookmarkp-help-button)
            (insert "           ")
            (help-insert-xref-button "[Customize]" 'bookmarkp-customize-button)
            (insert "\n\n")
            (setq top  (point))
            (goto-char (point-max))
            (insert "\nSend a Bookmark+ bug report: `\\[icicle-send-bug-report]'.\n\n")
            (help-insert-xref-button "[Doc in Commentary]" 'bookmarkp-commentary-button)
            (insert "           ")
            (help-insert-xref-button "[Doc on the Web]" 'bookmarkp-help-button)
            (insert "           ")
            (help-insert-xref-button "[Customize]" 'bookmarkp-customize-button)
            (insert "\n\n")
            (goto-char (point-min))
            (forward-line 2))
          (goto-char top)
          (insert
           (format
            "\nCurrent Status\n-------------------------------\n
Sorted:\t\t%s\nFiltering:\t%s\nMarked:\t\t%d\nOmitted:\t%d\nBookmark file:\t%s\n\n\n"
            (if (not bookmarkp-sort-comparer)
                "no"
              (format
               "%s%s" (bookmarkp-current-sort-order)
               ;; Code essentially the same as found in `bookmarkp-msg-about-sort-order'.
               (if (not (and (consp bookmarkp-sort-comparer) ; Ordinary single predicate
                             (consp (car bookmarkp-sort-comparer))))
                   (if bookmarkp-reverse-sort-p "; reversed" "")
                 (if (not (cadr (car bookmarkp-sort-comparer)))
                     ;; Single PRED.
                     (if (or (and bookmarkp-reverse-sort-p (not bookmarkp-reverse-multi-sort-p))
                             (and bookmarkp-reverse-multi-sort-p (not bookmarkp-reverse-sort-p)))
                         "; reversed"
                       "")
                   ;; In case we want to distinguish:
                   ;; (if (and bookmarkp-reverse-sort-p
                   ;;          (not bookmarkp-reverse-multi-sort-p))
                   ;;     "; reversed"
                   ;;   (if (and bookmarkp-reverse-multi-sort-p
                   ;;            (not bookmarkp-reverse-sort-p))
                   ;;       "; reversed +"
                   ;;     ""))

                   ;; At least two PREDs.
                   (cond ((and bookmarkp-reverse-sort-p (not bookmarkp-reverse-multi-sort-p))
                          "; reversed")
                         ((and bookmarkp-reverse-multi-sort-p (not bookmarkp-reverse-sort-p))
                          "; each predicate group reversed")
                         ((and bookmarkp-reverse-multi-sort-p bookmarkp-reverse-sort-p)
                          "; order of predicate groups reversed")
                         (t ""))))))
            (or (and bookmarkp-bmenu-filter-function (downcase bookmarkp-bmenu-title)) "None")
            (length bookmarkp-bmenu-marked-bookmarks)
            (length bookmarkp-bmenu-omitted-list)
            bookmarkp-current-bookmark-file))
          ;; Add face legend.
          (let ((info             "Info node\n")
                (gnus             "Gnus\n")
                (w3m              "W3M (URL)\n")
                (local-no-region  "Local file with no region\n")
                (local-w-region   "Local file with a region\n")
                (no-buf           "No current buffer\n")
                (bad              "Possibly invalid bookmark\n")
                (remote           "Remote file or directory\n")
                (sudo             "Remote accessed by `su' or `sudo'\n")
                (local-dir        "Local directory\n")
                (bookmark-list    "*Bookmark List*\n")
                (desktop          "Desktop\n")
                (function         "Function\n")
                (man              "Man page\n")
                (sequence         "Sequence\n")
                (buffer           "Buffer\n"))
            (put-text-property 0 (1- (length info))     'face 'bookmarkp-info         info)
            (put-text-property 0 (1- (length gnus))     'face 'bookmarkp-gnus         gnus)
            (put-text-property 0 (1- (length w3m))      'face 'bookmarkp-w3m          w3m)
            (put-text-property 0 (1- (length local-no-region))
                               'face 'bookmarkp-local-file-without-region             local-no-region)
            (put-text-property 0 (1- (length local-w-region))
                               'face 'bookmarkp-local-file-with-region                local-w-region)
            (put-text-property 0 (1- (length no-buf))   'face 'bookmarkp-non-file     no-buf)
            (put-text-property 0 (1- (length bad))      'face 'bookmarkp-bad-bookmark bad)
            (put-text-property 0 (1- (length remote))   'face 'bookmarkp-remote-file  remote)
            (put-text-property 0 (1- (length sudo))     'face 'bookmarkp-su-or-sudo   sudo)
            (put-text-property 0 (1- (length local-dir))
                               'face 'bookmarkp-local-directory                       local-dir)
            (put-text-property 0 (1- (length bookmark-list))
                               'face 'bookmarkp-bookmark-list                         bookmark-list)
            (put-text-property 0 (1- (length desktop))  'face 'bookmarkp-desktop      desktop)
            (put-text-property 0 (1- (length function)) 'face 'bookmarkp-function     function)
            (put-text-property 0 (1- (length man))      'face 'bookmarkp-man          man)
            (put-text-property 0 (1- (length sequence)) 'face 'bookmarkp-sequence     sequence)
            (put-text-property 0 (1- (length buffer))   'face 'bookmarkp-buffer       buffer)
            (insert "Face Legend for Bookmark Types\n------------------------------\n\n")
            (insert info) (insert gnus) (insert w3m) (insert local-no-region) (insert local-w-region)
            (insert no-buf) (insert bad) (insert remote) (insert sudo) (insert local-dir)
            (insert bookmark-list) (insert desktop) (insert function) (insert man) (insert sequence)
            (insert buffer) (insert "\n\n")))))))

(when (and (> emacs-major-version 21)
           (require 'help-mode nil t) (get 'help-xref 'button-category-symbol)) ; In `button.el'
  (define-button-type 'bookmarkp-help-button
      :supertype 'help-xref
      'help-function #'(lambda () (browse-url "http://www.emacswiki.org/emacs/BookmarkPlus"))
      'help-echo
      (purecopy "mouse-2, RET: Bookmark+ documentation on the Emacs Wiki (requires Internet access)"))
  (define-button-type 'bookmarkp-commentary-button
      :supertype 'help-xref
      'help-function #'(lambda ()
                         (message "Getting Bookmark+ doc from file commentary...")
                         (finder-commentary "bookmark+-doc")
                         (when (require 'linkd nil t) (linkd-mode 1))
                         (when (require 'fit-frame nil t) (fit-frame)))
      'help-echo (purecopy "mouse-2, RET: Bookmark+ documentation (no Internet needed)"))
  (define-button-type 'bookmarkp-customize-button
      :supertype 'help-xref
      'help-function #'(lambda () (customize-group-other-window 'bookmark-plus))
      'help-echo (purecopy "mouse-2, RET: Customize/Browse Bookmark+ Options & Faces")))

;;;###autoload
(defun bookmarkp-bmenu-define-jump-marked-command () ; `M-c' in bookmark list
  "Define a command to jump to a bookmark that is one of those now marked.
The bookmarks marked now will be those that are completion candidates
for the command (but omitted bookmarks are excluded).
Save the command definition in `bookmarkp-bmenu-commands-file'."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (let* ((cands  (mapcar #'list (bookmarkp-remove-if
                                 #'(lambda (bmk) (member bmk bookmarkp-bmenu-omitted-list))
                                 bookmarkp-bmenu-marked-bookmarks)))
         (fn     (intern (read-string "Define command to jump to a bookmark now marked: " nil
                                      'bookmarkp-bmenu-define-command-history)))
         (def    `(defun ,fn (bookmark-name &optional use-region-p)
                   (interactive (list (bookmarkp-read-bookmark-for-type nil ',cands t)
                                 current-prefix-arg))
                   (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))))
    (eval def)
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bookmarkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bookmarkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (message "Command `%s' defined and saved in file `%s'" fn bookmarkp-bmenu-commands-file)))

;;;###autoload
(defun bookmarkp-bmenu-define-command () ; `c' in bookmark list
  "Define a command to use the current sort order, filter, and omit list.
Prompt for the command name.  Save the command definition in
`bookmarkp-bmenu-commands-file'.

The current sort order, filter function, omit list, and title for
buffer `*Bookmark List*' are encapsulated as part of the command.
Use the command at any time to restore them."
  (interactive)
  (let* ((fn   (intern (read-string "Define sort+filter command: " nil
                                    'bookmarkp-bmenu-define-command-history)))
         (def  `(defun ,fn ()
                 (interactive)
                 (setq
                  bookmarkp-sort-comparer          ',bookmarkp-sort-comparer
                  bookmarkp-reverse-sort-p         ',bookmarkp-reverse-sort-p
                  bookmarkp-reverse-multi-sort-p   ',bookmarkp-reverse-multi-sort-p
                  bookmarkp-bmenu-filter-function  ',bookmarkp-bmenu-filter-function
                  bookmarkp-bmenu-omitted-list     ',bookmarkp-bmenu-omitted-list
                  bookmarkp-bmenu-title            ',bookmarkp-bmenu-title
                  bookmark-bmenu-toggle-filenames  ',bookmark-bmenu-toggle-filenames)
                 (bookmarkp-bmenu-refresh-menu-list)
                 (when (interactive-p)
                   (bookmarkp-msg-about-sort-order
                    (car (rassoc bookmarkp-sort-comparer bookmarkp-sort-orders-alist)))))))
    (eval def)
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bookmarkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bookmarkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (message "Command `%s' defined and saved in file `%s'" fn bookmarkp-bmenu-commands-file)))

;;;###autoload
(defun bookmarkp-bmenu-define-full-snapshot-command () ; `C' in bookmark list
  "Define a command to restore the current bookmark-list state.
Prompt for the command name.  Save the command definition in
`bookmarkp-bmenu-commands-file'.

Be aware that the command definition can be quite large, since it
copies the current bookmark list and accessory lists (hidden
bookmarks, marked bookmarks, etc.).  For a lighter weight command, use
`bookmarkp-bmenu-define-full-snapshot-command' instead.  That records
only the omit list and the sort & filter information."
  (interactive)
  (let* ((fn   (intern (read-string "Define restore-snapshot command: " nil
                                    'bookmarkp-bmenu-define-command-history)))
         (def  `(defun ,fn ()
                 (interactive)
                 (setq
                  bookmarkp-sort-comparer           ',bookmarkp-sort-comparer
                  bookmarkp-reverse-sort-p          ',bookmarkp-reverse-sort-p
                  bookmarkp-reverse-multi-sort-p    ',bookmarkp-reverse-multi-sort-p
                  bookmarkp-latest-bookmark-alist   ',bookmarkp-latest-bookmark-alist
                  bookmarkp-bmenu-omitted-list      ',bookmarkp-bmenu-omitted-list
                  bookmarkp-bmenu-marked-bookmarks  ',bookmarkp-bmenu-marked-bookmarks
                  bookmarkp-bmenu-filter-function   ',bookmarkp-bmenu-filter-function
                  bookmarkp-bmenu-title             ',bookmarkp-bmenu-title
                  bookmarkp-last-bmenu-bookmark     ',(and (get-buffer "*Bookmark List*")
                                                           (with-current-buffer
                                                               (get-buffer "*Bookmark List*")
                                                             (bookmark-bmenu-bookmark)))
                  bookmark-bmenu-toggle-filenames   ',bookmark-bmenu-toggle-filenames
                  bookmarkp-bmenu-before-hide-marked-alist
                  ',bookmarkp-bmenu-before-hide-marked-alist
                  bookmarkp-bmenu-before-hide-unmarked-alist
                  ',bookmarkp-bmenu-before-hide-unmarked-alist
                  bookmarkp-current-bookmark-file   ',bookmarkp-current-bookmark-file)
                 ;;(bookmarkp-bmenu-refresh-menu-list)
                 (let ((bookmark-alist  (or bookmarkp-latest-bookmark-alist bookmark-alist)))
                   (bookmarkp-bmenu-list-1 'filteredp nil (interactive-p)))
                 (when bookmarkp-last-bmenu-bookmark
                   (with-current-buffer (get-buffer "*Bookmark List*")
                     (bookmarkp-bmenu-goto-bookmark-named bookmarkp-last-bmenu-bookmark)))
                 (when (interactive-p)
                   (bookmarkp-msg-about-sort-order
                    (car (rassoc bookmarkp-sort-comparer bookmarkp-sort-orders-alist)))))))
    (eval def)
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bookmarkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bookmarkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (message "Command `%s' defined and saved in file `%s'" fn bookmarkp-bmenu-commands-file)))

;;;###autoload
(defun bookmarkp-define-tags-sort-command (tags &optional msgp) ; 
  "Define a command to sort bookmarks in the bookmark list by tags.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.

The new command sorts first by the first tag in TAGS, then by the
second, and so on.

Besides sorting for these specific tags, any bookmark that has a tag
sorts before one that has no tags.  Otherwise, sorting is by bookmark
name, alphabetically.

The name of the new command is `bookmarkp-bmenu-sort-' followed by the
specified tags, in order, separated by hyphens (`-').  E.g., for TAGS
\(\"alpha\" \"beta\"), the name is `bookmarkp-bmenu-sort-alpha-beta'."
  (interactive (list (bookmarkp-read-tags-completing) 'msg))
  (let ((sort-order  (concat "tags-" (mapconcat #'identity tags "-")))
        (doc-string  (read-string "Doc string for command: "))
        (comparer    ())
        def)
    (dolist (tag  tags)
      (push `(lambda (b1 b2)
              (let ((tags1  (bookmarkp-get-tags b1))
                    (tags2  (bookmarkp-get-tags b2)))
                (cond ((and (assoc-default ,tag tags1 nil t) (assoc-default ,tag tags2 nil t)) nil)
                      ((assoc-default ,tag tags1 nil t) '(t))
                      ((assoc-default ,tag tags2 nil t) '(nil))
                      ((and tags1 tags2) nil)
                      (tags1 '(t))
                      (tags2 '(nil))
                      (t nil))))
            comparer))
    (setq comparer  (nreverse comparer)
          comparer  (list comparer 'bookmarkp-alpha-p))
    (eval (setq def  (macroexpand `(bookmarkp-define-sort-command
                                    ,sort-order ,comparer ,doc-string))))
    (with-current-buffer (get-buffer-create " *User Bookmark List Commands*")
      (goto-char (point-min))
      (delete-region (point-min) (point-max))
      (let ((print-length  nil)
            (print-level   nil))
        (pp def (current-buffer))
        (insert "\n")
        (condition-case nil
            (write-region (point-min) (point-max) bookmarkp-bmenu-commands-file 'append)
          (file-error (error "Cannot write `%s'" bookmarkp-bmenu-commands-file)))
        (kill-buffer (current-buffer))))
    (when msgp (message "Defined and saved command `%s'"
                        (concat "bookmarkp-bmenu-sort-" sort-order)))))

;;;###autoload
(defun bookmarkp-bmenu-edit-bookmark () ; `E' in bookmark list
  "Edit the bookmark under the cursor: its name and file name."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (bookmark-bmenu-ensure-position)
  (let* ((new-data  (bookmarkp-edit-bookmark (bookmark-bmenu-bookmark)))
         (new-name  (car new-data)))
    (if (not new-data)
        (message "No changes made")
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (goto-char (point-min))
      (while (not (equal new-name (bookmark-bmenu-bookmark))) (forward-line 1))
      (forward-line 0))))

(defun bookmarkp-bmenu-propertize-item (bookmark-name start end)
  "Add text properties to BOOKMARK-NAME, from START to END."
  (let* ((buffp      (bookmarkp-get-buffer-name bookmark-name))
         (sequencep  (bookmarkp-sequence-bookmark-p bookmark-name))
         (functionp  (bookmarkp-function-bookmark-p bookmark-name))
         (w3m-p      (bookmarkp-w3m-bookmark-p bookmark-name))
         (gnus-p     (bookmarkp-gnus-bookmark-p bookmark-name))
         (desktop-p  (bookmarkp-desktop-bookmark-p bookmark-name))
         (handlerp   (bookmark-get-handler bookmark-name))
         (info-p     (bookmarkp-info-bookmark-p bookmark-name))
         (man-p      (bookmarkp-man-bookmark-p bookmark-name))
         (blist-p    (bookmarkp-bookmark-list-bookmark-p bookmark-name))
         (regionp    (bookmarkp-region-bookmark-p bookmark-name))

         ;; Begin `let*' dependencies.
         (filep     (bookmark-get-filename bookmark-name))
         (remotep   (and filep  (bookmarkp-file-remote-p filep)))
         (tramp-p   (and filep  (boundp 'tramp-file-name-regexp)
                         (save-match-data (string-match tramp-file-name-regexp filep))))
         (su-p      (and tramp-p (string-match bookmarkp-su-or-sudo-regexp filep))))
    (put-text-property start end 'bookmarkp-bookmark-name bookmark-name)
    (add-text-properties
     start  end
     (cond (sequencep  (append (bookmarkp-face-prop 'bookmarkp-sequence)
                               '(mouse-face highlight follow-link t
                                 help-echo "mouse-2: Invoke the bookmarks in this sequence")))
           (functionp  (append (bookmarkp-face-prop 'bookmarkp-function)
                               '(mouse-face highlight follow-link t
                                 help-echo "mouse-2: Invoke this function bookmark")))
           (blist-p    (append (bookmarkp-face-prop 'bookmarkp-bookmark-list)
                               '(mouse-face highlight follow-link t
                                 help-echo "mouse-2: Invoke this bookmark-list bookmark")))
           (desktop-p  (append (bookmarkp-face-prop 'bookmarkp-desktop)
                               '(mouse-face highlight follow-link t
                                 help-echo "mouse-2: Jump to this desktop bookmark")))
           (info-p     (append (bookmarkp-face-prop 'bookmarkp-info)
                               '(mouse-face highlight follow-link t
                                 help-echo "mouse-2: Jump to this Info bookmark")))
           (man-p      (append (bookmarkp-face-prop 'bookmarkp-man)
                               '(mouse-face highlight follow-link t
                                 help-echo (format "mouse-2 Goto `man' page"))))
           (gnus-p     (append (bookmarkp-face-prop 'bookmarkp-gnus)
                               '(mouse-face highlight follow-link t
                                 help-echo "mouse-2: Jump to this Gnus bookmark")))
           (w3m-p      (append (bookmarkp-face-prop 'bookmarkp-w3m)
                               `(mouse-face highlight follow-link t
                                 help-echo (format "mouse-2: Jump to URL `%s'" ,filep))))
           ((and su-p (not (bookmarkp-root-or-sudo-logged-p))) ; Root/sudo not logged
            (append (bookmarkp-face-prop 'bookmarkp-su-or-sudo)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) file `%s'" ,filep))))
           ;; Make sure we test for remoteness before any other tests of the file itself
           ;; (e.g. `file-exists-p'). We don't want to prompt for a password etc.
           ((and remotep (not su-p))    ; Remote file (ssh, ftp)
            (append (bookmarkp-face-prop 'bookmarkp-remote-file)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) remote file `%s'" ,filep))))
           ((and filep (file-directory-p filep)) ; Local directory
            (append (bookmarkp-face-prop 'bookmarkp-local-directory)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Dired directory `%s'" ,filep))))
           ((and filep (file-exists-p filep) regionp) ; Local file with region
            (append (bookmarkp-face-prop 'bookmarkp-local-file-with-region)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Activate region in file `%s'" ,filep))))
           ((and filep (file-exists-p filep)) ; Local file without region
            (append (bookmarkp-face-prop 'bookmarkp-local-file-without-region)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to (visit) file `%s'" ,filep))))
           ((and buffp (get-buffer buffp) (equal filep bookmarkp-non-file-filename)) ; Buffer
            (append (bookmarkp-face-prop 'bookmarkp-buffer)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to buffer `%s'" ,buffp))))
           ((and buffp  (or (not filep) (equal filep bookmarkp-non-file-filename)
                            (not (file-exists-p filep)))) ; Buffer bookmark, but no buffer.
            (append (bookmarkp-face-prop 'bookmarkp-non-file)
                    `(mouse-face highlight follow-link t
                      help-echo (format "mouse-2: Jump to buffer `%s'" ,buffp))))
           (t (append (bookmarkp-face-prop 'bookmarkp-bad-bookmark)
                      `(mouse-face highlight follow-link t
                        help-echo (format "BAD BOOKMARK (maybe): `%s'" ,filep))))))))

;;;###autoload
(defun bookmarkp-bmenu-quit ()          ; `q' in bookmark list
  "Quit the bookmark list (aka \"menu list\").
If `bookmarkp-bmenu-state-file' is non-nil, then save the state, to be
restored the next time the bookmark list is shown.  Otherwise, reset
the internal lists that record menu-list markings."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (if (not bookmarkp-bmenu-state-file)
      (setq bookmarkp-bmenu-marked-bookmarks            ()
            bookmarkp-bmenu-before-hide-marked-alist    ()
            bookmarkp-bmenu-before-hide-unmarked-alist  ())
    (bookmarkp-save-menu-list-state)
    (setq bookmarkp-bmenu-first-time-p  t))
  (quit-window))

(defun bookmarkp-save-menu-list-state ()
  "Save menu-list state, unless not saving or list has not yet been shown."
  (when (and (not bookmarkp-bmenu-first-time-p) bookmarkp-bmenu-state-file)
    (let ((config-list
           `((last-sort-comparer                    . ,bookmarkp-sort-comparer)
             (last-reverse-sort-p                   . ,bookmarkp-reverse-sort-p)
             (last-reverse-multi-sort-p             . ,bookmarkp-reverse-multi-sort-p)
             (last-latest-bookmark-alist            . ,bookmarkp-latest-bookmark-alist)
             (last-omitted-list                     . ,bookmarkp-bmenu-omitted-list)
             (last-bmenu-marked-bookmarks           . ,bookmarkp-bmenu-marked-bookmarks)
             (last-bmenu-filter-function            . ,bookmarkp-bmenu-filter-function)
             (last-bmenu-title                      . ,bookmarkp-bmenu-title)
             (last-bmenu-bookmark                   . ,(and (get-buffer "*Bookmark List*")
                                                            (with-current-buffer
                                                                (get-buffer "*Bookmark List*")
                                                              (bookmark-bmenu-bookmark))))
             (last-bmenu-toggle-filenames           . ,bookmark-bmenu-toggle-filenames)
             (last-bmenu-before-hide-marked-alist   . ,bookmarkp-bmenu-before-hide-marked-alist)
             (last-bmenu-before-hide-unmarked-alist . ,bookmarkp-bmenu-before-hide-unmarked-alist)
             (last-bookmark-file                    . ,(convert-standard-filename
                                                        (expand-file-name
                                                         bookmarkp-current-bookmark-file))))))
      (with-current-buffer (get-buffer-create " *Menu-List State*")
        (goto-char (point-min))
        (delete-region (point-min) (point-max))
        (let ((print-length  nil)
              (print-level   nil))
          (pp config-list (current-buffer))
          (condition-case nil
              (write-region (point-min) (point-max) bookmarkp-bmenu-state-file)
            (file-error (message "Cannot write `%s'" bookmarkp-bmenu-state-file)))
          (kill-buffer (current-buffer)))))))

(defun bookmarkp-bmenu-goto-bookmark-named (name)
  "Go to the first bookmark whose name matches NAME."
  (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
  (while (and (not (eobp)) (not (equal name (bookmark-bmenu-bookmark))))  (forward-line 1))
  (bookmark-bmenu-ensure-position))     ; Just in case we fall off the end.

(defun bookmarkp-barf-if-not-in-menu-list ()
  "Raise an error if current buffer is not `*Bookmark List*'."
  (unless (equal (buffer-name (current-buffer)) "*Bookmark List*")
    (error "Use this command only in buffer `*Bookmark List*'")))


;;(@* "Bookmark Predicates")
;;  *** Bookmark Predicates ***

(defun bookmarkp-bookmark-list-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a bookmark-list bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bookmarkp-jump-bookmark-list))

(defun bookmarkp-desktop-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a desktop bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bookmarkp-jump-desktop))

;; Note: To avoid remote access, if bookmark does not have the Dired handler, then we insist
;; that it be for a local directory.  IOW, we do not include remote directories that were not
;; bookmarked by Bookmark+ (and so do not have the Dired handler).
(defun bookmarkp-dired-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Dired bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (or (eq (bookmark-get-handler bookmark) 'bookmarkp-jump-dired)
      (bookmarkp-local-directory-bookmark-p bookmark)))

(defun bookmarkp-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a file or directory.
BOOKMARK is a bookmark name or a bookmark record.
This excludes bookmarks of a more specific kind (Info, Gnus, and W3M)."
  (let* ((filename   (bookmark-get-filename bookmark))
         (nonfile-p  (equal filename bookmarkp-non-file-filename))
         (handler    (bookmark-get-handler bookmark)))
    (and filename (not nonfile-p) (or (not handler) (eq handler 'bookmarkp-jump-dired))
         (not (and (bookmark-prop-get bookmark 'info-node)))))) ; Emacs 20-21 Info: no handler.

(defun bookmarkp-function-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a function bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bookmarkp-jump-function))

(defun bookmarkp-gnus-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Gnus bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (memq (bookmark-get-handler bookmark) '(bookmarkp-jump-gnus bmkext-jump-gnus)))

(defun bookmarkp-info-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an Info bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (or (eq (bookmark-get-handler bookmark) 'Info-bookmark-jump)
      (string= "*info*" (bookmarkp-get-buffer-name bookmark))
      ;; Emacs 20-21 form - no handler (and no `buffer-name' entry).
      (bookmark-prop-get bookmark 'info-node)))

(defun bookmarkp-local-directory-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local directory.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((file  (bookmark-get-filename bookmark)))
    (and (bookmarkp-local-file-bookmark-p bookmark) (file-directory-p file))))

(defun bookmarkp-local-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local file or directory.
BOOKMARK is a bookmark name or a bookmark record.
This excludes bookmarks of a more specific kind (Info, Gnus, and W3M)."
  (and (bookmarkp-file-bookmark-p bookmark) (not (bookmarkp-remote-file-bookmark-p bookmark))))

(defun bookmarkp-man-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a `man' page bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (memq (bookmark-get-handler bookmark) '(bookmarkp-jump-man bookmarkp-jump-woman
                                          bmkext-jump-man bmkext-jump-woman)))

(defun bookmarkp-marked-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a marked bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (unless (stringp bookmark) (setq bookmark  (car bookmark)))
  (member bookmark bookmarkp-bmenu-marked-bookmarks))

(defun bookmarkp-non-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a non-file bookmark (e.g *scratch*).
This excludes bookmarks of a more specific kind (Info, Gnus, and W3M).
It includes bookmarks to existing buffers, as well as bookmarks
defined for buffers that do not currently exist."
  (let* ((filename   (bookmark-get-filename bookmark))
         (nonfile-p  (equal filename bookmarkp-non-file-filename))) 
    (and (bookmarkp-get-buffer-name bookmark)
         (or (not filename) nonfile-p
             ;; Ensure not remote before calling `file-exists-p'.  (Do not prompt for password.)
             (and (not (bookmarkp-file-remote-p filename)) (not (file-exists-p filename))))
         (not (bookmark-get-handler bookmark)))))

(defun bookmarkp-region-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK has region information.
BOOKMARK is a bookmark name or a bookmark record."
  (and (bookmarkp-get-end-position bookmark)
       (/= (bookmark-get-position bookmark) (bookmarkp-get-end-position bookmark))))

(defun bookmarkp-remote-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a remote file or directory.
BOOKMARK is a bookmark name or a bookmark record.
This includes remote Dired bookmarks, but otherwise excludes bookmarks
with handlers (Info, Gnus, and W3M)."
  (let* ((handler   (bookmark-get-handler bookmark))
         (file      (bookmark-get-filename bookmark))
         (rem-file  (and file  (bookmarkp-file-remote-p file))))
    (and rem-file  (or (not handler) (eq handler 'bookmarkp-jump-dired)))))

(defun bookmarkp-sequence-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a sequence bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bookmarkp-jump-sequence))

(defun bookmarkp-w3m-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a W3M bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (memq (bookmark-get-handler bookmark) '(bookmarkp-jump-w3m bmkext-jump-w3m)))


;;(@* "Filter Functions")
;;  *** Filter Functions ***

(defun bookmarkp-bookmark-list-alist-only ()
  "`bookmark-alist', filtered to retain only bookmark-list bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-bookmark-list-bookmark-p bookmark-alist))

(defun bookmarkp-desktop-alist-only ()
  "`bookmark-alist', filtered to retain only desktop bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-desktop-bookmark-p bookmark-alist))

(defun bookmarkp-dired-alist-only ()
  "`bookmark-alist', filtered to retain only Dired bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-dired-bookmark-p bookmark-alist))

(defun bookmarkp-file-alist-only ()
  "`bookmark-alist', filtered to retain only file and directory bookmarks.
This excludes bookmarks that might contain file information but are
particular in some way - for example, Info bookmarks or Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-file-bookmark-p bookmark-alist))

(defun bookmarkp-gnus-alist-only ()
  "`bookmark-alist', filtered to retain only Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-gnus-bookmark-p bookmark-alist))

(defun bookmarkp-info-alist-only ()
  "`bookmark-alist', filtered to retain only Info bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-info-bookmark-p bookmark-alist))

(defun bookmarkp-man-alist-only ()
  "`bookmark-alist', filtered to retain only `man' page bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-man-bookmark-p bookmark-alist))

(defun bookmarkp-local-file-alist-only ()
  "`bookmark-alist', filtered to retain only local-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-local-file-bookmark-p bookmark-alist))

(defun bookmarkp-non-file-alist-only ()
  "`bookmark-alist', filtered to retain only non-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-non-file-bookmark-p bookmark-alist))

(defun bookmarkp-regexp-filtered-bookmark-name-alist-only ()
  "`bookmark-alist' for bookmarks matching `bookmarkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not
   #'(lambda (bmk) (string-match bookmarkp-bmenu-filter-pattern (car bmk))) bookmark-alist))

(defun bookmarkp-regexp-filtered-file-name-alist-only ()
  "`bookmark-alist' for files matching `bookmarkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (let (fname)
    (bookmarkp-remove-if-not #'(lambda (bmk)
                                 (and (setq fname  (bookmark-get-filename bmk))
                                      (string-match bookmarkp-bmenu-filter-pattern fname)))
                             bookmark-alist)))

(defun bookmarkp-regexp-filtered-tags-alist-only ()
  "`bookmark-alist' for tags matching `bookmarkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (let (tags)
    (bookmarkp-remove-if-not
     #'(lambda (bmk) (and (setq tags  (bookmarkp-get-tags bmk))
                          (bookmarkp-some (lambda (tag)
                                            (string-match bookmarkp-bmenu-filter-pattern
                                                          (bookmarkp-tag-name tag)))
                                          tags)))
     bookmark-alist)))

(defun bookmarkp-region-alist-only ()
  "`bookmark-alist', filtered to retain only bookmarks that have regions.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-region-bookmark-p bookmark-alist))

(defun bookmarkp-remote-file-alist-only ()
  "`bookmark-alist', filtered to retain only remote-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-remote-file-bookmark-p bookmark-alist))

(defun bookmarkp-w3m-alist-only ()
  "`bookmark-alist', filtered to retain only W3M bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bookmarkp-remove-if-not #'bookmarkp-w3m-bookmark-p bookmark-alist))


;;; Marked bookmarks

(defun bookmarkp-marked-bookmarks-only ()
  "Return the list of marked bookmarks."
  (bookmarkp-remove-if-not #'bookmarkp-marked-bookmark-p bookmark-alist))

(defun bookmarkp-unmarked-bookmarks-only ()
  "Return the list of unmarked bookmarks."
  (bookmarkp-remove-if #'bookmarkp-marked-bookmark-p bookmark-alist))

(defun bookmarkp-some-marked-p (alist)
  "Return non-nil if ALIST is nonempty and includes a marked bookmark."
  (catch 'break
    (dolist (i  alist)  (and (bookmarkp-marked-bookmark-p i)  (throw 'break t)))))

(defun bookmarkp-some-unmarked-p (alist)
  "Return non-nil if ALIST is nonempty and includes an unmarked bookmark."
  (catch 'break
    (dolist (i  alist)  (and (not (bookmarkp-marked-bookmark-p i))  (throw 'break t)))))


;;(@* "General Utility Functions")
;;  *** General Utility Functions ***

(defun bookmarkp-remove-dups (list)
  "Copy of LIST with duplicate elements removed.  Tested with `equal'."
  (let ((tail  list)
        new)
    (while tail
      (unless (member (car tail) new) (push (car tail) new))
      (pop tail))
    (nreverse new)))
  
(defun bookmarkp-remove-assoc-dups (alist &optional omit)
  "Shallow copy of ALIST without elements that have duplicate keys.
Only the first element of those with the same key is kept.
Keys are compared using `equal'.
If optional arg OMIT is non-nil, then omit from the return value any
elements with keys in list OMIT."
  (let ((new   ()))
    (dolist (ii  alist)
      (unless (or (assoc (car ii) new) (member (car ii) omit))  (push ii new)))
    (nreverse new)))

(defun bookmarkp-remove-if (pred xs)
  "A copy of list XS with no elements that satisfy predicate PRED."
  (let ((result  ()))
    (dolist (x  xs) (unless (funcall pred x) (push x result)))
    (nreverse result)))

(defun bookmarkp-remove-if-not (pred xs)
  "A copy of list XS with only elements that satisfy predicate PRED."
  (let ((result  ()))
    (dolist (x  xs) (when (funcall pred x) (push x result)))
    (nreverse result)))

(defun bookmarkp-assoc-delete-all (key alist)
  "Delete from ALIST all elements whose car is `equal' to KEY.
Return the modified alist.
Elements of ALIST that are not conses are ignored."
  (while (and (consp (car alist)) (equal (car (car alist)) key))  (setq alist  (cdr alist)))
  (let ((tail  alist)
        tail-cdr)
    (while (setq tail-cdr  (cdr tail))
      (if (and (consp (car tail-cdr))  (equal (car (car tail-cdr)) key))
          (setcdr tail (cdr tail-cdr))
        (setq tail  tail-cdr))))
  alist)

;; Similar to `every' in `cl-extra.el', without non-list sequences and multiple sequences.
(defun bookmarkp-every (predicate list)
  "Return t if PREDICATE is true for all elements of LIST; else nil."
  (let ((res  nil))
    (while (and list (funcall predicate (car list))) (setq list  (cdr list)))
    (null list)))

;; Similar to `some' in `cl-extra.el', without non-list sequences and multiple sequences.
(defun bookmarkp-some (predicate list)
  "Return non-nil if PREDICATE is true for some element of LIST; else nil.
Return the first non-nil value returned by PREDICATE."
  (let ((res  nil))
    (while (and list (not (setq res  (funcall predicate (pop list))))))
    res))

;; From `cl-seq.el', function `union', without keyword treatment.
;; (Same as `simple-set-union' in `misc-fns.el' and `icicle-set-union' in `icicles-fn.el'.)
(defun bookmarkp-set-union (list1 list2)
  "Combine LIST1 and LIST2 using a set-union operation.
The result list contains all items that appear in either LIST1 or
LIST2.  Comparison is done using `equal'.  This is a non-destructive
function; it copies the data if necessary."
  (cond ((null list1)         list2)
        ((null list2)         list1)
        ((equal list1 list2)  list1)
        (t
         (unless (>= (length list1) (length list2))
           (setq list1  (prog1 list2 (setq list2  list1)))) ; Swap them.
         (while list2
           (unless (member (car list2) list1)  (setq list1  (cons (car list2) list1)))
           (setq list2  (cdr list2)))
         list1)))

(defun bookmarkp-upcase (string)
  "`upcase', but in case of error, return original STRING.
This works around an Emacs 20 problem that occurs if STRING contains
binary data (weird chars)."
  (condition-case nil (upcase string) (error string)))

(defun bookmarkp-same-file-p (file1 file2)
  "Return non-nil if FILE1 and FILE2 name the same file.
If either name is not absolute, then it is considered relative to
`default-directory'."
  (string= (file-truename (expand-file-name file1)) (file-truename (expand-file-name file2))))

(defun bookmarkp-file-remote-p (file-name)
  "Returns non-nil if string FILE-NAME is likely to name a remote file."
  (if (fboundp 'file-remote-p)
      (file-remote-p file-name)
    (and (fboundp 'ffap-file-remote-p) (ffap-file-remote-p file-name))))

(defun bookmarkp-replace-regexp-in-string (regexp rep string
                                           &optional fixedcase literal subexp start)
  "Replace all matches for REGEXP with REP in STRING and return STRING."
  (if (fboundp 'replace-regexp-in-string) ; Emacs > 20.
      (replace-regexp-in-string regexp rep string fixedcase literal subexp start)
    (if (string-match regexp string)    ; Emacs 20
        (replace-match rep nil nil string)
      string)))

(defun bookmarkp-float-time (&optional specified-time)
  "Same as `float-time'.  (Needed for Emacs 20.)"
  (if (fboundp 'float-time)
      (float-time specified-time)
    (unless specified-time (setq specified-time  (current-time)))
    (+ (* (float (nth 0 specified-time)) (expt 2 16))  (nth 1 specified-time))))

(defun bookmarkp-face-prop (value)
  "Return a list with elements `face' or `font-lock-face' and VALUE.
Starting with Emacs 22, the first element is `font-lock-face'."
  (list (if (> emacs-major-version 21) 'font-lock-face 'face) value))  

(defun bookmarkp-make-plain-predicate (pred &optional final-pred)
  "Return a plain predicate that corresponds to component-predicate PRED.
PRED and FINAL-PRED correspond to their namesakes in
`bookmarkp-sort-comparer' (which see).

PRED should return `(t)', `(nil)', or nil.

Optional arg FINAL-PRED is the final predicate to use if PRED cannot
decide (returns nil).  If FINAL-PRED is nil, then `bookmarkp-alpha-p',
the plain-predicate equivalent of `bookmarkp-alpha-cp' is used as the
final predicate."
  `(lambda (b1 b2)
    (let ((res  (funcall ',pred b1 b2)))
      (if res (car res) (funcall ',(or final-pred 'bookmarkp-alpha-p) b1 b2)))))

;;; If you need this for some reason, uncomment it.
;;; (defun bookmarkp-fix-bookmark-alist-and-save ()
;;;   "Update format of `bookmark-default-file' created in summer of 2009.
;;; You DO NOT NEED THIS, unless you happen to have used `bookmark+.el' in
;;; the summer of 2009 to create non-file bookmarks.  If you did that,
;;; then some of those bookmarks might cause vanilla Emacs (emacs -Q) to
;;; raise an error.  You can use this command to fix that problem: it
;;; modifies your existing `bookmark-default-file' (`.emacs.bmk'), after
;;; backing up that file (suffixing the name with \"_saveNUMBER\")."
;;;   (interactive)
;;;   (require 'cl)                         ; For `gensym'
;;;   (if (not (yes-or-no-p
;;;              "This will modify your bookmark file, after backing it up.  OK? "))
;;;       (message "OK, nothing done")
;;;     (bookmark-maybe-load-default-file)
;;;     (let ((bkup-file  (concat bookmark-default-file "_" (symbol-name (gensym "save")))))
;;;       (when (condition-case err
;;;                 (progn
;;;                   (with-current-buffer (find-file-noselect bookmark-default-file)
;;;                     (write-file bkup-file))
;;;                   (dolist (bmk  bookmark-alist)
;;;                     (let ((fn-tail  (member '(filename) bmk))
;;;                           (hdlr     (bookmark-get-handler (car bmk))))
;;;                       (cond (fn-tail
;;;                              (setcar fn-tail (cons 'filename bookmarkp-non-file-filename)))
;;;                             ((and (eq hdlr 'bookmarkp-jump-gnus)
;;;                                   (not (assoc 'filename bmk)))
;;;                              (setcdr bmk (cons (cons 'filename bookmarkp-non-file-filename)
;;;                                                (cdr bmk)))))))
;;;                   t)                    ; Be sure `dolist' exit with t to allow saving.
;;;               (error (error "No changes made. %s" (error-message-string err))))
;;;         (bookmark-save)
;;;         (message "Bookmarks file fixed.  Old version is `%s'" bkup-file)))))


;;(@* "Bookmark Entry Access Functions")
;;  *** Bookmark Entry Access Functions ***

(defun bookmarkp-get-buffer-name (bookmark)
  "Return the `buffer-name' value for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'buffer-name))

(defun bookmarkp-get-end-position (bookmark)
  "Return the `end-position' value for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'end-position))

(defun bookmarkp-get-visits-count (bookmark)
  "Return the `visits' count for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'visits))

(defun bookmarkp-get-visit-time (bookmark)
  "Return the `time' value for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  ;; Should just be a prop-get, but when first implemented, we used a float
  ;; instead of a time cons, so we need to convert any such obsolete recorded times.
  (let ((vt  (bookmark-prop-get bookmark 'time)))
    (when (numberp vt)                  ; Convert mid-2009 time values (floats) to cons form.
      (setq vt  (if (boundp 'seconds-to-time)
                    (seconds-to-time vt)
                  (list (floor vt 65536) ; Inlined `seconds-to-time', for Emacs 20-21.
                        (floor (mod vt 65536))
                        (floor (* (- vt (ffloor vt)) 1000000))))))
    vt))


;;(@* "Sorting - General Functions")
;;  *** Sorting - General Functions ***

(defun bookmarkp-sort-and-remove-dups (alist &optional omit)
  "Remove duplicates from a copy of ALIST, then sort it and return it.
Do not sort if `bookmarkp-sort-comparer' is nil.
Always remove duplicates.  Keep only the first element with a given
key.  This is a non-destructive operation: ALIST is not modified.

Sorting is done using using `bookmarkp-sort-comparer'.
If `bookmarkp-reverse-sort-p' is non-nil, then reverse the sort order.
Keys are compared for sorting using `equal'.
If optional arg OMIT is non-nil, then omit from the return value any
elements with keys in list OMIT."
  (let ((new-alist  (bookmarkp-remove-assoc-dups alist omit))
        (sort-fn  (and bookmarkp-sort-comparer
                       (if (and (not (functionp bookmarkp-sort-comparer))
                                (consp bookmarkp-sort-comparer))
                           'bookmarkp-multi-sort
                         bookmarkp-sort-comparer))))
    (when sort-fn
      (setq new-alist  (sort new-alist (if bookmarkp-reverse-sort-p
                                           (lambda (a b) (not (funcall sort-fn a b)))
                                         sort-fn))))
    new-alist))

;;; KEEP this simpler version also.  This uses `run-hook-with-args-until-success', but it
;;; does not respect `bookmarkp-reverse-multi-sort-p'.
;;; (defun bookmarkp-multi-sort (b1 b2)
;;;   "Try predicates in `bookmarkp-sort-comparer', in order, until one decides.
;;; See the description of `bookmarkp-sort-comparer'."
;;;   (let* ((preds   (append (car bookmarkp-sort-comparer) (cdr bookmarkp-sort-comparer)))
;;;          (result  (run-hook-with-args-until-success 'preds b1 b2)))
;;;     (if (consp result)
;;;         (car result)
;;;       result)))

;; This Lisp definition respects `bookmarkp-reverse-multi-sort-p', and can be extended.
(defun bookmarkp-multi-sort (b1 b2)
  "Try predicates in `bookmarkp-sort-comparer', in order, until one decides.
See the description of `bookmarkp-sort-comparer'.
If `bookmarkp-reverse-multi-sort-p' is non-nil, then reverse the order
for using multi-sorting predicates."
  (let ((preds       (car bookmarkp-sort-comparer))
        (final-pred  (cadr bookmarkp-sort-comparer))
        (result      nil))
    (when bookmarkp-reverse-multi-sort-p (setq preds  (reverse preds)))
    (catch 'bookmarkp-multi-sort
      (dolist (pred  preds)
        (setq result  (funcall pred b1 b2))
        (when (consp result)
          (when bookmarkp-reverse-multi-sort-p (setq result  (list (not (car result)))))
          (throw 'bookmarkp-multi-sort (car result))))
      (and final-pred  (if bookmarkp-reverse-multi-sort-p
                           (not (funcall final-pred b1 b2))
                         (funcall final-pred b1 b2))))))

;; The message is only approximate.  The effect of `bookmarkp-reverse-multi-sort-p' is not
;; always intuitive, but it can often be useful.  What's not always intuitive is the placement
;; (the order) of bookmarks that are not sorted by the PREDs.
;; 
(defun bookmarkp-msg-about-sort-order (order &optional prefix-msg suffix-msg)
  "Display a message mentioning the current sort ORDER and direction.
Optional arg PREFIX-MSG is prepended to the constructed message, and
terminated with a period.
Similarly, SUFFIX-MSG is appended, after appending \".  \"."
  (let ((msg  (if (not bookmarkp-sort-comparer)
                  "Bookmarks NOT sorted"
                (format
                 "%s%s" (concat "Sorted " order)
                 (if (not (and (consp bookmarkp-sort-comparer) ; Ordinary single predicate.
                               (consp (car bookmarkp-sort-comparer))))
                     (if bookmarkp-reverse-sort-p "; REVERSED" "")
                   (if (not (cadr (car bookmarkp-sort-comparer)))
                       ;; Single PRED.
                       (if (or (and bookmarkp-reverse-sort-p (not bookmarkp-reverse-multi-sort-p))
                               (and bookmarkp-reverse-multi-sort-p (not bookmarkp-reverse-sort-p)))
                           "; REVERSED"
                         "")

                     ;; In case we want to distinguish:
                     ;; (if (and bookmarkp-reverse-sort-p (not bookmarkp-reverse-multi-sort-p))
                     ;;     "; reversed"
                     ;;   (if (and bookmarkp-reverse-multi-sort-p (not bookmarkp-reverse-sort-p))
                     ;;       "; reversed +"
                     ;;     ""))

                     ;; At least two PREDs.
                     (cond ((and bookmarkp-reverse-sort-p (not bookmarkp-reverse-multi-sort-p))
                            "; REVERSED")
                           ((and bookmarkp-reverse-multi-sort-p (not bookmarkp-reverse-sort-p))
                            "; each predicate group reversed")
                           ((and bookmarkp-reverse-multi-sort-p bookmarkp-reverse-sort-p)
                            "; order of predicate groups reversed")
                           (t ""))))))))
    (when prefix-msg (setq msg  (concat prefix-msg ".  " msg)))
    (when suffix-msg (setq msg  (concat msg ".  " suffix-msg)))
    (message msg)))


;;(@* "Sorting - Commands")
;;  *** Sorting - Commands ***

(defun bookmarkp-repeat-command (command)
  "Repeat COMMAND."
 (let ((repeat-previous-repeated-command  command)
       (repeat-message-function           'ignore)
       (last-repeatable-command           'repeat))
   (repeat nil)))

(defun bookmarkp-bmenu-change-sort-order-repeat (arg) ; `s s'... in bookmark list
  "Cycle to the next sort order.
With a prefix arg, reverse current sort order.
This is a repeatable version of `bookmarkp-bmenu-change-sort-order'."
  (interactive "P")
  (require 'repeat)
  (bookmarkp-repeat-command 'bookmarkp-bmenu-change-sort-order))

(defun bookmarkp-bmenu-change-sort-order (&optional arg)
  "Cycle to the next sort order.
With a prefix arg, reverse the current sort order."
  (interactive "P")
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-sort-orders-for-cycling-alist  (delq nil bookmarkp-sort-orders-for-cycling-alist))
  (if arg
      (bookmarkp-reverse-sort-order)
    (let ((current-bmk  (bookmark-bmenu-bookmark))
          next-order)
      (let ((orders  (mapcar #'car bookmarkp-sort-orders-for-cycling-alist)))
        (setq next-order  (or (cadr (member (bookmarkp-current-sort-order) orders))  (car orders))
              bookmarkp-sort-comparer  (cdr (assoc next-order
                                                   bookmarkp-sort-orders-for-cycling-alist))))
      (message "Sorting...")
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (bookmarkp-bmenu-goto-bookmark-named current-bmk) ; Put cursor back on the right line.
      (when (interactive-p) (bookmarkp-msg-about-sort-order next-order)))))

(defun bookmarkp-current-sort-order ()
  "Current sort order or sort function, as a string suitable in a message."
  (or (car (rassoc bookmarkp-sort-comparer bookmarkp-sort-orders-alist))
      (format "%s" bookmarkp-sort-comparer)))

(defun bookmarkp-reverse-sort-order ()  ; `s r' in bookmark list
  "Reverse the current bookmark sort order.
If you combine this with \\<bookmark-bmenu-mode-map>\
`\\[bookmarkp-reverse-multi-sort-order]', then see the doc for that command."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-reverse-sort-p  (not bookmarkp-reverse-sort-p))
  (let ((current-bmk  (bookmark-bmenu-bookmark)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (bookmarkp-bmenu-goto-bookmark-named current-bmk)) ; Put cursor back on the right line.
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order))))

(defun bookmarkp-reverse-multi-sort-order () ; `s C-r' in bookmark list
  "Reverse the application of multi-sorting predicates.
These are the PRED predicates described for option
`bookmarkp-sort-comparer'.

This reverses the order in which the predicates are tried, and it
also complements the truth value returned by each predicate.

For example, if the list of multi-sorting predicates is (p1 p2 p3),
then the predicates are tried in the order: p3, p2, p1.  And if a
predicate returns true, `(t)', then the effect is as if it returned
false, `(nil)', and vice versa.

The use of multi-sorting predicates tends to group bookmarks, with the
first predicate corresponding to the first bookmark group etc.

The effect of \\<bookmark-bmenu-mode-map>`\\[bookmarkp-reverse-multi-sort-order]' is \
roughly as follows:

 - without also `\\[bookmarkp-reverse-sort-order]', it reverses the bookmark order in each \
group

 - combined with `\\[bookmarkp-reverse-sort-order]', it reverses the order of the bookmark
   groups, but not the bookmarks within a group

This is a rough description.  The actual behavior can be complex,
because of how each predicate is defined.  If this description helps
you, fine.  If not, just experiment and see what happens. \;-)

Remember that ordinary `\\[bookmarkp-reverse-sort-order]' reversal on its own is \
straightforward.
If you find `\\[bookmarkp-reverse-multi-sort-order]' confusing or not helpful, then do not \
use it."
  (interactive)
  (bookmarkp-barf-if-not-in-menu-list)
  (setq bookmarkp-reverse-multi-sort-p  (not bookmarkp-reverse-multi-sort-p))
  (let ((current-bmk  (bookmark-bmenu-bookmark)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (bookmarkp-bmenu-goto-bookmark-named current-bmk)) ; Put cursor back on the right line.
  (when (interactive-p) (bookmarkp-msg-about-sort-order (bookmarkp-current-sort-order))))


;; The ORDER of the macro calls here defines the REVERSE ORDER of
;; `bookmarkp-sort-orders-alist'.  The first here is thus also the DEFAULT sort order.
;; Entries are traversed by `s s'..., in `bookmarkp-sort-orders-alist' order.

(bookmarkp-define-sort-command          ; `s k' in bookmark list (`k' for "kind")
 "by bookmark type"                     ; `bookmarkp-bmenu-sort-by-bookmark-type'
 ((bookmarkp-info-cp bookmarkp-gnus-cp bookmarkp-w3m-cp bookmarkp-local-file-type-cp
                     bookmarkp-handler-cp)
  bookmarkp-alpha-p)
 "Sort bookmarks by type: Info, Gnus, W3M, files, other.")

(bookmarkp-define-sort-command          ; `s w' in bookmark list
 "by w3m url"                           ; `bookmarkp-bmenu-sort-by-w3m-url'
 ((bookmarkp-w3m-cp) bookmarkp-alpha-p)
 "Sort W3M bookmarks alphabetically by their URL/filename.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bookmarkp-define-sort-command          ; `s g' in bookmark list
 "by Gnus thread"                       ; `bookmarkp-bmenu-sort-by-Gnus-thread'
 ((bookmarkp-gnus-cp) bookmarkp-alpha-p)
 "Sort Gnus bookmarks by group, then by article, then by message.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bookmarkp-define-sort-command          ; `s i' in bookmark list
 "by Info location"                     ; `bookmarkp-bmenu-sort-by-Info-location'
 ((bookmarkp-info-cp) bookmarkp-alpha-p)
 "Sort Info bookmarks by file name, then node name, then position.
When two bookmarks are not comparable this way, compare them by
bookmark name.")

(bookmarkp-define-sort-command          ; `s f u' in bookmark list
 "by last local file update"            ; `bookmarkp-bmenu-sort-by-last-local-file-update'
 ((bookmarkp-local-file-updated-more-recently-cp) bookmarkp-alpha-p)
 "Sort bookmarks by last local file update time.
Sort a local file before a remote file, and a remote file before other
bookmarks.  Otherwise, sort by bookmark name.")

(bookmarkp-define-sort-command          ; `s f t' in bookmark list
 "by last local file access"            ; `bookmarkp-bmenu-sort-by-last-local-file-access'
 ((bookmarkp-local-file-accessed-more-recently-cp) bookmarkp-alpha-p)
 "Sort bookmarks by last local file access time.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bookmarkp-define-sort-command          ; `s f s' in bookmark list
 "by local file size"                   ; `bookmarkp-bmenu-sort-by-local-file-size'
 ((bookmarkp-local-file-size-cp) bookmarkp-alpha-p)
 "Sort bookmarks by local file size.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bookmarkp-define-sort-command          ; `s f n' in bookmark list
 "by file name"                         ; `bookmarkp-bmenu-sort-by-file-name'
 ((bookmarkp-file-alpha-cp) bookmarkp-alpha-p)
 "Sort bookmarks by file name.
When two bookmarks are not comparable by file name, compare them by
bookmark name.")

(bookmarkp-define-sort-command          ; `s f d' in bookmark list (`d' for "directory")
 "by local file type"                   ; `bookmarkp-bmenu-sort-by-local-file-type'
 ((bookmarkp-local-file-type-cp) bookmarkp-alpha-p)
 "Sort bookmarks by local file type: file, symlink, directory.
A local file sorts before a remote file, which sorts before other
bookmarks.  Otherwise, sort by bookmark name.")

(bookmarkp-define-sort-command          ; `s >' in bookmark list
 "marked before unmarked"               ; `bookmarkp-bmenu-sort-marked-before-unmarked'
 ((bookmarkp-marked-cp) bookmarkp-alpha-p)
 "Sort bookmarks by putting marked before unmarked.
Otherwise alphabetize by bookmark name.")

(bookmarkp-define-sort-command          ; `s b' in bookmark list
 "by last buffer or file access"        ; `bookmarkp-bmenu-sort-by-last-buffer-or-file-access'
 ((bookmarkp-buffer-last-access-cp bookmarkp-local-file-accessed-more-recently-cp)
  bookmarkp-alpha-p)
 "Sort bookmarks by last buffer access or last local file access.
Sort a bookmark accessed more recently before one accessed less
recently or not accessed.  Sort a bookmark to an existing buffer
before a local file bookmark.  When two bookmarks are not comparable
by such critera, sort them by bookmark name.  (In particular, sort
remote-file bookmarks by bookmark name.")

(bookmarkp-define-sort-command          ; `s v' in bookmark list
 "by bookmark visit frequency"          ; `bookmarkp-bmenu-sort-by-bookmark-visit-frequency'
 ((bookmarkp-visited-more-cp) bookmarkp-alpha-p)
 "Sort bookmarks by the number of times they were visited as bookmarks.
When two bookmarks are not comparable by visit frequency, compare them
by bookmark name.")

(bookmarkp-define-sort-command          ; `s t' in bookmark list
 "by last bookmark access"              ; `bookmarkp-bmenu-sort-by-last-bookmark-access'
 ((bookmarkp-bookmark-last-access-cp) bookmarkp-alpha-p)
 "Sort bookmarks by the time of their last visit as bookmarks.
When two bookmarks are not comparable by visit time, compare them
by bookmark name.")

(bookmarkp-define-sort-command          ; `s 0' in bookmark list
 "by creation time"            ; `bookmarkp-bmenu-sort-by-creation-time'
 ((bookmarkp-bookmark-creation-cp) bookmarkp-alpha-p)
 "Sort bookmarks by the time of their creation.
When one or both of the bookmarks does not have a `created' entry),
compare them by bookmark name.")

(bookmarkp-define-sort-command          ; `s n' in bookmark list
 "by bookmark name"                     ; `bookmarkp-bmenu-sort-by-bookmark-name'
 bookmarkp-alpha-p
 "Sort bookmarks by bookmark name, respecting `case-fold-search'.")


;; These definitions MUST COME AFTER the calls to macro `bookmarkp-define-sort-command'.
;; Otherwise, they won't pick up a populated `bookmarkp-sort-orders-alist'.
;;;###autoload
(when (> emacs-major-version 20)
  (defcustom bookmarkp-sort-orders-for-cycling-alist (copy-sequence
                                                      bookmarkp-sort-orders-alist)
    "*Alist of sort orders used for cycling via `s s'...
This is a subset of the complete list of available sort orders,
`bookmarkp-sort-orders-alist'.  This lets you cycle among fewer sort
orders, if there are some that you do not use often.

See the doc for `bookmarkp-sort-orders-alist', for the structure of
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

;;;###autoload
(unless (> emacs-major-version 20)      ; Emacs 20: custom type `alist' doesn't exist.
  (defcustom bookmarkp-sort-orders-for-cycling-alist (copy-sequence
                                                      bookmarkp-sort-orders-alist)
    "*Alist of sort orders used for cycling via `s s'...
This is a subset of the complete list of available sort orders,
`bookmarkp-sort-orders-alist'.  This lets you cycle among fewer sort
orders, if there are some that you do not use often.

See the doc for `bookmarkp-sort-orders-alist', for the structure of
this value."
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


;;(@* "Sorting - General Predicates")
;;  *** Sorting - General Predicates ***

(defun bookmarkp-marked-cp (b1 b2)
  "True if bookmark B1 is marked and bookmark B2 is not.
B1 and B2 are bookmarks or bookmark names.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((m1  (bookmarkp-marked-bookmark-p b1))
        (m2  (bookmarkp-marked-bookmark-p b2)))
    (cond ((and m1 m2) nil)
          (m1 '(t))
          (m2 '(nil))
          (t nil))))

(defun bookmarkp-visited-more-cp (b1 b2)
  "True if bookmark B1 was visited more often than B2.
B1 and B2 are bookmarks or bookmark names.
True also if B1 was visited but B2 was not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((v1  (bookmarkp-get-visits-count b1))
        (v2  (bookmarkp-get-visits-count b2)))
    (cond ((and v1 v2)
           (cond ((> v1 v2) '(t))
                 ((> v2 v1) '(nil))
                 (t nil)))
          (v1 '(t))
          (v2 '(nil))
          (t nil))))

(defun bookmarkp-bookmark-creation-cp (b1 b2)
  "True if bookmark B1 was created more recently than B2.
B1 and B2 are bookmarks or bookmark names.
True also if B1 has a `created' entry but B2 has none.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((t1  (bookmark-prop-get b1 'created))
        (t2  (bookmark-prop-get b2 'created)))
    (cond ((and t1 t2)
           (setq t1  (bookmarkp-float-time t1)
                 t2  (bookmarkp-float-time t2))
           (cond ((> t1 t2) '(t))
                 ((> t2 t1) '(nil))
                 (t nil)))
          (t1 '(t))
          (t2 '(nil))
          (t nil))))

(defun bookmarkp-bookmark-last-access-cp (b1 b2)
  "True if bookmark B1 was visited more recently than B2.
B1 and B2 are bookmarks or bookmark names.
True also if B1 was visited but B2 was not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((t1  (bookmarkp-get-visit-time b1))
        (t2  (bookmarkp-get-visit-time b2)))
    (cond ((and t1 t2)
           (setq t1  (bookmarkp-float-time t1)
                 t2  (bookmarkp-float-time t2))
           (cond ((> t1 t2) '(t))
                 ((> t2 t1) '(nil))
                 (t nil)))
          (t1 '(t))
          (t2 '(nil))
          (t nil))))

(defun bookmarkp-buffer-last-access-cp (b1 b2)
  "True if bookmark B1's buffer or file was visited more recently than B2's.
B1 and B2 are bookmarks or bookmark names.
A bookmark to an existing buffer sorts before a file bookmark, even if
the buffer has not been visited during this session.

True also if B1 has a buffer but B2 does not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((buf1  (bookmarkp-get-buffer-name b1))
        (buf2  (bookmarkp-get-buffer-name b2))
        f1 f2 t1 t2)
    (setq buf1  (and buf1 (get-buffer buf1))
          buf2  (and buf2 (get-buffer buf2)))
    (cond ((and buf1 buf2)              ; Both buffers exist.   See whether they were accessed.
           (when buf1 (setq buf1  (member buf1 (buffer-list))
                            buf1  (length buf1)))
           (when buf2 (setq buf2  (member buf2 (buffer-list))
                            buf2  (length buf2)))
           (cond ((and buf1 buf2)       ; Both were accessed.  Priority to most recent access.
                  (cond ((< buf1 buf2) '(t))
                        ((< buf2 buf1) '(nil))
                        (t nil)))
                 (buf1 '(t))            ; Only buf1 was accessed.
                 (buf2 '(nil))          ; Only buf2 was accessed.
                 (t nil)))              ; Neither was accessed.

          (buf1 '(t))                   ; Only buf1 exists.
          (buf2 '(nil))                 ; Only buf2 exists.
          (t nil))))                    ; Neither buffer exists

(defun bookmarkp-handler-cp (b1 b2)
  "True if bookmark B1's handler name sorts alphabetically before B2's.
B1 and B2 are bookmarks or bookmark names.
Two bookmarks with handlers are compared alphabetically, by their
handler-function names, respecting `case-fold-search'.
True also if B1 has a handler but B2 has not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((h1  (bookmark-get-handler b1))
        (h2  (bookmark-get-handler b2)))
    (cond ((and h1 h2 (symbolp h1) (symbolp h2))
           ;; Pretend woman bookmarks are man bookmarks, to keep them together.
           (when (eq h1 'bookmarkp-jump-woman) (setq h1  'bookmarkp-jump-man))
           (when (eq h2 'bookmarkp-jump-woman) (setq h2  'bookmarkp-jump-man))
           (setq h1  (symbol-name h1)
                 h2  (symbol-name h2))
           (when case-fold-search (setq h1  (bookmarkp-upcase h1)
                                        h2  (bookmarkp-upcase h2)))
           (cond ((string-lessp h1 h2) '(t))
                 ((string-lessp h2 h1) '(nil))
                 (t nil)))
          (h1 '(t))
          (h2 '(nil))
          (t nil))))

(defun bookmarkp-info-cp (b1 b2)
  "True if bookmark B1 sorts as an Info bookmark before B2.
B1 and B2 are bookmarks or bookmark names.
Two Info bookmarks are compared first by file name (corresponding to
the manual), then by node name, then by position.
True also if B1 is an Info bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((i1  (bookmarkp-info-bookmark-p b1))
        (i2  (bookmarkp-info-bookmark-p b2)))
    (cond ((and i1 i2)
           (setq i1  (abbreviate-file-name (bookmark-get-filename b1))
                 i2  (abbreviate-file-name (bookmark-get-filename b2)))
           (when case-fold-search (setq i1  (bookmarkp-upcase i1)
                                        i2  (bookmarkp-upcase i2)))
           (cond ((string-lessp i1 i2) '(t)) ; Compare manuals (file names).
                 ((string-lessp i2 i1) '(nil))
                 (t                     ; Compare node names.
                  (setq i1  (bookmark-prop-get b1 'info-node)
                        i2  (bookmark-prop-get b2 'info-node))
                  (cond ((string-lessp i1 i2) '(t))
                        ((string-lessp i2 i1) '(nil))
                        (t
                         (setq i1  (bookmark-get-position b1)
                               i2  (bookmark-get-position b2))
                         (cond ((or (not i1) (not i2)) '(t)) ; Fallback if no `position' entry.
                               ((<= i1 i2) '(t))
                               ((< i2 i1) '(nil))))))))
          (i1 '(t))
          (i2 '(nil))
          (t nil))))

(defun bookmarkp-gnus-cp (b1 b2)
  "True if bookmark B1 sorts as a Gnus bookmark before B2.
B1 and B2 are bookmarks or bookmark names.
Two Gnus bookmarks are compared first by Gnus group name, then by
article number, then by message ID.
True also if B1 is a Gnus bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((g1  (bookmarkp-gnus-bookmark-p b1))
        (g2  (bookmarkp-gnus-bookmark-p b2)))
    (cond ((and g1 g2)
           (setq g1  (bookmark-prop-get b1 'group)
                 g2  (bookmark-prop-get b2 'group))
           (cond ((string-lessp g1 g2) '(t)) ; Compare groups.
                 ((string-lessp g2 g1) '(nil))
                 (t                     ; Compare article numbers.
                  (setq g1  (bookmark-prop-get b1 'article)
                        g2  (bookmark-prop-get b2 'article))
                  (cond ((< g1 g2) '(t))
                        ((< g2 g1) '(nil))
                        (t
                         (setq g1  (bookmark-prop-get b1 'message-id)
                               g2  (bookmark-prop-get b2 'message-id))
                         (cond ((string-lessp g1 g2) '(t)) ; Compare message IDs.
                               ((string-lessp g2 g1) '(nil))
                               (t nil)))))))   
          (g1 '(t))
          (g2 '(nil))
          (t nil))))

(defun bookmarkp-w3m-cp (b1 b2)
  "True if bookmark B1 sorts as a W3M URL bookmark before B2.
B1 and B2 are bookmarks or bookmark names.
Two W3M URL bookmarks are compared alphabetically, by their URLs.
True also if B1 is a W3M bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((w1  (bookmarkp-w3m-bookmark-p b1))
        (w2  (bookmarkp-w3m-bookmark-p b2)))
    (cond ((and w1 w2)
           (setq w1  (bookmark-get-filename b1)
                 w2  (bookmark-get-filename b2))
           (cond ((string-lessp w1 w2) '(t))
                 ((string-lessp w2 w1) '(nil))
                 (t nil)))
          (w1 '(t))
          (w2 '(nil))
          (t nil))))

(defun bookmarkp-alpha-cp (b1 b2)
  "True if bookmark B1's name sorts alphabetically before B2's.
B1 and B2 are bookmarks or bookmark names.
The bookmark names are compared, respecting `case-fold-search'.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((s1  (car b1))
        (s2  (car b2)))
    (when case-fold-search (setq s1  (bookmarkp-upcase s1)
                                 s2  (bookmarkp-upcase s2)))
    (cond ((string-lessp s1 s2) '(t))
          ((string-lessp s2 s1) '(nil))
          (t nil))))

;; Do not use `bookmarkp-make-plain-predicate', because it falls back on `bookmark-alpha-p'.
;; Return nil if `bookmark-alpha-cp' cannot decide.
(defun bookmarkp-alpha-p (b1 b2)
  "True if bookmark B1's name sorts alphabetically before B2's.
B1 and B2 are bookmarks or bookmark names.
The bookmark names are compared, respecting `case-fold-search'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (car (bookmarkp-alpha-cp b1 b2)))


;;(@* "Sorting - File-Name Predicates")
;;  *** Sorting - File-Name Predicates ***

(defun bookmarkp-file-alpha-cp (b1 b2)
  "True if bookmark B1's file name sorts alphabetically before B2's.
B1 and B2 are bookmarks or bookmark names.
The file names are shortened using `abbreviate-file-name', then they
are compared respecting `case-fold-search'.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((f1  (bookmarkp-file-bookmark-p b1))
        (f2  (bookmarkp-file-bookmark-p b2)))
    (cond ((and f1 f2)
           ;; Call `abbreviate-file-name' mainly to get letter case right per platform.
           (setq f1  (abbreviate-file-name (bookmark-get-filename b1))
                 f2  (abbreviate-file-name (bookmark-get-filename b2)))
           (when case-fold-search (setq f1  (bookmarkp-upcase f1)
                                        f2  (bookmarkp-upcase f2)))
           (cond ((string-lessp f1 f2) '(t))
                 ((string-lessp f2 f1) '(nil))
                 (t nil)))
          (f1 '(t))
          (f2 '(nil))
          (t nil))))

;; We define all file-attribute predicates, in case you want to use them.
;;
;; `bookmarkp-file-attribute-0-cp'  - type
;; `bookmarkp-file-attribute-1-cp'  - links
;; `bookmarkp-file-attribute-2-cp'  - uid
;; `bookmarkp-file-attribute-3-cp'  - gid
;; `bookmarkp-file-attribute-4-cp'  - last access time
;; `bookmarkp-file-attribute-5-cp'  - last update time
;; `bookmarkp-file-attribute-6-cp'  - last status change
;; `bookmarkp-file-attribute-7-cp'  - size
;; `bookmarkp-file-attribute-8-cp'  - modes
;; `bookmarkp-file-attribute-9-cp'  - gid change
;; `bookmarkp-file-attribute-10-cp' - inode
;; `bookmarkp-file-attribute-11-cp' - device
;;
(bookmarkp-define-file-sort-predicate 0) ; Type: file, symlink, dir
(bookmarkp-define-file-sort-predicate 1) ; Links
(bookmarkp-define-file-sort-predicate 2) ; Uid
(bookmarkp-define-file-sort-predicate 3) ; Gid
(bookmarkp-define-file-sort-predicate 4) ; Last access time
(bookmarkp-define-file-sort-predicate 5) ; Last modification time
(bookmarkp-define-file-sort-predicate 6) ; Last status-change time
(bookmarkp-define-file-sort-predicate 7) ; Size
(bookmarkp-define-file-sort-predicate 8) ; Modes
(bookmarkp-define-file-sort-predicate 9) ; Gid would change if re-created
(bookmarkp-define-file-sort-predicate 10) ; Inode
(bookmarkp-define-file-sort-predicate 11) ; Device

(defun bookmarkp-local-file-accessed-more-recently-cp (b1 b2)
  "True if bookmark B1's local file was accessed more recently than B2's.
B1 and B2 are bookmarks or bookmark names.
A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their
access times are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bookmarkp-local-file-bookmark-p b1) (bookmarkp-local-file-bookmark-p b2))
         (bookmarkp-cp-not (bookmarkp-file-attribute-4-cp b1 b2)))
        ((bookmarkp-local-file-bookmark-p b1) '(t))
        ((bookmarkp-local-file-bookmark-p b2) '(nil))
        ((and (bookmarkp-remote-file-bookmark-p b1) (bookmarkp-remote-file-bookmark-p b2)) nil)
        ((bookmarkp-remote-file-bookmark-p b1) '(t))
        ((bookmarkp-remote-file-bookmark-p b2) '(nil))
        (t nil)))

(defun bookmarkp-local-file-updated-more-recently-cp (b1 b2)
  "True if bookmark B1's local file was updated more recently than B2's.
B1 and B2 are bookmarks or bookmark names.
A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their
update times are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bookmarkp-local-file-bookmark-p b1) (bookmarkp-local-file-bookmark-p b2))
         (bookmarkp-cp-not (bookmarkp-file-attribute-5-cp b1 b2)))
        ((bookmarkp-local-file-bookmark-p b1) '(t))
        ((bookmarkp-local-file-bookmark-p b2) '(nil))
        ((and (bookmarkp-remote-file-bookmark-p b1) (bookmarkp-remote-file-bookmark-p b2)) nil)
        ((bookmarkp-remote-file-bookmark-p b1) '(t))
        ((bookmarkp-remote-file-bookmark-p b2) '(nil))
        (t nil)))

(defun bookmarkp-local-file-size-cp (b1 b2)
  "True if bookmark B1's local file is larger than B2's.
B1 and B2 are bookmarks or bookmark names.
A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their
sizes are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bookmarkp-local-file-bookmark-p b1) (bookmarkp-local-file-bookmark-p b2))
         (bookmarkp-cp-not (bookmarkp-file-attribute-7-cp b1 b2)))
        ((bookmarkp-local-file-bookmark-p b1) '(t))
        ((bookmarkp-local-file-bookmark-p b2) '(nil))
        ((and (bookmarkp-remote-file-bookmark-p b1) (bookmarkp-remote-file-bookmark-p b2)) nil)
        ((bookmarkp-remote-file-bookmark-p b1) '(t))
        ((bookmarkp-remote-file-bookmark-p b2) '(nil))
        (t nil)))

(defun bookmarkp-local-file-type-cp (b1 b2)
  "True if bookmark B1 sorts by local file type before B2.
B1 and B2 are bookmarks or bookmark names.
For two local files, a file sorts before a symlink, which sorts before
a directory.

A local file sorts before a remote file, which sorts before other
bookmarks.  Two remote files are considered incomparable - their file
types are not examined.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (cond ((and (bookmarkp-local-file-bookmark-p b1) (bookmarkp-local-file-bookmark-p b2))
         (bookmarkp-file-attribute-0-cp b1 b2))
        ((bookmarkp-local-file-bookmark-p b1) '(t))
        ((bookmarkp-local-file-bookmark-p b2) '(nil))
        ((and (bookmarkp-remote-file-bookmark-p b1) (bookmarkp-remote-file-bookmark-p b2)) nil)
        ((bookmarkp-remote-file-bookmark-p b1) '(t))
        ((bookmarkp-remote-file-bookmark-p b2) '(nil))
        (t nil)))

(defun bookmarkp-cp-not (truth)
  "Return the negation of boolean value TRUTH.
If TRUTH is (t), return (nil), and vice versa.
If TRUTH is nil, return nil."
  (and truth (if (car truth) '(nil) '(t))))


;;(@* "Other Bookmark+ Functions (`bookmarkp-*')")
;;  *** Other Bookmark+ Functions (`bookmarkp-*') ***

;;;###autoload
(defun bookmarkp-bmenu-describe-this+move-down (&optional defn) ; `C-down' in bookmark list
  "Describe bookmark of current line, then move down to the next bookmark.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bookmarkp-bmenu-describe-this-bookmark) (forward-line 1))

;;;###autoload
(defun bookmarkp-bmenu-describe-this+move-up (&optional defn) ; `C-up' in bookmark list
  "Describe bookmark of current line, then move down to the next bookmark.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bookmarkp-bmenu-describe-this-bookmark) (forward-line -1))

;;;###autoload
(defun bookmarkp-bmenu-describe-this-bookmark (&optional defn) ; `C-h RET' in bookmark list
  "Describe bookmark of current line.
With a prefix argument, show the internal definition of the bookmark."
  (interactive "P")
  (bookmarkp-barf-if-not-in-menu-list)
  (if defn
      (bookmarkp-describe-bookmark-internals (bookmark-bmenu-bookmark))
    (bookmarkp-describe-bookmark (bookmark-bmenu-bookmark))))

;;;###autoload
(defun bookmarkp-describe-bookmark (bookmark &optional defn)
  "Describe BOOKMARK.
With a prefix argument, show the internal definition of the bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (interactive
   (list (bookmark-completing-read "Describe bookmark" (bookmarkp-default-bookmark-name))
         current-prefix-arg))
  (if defn
      (bookmarkp-describe-bookmark-internals bookmark)
    (setq bookmark     (bookmark-get-bookmark bookmark))
    (let ((bname       (bookmark-name-from-full-record bookmark))
          (buf         (bookmarkp-get-buffer-name bookmark))
          (file        (bookmark-get-filename bookmark))
          (start       (bookmark-get-position bookmark))
          (end         (bookmarkp-get-end-position bookmark))
          (created     (bookmark-prop-get bookmark 'created))
          (time        (bookmarkp-get-visit-time bookmark))
          (visits      (bookmarkp-get-visits-count bookmark))
          (tags        (mapcar #'bookmarkp-tag-name (bookmarkp-get-tags bookmark)))
          (sequence-p  (bookmarkp-sequence-bookmark-p bookmark))
          (function-p  (bookmarkp-function-bookmark-p bookmark))
          (desktop-p   (bookmarkp-desktop-bookmark-p bookmark))
          (dired-p     (bookmarkp-dired-bookmark-p bookmark))
          (gnus-p      (bookmarkp-gnus-bookmark-p bookmark))
          (info-p      (bookmarkp-info-bookmark-p bookmark))
          (man-p       (bookmarkp-man-bookmark-p bookmark))
          (w3m-p       (bookmarkp-w3m-bookmark-p bookmark))
          (annot       (bookmark-get-annotation bookmark))
          no-position-p)
      (when (or sequence-p function-p) (setq no-position-p  t))
      (help-setup-xref (list #'bookmarkp-describe-bookmark bookmark) (interactive-p))
      (let* ((help-text
              (concat
               (format "%s\n%s\n\n" bname (make-string (length bname) ?-))
               (cond (sequence-p  (format "Sequence:\n%s\n"
                                          (pp-to-string
                                           (bookmark-prop-get bookmark 'sequence))))
                     (function-p  (let ((fn  (bookmark-prop-get bookmark 'function)))
                                    (if (symbolp fn)
                                        (format "Function:\t\t%s\n" fn)
                                      (format "Function:\n%s\n"
                                              (pp-to-string
                                               (bookmark-prop-get bookmark 'function))))))
                     (gnus-p      (format "Gnus, group:\t\t%s, article: %s, message-id: %s\n"
                                          (bookmark-prop-get bookmark 'group)
                                          (bookmark-prop-get bookmark 'article)
                                          (bookmark-prop-get bookmark 'message-id)))
                     (man-p       (format "UNIX `man' page for:\t`%s'\n"
                                          (or (bookmark-prop-get bookmark 'man-args)
                                              ;; WoMan has no variable for the cmd name.
                                              (bookmark-prop-get bookmark 'buffer-name))))
                     (info-p      (format "Info node:\t\t(%s) %s\n"
                                          (file-name-nondirectory file)
                                          (bookmark-prop-get bookmark 'info-node)))
                     (w3m-p       (format "W3M URL:\t\t%s\n" file))
                     (desktop-p   (format "Desktop file:\t\t%s\n"
                                          (bookmark-prop-get bookmark 'desktop-file)))
                     (dired-p 
                      (let ((switches  (bookmark-prop-get bookmark 'dired-switches))
                            (marked    (length (bookmark-prop-get bookmark
                                                                  'dired-marked)))
                            (inserted  (length (bookmark-prop-get bookmark
                                                                  'dired-subdirs)))
                            (hidden    (length (bookmark-prop-get bookmark
                                                                  'dired-hidden-dirs))))
                        (format "Dired%s:%s\t\t%s\nMarked:\t\t\t%s\n\
Inserted subdirs:\t%s\nHidden subdirs:\t\t%s\n"
                                (if switches (format " `%s'" switches) "")
                                (if switches "" (format "\t"))
                                (expand-file-name file)
                                marked inserted hidden)))
                     ((equal file bookmarkp-non-file-filename)
                      (format "Buffer:\t\t\t%s\n" (bookmarkp-get-buffer-name bookmark)))
                     (file        (format "File:\t\t\t%s\n" (expand-file-name file)))
                     (t           "Unknown\n"))
               (unless no-position-p
                 (if (bookmarkp-region-bookmark-p bookmark)
                     (format "Region:\t\t\t%d to %d (%d chars)\n" start end (- end start))
                   (format "Position:\t\t%d\n" start)))
               (if visits  (format "Visits:\t\t\t%d\n" visits) "")
               (if time    (format "Last visit:\t\t%s\n" (format-time-string "%c" time)) "")
               (if created (format "Creation:\t\t%s\n" (format-time-string "%c" created)) "")
               (if tags    (format "Tags:\t\t\t%S\n" tags) "")
               (if annot   (format "\nAnnotation:\n%s" annot)))))
        (with-output-to-temp-buffer "*Help*" (princ help-text))
        help-text))))

;;;###autoload
(defun bookmarkp-describe-bookmark-internals (bookmark)
  "Show the internal definition of the bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (interactive
   (list (bookmark-completing-read "Describe bookmark" (bookmarkp-default-bookmark-name))))
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (help-setup-xref (list #'bookmarkp-describe-bookmark-internals bookmark) (interactive-p))
  (let* ((bname      (bookmark-name-from-full-record bookmark))
         (help-text  (format "%s\n%s\n\n%s"
                             bname (make-string (length bname) ?-) (pp-to-string bookmark))))
    (with-output-to-temp-buffer "*Help*" (princ help-text))
    help-text))

;;;###autoload
(defun bookmarkp-list-defuns-in-commands-file ()
  "List the functions defined in `bookmarkp-bmenu-commands-file'.
Typically, these are all commands."
  (interactive)
  (when (and bookmarkp-bmenu-commands-file (file-readable-p bookmarkp-bmenu-commands-file))
    (let ((fns  ())
          (buf  (let ((enable-local-variables  nil))
                  (find-file-noselect bookmarkp-bmenu-commands-file))))
      (help-setup-xref (list #'bookmarkp-list-defuns-in-commands-file) (interactive-p))
      (with-current-buffer buf
        (goto-char (point-min))
        (while (not (eobp))
          (when (re-search-forward "\\s-*(defun \\([^ \t\n(\"]+\\)[ \t\n(]" nil 'move)
            (push (match-string 1) fns)))
        (setq fns  (nreverse fns)
              fns  (sort fns 'string-lessp)))
      (when (buffer-live-p buf) (kill-buffer buf))
      (with-output-to-temp-buffer "*Help*"
        (princ "Bookmark Commands You Defined (in `bookmarkp-bmenu-commands-file')") (terpri)
        (princ "------------------------------------------------------------------") (terpri)
        (terpri)
        (let ((non-dups  (bookmarkp-remove-dups fns)))
          (dolist (fn  non-dups)
            (if (and (fboundp (intern fn)) (fboundp 'help-insert-xref-button))
                (with-current-buffer "*Help*"
                  (goto-char (point-max))
                  (help-insert-xref-button fn 'help-function (intern fn) (commandp (intern fn))))
              (princ fn))
            (let ((dups   (member fn fns)) ; Sorted, so all dups are together.
                  (count  0))
              (while (equal fn (car dups))
                (setq count  (1+ count)
                      dups   (cdr dups)))
              (when (> count 1) (princ (format "  (%d times)" count))))
            (terpri)))
        (help-make-xrefs (current-buffer)))
      fns)))

(defun bookmarkp-root-or-sudo-logged-p ()
  "Return t if the user logged in using Tramp as `root' or `sudo'.
Otherwise, return nil."
  (catch 'break
    (dolist (ii  (mapcar #'buffer-name (buffer-list)))
      (when (string-match "*tramp/\\(su\\|sudo\\) ." ii) (throw 'break t)))))

(defun bookmarkp-position-post-context (breg)
  "Return `bookmark-search-size' chars, starting at position BREG.
Return nil if there are not that many chars.
This is text that follows the bookmark's `position'.
This is used for a non-region bookmark."
  (and (>= (- (point-max) breg) bookmark-search-size)
       (buffer-substring-no-properties breg (+ breg bookmark-search-size))))

(defun bookmarkp-position-post-context-region (breg ereg)
  "Return the region prefix, at BREG.
Return at most `bookmarkp-region-search-size' or (- EREG BREG) chars.
This is text that follows the bookmark's `position'.
This is used for a region bookmark."
  (buffer-substring-no-properties breg (+ breg (min bookmarkp-region-search-size (- ereg breg)))))

(defun bookmarkp-position-pre-context (breg)
  "Return `bookmark-search-size' chars that precede BREG.
Return nil if there are not that many chars.
This is text that precedes the bookmark's `position'.
This is used for a non-region bookmark."
  (and (>= (- breg (point-min)) bookmark-search-size)
       (buffer-substring-no-properties breg (- breg bookmark-search-size))))

(defun bookmarkp-position-pre-context-region (breg)
  "Return the text preceding the region beginning, BREG.
Return at most `bookmarkp-region-search-size' chars.
This is text that precedes the bookmark's `position'.
This is used for a region bookmark."
  (buffer-substring-no-properties (max (- breg bookmarkp-region-search-size) (point-min)) breg))

(defun bookmarkp-end-position-pre-context (breg ereg)
  "Return the region suffix, ending at EREG.
Return at most `bookmarkp-region-search-size' or (- EREG BREG) chars.
This is text that precedes the bookmark's `end-position'."
  (buffer-substring-no-properties (- ereg (min bookmarkp-region-search-size (- ereg breg))) ereg))

(defun bookmarkp-end-position-post-context (ereg)
  "Return the text following the region end, EREG.
Return at most `bookmarkp-region-search-size' chars.
This is text that follows the bookmark's `end-position'."
  (buffer-substring-no-properties
   ereg (+ ereg (min bookmarkp-region-search-size (- (point-max) (point))))))

(defun bookmarkp-position-after-whitespace (position)
  "Move forward from POSITION, skipping over whitespace.  Return point."
  (goto-char position)  (skip-chars-forward " \n\t" (point-max))  (point))

(defun bookmarkp-position-before-whitespace (position)
  "Move backward from POSITION, skipping over whitespace.  Return point."
  (goto-char position)  (skip-chars-backward " \n\t" (point-min))  (point))

(defun bookmarkp-save-new-region-location (bookmark beg end)
  "Update and save `bookmark-alist' for BOOKMARK, relocating its region.
BOOKMARK is a bookmark record.
BEG and END are the new region limits for BOOKMARK.
Do nothing and return nil if `bookmarkp-save-new-location-flag' is nil.
Otherwise, return non-nil if region was relocated."
  (and bookmarkp-save-new-location-flag
       (y-or-n-p "Region relocated.  Do you want to save new region limits? ")
       (progn (bookmark-prop-set bookmark 'front-context-string
                                 (bookmarkp-position-post-context-region beg end))
              (bookmark-prop-set bookmark 'rear-context-string
                                 (bookmarkp-position-pre-context-region beg))
              (bookmark-prop-set bookmark 'front-context-region-string
                                 (bookmarkp-end-position-pre-context beg end))
              (bookmark-prop-set bookmark 'rear-context-region-string
                                 (bookmarkp-end-position-post-context end))
              (bookmark-prop-set bookmark 'position beg)
              (bookmark-prop-set bookmark 'end-position end)
              (bookmarkp-maybe-save-bookmarks)
              t)))

(defun bookmarkp-handle-region-default (bookmark)
  "Default function to handle BOOKMARK's region.
BOOKMARK is a bookmark name or a bookmark record.
Relocate the region if necessary, then activate it.
If region was relocated, save it if user confirms saving."
  ;; Relocate by searching from the beginning (and possibly the end) of the buffer.
  (let* (;; Get bookmark object once and for all.
         ;; Actually, we know BOOKMARK is a bookmark object (not a name), but play safe.
         (bmk              (bookmark-get-bookmark bookmark))
         (bor-str          (bookmark-get-front-context-string bmk))
         (eor-str          (bookmark-prop-get bmk 'front-context-region-string))
         (br-str           (bookmark-get-rear-context-string bmk))
         (ar-str           (bookmark-prop-get bookmark 'rear-context-region-string))
         (pos              (bookmark-get-position bmk))
         (end-pos          (bookmarkp-get-end-position bmk))
         (reg-retrieved-p  t)
         (reg-relocated-p  nil))
    (unless (and (string= bor-str (buffer-substring-no-properties
                                   (point) (+ (point) (length bor-str))))
                 (save-excursion
                   (goto-char end-pos)
                   (string= eor-str (buffer-substring-no-properties
                                     (point) (- (point) (length bor-str))))))
      ;; Relocate region by searching from beginning (and possibly from end) of buffer.
      (let ((beg  nil)
            (end  nil))
        ;;  Go to bob and search forward for END.
        (goto-char (point-min))
        (if (search-forward eor-str (point-max) t) ; Find END, using `eor-str'.
            (setq end  (point))
          ;; Verify that region is not before context.
          (unless (search-forward br-str (point-max) t)
            (when (search-forward ar-str (point-max) t) ; Find END, using `ar-str'.
              (setq end  (match-beginning 0)
                    end  (and end (bookmarkp-position-before-whitespace end))))))
        ;; If failed to find END, go to eob and search backward for BEG.
        (unless end (goto-char (point-max)))
        (if (search-backward bor-str (point-min) t) ; Find BEG, using `bor-str'.
            (setq beg  (point))
          ;; Verify that region is not after context.
          (unless (search-backward ar-str (point-min) t)
            (when (search-backward br-str (point-min) t) ; Find BEG, using `br-str'.
              (setq beg  (match-end 0)
                    beg  (and beg (bookmarkp-position-after-whitespace beg))))))
        (setq reg-retrieved-p  (or beg end)
              reg-relocated-p  reg-retrieved-p
              ;; If only one of BEG or END was found, the relocated region is only
              ;; approximate (keep the same length).  If both were found, it is exact.
              pos              (or beg  (and end (- end (- end-pos pos)))  pos)
              end-pos          (or end  (and beg (+ pos (- end-pos pos)))  end-pos))))
    ;; Region is available. Activate it and maybe save it.
    (cond (reg-retrieved-p
           (goto-char pos)
           (push-mark end-pos 'nomsg 'activate)
           (setq deactivate-mark  nil)
           (when bookmarkp-show-end-of-region
             (let ((end-win  (save-excursion (forward-line (window-height))
                                             (end-of-line) (point))))
               ;; Bounce point and mark.
               (save-excursion (sit-for 0.6) (exchange-point-and-mark) (sit-for 1))
               ;; Recenter if region end is not visible.
               (when (> end-pos end-win) (recenter 1))))
           ;; Maybe save region.
           (if (and reg-relocated-p (bookmarkp-save-new-region-location bmk pos end-pos))
               (message "Saved relocated region (from %d to %d)" pos end-pos)
             (message "Region is from %d to %d" pos end-pos)))
          (t                            ; No region.  Go to old start.  Don't push-mark.
           (goto-char pos) (forward-line 0)
           (message "No region from %d to %d" pos end-pos)))))

;; Same as `line-number-at-pos', which is not available until Emacs 22.
(defun bookmarkp-line-number-at-pos (&optional pos)
  "Buffer line number at position POS. Current line number if POS is nil.
Counting starts at (point-min), so any narrowing restriction applies."
  (1+ (count-lines (point-min) (save-excursion (when pos (goto-char pos))
                                               (forward-line 0) (point)))))

(defun bookmarkp-goto-position (file buf bufname pos forward-str behind-str)
  "Go to a bookmark that has no region.
Arguments are, respectively, the bookmark's file, buffer, buffer name,
position, and the context strings for the position."
  (if (and file (file-readable-p file) (not (buffer-live-p buf)))
      (with-current-buffer (find-file-noselect file) (setq buf  (buffer-name)))
    ;; No file found.  See if a non-file buffer exists for this.  If not, raise error.
    (unless (or (and buf (get-buffer buf))
                (and bufname (get-buffer bufname) (not (string= buf bufname))))
      (signal 'file-error `("Jumping to bookmark" "No such file or directory" file))))
  (set-buffer (or buf bufname))
  (when bookmarkp-jump-display-function
    (save-current-buffer (funcall bookmarkp-jump-display-function (current-buffer))))
  (setq deactivate-mark  t)
  (raise-frame)
  (goto-char pos)
  ;; Try to relocate position.
  ;; Search forward first.  Then, if FORWARD-STR exists and was found in the file, search
  ;; backward for BEHIND-STR.  The rationale is that if text was inserted between the two
  ;; in the file, then it's better to end up before point, so you can see the text, rather
  ;; than after it and not see it.
  (when (and forward-str (search-forward forward-str (point-max) t))
    (goto-char (match-beginning 0)))
  (when (and behind-str (search-backward behind-str (point-min) t)) (goto-char (match-end 0)))
  nil)                                  ; $$$$$ Why return nil?

(defun bookmarkp-jump-sequence (bookmark)
  "Handle a sequence bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for sequence bookmarks."
  (dolist (bmk  (bookmark-prop-get bookmark 'sequence))
    (bookmark--jump-via bmk bookmarkp-sequence-jump-display-function))
  (message "Done invoking bookmarks in sequence `%s'"
           (if (stringp bookmark) bookmark (bookmark-name-from-full-record bookmark))))

(defun bookmarkp-jump-function (bookmark)
  "Handle a function bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for function bookmarks."
  (funcall (bookmark-prop-get bookmark 'function)))

(defun bookmarkp-make-bookmark-list-record ()
  "Create and return a bookmark-list bookmark record.
This records the current state of buffer `*Bookmark List*': the sort
order, filter, title, and omit list."
  (let ((state  `((last-sort-comparer          . ,bookmarkp-sort-comparer)
                  (last-reverse-sort-p         . ,bookmarkp-reverse-sort-p)
                  (last-reverse-multi-sort-p   . ,bookmarkp-reverse-multi-sort-p)
                  (last-bmenu-filter-function  . ,bookmarkp-bmenu-filter-function)
                  (last-omitted-list           . ,bookmarkp-bmenu-omitted-list)
                  (last-bmenu-title            . ,bookmarkp-bmenu-title)
                  (last-bmenu-toggle-filenames . ,bookmark-bmenu-toggle-filenames))))
    `(,@(bookmark-make-record-default 'point-only)
      (filename      . ,bookmarkp-non-file-filename)
      (bookmark-list . ,state)
      (handler       . bookmarkp-jump-bookmark-list))))

(add-hook 'bookmark-bmenu-mode-hook
          #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                            'bookmarkp-make-bookmark-list-record)))

(defun bookmarkp-jump-bookmark-list (bookmark)
  "Jump to bookmark-list bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bookmarkp-make-bookmark-list-record'."
  (let ((state  (bookmark-prop-get bookmark 'bookmark-list)))
    (setq bookmarkp-sort-comparer          (cdr (assq 'last-sort-comparer          state))
          bookmarkp-reverse-sort-p         (cdr (assq 'last-reverse-sort-p         state))
          bookmarkp-reverse-multi-sort-p   (cdr (assq 'last-reverse-multi-sort-p   state))
          bookmarkp-bmenu-filter-function  (cdr (assq 'last-bmenu-filter-function  state))
          bookmarkp-bmenu-omitted-list     (cdr (assq 'last-omitted-list           state))
          bookmarkp-bmenu-title            (cdr (assq 'last-bmenu-title            state))
          bookmark-bmenu-toggle-filenames  (cdr (assq 'last-bmenu-toggle-filenames state))))
  (let ((bookmark-alist  (if bookmarkp-bmenu-filter-function
                             (funcall bookmarkp-bmenu-filter-function)
                           bookmark-alist)))
    (bookmark-bmenu-list 'filteredp)
    (when (get-buffer "*Bookmark List*") (pop-to-buffer "*Bookmark List*"))))

;; Desktop bookmarks
;;;###autoload
(defun bookmarkp-set-desktop-bookmark (desktop-file) ; Bound globally to `C-x p K', `C-x r K'
  "Save the desktop as a bookmark.
You are prompted for the location for saving the desktop file."
  (interactive (list (read-file-name "Save desktop in file: ")))
  (set-text-properties 0 (length desktop-file) nil desktop-file)
  (unless (file-name-absolute-p desktop-file) (setq desktop-file  (expand-file-name desktop-file)))
  (unless (require 'desktop nil t) (error "You must have library `desktop.el' to use this command"))
  (let ((desktop-basefilename     (file-name-nondirectory desktop-file)) ; Emacs < 22
        (desktop-base-file-name   (file-name-nondirectory desktop-file)) ; Emacs 23+
        (desktop-dir              (file-name-directory desktop-file))
        (desktop-restore-eager    t)    ; Don't bother with lazy restore.
        (desktop-globals-to-save  (bookmarkp-remove-if
                                   #'(lambda (elt) (memq elt bookmarkp-desktop-no-save-vars))
                                   desktop-globals-to-save)))
    (if (< emacs-major-version 22)
        (desktop-save desktop-dir)      ; Emacs < 22 has no locking.
      (desktop-save desktop-dir 'RELEASE))
    (message "Desktop saved in `%s'" desktop-file)
    (let ((bookmark-make-record-function  #'(lambda () (bookmarkp-make-desktop-record desktop-file))))
      (call-interactively #'bookmark-set))))

(defun bookmarkp-make-desktop-record (desktop-file)
  "Create and return a desktop bookmark record.
DESKTOP-FILE is the absolute file name of the desktop file to use."
  `(,@(bookmark-make-record-default 'point-only)
      (filename     . ,bookmarkp-non-file-filename)
      (desktop-file . ,desktop-file)
      (handler      . bookmarkp-jump-desktop)))

(defun bookmarkp-jump-desktop (bookmark)
  "Jump to desktop bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bookmarkp-make-desktop-record'."
  (let ((desktop-file  (bookmark-prop-get bookmark 'desktop-file)))
    (unless (require 'desktop nil t) (error "You must have library `desktop.el' to use this command"))
    ;; (unless desktop-file (error "Not a desktop-bookmark: %S" bookmark)) ; Shouldn't happen.
    (bookmarkp-desktop-change-dir desktop-file)
    (unless (bookmarkp-desktop-read desktop-file) (error "Could not load desktop file"))))

;; Derived from code in `desktop-change-dir'.
;;;###autoload
(defun bookmarkp-desktop-change-dir (desktop-file)
  "Change to desktop saved in DESKTOP-FILE.
Kill the desktop as specified by variables `desktop-save-mode' and
 `desktop-save' (starting with Emacs 22).
Clear the desktop and load DESKTOP-FILE DIRNAME."
  (interactive (list (read-file-name "Change to desktop file: ")))
  (set-text-properties 0 (length desktop-file) nil desktop-file)
  (unless (file-name-absolute-p desktop-file) (setq desktop-file  (expand-file-name desktop-file)))
  (unless (require 'desktop nil t) (error "You must have library `desktop.el' to use this command"))
  (let ((desktop-basefilename     (file-name-nondirectory desktop-file)) ; Emacs < 22
        (desktop-base-file-name   (file-name-nondirectory desktop-file)) ; Emacs 23+
        (desktop-dir              (file-name-directory desktop-file))
        (desktop-restore-eager    t)    ; Don't bother with lazy restore.
        (desktop-globals-to-save  (bookmarkp-remove-if
                                   #'(lambda (elt) (memq elt bookmarkp-desktop-no-save-vars))
                                   desktop-globals-to-save)))
    (bookmarkp-desktop-kill)
    (desktop-clear)
    (desktop-read desktop-dir)))
    
;; Derived from code in `desktop-kill'.
(defun bookmarkp-desktop-kill ()
  "If `desktop-save-mode' is non-nil, do what `desktop-save' says to do.
This does nothing in Emacs versions prior to Emacs 22."
  ;; We assume here: `desktop.el' has been loaded and `desktop-dirname' is defined.
  (when (and (and (boundp 'desktop-save-mode) desktop-save-mode) ; Not defined in Emacs 20-21.
             (let ((exists  (file-exists-p (desktop-full-file-name))))
               (or (eq desktop-save t)
                   (and exists (memq desktop-save '(ask-if-new if-exists)))
                   (and (or (memq desktop-save '(ask ask-if-new))
                            (and exists (eq desktop-save 'ask-if-exists)))
                        (y-or-n-p "Save current desktop? ")))))
    (condition-case err
	(if (< emacs-major-version 22)
            (desktop-save desktop-dirname) ; Emacs < 22 has no locking.
          (desktop-save desktop-dirname 'RELEASE))
      (file-error (unless (yes-or-no-p "Error while saving the desktop.  Ignore? ")
                    (signal (car err) (cdr err))))))
  ;; Just release lock, regardless of whether this Emacs process is the owner.
  (desktop-release-lock))

;; Derived from code in `desktop-read'.
;;;###autoload
(defun bookmarkp-desktop-read (file)
  "Load desktop-file FILE, then run `desktop-after-read-hook'.
Return t if FILE was loaded, nil otherwise."
  (interactive)
  (unless (file-name-absolute-p file) (setq file  (expand-file-name file))) ; Shouldn't happen.
  (setq desktop-dirname  (file-name-directory file))
  (if (not (file-readable-p file))
      nil                               ; Return nil, meaning not loaded.
    (let ((desktop-restore-eager      t) ; Don't bother with lazy restore.
          (desktop-first-buffer       nil)
          (desktop-buffer-ok-count    0)
          (desktop-buffer-fail-count  0)
          (desktop-save               nil)) ; Prevent desktop saving during eval of desktop buffer.
      (when (fboundp 'desktop-lazy-abort) (desktop-lazy-abort)) ; Emacs 22+.
      (load file t t t)
      (when (boundp 'desktop-file-modtime) ; Emacs 22+
        (setq desktop-file-modtime  (nth 5 (file-attributes file))))
      ;; `desktop-create-buffer' puts buffers at end of the buffer list.
      ;; We want buffers existing prior to evaluating the desktop (and not reused) to be placed
      ;; at the end of the buffer list, so we move them here.
      (mapc 'bury-buffer (nreverse (cdr (memq desktop-first-buffer (nreverse (buffer-list))))))
      (switch-to-buffer (car (buffer-list)))
      (run-hooks 'desktop-delay-hook)
      (setq desktop-delay-hook  ())
      (run-hooks 'desktop-after-read-hook)
      (when (boundp 'desktop-buffer-ok-count) ; Emacs 22+
        (message "Desktop: %d buffer%s restored%s%s." desktop-buffer-ok-count
                 (if (= 1 desktop-buffer-ok-count) "" "s")
                 (if (< 0 desktop-buffer-fail-count)
                     (format ", %d failed to restore" desktop-buffer-fail-count)
                   "")
                 (if desktop-buffer-args-list
                     (format ", %d to be restored lazily" (length desktop-buffer-args-list))
                   "")))
      t)))                              ; Return t, meaning successfully loaded.

;;;###autoload
(defun bookmarkp-desktop-delete (bookmark-name)
  "Delete desktop bookmark BOOKMARK-NAME, and delete its desktop file.
Release the lock file in that desktop's directory.
\(This means that if you currently have locked a different desktop
in the same directory, then you will need to relock it.)"
  (interactive (let ((alist  (bookmarkp-desktop-alist-only)))
                 (list (bookmarkp-read-bookmark-for-type
                        "desktop " alist nil nil 'bookmarkp-desktop-history "Delete "))))
  (let ((desktop-file  (bookmark-prop-get bookmark-name 'desktop-file)))
    (unless desktop-file (error "Not a desktop-bookmark: `%s'" bookmark-name))
    ;; Release the desktop lock file in the same directory as DESKTOP-FILE.
    ;; This will NOT be the right thing to do if a desktop file different from DESKTOP-FILE
    ;; is currently locked in the same directory.
    (let ((desktop-dir  (file-name-directory desktop-file))) (desktop-release-lock))
    (when (file-exists-p desktop-file) (delete-file desktop-file)))
  (bookmark-delete bookmark-name))

;; W3M support
(defun bookmarkp-make-w3m-record ()
  "Make a special entry for w3m buffers."
  (require 'w3m)                        ; For `w3m-current-url'.
  `(,@(bookmark-make-record-default 'point-only)
    (filename . ,w3m-current-url)
    (handler . bookmarkp-jump-w3m)))

(add-hook 'w3m-mode-hook #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                                           'bookmarkp-make-w3m-record)))

(defun bookmarkp-w3m-set-new-buffer-name ()
  "Set the w3m buffer name according to the number of w3m buffers already open."
  (let ((len  (length (w3m-list-buffers 'nosort))))
    (if (eq len 0)  "*w3m*"  (format "*w3m*<%d>" (1+ len)))))

(defun bookmarkp-jump-w3m-new-session (bookmark)
  "Jump to W3M bookmark BOOKMARK, setting a new tab."
  (let ((buf   (bookmarkp-w3m-set-new-buffer-name)))
    (w3m-browse-url (bookmark-prop-get bookmark 'filename) 'newsession)
    (while (not (get-buffer buf)) (sit-for 1)) ; Be sure we have the W3M buffer.
    (with-current-buffer buf
      (goto-char (point-min))
      ;; Wait until data arrives in buffer, before setting region.
      (while (eq (line-beginning-position) (line-end-position)) (sit-for 1)))
    (bookmark-default-handler
     `("" (buffer . ,buf) . ,(bookmark-get-bookmark-record bookmark)))))

(defun bookmarkp-jump-w3m-only-one-tab (bookmark)
  "Close all W3M sessions and jump to BOOKMARK in a new W3M buffer."
  (w3m-quit 'force)                     ; Be sure we start with an empty W3M buffer.
  (w3m-browse-url (bookmark-prop-get bookmark 'filename))
  (with-current-buffer "*w3m*" (while (eq (point-min) (point-max)) (sit-for 1)))
  (bookmark-default-handler
   `("" (buffer . ,(buffer-name (current-buffer))) . ,(bookmark-get-bookmark-record bookmark))))

(defalias 'bmkext-jump-w3m 'bookmarkp-jump-w3m)
(defun bookmarkp-jump-w3m (bookmark)
  "Handler function for record returned by `bookmarkp-make-w3m-record'.
BOOKMARK is a bookmark name or a bookmark record.
Use multi-tabs in W3M if `bookmarkp-w3m-allow-multi-tabs' is non-nil."
  (if bookmarkp-w3m-allow-multi-tabs
      (bookmarkp-jump-w3m-new-session bookmark)
    (bookmarkp-jump-w3m-only-one-tab bookmark)))

;; GNUS support.  Does not handle regions.
(defun bookmarkp-make-gnus-record ()
  "Make a bookmark entry for a Gnus buffer."
  (require 'gnus)
  (unless (and (eq major-mode 'gnus-summary-mode) gnus-article-current)
    (error "Please retry from the Gnus summary buffer")) ;[1]
  (let* ((grp   (car gnus-article-current))
         (art   (cdr gnus-article-current))
         (head  (gnus-summary-article-header art))
         (id    (mail-header-id head)))
    `(,@(bookmark-make-record-default 'point-only)
        (filename . ,bookmarkp-non-file-filename)
        (group . ,grp) (article . ,art) (message-id . ,id) (handler . bookmarkp-jump-gnus))))

(add-hook 'gnus-summary-mode-hook #'(lambda ()
                                      (set (make-local-variable 'bookmark-make-record-function)
                                           'bookmarkp-make-gnus-record)))

;; Raise an error if we try to bookmark from here [1]
(add-hook 'gnus-article-mode-hook #'(lambda ()
                                      (set (make-local-variable 'bookmark-make-record-function)
                                           'bookmarkp-make-gnus-record)))

(defalias 'bmkext-jump-gnus 'bookmarkp-jump-gnus)
(defun bookmarkp-jump-gnus (bookmark)
  "Handler function for record returned by `bookmarkp-make-gnus-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((group    (bookmark-prop-get bookmark 'group))
        (article  (bookmark-prop-get bookmark 'article))
        (id       (bookmark-prop-get bookmark 'message-id))
        (buf      (bookmark-prop-get bookmark 'buffer)))
    (gnus-fetch-group group (list article))
    (gnus-summary-insert-cached-articles)
    (gnus-summary-goto-article id nil 'force)
    (bookmark-default-handler `("" (buffer . ,buf) . ,(bookmark-get-bookmark-record bookmark)))))

(when (> emacs-major-version 20)
  (defun bookmarkp-make-woman-record ()
    "Create bookmark record for `man' page bookmark created by `woman'."
    `(,@(bookmark-make-record-default 'point-only)
      (filename . ,woman-last-file-name) (handler . bookmarkp-jump-woman)))

  (add-hook 'woman-mode-hook #'(lambda ()
                                 (set (make-local-variable 'bookmark-make-record-function)
                                      'bookmarkp-make-woman-record))))

(defun bookmarkp-make-man-record ()
  "Create bookmark record for `man' page bookmark created by `man'."
  `(,@(bookmark-make-record-default 'point-only)
    (filename . ,bookmarkp-non-file-filename)
    (man-args . ,Man-arguments) (handler . bookmarkp-jump-man)))

  (add-hook 'Man-mode-hook #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                                             'bookmarkp-make-man-record)))

(defalias 'bmkext-jump-woman 'bookmarkp-jump-woman)
(defun bookmarkp-jump-woman (bookmark)
  "Handler function for `man' page bookmark created by `woman'."
  (unless (> emacs-major-version 20)
    (error "`woman' bookmarks are not supported in Emacs prior to Emacs 21"))
  (bookmark-default-handler
   `("" (buffer . ,(save-window-excursion (woman-find-file (bookmark-get-filename bookmark))
                                          (current-buffer)))
     . ,(bookmark-get-bookmark-record bookmark))))

(defalias 'bmkext-jump-man 'bookmarkp-jump-man)
(defun bookmarkp-jump-man (bookmark)
  "Handler function for `man' page bookmark created by `man'."
  (require 'man)
  (let ((Man-notify-method  (case bookmarkp-jump-display-function
                              (display-buffer    'quiet)
                              (switch-to-buffer  'pushy)
                              (t                 'friendly)))) ; pop-to
    (Man-getpage-in-background (bookmark-prop-get bookmark 'man-args))
    (while (get-process "man") (sit-for 0.2))
    (bookmark-default-handler (bookmark-get-bookmark bookmark))))

(defun bookmarkp-make-dired-record ()
  "Create and return a Dired bookmark record."
  (let ((hidden-dirs  (save-excursion (dired-remember-hidden))))
    (unwind-protect
         (let ((dir      (expand-file-name (if (consp dired-directory)
                                               (file-name-directory (car dired-directory))
                                             dired-directory)))
               (subdirs  (bookmarkp-dired-subdirs))
               (mfiles   (mapcar #'(lambda (mm) (car mm))
                                 (dired-remember-marks (point-min) (point-max)))))
           `(,dir
             ,@(bookmark-make-record-default 'point-only)
             (filename . ,dir) (dired-directory . ,dired-directory)
             (dired-marked . ,mfiles) (dired-switches . ,dired-actual-switches)
             (dired-subdirs . ,subdirs) (dired-hidden-dirs . ,hidden-dirs)
             (handler . bookmarkp-jump-dired)))
      (save-excursion			; Hide subdirs that were hidden.
        (mapcar #'(lambda (dir) (when (dired-goto-subdir dir) (dired-hide-subdir 1)))
                hidden-dirs)))))

(defun bookmarkp-dired-subdirs ()
  "Alist of inserted subdirectories, without their positions (markers).
This is like `dired-subdir-alist' but without the top-level dir and
without subdir positions (markers)."
  (interactive)
  (let ((subdir-alist      (cdr (reverse dired-subdir-alist))) ; Remove top.
        (subdirs-wo-posns  ()))
    (dolist (sub  subdir-alist)
      (push (list (car sub)) subdirs-wo-posns))
    subdirs-wo-posns))

(add-hook 'dired-mode-hook #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                                             'bookmarkp-make-dired-record)))

(defun bookmarkp-jump-dired (bookmark)
  "Jump to Dired bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bookmarkp-make-dired-record'."
  (let ((dir          (bookmark-prop-get bookmark 'dired-directory))
        (mfiles       (bookmark-prop-get bookmark 'dired-marked))
        (switches     (bookmark-prop-get bookmark 'dired-switches))
        (subdirs      (bookmark-prop-get bookmark 'dired-subdirs))
        (hidden-dirs  (bookmark-prop-get bookmark 'dired-hidden-dirs)))
    (case bookmarkp-jump-display-function
      (switch-to-buffer  (dired dir switches))
      (t                 (dired-other-window dir switches)))
    (let ((inhibit-read-only  t))
      (dired-insert-old-subdirs subdirs)
      (dired-mark-remembered (mapcar #'(lambda (mf) (cons (expand-file-name mf dir) 42)) mfiles))
      (save-excursion (mapcar #'(lambda (dir) (when (dired-goto-subdir dir) (dired-hide-subdir 1)))
                              hidden-dirs)))
    (goto-char (bookmark-get-position bookmark))))

(defun bookmarkp-read-bookmark-for-type (type alist &optional other-win pred hist action)
  "Read name of a bookmark of type TYPE.
ALIST is the alist used for completion - nil means `bookmark-alist'.
Non-nil OTHER-WIN means append \" in another window\" to the prompt.
Non-nil PRED is a predicate used for completion.
Non-nil HIST is a history symbol.  Default is `bookmark-history'.
ACTION is the action to mention in the prompt.  `Jump to ', if nil."
  (unless alist (error "No bookmarks of type %s" type))
  (bookmark-completing-read
   (concat (or action "Jump to ") type "bookmark" (and other-win " in another window"))
   (bookmarkp-default-bookmark-name alist)
   alist pred hist))

;;;###autoload
(defun bookmarkp-jump-to-type (bookmark-name &optional use-region-p) ; `C-x j :'
  "Jump to a bookmark of a given type.  You are prompted for the type.
Otherwise, this is the same as `bookmark-jump' - see that, in
particular, for info about using a prefix argument."
  (interactive
   (let* ((completion-ignore-case  t)
          (type-cands              bookmarkp-types-alist)
          (type                    (completing-read "Type of bookmark: " type-cands nil t))
          (alist                   (funcall (intern (format "bookmarkp-%s-alist-only" type))))
          (history                 (assoc-default type type-cands))
          (bmk-name                (bookmarkp-read-bookmark-for-type
                                    (concat type " ") alist nil nil history)))
     (list bmk-name  (or (equal type "Region") current-prefix-arg))))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-jump-to-type-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j :'
  "Jump to a bookmark of a given type.  You are prompted for the type.
See `bookmarkp-jump-to-type'."
  (interactive
   (let* ((completion-ignore-case  t)
          (type-cands              bookmarkp-types-alist)
          (type                    (completing-read "Type of bookmark: " type-cands nil t))
          (alist                   (funcall (intern (format "bookmarkp-%s-alist-only" type))))
          (history                 (assoc-default type type-cands))
          (bmk-name                (bookmarkp-read-bookmark-for-type
                                    (concat type " ") alist t nil history)))
     (list bmk-name (or (equal type "Region") current-prefix-arg))))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-bookmark-list-jump (bookmark-name &optional use-region-p) ; `C-x j B'
  "Jump to a bookmark-list bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-bookmark-list-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "bookmark-list " alist nil nil
                                             'bookmarkp-bookmark-list-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-desktop-jump (bookmark-name &optional use-region-p) ; `C-x j K'
  "Jump to a desktop bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-desktop-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "desktop " alist nil nil 'bookmarkp-desktop-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-dired-jump (bookmark-name &optional use-region-p) ; `C-x j d'
  "Jump to a Dired bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-dired-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Dired " alist nil nil 'bookmarkp-dired-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-dired-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j d'
  "Jump to a Dired bookmark in another window.
See `bookmarkp-dired-jump'."
  (interactive
   (let ((alist  (bookmarkp-dired-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Dired " alist t nil 'bookmarkp-dired-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-dired-jump-current (bookmark-name &optional use-region-p)
  "Jump to a Dired bookmark for the current directory.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-dired-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Dired " alist nil
                                             (lambda (bmk-name)
                                               (let ((dir  (bookmark-get-filename bmk-name)))
                                                 (string= dir default-directory)))
                                             'bookmarkp-dired-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-dired-jump-current-other-window (bookmark-name &optional use-region-p)
  "Jump to a Dired bookmark for the current directory in another window.
See `bookmarkp-dired-jump-current'."
  (interactive
   (let ((alist  (bookmarkp-dired-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Dired " alist t
                                             (lambda (bmk-name)
                                               (let ((dir  (bookmark-get-filename bmk-name)))
                                                 (string= dir default-directory)))
                                             'bookmarkp-dired-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-file-jump (bookmark-name &optional use-region-p) ; `C-x j f'
  "Jump to a file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "file " alist nil nil 'bookmarkp-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j f'
  "Jump to a file or directory bookmark in another window.
See `bookmarkp-file-jump'."
  (interactive
   (let ((alist  (bookmarkp-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "file " alist t nil 'bookmarkp-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-gnus-jump (bookmark-name &optional use-region-p) ; `C-x j g'
  "Jump to a Gnus bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-gnus-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Gnus " alist nil nil 'bookmarkp-gnus-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-gnus-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j g'
  "Jump to a Gnus bookmark in another window.
See `bookmarkp-gnus-jump'."
  (interactive
   (let ((alist  (bookmarkp-gnus-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Gnus " alist t nil 'bookmarkp-gnus-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-info-jump (bookmark-name &optional use-region-p) ; `C-x j i'
  "Jump to an Info bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-info-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Info " alist nil nil 'bookmarkp-info-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-info-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j i'
  "Jump to an Info bookmark in another window.
See `bookmarkp-info-jump'."
  (interactive
   (let ((alist  (bookmarkp-info-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "Info " alist t nil 'bookmarkp-info-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-local-file-jump (bookmark-name &optional use-region-p) ; `C-x j l'
  "Jump to a local file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-local-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "local file " alist nil nil
                                             'bookmarkp-local-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-local-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j l'
  "Jump to a local file or directory bookmark in another window.
See `bookmarkp-local-file-jump'."
  (interactive
   (let ((alist  (bookmarkp-local-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "local file " alist t nil 'bookmarkp-local-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-man-jump (bookmark-name &optional use-region-p) ; `C-x j m'
  "Jump to a `man'-page bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-man-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "`man' " alist nil nil 'bookmarkp-man-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-man-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j m'
  "Jump to a `man'-page bookmark in another window.
See `bookmarkp-man-jump'."
  (interactive
   (let ((alist  (bookmarkp-man-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "`man' " alist t nil 'bookmarkp-man-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-non-file-jump (bookmark-name &optional use-region-p) ; `C-x j b'
  "Jump to a non-file (buffer) bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-non-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "non-file (buffer) " alist nil nil
                                             'bookmarkp-non-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-non-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j b'
  "Jump to a non-file (buffer) bookmark in another window.
See `bookmarkp-non-file-jump'."
  (interactive
   (let ((alist  (bookmarkp-non-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "non-file (buffer) " alist t nil
                                             'bookmarkp-non-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-region-jump (bookmark-name) ; `C-x j r'
  "Jump to a region bookmark.
This is a specialization of `bookmark-jump', but without a prefix arg."
  (interactive (list (bookmarkp-read-bookmark-for-type "region " (bookmarkp-region-alist-only)
                                                       nil nil 'bookmarkp-region-history)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer t))

;;;###autoload
(defun bookmarkp-region-jump-other-window (bookmark-name) ; `C-x 4 j r'
  "Jump to a region bookmark in another window.
See `bookmarkp-region-jump'."
  (interactive (list (bookmarkp-read-bookmark-for-type "region " (bookmarkp-region-alist-only)
                                                       t nil 'bookmarkp-region-history)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window t))

;;;###autoload
(defun bookmarkp-remote-file-jump (bookmark-name &optional use-region-p) ; `C-x j n'
  "Jump to a remote file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-remote-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "remote file " alist nil nil
                                             'bookmarkp-remote-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-remote-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j n'
  "Jump to a remote file or directory bookmark in another window.
See `bookmarkp-remote-file-jump'."
  (interactive
   (let ((alist  (bookmarkp-remote-file-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "remote file " alist t nil
                                             'bookmarkp-remote-file-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-w3m-jump (bookmark-name &optional use-region-p) ; `C-x j n'
  "Jump to a W3M bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bookmarkp-w3m-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "W3M " alist nil nil 'bookmarkp-w3m-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bookmarkp-w3m-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j w'
  "Jump to an W3M bookmark in another window.
See `bookmarkp-w3m-jump'."
  (interactive
   (let ((alist  (bookmarkp-w3m-alist-only)))
     (list (bookmarkp-read-bookmark-for-type "W3M " alist t nil 'bookmarkp-w3m-history)
           current-prefix-arg)))
  (bookmarkp-jump-1 bookmark-name 'switch-to-buffer-other-window use-region-p))

;;;###autoload
(defun bookmarkp-all-tags-regexp-jump (regexp bookmark) ; `C-x j t % *'
  "Jump to a BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((regexp  (read-string "Regexp for tags: "))
          (alist   (bookmarkp-remove-if-not
                    #'(lambda (bmk)
                        (let ((bmk-tags  (bookmarkp-get-tags bmk)))
                          (and bmk-tags
                               (bookmarkp-every #'(lambda (tag)
                                                    (string-match regexp (bookmarkp-tag-name tag)))
                                                bmk-tags))))
                    bookmark-alist)))
     (unless alist (error "No bookmarks have tags that match `%s'" regexp))
     (list regexp (bookmark-completing-read
                   "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bookmarkp-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t % *'
  "Jump to a BOOKMARK that has each tag matching REGEXP, in another window.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((regexp  (read-string "Regexp for tags: "))
          (alist   (bookmarkp-remove-if-not
                    #'(lambda (bmk)
                        (let ((bmk-tags  (bookmarkp-get-tags bmk)))
                          (and bmk-tags
                               (bookmarkp-every #'(lambda (tag)
                                                    (string-match regexp (bookmarkp-tag-name tag)))
                                                bmk-tags))))
                    bookmark-alist)))
     (unless alist (error "No bookmarks have tags that match `%s'" regexp))
     (list regexp (bookmark-completing-read
                   "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bookmarkp-some-tags-regexp-jump (regexp bookmark) ; `C-x j t % +'
  "Jump to a BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((regexp  (read-string "Regexp for tags: "))
          (alist   (bookmarkp-remove-if-not
                    #'(lambda (bmk)
                        (bookmarkp-some #'(lambda (tag)
                                            (string-match regexp (bookmarkp-tag-name tag)))
                                        (bookmarkp-get-tags bmk)))
                    bookmark-alist)))
     (unless alist (error "No bookmarks have tags that match `%s'" regexp))
     (list regexp (bookmark-completing-read
                   "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bookmarkp-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t % +'
  "Jump to a BOOKMARK that has a tag matching REGEXP, in another window.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((regexp  (read-string "Regexp for tags: "))
          (alist   (bookmarkp-remove-if-not
                    #'(lambda (bmk)
                        (bookmarkp-some #'(lambda (tag)
                                            (string-match regexp (bookmarkp-tag-name tag)))
                                        (bookmarkp-get-tags bmk)))
                    bookmark-alist)))
     (unless alist (error "No bookmarks have tags that match `%s'" regexp))
     (list regexp (bookmark-completing-read
                   "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bookmarkp-some-tags-jump (tags bookmark) ; `C-x j t +'
  "Jump to a BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag."
  (interactive
   (let* ((tags   (bookmarkp-read-tags-completing))
          (alist  (bookmarkp-remove-if-not
                   #'(lambda (bmk)
                       (bookmarkp-some #'(lambda (tag) (bookmarkp-has-tag-p bmk tag)) tags))
                   bookmark-alist)))
     (unless tags (error "You did not specify any tags"))
     (unless alist (error "No bookmarks have any of the specified tags" regexp))
     (list tags (bookmark-completing-read
                 "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bookmarkp-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t +'
  "Jump to a BOOKMARK that has at least one of the TAGS, in another window.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag."
  (interactive
   (let* ((tags   (bookmarkp-read-tags-completing))
          (alist  (bookmarkp-remove-if-not
                   #'(lambda (bmk)
                       (bookmarkp-some #'(lambda (tag) (bookmarkp-has-tag-p bmk tag)) tags))
                   bookmark-alist)))
     (unless tags (error "You did not specify any tags"))
     (unless alist (error "No bookmarks have any of the specified tags" regexp))
     (list tags (bookmark-completing-read
                 "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bookmarkp-all-tags-jump (tags bookmark) ; `C-x j t *'
  "Jump to a BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate."
  (interactive
   (let* ((tags   (bookmarkp-read-tags-completing))
          (alist  (bookmarkp-remove-if-not
                   #'(lambda (bmk)
                       (let ((bmk-tags  (bookmarkp-get-tags bmk)))
                         (and bmk-tags
                              (bookmarkp-every #'(lambda (tag) (bookmarkp-has-tag-p bmk tag))
                                               tags))))
                   bookmark-alist)))
     (unless alist (error "No bookmarks have all of the specified tags" regexp))
     (list tags (bookmark-completing-read
                 "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bookmarkp-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t +'
  "Jump to a BOOKMARK that has all of the TAGS, in another window.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate."
  (interactive
   (let* ((tags   (bookmarkp-read-tags-completing))
          (alist  (bookmarkp-remove-if-not
                   #'(lambda (bmk)
                       (let ((bmk-tags  (bookmarkp-get-tags bmk)))
                         (and bmk-tags
                              (bookmarkp-every #'(lambda (tag) (bookmarkp-has-tag-p bmk tag))
                                               tags))))
                   bookmark-alist)))
     (unless alist (error "No bookmarks have all of the specified tags" regexp))
     (list tags (bookmark-completing-read
                 "Bookmark" (bookmarkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))
 
;;(@* "Keymaps")
;;; Keymaps ----------------------------------------------------------

;; `bookmark-map'

;;;###autoload
(define-key ctl-x-map "p" bookmark-map)
;;;###autoload
(define-key ctl-x-map "pj" 'bookmark-jump-other-window)
;;;###autoload
(define-key ctl-x-map "rK" 'bookmarkp-set-desktop-bookmark)
;;;###autoload
(define-key bookmark-map "0" 'bookmarkp-empty-file)
;;;###autoload
(define-key bookmark-map "K" 'bookmarkp-set-desktop-bookmark)
;;;###autoload
(define-key bookmark-map "L" 'bookmarkp-switch-bookmark-file)
;;;###autoload
(define-key bookmark-map "o" 'bookmark-jump-other-window)
;;;###autoload
(define-key bookmark-map "q" 'bookmark-jump-other-window)
;;;###autoload
(define-key bookmark-map "?" 'bookmarkp-describe-bookmark)

;; `bookmark-bmenu-mode-map'

;;;###autoload
(when (< emacs-major-version 21)
  (define-key bookmark-bmenu-mode-map (kbd "RET") 'bookmark-bmenu-this-window))
;;;###autoload
(define-key bookmark-bmenu-mode-map "."    'bookmarkp-bmenu-show-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map ">"    'bookmarkp-bmenu-toggle-show-only-marked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "<"    'bookmarkp-bmenu-toggle-show-only-unmarked)
;;;###autoload
(define-key bookmark-bmenu-mode-map (kbd "M-<DEL>") 'bookmarkp-bmenu-unmark-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "%"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "%m"   'bookmarkp-bmenu-regexp-mark)
;;;###autoload
(define-key bookmark-bmenu-mode-map "*"    nil) ; For Emacs 20
;;;###autoload
(when (< emacs-major-version 21)
  (define-key bookmark-bmenu-mode-map "*m" 'bookmark-bmenu-mark))
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-a" 'bookmarkp-bmenu-search-marked-bookmarks-regexp)
;;;###autoload
(define-key bookmark-bmenu-mode-map "B"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "BM"   'bookmarkp-bmenu-mark-non-file-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "BS"   'bookmarkp-bmenu-show-only-non-files)
;;;###autoload
(define-key bookmark-bmenu-mode-map "c"    'bookmarkp-bmenu-define-command)
;;;###autoload
(define-key bookmark-bmenu-mode-map "C"    'bookmarkp-bmenu-define-full-snapshot-command)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-c" 'bookmarkp-bmenu-define-jump-marked-command)
;;;###autoload
(define-key bookmark-bmenu-mode-map "D"    'bookmarkp-bmenu-delete-marked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-d" nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-d>"    'bookmarkp-bmenu-dired-marked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-d\M-m" 'bookmarkp-bmenu-mark-dired-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-d\M-s" 'bookmarkp-bmenu-show-only-dired)
;;;###autoload
(define-key bookmark-bmenu-mode-map "E"    'bookmarkp-bmenu-edit-bookmark)
;;;###autoload
(define-key bookmark-bmenu-mode-map "F"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "FM"   'bookmarkp-bmenu-mark-file-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "FS"   'bookmarkp-bmenu-show-only-files)
;;;###autoload
(define-key bookmark-bmenu-mode-map "g"    'bookmarkp-bmenu-refresh-menu-list)
;;;###autoload
(define-key bookmark-bmenu-mode-map "G"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "GM"   'bookmarkp-bmenu-mark-gnus-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "GS"   'bookmarkp-bmenu-show-only-gnus)
;;;###autoload
(if (fboundp 'command-remapping)
    (define-key bookmark-bmenu-mode-map [remap describe-mode] 'bookmarkp-bmenu-mode-status-help)
  ;; In Emacs < 22, the `substitute-...' affects only `?', not `C-h m', so we add it separately.
  (substitute-key-definition 'describe-mode 'bookmarkp-bmenu-mode-status-help
                             bookmark-bmenu-mode-map)
  (define-key bookmark-bmenu-mode-map "\C-hm" 'bookmarkp-bmenu-mode-status-help))
;;;###autoload
(define-key bookmark-bmenu-mode-map (kbd "C-h RET")        'bookmarkp-bmenu-describe-this-bookmark)
;;;###autoload
(define-key bookmark-bmenu-mode-map (kbd "C-h C-<return>") 'bookmarkp-bmenu-describe-this-bookmark)
;;;###autoload
(define-key bookmark-bmenu-mode-map (kbd "C-<down>")       'bookmarkp-bmenu-describe-this+move-down)
;;;###autoload
(define-key bookmark-bmenu-mode-map (kbd "C-<up>")         'bookmarkp-bmenu-describe-this+move-up)
;;;###autoload
(define-key bookmark-bmenu-mode-map (kbd "M-<return>")     'bookmarkp-bmenu-w32-open)
;;;###autoload
(define-key bookmark-bmenu-mode-map [M-mouse-2]            'bookmarkp-bmenu-w32-open-with-mouse)
;;;###autoload
(define-key bookmark-bmenu-mode-map "I"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "IM"   'bookmarkp-bmenu-mark-info-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "IS"   'bookmarkp-bmenu-show-only-info-nodes)
;;;###autoload
(define-key bookmark-bmenu-mode-map "K"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "KM"   'bookmarkp-bmenu-mark-desktop-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "KS"   'bookmarkp-bmenu-show-only-desktops)
;;;###autoload
(define-key bookmark-bmenu-mode-map "L"    'bookmarkp-switch-bookmark-file)
;;;###autoload
(define-key bookmark-bmenu-mode-map "M"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "MM"   'bookmarkp-bmenu-mark-man-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "MS"   'bookmarkp-bmenu-show-only-man-pages)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-m" 'bookmarkp-bmenu-mark-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "O"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "O>"   'bookmarkp-bmenu-omit/unomit-marked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "OS"   'bookmarkp-bmenu-show-only-omitted)
;;;###autoload
(define-key bookmark-bmenu-mode-map "OU"   'bookmarkp-unomit-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "P"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "PB"   'bookmarkp-bmenu-filter-bookmark-name-incrementally)
;;;###autoload
(define-key bookmark-bmenu-mode-map "PF"   'bookmarkp-bmenu-filter-file-name-incrementally)
;;;###autoload
(define-key bookmark-bmenu-mode-map "PT"   'bookmarkp-bmenu-filter-tags-incrementally)
;;;###autoload
(define-key bookmark-bmenu-mode-map "q"    'bookmarkp-bmenu-quit)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-q" 'bookmarkp-bmenu-query-replace-marked-bookmarks-regexp)
;;;###autoload
(define-key bookmark-bmenu-mode-map "R"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "RM"   'bookmarkp-bmenu-mark-region-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "RS"   'bookmarkp-bmenu-show-only-regions)
;;;###autoload
(when (fboundp 'bookmark-bmenu-relocate)
  (define-key bookmark-bmenu-mode-map "\M-r" 'bookmark-bmenu-relocate)) ; `R' in Emacs
;;;###autoload
(define-key bookmark-bmenu-mode-map "S"    'bookmark-bmenu-save) ; `s' in Emacs
;;;###autoload
(define-key bookmark-bmenu-mode-map "s"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "s>"   'bookmarkp-bmenu-sort-marked-before-unmarked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "s0"   'bookmarkp-bmenu-sort-by-creation-time)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sb"   'bookmarkp-bmenu-sort-by-last-buffer-or-file-access)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sfd"  'bookmarkp-bmenu-sort-by-local-file-type)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sfn"  'bookmarkp-bmenu-sort-by-file-name)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sfs"  'bookmarkp-bmenu-sort-by-local-file-size)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sft"  'bookmarkp-bmenu-sort-by-last-local-file-access)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sfu"  'bookmarkp-bmenu-sort-by-last-local-file-update)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sg"   'bookmarkp-bmenu-sort-by-Gnus-thread)
;;;###autoload
(define-key bookmark-bmenu-mode-map "si"   'bookmarkp-bmenu-sort-by-Info-location)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sk"   'bookmarkp-bmenu-sort-by-bookmark-type)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sn"   'bookmarkp-bmenu-sort-by-bookmark-name)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sr"   'bookmarkp-reverse-sort-order)
;;;###autoload
(define-key bookmark-bmenu-mode-map "s\C-r" 'bookmarkp-reverse-multi-sort-order)
;;;###autoload
(define-key bookmark-bmenu-mode-map "ss"   'bookmarkp-bmenu-change-sort-order-repeat)
;;;###autoload
(define-key bookmark-bmenu-mode-map "st"   'bookmarkp-bmenu-sort-by-last-bookmark-access)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sv"   'bookmarkp-bmenu-sort-by-bookmark-visit-frequency)
;;;###autoload
(define-key bookmark-bmenu-mode-map "sw"   'bookmarkp-bmenu-sort-by-w3m-url)
;;;###autoload
(when (> emacs-major-version 22)        ; Emacs 23+
 (define-key bookmark-bmenu-mode-map (kbd "M-s a C-s") 'bookmarkp-bmenu-isearch-marked-bookmarks)
 (define-key bookmark-bmenu-mode-map (kbd "M-s a M-C-s")
   'bookmarkp-bmenu-isearch-marked-bookmarks-regexp))
;;;###autoload
(define-key bookmark-bmenu-mode-map "T"    nil) ; For Emacs20
;;;###autoload
(define-key bookmark-bmenu-mode-map "T0"   'bookmarkp-remove-all-tags)
;;;###autoload
(define-key bookmark-bmenu-mode-map "T+"   'bookmarkp-add-tags)
;;;###autoload
(define-key bookmark-bmenu-mode-map "T-"   'bookmarkp-remove-tags)
;;;###autoload
(define-key bookmark-bmenu-mode-map "T>+"  'bookmarkp-bmenu-add-tags-to-marked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "T>-"  'bookmarkp-bmenu-remove-tags-from-marked)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Td"   'bookmarkp-remove-tags-from-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tl"   'bookmarkp-list-all-tags)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tm*"  'bookmarkp-bmenu-mark-bookmarks-tagged-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tm%"  'bookmarkp-bmenu-mark-bookmarks-tagged-regexp)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tm+"  'bookmarkp-bmenu-mark-bookmarks-tagged-some)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tm~*" 'bookmarkp-bmenu-mark-bookmarks-tagged-not-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tm~+" 'bookmarkp-bmenu-mark-bookmarks-tagged-none)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tr"   'bookmarkp-rename-tag)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Ts"   'bookmarkp-define-tags-sort-command)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tu*"  'bookmarkp-bmenu-unmark-bookmarks-tagged-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tu+"  'bookmarkp-bmenu-unmark-bookmarks-tagged-some)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tu~*" 'bookmarkp-bmenu-unmark-bookmarks-tagged-not-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tu~+" 'bookmarkp-bmenu-unmark-bookmarks-tagged-none)
;;;###autoload
(define-key bookmark-bmenu-mode-map "Tv"   'bookmarkp-bmenu-set-tag-value)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-l" 'bookmarkp-toggle-saving-menu-list-state)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-~" 'bookmarkp-toggle-saving-bookmark-file)
;;;###autoload
(define-key bookmark-bmenu-mode-map "\M-t" 'bookmark-bmenu-toggle-filenames) ; `t' in Emacs
;;;###autoload
(define-key bookmark-bmenu-mode-map "t"    'bookmarkp-bmenu-toggle-marks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "U"    'bookmarkp-bmenu-unmark-all)
;;;###autoload
(define-key bookmark-bmenu-mode-map "V"    'bookmarkp-bmenu-w32-open-select)
;;;###autoload
(define-key bookmark-bmenu-mode-map "W"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmark-bmenu-mode-map "WM"   'bookmarkp-bmenu-mark-w3m-bookmarks)
;;;###autoload
(define-key bookmark-bmenu-mode-map "WS"   'bookmarkp-bmenu-show-only-w3m-urls)


;; `bookmark-jump-map' and `bookmarkp-jump-other-window-map'

(defvar bookmarkp-jump-map nil
  "Keymap containing bindings for bookmark jump commands.")

(defvar bookmarkp-jump-other-window-map nil
  "Keymap containing bindings for bookmark jump other-window commands.")

;;;###autoload
(define-prefix-command 'bookmarkp-jump-map)
;;;###autoload
(define-prefix-command 'bookmarkp-jump-other-window-map)
;;;###autoload
(define-key ctl-x-map   "j" bookmarkp-jump-map)
;;;###autoload
(define-key ctl-x-4-map "j" bookmarkp-jump-other-window-map)

;;;###autoload
(define-key bookmarkp-jump-map              "b"    'bookmarkp-non-file-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "b"    'bookmarkp-non-file-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "B"    'bookmarkp-bookmark-list-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "B"    'bookmarkp-bookmark-list-jump) ; Same
;;;###autoload
(define-key bookmarkp-jump-map              "d"    'bookmarkp-dired-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "d"    'bookmarkp-dired-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "f"    'bookmarkp-file-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "f"    'bookmarkp-file-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "g"    'bookmarkp-gnus-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "g"    'bookmarkp-gnus-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "i"    'bookmarkp-info-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "i"    'bookmarkp-info-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "j"    'bookmark-jump)
(put 'bookmark-jump :advertised-binding "\C-xjj")
;;;###autoload
(define-key bookmarkp-jump-other-window-map "j"    'bookmark-jump-other-window)
(put 'bookmark-jump-other-window :advertised-binding "\C-x4jj")
(put 'jump-other :advertised-binding "\C-x4jj")
;;;###autoload
(define-key bookmarkp-jump-map              "K"    'bookmarkp-desktop-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "K"    'bookmarkp-desktop-jump) ; Same
;;;###autoload
(define-key bookmarkp-jump-map              "l"    'bookmarkp-local-file-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "l"    'bookmarkp-local-file-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "m"    'bookmarkp-man-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "m"    'bookmarkp-man-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "n"    'bookmarkp-remote-file-jump) ; "_n_etwork"
;;;###autoload
(define-key bookmarkp-jump-other-window-map "n"    'bookmarkp-remote-file-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "r"    'bookmarkp-region-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "r"    'bookmarkp-region-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "t"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmarkp-jump-other-window-map "t"    nil) ; For Emacs 20
;;;###autoload
(define-key bookmarkp-jump-map              "t*"   'bookmarkp-all-tags-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "t*"   'bookmarkp-all-tags-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "t+"   'bookmarkp-some-tags-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "t+"   'bookmarkp-some-tags-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "t%"   nil) ; For Emacs 20
;;;###autoload
(define-key bookmarkp-jump-other-window-map "t%"   nil) ; For Emacs 20
;;;###autoload
(define-key bookmarkp-jump-map              "t%*"  'bookmarkp-all-tags-regexp-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "t%*"  'bookmarkp-all-tags-regexp-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "t%+"  'bookmarkp-some-tags-regexp-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "t%+"  'bookmarkp-some-tags-regexp-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              "w"    'bookmarkp-w3m-jump)
;;;###autoload
(define-key bookmarkp-jump-other-window-map "w"    'bookmarkp-w3m-jump-other-window)
;;;###autoload
(define-key bookmarkp-jump-map              ":"    'bookmarkp-jump-to-type)
;;;###autoload
(define-key bookmarkp-jump-other-window-map ":"    'bookmarkp-jump-to-type-other-window)


;; Add jump commands to other keymaps: Buffer-menu, Dired, Gnus, Info, Man, Woman, W3M.
(add-hook 'buffer-menu-mode-hook
          #'(lambda () (unless (lookup-key Buffer-menu-mode-map "j")
                         (define-key Buffer-menu-mode-map "j" 'bookmarkp-non-file-jump))))
(add-hook 'dired-mode-hook
          #'(lambda ()
              (let ((now  (lookup-key dired-mode-map "J")))
                ;; Uppercase, since `j' is `dired-goto-file'.
                (unless (and now (not (eq now 'undefined))) ; `dired+.el' uses `undefined'.
                  (define-key dired-mode-map "J" 'bookmarkp-dired-jump))
                (setq now  (lookup-key dired-mode-map "\C-j"))
                (unless (and now (not (eq now 'undefined))) ; `dired+.el' uses `undefined'.
                  (define-key dired-mode-map "\C-j" 'bookmarkp-dired-jump-current)))
              (let ((map   dired-mode-map)
                    (sep   '(menu-bar subdir separator-bookmarkp))
                    (bdj   '(menu-bar subdir bookmarkp-dired-jump))
                    (bdjc  '(menu-bar subdir bookmarkp-dired-jump-current)))
                (when (boundp 'diredp-menu-bar-subdir-menu) ; In `dired+el'.
                  (setq map   diredp-menu-bar-subdir-menu
                        sep   (cddr sep)
                        bdj   (cddr bdj)
                        bdjc  (cddr bdjc)))
                (define-key map (apply #'vector sep) '("--"))
                (define-key map (apply #'vector bdj)
                  '(menu-item "Jump to a Dired Bookmark" bookmarkp-dired-jump
                    :help "Jump to a bookmarked Dired buffer"))
                (define-key map (apply #'vector bdjc)
                  '(menu-item "Show This Dir Using a Bookmark" bookmarkp-dired-jump-current
                    :help "Use a bookmarked version of this directory")))))
(add-hook 'gnus-summary-mode-hook
          #'(lambda () (unless (lookup-key gnus-summary-mode-map "j")
                         (define-key gnus-summary-mode-map "j" 'bookmarkp-gnus-jump))))
(add-hook 'Info-mode-hook
          #'(lambda ()
              (unless (lookup-key Info-mode-map "j")
                (define-key Info-mode-map "j" 'bookmarkp-info-jump))
              (define-key-after Info-mode-menu [bookmarkp-info-jump]
                '(menu-item "Jump to an Info Bookmark" bookmarkp-info-jump
                  :help "Jump to a bookmarked Info node")
                'Go\ to\ Node\.\.\.)))  ; Used by `info(+).el' - corresponds to `Info-goto-node'.
(add-hook 'Man-mode-hook
          #'(lambda () (unless (lookup-key Man-mode-map "j")
                         (define-key Man-mode-map "j" 'bookmarkp-man-jump))))
(add-hook 'woman-mode-hook
          #'(lambda ()
              (unless (lookup-key woman-mode-map "j")
                (define-key woman-mode-map "j" 'bookmarkp-man-jump))
              (when (boundp 'woman-menu)
                (define-key-after woman-menu [bookmarkp-man-jump]
                  '(menu-item "Jump to a `man'-page Bookmark" bookmarkp-man-jump
                    :help "Jump to a bookmarked `man' page")
                  'WoMan\.\.\.)))) ; Used by `woman.el' - corresponds to command `woman'.
(add-hook 'w3m-minor-mode-hook
          #'(lambda () (unless (lookup-key w3m-minor-mode-map "j")
                         (define-key w3m-minor-mode-map "j" 'bookmarkp-w3m-jump))))
(add-hook 'w3m-mode-hook
          #'(lambda () (unless (lookup-key w3m-mode-map "j")
                         (define-key w3m-mode-map "j" 'bookmarkp-w3m-jump))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Only the doc string is different.
;;
(defun bookmark-bmenu-mode ()
  "Major mode for editing a list of bookmarks.
Each line represents an Emacs bookmark.\\<bookmark-bmenu-mode-map>


Help (Describe)
---------------

\\[bookmarkp-bmenu-describe-this-bookmark]\t- Show information about this bookmark (`C-u': \
internal form)
\\[bookmarkp-bmenu-describe-this+move-down]\t- Show the info, then move to next bookmark
\\[bookmarkp-bmenu-describe-this+move-up]\t- Show the info, then move to previous bookmark
\\[bookmark-bmenu-locate]\t- Show the location of this bookmark in the minibuffer
\\[bookmark-bmenu-show-annotation]\t- Show this bookmark's annotation
\\[bookmark-bmenu-show-all-annotations]\t- Show the annotations of all annotated bookmarks
\\[bookmark-bmenu-toggle-filenames]\t- Toggle showing filenames next to bookmarks

\\[bookmarkp-list-defuns-in-commands-file]
\t- List the commands defined in `bookmarkp-bmenu-commands-file'


Jump to (Visit)
---------------

\\[bookmark-bmenu-select]\t- Jump to this bookmark and also visit bookmarks marked `>'
\\[bookmark-bmenu-this-window]\t- Jump to this bookmark in the same window
\\[bookmark-bmenu-other-window]\t- Jump to this bookmark in another window
\\[bookmark-bmenu-switch-other-window]\t- Visit this bookmark in other window, without selecting it
\\[bookmark-bmenu-1-window]\t- Jump to this bookmark in a full-frame window
\\[bookmark-bmenu-2-window]\t- Jump to this bookmark and last-visited bookmark

\\[bookmark-jump]\t- Jump to a bookmark by name
\\[bookmarkp-jump-to-type]\t- Jump to a bookmark by type
\\[bookmarkp-desktop-jump]\t- Jump to a desktop bookmark
\\[bookmarkp-bookmark-list-jump]\t- Jump to a bookmark-list bookmark
\\[bookmarkp-dired-jump]\t- Jump to a Dired bookmark
\\[bookmarkp-file-jump]\t- Jump to a file bookmark
\\[bookmarkp-local-file-jump]\t- Jump to a local-file bookmark
\\[bookmarkp-remote-file-jump]\t- Jump to a remote-file bookmark
\\[bookmarkp-region-jump]\t- Jump to a region bookmark
\\[bookmarkp-info-jump]\t- Jump to a Info bookmark
\\[bookmarkp-man-jump]\t- Jump to a `man'-page bookmark
\\[bookmarkp-non-file-jump]\t- Jump to a non-file (buffer) bookmark
\\[bookmarkp-gnus-jump]\t- Jump to a Gnus bookmark
\\[bookmarkp-w3m-jump]\t- Jump to a W3M (URL) bookmark
\\[bookmarkp-some-tags-jump]\t- Jump to a bookmark with some tags you specify
\\[bookmarkp-some-tags-regexp-jump]\t- Jump to a bookmark with some tags matching a regexp
\\[bookmarkp-all-tags-jump]\t- Jump to a bookmark with all tags you specify
\\[bookmarkp-all-tags-regexp-jump]\t- Jump to a bookmark with all tags matching a regexp


General
-------

\\[bookmarkp-bmenu-refresh-menu-list]\t- Refresh (revert) to up-to-date bookmark list
\\[bookmarkp-bmenu-quit]\t- Quit (`*Bookmark List*')
\\[bookmarkp-bmenu-dired-marked]\t- Open Dired for the marked files and directories

\\[bookmark-bmenu-load]\t- Add bookmarks from a different bookmark file (extra load)
\\[bookmarkp-switch-bookmark-file]\t- Switch to a different bookmark file (overwrite load)
\\[bookmark-bmenu-save]\t- Save bookmarks (`C-u': prompt for the bookmark file to use)
\\[bookmarkp-toggle-saving-bookmark-file]\t- Toggle autosaving the bookmark file
\\[bookmarkp-toggle-saving-menu-list-state]\t- Toggle autosaving the bookmark-list display state

\\[bookmarkp-toggle-bookmark-set-refreshes]
\t- Toggle whether `bookmark-set' refreshes the bookmark list
\\[bookmarkp-make-function-bookmark]
\t- Create a function bookmark
\\[bookmarkp-bmenu-make-sequence-from-marked]
\t- Create a sequence bookmark from the marked bookmarks


Search-and-Replace Targets (in sort order)
--------------------------

\\[bookmarkp-bmenu-search-marked-bookmarks-regexp]\t\t- Regexp-search the marked file bookmarks
\\[bookmarkp-bmenu-query-replace-marked-bookmarks-regexp]\t\t- Query-replace the marked file \
bookmarks
M-s a C-s\t- Isearch the marked bookmarks (Emacs 23+)
M-s a C-M-s\t- Regexp Isearch the marked bookmarks (Emacs 23+)


Mark/Unmark
-----------

\(Mark means `>'.  Flag means `D'.   See also `Tags', below.)

\\[bookmark-bmenu-delete]\t- Flag this bookmark `D' for deletion, then move down
\\[bookmark-bmenu-delete-backwards]\t- Flag this bookmark `D' for deletion, then move up

\\[bookmark-bmenu-mark]\t- Mark this bookmark
\\[bookmark-bmenu-unmark]\t- Unmark this bookmark (`C-u': move up one line)
\\[bookmark-bmenu-backup-unmark]\t- Unmark previous bookmark (move up, then unmark)

\\[bookmarkp-bmenu-mark-all]\t- Mark all bookmarks
\\[bookmarkp-bmenu-regexp-mark]\t- Mark all bookmarks whose names match a regexp
\\[bookmarkp-bmenu-unmark-all]\t- Unmark all bookmarks (`C-u': interactive query)
\\[bookmarkp-bmenu-toggle-marks]\t- Toggle marks: unmark the marked and mark the unmarked

\\[bookmarkp-bmenu-mark-non-file-bookmarks]\t- Mark non-file (i.e. buffer) bookmarks
\\[bookmarkp-bmenu-mark-dired-bookmarks]\t- Mark Dired bookmarks
\\[bookmarkp-bmenu-mark-file-bookmarks]\t- Mark file & directory bookmarks (`C-u': local only)
\\[bookmarkp-bmenu-mark-gnus-bookmarks]\t- Mark Gnus bookmarks
\\[bookmarkp-bmenu-mark-info-bookmarks]\t- Mark Info bookmarks
\\[bookmarkp-bmenu-mark-desktop-bookmarks]\t- Mark desktop bookmarks
\\[bookmarkp-bmenu-mark-man-bookmarks]\t- Mark `man' page bookmarks (that's `M' twice, not Meta-M)
\\[bookmarkp-bmenu-mark-region-bookmarks]\t- Mark region bookmarks
\\[bookmarkp-bmenu-mark-w3m-bookmarks]\t- Mark W3M (URL) bookmarks


Modify
------

\(See also `Tags', next.)

\\[bookmark-bmenu-edit-annotation]\t- Edit this bookmark's annotation
\\[bookmarkp-bmenu-edit-bookmark]\t- Rename and relocate this bookmark
\\[bookmark-bmenu-rename]\t- Rename this bookmark
\\[bookmark-bmenu-relocate]\t- Relocate this bookmark (change file)
\\[bookmark-bmenu-execute-deletions]\t- Delete (visible) bookmarks flagged `D'
\\[bookmarkp-bmenu-delete-marked]\t- Delete (visible) bookmarks marked `>'


Tags
----

\\[bookmarkp-add-tags]\t- Add some tags to a bookmark
\\[bookmarkp-remove-tags]\t- Remove some tags from a bookmark
\\[bookmarkp-remove-all-tags]\t- Remove all tags from a bookmark
\\[bookmarkp-remove-tags-from-all]\t- Remove some tags from all bookmarks
\\[bookmarkp-rename-tag]\t- Rename a tag in all bookmarks
\\[bookmarkp-list-all-tags]\t- List all tags used in any bookmarks (`C-u': show tag values)
\\[bookmarkp-bmenu-set-tag-value]\t- Set the value of a tag (as attribute)

\\[bookmarkp-bmenu-add-tags-to-marked]\t- Add some tags to the marked bookmarks
\\[bookmarkp-bmenu-remove-tags-from-marked]\t- Remove some tags from the marked bookmarks

\\[bookmarkp-bmenu-mark-bookmarks-tagged-regexp]\t- Mark bookmarks having at least one \
tag that matches a regexp

\\[bookmarkp-bmenu-mark-bookmarks-tagged-some]\t- Mark bookmarks having at least one tag \
in a set    (OR)
\\[bookmarkp-bmenu-mark-bookmarks-tagged-all]\t- Mark bookmarks having all of the tags \
in a set     (AND)
\\[bookmarkp-bmenu-mark-bookmarks-tagged-none]\t- Mark bookmarks not having any of the tags \
in a set (NOT OR)
\\[bookmarkp-bmenu-mark-bookmarks-tagged-not-all]\t- Mark bookmarks not having all of the \
tags in a set (NOT AND)

\\[bookmarkp-bmenu-unmark-bookmarks-tagged-some]\t- Unmark bookmarks having at least one \
tag in a set  (OR)
\\[bookmarkp-bmenu-unmark-bookmarks-tagged-all]\t- Unmark bookmarks having all of the tags \
in a set   (AND)
\\[bookmarkp-bmenu-unmark-bookmarks-tagged-none]\t- Unmark bookmarks not having any tags \
in a set      (NOT OR)
\\[bookmarkp-bmenu-unmark-bookmarks-tagged-not-all]\t- Unmark bookmarks not having all tags \
in a set      (NOT AND)


Sort
----

\(Repeat to cycle normal/reversed/off, except as noted.)

\\[bookmarkp-bmenu-sort-marked-before-unmarked]\t- Sort marked bookmarks first
\\[bookmarkp-bmenu-sort-by-last-buffer-or-file-access]\t- Sort by last buffer or file \
access
\\[bookmarkp-bmenu-sort-by-Gnus-thread]\t- Sort by Gnus thread: group, article, message
\\[bookmarkp-bmenu-sort-by-Info-location]\t- Sort by Info manual, node, position
\\[bookmarkp-bmenu-sort-by-bookmark-type]\t- Sort by bookmark type
\\[bookmarkp-bmenu-sort-by-bookmark-name]\t- Sort by bookmark name
\\[bookmarkp-bmenu-sort-by-creation-time]\t- Sort by bookmark creation time
\\[bookmarkp-bmenu-sort-by-last-bookmark-access]\t- Sort by last bookmark access time
\\[bookmarkp-bmenu-sort-by-bookmark-visit-frequency]\t- Sort by bookmark visit frequency
\\[bookmarkp-bmenu-sort-by-w3m-url]\t- Sort by W3M URL

\\[bookmarkp-bmenu-sort-by-local-file-type]\t- Sort by local file type: file, symlink, dir
\\[bookmarkp-bmenu-sort-by-file-name]\t- Sort by file name
\\[bookmarkp-bmenu-sort-by-local-file-size]\t- Sort by local file size
\\[bookmarkp-bmenu-sort-by-last-local-file-access]\t- Sort by last local file access
\\[bookmarkp-bmenu-sort-by-last-local-file-update]\t- Sort by last local file update (edit)

\\[bookmarkp-reverse-sort-order]\t- Reverse current sort direction       (repeat to toggle)
\\[bookmarkp-reverse-multi-sort-order]\t- Complement sort predicate decisions  (repeat \
to toggle)
\\[bookmarkp-bmenu-change-sort-order-repeat]\t- Cycle sort orders                    (repeat \
to cycle)


Hide/Show
---------

\\[bookmarkp-bmenu-show-all]\t- Show all bookmarks
\\[bookmarkp-bmenu-toggle-show-only-marked]\t- Toggle showing only marked bookmarks
\\[bookmarkp-bmenu-toggle-show-only-unmarked]\t- Toggle showing only unmarked bookmarks
\\[bookmarkp-bmenu-show-only-non-files]\t- Show only non-file (i.e. buffer) bookmarks
\\[bookmarkp-bmenu-show-only-dired]\t- Show only Dired bookmarks
\\[bookmarkp-bmenu-show-only-files]\t- Show only file & directory bookmarks (`C-u': local only)
\\[bookmarkp-bmenu-show-only-gnus]\t- Show only Gnus bookmarks
\\[bookmarkp-bmenu-show-only-info-nodes]\t- Show only Info bookmarks
\\[bookmarkp-bmenu-show-only-desktops]\t- Show only desktop bookmarks
\\[bookmarkp-bmenu-show-only-man-pages]\t- Show only `man' page bookmarks
\\[bookmarkp-bmenu-show-only-regions]\t- Show only region bookmarks
\\[bookmarkp-bmenu-show-only-w3m-urls]\t- Show only W3M (URL) bookmarks
\\[bookmarkp-bmenu-filter-bookmark-name-incrementally]\t- Incrementally show only bookmarks \
whose names match a regexp
\\[bookmarkp-bmenu-filter-file-name-incrementally]\t- Incrementally show only bookmarks whose \
files match a regexp
\\[bookmarkp-bmenu-filter-tags-incrementally]\t- Incrementally show only bookmarks whose tags \
match a regexp


Omit/Un-omit
------------

\\[bookmarkp-bmenu-show-only-omitted]\t- Show (only) the omitted bookmarks
\\[bookmarkp-bmenu-show-all]\t- Show the un-omitted bookmarks (all)
\\[bookmarkp-bmenu-omit/unomit-marked]\t- Omit the marked bookmarks; un-omit them if after \
`\\[bookmarkp-bmenu-show-only-omitted]'
\\[bookmarkp-unomit-all]\t- Un-omit all omitted bookmarks


Define Commands for `*Bookmark List*'
-------------------------------------

\\[bookmarkp-bmenu-define-command]\t- Define a command to restore the current sort order & filter
\\[bookmarkp-bmenu-define-full-snapshot-command]\t- Define a command to restore the current \
bookmark-list state
\\[bookmarkp-define-tags-sort-command]\t- Define a command to sort bookmarks by tags
\\[bookmarkp-bmenu-define-jump-marked-command]\t- Define a command to jump to a bookmark that is \
now marked


Options for `*Bookmark List*'
-----------------------------

bookmarkp-sort-comparer          - Initial sort
bookmarkp-sort-orders-for-cycling-alist
                                 - Sort orders that \
`\\[bookmarkp-bmenu-change-sort-order-repeat]'... cycles
bookmark-bmenu-toggle-filenames  - Show filenames initially?
bookmark-bmenu-file-column       - Bookmark width if files are shown
bookmarkp-bmenu-state-file       - File to save bookmark-list state
                                   (\"home\") nil: do not save/restore
bookmarkp-bmenu-omitted-list     - List of omitted bookmarks


Other Options
-------------

bookmarkp-menu-popup-max-length  - Use menus to choose bookmarks?
bookmark-completion-ignore-case  - Case-sensitive completion?
bookmark-default-file            - File to save bookmarks in
bookmarkp-save-new-location-flag - Save if bookmark relocated?
bookmark-save-flag               - Whether and when to save
bookmark-default-file            - Numbered backups of bookmark file?
bookmark-use-annotations         - Query for annotation when saving?

bookmarkp-use-region-flag        - Activate saved region when visit?
bookmarkp-su-or-sudo-regexp      - Bounce-show each end of region?
bookmark-automatically-show-annotations  - Show annotation when visit?
bookmarkp-sequence-jump-display-function - How to display a sequence
bookmark-menu-length             - Max size of bookmark-name menu item"
  (kill-all-local-variables)
  (use-local-map bookmark-bmenu-mode-map)
  (setq truncate-lines t)
  (setq buffer-read-only t)
  (setq major-mode 'bookmark-bmenu-mode)
  (setq mode-name "Bookmark Menu")
  (if (fboundp 'run-mode-hooks)
      (run-mode-hooks 'bookmark-bmenu-mode-hook)
    (run-hooks 'bookmark-bmenu-mode-hook)))


;; Vanilla `Bookmarks' menu (see also [jump], below).
(define-key-after menu-bar-bookmark-map [bookmarkp-empty-file]
  '(menu-item "New (Empty) Bookmark File..." bookmarkp-empty-file
    :help "Create a new, empty bookmark file, or empty an existing bookmark file")
  'write)
(define-key menu-bar-bookmark-map [load] ; Just to modify text slightly.
  '(menu-item "Add Bookmarks from File..." bookmark-load
    :help "Load additional bookmarks from a bookmark file"))
(define-key-after menu-bar-bookmark-map [load-read-only]
  '(menu-item "Switch to Bookmark File..." bookmarkp-switch-bookmark-file
    :help "Switch to a different bookmark file, *replacing* the current set of bookmarks")
  'load)

(defvar bookmarkp-bmenu-menubar-menu (make-sparse-keymap "Bookmark+"))
(define-key bookmark-bmenu-mode-map [menu-bar bookmarkp]
  (cons "Bookmark+" bookmarkp-bmenu-menubar-menu))

;; Top level
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-quit]
  '(menu-item "Quit" bookmarkp-bmenu-quit
    :help "Quit the bookmark list, saving its state and the current set of bookmarks"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-mode-status-help]
  '(menu-item "Current Status, Mode Help" bookmarkp-bmenu-mode-status-help :keys "?"
    :help "Describe `*Bookmark List*' and show its current status"))
(define-key bookmarkp-bmenu-menubar-menu [top-sep2] '("--"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-toggle-saving-menu-list-state]
  '(menu-item "Toggle Autosaving Display State" bookmarkp-toggle-saving-menu-list-state
    :help "Toggle the value of option `bookmarkp-bmenu-state-file'"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-toggle-saving-bookmark-file]
  '(menu-item "Toggle Autosaving Bookmark File" bookmarkp-toggle-saving-bookmark-file
    :help "Toggle the value of option `bookmark-save-flag'"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-switch-bookmark-file]
  '(menu-item "Switch to Bookmark File..." bookmarkp-switch-bookmark-file
    :help "Switch to a different bookmark file, *replacing* the current set of bookmarks"))
(define-key bookmarkp-bmenu-menubar-menu [bookmark-bmenu-load]
  '(menu-item "Add Bookmarks from File..." bookmark-bmenu-load
    :help "Load additional bookmarks from a bookmark file"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-empty-file]
  '(menu-item "New (Empty) Bookmark File..." bookmarkp-empty-file
    :help "Create a new, empty bookmark file, or empty an existing bookmark file"))
(define-key bookmarkp-bmenu-menubar-menu [bookmark-write]
  '(menu-item "Save As..." bookmark-write
    :help "Write the current set of bookmarks to a file whose name you enter"))
(define-key bookmarkp-bmenu-menubar-menu [bookmark-bmenu-save]
  '(menu-item "Save" bookmark-bmenu-save
    :help "Save the current set of bookmarks to the current bookmark file"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-refresh-menu-list]
  '(menu-item "Refresh (Revert)" bookmarkp-bmenu-refresh-menu-list
    :help "Update the displayed bookmark list to reflect the currently defined bookmarks"))
(define-key bookmarkp-bmenu-menubar-menu [top-sep1] '("--"))

(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-make-function-bookmark]
  '(menu-item "New Function Bookmark..." bookmarkp-make-function-bookmark
    :help "Create a bookmark that will invoke FUNCTION when \"jumped\" to"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-make-sequence-from-marked]
  '(menu-item "New Sequence Bookmark from Marked..." bookmarkp-bmenu-make-sequence-from-marked
    :help "Create or update a sequence bookmark from the visible marked bookmarks"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-list-defuns-in-commands-file]
  '(menu-item "List User-Defined Commands" bookmarkp-list-defuns-in-commands-file
    :help "List the functions defined in `bookmarkp-bmenu-commands-file'"))

(defvar bookmarkp-bmenu-define-command-menu (make-sparse-keymap "Define Command"))
(define-key bookmarkp-bmenu-menubar-menu [define-command]
  (cons "Define Command" bookmarkp-bmenu-define-command-menu))

(define-key bookmarkp-bmenu-define-command-menu [bookmarkp-bmenu-define-full-snapshot-command]
  '(menu-item "To Restore Full Bookmark-List State..." bookmarkp-bmenu-define-full-snapshot-command
    :help "Define a command to restore the current bookmark-list state"))
(define-key bookmarkp-bmenu-define-command-menu [bookmarkp-bmenu-define-command]
  '(menu-item "To Restore Current Order and Filter..." bookmarkp-bmenu-define-command
    :help "Define a command to use the current sort order, filter, and omit list"))
(define-key bookmarkp-bmenu-define-command-menu [bookmarkp-define-tags-sort-command]
  '(menu-item "To Sort by Specific Tags..." bookmarkp-define-tags-sort-command
    :help "Define a command to sort bookmarks in the bookmark list by certain tags"))
(define-key bookmarkp-bmenu-define-command-menu [bookmarkp-bmenu-define-jump-marked-command]
  '(menu-item "To Jump to a Bookmark Now Marked..." bookmarkp-bmenu-define-jump-marked-command
    :help "Define a command to jump to one of the bookmarks that is now marked"
    :enable bookmarkp-bmenu-marked-bookmarks))

(defvar bookmarkp-bmenu-jump-menu (make-sparse-keymap "Jump To"))
(define-key bookmarkp-bmenu-menubar-menu [jump] (cons "Jump To" bookmarkp-bmenu-jump-menu))
;; Add `Jump' menu also to the vanilla `Bookmarks' menu, and remove the two jump commands there.
(define-key menu-bar-bookmark-map [jump] (cons "Jump To Bookmark" bookmarkp-bmenu-jump-menu))
(define-key menu-bar-bookmark-map [jump-other] nil)

(define-key bookmarkp-bmenu-jump-menu [bookmarkp-all-tags-regexp-jump-other-window]
  '(menu-item "All Tags Matching Regexp..." bookmarkp-all-tags-regexp-jump-other-window
    :help "Jump to a bookmark that has each tag matching a regexp that you enter"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-some-tags-regexp-jump-other-window]
  '(menu-item "Any Tag Matching Regexp..." bookmarkp-some-tags-regexp-jump-other-window
    :help "Jump to a bookmark that has at least one tag matching a regexp that you enter"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-all-tags-jump-other-window]
  '(menu-item "All Tags in Set..." bookmarkp-all-tags-jump-other-window
    :help "Jump to a bookmark that has all of a set of tags that you enter"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-some-tags-jump-other-window]
  '(menu-item "Any Tag in Set..." bookmarkp-some-tags-jump-other-window
    :help "Jump to a bookmark that has some of a set of tags that you enter"))
(define-key bookmarkp-bmenu-jump-menu [jump-sep1] '("--"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-w3m-jump-other-window]
  '(menu-item "URL (W3M)..." bookmarkp-w3m-jump-other-window :help "Jump to an W3M bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-gnus-jump-other-window]
  '(menu-item "Gnus..." bookmarkp-gnus-jump-other-window :help "Jump to a Gnus bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-man-jump-other-window]
  '(menu-item "Man Page..." bookmarkp-man-jump-other-window :help "Jump to a `man'-page bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-info-jump-other-window]
  '(menu-item "Info Node..." bookmarkp-info-jump-other-window :help "Jump to an Info bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-non-file-jump-other-window]
  '(menu-item "Buffer (Non-File)..." bookmarkp-non-file-jump-other-window
    :help "Jump to a non-file (buffer) bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-region-jump-other-window]
  '(menu-item "Region..." bookmarkp-region-jump-other-window
    :help "Jump to a bookmark that defines the active region"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-remote-file-jump-other-window]
  '(menu-item "Remote File..." bookmarkp-remote-file-jump-other-window
    :help "Jump to a remote file or directory bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-local-file-jump-other-window]
  '(menu-item "Local File..." bookmarkp-local-file-jump-other-window
    :help "Jump to a local file or directory bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-file-jump-other-window]
  '(menu-item "File..." bookmarkp-file-jump-other-window
    :help "Jump to a file or directory bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-dired-jump-other-window]
  '(menu-item "Dired..." bookmarkp-dired-jump-other-window
    :help "Jump to a Dired bookmark, restoring the recorded Dired state"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-bookmark-list-jump]
  '(menu-item "Bookmark List..." bookmarkp-bookmark-list-jump
    :help "Jump to a bookmark-list bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-desktop-jump]
  '(menu-item "Desktop..." bookmarkp-desktop-jump :help "Jump to a desktop bookmark"))
(define-key bookmarkp-bmenu-jump-menu [bookmarkp-jump-to-type-other-window]
  '(menu-item "Of Type..." bookmarkp-jump-to-type-other-window
    :help "Jump to a bookmark of a type that you specify"))
(define-key bookmarkp-bmenu-jump-menu [bookmark-jump-other-window]
  '(menu-item "Any in Other Window..." bookmark-jump-other-window
    :help "Jump to a bookmark of any type, in another window"))
(define-key bookmarkp-bmenu-jump-menu [bookmark-jump]
  '(menu-item "Any..." bookmark-jump :help "Jump to a bookmark of any type, in this window"))

(defvar bookmarkp-bmenu-sort-menu (make-sparse-keymap "Sort"))
(define-key bookmarkp-bmenu-menubar-menu [sort] (cons "Sort" bookmarkp-bmenu-sort-menu))

(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-w3m-url]
  '(menu-item "By URL (W3M)" bookmarkp-bmenu-sort-by-w3m-url
    :help "Sort W3M bookmarks alphabetically by their URL/filename"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-Gnus-thread]
  '(menu-item "By Gnus Thread" bookmarkp-bmenu-sort-by-Gnus-thread
    :help "Sort Gnus bookmarks by group, then by article, then by message"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-Info-location]
  '(menu-item "By Info Node" bookmarkp-bmenu-sort-by-Info-location
    :help "Sort Info bookmarks by file name, then node name, then position"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-last-local-file-update]
  '(menu-item "By Last Local File Update" bookmarkp-bmenu-sort-by-last-local-file-update
    :help "Sort bookmarks by last local file update time"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-last-buffer-or-file-access]
  '(menu-item "By Last Buffer/File Access" bookmarkp-bmenu-sort-by-last-buffer-or-file-access
    :help "Sort bookmarks by time of last buffer access or local-file access"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-local-file-size]
  '(menu-item "By Local File Size" bookmarkp-bmenu-sort-by-local-file-size
    :help "Sort bookmarks by local file size"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-local-file-type]
  '(menu-item "By Local File Type" bookmarkp-bmenu-sort-by-local-file-type
    :help "Sort bookmarks by local file type: file, symlink, directory"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-bookmark-type]
  '(menu-item "By Type" bookmarkp-bmenu-sort-by-bookmark-type
    :help "Sort bookmarks by type: Info, Gnus, W3M, files, other"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-file-name]
  '(menu-item "By File Name" bookmarkp-bmenu-sort-by-file-name
    :help "Sort bookmarks by file name"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-bookmark-name]
  '(menu-item "By Bookmark Name" bookmarkp-bmenu-sort-by-bookmark-name
    :help "Sort bookmarks by bookmark name, respecting `case-fold-search'"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-creation-time]
  '(menu-item "By Creation Time" bookmarkp-bmenu-sort-by-creation-time
    :help "Sort bookmarks by the time of their creation"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-last-bookmark-access]
  '(menu-item "By Last Bookmark Access" bookmarkp-bmenu-sort-by-last-bookmark-access
    :help "Sort bookmarks by the time of their last visit as bookmarks"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-by-bookmark-visit-frequency]
  '(menu-item "By Bookmark Use" bookmarkp-bmenu-sort-by-bookmark-visit-frequency
    :help "Sort bookmarks by the number of times they were visited as bookmarks"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-bmenu-sort-marked-before-unmarked]
  '(menu-item "Marked Before Unmarked" bookmarkp-bmenu-sort-marked-before-unmarked
    :help "Sort bookmarks by putting marked before unmarked"))
(define-key bookmarkp-bmenu-sort-menu [bookmarkp-reverse-sort-order]
  '(menu-item "Reverse" bookmarkp-reverse-sort-order
    :help "Reverse the current bookmark sort order"))

(defvar bookmarkp-bmenu-show-menu (make-sparse-keymap "Show"))
(define-key bookmarkp-bmenu-menubar-menu [show] (cons "Show" bookmarkp-bmenu-show-menu))

(define-key bookmarkp-bmenu-show-menu [bookmark-bmenu-show-all-annotations]
  '(menu-item "Show Annotations" bookmark-bmenu-show-all-annotations
    :help "Show the annotations for all bookmarks (in another window)"))
(define-key bookmarkp-bmenu-show-menu [bookmark-bmenu-toggle-filenames]
  '(menu-item "Show/Hide File Names" bookmark-bmenu-toggle-filenames
    :help "Toggle whether filenames are shown in the bookmark list"))
(define-key bookmarkp-bmenu-show-menu [show-sep1] '("--"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-all]
  '(menu-item "Show All" bookmarkp-bmenu-show-all
    :help "Show all bookmarks currently known to the bookmark list"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-filter-tags-incrementally]
  '(menu-item "Show Only Tag Matches..." bookmarkp-bmenu-filter-tags-incrementally
    :help "Incrementally filter bookmarks by tags using a regexp"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-filter-file-name-incrementally]
  '(menu-item "Show Only File Name Matches..." bookmarkp-bmenu-filter-file-name-incrementally
    :help "Incrementally filter bookmarks by file name using a regexp"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-filter-bookmark-name-incrementally]
  '(menu-item "Show Only Name Matches..." bookmarkp-bmenu-filter-bookmark-name-incrementally
    :help "Incrementally filter bookmarks by bookmark name using a regexp"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-w3m-urls]
  '(menu-item "Show Only URLs (W3M)" bookmarkp-bmenu-show-only-w3m-urls
    :help "Display (only) the w3m bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-gnus]
  '(menu-item "Show Only Gnus Messages" bookmarkp-bmenu-show-only-gnus
    :help "Display (only) the Gnus bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-man-pages]
  '(menu-item "Show Only UNIX Manual Pages" bookmarkp-bmenu-show-only-man-pages
    :help "Display (only) the `man' page bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-info-nodes]
  '(menu-item "Show Only Info Nodes" bookmarkp-bmenu-show-only-info-nodes
    :help "Display (only) the Info bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-dired]
  '(menu-item "Show Only Dired Buffers" bookmarkp-bmenu-show-only-dired
    :help "Display (only) the Dired bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-desktops]
  '(menu-item "Show Only Desktops" bookmarkp-bmenu-show-only-desktops
    :help "Display (only) the desktop bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-regions]
  '(menu-item "Show Only Regions" bookmarkp-bmenu-show-only-regions
    :help "Display (only) the bookmarks that record a region"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-non-files]
  '(menu-item "Show Only Non-Files (Buffers)" bookmarkp-bmenu-show-only-non-files
    :help "Display (only) the non-file bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-show-only-files]
  '(menu-item "Show Only Files" bookmarkp-bmenu-show-only-files
    :help "Display (only) the file and directory bookmarks"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-toggle-show-only-unmarked]
  '(menu-item "Show Only Unmarked" bookmarkp-bmenu-toggle-show-only-unmarked
    :help "Hide all marked bookmarks.  Repeat to toggle, showing all"))
(define-key bookmarkp-bmenu-show-menu [bookmarkp-bmenu-toggle-show-only-marked]
  '(menu-item "Show Only Marked" bookmarkp-bmenu-toggle-show-only-marked
    :help "Hide all unmarked bookmarks.  Repeat to toggle, showing all"))

(defvar bookmarkp-bmenu-tags-menu (make-sparse-keymap "Tags"))
(define-key bookmarkp-bmenu-menubar-menu [tags] (cons "Tags" bookmarkp-bmenu-tags-menu))

(define-key bookmarkp-bmenu-tags-menu [bookmarkp-list-all-tags]
  '(menu-item "List All Tags" bookmarkp-list-all-tags
    :help "List all tags used for any bookmarks"))
(define-key bookmarkp-bmenu-tags-menu [bookmarkp-rename-tag]
  '(menu-item "Rename Tag..." bookmarkp-rename-tag
    :help "Rename a tag in all bookmarks, even those not showing"))
(define-key bookmarkp-bmenu-tags-menu [bookmarkp-remove-tags-from-all]
  '(menu-item "Remove Some Tags from All..." bookmarkp-remove-tags-from-all
    :help "Remove a set of tags from all bookmarks"))
(define-key bookmarkp-bmenu-tags-menu [bookmarkp-bmenu-remove-tags-from-marked]
  '(menu-item "Remove Some Tags from Marked..." bookmarkp-bmenu-remove-tags-from-marked
    :help "Remove a set of tags from each of the marked bookmarks"))
(define-key bookmarkp-bmenu-tags-menu [bookmarkp-bmenu-add-tags-to-marked]
  '(menu-item "Add Some Tags to Marked..." bookmarkp-bmenu-add-tags-to-marked
    :help "Add a set of tags to each of the marked bookmarks"))

(defvar bookmarkp-bmenu-omit-menu (make-sparse-keymap "Omit"))
(define-key bookmarkp-bmenu-menubar-menu [omitting] (cons "Omit" bookmarkp-bmenu-omit-menu))

(define-key bookmarkp-bmenu-omit-menu [bookmarkp-bmenu-show-all]
  '(menu-item "Show All" bookmarkp-bmenu-show-all
    :visible (eq bookmarkp-bmenu-filter-function 'bookmarkp-omitted-alist-only)
    :help "Show all bookmarks (except omitted)"))
(define-key bookmarkp-bmenu-omit-menu [bookmarkp-bmenu-show-only-omitted]
  '(menu-item "Show Only Omitted" bookmarkp-bmenu-show-only-omitted
    :visible (not (eq bookmarkp-bmenu-filter-function 'bookmarkp-omitted-alist-only))
    :enable bookmarkp-bmenu-omitted-list
    :help "Show only the omitted bookmarks"))
(define-key bookmarkp-bmenu-omit-menu [bookmarkp-unomit-all]
  '(menu-item "Un-Omit All" bookmarkp-unomit-all
    :visible bookmarkp-bmenu-omitted-list :help "Un-omit all omitted bookmarks"))
(define-key bookmarkp-bmenu-omit-menu [bookmarkp-bmenu-unomit-marked]
  '(menu-item "Un-Omit Marked" bookmarkp-bmenu-unomit-marked
    :visible (eq bookmarkp-bmenu-filter-function 'bookmarkp-omitted-alist-only)
    :enable (and bookmarkp-bmenu-omitted-list
             (save-excursion (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
                             (re-search-forward "^>" (point-max) t)))
    :help "Un-omit the marked bookmarks"
    :keys "\\[bookmarkp-bmenu-omit/unomit-marked]"))
(define-key bookmarkp-bmenu-omit-menu [bookmarkp-bmenu-omit-marked]
  '(menu-item "Omit Marked" bookmarkp-bmenu-omit-marked
    :visible (not (eq bookmarkp-bmenu-filter-function 'bookmarkp-omitted-alist-only))
    :enable (and (save-excursion (goto-char (point-min)) (forward-line bookmarkp-bmenu-header-lines)
                                 (re-search-forward "^>" (point-max) t)))
    :help "Omit the marked bookmarks"
    :keys "\\[bookmarkp-bmenu-omit/unomit-marked]"))

(defvar bookmarkp-bmenu-mark-menu (make-sparse-keymap "Mark"))
(define-key bookmarkp-bmenu-menubar-menu [marking] (cons "Mark" bookmarkp-bmenu-mark-menu))

(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-unmark-bookmarks-tagged-not-all]
  '(menu-item "Unmark If Not Tagged with All..." bookmarkp-bmenu-unmark-bookmarks-tagged-not-all
    :help "Unmark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-unmark-bookmarks-tagged-none]
  '(menu-item "Unmark If Tagged with None..." bookmarkp-bmenu-unmark-bookmarks-tagged-none
    :help "Unmark all visible bookmarks that are *not* tagged with *any* tag you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-unmark-bookmarks-tagged-all]
  '(menu-item "Unmark If Tagged with All..." bookmarkp-bmenu-unmark-bookmarks-tagged-all
    :help "Unmark all visible bookmarks that are tagged with *each* tag you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-unmark-bookmarks-tagged-some]
  '(menu-item "Unmark If Tagged with Some..." bookmarkp-bmenu-unmark-bookmarks-tagged-some
    :help "Unmark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-bookmarks-tagged-not-all]
  '(menu-item "Mark If Not Tagged with All..." bookmarkp-bmenu-mark-bookmarks-tagged-not-all
    :help "Mark all visible bookmarks that are *not* tagged with *all* tags you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-bookmarks-tagged-none]
  '(menu-item "Mark If Tagged with None..." bookmarkp-bmenu-mark-bookmarks-tagged-none
    :help "Mark all visible bookmarks that are not tagged with *any* tag you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-bookmarks-tagged-all]
  '(menu-item "Mark If Tagged with All..." bookmarkp-bmenu-mark-bookmarks-tagged-all
    :help "Mark all visible bookmarks that are tagged with *each* tag you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-bookmarks-tagged-some]
  '(menu-item "Mark If Tagged with Some..." bookmarkp-bmenu-mark-bookmarks-tagged-some
    :help "Mark all visible bookmarks that are tagged with *some* tag in a set you specify"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-bookmarks-tagged-regexp]
  '(menu-item "Mark If Tagged Matching Regexp..." bookmarkp-bmenu-mark-bookmarks-tagged-regexp
    :help "Mark bookmarks any of whose tags match a regexp you enter"))
(define-key bookmarkp-bmenu-mark-menu [mark-sep1] '("--"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-w3m-bookmarks]
  '(menu-item "Mark URLs (W3M)" bookmarkp-bmenu-mark-w3m-bookmarks :help "Mark W3M (URL) bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-gnus-bookmarks]
  '(menu-item "Mark Gnus Messages" bookmarkp-bmenu-mark-gnus-bookmarks :help "Mark Gnus bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-man-bookmarks]
  '(menu-item "Mark UNIX Manual Pages" bookmarkp-bmenu-mark-man-bookmarks
    :help "Mark `man' page bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-info-bookmarks]
  '(menu-item "Mark Info Nodes" bookmarkp-bmenu-mark-info-bookmarks :help "Mark Info bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-dired-bookmarks]
  '(menu-item "Mark Dired Buffers" bookmarkp-bmenu-mark-dired-bookmarks :help "Mark Dired bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-desktop-bookmarks]
  '(menu-item "Mark Desktop Buffers" bookmarkp-bmenu-mark-desktop-bookmarks
    :help "Mark desktop bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-region-bookmarks]
  '(menu-item "Mark Regions" bookmarkp-bmenu-mark-region-bookmarks
    :help "Mark bookmarks that record a region"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-non-file-bookmarks]
  '(menu-item "Mark Non-Files (Buffers)" bookmarkp-bmenu-mark-non-file-bookmarks
    :help "Mark non-file bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-file-bookmarks]
  '(menu-item "Mark Files" bookmarkp-bmenu-mark-file-bookmarks :help "Mark file bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-unmark-all]
  '(menu-item "Unmark All" bookmarkp-bmenu-unmark-all
    :help "Remove a mark you specify (> or D) from each bookmark (RET to remove both kinds)"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-mark-all]
  '(menu-item "Mark All" bookmarkp-bmenu-mark-all
    :help "Mark all bookmarks, using mark `>'"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-toggle-marks]
  '(menu-item "Toggle Marked/Unmarked" bookmarkp-bmenu-toggle-marks
    :help "Unmark all marked bookmarks; mark all unmarked bookmarks"))
(define-key bookmarkp-bmenu-mark-menu [bookmarkp-bmenu-regexp-mark]
  '(menu-item "Mark Regexp Matches..." bookmarkp-bmenu-regexp-mark
    :help "Mark bookmarks that match a regexp that you enter"))

(define-key bookmarkp-bmenu-menubar-menu [bookmark-bmenu-execute-deletions]
  '(menu-item "Delete Flagged (D)" bookmark-bmenu-execute-deletions
    :help "Delete the (visible) bookmarks flagged `D'"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-delete-marked]
  '(menu-item "Delete Marked (>)" bookmarkp-bmenu-delete-marked
    :help "Delete all (visible) bookmarks marked `>', after confirmation"))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-query-replace-marked-bookmarks-regexp]
  '(menu-item "Query-Replace Marked..." bookmarkp-bmenu-query-replace-marked-bookmarks-regexp
    :help "`query-replace-regexp' over all files whose bookmarks are marked"))
(when (fboundp 'bookmarkp-bmenu-isearch-marked-bookmarks)
  (define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-isearch-marked-bookmarks-regexp]
    '(menu-item "Regexp-Isearch Marked..." bookmarkp-bmenu-isearch-marked-bookmarks-regexp
      :help "Regexp Isearch the marked bookmark locations, in their current order"))
  (define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-isearch-marked-bookmarks]
    '(menu-item "Isearch Marked..." bookmarkp-bmenu-isearch-marked-bookmarks
      :help "Isearch the marked bookmark locations, in their current order")))
(define-key bookmarkp-bmenu-menubar-menu [bookmarkp-bmenu-search-marked-bookmarks-regexp]
  '(menu-item "Search Marked..." bookmarkp-bmenu-search-marked-bookmarks-regexp
    :help "Regexp-search the files whose bookmarks are marked, in their current order"))
(define-key bookmarkp-bmenu-menubar-menu [bookmark-bmenu-select]
  '(menu-item "Jump to Marked" bookmark-bmenu-select
    :help "Jump to this line's bookmark.  Also visit each bookmark marked with `>'"))


;;; Mouse-3 menu binding.

;;;###autoload
(defvar bookmarkp-bmenu-line-overlay nil)
(define-key bookmark-bmenu-mode-map [mouse-3] 'bookmarkp-bmenu-mouse-3-menu)

;;;###autoload
(defun bookmarkp-bmenu-mouse-3-menu (event)
  "Pop-up menu on `mouse-3' for a bookmark listed in `*Bookmark List*'."
  (interactive "e")
  (let* ((mouse-pos                  (event-start event))
         (inhibit-field-text-motion  t) ; Just in case.
         bol eol
         (bmk-name                   (save-excursion
                                       (set-buffer (window-buffer (posn-window mouse-pos)))
                                       (save-excursion
                                         (goto-char (posn-point mouse-pos))
                                         (save-excursion
                                           (setq bol (progn (beginning-of-line) (point)))
                                           (setq eol (progn (end-of-line) (point))))
                                         (if bookmarkp-bmenu-line-overlay ; Don't recreate.
                                             (move-overlay bookmarkp-bmenu-line-overlay
                                                           bol eol (current-buffer))
                                           (setq bookmarkp-bmenu-line-overlay
                                                 (make-overlay bol eol))
                                           (overlay-put bookmarkp-bmenu-line-overlay 'face 'region))
                                         (bookmark-bmenu-bookmark)))))
    (sit-for 0)
    (let ((menu-choice
           (x-popup-menu
            event
            (list
             "This Bookmark"
             (if bmk-name
                 (list bmk-name
                       (if (member bmk-name bookmarkp-bmenu-marked-bookmarks)
                           '("Unmark" . bookmark-bmenu-unmark)
                         '("Mark" . bookmark-bmenu-mark))
                       (save-excursion
                         (goto-char (posn-point mouse-pos))
                         (beginning-of-line)
                         (if (looking-at "^D")
                             '("Unmark" . bookmark-bmenu-unmark)
                           '("Flag for Deletion" . bookmark-bmenu-delete)))
                       '("Omit" . bookmarkp-bmenu-omit)
                       '("--")          ; ----------------------------------------
                       '("Jump To" . bookmark-bmenu-this-window)
                       '("Jump To in Other Window" . bookmark-bmenu-other-window)
                       '("--")          ; ----------------------------------------
                       '("Add Some Tags..." . bookmarkp-bmenu-add-tags)
                       '("Remove Some Tags..." . bookmarkp-bmenu-remove-tags)
                       '("Remove All Tags..." . bookmarkp-bmenu-remove-all-tags)
                       '("Set Tag Value..." . bookmarkp-bmenu-set-tag-value)
                       '("--")          ; ----------------------------------------
                       '("Show Annotation" . bookmark-bmenu-show-annotation)
                       '("Edit Annotation..." . bookmark-bmenu-edit-annotation)
                       '("Edit Name, File Name..." . bookmarkp-bmenu-edit-bookmark)
                       '("Rename..." . bookmark-bmenu-rename)
                       (and (fboundp 'bookmark-bmenu-relocate)
                            '("Relocate..." . bookmark-bmenu-relocate))
                       '("--")          ; ----------------------------------------
                       '("Describe" . bookmarkp-bmenu-describe-this-bookmark)
                       )
               '("" ("")))))))          ; No menu: not on a bookmark line.
      (when bookmarkp-bmenu-line-overlay (delete-overlay bookmarkp-bmenu-line-overlay))
      (and menu-choice
           (save-excursion
             (goto-char (posn-point mouse-pos))
             (call-interactively menu-choice))))))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+.el ends here

