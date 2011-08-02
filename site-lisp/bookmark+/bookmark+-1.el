;;; bookmark+-1.el - First part of package Bookmark+.
;; 
;; Filename: bookmark+-1.el
;; Description: First part of package Bookmark+.
;; Author: Drew Adams, Thierry Volpiatto
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2011, Drew Adams, all rights reserved.
;; Copyright (C) 2009, Thierry Volpiatto, all rights reserved.
;; Created: Mon Jul 12 13:43:55 2010 (-0700)
;; Last-Updated: Sun May  8 11:47:14 2011 (-0700)
;;           By: dradams
;;     Update #: 2098
;; URL: http://www.emacswiki.org/cgi-bin/wiki/bookmark+-1.el
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search, info, url, w3m, gnus
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   `bookmark', `bookmark+-1', `bookmark+-mac', `dired',
;;   `dired-aux', `dired-x', `ffap', `pp'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary: 
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other (non-bmenu) required code (this file)
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
;;  (@> "User Options (Customizable)")
;;  (@> "Internal Variables")
;;  (@> "Compatibility Code for Older Emacs Versions")
;;  (@> "Core Replacements (`bookmark-*' except `bookmark-bmenu-*')")
;;  (@> "Bookmark+ Functions (`bmkp-*')")
;;    (@> "Search-and-Replace Locations of Marked Bookmarks")
;;    (@> "Tags")
;;    (@> "Bookmark Predicates")
;;    (@> "Filter Functions")
;;    (@> "General Utility Functions")
;;    (@> "Bookmark Entry Access Functions")
;;    (@> "Sorting - General Functions")
;;    (@> "Sorting - Commands")
;;    (@> "Sorting - General Predicates")
;;    (@> "Sorting - File-Name Predicates")
;;    (@> "Indirect Bookmarking Functions")
;;    (@> "Other Bookmark+ Functions (`bmkp-*')")
;;  (@> "Keymaps")
 
;;(@* "Things Defined Here")
;;
;;  Things Defined Here
;;  -------------------
;;
;;  Commands defined here:
;;
;;    `bmkp-add-tags', `bmkp-all-tags-jump',
;;    `bmkp-all-tags-jump-other-window', `bmkp-all-tags-regexp-jump',
;;    `bmkp-all-tags-regexp-jump-other-window',
;;    `bmkp-autofile-add-tags', `bmkp-autofile-jump',
;;    `bmkp-autofile-jump-other-window', `bmkp-autofile-remove-tags',
;;    `bmkp-autofile-set', `bmkp-autonamed-jump',
;;    `bmkp-autonamed-jump-other-window',
;;    `bmkp-autonamed-this-buffer-jump',
;;    `bmkp-autonamed-this-buffer-jump-other-window',
;;    `bmkp-bookmark-a-file' `bmkp-bookmark-file-jump',
;;    `bmkp-bookmark-list-jump',
;;    `bmkp-choose-navlist-from-bookmark-list',
;;    `bmkp-choose-navlist-of-type', `bmkp-compilation-target-set',
;;    `bmkp-compilation-target-set-all', `bmkp-copy-tags',
;;    `bmkp-crosshairs-highlight', `bmkp-cycle',
;;    `bmkp-cycle-autonamed', `bmkp-cycle-autonamed-other-window',
;;    `bmkp-cycle-bookmark-list',
;;    `bmkp-cycle-bookmark-list-other-window', `bmkp-cycle-desktop',
;;    `bmkp-cycle-dired', `bmkp-cycle-dired-other-window',
;;    `bmkp-cycle-file', `bmkp-cycle-file-other-window',
;;    `bmkp-cycle-gnus', `bmkp-cycle-gnus-other-window',
;;    `bmkp-cycle-info', `bmkp-cycle-info-other-window',
;;    `bmkp-cycle-lighted', `bmkp-cycle-lighted-other-window',
;;    `bmkp-cycle-local-file', `bmkp-cycle-local-file-other-window',
;;    `bmkp-cycle-man', `bmkp-cycle-man-other-window',
;;    `bmkp-cycle-non-file', `bmkp-cycle-non-file-other-window',
;;    `bmkp-cycle-other-window', `bmkp-cycle-remote-file',
;;    `bmkp-cycle-remote-file-other-window',
;;    `bmkp-cycle-specific-buffers',
;;    `bmkp-cycle-specific-buffers-other-window',
;;    `bmkp-cycle-specific-files',
;;    `bmkp-cycle-specific-files-other-window',
;;    `bmkp-cycle-this-buffer', `bmkp-cycle-this-buffer-other-window',
;;    `bmkp-cycle-variable-list', `bmkp-cycle-url',
;;    `bmkp-cycle-url-other-window',
;;    `bmkp-delete-all-autonamed-for-this-buffer',
;;    `bmkp-delete-bookmarks', `bmkp-describe-bookmark',
;;    `bmkp-describe-bookmark-internals', `bmkp-desktop-change-dir',
;;    `bmkp-desktop-delete', `bmkp-desktop-jump', `bmkp-desktop-read',
;;    `bmkp-dired-jump', `bmkp-dired-jump-other-window',
;;    `bmkp-dired-this-dir-jump',
;;    `bmkp-dired-this-dir-jump-other-window', `bmkp-edit-bookmark',
;;    `bmkp-edit-bookmark-record', `bmkp-edit-bookmark-record-mode',
;;    `bmkp-edit-bookmark-record-send', `bmkp-edit-tags',
;;    `bmkp-edit-tags-send', `bmkp-empty-file',
;;    `bmkp-file-target-set', `bmkp-file-all-tags-jump',
;;    `bmkp-file-all-tags-jump-other-window',
;;    `bmkp-file-all-tags-regexp-jump',
;;    `bmkp-file-all-tags-regexp-jump-other-window', `bmkp-file-jump',
;;    `bmkp-file-jump-other-window', `bmkp-file-some-tags-jump',
;;    `bmkp-file-some-tags-jump-other-window',
;;    `bmkp-file-some-tags-regexp-jump',
;;    `bmkp-file-some-tags-regexp-jump-other-window',
;;    `bmkp-file-this-dir-all-tags-jump',
;;    `bmkp-file-this-dir-all-tags-jump-other-window',
;;    `bmkp-file-this-dir-all-tags-regexp-jump',
;;    `bmkp-file-this-dir-all-tags-regexp-jump-other-window',
;;    `bmkp-file-this-dir-jump',
;;    `bmkp-file-this-dir-jump-other-window',
;;    `bmkp-file-this-dir-some-tags-jump',
;;    `bmkp-file-this-dir-some-tags-jump-other-window',
;;    `bmkp-file-this-dir-some-tags-regexp-jump',
;;    `bmkp-file-this-dir-some-tags-regexp-jump-other-window',
;;    `bmkp-find-file', `bmkp-find-file-other-window',
;;    `bmkp-find-file-all-tags',
;;    `bmkp-find-file-all-tags-other-window',
;;    `bmkp-find-file-all-tags-regexp',
;;    `bmkp-find-file-all-tags-regexp-other-window',
;;    `bmkp-find-file-some-tags',
;;    `bmkp-find-file-some-tags-other-window',
;;    `bmkp-find-file-some-tags-regexp',
;;    `bmkp-find-file-some-tags-regexp-other-window',
;;    `bmkp-gnus-jump', `bmkp-gnus-jump-other-window',
;;    `bmkp-info-jump', `bmkp-info-jump-other-window',
;;    `bmkp-jump-in-navlist', `bmkp-jump-in-navlist-other-window',
;;    `bmkp-jump-to-type', `bmkp-jump-to-type-other-window',
;;    `bmkp-list-all-tags', `bmkp-list-defuns-in-commands-file',
;;    `bmkp-local-file-jump', `bmkp-local-file-jump-other-window',
;;    `bmkp-make-function-bookmark', `bmkp-man-jump',
;;    `bmkp-man-jump-other-window', `bmkp-menu-jump-other-window'
;;    (Emacs 20, 21), `bmkp-navlist-bmenu-list',
;;    `bmkp-next-autonamed-bookmark',
;;    `bmkp-next-autonamed-bookmark-repeat', `bmkp-next-bookmark',
;;    `bmkp-next-bookmark-list-bookmark',
;;    `bmkp-next-bookmark-list-bookmark-repeat',
;;    `bmkp-next-bookmark-repeat', `bmkp-next-bookmark-this-buffer',
;;    `bmkp-next-bookmark-this-buffer-repeat',
;;    `bmkp-next-bookmark-w32', `bmkp-next-bookmark-w32-repeat',
;;    `bmkp-next-desktop-bookmark',
;;    `bmkp-next-desktop-bookmark-repeat', `bmkp-next-dired-bookmark',
;;    `bmkp-next-dired-bookmark-repeat', `bmkp-next-file-bookmark',
;;    `bmkp-next-file-bookmark-repeat', `bmkp-next-gnus-bookmark',
;;    `bmkp-next-gnus-bookmark-repeat', `bmkp-next-info-bookmark',
;;    `bmkp-next-info-bookmark-repeat', `bmkp-next-lighted-bookmark',
;;    `bmkp-next-lighted-bookmark-repeat',
;;    `bmkp-next-local-file-bookmark',
;;    `bmkp-next-local-file-bookmark-repeat',
;;    `bmkp-next-man-bookmark', `bmkp-next-man-bookmark-repeat',
;;    `bmkp-next-non-file-bookmark',
;;    `bmkp-next-non-file-bookmark-repeat',
;;    `bmkp-next-remote-file-bookmark',
;;    `bmkp-next-remote-file-bookmark-repeat',
;;    `bmkp-next-specific-buffers-bookmark',
;;    `bmkp-next-specific-buffers-bookmark-repeat',
;;    `bmkp-next-specific-files-bookmark',
;;    `bmkp-next-specific-files-bookmark-repeat',
;;    `bmkp-next-variable-list-bookmark',
;;    `bmkp-next-variable-list-bookmark-repeat',
;;    `bmkp-next-url-bookmark', `bmkp-next-url-bookmark-repeat',
;;    `bmkp-non-file-jump', `bmkp-non-file-jump-other-window',
;;    `bmkp-occur-create-autonamed-bookmarks',
;;    `bmkp-occur-target-set', `bmkp-occur-target-set-all',
;;    `bmkp-paste-add-tags', `bmkp-paste-replace-tags',
;;    `bmkp-previous-bookmark', `bmkp-previous-bookmark-repeat',
;;    `bmkp-previous-bookmark-this-buffer',
;;    `bmkp-previous-bookmark-this-buffer-repeat',
;;    `bmkp-previous-bookmark-w32',
;;    `bmkp-previous-bookmark-w32-repeat',
;;    `bmkp-purge-notags-autofiles', `bmkp-read-bookmark-for-type',
;;    `bmkp-region-jump', `bmkp-region-jump-other-window',
;;    `bmkp-remote-file-jump', `bmkp-remote-file-jump-other-window',
;;    `bmkp-remove-all-tags', `bmkp-remove-tags',
;;    `bmkp-remove-tags-from-all', `bmkp-rename-tag',
;;    `bmkp-save-menu-list-state', `bmkp-send-bug-report',
;;    `bmkp-set-autonamed-bookmark',
;;    `bmkp-set-autonamed-bookmark-at-line',
;;    `bmkp-set-autonamed-regexp-buffer',
;;    `bmkp-set-autonamed-regexp-region',
;;    `bmkp-set-bookmark-file-bookmark', `bmkp-set-desktop-bookmark',
;;    `bmkp-set-restrictions-bookmark', `bmkp-set-tag-value',
;;    `bmkp-set-tag-value-for-navlist',
;;    `bmkp-set-variable-list-bookmark', `bmkp-some-tags-jump',
;;    `bmkp-some-tags-jump-other-window',
;;    `bmkp-some-tags-regexp-jump',
;;    `bmkp-some-tags-regexp-jump-other-window',
;;    `bmkp-specific-buffers-jump',
;;    `bmkp-specific-buffers-jump-other-window',
;;    `bmkp-specific-files-jump',
;;    `bmkp-specific-files-jump-other-window',
;;    `bmkp-switch-bookmark-file',
;;    `bmkp-switch-to-last-bookmark-file', `bmkp-tag-a-file',
;;    `bmkp-this-buffer-bmenu-list', `bmkp-this-buffer-jump',
;;    `bmkp-this-buffer-jump-other-window',
;;    `bmkp-toggle-autonamed-bookmark-set/delete',
;;    `bmkp-toggle-bookmark-set-refreshes',
;;    `bmkp-toggle-saving-bookmark-file',
;;    `bmkp-toggle-saving-menu-list-state',
;;    `bmkp-toggle-bookmark-set-refreshes', `bmkp-unomit-all',
;;    `bmkp-untag-a-file', `bmkp-url-target-set', `bmkp-url-jump',
;;    `bmkp-url-jump-other-window', `bmkp-use-bookmark-file-create',
;;    `bmkp-variable-list-jump', `bmkp-version', `bmkp-w3m-jump',
;;    `bmkp-w3m-jump-other-window', `old-bookmark-insert',
;;    `old-bookmark-relocate'.
;;
;;  User options defined here:
;;
;;    `bmkp-autoname-bookmark-function', `bmkp-autoname-format',
;;    `bmkp-bookmark-name-length-max', `bmkp-crosshairs-flag',
;;    `bmkp-default-bookmark-name',
;;    `bmkp-default-handler-associations',
;;    `bmkp-desktop-no-save-vars', `bmkp-handle-region-function',
;;    `bmkp-incremental-filter-delay', `bmkp-menu-popup-max-length',
;;    `bmkp-other-window-pop-to-flag', `bmkp-prompt-for-tags-flag',
;;    `bmkp-region-search-size', `bmkp-save-new-location-flag',
;;    `bmkp-sequence-jump-display-function',
;;    `bmkp-show-end-of-region', `bmkp-sort-comparer',
;;    `bmkp-su-or-sudo-regexp',
;;    `bmkp-this-buffer-cycle-sort-comparer', `bmkp-use-region',
;;    `bmkp-w3m-allow-multi-tabs'.
;;
;;  Non-interactive functions defined here:
;;
;;    `bmkext-jump-gnus', `bmkext-jump-man', `bmkext-jump-w3m',
;;    `bmkext-jump-woman', `bmkp-all-exif-data',
;;    `bmkp-all-tags-alist-only', `bmkp-all-tags-regexp-alist-only',
;;    `bmkp-alpha-cp', `bmkp-alpha-p', `bmkp-annotated-alist-only',
;;    `bmkp-autofile-alist-only', `bmkp-autofile-bookmark-p',
;;    `bmkp-autoname-bookmark', `bmkp-autonamed-alist-only',
;;    `bmkp-autonamed-bookmark-for-buffer-p',
;;    `bmkp-autonamed-bookmark-p',
;;    `bmkp-autonamed-this-buffer-alist-only',
;;    `bmkp-bookmark-creation-cp', `bmkp-bookmark-description',
;;    `bmkp-bookmark-last-access-cp', `bmkp-bookmark-file-alist-only',
;;    `bmkp-bookmark-list-alist-only',
;;    `bmkp-bookmark-file-bookmark-p',
;;    `bmkp-bookmark-image-bookmark-p',
;;    `bmkp-bookmark-list-bookmark-p', `bmkp-bookmark-name-member',
;;    `bmkp-bookmark-type', `bmkp-buffer-last-access-cp',
;;    `bmkp-buffer-names', `bmkp-compilation-file+line-at',
;;    `bmkp-completing-read-1', `bmkp-completing-read-buffer-name',
;;    `bmkp-completing-read-file-name', `bmkp-completing-read-lax',
;;    `bmkp-cp-not', `bmkp-create-variable-list-bookmark',
;;    `bmkp-current-bookmark-list-state', `bmkp-current-sort-order',
;;    `bmkp-cycle-1', `bmkp-default-bookmark-name',
;;    `bmkp-default-handler-for-file', `bmkp-default-handler-user',
;;    `bmkp-delete-autonamed-no-confirm',
;;    `bmkp-delete-autonamed-this-buffer-no-confirm',
;;    `bmkp-delete-bookmark-name-from-list',
;;    `bmkp-desktop-alist-only', `bmkp-desktop-bookmark-p',
;;    `bmkp-desktop-kill', `bmkp-dired-alist-only',
;;    `bmkp-dired-bookmark-p', `bmkp-dired-subdirs',
;;    `bmkp-dired-this-dir-alist-only',
;;    `bmkp-dired-this-dir-bookmark-p', `bmkp-edit-tags-mode',
;;    `bmkp-end-position-post-context',
;;    `bmkp-end-position-pre-context', `bmkp-every', `bmkp-face-prop',
;;    `bmkp-file-alist-only', `bmkp-file-all-tags-alist-only',
;;    `bmkp-file-all-tags-regexp-alist-only', `bmkp-file-alpha-cp',
;;    `bmkp-file-attribute-0-cp', `bmkp-file-attribute-1-cp',
;;    `bmkp-file-attribute-2-cp', `bmkp-file-attribute-3-cp',
;;    `bmkp-file-attribute-4-cp', `bmkp-file-attribute-5-cp',
;;    `bmkp-file-attribute-6-cp', `bmkp-file-attribute-7-cp',
;;    `bmkp-file-attribute-8-cp', `bmkp-file-attribute-9-cp',
;;    `bmkp-file-attribute-10-cp', `bmkp-file-attribute-11-cp',
;;    `bmkp-file-bookmark-p', `bmkp-file-names', `bmkp-file-remote-p',
;;    `bmkp-file-some-tags-alist-only',
;;    `bmkp-file-some-tags-regexp-alist-only',
;;    `bmkp-file-this-dir-alist-only',
;;    `bmkp-file-this-dir-all-tags-alist-only',
;;    `bmkp-file-this-dir-all-tags-regexp-alist-only',
;;    `bmkp-file-this-dir-bookmark-p',
;;    `bmkp-file-this-dir-some-tags-alist-only',
;;    `bmkp-file-this-dir-some-tags-regexp-alist-only',
;;    `bmkp-float-time', `bmkp-full-tag', `bmkp-function-bookmark-p',
;;    `bmkp-get-autofile-bookmark', `bmkp-get-buffer-name',
;;    `bmkp-get-end-position', `bmkp-get-tag-value', `bmkp-get-tags',
;;    `bmkp-get-visit-time', `bmkp-get-visits-count',
;;    `bmkp-gnus-alist-only', `bmkp-gnus-bookmark-p', `bmkp-gnus-cp',
;;    `bmkp-goto-position', `bmkp-handle-region-default',
;;    `bmkp-handler-cp', `bmkp-has-tag-p', `bmkp-info-alist-only',
;;    `bmkp-info-bookmark-p', `bmkp-info-cp', `bmkp-isearch-bookmarks'
;;    (Emacs 23+), `bmkp-isearch-bookmarks-regexp' (Emacs 23+),
;;    `bmkp-isearch-next-bookmark-buffer' (Emacs 23+), `bmkp-jump-1',
;;    `bmkp-jump-bookmark-file', `bmkp-jump-bookmark-list',
;;    `bmkp-jump-desktop', `bmkp-jump-dired', `bmkp-jump-function',
;;    `bmkp-jump-gnus', `bmkp-jump-man', `bmkp-jump-sequence',
;;    `bmkp-jump-url-browse', `bmkp-jump-variable-list',
;;    `bmkp-jump-w3m', `bmkp-jump-w3m-new-session',
;;    `bmkp-jump-w3m-only-one-tab', `bmkp-jump-woman',
;;    `bmkp-last-specific-buffer-alist-only',
;;    `bmkp-last-specific-buffer-p',
;;    `bmkp-last-specific-file-alist-only',
;;    `bmkp-last-specific-file-p', `bmkp-line-number-at-pos',
;;    `bmkp-list-position', `bmkp-local-directory-bookmark-p',
;;    `bmkp-local-file-accessed-more-recently-cp',
;;    `bmkp-local-file-alist-only', `bmkp-local-file-bookmark-p',
;;    `bmkp-local-file-size-cp', `bmkp-local-file-type-cp',
;;    `bmkp-local-file-updated-more-recently-cp',
;;    `bmkp-make-bookmark-file-record',
;;    `bmkp-make-bookmark-list-record', `bmkp-make-desktop-record',
;;    `bmkp-make-dired-record', `bmkp-make-gnus-record',
;;    `bmkp-make-man-record', `bmkp-make-plain-predicate',
;;    `bmkp-make-record-for-target-file',
;;    `bmkp-make-url-browse-record', `bmkp-make-variable-list-record',
;;    `bmkp-make-w3m-record', `bmkp-make-woman-record' (Emacs 21+),
;;    `bmkp-man-alist-only', `bmkp-man-bookmark-p',
;;    `bmkp-marked-bookmark-p', `bmkp-marked-bookmarks-only',
;;    `bmkp-marked-cp', `bmkp-maybe-save-bookmarks',
;;    `bmkp-msg-about-sort-order', `bmkp-multi-sort',
;;    `bmkp-names-same-bookmark-p', `bmkp-non-autonamed-alist-only',
;;    `bmkp-non-file-alist-only', `bmkp-non-file-bookmark-p',
;;    `bmkp-omitted-alist-only', `bmkp-position-after-whitespace',
;;    `bmkp-position-before-whitespace', `bmkp-position-cp',
;;    `bmkp-position-post-context',
;;    `bmkp-position-post-context-region',
;;    `bmkp-position-pre-context', `bmkp-position-pre-context-region',
;;    `bmkp-printable-p', `bmkp-printable-vars+vals',
;;    `bmkp-read-bookmark-file-name', `bmkp-read-tag-completing',
;;    `bmkp-read-tags', `bmkp-read-tags-completing',
;;    `bmkp-read-variable', `bmkp-read-variables-completing',
;;    `bmkp-record-visit', `bmkp-refresh-latest-bookmark-list',
;;    `bmkp-refresh-menu-list',
;;    `bmkp-regexp-filtered-annotation-alist-only',
;;    `bmkp-regexp-filtered-bookmark-name-alist-only',
;;    `bmkp-regexp-filtered-file-name-alist-only',
;;    `bmkp-regexp-filtered-tags-alist-only',
;;    `bmkp-region-alist-only', `bmkp-region-bookmark-p',
;;    `bmkp-remote-file-alist-only', `bmkp-remote-file-bookmark-p',
;;    `bmkp-remove-dups', `bmkp-remove-if', `bmkp-remove-if-not',
;;    `bmkp-remove-omitted', `bmkp-repeat-command',
;;    `bmkp-replace-existing-bookmark', `bmkp-root-or-sudo-logged-p',
;;    `bmkp-same-creation-time-p', `bmkp-same-file-p',
;;    `bmkp-save-new-region-location',
;;    `bmkp-select-buffer-other-window', `bmkp-sequence-bookmark-p',
;;    `bmkp-set-tag-value-for-bookmarks', `bmkp-set-union',
;;    `bmkp-some', `bmkp-some-marked-p', `bmkp-some-tags-alist-only',
;;    `bmkp-some-tags-regexp-alist-only', `bmkp-some-unmarked-p'
;;    `bmkp-sort-omit', `bmkp-sound-jump',
;;    `bmkp-specific-buffers-alist-only',
;;    `bmkp-specific-files-alist-only', `bmkp-tag-name',
;;    `bmkp-tags-list', `bmkp-this-buffer-alist-only',
;;    `bmkp-this-buffer-p', `bmkp-this-file-alist-only',
;;    `bmkp-this-file-p', `bmkp-unmarked-bookmarks-only',
;;    `bmkp-upcase', `bmkp-update-autonamed-bookmark',
;;    `bmkp-url-alist-only', `bmkp-url-bookmark-p',
;;    `bmkp-url-browse-alist-only', `bmkp-url-browse-bookmark-p',
;;    `bmkp-url-cp', `bmkp-variable-list-alist-only',
;;    `bmkp-variable-list-bookmark-p', `bmkp-visited-more-cp',
;;    `bmkp-w3m-alist-only', `bmkp-w3m-bookmark-p', `bmkp-w3m-cp',
;;    `bmkp-w3m-set-new-buffer-name'.
;;
;;  Internal variables defined here:
;;
;;    `bmkp-after-set-hook', `bmkp-bookmark-file-history',
;;    `bmkp-bookmark-list-history', `bmkp-current-bookmark-file',
;;    `bmkp-current-nav-bookmark', `bmkp-desktop-history',
;;    `bmkp-dired-history', `bmkp-edit-bookmark-record-mode-map',
;;    `bmkp-edit-tags-mode-map', `bmkp-file-history',
;;    `bmkp-gnus-history', `bmkp-info-history',
;;    `bmkp-isearch-bookmarks' (Emacs 23+),
;;    `bmkp-jump-display-function', `bmkp-jump-other-window-map',
;;    `bmkp-last-bmenu-state-file', `bmkp-last-bookmark-file',
;;    `bmkp-last-save-flag-value', `bmkp-last-specific-buffer',
;;    `bmkp-last-specific-file', `bmkp-latest-bookmark-alist',
;;    `bmkp-local-file-history', `bmkp-man-history', `bmkp-nav-alist',
;;    `bmkp-non-file-filename', `bmkp-non-file-history',
;;    `bmkp-region-history', `bmkp-remote-file-history',
;;    `bmkp-return-buffer', `bmkp-reverse-multi-sort-p',
;;    `bmkp-reverse-sort-p', `bmkp-sorted-alist',
;;    `bmkp-specific-buffers-history', `bmkp-specific-files-history',
;;    `bmkp-tag-history', `bmkp-tags-alist', `bmkp-types-alist',
;;    `bmkp-url-history', `bmkp-use-w32-browser-p',
;;    `bmkp-variable-list-history', `bmkp-version-number',
;;    `bmkp-w3m-history'.
;;
;;
;;  ***** NOTE: The following commands defined in `bookmark.el'
;;              have been REDEFINED HERE:
;;
;;    `bookmark-delete', `bookmark-edit-annotation',
;;    `bookmark-edit-annotation-mode', `bookmark-insert',
;;    `bookmark-insert-location', `bookmark-jump',
;;    `bookmark-jump-other-window', `bookmark-load',
;;    `bookmark-relocate', `bookmark-rename', `bookmark-save',
;;    `bookmark-send-edited-annotation', `bookmark-set',
;;    `bookmark-yank-word'.
;;
;;
;;  ***** NOTE: The following non-interactive functions defined in
;;              `bookmark.el' have been REDEFINED HERE:
;;
;;    `bookmark--jump-via', `bookmark-all-names',
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

;;;;;;;;;;;;;;;;;;;;;;;

(unless (fboundp 'file-remote-p) (require 'ffap)) ;; ffap-file-remote-p
(eval-when-compile (require 'gnus)) ;; mail-header-id (really in `nnheader.el')
(eval-when-compile (require 'gnus-sum)) ;; gnus-summary-article-header
(eval-when-compile (require 'cl)) ;; case, multiple-value-bind

(require 'bookmark)
;; bookmark-alist, bookmark-alist-from-buffer,
;; bookmark-alist-modification-count, bookmark-annotation-name,
;; bookmark-automatically-show-annotations, bookmark-bmenu-bookmark,
;; bookmark-bmenu-surreptitiously-rebuild-list,
;; bookmark-bmenu-toggle-filenames, bookmark-buffer-file-name,
;; bookmark-buffer-name, bookmark-completion-ignore-case,
;; bookmark-current-bookmark, bookmark-default-file,
;; bookmark-edit-annotation, bookmark-get-annotation,
;; bookmark-get-bookmark, bookmark-get-bookmark-record,
;; bookmark-get-filename, bookmark-get-front-context-string,
;; bookmark-get-handler, bookmark-get-position,
;; bookmark-get-rear-context-string, bookmark-import-new-list,
;; bookmark-insert-file-format-version-stamp, bookmark-kill-line,
;; bookmark-make-record, bookmark-maybe-historicize-string,
;; bookmark-maybe-load-default-file, bookmark-maybe-message,
;; bookmark-maybe-upgrade-file-format, bookmark-menu-popup-paned-menu,
;; bookmark-name-from-full-record, bookmark-name-from-record,
;; bookmark-popup-menu-and-apply-function, bookmark-prop-get,
;; bookmarks-already-loaded, bookmark-save-flag, bookmark-search-size,
;; bookmark-set-annotation, bookmark-set-filename, bookmark-set-name,
;; bookmark-set-position, bookmark-store, bookmark-time-to-save-p,
;; bookmark-use-annotations, bookmark-version-control,
;; bookmark-yank-point

;;; Fix incompatibility introduced by gratuitous Emacs name change.
(cond ((and (fboundp 'bookmark-name-from-record) (not (fboundp 'bookmark-name-from-full-record)))
       (defalias 'bookmark-name-from-full-record 'bookmark-name-from-record))
      ((and (fboundp 'bookmark-name-from-full-record) (not (fboundp 'bookmark-name-from-record)))
       (defalias 'bookmark-name-from-record 'bookmark-name-from-full-record)))

(require 'bookmark+-mac)
;; bmkp-define-cycle-command, bmkp-define-file-sort-predicate, bmkp-menu-bar-make-toggle,
;; bmkp-replace-regexp-in-string

(eval-when-compile (require 'bookmark+-bmu))
;; bmkp-bmenu-before-hide-marked-alist,
;; bmkp-bmenu-before-hide-unmarked-alist, bmkp-bmenu-commands-file,
;; bmkp-bmenu-filter-function, bmkp-bmenu-filter-pattern,
;; bmkp-bmenu-first-time-p, bmkp-bmenu-goto-bookmark-named,
;; bmkp-bmenu-marked-bookmarks, bmkp-bmenu-omitted-bookmarks, bmkp-bmenu-refresh-menu-list,
;; bmkp-bmenu-show-all, bmkp-bmenu-state-file, bmkp-bmenu-title,
;; bmkp-maybe-unpropertize-bookmark-names, bmkp-sort-orders-alist

;; (eval-when-compile (require 'bookmark+-lit nil t))
;; bmkp-light-bookmark, bmkp-light-bookmarks, bmkp-light-this-buffer


;; For the redefinition of `bookmark-get-bookmark' in Emacs < 23.
(provide 'bookmark+-1)                  ; Ensure this library is loaded before we compile it.
(require 'bookmark+-1)                  ; So be sure to put this library in your `load-path' before
                                        ; trying to byte-compile it.

;;;;;;;;;;;;;;;;;;;;;;;

;; Quiet the byte-compiler

(defvar bmkp-auto-light-when-set)       ; Defined in `bookmark+-lit.el'.
(defvar bmkp-auto-light-when-jump)      ; Defined in `bookmark+-lit.el'.
(defvar bmkp-light-priorities)          ; Defined in `bookmark+-lit.el'.
(defvar bookmark-current-point)         ; Defined in `bookmark.el', but not in Emacs 23+.
(defvar bookmark-edit-annotation-text-func) ; Defined in `bookmark.el'.
(defvar bookmark-read-annotation-text-func) ; Defined in `bookmark.el', but not in Emacs 23+.
(defvar bookmark-make-record-function)  ; Defined in `bookmark.el'.
(defvar desktop-buffer-args-list)       ; Defined in `desktop.el'.
(defvar desktop-delay-hook)             ; Defined in `desktop.el'.
(defvar desktop-dirname)                ; Defined in `desktop.el'.
(defvar desktop-file-modtime)           ; Defined in `desktop.el'.
(defvar desktop-globals-to-save)        ; Defined in `desktop.el'.
(defvar desktop-save-mode)              ; Defined in `desktop.el'.
(defvar desktop-save)                   ; Defined in `desktop.el'.
(defvar dired-actual-switches)          ; Defined in `dired.el'.
(defvar dired-buffers)                  ; Defined in `dired.el'.
(defvar dired-directory)                ; Defined in `dired.el'.
(defvar dired-guess-shell-case-fold-search) ; Defined in `dired-x.el'.
(defvar dired-subdir-alist)             ; Defined in `dired.el'.
(defvar gnus-article-current)           ; Defined in `gnus-sum.el'.
(defvar Info-current-node)              ; Defined in `info.el'.
(defvar Info-current-file)              ; Defined in `info.el'.
(defvar Man-arguments)                  ; Defined in `man.el'.
(defvar read-file-name-completion-ignore-case) ; Emacs 23+.
(defvar last-repeatable-command)        ; Defined in `repeat.el'.
(defvar w3m-current-title)              ; Defined in `w3m.el'.
(defvar w3m-current-url)                ; Defined in `w3m.el'.
(defvar w3m-mode-map)                   ; Defined in `w3m.el'.
(defvar wide-n-restrictions)            ; Defined in `wide-n.el'.
(defvar woman-last-file-name)           ; Defined in `woman.el'.
 
;;(@* "User Options (Customizable)")
;;; User Options (Customizable) --------------------------------------

;;;###autoload
(defcustom bmkp-autoname-bookmark-function 'bmkp-autoname-bookmark
  "*Function to automatically name a bookmark at point (cursor position)."
  :type 'function :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-autoname-format (if (> emacs-major-version 21) "^[0-9]\\{9\\} %s" "^[0-9]+ %s")
  "*Format string to match an autonamed bookmark name.
It must have a single `%s' that to accept the buffer name."
  :type 'string :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-bookmark-name-length-max 70
  "*Max number of chars for default name for a bookmark with a region."
  :type 'integer :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-crosshairs-flag (> emacs-major-version 21)
  "*Non-nil means highlight with crosshairs when you visit a bookmark.
The highlighting is temporary - until your next action.
You need library `crosshairs.el' for this feature, and you need Emacs
22 or later.

If you use this option in Lisp code, you will want to add/remove
`bmkp-crosshairs-highlight' to/from `bookmark-after-jump-hook'."
  :set (lambda (sym new-val)
         (custom-set-default sym new-val)
         (if (and bmkp-crosshairs-flag (> emacs-major-version 21)
                  (condition-case nil (require 'crosshairs nil t) (error nil)))
             (add-hook 'bookmark-after-jump-hook 'bmkp-crosshairs-highlight)
           (remove-hook 'bookmark-after-jump-hook 'bmkp-crosshairs-highlight)))         
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-default-bookmark-name 'highlighted
  "*Default bookmark name preference.
In `*Bookmark List*' use the name of the current line's bookmark.
Otherwise, if `bookmark+-lit.el' is not loaded then use the name of
 the last-used bookmark in the current file.

Otherwise, use this option to determine the default, by preferring one
of the following, if available:

* a highlighted bookmark at point
* the last-used bookmark in the current file"
  :type '(choice
          (const :tag "Highlighted bookmark at point"    highlighted)
          (const :tag "Last used bookmark in same file"  last-used))
  :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-default-handler-associations
  (and (require 'dired-x)               ; It in turn requires `dired-aux.el'
       (let ((assns  ()))
         (dolist (shell-assn  dired-guess-shell-alist-user)
           (push (cons (car shell-assn)
                       `(lambda (bmk) 
                         (dired-run-shell-command
                          (dired-shell-stuff-it ,(cadr shell-assn) (list (bookmark-get-filename bmk))
                           nil nil))))
                 assns))
         assns))
  "*File associations for bookmark handlers used for indirect bookmarks.
Each element of the alist is (REGEXP . COMMAND).
REGEXP matches a file name.
COMMAND is a sexp that evaluates to either a shell command (a string)
 or an Emacs function (a symbol or a lambda form).

Example value:

 ((\"\\.pdf$\" . \"AcroRd32.exe\") ; Adobe Acrobat Reader
  (\"\\.ps$\" . \"gsview32.exe\")) ; Ghostview (PostScript viewer)

When you change this option using Customize, if you want to use a
literal string as COMMAND then you must double-quote the text:
\"...\".  (But do not use double-quotes for the REGEXP.)  If you want
to use a symbol as COMMAND, then single-quote it - e.g. 'foo.

This option is used by `bmkp-default-handler-user'.  If an association
for a given file name is not found using this option, then
`bmkp-default-handler-for-file' looks for an association in
`dired-guess-shell-alist-user', `dired-guess-shell-alist-default', and
in mailcap entries (Emacs 23+), in that order."
  :type '(alist :key-type
          regexp :value-type
          (sexp :tag "Shell command (string) or Emacs function (symbol or lambda form)"))
  :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-desktop-no-save-vars '(search-ring regexp-search-ring kill-ring)
  "*List of variables not to save when creating a desktop bookmark.
They are removed from `desktop-globals-to-save' for the duration of
the save (only)."
  :type '(repeat (variable :tag "Variable")) :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-handle-region-function 'bmkp-handle-region-default
  "*Function to handle a bookmarked region."
  :type 'function :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-incremental-filter-delay 0.6
  "*Seconds to wait before updating display when filtering bookmarks."
  :type 'number :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-menu-popup-max-length 20
  "*Max number of bookmarks for `bookmark-completing-read' to use a menu.
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
(defcustom bmkp-other-window-pop-to-flag t
  "*Non-nil means other-window bookmark jumping uses `pop-to-buffer'.
Use nil if you want the vanilla Emacs behavior, which uses
`switch-to-buffer-other-window'.  That creates a new window even if
there is already another window showing the buffer."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-prompt-for-tags-flag nil
  "*Non-nil means `bookmark-set' prompts for tags (when called interactively)."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-region-search-size 40
  "*Same as `bookmark-search-size', but specialized for bookmark regions."
  :type 'integer :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-save-new-location-flag t
  "*Non-nil means save automatically relocated bookmarks.
If nil, then the new bookmark location is visited, but it is not saved
as part of the bookmark definition."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-sequence-jump-display-function 'pop-to-buffer
  "*Function used to display the bookmarks in a bookmark sequence."
  :type 'function :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-show-end-of-region t
  "*Show end of region with `exchange-point-and-mark' when activating a region.
If nil show only beginning of region."
  :type 'boolean :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-sort-comparer '((bmkp-info-cp bmkp-gnus-cp bmkp-url-cp bmkp-local-file-type-cp)
                                bmkp-alpha-p) ; This corresponds to `s k'.
  ;; $$$$$$ An alternative default value: `bmkp-alpha-p', which corresponds to `s n'.
  "*Predicate or predicates for sorting (comparing) bookmarks.
This defines the default sort for bookmarks in the bookmark list.

Various sorting commands, such as \\<bookmark-bmenu-mode-map>\
`\\[bmkp-bmenu-sort-by-bookmark-visit-frequency]', change the value of this
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
 ((p1) p2-plain) where p2-plain is (bmkp-make-plain-predicate p2)

Likewise, these three values generally act equivalently (*):

 ((p1))
 (() p1-plain)
 p1-plain        where p1-plain is (bmkp-make-plain-predicate p1)

The PRED form lets you easily combine predicates: use `p1' unless it
cannot decide, in which case try `p2', and so on.  The value ((p2 p1))
tries the predicates in the opposite order: first `p2', then `p1' if
`p2' returns nil.

Using a single predicate or FINAL-PRED makes it easy to reuse an
existing predicate that returns nil or non-nil.

You can also convert a PRED-type predicate (which returns (t), (nil),
or nil) into an ordinary predicate, by using function
`bmkp-make-plain-predicate'.  That lets you reuse elsewhere, as
ordinary predicates, any PRED-type predicates you define.

For example, this defines a plain predicate to compare by URL:
 (defalias 'bmkp-url-p (bmkp-make-plain-predicate 'bmkp-url-cp))

Note: As a convention, predefined Bookmark+ PRED-type predicate names
have the suffix `-cp' (for \"component predicate\") instead of `-p'.

--
* If you use `\\[bmkp-reverse-multi-sort-order]', then there is a difference in \
behavior between

   (a) using a plain predicate as FINAL-PRED and
   (b) using the analogous PRED-type predicate (and no FINAL-PRED).

  In the latter case, `\\[bmkp-reverse-multi-sort-order]' affects when the predicate \
is tried and
  its return value.  See `bmkp-reverse-multi-sort-order'."
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
(defcustom bmkp-su-or-sudo-regexp "\\(/su:\\|/sudo:\\)"
  "*Regexp to recognize `su' or `sudo' Tramp bookmarks."
  :type 'regexp :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-this-buffer-cycle-sort-comparer '((bmkp-position-cp))
  "*`bmkp-sort-comparer' value for cycling this-buffer bookmarks.
Some values you might want to use: ((bmkp-position-cp)),
 ((bmkp-bookmark-creation-cp)), ((bmkp-visited-more-cp)).
See `bmkp-sort-comparer'."
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
(defcustom bmkp-use-region t
  "*Non-nil means visiting a bookmark activates its recorded region."
  :type '(choice
          (const :tag "Activate bookmark region (except during cycling)"  t)
          (const :tag "Do not activate bookmark region"                   nil)
          (const :tag "Activate bookmark region even during cycling"      cycling-too))
  :group 'bookmark-plus)

;;;###autoload
(defcustom bmkp-w3m-allow-multi-tabs t
  "*Non-nil means jump to W3M bookmarks in a new session."
  :type 'boolean :group 'bookmark-plus)
 
;;(@* "Internal Variables")
;;; Internal Variables -----------------------------------------------

(defconst bmkp-non-file-filename "   - no file -"
  "Name to use for `filename' entry, for non-file bookmarks.")

(defconst bmkp-types-alist '(("bookmark-file"    . bmkp-bookmark-file-history)
                             ("bookmark-list"    . bmkp-bookmark-list-history)
                             ("desktop"          . bmkp-desktop-history)
                             ("dired"            . bmkp-dired-history)
                             ("dired-this-dir"   . bmkp-dired-history)
                             ("file"             . bmkp-file-history)
                             ("file-this-dir"    . bmkp-file-history)
                             ("gnus"             . bmkp-gnus-history)
                             ("info"             . bmkp-info-history)
                             ("local-file"       . bmkp-local-file-history)
                             ("man"              . bmkp-man-history)
                             ("non-file"         . bmkp-non-file-history)
                             ("region"           . bmkp-region-history)
                             ("remote-file"      . bmkp-remote-file-history)
                             ("specific-buffers" . bmkp-specific-buffers-history)
                             ("specific-files"   . bmkp-specific-files-history)
                             ("url"              . bmkp-url-history)
                             ("variable-list"    . bmkp-variable-list-history))
  "Alist of bookmark types used by `bmkp-jump-to-type'.
Keys are bookmark type names.  Values are corresponding history variables.")

(defvar bmkp-bookmark-file-history ()    "History for bookmark-file bookmarks.")
(defvar bmkp-bookmark-list-history ()    "History for bookmark-list bookmarks.")
(defvar bmkp-desktop-history ()          "History for desktop bookmarks.")
(defvar bmkp-dired-history ()            "History for Dired bookmarks.")
(defvar bmkp-file-history ()             "History for file bookmarks.")
(defvar bmkp-gnus-history ()             "History for Gnus bookmarks.")
(defvar bmkp-info-history ()             "History for Info bookmarks.")
(defvar bmkp-last-bmenu-state-file nil   "Last value of option `bmkp-bmenu-state-file'.")
(defvar bmkp-local-file-history ()       "History for local-file bookmarks.")
(defvar bmkp-man-history ()              "History for `man'-page bookmarks.")
(defvar bmkp-non-file-history ()         "History for buffer (non-file) bookmarks.")
(defvar bmkp-region-history ()           "History for bookmarks that activate the region.")
(defvar bmkp-remote-file-history ()      "History for remote-file bookmarks.")
(defvar bmkp-specific-buffers-history () "History for specific-buffers bookmarks.")
(defvar bmkp-specific-files-history ()   "History for specific-files bookmarks.")
(defvar bmkp-url-history ()              "History for URL bookmarks.")
(defvar bmkp-variable-list-history ()    "History for variable-list bookmarks.")
(defvar bmkp-w3m-history ()              "History for W3M bookmarks.")

(defvar bmkp-after-set-hook nil "Hook run after `bookmark-set' sets a bookmark.")

(defvar bmkp-copied-tags ()
  "List of tags copied from a bookmark, for pasting to other bookmarks.")

(defvar bmkp-current-bookmark-file bookmark-default-file
  "Current bookmark file.
When you start Emacs, this is initialized to `bookmark-default-file'.
When you load bookmarks using `bmkp-switch-bookmark-file', this is set
to the file you load.  When you save bookmarks using `bookmark-save'
with no prefix arg, they are saved to this file.

However, this does not change the value of `bookmark-default-file'.
The value of `bookmark-default-file' is never changed, except by your
customizations.  Each Emacs session uses `bookmark-default-file' for
the initial set of bookmarks.")

(defvar bmkp-last-bookmark-file bookmark-default-file
  "Last bookmark file used in this session (or default bookmark file).
This is a backup for `bmkp-current-bookmark-file'.")

(defvar bmkp-current-nav-bookmark nil "Current bookmark for navigation.")

(defvar bmkp-jump-display-function nil "Function used currently to display a bookmark.")

(defvar bmkp-last-specific-buffer ""
  "Name of buffer used by `bmkp-last-specific-buffer-p'.")

(defvar bmkp-last-specific-file ""
  "(Absolute) file name used by `bmkp-last-specific-file-p'.")

(defvar bmkp-nav-alist () "Current bookmark alist used for navigation.")

(defvar bmkp-return-buffer nil "Name of buffer to return to.")

(defvar bmkp-reverse-sort-p nil "Non-nil means the sort direction is reversed.")

(defvar bmkp-reverse-multi-sort-p nil
  "Non-nil means the truth values returned by predicates are complemented.
This changes the order of the sorting groups, but it does not in
general reverse that order.  The order within each group is unchanged
\(not reversed).")

(defvar bmkp-use-w32-browser-p nil
  "Non-nil means use `w32-browser' in the default bookmark handler.
That is, use the default Windows application for the bookmarked file.
This has no effect if `w32-browser' is not defined.")

(defvar bmkp-latest-bookmark-alist () "Copy of `bookmark-alist' as last filtered.")

(defvar bmkp-last-save-flag-value nil "Last value of option `bookmark-save-flag'.")

(defvar bmkp-sorted-alist ()
  "Copy of current bookmark alist, as sorted for buffer `*Bookmark List*'.
Has the same structure as `bookmark-alist'.")

(defvar bmkp-tag-history () "History of tags read from the user.")

(defvar bmkp-tags-alist ()         
  "Alist of all tags, from all bookmarks.
Each entry is a cons whose car is a tag name, a string.
This is set by function `bmkp-tags-list'.
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
 (location . LOCATION)
 (position . POS)
 (front-context-string . STR-AFTER-POS)
 (rear-context-string  . STR-BEFORE-POS)
 (handler . HANDLER)
 (annotation . ANNOTATION)

 FILENAME names the bookmarked file.
 LOCATION names the bookmarked file, URL, or other place (Emacs 23+).
  FILENAME or LOCATION is what is shown in the bookmark list
  (`C-x r l') when you use `M-t'.
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

2. The buffer name is recorded, using entry `buffer-name'.  It need
not be associated with a file.

3. If no file is associated with the bookmark, then FILENAME is
   `   - no file -'.

4. Bookmarks can be tagged by users.  The tag information is recorded
using entry `tags':

 (tags . TAGS-ALIST)

 TAGS-ALIST is an alist with string keys.

5. Bookmarks can have individual highlighting, provided by users.
This overrides any default highlighting.

 (lighting . HIGHLIGHTING)

 HIGHLIGHTING is a property list that contain any of these keyword
 pairs:

   `:style' - Highlighting style.  Cdrs of `bmkp-light-styles-alist'
              entries are the possible values.
   `:face'  - Highlighting face, a symbol.
   `:when'  - A sexp to be evaluated.  Return value of `:no-light'
              means do not highlight.

6. The following additional entries are used to record region
information.  When a region is bookmarked, POS represents the region
start position.

 (end-position . END-POS)
 (front-context-region-string . STR-BEFORE-END-POS)
 (rear-context-region-string . STR-AFTER-END-POS))

 END-POS is the region end position.
 STR-BEFORE-END-POS is buffer text that precedes END-POS.
 STR-AFTER-END-POS is buffer text that follows END-POS.

The two context region strings are non-nil only when a region is
bookmarked.

 NOTE: The relative locations of `front-context-region-string' and
 `rear-context-region-string' are reversed from those of
 `front-context-string' and `rear-context-string'.  For example,
 `front-context-string' is the text that *follows* `position', but
 `front-context-region-string' *precedes* `end-position'.

7. The following additional entries are used for a Dired bookmark.

 (dired-marked . MARKED-FILES)
 (dired-switches . SWITCHES)

 MARKED-FILES is the list of files that were marked.
 SWITCHES is the string of `dired-listing-switches'.

8. The following additional entries are used for a Gnus bookmark.

 (group . GNUS-GROUP-NAME)
 (article . GNUS-ARTICLE-NUMBER)
 (message-id . GNUS-MESSAGE-ID)

 GNUS-GROUP-NAME is the name of a Gnus group.
 GNUS-ARTICLE-NUMBER is the number of a Gnus article.
 GNUS-MESSAGE-ID is the identifier of a Gnus message.

9. For a URL bookmark, FILENAME or LOCATION is a URL.

10. A sequence bookmark has this additional entry:

 (sequence . COMPONENT-BOOKMARKS)

 COMPONENT-BOOKMARKS is the list of component bookmark names.

11. A function bookmark has this additional entry, which records the
FUNCTION:

 (function . FUNCTION)

12. A bookmark-list bookmark has this additional entry, which records
the state of buffer `*Bookmark List*' at the time it is created:

 (bookmark-list . STATE)

 STATE records the sort order, filter function, omit list, and title.")
 
;;(@* "Compatibility Code for Older Emacs Versions")
;;; Compatibility Code for Older Emacs Versions ----------------------

(when (< emacs-major-version 23)

  ;; These definitions are for Emacs versions prior to Emacs 23.
  ;; They are the same as the vanilla Emacs 23+ definitions, except as noted.
  ;; They let older versions of Emacs handle bookmarks created with Emacs 23.

  (defun bookmark-get-bookmark-record (bookmark)
    "Return the guts of the entry for BOOKMARK in `bookmark-alist'.
That is, all information but the name.
BOOKMARK is a bookmark name or a bookmark record."
    (let ((alist  (cdr (bookmark-get-bookmark bookmark))))
      ;; A bookmark record is either (NAME ALIST) or (NAME . ALIST).
      (if (and (null (cdr alist)) (consp (caar alist)))
          (car alist)
        alist)))

  (defun Info-bookmark-make-record ()
    "Create an Info bookmark record."
    `(,Info-current-node
      ,@(bookmark-make-record-default 'no-file)
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

(when (< emacs-major-version 22)

  ;; These definitions are for Emacs versions prior to Emacs 22.
  ;; They are the same as the vanilla Emacs 22+ definitions, except as noted.

  ;; Emacs 22+ just uses `bookmark-jump-other-window' for the menu also.
  (defun bmkp-menu-jump-other-window (event)
    "Jump to BOOKMARK (a point in some file) in another window.
See `bookmark-jump-other-window'."
    (interactive "e")
    (bookmark-popup-menu-and-apply-function 'bookmark-jump-other-window
                                            "Jump to Bookmark (Other Window)" event))

  (defun bookmark-maybe-message (fmt &rest args)
    "Apply `message' to FMT and ARGS, but only if the display is fast enough."
    (when (>= baud-rate 9600) (apply 'message fmt args))))
 
;;(@* "Core Replacements (`bookmark-*' except `bookmark-bmenu-*')")
;;; Core Replacements (`bookmark-*' except `bookmark-bmenu-*') -------


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. If BOOKMARK is a bookmark-name string that has non-nil property `bmkp-full-record'
;;    then return the value of that property.
;; 2. Handle the should-not-happen case of non-string, non-cons.
;; 3. Document NOERROR in doc string.
(defun bookmark-get-bookmark (bookmark &optional noerror)
  "Return the bookmark record corresponding to BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If BOOKMARK is a bookmark record, just return it.
Otherwise look for the corresponding bookmark in `bookmark-alist'.
Return the bookmark found or raise an error if none found.

If BOOKMARK is a bookmark-name string that has non-nil property
`bmkp-full-record' then return the value of that property.

Non-nil optional arg NOERROR means return nil if BOOKMARK
is not a valid bookmark - do not raise an error."
  (cond ((consp bookmark) bookmark)
        ((stringp bookmark)
         (let ((full  (get-text-property 0 'bmkp-full-record bookmark)))
           (or full                     ; If unpropertized string then punt.
               (if (fboundp 'assoc-string) ; Emacs 22+.
                   (assoc-string bookmark bookmark-alist bookmark-completion-ignore-case)
                 (assoc bookmark bookmark-alist))
               (unless noerror (error "Invalid bookmark: `%s'" bookmark)))))
        (t (unless noerror (error "Invalid bookmark: `%s'" bookmark)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Put the full bookmark on the bookmark name as property `bmkp-full-record'.
;; 2. Use `bmkp-maybe-save-bookmarks'.
;; 3. Return the bookmark.
;;
(defun bookmark-store (bookmark-name data no-overwrite)
  "Store the bookmark named BOOKMARK-NAME, giving it DATA.
If NO-OVERWRITE is non-nil and bookmark BOOKMARK-NAME already exists,
then record the new bookmark but do not discard the old one.

The check for existence uses `bookmark-get-bookmark', so if string
BOOKMARK-NAME has property `bmkp-full-record' then the check is for a
particular bookmark with the given name.  If BOOKMARK-NAME does not
have that property then the check is for any bookmark with that name.

Return the new bookmark."
  (bookmark-maybe-load-default-file)
  (let ((bname  (copy-sequence bookmark-name))
        bmk)
    (unless (featurep 'xemacs)
      ;; XEmacs's `set-text-properties' doesn't work on free-standing strings, apparently.
      (set-text-properties 0 (length bname) () bname))
    (if (and (not no-overwrite) (bookmark-get-bookmark bname 'noerror))
        ;; Existing bookmark under that name and no prefix arg means just overwrite existing.
        ;; Use the new (NAME . ALIST) format.
        (setcdr (setq bmk  (bookmark-get-bookmark bname)) data)
      (push (setq bmk  (cons bname data)) bookmark-alist)
      ;; Put the bookmark on the name as property `bmkp-full-record'.
      (when (and (> emacs-major-version 20) ; Emacs 21+.  Cannot just use (boundp 'print-circle).
                 bmkp-propertize-bookmark-names-flag)
        (put-text-property 0 (length bname) 'bmkp-full-record bmk bname)))
    (bmkp-maybe-save-bookmarks)
    (setq bookmark-current-bookmark  bname)
    (bookmark-bmenu-surreptitiously-rebuild-list)
    bmk))                               ; Return the bookmark.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; BUG fix: Need bookmark arg in `interactive' spec.
;;
;;;###autoload
(defun bookmark-edit-annotation-mode (bookmark)
  "Mode for editing the annotation of bookmark BOOKMARK.
When you have finished composing, type \\[bookmark-send-annotation].
BOOKMARK is a bookmark name or a bookmark record.

\\{bookmark-edit-annotation-mode-map}"
  (interactive (list (bookmark-completing-read "Edit annotation of bookmark"
                                               (bmkp-default-bookmark-name)
                                               (bmkp-annotated-alist-only))))
  (kill-all-local-variables)
  (make-local-variable 'bookmark-annotation-name)
  (setq bookmark-annotation-name  bookmark)
  (use-local-map bookmark-edit-annotation-mode-map)
  (setq major-mode  'bookmark-edit-annotation-mode
        mode-name  "Edit Bookmark Annotation")
  (insert (funcall (if (boundp 'bookmark-edit-annotation-text-func)
                       bookmark-edit-annotation-text-func
                     bookmark-read-annotation-text-func)
                   bookmark))
  (let ((annotation  (bookmark-get-annotation bookmark)))
    (if (and annotation (not (string-equal annotation "")))
	(insert annotation)))
  (if (fboundp 'run-mode-hooks)
      (run-mode-hooks 'text-mode-hook)
    (run-hooks 'text-mode-hook)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. BUG fix: Put point back where it was (on the bookmark just annotated).
;; 2. Refresh menu list, to pick up the `a' marker.
;; 3. Make sure it's the annotation buffer that gets killed.
;; 4. Delete window also, if `misc-cmds.el' loaded.
;;
;;;###autoload
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
  (let ((annotation      (buffer-substring-no-properties (point-min) (point-max)))
	(bookmark        bookmark-annotation-name)
        (annotation-buf  (current-buffer)))
    (bookmark-set-annotation bookmark annotation)
    (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
      (with-current-buffer (get-buffer "*Bookmark List*")
        (bmkp-refresh-menu-list bookmark))) ; So the `a' marker is displayed (updated).
    (if (fboundp 'kill-buffer-and-its-windows)
        (kill-buffer-and-its-windows annotation-buf) ; Defined in `misc-cmds.el'.
      (kill-buffer annotation-buf))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Added `interactive' spec.
;;
;;;###autoload
(defun bookmark-edit-annotation (bookmark)
  "Pop up a buffer for editing bookmark BOOKMARK's annotation.
BOOKMARK is a bookmark name or a bookmark record."
  (interactive (list (bookmark-completing-read "Edit annotation of bookmark"
                                               (bmkp-default-bookmark-name)
                                               (bmkp-annotated-alist-only))))
  (pop-to-buffer (generate-new-buffer-name "*Bookmark Annotation Compose*"))
  (bookmark-edit-annotation-mode bookmark))


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
;; 1. Added optional args ALIST, PRED, and HIST.
;; 2. Define using helper function `bmkp-completing-read-1',
;;    which binds `icicle-delete-candidate-object' to (essentially) `bookmark-delete'.
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
of option `bmkp-menu-popup-max-length' and the number of
bookmarks in ALIST, you choose the bookmark using a menu or using
completion.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (bmkp-completing-read-1 prompt default alist pred hist nil))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Handles also regions and non-file buffers.
;; 2. Do not use NO-CONTEXT or POSN if < Emacs 24.
;;
(defun bookmark-make-record-default (&optional no-file no-context position visits)
  "Return the record describing the location of a new bookmark.
Point must be where the bookmark is to be set.

Non-nil NO-FILE means return only the subset of the record that
 pertains to the location within the buffer (not also the file name).

Non-nil NO-CONTEXT means do not include the front and rear context
strings in the record enough.

Non-nil POSITION means record it, not point, as the `position' entry.

Non-nil VISITS means record it as the `visits' entry."
  (let* ((dired-p  (and (boundp 'dired-buffers) (car (rassq (current-buffer) dired-buffers))))
         (buf      (buffer-name))
         (ctime    (current-time))

         ;; Begin `let*' dependencies.
         (regionp  (and transient-mark-mode mark-active (not (eq (mark) (point)))))
         (beg      (if regionp (region-beginning) (or position (point))))
         (end      (if regionp (region-end) (point)))
         (fcs      (if regionp
                       (bmkp-position-post-context-region beg end)
                     (bmkp-position-post-context beg)))
         (rcs      (if regionp
                       (bmkp-position-pre-context-region beg)
                     (bmkp-position-pre-context beg)))
         (fcrs     (when regionp (bmkp-end-position-pre-context beg end)))
         (ecrs     (when regionp (bmkp-end-position-post-context end))))
    `(,@(unless no-file
                `((filename . ,(cond ((buffer-file-name)
                                      (bookmark-buffer-file-name))
                                     (dired-p  nil)
                                     (t        bmkp-non-file-filename)))))
      (buffer-name . ,buf)
      ,@(unless (and no-context (> emacs-major-version 23))
                `((front-context-string . ,fcs)))
      ,@(unless (and no-context (> emacs-major-version 23))
                `((rear-context-string . ,rcs)))
      ,@(unless (and no-context (> emacs-major-version 23))
                `((front-context-region-string . ,fcrs)))
      ,@(unless (and no-context (> emacs-major-version 23))
                `((rear-context-region-string  . ,ecrs)))
      (visits       . ,(or visits 0))
      (time         . ,ctime)
      (created      . ,ctime)
      (position     . ,beg)
      (end-position . ,end))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use `bookmark-make-record'.
;; 2. Use special default prompts for active region, W3M, and Gnus.
;; 3. Use `bmkp-completing-read-lax', choosing from current buffer's bookmarks.
;; 4. Numeric prefix arg (diff from plain): all bookmarks as completion candidates.
;; 5. Prompt for tags if `bmkp-prompt-for-tags-flag' is non-nil.
;; 6. Possibly highlight bookmark and other bookmarks in buffer, per `bmkp-auto-light-when-set'.
;;
;;;###autoload
(defun bookmark-set (&optional name parg interactivep) ; `C-x r m'
  "Set a bookmark named NAME, then run `bmkp-after-set-hook'.
If the region is active (`transient-mark-mode') and nonempty, then
record the region limits in the bookmark.

If NAME is nil, then prompt for the bookmark name.  The default name
for prompting is as follows (in order of priority):

 * If the region is active and nonempty, then the buffer name followed
   by \": \" and the region prefix (up to
   `bmkp-bookmark-name-length-max' chars).

 * If in W3M mode, then the current W3M title.

 * If in a Gnus mode, then the Gnus summary article header.

 * If on a `man' page, then the page name (command and section).

 * Otherwise, the current buffer name.

While entering a bookmark name at the prompt:

 * You can use (lax) completion against bookmarks in the same buffer.
   If there are no bookmarks in the current buffer, then all bookmarks
   are completion candidates.  (See also below, about a numeric prefix
   argument.)

 * You can use `C-w' to yank words from the buffer to the minibuffer.
   Repeating `C-w' yanks successive words.

 * You can use `C-u' to insert the name of the last bookmark used in
   the buffer.  This can be useful as an aid to track your progress
   through a large file.  (If no bookmark has yet been used, then
   `C-u' inserts the name of the visited file.)

A prefix argument changes the behavior as follows:

 * Numeric prefix arg: Use all bookmarks as completion candidates,
   instead of just the bookmarks for the current buffer.

 * Plain prefix arg (`C-u'): Do not overwrite a bookmark that has the
   same name as NAME, if such a bookmark already exists.  Instead,
   push the new bookmark onto the bookmark alist.

   The most recently set bookmark named NAME is thus the one in effect
   at any given time, but any others named NAME are still available,
   should you decide to delete the most recent one.

Use `\\[bookmark-delete]' to remove bookmarks (you give it a name, and it removes
only the first instance of a bookmark with that name from the list of
bookmarks)."
  (interactive (list nil current-prefix-arg t))
  (bookmark-maybe-load-default-file)
  (setq bookmark-current-point   (point) ; `bookmark-current-point' is a free var here.
        bookmark-current-buffer  (current-buffer))
  (save-excursion (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
  (let* ((record   (bookmark-make-record))
         (regionp  (and transient-mark-mode mark-active (not (eq (mark) (point)))))
         (regname  (concat (buffer-name) ": "
                           (buffer-substring (if regionp (region-beginning) (point))
                                             (if regionp
                                                 (region-end)
                                               (save-excursion (end-of-line) (point))))))
         (defname  (bmkp-replace-regexp-in-string
                    "\n" " "
                    (cond (regionp (save-excursion (goto-char (region-beginning))
                                                   (skip-chars-forward " ")
                                                   (setq bookmark-yank-point  (point)))
                                   (substring regname 0 (min bmkp-bookmark-name-length-max
                                                             (length regname))))
                          ((eq major-mode 'w3m-mode) w3m-current-title)
                          ((eq major-mode 'gnus-summary-mode) (elt (gnus-summary-article-header) 1))
                          ((memq major-mode '(Man-mode woman-mode))
                           (buffer-substring (point-min) (save-excursion (goto-char (point-min))
                                                                         (skip-syntax-forward "^ ")
                                                                         (point))))
                          (t (car record)))))
         (bname    (or name  (bmkp-completing-read-lax
                              "Set bookmark " defname
                              (and (or (not parg) (consp parg)) ; No numeric PARG: all bookmarks.
                                   (bmkp-specific-buffers-alist-only))
                              nil 'bookmark-history))))
    (when (string-equal bname "") (setq bname  defname))
    (bookmark-store bname (cdr record) (consp parg))
    (when (and interactivep bmkp-prompt-for-tags-flag)
      (bmkp-add-tags bname (bmkp-read-tags-completing)))
    (case (and (boundp 'bmkp-auto-light-when-set) bmkp-auto-light-when-set)
      (autonamed-bookmark       (when (bmkp-autonamed-bookmark-p bname)
                                  (bmkp-light-bookmark bname)))
      (non-autonamed-bookmark   (unless (bmkp-autonamed-bookmark-p bname)
                                  (bmkp-light-bookmark bname)))
      (any-bookmark             (bmkp-light-bookmark bname))
      (autonamed-in-buffer      (bmkp-light-bookmarks (bmkp-remove-if-not
                                                           #'bmkp-autonamed-bookmark-p
                                                           (bmkp-this-buffer-alist-only)) nil 'MSG))
      (non-autonamed-in-buffer  (bmkp-light-bookmarks (bmkp-remove-if
                                                           #'bmkp-autonamed-bookmark-p
                                                           (bmkp-this-buffer-alist-only)) nil 'MSG))
      (all-in-buffer            (bmkp-light-this-buffer nil 'MSG)))
    (run-hooks 'bmkp-after-set-hook)
    (if bookmark-use-annotations
        (bookmark-edit-annotation bname)
      (goto-char bookmark-current-point)))) ; `bookmark-current-point' is a free var here.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Prevent adding a newline in a bookmark name when yanking.
;; 
;;;###autoload
(defun bookmark-yank-word ()            ; Bound to `C-w' in minibuffer when setting bookmark.
  "Yank the word at point in `bookmark-current-buffer'.
Repeat to yank subsequent words from the buffer, appending them.
Newline characters are stripped out."
  (interactive)
  (let ((string  (with-current-buffer bookmark-current-buffer
                   (goto-char bookmark-yank-point)
                   (buffer-substring-no-properties (point)
                                                   (progn (forward-word 1)
                                                          (setq bookmark-yank-point  (point)))))))
    (setq string  (bmkp-replace-regexp-in-string "\n" "" string))
    (insert string)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Save DISPLAY-FUNCTION to `bmkp-jump-display-function' before calling
;;    `bookmark-handle-bookmark'.
;; 2. Update the name and position of an autonamed bookmark, in case it moved.
;; 3. Possibly highlight bookmark and other bookmarks in buffer, per `bmkp-auto-light-when-jump'.
;; 4. Added `catch', so a handler can throw to skip the rest of the processing if it wants.
;;
(defun bookmark--jump-via (bookmark display-function)
  "Display BOOKMARK using DISPLAY-FUNCTION.
Then run `bookmark-after-jump-hook' and show annotations for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bmkp-record-visit bookmark 'batch)
  (setq bmkp-jump-display-function  display-function)
  (catch 'bookmark--jump-via
    (bookmark-handle-bookmark bookmark)
    (let ((win  (get-buffer-window (current-buffer) 0)))
      (when win (set-window-point win (point))))
    ;; If this is an autonamed bookmark, update its name and position, in case it moved.
    ;; But don't do it if we're using w32, since we might not have moved to the bookmark position.
    (when (and (bmkp-autonamed-bookmark-for-buffer-p bookmark (buffer-name))
               (not bmkp-use-w32-browser-p))
      (setq bookmark  (bmkp-update-autonamed-bookmark bookmark)))
    (case (and (boundp 'bmkp-auto-light-when-jump) bmkp-auto-light-when-jump)
      (autonamed-bookmark       (when (bmkp-autonamed-bookmark-p bookmark)
                                  (bmkp-light-bookmark bookmark nil nil nil 'USE-POINT)))
      (non-autonamed-bookmark   (unless (bmkp-autonamed-bookmark-p bookmark)
                                  (bmkp-light-bookmark bookmark nil nil nil 'USE-POINT)))
      (any-bookmark             (bmkp-light-bookmark bookmark nil nil nil 'USE-POINT))
      (autonamed-in-buffer      (bmkp-light-bookmarks (bmkp-remove-if-not
                                                       #'bmkp-autonamed-bookmark-p
                                                       (bmkp-this-buffer-alist-only)) nil 'MSG))
      (non-autonamed-in-buffer  (bmkp-light-bookmarks (bmkp-remove-if
                                                       #'bmkp-autonamed-bookmark-p
                                                       (bmkp-this-buffer-alist-only)) nil 'MSG))
      (all-in-buffer            (bmkp-light-this-buffer nil 'MSG)))
    (let ((orig-buff  (current-buffer))) ; Used by `crosshairs-highlight'.
      (run-hooks 'bookmark-after-jump-hook))
    (let ((jump-fn  (bmkp-get-tag-value bookmark "bmkp-jump")))
      (when jump-fn (funcall jump-fn)))
    (when bookmark-automatically-show-annotations (bookmark-show-annotation bookmark))))


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
;; 2. Use `bmkp-default-bookmark-name' as default when interactive.
;; 3. Use `bmkp-jump-1'.
;; 4. Added note about Icicles `S-delete' to doc string.
;;
;;;###autoload
(defun bookmark-jump (bookmark          ; Bound to `C-x j j', `C-x r b', `C-x p g'
                      &optional display-function use-region-p)
  "Jump to bookmark BOOKMARK.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If the file pointed to by BOOKMARK no longer exists, you are asked if
you wish to give the bookmark a new location.  If so, `bookmark-jump'
jumps to the new location and saves it.

If the bookmark defines a region, then the region is activated if
`bmkp-use-region' is not-nil or it is nil and you use a prefix
argument.  A prefix arg temporarily flips the value of
`bmkp-use-region'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.

In Lisp code:
BOOKMARK is a bookmark name or a bookmark record.
Non-nil DISPLAY-FUNCTION is a function to display the bookmark.  By
 default, `switch-to-buffer' is used.
Non-nil USE-REGION-P flips the value of `bmkp-use-region'."
  (interactive (list (bookmark-completing-read "Jump to bookmark" (bmkp-default-bookmark-name))
                     nil
                     current-prefix-arg))
  (bmkp-jump-1 bookmark (or display-function 'switch-to-buffer) use-region-p))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg USE-REGION-P.
;; 2. Use `bmkp-default-bookmark-name' as default when interactive.
;; 3. Use `bmkp-jump-1'.
;;
;;;###autoload
(defun bookmark-jump-other-window (bookmark &optional use-region-p) ; `C-x 4 j j', `C-x p o'
  "Jump to bookmark BOOKMARK in another window.
See `bookmark-jump', in particular for info about using a prefix arg."
  (interactive (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                               (bmkp-default-bookmark-name))
                     current-prefix-arg))
  (bmkp-jump-1 bookmark 'bmkp-select-buffer-other-window use-region-p))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Different relocation message for non-file bookmark.
;;
(defun bookmark-handle-bookmark (bookmark)
  "Call BOOKMARK's handler, or `bookmark-default-handler' if it has none.
The default handler changes the current buffer and point.
BOOKMARK is a bookmark name or a bookmark record.
Returns nil or raises an error.

If the default handler is used and a file error is raised, the error
is handled as follows:
 If BOOKMARK has no `filename' entry, do nothing.
 Else prompt to relocate the file.
   If relocated, then try again to handle.  Else raise a file error."
  (if (bookmark-get-handler bookmark)
      (funcall (bookmark-get-handler bookmark) (bookmark-get-bookmark bookmark))
    (condition-case err
        (funcall 'bookmark-default-handler (bookmark-get-bookmark bookmark))
      (bookmark-error-no-filename         ; `file-error'
       ;; BOOKMARK can be either a bookmark name or a bookmark record.
       ;; If a record, do nothing - assume it is a bookmark used internally by some other package.
       (when (stringp bookmark)
         (let ((file             (bookmark-get-filename bookmark))
               (use-dialog-box   nil)
               (use-file-dialog  nil))
           (when file
             ;; Ask user whether to relocate the file.  If no, signal the file error.
             (unless (string= file bmkp-non-file-filename) (setq file  (expand-file-name file)))
             (ding)
             (cond ((y-or-n-p (if (and (string= file bmkp-non-file-filename)
                                       (bmkp-get-buffer-name bookmark))
                                  "Bookmark's buffer does not exist.  Re-create it? "
                                (concat (file-name-nondirectory file) " nonexistent.  Relocate \""
                                        bookmark "\"? ")))
                    (if (string= file bmkp-non-file-filename)
                        ;; This is probably not the right way to get the correct buffer, but it's
                        ;; better than nothing, and it gives the user a chance to DTRT.
                        (pop-to-buffer (bmkp-get-buffer-name bookmark)) ; Create buffer.
                      (bookmark-relocate bookmark)) ; Relocate to file.
                    (funcall (or (bookmark-get-handler bookmark) 'bookmark-default-handler)
                             (bookmark-get-bookmark bookmark))) ; Try again
                   (t
                    (message "Bookmark not relocated: `%s'" bookmark)
                    (signal (car err) (cdr err))))))))))
  (when (stringp bookmark) (setq bookmark-current-bookmark  bookmark))
  ;; $$$$$$ The vanilla code returns nil, but there is no explanation of why and no code seems
  ;; to use the return value.  Perhaps we should return the bookmark instead?
  nil)                                  ; Return nil if no error.

(put 'bookmark-error-no-filename 'error-conditions
     '(error bookmark-errors bookmark-error-no-filename))
(put 'bookmark-error-no-filename 'error-message "Bookmark has no associated file (or directory)")


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Support regions and buffer names.
;; 2. Handles w32 `Open' command if `bmkp-use-w32-browser-p' and if `w32-browser' is defined.
;;
(defun bookmark-default-handler (bookmark)
  "Default handler to jump to the location of BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
If BOOKMARK records a nonempty region, and `bmkp-use-region' is
 non-nil, then activate the region.

Non-nil `bmkp-use-w32-browser-p' means just call `w32-browser'
 (if defined).  That is, use the default MS Windows application for
 the bookmarked file.

Return nil or signal `file-error'."
  (let* ((bmk            (bookmark-get-bookmark bookmark))
         (file           (bookmark-get-filename bmk))
         (buf            (bookmark-prop-get bmk 'buffer))
         (bufname        (bmkp-get-buffer-name bmk))
         (pos            (bookmark-get-position bmk))
         (end-pos        (bmkp-get-end-position bmk))
         (old-info-node  (and (not (bookmark-get-handler bookmark))
                              (bookmark-prop-get bmk 'info-node))))
    (if (and bmkp-use-w32-browser-p (fboundp 'w32-browser) file)
        (w32-browser file)
      (if old-info-node                 ; Emacs 20-21 Info bookmarks - no handler entry.
          (progn (require 'info) (Info-find-node file old-info-node) (goto-char pos))
        (if (not (and bmkp-use-region end-pos (/= pos end-pos)))
            ;; Single-position bookmark (no region).  Go to it.
            (bmkp-goto-position bmk file buf bufname pos
                                (bookmark-get-front-context-string bmk)
                                (bookmark-get-rear-context-string bmk))
          ;; Bookmark with a region.  Go to it and activate the region.
          (if (and file (file-readable-p file) (not (buffer-live-p buf)))
              (with-current-buffer (find-file-noselect file) (setq buf  (buffer-name)))
            ;; No file found.  If no buffer either, then signal that file doesn't exist.
            (unless (or (and buf (get-buffer buf))
                        (and bufname (get-buffer bufname) (not (string= buf bufname))))
              (signal 'bookmark-error-no-filename (list 'stringp file))))
          (set-buffer (or buf bufname))
          (when bmkp-jump-display-function
            (save-current-buffer (funcall bmkp-jump-display-function (current-buffer)))
            (raise-frame))
          (goto-char (min pos (point-max)))
          (when (> pos (point-max)) (error "Bookmark position is beyond buffer end"))
          ;; Activate region.  Relocate it if it moved.  Save relocated bookmark if confirm.
          (funcall bmkp-handle-region-function bmk))))
    ;; $$$$$$ The vanilla code returns nil, but there is no explanation of why and no code seems
    ;; to use the return value.  Perhaps we should return the bookmark instead?
    nil))                               ; Return nil if no file error.


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
(defun bookmark-relocate (bookmark-name) ; Not bound
  "Relocate the bookmark named BOOKMARK-NAME to another file.
You are prompted for the new file name.
Changes the file associated with the bookmark.
Useful when a file has been renamed after a bookmark was set in it.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Bookmark to relocate"
                                               (bmkp-default-bookmark-name))))
  (old-bookmark-relocate bookmark-name)
  (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0)
             bookmark-bmenu-toggle-filenames)
    (with-current-buffer (get-buffer "*Bookmark List*")
      (bmkp-refresh-menu-list bookmark-name)))) ; So the new location is displayed.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Do not add any text properties here.  That's done in `bmkp-bmenu-propertize-item'.
;; 3. Added note about `S-delete' to doc string.
;; 4. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;;
;;;###autoload
(defun bookmark-insert-location (bookmark-name &optional no-history) ; `C-x p I' (original: `C-x p f')
  "Insert file or buffer name for the bookmark named BOOKMARK-NAME.
If a file is bookmarked, insert the recorded file name.
If a non-file buffer is bookmarked, insert the recorded buffer name.

Optional second arg NO-HISTORY means do not record this in the
minibuffer history list `bookmark-history'.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive
   (let ((bmk  (bookmark-completing-read "Insert bookmark location" (bmkp-default-bookmark-name))))
     (if (> emacs-major-version 21) (list bmk) bmk)))
  (or no-history (bookmark-maybe-historicize-string bookmark-name))
  (insert (bookmark-location bookmark-name))) ; Return the line inserted.


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Pass full bookmark to the various "get" functions.
;; 2. Location returned can be a buffer name, instead of a file name.
;;
(defun bookmark-location (bookmark)
  "Return the name of the file or buffer associated with BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Return \"-- Unknown location --\" if no such name can be found."
  (bookmark-maybe-load-default-file)
  (setq bookmark  (bookmark-get-bookmark bookmark)) ; Possibly from the propertized string.
  (or (bookmark-prop-get bookmark 'location)
      (bookmark-get-filename bookmark)
      (bmkp-get-buffer-name bookmark)
      (bookmark-prop-get bookmark 'buffer)
      "-- Unknown location --"))
      ;; $$$$$$$$$ ""))
      ;; $$$$ (error "Bookmark has no file or buffer name: %S" bookmark)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added bookmark default for interactive use.
;; 2. Added note about `S-delete' to doc string.
;; 3. Added BATCH arg.
;; 4. Put `bmkp-full-record' property on new name.
;; 5. Refresh menu list, to show new name.
;;
;;;###autoload
(defun bookmark-rename (old &optional new batch) ; Bound to `C-x p r'
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
                                               (bmkp-default-bookmark-name))))
  (bookmark-maybe-historicize-string old)
  (bookmark-maybe-load-default-file)
  (setq bookmark-current-point  (point)) ; `bookmark-current-point' is a free var here.
  (save-excursion (skip-chars-forward " ") (setq bookmark-yank-point  (point)))
  (setq bookmark-current-buffer  (current-buffer))
  (let ((newname  (or new  (read-from-minibuffer "New name: " nil
                                                 (let ((now-map  (copy-keymap minibuffer-local-map)))
                                                   (define-key now-map  "\C-w" 'bookmark-yank-word)
                                                   now-map)
                                                 nil 'bookmark-history))))
    (bookmark-set-name old newname)
    (when (and (> emacs-major-version 20) ; Emacs 21+.  Cannot just use (boundp 'print-circle).
               bmkp-propertize-bookmark-names-flag)
      (put-text-property 0 (length newname) 'bmkp-full-record (bookmark-get-bookmark newname) newname))
    (setq bookmark-current-bookmark  newname)
    (unless batch
      (bookmark-bmenu-surreptitiously-rebuild-list)
      (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
        (with-current-buffer (get-buffer "*Bookmark List*")
          (bmkp-refresh-menu-list newname)))) ; So the new name is displayed.
    (bmkp-maybe-save-bookmarks)
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
(defun bookmark-insert (bookmark-name)  ; Bound to `C-x p i'
  "Insert the text of a bookmarked file.
BOOKMARK-NAME is the name of the bookmark.
You may have a problem using this function if the value of variable
`bookmark-alist' is nil.  If that happens, you need to load in some
bookmarks.  See function `bookmark-load' for more about this.

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate."
  (interactive (list (bookmark-completing-read "Insert bookmark contents"
                                               (bmkp-default-bookmark-name))))
  (old-bookmark-insert bookmark-name))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Accept a bookmark or a bookmark name as arg.
;; 2. Use `bmkp-default-bookmark-name' as default when interactive.
;; 3. If it is a name and it  has property `bmkp-full-record' then use that to find the bookmark to delete.
;; 4. Remove highlighting for the bookmark.
;; 5. Doc string includes note about `S-delete' for Icicles.
;; 6. Update `bmkp-latest-bookmark-alist' and `bmkp-bmenu-omitted-bookmarks'.
;; 7. Increment `bookmark-alist-modification-count' even when using `batch' arg.
;;
;;;###autoload
(defun bookmark-delete (bookmark &optional batch) ; Bound to `C-x p d'
  "Delete the BOOKMARK from the bookmark list.
BOOKMARK is a bookmark name or a bookmark record.
Interactively, default to the \"current\" bookmark (that is, the one
most recently used in this file), if it exists.

If BOOKMARK is a name and it has property `bmkp-full-record' then use
that property along with the name to find the bookmark to delete.
If it is a name without property `bmkp-full-record' then delete (only)
the first bookmark in `bookmark-alist' with that name.

Optional second arg BATCH means do not update the bookmark list buffer
\(probably because we were called from there).

If you use Icicles, then you can use `S-delete' during completion of a
bookmark name to delete the bookmark named by the current completion
candidate.  In this way, you can delete multiple bookmarks."
  (interactive
   (list (bookmark-completing-read "Delete bookmark" (bmkp-default-bookmark-name))))
  ;; $$$$$$ Instead of loading unconditionally, maybe we should just try to delete conditionally?
  ;; IOW, why not (when bookmarks-already-loaded BODY) instead of `bookmark-maybe-load-default-file'?
  ;; If it gets called on a hook that gets run before ever loading, then should probably do nothing.
  ;; Leaving it as is for now (2011-04-06).
  (bookmark-maybe-load-default-file)
  (let* ((bmk    (bookmark-get-bookmark bookmark 'NOERROR))
         (bname  (and (bookmark-name-from-full-record bmk)))) ; BOOKMARK might have been a bookmark.
    (when bname                         ; Do nothing if BOOKMARK does not represent a bookmark.
      (bookmark-maybe-historicize-string bname)
      (when (fboundp 'bmkp-unlight-bookmark) (bmkp-unlight-bookmark bmk 'NOERROR))
      (setq bookmark-alist                (delq bmk bookmark-alist)
            bmkp-latest-bookmark-alist    (delq bmk bmkp-latest-bookmark-alist)
            bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
                                           bname bmkp-bmenu-omitted-bookmarks))
      ;; Added by DB.  `bookmark-current-bookmark' should be nil if last occurrence was deleted.
      (unless (bookmark-get-bookmark bookmark-current-bookmark 'noerror)
        (setq bookmark-current-bookmark  nil))
      ;; Do not rebuild the list when using `batch' arg
      (unless batch (bookmark-bmenu-surreptitiously-rebuild-list))
      (bmkp-maybe-save-bookmarks))))


;;; ;; REPLACES ORIGINAL in `bookmark.el'.
;;; ;;
;;; ;; 1. Changed arg name: BOOKMARK -> BOOKMARK-NAME.
;;; ;; 2. If BOOKMARK-NAME has property `bmkp-full-record' then use that to find the bookmark to delete.
;;; ;; 3. Remove highlighting for the bookmark.
;;; ;; 4. Added note about `S-delete' to doc string.
;;; ;; 5. Use `bmkp-default-bookmark-name' as default when interactive.
;;; ;; 6. Update `bmkp-latest-bookmark-alist' and `bmkp-bmenu-omitted-bookmarks'.
;;; ;; 7. Increment `bookmark-alist-modification-count' even when using `batch' arg.
;;; ;;
;;; $$$$$$$
;;; (defun bookmark-delete (bookmark-name &optional batch) ; Bound to `C-x p d'
;;;   "Delete the bookmark named BOOKMARK-NAME from the bookmark list.
;;; Removes only the first instance of a bookmark with that name.
;;; If there are other bookmarks with the same name, they are not deleted.
;;; Defaults to the \"current\" bookmark (that is, the one most recently
;;; used in this file), if it exists.  Optional second arg BATCH means do
;;; not update the bookmark list buffer (probably because we were called
;;; from there).

;;; If BOOKMARK-NAME has property `bmkp-full-record' then that is used
;;; along with the name to find the first matching bookmark to delete.

;;; If you use Icicles, then you can use `S-delete' during completion of a
;;; bookmark name to delete the bookmark named by the current completion
;;; candidate.  In this way, you can delete multiple bookmarks."
;;;   (interactive
;;;    (list (bookmark-completing-read "Delete bookmark" (bmkp-default-bookmark-name))))
;;;   (bookmark-maybe-historicize-string bookmark-name)
;;;   ;; $$$$$$ Instead of loading unconditionally, maybe we should just try to delete conditionally?
;;;   ;; IOW, why not (when bookmarks-already-loaded BODY) instead of `bookmark-maybe-load-default-file'?
;;;   ;; If it gets called on a hook that gets run before ever loading, then should probably do nothing.
;;;   ;; Leaving it as is for now (2011-04-06).
;;;   (bookmark-maybe-load-default-file)
;;;   (let ((bmk  (bookmark-get-bookmark bookmark-name 'NOERROR)))
;;;     (when (fboundp 'bmkp-unlight-bookmark) (bmkp-unlight-bookmark bmk 'NOERROR))
;;;     (setq bookmark-alist                (delq bmk bookmark-alist)
;;;           bmkp-latest-bookmark-alist    (delq bmk bmkp-latest-bookmark-alist)
;;;           bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
;;;                                          bookmark-name bmkp-bmenu-omitted-bookmarks)))
;;;   ;; Added by DB.  `bookmark-current-bookmark' should be nil if last occurrence was deleted.
;;;   (unless (bookmark-get-bookmark bookmark-current-bookmark 'noerror)
;;;     (setq bookmark-current-bookmark  nil))
;;;   ;; Do not rebuild the list when using `batch' arg
;;;   (unless batch (bookmark-bmenu-surreptitiously-rebuild-list))
;;;   (bmkp-maybe-save-bookmarks))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Use `bmkp-current-bookmark-file', not `bookmark-default-file'.
;;
;;;###autoload
(defun bookmark-save (&optional parg file) ; Bound to `C-x p s'
  "Save currently defined bookmarks.
Save by default in the file named by variable
`bmkp-current-bookmark-file'.  With a prefix arg, you are prompted for
the file to save to.

To load bookmarks from a specific file, use `\\[bookmark-load]'
\(`bookmark-load').

If called from Lisp:
 Witn nil PARG, use file `bmkp-current-bookmark-file'.
 With non-nil PARG and non-nil FILE, use file FILE.
 With non-nil PARG and nil FILE, prompt the user for the file to use."
  (interactive "P")
  (bookmark-maybe-load-default-file)
  (cond ((and (not parg) (not file)) (bookmark-write-file bmkp-current-bookmark-file))
        ((and (not parg) file) (bookmark-write-file file))
        ((and parg (not file))
         (bookmark-write-file (bmkp-read-bookmark-file-name "File to save bookmarks in: ")))
        (t (bookmark-write-file file)))
  ;; Indicate by the count that we have synced the current bookmark file.
  ;; If an error has already occurred somewhere, the count will not be set, which is what we want.
  (setq bookmark-alist-modification-count 0))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg ALT-MSG.
;; 2. Insert code piecewise, to improve performance when saving `bookmark-alist'.
;;    (Do not let `pp' parse all of `bookmark-alist' at once.)
;; 3. Unless `bmkp-propertize-bookmark-names-flag', remove text properties from bookmark name and file name.
;; 4. Bind `print-circle' to t around pp, to record bookmark name with `bmkp-full-record' property.
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
          (when (or (not (> emacs-major-version 20)) ; Emacs 20.  Cannot use (not (boundp 'print-circle)).
                    (not bmkp-propertize-bookmark-names-flag))
            (set-text-properties 0 (length bname) () bname)
            (when fname (set-text-properties 0 (length fname) () fname)))
          (setcar bmk bname)
          (when (setq last-fname  (assq 'filename bmk)) (setcdr last-fname fname))
          (let ((print-circle  t)) (pp bmk (current-buffer))))
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
;; 2. Update `bmkp-current-bookmark-file' if OVERWRITE is non-nil.
;; 3. New doc string.
;; 4. Final msg says whether overwritten.
;; 5. Call `bmkp-bmenu-refresh-menu-list' at end.
;;
;;;###autoload
(defun bookmark-load (file &optional overwrite no-msg) ; Bound to `C-x p l'
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
bookmarks.  The value of `bmkp-current-bookmark-file' is changed to
FILE, so bookmarks will subsequently be saved to FILE.  The value
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
   (list (let ((bfile  (if (bmkp-same-file-p bmkp-current-bookmark-file bmkp-last-bookmark-file)
                           bookmark-default-file
                         bmkp-last-bookmark-file)))
           (bmkp-read-bookmark-file-name
            (if current-prefix-arg "Switch to bookmark file: " "Add bookmarks from file: ")
            (or (file-name-directory bfile) "~/")
            bfile
            'CONFIRM))
         current-prefix-arg))
  (setq file  (abbreviate-file-name (expand-file-name file)))
  (unless (file-readable-p file) (error "Cannot read bookmark file `%s'" file))
  (unless no-msg (bookmark-maybe-message "Loading bookmarks from `%s'..." file))
  (with-current-buffer (let ((enable-local-variables nil)) (find-file-noselect file))
    (goto-char (point-min))
    (bookmark-maybe-upgrade-file-format)
    (let ((blist  (bookmark-alist-from-buffer)))
      (unless (listp blist) (error "Invalid bookmark list in `%s'" file))
      (if overwrite
          (setq bmkp-last-bookmark-file            bmkp-current-bookmark-file
                bmkp-current-bookmark-file         file
                bookmark-alist                     blist
                bookmark-alist-modification-count  0)
        (bookmark-import-new-list blist)
        (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count)))
      (when (string-equal (abbreviate-file-name (expand-file-name bookmark-default-file)) file)
        (setq bookmarks-already-loaded  t))
      (bookmark-bmenu-surreptitiously-rebuild-list))
    (kill-buffer (current-buffer)))
  (unless no-msg (message "%s bookmark file `%s'" (if overwrite "Switched to" "Loaded") file))
  (let ((bmklistbuf  (get-buffer "*Bookmark List*")))
    (when bmklistbuf (with-current-buffer bmklistbuf (bmkp-bmenu-refresh-menu-list)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Added optional arg MSGP.  Show message if no annotation.
;; 2. Name buffer after the bookmark.
;; 3. MSGP means message if no annotation.
;; 4. Use `view-mode'.  `q' uses `quit-window'.
;; 5. Fit frame to buffer if `one-windowp'.
;; 6. Restore frame selection.
;;
(defun bookmark-show-annotation (bookmark &optional msgp)
  "Display the annotation for BOOKMARK.
If no annotation and MSGP is non-nil, show a no-annotation message."
  (let* ((bmk       (bookmark-get-bookmark bookmark))
         (bmk-name  (bookmark-name-from-full-record bmk))
         (ann       (bookmark-get-annotation bmk)))
    (if (not (and ann (not (string-equal ann ""))))
        (when msgp (message "Bookmark has no annotation"))
      (let ((oframe  (selected-frame)))
        (save-selected-window
          (pop-to-buffer (get-buffer-create (format "*`%s' Annotation*" bmk-name)))
          (let ((buffer-read-only  nil)) ; Because buffer might already exist, in view mode.
            (delete-region (point-min) (point-max))
            (insert (concat "Annotation for bookmark '" bmk-name "':\n\n"))
            (put-text-property (line-beginning-position -1) (line-end-position 1)
                               'face 'bmkp-heading)
            (insert ann))
          (goto-char (point-min))
          (view-mode-enter (cons (selected-window) (cons nil 'quit-window)))
          (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window)))
        (select-frame-set-input-focus oframe)))))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; 1. Use name `*Bookmark Annotations*', not `*Bookmark Annotation*'.
;; 2. Don't list bookmarks that have no annotation.
;; 3. Highlight bookmark names.  Don't indent annotations.  Add a blank line after each annotation.
;; 4. Use `view-mode'.  `q' uses `quit-window'.
;; 5. Fit frame to buffer if `one-windowp'.
;; 6. Restore frame selection.
;;
(defun bookmark-show-all-annotations ()
  "Display the annotations for all bookmarks."
  (let ((oframe  (selected-frame)))
    (save-selected-window
      (pop-to-buffer (get-buffer-create "*Bookmark Annotations*"))
      (let ((buffer-read-only  nil))    ; Because buffer might already exist, in view mode.
        (delete-region (point-min) (point-max))
        (dolist (full-record  bookmark-alist) ; (Could use `bmkp-annotated-alist-only' here instead.)
          (let ((ann  (bookmark-get-annotation full-record)))
            (when (and ann (not (string-equal ann "")))
              (insert (concat (bookmark-name-from-full-record full-record) ":\n"))
              (put-text-property (line-beginning-position 0) (line-end-position 0)
                                 'face 'bmkp-heading)
              (insert ann) (unless (bolp) (insert "\n\n")))))
        (goto-char (point-min))
        (view-mode-enter (cons (selected-window) (cons nil 'quit-window)))
        (when (fboundp 'fit-frame-if-one-window) (fit-frame-if-one-window))))
    (select-frame-set-input-focus oframe)))


;; REPLACES ORIGINAL in `bookmark.el'.
;;
;; Save menu-list state to `bmkp-bmenu-state-file'.
;;
(defun bookmark-exit-hook-internal ()   ; This goes on `kill-emacs-hook'.
  "Save currently defined bookmarks and perhaps bookmark menu-list state.
Run `bookmark-exit-hook', then save bookmarks if they were updated.
Then save menu-list state to file `bmkp-bmenu-state-file', but only if
that option is non-nil."
  (run-hooks 'bookmark-exit-hook)
  (when (and bookmark-alist (bookmark-time-to-save-p t)) (bookmark-save))
  (bmkp-save-menu-list-state))
 
;;(@* "Bookmark+ Functions (`bmkp-*')")
;;; Bookmark+ Functions (`bmkp-*') -----------------------------------

(defun bmkp-completing-read-lax (prompt &optional default alist pred hist)
  "Read a bookmark name, prompting with PROMPT.
Same as `bookmark-completing-read', but completion is lax."
  (unwind-protect
       (progn (define-key minibuffer-local-completion-map "\C-w" 'bookmark-yank-word)
              (define-key minibuffer-local-completion-map "\C-u" 'bookmark-insert-current-bookmark)
              (bmkp-completing-read-1 prompt default alist pred hist t))
    (define-key minibuffer-local-completion-map "\C-w" nil)
    (define-key minibuffer-local-completion-map "\C-u" nil)))

(defun bmkp-completing-read-1 (prompt default alist pred hist laxp)
  "Helper for `bookmark-completing-read(-lax)'.
LAXP non-nil means use lax completion."
  (bookmark-maybe-load-default-file)
  (setq alist  (or alist bookmark-alist))
  (if (and (not laxp)
           (listp last-nonmenu-event)
           (or (eq t bmkp-menu-popup-max-length)
               (and (integerp bmkp-menu-popup-max-length)
                    (< (length alist) bmkp-menu-popup-max-length))))
      (bookmark-menu-popup-paned-menu
       t prompt
       (if bmkp-sort-comparer           ; Test whether to sort, but always use `string-lessp'.
           (sort (bookmark-all-names alist) 'string-lessp)
         (bookmark-all-names alist)))
    (let* ((icicle-delete-candidate-object  (lambda (cand) ; For `S-delete' in Icicles.
                                              (bookmark-delete
                                               (icicle-transform-multi-completion cand))))
           (completion-ignore-case          bookmark-completion-ignore-case)
           (default                         default)
           (prompt                          (if default
                                                (concat prompt (format " (%s): " default))
                                              (concat prompt ": ")))
           (str                             (completing-read
                                             prompt alist pred (not laxp) nil
                                             (or hist 'bookmark-history) default)))
      (if (and (string-equal "" str) default) default str))))

(defun bmkp-jump-1 (bookmark display-function use-region-p)
  "Helper function for `bookmark-jump' commands.
BOOKMARK is a bookmark name (a string) or a bookmark record.
DISPLAY-FUNCTION is passed to `bookmark--jump-via'.
Non-nil USE-REGION-P means activate the region, if recorded."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (unless bookmark (error "No bookmark specified"))
  (bookmark-maybe-historicize-string (bookmark-name-from-full-record bookmark))
  (let ((bmkp-use-region  (if use-region-p (not bmkp-use-region) bmkp-use-region)))
    (bookmark--jump-via bookmark display-function)))

(defun bmkp-select-buffer-other-window (buffer)
  "Select BUFFER in another window.
If `bmkp-other-window-pop-to-flag' is non-nil, then use
`pop-to-buffer'.  Otherwise, use `switch-to-buffer-other-window'."
  (if bmkp-other-window-pop-to-flag
      (pop-to-buffer buffer t)
    (switch-to-buffer-other-window buffer)))  

(defun bmkp-maybe-save-bookmarks ()
  "Increment save counter and maybe save `bookmark-alist'."
  (setq bookmark-alist-modification-count  (1+ bookmark-alist-modification-count))
  (when (bookmark-time-to-save-p) (bookmark-save)))

;;;###autoload
(defun bmkp-edit-bookmark (bookmark &optional internalp) ; Bound to `C-x p E'
  "Edit BOOKMARK's name and file name, and maybe save them.
BOOKMARK is a bookmark name (a string) or a bookmark record.
With a prefix argument, edit the complete bookmark record (the
internal, Lisp form).
Return a list of the new bookmark name and new file name."
  (interactive
   (list (bookmark-completing-read
          (concat "Edit " (and current-prefix-arg "internal record for ") "bookmark")
          (bmkp-default-bookmark-name))
         current-prefix-arg))
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (if internalp
      (bmkp-edit-bookmark-record bookmark)
    (let* ((bookmark-name      (bookmark-name-from-full-record bookmark))
           (bookmark-filename  (bookmark-get-filename bookmark-name))
           (new-bmk-name       (read-from-minibuffer "New bookmark name: " nil nil nil nil
                                                     bookmark-name))
           (new-filename       (read-from-minibuffer "New file name (location): " nil nil nil nil
                                                     bookmark-filename)))
      (when (and (or (not (equal new-bmk-name "")) (not (equal new-filename "")))
                 (y-or-n-p "Save changes? "))
        (bookmark-rename bookmark-name new-bmk-name 'batch)
        (bookmark-set-filename new-bmk-name new-filename)
        ;; Change location for Dired too, but not if different from original file name (e.g. a cons).
        (let ((dired-dir  (bookmark-prop-get new-bmk-name 'dired-directory)))
          (when (and dired-dir (equal dired-dir bookmark-filename))
            (bookmark-prop-set new-bmk-name 'dired-directory new-filename)))
        (bmkp-maybe-save-bookmarks)
        (list new-bmk-name new-filename)))))

(define-derived-mode bmkp-edit-bookmark-record-mode emacs-lisp-mode
    "Edit Bookmark Record"
  "Mode for editing an internal bookmark record.
When you have finished composing, type \\[bmkp-edit-bookmark-record-send]."
  :group 'bookmark-plus)

;; This binding must be defined *after* the mode, so `bmkp-edit-bookmark-record-mode-map' is defined.
;; (Alternatively, we could use a `defvar' to define `bmkp-edit-bookmark-record-mode-map' before
;; calling `define-derived-mode'.)
(define-key bmkp-edit-bookmark-record-mode-map "\C-c\C-c" 'bmkp-edit-bookmark-record-send)

;;;###autoload
(defun bmkp-edit-bookmark-record (bookmark)
  "Edit the internal record for bookmark BOOKMARK.
When you have finished, Use `\\[bmkp-edit-bookmark-record-send]'.
BOOKMARK is a bookmark name (a string) or a bookmark record."
  (interactive (list (bookmark-completing-read "Edit internal record for bookmark"
                                               (bmkp-default-bookmark-name))))
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let* ((bmk-name  (bookmark-name-from-full-record bookmark))
         (bufname   (format "*Edit Bookmark `%s'*" bmk-name)))
    (with-output-to-temp-buffer bufname
      (princ
       (substitute-command-keys
        (concat ";; Edit the internal record for bookmark\n;;\n"
                ";; " bmk-name "\n;;\n"
                ";; Type \\<bmkp-edit-bookmark-record-mode-map>\
`\\[bmkp-edit-bookmark-record-send]' when done.\n;;\n"
                ";; NOTE: If you edit the bookmark *name* within the record, then\n"
                ";;       a new bookmark is created for the new name, and the\n"
                ";;       original (unedited) bookmark continues to exist as well.\n\n")))
      (let ((print-circle  t)) (pp bookmark))
      (goto-char (point-min)))
    (pop-to-buffer bufname)
    (buffer-enable-undo)
    (with-current-buffer (get-buffer bufname) (bmkp-edit-bookmark-record-mode))))

;;;###autoload
(defun bmkp-edit-bookmark-record-send (arg &optional force)
  "Use buffer contents as a bookmark record.
Lines beginning with `;;' are ignored.
With a prefix argument, do not update `time' or `visits' entries."
  (interactive "P")
  (unless (eq major-mode 'bmkp-edit-bookmark-record-mode)
    (error "Not in `bmkp-edit-bookmark-record-mode'"))
  (goto-char (point-min))
  (let ((bmk  (read (current-buffer))))
    (when (or force (bmkp-bookmark-type bmk) ; Must pass BMK, not BMK-NAME, since might be renamed.
              (and (interactive-p)
                   (or (y-or-n-p "Bookmard record not recognized as valid.  Save anyway? ")
                       (error "Canceled"))))
      (unless arg (bmkp-record-visit bmk t))
      (bookmark-store (bookmark-name-from-full-record bmk) (bookmark-get-bookmark-record bmk) nil)
      (when (interactive-p) (message "Updated bookmark file"))))
  (kill-buffer (current-buffer)))

(define-derived-mode bmkp-edit-tags-mode emacs-lisp-mode
    "Edit Bookmark Tags"
  "Mode for editing bookmark tags.
When you have finished composing, type \\[bmkp-edit-tags-send]."
  :group 'bookmark-plus)

;; This binding must be defined *after* the mode, so `bmkp-edit-tags-mode-map' is defined.
;; (Alternatively, we could use a `defvar' to define `bmkp-edit-tags-mode-map' before
;; calling `define-derived-mode'.)
(define-key bmkp-edit-tags-mode-map "\C-c\C-c" 'bmkp-edit-tags-send)

;;;###autoload
(defun bmkp-edit-tags (bookmark)        ; Bound to `C-x p t e'
  "Edit BOOKMARK's tags, and maybe save the result.
The edited value must be a list each of whose elements is either a
 string or a cons whose key is a string.
BOOKMARK is a bookmark name (a string) or a bookmark record."
  (interactive (list (bookmark-completing-read "Edit tags for bookmark" (bmkp-default-bookmark-name))))
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let* ((btags    (bmkp-get-tags bookmark))
         (bmkname  (bookmark-name-from-full-record bookmark))
         (edbuf    (format "*Edit Tags for Bookmark `%s'*" bmkname)))
    (setq bmkp-return-buffer  (current-buffer))
    (with-output-to-temp-buffer edbuf
      (princ
       (substitute-command-keys
        (concat ";; Edit tags for bookmark\n;;\n;; \"" bmkname "\"\n;;\n"
                ";; The edited value must be a list each of whose elements is\n"
                ";; either a string or a cons whose key is a string.\n;;\n"
                ";; DO NOT MODIFY THESE COMMENTS.\n;;\n"
                ";; Type \\<bmkp-edit-tags-mode-map>`\\[bmkp-edit-tags-send]' when done.\n\n")))
      (let ((print-circle  t)) (pp btags))
      (goto-char (point-min)))
    (pop-to-buffer edbuf)
    (buffer-enable-undo)
    (with-current-buffer (get-buffer edbuf) (bmkp-edit-tags-mode))))  

;;;###autoload
(defun bmkp-edit-tags-send ()
  "Use buffer contents as the internal form of a bookmark's tags.
DO NOT MODIFY the header comment lines, which begin with `;;'."
  (interactive)
  (unless (eq major-mode 'bmkp-edit-tags-mode) (error "Not in `bmkp-edit-tags-mode'"))
  (let (bname)
    (unwind-protect
         (let (tags bmk)
           (goto-char (point-min))
           (unless (search-forward ";; Edit tags for bookmark\n;;\n;; ")
             (error "Missing header in edit buffer"))
           (unless (stringp (setq bname  (read (current-buffer))))
             (error "Bad bookmark name in edit-buffer header"))
           (unless (setq bmk  (bookmark-get-bookmark bname)) (error "No such bookmark: `%s'" bname))
           (unless (bmkp-bookmark-type bmk) (error "Invalid bookmark"))
           (goto-char (point-min))
           (setq tags  (read (current-buffer)))
           (unless (listp tags) (error "Tags sexp is not a list of strings or an alist with string keys"))
           (bookmark-prop-set bmk 'tags tags)
           (setq bname  (bookmark-name-from-full-record bmk))
           (bmkp-record-visit bmk)      ; Not BATCH.
           (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
             (with-current-buffer (get-buffer "*Bookmark List*")
               (bmkp-refresh-menu-list bname))) ; To update display.
           (bmkp-maybe-save-bookmarks)
           (when (interactive-p) (message "Updated bookmark file with edited tags")))
      (kill-buffer (current-buffer)))
    (when bmkp-return-buffer
      (pop-to-buffer bmkp-return-buffer)
      (when (equal (buffer-name (current-buffer)) "*Bookmark List*")
        (bmkp-bmenu-goto-bookmark-named bname)))))

(defun bmkp-bookmark-type (bookmark)
  "Return the type of BOOKMARK or nil if no type is recognized.
Return nil if the bookmark record is not recognized (invalid).
See the code for the possible non-nil return values.
BOOKMARK is a bookmark name or a bookmark record."
  (condition-case nil
      (progn
        ;; If BOOKMARK is already a bookmark record, not a bookmark name, then we must use it.
        ;; If we used the name instead, then tests such as `bookmark-get-filename' would fail,
        ;; because they call `bookmark-get-bookmark', which, for a string, checks whether the
        ;; bookmark exists in `bookmark-alist'.  But we want to be able to use `bmkp-bookmark-type'
        ;; to get the type of any bookmark record, not necessarily one that is in `bookmark-alist'.
        (when (stringp bookmark) (setq bookmark  (bookmark-get-bookmark bookmark)))
        (let ((filep  (bookmark-get-filename bookmark)))
          (cond ((bmkp-sequence-bookmark-p bookmark)             'bmkp-sequence-bookmark-p)
                ((bmkp-function-bookmark-p bookmark)             'bmkp-function-bookmark-p)
                ((bmkp-variable-list-bookmark-p bookmark)        'bmkp-variable-list-bookmark-p)
                ((bmkp-url-bookmark-p bookmark)                  'bmkp-url-bookmark-p)
                ((bmkp-gnus-bookmark-p bookmark)                 'bmkp-gnus-bookmark-p)
                ((bmkp-desktop-bookmark-p bookmark)              'bmkp-desktop-bookmark-p)
                ((bmkp-bookmark-file-bookmark-p bookmark)        'bmkp-bookmark-file-bookmark-p)
                ((bmkp-bookmark-list-bookmark-p bookmark)        'bmkp-bookmark-list-bookmark-p)
                ((bmkp-man-bookmark-p bookmark)                  'bmkp-man-bookmark-p)
                ((bmkp-info-bookmark-p bookmark)                 'bmkp-info-bookmark-p)
                ((bookmark-get-handler bookmark)                 'bookmark-get-handler)
                ((bmkp-region-bookmark-p bookmark)               'bmkp-region-bookmark-p)
                ;; Make sure we test for remoteness before any other tests of the file itself
                ;; (e.g. `file-exists-p'). We do not want to prompt for a password etc.
                ((and filep (bmkp-file-remote-p filep))          'remote-file)
                ((and filep (file-directory-p filep))            'local-directory)
                (filep                                           'local-file)
                ((and (bmkp-get-buffer-name bookmark)
                      (or (not filep)
                          (equal filep bmkp-non-file-filename))) 'buffer)
                (t                                               nil))))
    (error nil)))

(defun bmkp-record-visit (bookmark &optional batch)
  "Update the data recording a visit to BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
This increments the `visits' entry and sets the `time' entry to the
current time.  If either an entry is not present, it is added (with 0
value for `visits').
With non-nil optional arg BATCH, do not rebuild the menu list."
  (let ((vis  (bookmark-prop-get bookmark 'visits)))
    (if vis  (bookmark-prop-set bookmark 'visits (1+ vis))  (bookmark-prop-set bookmark 'visits 0))
    (bookmark-prop-set bookmark 'time (current-time))
    (unless batch (bookmark-bmenu-surreptitiously-rebuild-list))
    (let ((bookmark-save-flag  nil))  (bmkp-maybe-save-bookmarks))))

(defun bmkp-default-bookmark-name (&optional alist)
  "Default bookmark name.  See option `bmkp-default-bookmark-name'.
Non-nil ALIST means return nil unless the default names a bookmark in
ALIST."
  (let ((bname  (if (equal (buffer-name (current-buffer)) "*Bookmark List*")
                    (bookmark-bmenu-bookmark)
                  (if (fboundp 'bmkp-default-lighted)
                      (if (eq 'highlighted bmkp-default-bookmark-name)
                          (or (bmkp-default-lighted) bookmark-current-bookmark)
                        (or bookmark-current-bookmark (bmkp-default-lighted)))
                    bookmark-current-bookmark))))
    (when (and bname alist)
      (let ((bookmark-alist  alist))
        (setq bname  (bookmark-name-from-full-record (bookmark-get-bookmark bname)))))
    bname))

(defun bmkp-buffer-names ()
  "Buffer names used by existing bookmarks that really have buffers.
This excludes buffers for bookmarks such as desktops that are not
really associated with a buffer."
  (let ((bufs  ())
        buf)
    (dolist (bmk  bookmark-alist)
      (when (and (not (bmkp-desktop-bookmark-p        bmk))
                 (not (bmkp-bookmark-file-bookmark-p  bmk))
                 (not (bmkp-sequence-bookmark-p       bmk))
                 (not (bmkp-function-bookmark-p       bmk))
                 (not (bmkp-variable-list-bookmark-p  bmk))
                 (setq buf  (bmkp-get-buffer-name     bmk)))
        (add-to-list 'bufs buf)))
    bufs))

(defun bmkp-file-names ()
  "The absolute file names used by the existing bookmarks.
This excludes the pseudo file name `bmkp-non-file-filename'."
  (let ((files  ())
        file)
    (dolist (bmk  bookmark-alist)
      (when (and (setq file  (bookmark-get-filename bmk))  (not (equal file bmkp-non-file-filename)))
        (add-to-list 'files file)))
    files))

;;;###autoload
(defun bmkp-send-bug-report ()          ; Not bound
  "Send a bug report about a Bookmark+ problem."
  (interactive)
  (browse-url (format (concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
Bookmark+ bug: \
&body=Describe bug below, using a precise recipe that starts with `emacs -Q' or `emacs -q'.  \
Be sure to mention the `Update #' from header of the particular Bookmark+ file header.\
%%0A%%0AEmacs version: %s")
                      (emacs-version))))

;;;###autoload
(defun bmkp-toggle-bookmark-set-refreshes () ; Not bound
  "Toggle `bookmark-set' refreshing `bmkp-latest-bookmark-alist'.
Add/remove `bmkp-refresh-latest-bookmark-list' to/from
`bmkp-after-set-hook'."
  (interactive)
  (if (member 'bmkp-refresh-latest-bookmark-list bmkp-after-set-hook)
      (remove-hook 'bmkp-after-set-hook 'bmkp-refresh-latest-bookmark-list)
    (add-hook 'bmkp-after-set-hook 'bmkp-refresh-latest-bookmark-list)))

(defun bmkp-refresh-latest-bookmark-list ()
  "Refresh `bmkp-latest-bookmark-alist' to reflect `bookmark-alist'."
  (setq bmkp-latest-bookmark-alist  (if bmkp-bmenu-filter-function
                                        (funcall bmkp-bmenu-filter-function)
                                      bookmark-alist)))

;;;###autoload
(defun bmkp-toggle-saving-menu-list-state () ; Bound to `M-l' in bookmark list
  "Toggle the value of option `bmkp-bmenu-state-file'.
Tip: You can use this before quitting Emacs, to not save the state.
If the initial value of `bmkp-bmenu-state-file' is nil, then this
command has no effect."
  (interactive)
  (unless (or bmkp-last-bmenu-state-file bmkp-bmenu-state-file)
    (error "Cannot toggle: initial value of `bmkp-bmenu-state-file' is nil"))
  (setq bmkp-last-bmenu-state-file  (prog1 bmkp-bmenu-state-file
                                      (setq bmkp-bmenu-state-file  bmkp-last-bmenu-state-file)))
  (message (if bmkp-bmenu-state-file
               "Autosaving of bookmark list state is now ON"
             "Autosaving of bookmark list state is now OFF")))

;;;###autoload
(defun bmkp-save-menu-list-state ()     ; Used in `bookmark-exit-hook-internal'.
  "Save menu-list state, unless not saving or list has not yet been shown.
The state is saved to the value of `bmkp-bmenu-state-file'."
  (interactive)
  (when (and (not bmkp-bmenu-first-time-p) bmkp-bmenu-state-file)
    (let ((config-list
           `((last-sort-comparer                    . ,bmkp-sort-comparer)
             (last-reverse-sort-p                   . ,bmkp-reverse-sort-p)
             (last-reverse-multi-sort-p             . ,bmkp-reverse-multi-sort-p)
             (last-latest-bookmark-alist            . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-latest-bookmark-alist))
             (last-bmenu-omitted-bookmarks          . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-omitted-bookmarks))
             (last-bmenu-marked-bookmarks           . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-marked-bookmarks))
             (last-bmenu-filter-function            . ,bmkp-bmenu-filter-function)
             (last-bmenu-filter-pattern             . ,bmkp-bmenu-filter-pattern)
             (last-bmenu-title                      . ,bmkp-bmenu-title)
             (last-bmenu-bookmark                   . ,(and (get-buffer "*Bookmark List*")
                                                            (with-current-buffer
                                                                (get-buffer "*Bookmark List*")
                                                              (bookmark-bmenu-bookmark))))
             (last-specific-buffer                  . ,bmkp-last-specific-buffer)
             (last-specific-file                    . ,bmkp-last-specific-file)
             (last-bmenu-toggle-filenames           . ,bookmark-bmenu-toggle-filenames)
             (last-bmenu-before-hide-marked-alist   . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-before-hide-marked-alist))
             (last-bmenu-before-hide-unmarked-alist . ,(bmkp-maybe-unpropertize-bookmark-names
                                                        bmkp-bmenu-before-hide-unmarked-alist))
             (last-bookmark-file                    . ,(convert-standard-filename
                                                        (expand-file-name
                                                         bmkp-current-bookmark-file))))))
      (with-current-buffer (get-buffer-create " *Menu-List State*")
        (goto-char (point-min))
        (delete-region (point-min) (point-max))
        (let ((print-length  nil)
              (print-level   nil)
              (print-circle  t))
          (pp config-list (current-buffer)))
        (condition-case nil
            (write-region (point-min) (point-max) bmkp-bmenu-state-file)
          (file-error (message "Cannot write `%s'" bmkp-bmenu-state-file)))
        (kill-buffer (current-buffer))))))

;;;###autoload
(defun bmkp-toggle-saving-bookmark-file () ; Bound to `M-~' in bookmark list
  "Toggle the value of option `bookmark-save-flag'.
If the initial value of `bookmark-save-flag' is nil, then this
command has no effect."
  (interactive)
  (unless (or bmkp-last-save-flag-value bookmark-save-flag)
    (error "Cannot toggle: initial value of `bookmark-save-flag' is nil"))
  (setq bmkp-last-save-flag-value  (prog1 bookmark-save-flag
                                     (setq bookmark-save-flag  bmkp-last-save-flag-value)))
  (message (if bookmark-save-flag
               "Autosaving of current bookmark file is now ON"
             "Autosaving of current bookmark file is now OFF")))

;;;###autoload
(defun bmkp-make-function-bookmark (bookmark-name function) ; Not bound
  "Create a bookmark that invokes FUNCTION when \"jumped\" to.
You are prompted for the bookmark name and the name of the function.
Returns the new bookmark (internal record)."
  (interactive (list (read-string "Bookmark: ") (completing-read "Function: " obarray 'functionp)))
  (bookmark-store bookmark-name `((filename . ,bmkp-non-file-filename)
                                  (position . 0)
                                  (function . ,(read function))
                                  (handler  . bmkp-jump-function))
                  nil)
  (let ((new  (bookmark-get-bookmark bookmark-name 'noerror)))
    (unless (memq new bmkp-latest-bookmark-alist)
      (setq bmkp-latest-bookmark-alist  (cons new bmkp-latest-bookmark-alist)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    new))

;;;###autoload
(defun bmkp-switch-bookmark-file (file &optional no-msg) ; Bound to `L' in bookmark list
  "Switch to a different bookmark file, FILE.
Replace all currently existing bookmarks with the newly loaded
bookmarks.  Change the value of `bmkp-current-bookmark-file' to FILE,
so bookmarks will subsequently be saved to FILE.

`bookmark-default-file' is unaffected, so your next Emacs session will
still use `bookmark-default-file' for the initial set of bookmarks."
  (interactive
   (list
    (let ((bfile  (if (bmkp-same-file-p bmkp-current-bookmark-file
                                        bmkp-last-bookmark-file)
                      bookmark-default-file
                    bmkp-last-bookmark-file)))
      (bmkp-read-bookmark-file-name "Switch to bookmark file: "
                                    (or (file-name-directory bfile) "~/")
                                    bfile
                                    'CONFIRM))))
  (bookmark-load file t no-msg))

;;;###autoload
(defun bmkp-switch-to-last-bookmark-file (&optional no-msg) ; Not bound
  "Switch back to the last-used bookmarkfile.
Replace all currently existing bookmarks with those newly loaded from
the last-used file.  Swap the values of `bmkp-last-bookmark-file' and
`bmkp-current-bookmark-file'."
  (interactive)
  (bookmark-load (or bmkp-last-bookmark-file bookmark-default-file) t no-msg))

;;;###autoload
(defun bmkp-use-bookmark-file-create (file) ; Not bound
  "Switch current bookmark file to FILE, creating it if it does not exist.
Interactively, you are prompted for the file name.  The default is
`.emacs.bmk' in the current directory, but you can enter any file
name, anywhere.

If there is no file with the name you provide then a new, an empty
bookmark file with that name is created.

You are prompted to confirm the bookmark-file switch.

Returns FILE."
  (interactive (list (bmkp-read-bookmark-file-name)))
  (unless (file-readable-p file) (bmkp-empty-file file))
  (when (y-or-n-p (format "Use `%s' as the current bookmark file? " file))
    (bmkp-switch-bookmark-file file))
  file)

(defun bmkp-read-bookmark-file-name (&optional prompt dir default-filename require-match)
  "Read and return an (absolute) bookmark file name.
PROMPT is the prompt to use (default: \"Use bookmark file: \").
The other args are the same as for `read-file-name'."
  (let ((insert-default-directory  t))
    (expand-file-name
     (read-file-name (or prompt "Use bookmark file: ")
                     dir
                     (or default-filename
                         (if (> emacs-major-version 22)
                             (list ".emacs.bmk" bookmark-default-file)
                           ".emacs.bmk"))
                     require-match))))

;;;###autoload
(defun bmkp-empty-file (file)           ; Bound to `C-x p 0'
  "Empty the bookmark file FILE, or create FILE (empty) if it does not exist.
In either case, FILE will become an empty bookmark file.  Return FILE.

NOTE: If FILE already exists and you confirm emptying it, no check is
      made that it is in fact a bookmark file before emptying it.
      It is simply replaced by an empty bookmark file and saved.

This does NOT also make FILE the current bookmark file.  To do that,
use `\\[bmkp-switch-bookmark-file]' (`bmkp-switch-bookmark-file')."
  (interactive (list (read-file-name "Create empty bookmark file: " "~/")))
  (setq file  (expand-file-name file))
  (bookmark-maybe-load-default-file)
  (when (and (file-exists-p file)
             (not (y-or-n-p (format "CONFIRM: Empty the existing file `%s'? " file))))
    (error "OK, cancelled"))
  (let ((bookmark-alist  ()))
    (bookmark-write-file file (if (file-exists-p file)
                                  "Emptying bookmark file `%s'..."
                                "Creating new, empty bookmark file `%s'...")))
  file)

;;;###autoload
(defun bmkp-crosshairs-highlight ()     ; Not bound
  "Call `crosshairs-highlight', unless the region is active.
You can add this to hook `bookmark-after-jump-hook'.
You need library `crosshairs.el' to use this command."
  (interactive)
  (when (> emacs-major-version 21)      ; No-op for Emacs 20-21.
    (unless (condition-case nil (require 'crosshairs nil t) (error nil))
      (error "You need library `crosshairs.el' to use this command"))
    (unless mark-active
      (let ((crosshairs-overlay-priority  (and (boundp 'bmkp-light-priorities)
                                               (1+ (apply #'max
                                                          (mapcar #'cdr bmkp-light-priorities))))))
        (crosshairs-highlight)))))

;;;###autoload
(defun bmkp-choose-navlist-from-bookmark-list (bookmark-name &optional alist) ; Bound to `C-x p B'
  "Choose a bookmark-list bookmark and set the bookmark navigation list.
The navigation-list variable, `bmkp-nav-alist', is set to the list of
bookmarks that would be displayed by `bookmark-bmenu-list' (`C-x r l')
for the chosen bookmark-list bookmark, sorted and filtered as
appropriate.

Instead of choosing a bookmark-list bookmark, you can choose the
pseudo-bookmark `CURRENT *Bookmark List*'.  The bookmarks used for the
navigation list are those that would be currently shown in the
`*Bookmark List*' (even if the list is not currently displayed)."
  (interactive
   (let ((bookmark-alist  (cons (bmkp-current-bookmark-list-state) (bmkp-bookmark-list-alist-only))))
     (list (bmkp-read-bookmark-for-type "bookmark-list " bookmark-alist nil nil
                                        'bmkp-bookmark-list-history "Choose ")
           bookmark-alist)))
  (let ((state  (let ((bookmark-alist  (or alist (cons (bmkp-current-bookmark-list-state)
                                                       (bmkp-bookmark-list-alist-only)))))
                  (bookmark-prop-get bookmark-name 'bookmark-list))))
    (let ((bmkp-sort-comparer               (cdr (assq 'last-sort-comparer              state)))
          (bmkp-reverse-sort-p              (cdr (assq 'last-reverse-sort-p             state)))
          (bmkp-reverse-multi-sort-p        (cdr (assq 'last-reverse-multi-sort-p       state)))
          (bmkp-bmenu-omitted-bookmarks     (cdr (assq 'last-bmenu-omitted-bookmarks    state)))
          (bmkp-bmenu-filter-function       (cdr (assq 'last-bmenu-filter-function      state)))
          (bmkp-bmenu-filter-pattern        (or (cdr (assq 'last-bmenu-filter-pattern   state)) ""))
          (bmkp-bmenu-title                 (cdr (assq 'last-bmenu-title                state)))
          (bookmark-bmenu-toggle-filenames  (cdr (assq 'last-bmenu-toggle-filenames     state))))
      (setq bmkp-nav-alist             (bmkp-sort-omit
                                        (if bmkp-bmenu-filter-function
                                            (funcall bmkp-bmenu-filter-function)
                                          (if (string= "CURRENT *Bookmark List*" bookmark-name)
                                              (or bmkp-latest-bookmark-alist bookmark-alist)
                                            bookmark-alist))
                                        (and (not (eq bmkp-bmenu-filter-function
                                                      'bmkp-omitted-alist-only))
                                             bmkp-bmenu-omitted-bookmarks))
            bmkp-current-nav-bookmark  (car bmkp-nav-alist))))
  (message "Bookmark navigation list is now %s"
           (if (and (string= "CURRENT *Bookmark List*" bookmark-name)
                    (not (get-buffer "*Bookmark List*")))
               "the global bookmark list"
             (format "`%s'" bookmark-name))))

(defun bmkp-current-bookmark-list-state ()
  "Pseudo-bookmark for the current `*Bookmark List*' state."
  (bookmark-bmenu-surreptitiously-rebuild-list)
  (cons "CURRENT *Bookmark List*" (bmkp-make-bookmark-list-record)))

;;;###autoload
(defun bmkp-choose-navlist-of-type (type) ; Bound to `C-x p :'
  "Set the bookmark navigation list to the bookmarks of a type you choose.
The pseudo-type `any' sets the navigation list to all bookmarks.
This sets variable `bmkp-nav-alist'."
  (interactive (let ((completion-ignore-case  t)
                     (type                    (completing-read "Type: "
                                                               (cons '("any" . bookmark-history)
                                                                     bmkp-types-alist)
                                                               nil t nil nil "any")))
                 (list type)))
  (setq bmkp-nav-alist  (if (equal "any" type)
                            bookmark-alist
                          (funcall (intern (format "bmkp-%s-alist-only" type)))))
  (unless bmkp-nav-alist (error "No bookmarks"))
  (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
  (message "Bookmark navigation list is now %s"
           (if (equal "any" type) "all bookmarks" (format "for type `%s'" type))))

(defun bmkp-autonamed-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a (valid) autonamed bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (if (not bookmark)
      nil
    (string-match (format bmkp-autoname-format ".*")
                  (bookmark-name-from-full-record bookmark))))

(defun bmkp-autonamed-bookmark-for-buffer-p (bookmark buffer-name)
  "Return non-nil if BOOKMARK is a (valid) autonamed bookmark for BUFFER.
BOOKMARK is a bookmark name or a bookmark record.
BUFFER-NAME is a string matching the buffer-name part of an autoname."
  (setq bookmark  (bookmark-get-bookmark bookmark 'NOERROR))
  (if (not bookmark)
      nil
    (string-match (format bmkp-autoname-format (regexp-quote buffer-name))
                  (bookmark-name-from-full-record bookmark))))

(defun bmkp-update-autonamed-bookmark (bookmark)
  "Update the name and position of the autonamed BOOKMARK at point.
BOOKMARK is a bookmark name or a bookmark record.
Return the updated BOOKMARK: If input was a bookmark name, then return
 then new name, else the new (full) bookmark.
It is a good idea to set BOOKMARK to the result of this call."
  (let ((namep  (stringp bookmark)))
    (setq bookmark  (bookmark-get-bookmark bookmark))
    (bookmark-set-position bookmark (point))
    ;; Autonamed bookmarks do not have regions.  Update `end-position' to be the same as `position'.
    (when (bmkp-get-end-position bookmark)
      (bookmark-prop-set bookmark 'end-position (point)))
    (let ((newname  (funcall bmkp-autoname-bookmark-function (point))))
      (bookmark-rename (bookmark-name-from-full-record bookmark) newname 'batch)
      (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
        (with-current-buffer (get-buffer "*Bookmark List*")
          (bmkp-refresh-menu-list (bookmark-name-from-full-record bookmark)))) ; So display new name.
      (bmkp-maybe-save-bookmarks))
    (if namep (bookmark-name-from-full-record bookmark) bookmark))) ; Return updated bookmark or name.

;;;###autoload
(defun bmkp-this-buffer-bmenu-list ()   ; Bound to `C-x p .'
  "Show the bookmark list just for bookmarks for the current buffer.
Set `bmkp-last-specific-buffer' to the current buffer name."
  (interactive)
  (setq bmkp-last-specific-buffer   (buffer-name)
        bmkp-bmenu-filter-function  'bmkp-last-specific-buffer-alist-only
        bmkp-bmenu-title            (format "Buffer `%s' Bookmarks" bmkp-last-specific-buffer))
  (let ((bookmark-alist         (funcall bmkp-bmenu-filter-function))
        (bmkp-bmenu-state-file  nil))   ; Prevent restoring saved state.
    (unless bookmark-alist (error "No bookmarks for buffer `%s'" bmkp-last-specific-buffer))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (pop-to-buffer (get-buffer-create "*Bookmark List*"))
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                               (format "Only bookmarks for buffer `%s' are shown"
                                       bmkp-last-specific-buffer)))
  (raise-frame))

;;;###autoload
(defun bmkp-navlist-bmenu-list ()       ; Bound to `C-x p N'
  "Show the bookmark list just for bookmarks from the navigation list."
  (interactive)
  (unless bmkp-nav-alist
    (bookmark-maybe-load-default-file)
    (setq bmkp-nav-alist  bookmark-alist)
    (unless bmkp-nav-alist (error "No bookmarks"))
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
    (message "Bookmark navigation list is now the global bookmark list") (sit-for 2))
  (setq bmkp-bmenu-title  "Current Navlist Bookmarks")
  (let ((bookmark-alist         bmkp-nav-alist)
        (bmkp-bmenu-state-file  nil))   ; Prevent restoring saved state.
    (unless bookmark-alist (error "No bookmarks"))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (pop-to-buffer (get-buffer-create "*Bookmark List*"))
    (bookmark-bmenu-list 'filteredp))
  (when (interactive-p)
    (bmkp-msg-about-sort-order (bmkp-current-sort-order)
                               "Only bookmarks for the navigation list are shown"))
  (raise-frame))

(defun bmkp-completing-read-buffer-name (&optional no-default-p)
  "Read the name of a buffer associated with a bookmark.
The candidates are the buffers in `bmkp-buffer-names'.
Non-nil NO-DEFAULT-P means provide no default value.  Used when
 called in a loop, to let the user exit using empty input.
If NO-DEFAULT-P is nil, then the default is the current buffer's name,
 or the value of `bmkp-last-specific-buffer' if the current buffer has
 no bookmarks."
  (bookmark-maybe-load-default-file)
  (completing-read "Buffer: " (mapcar #'list (bmkp-buffer-names)) nil t nil 'buffer-name-history
                   (and (not no-default-p)
                        (if (member (buffer-name) (bmkp-buffer-names))
                            (buffer-name)
                          bmkp-last-specific-buffer))))

(defun bmkp-completing-read-file-name (&optional no-default-p)
  "Read the name of a file associated with a bookmark.
The candidates are the absolute file names in `bmkp-file-names'.
Non-nil NO-DEFAULT-P means provide no default value.  Used when
 called in a loop, to let the user exit using empty input.
If NO-DEFAULT-P is nil, then the default is the current buffer's file
 name, if any, or the value of `bmkp-last-specific-file' if the
 current buffer has no associated file or the file has no bookmarks."
  (bookmark-maybe-load-default-file)
  (let ((completion-ignore-case  (if (boundp 'read-file-name-completion-ignore-case)
                                     read-file-name-completion-ignore-case
                                   (memq system-type '(ms-dos windows-nt darwin cygwin)))))
    (completing-read "File: " (mapcar #'list (bmkp-file-names)) nil t nil 'file-name-history
                     (and (not no-default-p)
                          (let ((file  (buffer-file-name)))
                            (if (and file (member file (bmkp-file-names)))
                                file
                              bmkp-last-specific-file))))))

(defun bmkp-refresh-menu-list (&optional bookmark)
  "Refresh (revert) the bookmark list (\"menu list\").
This brings the displayed list up to date.  It does not change the
current filtering or sorting of the displayed list.
Non-nil optional arg BOOKMARK means move cursor to BOOKMARK's line."
  (let ((bookmark-alist  (if bmkp-bmenu-filter-function
                             (funcall bmkp-bmenu-filter-function)
                           bookmark-alist)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)
    (when bookmark
      (with-current-buffer (get-buffer "*Bookmark List*")
        (bmkp-bmenu-goto-bookmark-named bookmark)
        (let ((bmenu-win  (get-buffer-window (current-buffer) 0)))
          (when bmenu-win (set-window-point bmenu-win (point))))))))

;;;###autoload
(defun bmkp-unomit-all ()               ; Bound to `O U' in bookmark list
  "Remove all bookmarks from the list of omitted bookmarks.
All bookmarks will henceforth be available for display."
  (interactive)
  (unless bmkp-bmenu-omitted-bookmarks (error "No omitted bookmarks to UN-omit"))
  (message "UN-omitting ALL omitted bookmarks...")
  (let ((count  0))
    (dolist (bmk-name  bmkp-bmenu-omitted-bookmarks)
      (setq bmkp-bmenu-omitted-bookmarks  (bmkp-delete-bookmark-name-from-list
                                           bmk-name bmkp-bmenu-omitted-bookmarks)
            count                         (1+ count)))
    (bookmark-bmenu-surreptitiously-rebuild-list)
    (message "UN-omitted %d bookmarks" count))
  (when (equal (buffer-name (current-buffer)) "*Bookmark List*") (bmkp-bmenu-show-all))
  (when (and (fboundp 'fit-frame-if-one-window)
             (equal (buffer-name (current-buffer)) "*Bookmark List*"))
    (fit-frame-if-one-window)))

(defun bmkp-omitted-alist-only ()
  "`bookmark-alist', filtered to retain only the omitted bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-omitted-bookmark-p bookmark-alist))

(defun bmkp-omitted-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an omitted bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (unless (stringp bookmark) (setq bookmark  (bookmark-name-from-full-record bookmark)))
  (bmkp-bookmark-name-member bookmark bmkp-bmenu-omitted-bookmarks))


;;(@* "Search-and-Replace Locations of Marked Bookmarks")
;;  *** Search-and-Replace Locations of Marked Bookmarks ***

(when (> emacs-major-version 22)
  (defvar bmkp-isearch-bookmarks nil
    "Bookmarks whose locations are to be incrementally searched.")

  (defun bmkp-isearch-next-bookmark-buffer (&optional bookmark wrap)
    "Return the next buffer in a series of bookmark buffers.
Used as a value for `multi-isearch-next-buffer-function', for Isearch
of multiple bookmarks.

Variable `bmkp-isearch-bookmarks' is a list of bookmarks.  Each
bookmark in the list is visited by `bookmark--jump-via', and the
corresponding bookmark buffer is returned."
    (let ((bookmarks  (if isearch-forward bmkp-isearch-bookmarks (reverse bmkp-isearch-bookmarks))))
      (bookmark--jump-via
       (if wrap
           (car bookmarks)
         (let ((this-bmk  (catch 'bmkp-isearch-next-bookmark-buffer
                            (dolist (bmk  bookmarks)
                              (when (if (bmkp-get-buffer-name bmk)
                                        (equal (bmkp-get-buffer-name bmk) (buffer-name))
                                      (equal (bookmark-get-filename bmk) (buffer-file-name)))
                                (throw 'bmkp-isearch-next-bookmark-buffer bmk)))
                            (car bookmarks))))
           (cadr (member this-bmk bookmarks))))
       'ignore)
      (current-buffer)))

  (defun bmkp-isearch-bookmarks (bookmarks)
    "Start multi-bookmark Isearch on BOOKMARKS."
    (let ((multi-isearch-next-buffer-function  'bmkp-isearch-next-bookmark-buffer)
          (bmkp-isearch-bookmarks              bookmarks))
      (bookmark-jump (car bookmarks))
      (goto-char (if isearch-forward (point-min) (point-max)))
      (isearch-forward)))

  (defun bmkp-isearch-bookmarks-regexp (bookmarks)
    "Start multi-bookmark regexp Isearch on BOOKMARKS."
    (let ((multi-isearch-next-buffer-function  'bmkp-isearch-next-bookmark-buffer)
          (bmkp-isearch-bookmarks              bookmarks))
      (bookmark-jump (car bookmarks))
      (goto-char (if isearch-forward (point-min) (point-max)))
      (isearch-forward-regexp))))


;;(@* "Tags")
;;  *** Tags ***

(defun bmkp-get-tags (bookmark)
  "Return the `tags' entry for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'tags))

(defun bmkp-get-tag-value (bookmark tag &optional msgp)
  "Return value of BOOKMARK's tag TAG.
BOOKMARK is a bookmark name or a bookmark record.
TAG is a string.
Return nil if BOOKMARK has no such TAG or if TAG has no value."
  (assoc-default tag (bmkp-get-tags bookmark)))

(defun bmkp-has-tag-p (bookmark tag &optional msgp)
  "Return non-nil if BOOKMARK is tagged with TAG.
BOOKMARK is a bookmark name or a bookmark record.
TAG is a string."
  (assoc-default tag (bmkp-get-tags bookmark) nil t))

;; NOT USED currently - we use `bmkp-read-tags-completing' instead.
(defun bmkp-read-tags ()
  "Read tags one by one, and return them as a list."
  (let ((tag    (read-string "Tag (RET for each, empty input to finish): "))
        (btags  ()))
    (while (not (string= "" tag))
      (push tag btags)
      (setq tag  (read-string "Tag: ")))
    btags))

(defun bmkp-read-tag-completing (&optional prompt candidate-tags require-match update-tags-alist-p)
  "Read a tag with completion, and return it as a string.
PROMPT is the prompt string.  If nil, then use \"Tag: \".
CANDIDATE-TAGS is an alist of tags to use for completion.
 If nil, then all tags from all bookmarks are used for completion.
 The set of all tags is taken from variable `bmkp-tags-alist'.
REQUIRE-MATCH is passed to `completing-read'.
Non-nil UPDATE-TAGS-ALIST-P means update var `bmkp-tags-alist'."
  (bookmark-maybe-load-default-file)
  (let ((cand-tags  (copy-sequence
                     (or candidate-tags
                         (and (not update-tags-alist-p) bmkp-tags-alist) ; Use cached list.
                         (bmkp-tags-list))))) ; Update the cache.
    (completing-read (or prompt "Tag: ") cand-tags nil require-match nil 'bmkp-tag-history)))

(defun bmkp-read-tags-completing (&optional candidate-tags require-match update-tags-alist-p)
  "Read tags with completion, and return them as a list of strings.
Reads tags one by one, until you hit `RET' twice consecutively.
CANDIDATE-TAGS is an alist of tags to use for completion.
 If nil, then all tags from all bookmarks are used for completion.
 The set of all tags is taken from variable `bmkp-tags-alist'.
REQUIRE-MATCH is passed to `completing-read'.
Non-nil UPDATE-TAGS-ALIST-P means update var `bmkp-tags-alist'."
  (bookmark-maybe-load-default-file)
  (let ((cands    ())
        (btags    ())
        (prompt1  "Tag (RET for each, empty input to finish): ")
        (prompt2  "Tag: ")
        tag old-tag)
    ;; Make a new candidates alist, with just one entry per tag name.  The original cdr is discarded.
    (dolist (full-tag  (or candidate-tags
                           (and (not update-tags-alist-p) bmkp-tags-alist) ; Use cached list.
                           (bmkp-tags-list)))
      (add-to-list 'cands (list (if (consp full-tag) (car full-tag) full-tag))))
    (setq tag    (completing-read prompt1 cands nil require-match nil 'bmkp-tag-history)
          cands  (delete (assoc tag cands) cands)) ; Tag read is no longer a candidate.
    (while (not (string= "" tag))
      (if (member tag btags)            ; User can enter it more than once, if not REQUIRE-MATCH.
          (message "Tag `%s' already included" tag)
        (push tag btags))               ; But we only add it once.
      (setq tag    (completing-read prompt2 cands nil require-match nil 'bmkp-tag-history)
            cands  (delete (assoc tag cands) cands)))
    (nreverse btags)))

;;;###autoload
(defun bmkp-list-all-tags (fullp)       ; Bound to `T l' in bookmark list, `C-x p t l' elsewhere
  "List all tags used for any bookmarks.
With a prefix argument, list the full alist of tags.
Otherwise, list only the tag names.

Note that when the full alist is shown, the same tag name will appear
once for each of its different values.

Show list in minibuffer or, if not enough space, buffer `*All Tags*'."
  (interactive "P")
  (require 'pp)
  (pp-display-expression (bmkp-tags-list (not fullp)) "*All Tags"))
  
(defun bmkp-tags-list (&optional names-only-p)
  "Current list of all tags, from all bookmarks.
Non-nil NAMES-ONLY-P means return a list of only the tag names.
Otherwise, return an alist of the full tags and set variable
`bmkp-tags-alist' to that alist, as a cache."
  (bookmark-maybe-load-default-file)
  (let ((tags  ())
        bmk-tags)
    (dolist (bmk  bookmark-alist)
      (setq bmk-tags  (bmkp-get-tags bmk))
      (dolist (tag  bmk-tags)
        (add-to-list 'tags (if names-only-p (bmkp-tag-name tag) (bmkp-full-tag tag)))))
    (unless names-only-p (setq bmkp-tags-alist  tags))
    tags))

(defun bmkp-tag-name (tag)
  "Name of TAG.  If TAG is an atom, then TAG, else (car TAG)."
  (if (atom tag) tag (car tag)))

(defun bmkp-full-tag (tag)
  "Full cons entry for TAG.  If TAG is a cons, then TAG, else (list TAG)."
  (if (consp tag) tag (list tag)))

;; `T 0' in bookmark list, `C-x p t 0' elsewhere.
;;;###autoload
(defun bmkp-remove-all-tags (bookmark &optional msgp no-cache-update-p)
  "Remove all tags from BOOKMARK.
Non-nil optional arg MSGP means display a message about the removal.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'msg))
  (when (and msgp (null (bmkp-get-tags bookmark))) (error "Bookmark has no tags to remove"))
  (let ((nb-removed  (and (interactive-p) (length (bmkp-get-tags bookmark)))))
    (bookmark-prop-set bookmark 'tags ())
    (unless no-cache-update-p (bmkp-tags-list)) ; Update the tags cache.
    (bmkp-maybe-save-bookmarks)
    (when (and msgp nb-removed) (message "%d tags removed" nb-removed)))
  (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
    (with-current-buffer (get-buffer "*Bookmark List*")
      (bmkp-refresh-menu-list bookmark)))) ; So the `t' markers are removed.

;; `T +' in bookmark list, `C-x p t + b' elsewhere (`b' for bookmark)
;;;###autoload
(defun bmkp-add-tags (bookmark tags &optional msgp no-cache-update-p)
  "Add TAGS to BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
Completion for the bookmark name is strict.
Completion for tags is lax: you are not limited to existing tags.

TAGS is a list of strings.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags added."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name))
                     (bmkp-read-tags-completing)
                     'msg))
  (let* ((newtags  (copy-alist (bmkp-get-tags bookmark)))
         (olen     (length newtags)))
    (dolist (tag  tags)  (unless (or (assoc tag newtags) (member tag newtags))  (push tag newtags)))
    (bookmark-prop-set bookmark 'tags newtags)
    (unless no-cache-update-p (bmkp-tags-list)) ; Update the tags cache.
    (bmkp-maybe-save-bookmarks)
    (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
      (with-current-buffer (get-buffer "*Bookmark List*")
        (bmkp-refresh-menu-list bookmark))) ; So the `t' markers are displayed (updated).
    (let ((nb-added  (- (length newtags) olen)))
      (when msgp (message "%d tags added. Now: %S" nb-added ; Echo just the tag names.
                          (let ((tgs  (mapcar #'bmkp-tag-name newtags)))
                            (setq tgs (sort tgs #'string<)))))
      nb-added)))

;; $$$$$$ NOT YET USED
;;;###autoload
(defun bmkp-set-tag-value-for-navlist (tag value) ; Bound to `C-x p t V'
  "Set the value of TAG to VALUE, for each bookmark in the navlist.
If any of the bookmarks has no tag named TAG, then add one with VALUE."
  (interactive (list (bmkp-read-tag-completing) (read (read-string "Value: ")) 'msg))
  (bmkp-set-tag-value-for-bookmarks bmkp-nav-alist tag value))

;; $$$$$$ NOT YET USED
(defun bmkp-set-tag-value-for-bookmarks (bookmarks tag value) ; Not bound
  "Set the value of TAG to VALUE, for each of the BOOKMARKS.
If any of the BOOKMARKS has no tag named TAG, then add one with VALUE."
  (dolist (bmk  bookmarks) (bmkp-set-tag-value bmk tag value)))

;;;###autoload
(defun bmkp-set-tag-value (bookmark tag value &optional msgp) ; Bound to `C-x p t v'
  "For BOOKMARK's TAG, set the value to VALUE.
If BOOKMARK has no tag named TAG, then add one with value VALUE."
  (interactive
   (let* ((bmk  (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)))
          (tag  (bmkp-read-tag-completing "Tag: " (mapcar 'bmkp-full-tag (bmkp-get-tags bmk)))))
     (list bmk tag (read (read-string "Value: ")) 'msg)))
  (unless (bmkp-has-tag-p bookmark tag) (bmkp-add-tags bookmark (list tag)))
  (let* ((newtags     (copy-alist (bmkp-get-tags bookmark)))
         (assoc-tag   (assoc tag newtags))
         (member-tag  (and (not assoc-tag) (member tag newtags))))
    (if assoc-tag (setcdr assoc-tag value) (setcar member-tag (cons (car member-tag) value)))
    (bookmark-prop-set bookmark 'tags newtags))
  (when msgp "Tag value added"))

;; `T -' in bookmark list, `C-x p t - b' elsewhere (`b' for bookmark)
;;;###autoload
(defun bmkp-remove-tags (bookmark tags &optional msgp no-cache-update-p) ; `T -' in bookmark list
  "Remove TAGS from BOOKMARK.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.

TAGS is a list of strings.  The corresponding tags are removed.
Non-nil MSGP means display messages.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags removed."
  (interactive (let ((bmk  (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name))))
                 (list bmk
                       (bmkp-read-tags-completing (mapcar 'bmkp-full-tag (bmkp-get-tags bmk)) t)
                       'msg)))
  (let* ((remtags  (copy-alist (bmkp-get-tags bookmark)))
         (olen     (length remtags)))
    (if (null remtags)
        (when msgp (message "Bookmark has no tags to remove")) ; Do nothing if bookmark has no tags.
      (setq remtags  (bmkp-remove-if #'(lambda (tag)
                                         (if (atom tag) (member tag tags) (member (car tag) tags)))
                                     remtags))
      (bookmark-prop-set bookmark 'tags remtags)
      (unless no-cache-update-p (bmkp-tags-list)) ; Update the tags cache.
      (bmkp-maybe-save-bookmarks)
      (when (and (get-buffer "*Bookmark List*") (get-buffer-window (get-buffer "*Bookmark List*") 0))
        (with-current-buffer (get-buffer "*Bookmark List*")
          (bmkp-refresh-menu-list bookmark))) ; So the `t' markers are removed.
      (let ((nb-removed  (- olen (length remtags))))
        (when msgp (message "%d tags removed. Now: %S" nb-removed ; Echo just the tag names.
                            (let ((tgs  (mapcar #'bmkp-tag-name remtags)))
                              (setq tgs (sort tgs #'string<)))))
        nb-removed))))

;;;###autoload
(defun bmkp-remove-tags-from-all (tags &optional msgp) ; Bound to `T d' in bookmark list
  "Remove TAGS from all bookmarks.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter each tag.
This affects all bookmarks, even those not showing in bookmark list.

TAGS is a list of strings.  The corresponding tags are removed.
Non-nil optional arg MSGP means display a message about the deletion."
  (interactive
   (if (not (y-or-n-p "Delete the tags you specify from ALL bookmarks? "))
       (error "Deletion cancelled")
     (list (bmkp-read-tags-completing nil t)  'MSG)))
  (dolist (bmk  (bookmark-all-names)) (bmkp-remove-tags bmk tags nil 'NO-CACHE-UPDATE))
  (bmkp-tags-list)                      ; Update the tags cache (only once, at end).
  (when msgp (message "Tags removed from all bookmarks: %S" tags)))

;;;###autoload
(defun bmkp-rename-tag (tag newname &optional msgp) ; Bound to `T r' in bookmark list, `C-x p t r' elsewhere
  "Rename TAG to NEWNAME in all bookmarks, even those not showing.
Non-nil optional arg MSGP means display a message about the deletion."
  (interactive (list (bmkp-read-tag-completing "Tag (old name): ")
                     (bmkp-read-tag-completing "New name: ")
                     'MSG))
  (let ((tag-exists-p  nil))
    (dolist (bmk  (bookmark-all-names))
      (let ((newtags  (copy-alist (bmkp-get-tags bmk))))
        (when newtags
          (let* ((assoc-tag   (assoc tag newtags))
                 (member-tag  (and (not assoc-tag) (member tag newtags))))
            (cond (assoc-tag  (setcar assoc-tag newname))
                  (member-tag (setcar member-tag newname)))
            (when (or assoc-tag member-tag)
              (setq tag-exists-p  t)
              (bookmark-prop-set bmk 'tags newtags))))))
    (if tag-exists-p
        (bmkp-tags-list)                ; Update the tags cache.
      (error "No such tag: `%s'" tag))
    (when msgp (message "Renamed"))))

;;;###autoload
(defun bmkp-copy-tags (bookmark &optional msgp) ; `C-x p t c',  `C-x p t M-w'
  "Copy tags from BOOKMARK, so you can paste them to another bookmark.
Note that you can copy from a BOOKMARK that has no tags or has an
empty tags list.  In that case, the copied-tags list is empty, so if
you paste it as a replacement then the recipient bookmark will end up
with no tags.

Non-nil optional arg MSGP means display a message about the number of
tags copied."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'msg))
  (let ((btags  (bmkp-get-tags bookmark)))
    (setq bmkp-copied-tags  (copy-alist btags))
    (when msgp (message "%d tags now available for pasting" (length btags)))))

;;;###autoload
(defun bmkp-paste-add-tags (bookmark &optional msgp no-cache-update-p) ; `C-x p t p',  ; `C-x p t C-y'
  "Add tags to BOOKMARK that were previously copied from another bookmark.
The tags are copied from `bmkp-copied-tags'.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags added."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'msg))
  (unless (listp bmkp-copied-tags)
    (error "`bmkp-paste-add-tags': `bmkp-copied-tags' is not a list"))
  (bmkp-add-tags bookmark bmkp-copied-tags msgp no-cache-update-p))

;;;###autoload
(defun bmkp-paste-replace-tags (bookmark &optional msgp no-cache-update-p) ; `C-x p t q'
  "Replace tags for BOOKMARK with those copied from another bookmark.
The tags are copied from `bmkp-copied-tags'.
Any previously existing tags for BOOKMARK are lost.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags."
  (interactive (list (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name)) 'msg))
  (unless (listp bmkp-copied-tags)
    (error "`bmkp-paste-replace-tags': `bmkp-copied-tags' is not a list"))
  (when (and (bmkp-get-tags bookmark) msgp)
    (y-or-n-p "Existing tags will be lost - really replace them? "))
  (bmkp-remove-all-tags bookmark msgp no-cache-update-p)
  (bmkp-add-tags bookmark bmkp-copied-tags msgp no-cache-update-p))


;;(@* "Bookmark Predicates")
;;  *** Bookmark Predicates ***

(defun bmkp-autofile-bookmark-p (bookmark &optional prefix)
  "Return non-nil if BOOKMARK is an autofile bookmark.
That means that it is `bmkp-file-bookmark-p' and also its
non-directory file name is the same as the bookmark name.
BOOKMARK is a bookmark name or a bookmark record.

Non-nil optional arg PREFIX means that the bookmark name is actually
expected to be the file name prefixed by PREFIX (a string)."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (and (bmkp-file-bookmark-p bookmark)
       (let ((fname  (file-name-nondirectory (bookmark-get-filename bookmark))))
         (string= (if prefix (concat prefix fname) fname)
                  (bookmark-name-from-full-record bookmark)))))

(defun bmkp-bookmark-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a bookmark-file bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-bookmark-file))

(defun bmkp-bookmark-image-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an image-file bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (or (eq (bookmark-get-handler bookmark) 'image-bookmark-jump)
      (and (fboundp 'image-file-name-regexp) ; In `image-file.el' (Emacs 22+).
           (bmkp-file-bookmark-p bookmark)
           (not (bmkp-dired-bookmark-p bookmark))
           (if (fboundp 'string-match-p)
               (string-match-p (image-file-name-regexp) (bookmark-get-filename bookmark))
             (save-match-data
               (string-match (image-file-name-regexp) (bookmark-get-filename bookmark)))))))

(defun bmkp-bookmark-list-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a bookmark-list bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-bookmark-list))

(defun bmkp-desktop-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a desktop bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-desktop))

;; Note: To avoid remote access, if bookmark does not have the Dired handler, then we insist
;; that it be for a local directory.  IOW, we do not include remote directories that were not
;; bookmarked by Bookmark+ (and so do not have the Dired handler).
(defun bmkp-dired-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Dired bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (or (eq (bookmark-get-handler bookmark) 'bmkp-jump-dired)
      (bmkp-local-directory-bookmark-p bookmark)))

(defun bmkp-dired-this-dir-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Dired bookmark for the `default-directory'.
BOOKMARK is a bookmark name or a bookmark record."
  (and (bmkp-dired-bookmark-p bookmark)  (let ((dir  (bookmark-get-filename bookmark)))
                                           (bmkp-same-file-p dir default-directory))))

(defun bmkp-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a file or directory.
BOOKMARK is a bookmark name or a bookmark record.
This excludes bookmarks of a more specific kind (e.g. Info, Gnus)."
  (let* ((filename   (bookmark-get-filename bookmark))
         (nonfile-p  (equal filename bmkp-non-file-filename))
         (handler    (bookmark-get-handler bookmark)))
    (and filename (not nonfile-p) (or (not handler) (eq handler 'bmkp-jump-dired))
         (not (and (bookmark-prop-get bookmark 'info-node)))))) ; Emacs 20-21 Info: no handler.

(defun bmkp-file-this-dir-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks file/subdir in `default-directory'.
BOOKMARK is a bookmark name or a bookmark record.
This excludes bookmarks of a more specific kind (e.g. Info, Gnus)."
  (and (bmkp-file-bookmark-p bookmark)
       (equal (file-name-directory (bookmark-get-filename bookmark)) default-directory)))

(defun bmkp-function-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a function bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-function))

(defun bmkp-gnus-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a Gnus bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (memq (bookmark-get-handler bookmark)
        '(gnus-summary-bookmark-jump bmkp-jump-gnus bmkext-jump-gnus)))

(defun bmkp-info-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is an Info bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (or (eq (bookmark-get-handler bookmark) 'Info-bookmark-jump)
      (and (not (bookmark-get-handler bookmark))
           (or (string= "*info*" (bmkp-get-buffer-name bookmark))
               (bookmark-prop-get bookmark 'info-node))))) ; Emacs 20-21 - no `buffer-name' entry.

(defun bmkp-local-directory-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local directory.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((file  (bookmark-get-filename bookmark)))
    (and (bmkp-local-file-bookmark-p bookmark) (file-directory-p file))))

(defun bmkp-local-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a local file or directory.
BOOKMARK is a bookmark name or a bookmark record.
This excludes bookmarks of a more specific kind (e.g. Info, Gnus)."
  (and (bmkp-file-bookmark-p bookmark) (not (bmkp-remote-file-bookmark-p bookmark))))

(defun bmkp-man-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a `man' page bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (memq (bookmark-get-handler bookmark) '(bmkp-jump-man bmkp-jump-woman
                                          bmkext-jump-man bmkext-jump-woman)))

(defun bmkp-marked-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a marked bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (unless (stringp bookmark) (setq bookmark  (car bookmark)))
  (bmkp-bookmark-name-member bookmark bmkp-bmenu-marked-bookmarks))

(defun bmkp-non-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a non-file bookmark (e.g *scratch*).
This excludes bookmarks of a more specific kind (e.g. Info, Gnus).
It includes bookmarks to existing buffers, as well as bookmarks
defined for buffers that do not currently exist."
  (let* ((filename   (bookmark-get-filename bookmark))
         (nonfile-p  (equal filename bmkp-non-file-filename))) 
    (and (bmkp-get-buffer-name bookmark)
         (or (not filename) nonfile-p
             ;; Ensure not remote before calling `file-exists-p'.  (Do not prompt for password.)
             (and (not (bmkp-file-remote-p filename)) (not (file-exists-p filename))))
         (not (bookmark-get-handler bookmark)))))

(defun bmkp-region-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK has region information.
BOOKMARK is a bookmark name or a bookmark record."
  (and (bmkp-get-end-position bookmark)
       (/= (bookmark-get-position bookmark) (bmkp-get-end-position bookmark))))

(defun bmkp-remote-file-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK bookmarks a remote file or directory.
BOOKMARK is a bookmark name or a bookmark record.
This includes remote Dired bookmarks, but otherwise excludes bookmarks
with handlers (e.g. Info, Gnus)."
  (let* ((handler   (bookmark-get-handler bookmark))
         (file      (bookmark-get-filename bookmark))
         (rem-file  (and file  (bmkp-file-remote-p file))))
    (and rem-file  (or (not handler) (eq handler 'bmkp-jump-dired)))))

(defun bmkp-this-buffer-p (bookmark)
  "Return non-nil if BOOKMARK's buffer is the current buffer.
But return nil for bookmarks, such as desktops, that are not really
associated with a buffer, even if they have a `buffer-name' entry.
BOOKMARK is a bookmark name or a bookmark record."
  (and (equal (bmkp-get-buffer-name bookmark) (buffer-name))
       (not (bmkp-desktop-bookmark-p        bookmark))
       (not (bmkp-bookmark-file-bookmark-p  bookmark))
       (not (bmkp-sequence-bookmark-p       bookmark))
       (not (bmkp-function-bookmark-p       bookmark))
       (not (bmkp-variable-list-bookmark-p  bookmark))))

(defun bmkp-this-file-p (bookmark)
  "Return non-nil if BOOKMARK's filename is the current (absolute) file name.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((bmk-file   (bookmark-get-filename bookmark))
        (this-file  (or (buffer-file-name)  (and (eq major-mode 'dired-mode)  (if (consp dired-directory)
                                                                                  (car dired-directory)
                                                                                dired-directory)))))
    (and bmk-file (equal bmk-file this-file))))

(defun bmkp-last-specific-buffer-p (bookmark)
  "Return t if BOOKMARK's `buffer-name' is `bmkp-last-specific-buffer'.
But return nil for bookmarks, such as desktops, that are not really
associated with a buffer, even if they have a `buffer-name' entry.
It does not matter whether the buffer exists.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((buf  (bmkp-get-buffer-name bookmark)))
    (and buf (string= buf bmkp-last-specific-buffer)
         (not (bmkp-desktop-bookmark-p        bookmark))
         (not (bmkp-bookmark-file-bookmark-p  bookmark))
         (not (bmkp-sequence-bookmark-p       bookmark))
         (not (bmkp-function-bookmark-p       bookmark))
         (not (bmkp-variable-list-bookmark-p  bookmark)))))

(defun bmkp-last-specific-file-p (bookmark)
  "Return t if BOOKMARK's `filename' is `bmkp-last-specific-file'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((file  (bookmark-get-filename bookmark)))
    (and file (string= file bmkp-last-specific-file))))

(defun bmkp-sequence-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a sequence bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-sequence))

(defun bmkp-url-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a URL bookmark.
That means that it satifies either `bmkp-url-browse-bookmark-p' or
`bmkp-w3m-bookmark-p'.
BOOKMARK is a bookmark name or a bookmark record."
  (or (bmkp-url-browse-bookmark-p bookmark) (bmkp-w3m-bookmark-p bookmark)))

(defun bmkp-url-browse-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a `browse-url' bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-url-browse))

(defun bmkp-variable-list-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a variable-list bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (eq (bookmark-get-handler bookmark) 'bmkp-jump-variable-list))

(defun bmkp-w3m-bookmark-p (bookmark)
  "Return non-nil if BOOKMARK is a W3M bookmark.
BOOKMARK is a bookmark name or a bookmark record."
  (memq (bookmark-get-handler bookmark) '(bmkp-jump-w3m bmkext-jump-w3m)))


;;(@* "Filter Functions")
;;  *** Filter Functions ***

(defun bmkp-all-tags-alist-only (tags)
  "`bookmark-alist', but with only bookmarks having all their tags in TAGS.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (let ((bmk-tags  (bmkp-get-tags bmk)))
         (and bmk-tags (bmkp-every #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags))))
   bookmark-alist))

(defun bmkp-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', but with only bookmarks having all tags match REGEXP.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (let ((bmk-tags  (bmkp-get-tags bmk)))
         (and bmk-tags (bmkp-every #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                   bmk-tags))))
   bookmark-alist))

(defun bmkp-annotated-alist-only ()
  "`bookmark-alist', but only for bookmarks with non-empty annotations.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk)
                        (let ((annotation  (bookmark-get-annotation bmk)))
                          (and annotation (not (string-equal annotation "")))))
                      bookmark-alist))

(defun bmkp-autofile-alist-only (&optional prefix)
  "`bookmark-alist', filtered to retain only autofile bookmarks.
With non-nil arg PREFIX, the bookmark names must all have that PREFIX."
  (bookmark-maybe-load-default-file)
  (if (not prefix)
      (bmkp-remove-if-not #'bmkp-autofile-bookmark-p bookmark-alist)
    (bmkp-remove-if-not #'(lambda (bb) (bmkp-autofile-bookmark-p bb prefix)) bookmark-alist)))

(defun bmkp-autonamed-alist-only ()
  "`bookmark-alist', with only autonamed bookmarks (from any buffers).
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-autonamed-bookmark-p bookmark-alist))

(defun bmkp-autonamed-this-buffer-alist-only ()
  "`bookmark-alist', with only autonamed bookmarks for the current buffer.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (bmkp-autonamed-bookmark-for-buffer-p bmk (buffer-name)))
                      bookmark-alist))

(defun bmkp-bookmark-file-alist-only ()
  "`bookmark-alist', filtered to retain only bookmark-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-bookmark-file-bookmark-p bookmark-alist))

(defun bmkp-bookmark-list-alist-only ()
  "`bookmark-alist', filtered to retain only bookmark-list bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-bookmark-list-bookmark-p bookmark-alist))

(defun bmkp-desktop-alist-only ()
  "`bookmark-alist', filtered to retain only desktop bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-desktop-bookmark-p bookmark-alist))

(defun bmkp-dired-alist-only ()
  "`bookmark-alist', filtered to retain only Dired bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-dired-bookmark-p bookmark-alist))

(defun bmkp-dired-this-dir-alist-only ()
  "`bookmark-alist', with only Dired bookmarks for the current directory.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-dired-this-dir-bookmark-p bookmark-alist))

(defun bmkp-file-alist-only ()
  "`bookmark-alist', filtered to retain only file and directory bookmarks.
This excludes bookmarks that might contain file information but are
particular in some way - for example, Info bookmarks or Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-file-bookmark-p bookmark-alist))

(defun bmkp-file-all-tags-alist-only (tags)
  "`bookmark-alist', with only file bookmarks having all tags in TAGS.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (and (bmkp-file-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags (bmkp-every #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags)))))
   bookmark-alist))

(defun bmkp-file-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', with only file bookmarks having all tags match REGEXP.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (and (bmkp-file-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags (bmkp-every #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                        bmk-tags)))))
   bookmark-alist))

(defun bmkp-file-some-tags-alist-only (tags)
  "`bookmark-alist', with only file bookmarks having some tags in TAGS.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk) (and (bmkp-file-bookmark-p bmk)
                        (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags)))
   bookmark-alist))

(defun bmkp-file-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', with only file bookmarks having some tags match REGEXP.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk) (and (bmkp-file-bookmark-p bmk)
                        (bmkp-some #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                   (bmkp-get-tags bmk))))
   bookmark-alist))

(defun bmkp-file-this-dir-alist-only ()
  "`bookmark-alist', filtered with `bmkp-file-this-dir-bookmark-p'.
Include only files and subdir that are in `default-directory'.
This excludes bookmarks that might contain file information but are
particular in some way - for example, Info bookmarks or Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-file-this-dir-bookmark-p bookmark-alist))

(defun bmkp-file-this-dir-all-tags-alist-only (tags)
  "`bookmark-alist', for files in this dir having all tags in TAGS.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (and (bmkp-file-this-dir-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags (bmkp-every #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags)))))
   bookmark-alist))

(defun bmkp-file-this-dir-all-tags-regexp-alist-only (regexp)
  "`bookmark-alist', for files in this dir having all tags match REGEXP.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (and (bmkp-file-this-dir-bookmark-p bmk)
            (let ((bmk-tags  (bmkp-get-tags bmk)))
              (and bmk-tags (bmkp-every #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                        bmk-tags)))))
   bookmark-alist))

(defun bmkp-file-this-dir-some-tags-alist-only (tags)
  "`bookmark-alist', for files in this dir having some tags in TAGS.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk) (and (bmkp-file-this-dir-bookmark-p bmk)
                        (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags)))
   bookmark-alist))

(defun bmkp-file-this-dir-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', for files in this dir having some tags match REGEXP.
Include only files and subdir that are in `default-directory'.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk) (and (bmkp-file-this-dir-bookmark-p bmk)
                        (bmkp-some #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                   (bmkp-get-tags bmk))))
   bookmark-alist))

(defun bmkp-gnus-alist-only ()
  "`bookmark-alist', filtered to retain only Gnus bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-gnus-bookmark-p bookmark-alist))

(defun bmkp-info-alist-only ()
  "`bookmark-alist', filtered to retain only Info bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-info-bookmark-p bookmark-alist))

(defun bmkp-last-specific-buffer-alist-only ()
  "`bookmark-alist', but only for `bmkp-last-specific-buffer'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-last-specific-buffer-p bookmark-alist))

(defun bmkp-last-specific-file-alist-only ()
  "`bookmark-alist', but only for `bmkp-last-specific-file'.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-last-specific-file-p bookmark-alist))

(defun bmkp-man-alist-only ()
  "`bookmark-alist', filtered to retain only `man' page bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-man-bookmark-p bookmark-alist))

(defun bmkp-local-file-alist-only ()
  "`bookmark-alist', filtered to retain only local-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-local-file-bookmark-p bookmark-alist))

(defun bmkp-non-autonamed-alist-only ()
  "`bookmark-alist', with only non-autonamed bookmarks (from any buffers).
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (not (bmkp-autonamed-bookmark-p bmk))) bookmark-alist))

(defun bmkp-non-file-alist-only ()
  "`bookmark-alist', filtered to retain only non-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-non-file-bookmark-p bookmark-alist))

(defun bmkp-regexp-filtered-annotation-alist-only ()
  "`bookmark-alist' for annotations matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (let ((annot  (bookmark-get-annotation bmk)))
         (and (stringp annot) (not (string= "" annot))
              (string-match bmkp-bmenu-filter-pattern annot))))
   bookmark-alist))                     ; (Could use `bmkp-annotated-alist-only' here instead.)

(defun bmkp-regexp-filtered-bookmark-name-alist-only ()
  "`bookmark-alist' for bookmarks matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not
   #'(lambda (bmk) (string-match bmkp-bmenu-filter-pattern (car bmk))) bookmark-alist))

(defun bmkp-regexp-filtered-file-name-alist-only ()
  "`bookmark-alist' for files matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (let (fname)
    (bmkp-remove-if-not #'(lambda (bmk) (and (setq fname  (bookmark-get-filename bmk))
                                             (string-match bmkp-bmenu-filter-pattern fname)))
                        bookmark-alist)))

(defun bmkp-regexp-filtered-tags-alist-only ()
  "`bookmark-alist' for tags matching `bmkp-bmenu-filter-pattern'."
  (bookmark-maybe-load-default-file)
  (let (tags)
    (bmkp-remove-if-not
     #'(lambda (bmk) (and (setq tags  (bmkp-get-tags bmk))
                          (bmkp-some (lambda (tag)
                                       (string-match bmkp-bmenu-filter-pattern (bmkp-tag-name tag)))
                                     tags)))
     bookmark-alist)))

(defun bmkp-region-alist-only ()
  "`bookmark-alist', filtered to retain only bookmarks that have regions.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-region-bookmark-p bookmark-alist))

(defun bmkp-remote-file-alist-only ()
  "`bookmark-alist', filtered to retain only remote-file bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-remote-file-bookmark-p bookmark-alist))

(defun bmkp-some-tags-alist-only (tags)
  "`bookmark-alist', but with only bookmarks having some tags in TAGS.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk) (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags))
   bookmark-alist))

(defun bmkp-some-tags-regexp-alist-only (regexp)
  "`bookmark-alist', but with only bookmarks having some tags match REGEXP.
A new list is returned (no side effects)."
  (bmkp-remove-if-not
   #'(lambda (bmk)
       (bmkp-some #'(lambda (tag) (string-match regexp (bmkp-tag-name tag))) (bmkp-get-tags bmk)))
   bookmark-alist))

(defun bmkp-specific-buffers-alist-only (&optional buffers)
  "`bookmark-alist', filtered to retain only bookmarks to buffers BUFFERS.
BUFFERS is a list of buffer names.
It defaults to a singleton list with the current buffer's name.
A new list is returned (no side effects).

Note: Bookmarks created by vanilla Emacs do not record the buffer
name.  They are therefore excluded from the returned alist."
  (unless buffers  (setq buffers  (list (buffer-name))))
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (and (not (bmkp-desktop-bookmark-p       bmk)) ; Exclude these
                                         (not (bmkp-bookmark-file-bookmark-p bmk))
                                         (not (bmkp-sequence-bookmark-p      bmk))
                                         (not (bmkp-function-bookmark-p      bmk))
                                         (not (bmkp-variable-list-bookmark-p bmk))
                                         (member (bmkp-get-buffer-name bmk) buffers)))
                      bookmark-alist))

(defun bmkp-specific-files-alist-only (&optional files)
  "`bookmark-alist', filtered to retain only bookmarks to files FILES.
FILES is a list of absolute file names.
It defaults to a singleton list with the current buffer's file name.
A new list is returned (no side effects)."
  (unless files  (setq files  (list (buffer-file-name))))
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not (lambda (bmk) (member (bookmark-get-filename bmk) files)) bookmark-alist))

(defun bmkp-this-buffer-alist-only ()
  "`bookmark-alist', with only bookmarks for the current buffer.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-this-buffer-p bookmark-alist))

(defun bmkp-this-file-alist-only ()
  "`bookmark-alist', with only bookmarks for the current file.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-this-file-p bookmark-alist))

(defun bmkp-url-alist-only ()
  "`bookmark-alist', filtered to retain only URL bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-url-bookmark-p bookmark-alist))

(defun bmkp-url-browse-alist-only ()
  "`bookmark-alist', filtered to retain only non-W3M URL bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-url-browse-bookmark-p bookmark-alist))

(defun bmkp-variable-list-alist-only ()
  "`bookmark-alist', filtered to retain only variable-list bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-variable-list-bookmark-p bookmark-alist))

(defun bmkp-w3m-alist-only ()
  "`bookmark-alist', filtered to retain only W3M bookmarks.
A new list is returned (no side effects)."
  (bookmark-maybe-load-default-file)
  (bmkp-remove-if-not #'bmkp-w3m-bookmark-p bookmark-alist))


;;; Marked bookmarks

(defun bmkp-marked-bookmarks-only ()
  "Return the list of marked bookmarks."
  (bmkp-remove-if-not #'bmkp-marked-bookmark-p bookmark-alist))

(defun bmkp-unmarked-bookmarks-only ()
  "Return the list of unmarked bookmarks."
  (bmkp-remove-if #'bmkp-marked-bookmark-p bookmark-alist))

(defun bmkp-some-marked-p (alist)
  "Return non-nil if ALIST is nonempty and includes a marked bookmark."
  (catch 'break (dolist (i  alist)  (and (bmkp-marked-bookmark-p i)  (throw 'break t)))))

(defun bmkp-some-unmarked-p (alist)
  "Return non-nil if ALIST is nonempty and includes an unmarked bookmark."
  (catch 'break (dolist (i  alist)  (and (not (bmkp-marked-bookmark-p i))  (throw 'break t)))))


;;(@* "General Utility Functions")
;;  *** General Utility Functions ***

(defun bmkp-remove-dups (list)
  "Copy of LIST with duplicate elements removed.  Tested with `equal'."
  (let ((tail  list)
        new)
    (while tail
      (unless (member (car tail) new) (push (car tail) new))
      (pop tail))
    (nreverse new)))

;; Similar to `bmkp-assoc-delete-all', but compares also property `bmkp-full-record'.
(defun bmkp-delete-bookmark-name-from-list (delname bnames)
  "Delete names that represent the same bookmark as DELNAME from BNAMES.
This menas that they are `string=' and have the same value of property
`bmkp-full-record'.
Return the modified list BNAMES."
  (let ((delprop  (get-text-property 0 'bmkp-full-record delname)))
    (if (not delprop)
        (delete delname bnames)         ; Unpropertized - just use `delete'.
      (while (and bnames  (string= delname (car bnames))
                  (eq delprop (get-text-property 0 'bmkp-full-record (car bnames))))
        (setq bnames  (cdr bnames)))
      (let ((tail  bnames)
            tail-cdr)
        (while (setq tail-cdr  (cdr tail))
          (if (and (car tail-cdr)  (string= delname (car tail-cdr))
                   (eq delprop (get-text-property 0 'bmkp-full-record (car tail-cdr))))
              (setcdr tail  (cdr tail-cdr))
            (setq tail  tail-cdr))))
      bnames)))

(defun bmkp-bookmark-name-member (name names) ; $$$$$$ PUT BACK `eq' instead of `equal'?.
  "Like `member', but tests also bookmark NAME's `bmkp-full-record' property.
If NAME has no `bmkp-full-record' property then this is just `member'.

If NAME has property `bmkp-full-record', then test whether both:
 a. NAME is a member of NAMES and
 b. NAME has the same `bmkp-full-record' value as an element of NAMES.
Return the tail of NAMES whose car is NAME with the property match."
  (let ((prop  (get-text-property 0 'bmkp-full-record name)))
    (if (not prop)
        (member name names)             ; Unpropertized - just use `member'.
      (while (and names  (not (and (string= name (car names)) ; = `bmkp-names-same-bookmark-p'.
                                   (equal prop (get-text-property 0 'bmkp-full-record (car names))))))
        (setq names  (cdr names)))
      names)))

(defun bmkp-names-same-bookmark-p (name1 name2) ; $$$$$$ PUT BACK `eq' instead of `equal'?.
  "Return non-nil if the two strings name the same bookmark.
The strings are `string=' and their `bmkp-full-record' property values
for the first character are `eq'."
  (and (string= name1 name2)
       (equal (get-text-property 0 'bmkp-full-record name1)
              (get-text-property 0 'bmkp-full-record name2))))

(defun bmkp-remove-if (pred xs)
  "A copy of list XS with no elements that satisfy predicate PRED."
  (let ((result  ()))
    (dolist (x  xs)  (unless (funcall pred x) (push x result)))
    (nreverse result)))

(defun bmkp-remove-if-not (pred xs)
  "A copy of list XS with only elements that satisfy predicate PRED."
  (let ((result  ()))
    (dolist (x  xs)  (when (funcall pred x) (push x result)))
    (nreverse result)))

;; Similar to `every' in `cl-extra.el', without non-list sequences and multiple sequences.
(defun bmkp-every (predicate list)
  "Return t if PREDICATE is true for all elements of LIST; else nil."
  (let ((res  nil))
    (while (and list (funcall predicate (car list))) (setq list  (cdr list)))
    (null list)))

;; Similar to `some' in `cl-extra.el', without non-list sequences and multiple sequences.
(defun bmkp-some (predicate list)
  "Return non-nil if PREDICATE is true for some element of LIST; else nil.
Return the first non-nil value returned by PREDICATE."
  (let ((res  nil))
    (while (and list (not (setq res  (funcall predicate (pop list))))))
    res))

;; From `cl-seq.el', function `union', without keyword treatment.
;; (Same as `simple-set-union' in `misc-fns.el' and `icicle-set-union' in `icicles-fn.el'.)
(defun bmkp-set-union (list1 list2)
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

(defun bmkp-upcase (string)
  "`upcase', but in case of error, return original STRING.
This works around an Emacs 20 problem that occurs if STRING contains
binary data (weird chars)."
  (condition-case nil (upcase string) (error string)))

(defun bmkp-same-file-p (file1 file2)
  "Return non-nil if FILE1 and FILE2 name the same file.
If either name is not absolute, then it is considered relative to
`default-directory'."
  (string= (file-truename (expand-file-name file1)) (file-truename (expand-file-name file2))))

(defun bmkp-file-remote-p (file-name)
  "Returns non-nil if string FILE-NAME is likely to name a remote file."
  (if (fboundp 'file-remote-p)
      (file-remote-p file-name)
    (and (fboundp 'ffap-file-remote-p) (ffap-file-remote-p file-name))))

(defun bmkp-float-time (&optional specified-time)
  "Same as `float-time'.  (Needed for Emacs 20.)"
  (if (fboundp 'float-time)
      (float-time specified-time)
    (unless specified-time (setq specified-time  (current-time)))
    (+ (* (float (nth 0 specified-time)) (expt 2 16))  (nth 1 specified-time))))

(defun bmkp-face-prop (value)
  "Return a list with elements `face' or `font-lock-face' and VALUE.
Starting with Emacs 22, the first element is `font-lock-face'."
  (list (if (> emacs-major-version 21) 'font-lock-face 'face) value))  

(defun bmkp-make-plain-predicate (pred &optional final-pred)
  "Return a plain predicate that corresponds to component-predicate PRED.
PRED and FINAL-PRED correspond to their namesakes in
`bmkp-sort-comparer' (which see).

PRED should return `(t)', `(nil)', or nil.

Optional arg FINAL-PRED is the final predicate to use if PRED cannot
decide (returns nil).  If FINAL-PRED is nil, then `bmkp-alpha-p', the
plain-predicate equivalent of `bmkp-alpha-cp' is used as the final
predicate."
  `(lambda (b1 b2) (let ((res  (funcall ',pred b1 b2)))
                     (if res (car res) (funcall ',(or final-pred 'bmkp-alpha-p) b1 b2)))))

(defun bmkp-repeat-command (command)
  "Repeat COMMAND."
  (let ((repeat-message-function  'ignore))
    (setq last-repeatable-command  command)
    (repeat nil)))


;;; If you need this for some reason, uncomment it.
;;; (defun bmkp-fix-bookmark-alist-and-save ()
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
;;;                              (setcar fn-tail (cons 'filename bmkp-non-file-filename)))
;;;                             ((and (eq hdlr 'bmkp-jump-gnus)
;;;                                   (not (assoc 'filename bmk)))
;;;                              (setcdr bmk (cons (cons 'filename bmkp-non-file-filename)
;;;                                                (cdr bmk)))))))
;;;                   t)                    ; Be sure `dolist' exit with t to allow saving.
;;;               (error (error "No changes made. %s" (error-message-string err))))
;;;         (bookmark-save)
;;;         (message "Bookmarks file fixed.  Old version is `%s'" bkup-file)))))


;;(@* "Bookmark Entry Access Functions")
;;  *** Bookmark Entry Access Functions ***

(defun bmkp-get-buffer-name (bookmark)
  "Return the `buffer-name' value for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'buffer-name))

(defun bmkp-get-end-position (bookmark)
  "Return the `end-position' value for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'end-position))

(defun bmkp-get-visits-count (bookmark)
  "Return the `visits' count for BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (bookmark-prop-get bookmark 'visits))

(defun bmkp-get-visit-time (bookmark)
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

(defun bmkp-sort-omit (alist &optional omit)
  "Sort a copy of ALIST, omitting any elements whose keys are in OMIT.
Return the copy.
Do not sort if `bmkp-sort-comparer' is nil.
This is a non-destructive operation: ALIST is not modified.

Sorting is done using using `bmkp-sort-comparer'.
If `bmkp-reverse-sort-p' is non-nil, then reverse the sort order.
Keys are compared for sorting using `equal'.

If optional arg OMIT is non-nil, then it is a list of keys.  Omit from
the return value any elements with keys in the list."
  (let ((new-alist  (bmkp-remove-omitted alist omit))
        (sort-fn  (and bmkp-sort-comparer  (if (and (not (functionp bmkp-sort-comparer))
                                                    (consp bmkp-sort-comparer))
                                               'bmkp-multi-sort
                                             bmkp-sort-comparer))))
    (when sort-fn
      (setq new-alist  (sort new-alist (if bmkp-reverse-sort-p
                                           (lambda (a b) (not (funcall sort-fn a b)))
                                         sort-fn))))
    new-alist))

(defun bmkp-remove-omitted (alist &optional omit)
  "Copy of bookmark ALIST without bookmarks whose names are in list OMIT.
Name comparison is done using `bmkp-bookmark-name-member'.
If optional arg OMIT is non-nil, then omit from the return value any
elements with keys in list OMIT."
  (let ((new  ()))
    (dolist (ii  alist)  (unless (bmkp-bookmark-name-member (car ii) omit)  (push ii new)))
    (nreverse new)))

;;; $$$$$$ No longer used.
;;; (defun bmkp-sort-and-remove-dups (alist &optional omit)
;;;   "Remove duplicates from a copy of ALIST, then sort it and return it.
;;; Do not sort if `bmkp-sort-comparer' is nil.
;;; Always remove duplicates.  Keep only the first element with a given
;;; key.  This is a non-destructive operation: ALIST is not modified.

;;; Sorting is done using using `bmkp-sort-comparer'.
;;; If `bmkp-reverse-sort-p' is non-nil, then reverse the sort order.
;;; Keys are compared for sorting using `equal'.
;;; If optional arg OMIT is non-nil, then omit from the return value any
;;; elements with keys in list OMIT."
;;;   (let ((new-alist  (bmkp-remove-assoc-dups alist omit))
;;;         (sort-fn  (and bmkp-sort-comparer  (if (and (not (functionp bmkp-sort-comparer))
;;;                                                     (consp bmkp-sort-comparer))
;;;                                                'bmkp-multi-sort
;;;                                              bmkp-sort-comparer))))
;;;     (when sort-fn
;;;       (setq new-alist  (sort new-alist (if bmkp-reverse-sort-p
;;;                                            (lambda (a b) (not (funcall sort-fn a b)))
;;;                                          sort-fn))))
;;;     new-alist))

;;; KEEP this simpler version also.  This uses `run-hook-with-args-until-success', but it
;;; does not respect `bmkp-reverse-multi-sort-p'.
;;; (defun bmkp-multi-sort (b1 b2)
;;;   "Try predicates in `bmkp-sort-comparer', in order, until one decides.
;;; See the description of `bmkp-sort-comparer'."
;;;   (let* ((preds   (append (car bmkp-sort-comparer) (cdr bmkp-sort-comparer)))
;;;          (result  (run-hook-with-args-until-success 'preds b1 b2)))
;;;     (if (consp result)
;;;         (car result)
;;;       result)))

;;; $$$$$$ No longer used.
;;; (defun bmkp-remove-assoc-dups (alist &optional omit)
;;;   "Shallow copy of ALIST without elements that have duplicate keys.
;;; Only the first element of those with the same key is kept.
;;; Keys are compared using `equal'.
;;; If optional arg OMIT is non-nil, then omit from the return value any
;;; elements with keys in list OMIT."
;;;   (let ((new  ()))
;;;     (dolist (ii  alist)  (unless (or (assoc (car ii) new) (member (car ii) omit))  (push ii new)))
;;;     (nreverse new)))


;; This Lisp definition respects `bmkp-reverse-multi-sort-p', and can be extended.
(defun bmkp-multi-sort (b1 b2)
  "Try predicates in `bmkp-sort-comparer', in order, until one decides.
See the description of `bmkp-sort-comparer'.
If `bmkp-reverse-multi-sort-p' is non-nil, then reverse the order for
using multi-sorting predicates."
  (let ((preds       (car bmkp-sort-comparer))
        (final-pred  (cadr bmkp-sort-comparer))
        (result      nil))
    (when bmkp-reverse-multi-sort-p (setq preds  (reverse preds)))
    (catch 'bmkp-multi-sort
      (dolist (pred  preds)
        (setq result  (funcall pred b1 b2))
        (when (consp result)
          (when bmkp-reverse-multi-sort-p (setq result  (list (not (car result)))))
          (throw 'bmkp-multi-sort (car result))))
      (and final-pred  (if bmkp-reverse-multi-sort-p
                           (not (funcall final-pred b1 b2))
                         (funcall final-pred b1 b2))))))

;; The message is only approximate.  The effect of `bmkp-reverse-multi-sort-p' is not
;; always intuitive, but it can often be useful.  What's not always intuitive is the placement
;; (the order) of bookmarks that are not sorted by the PREDs.
;; 
(defun bmkp-msg-about-sort-order (order &optional prefix-msg suffix-msg)
  "Display a message mentioning the current sort ORDER and direction.
Optional arg PREFIX-MSG is prepended to the constructed message, and
terminated with a period.
Similarly, SUFFIX-MSG is appended, after appending \".  \"."
  (let ((msg  (if (not bmkp-sort-comparer)
                  "Bookmarks NOT sorted"
                (format "%s%s" (concat "Sorted " order)
                        (if (not (and (consp bmkp-sort-comparer) ; Ordinary single predicate.
                                      (consp (car bmkp-sort-comparer))))
                            (if bmkp-reverse-sort-p "; REVERSED" "")
                          (if (not (cadr (car bmkp-sort-comparer)))
                              ;; Single PRED.
                              (if (or (and bmkp-reverse-sort-p (not bmkp-reverse-multi-sort-p))
                                      (and bmkp-reverse-multi-sort-p (not bmkp-reverse-sort-p)))
                                  "; REVERSED"
                                "")

                            ;; In case we want to distinguish:
                            ;; (if (and bmkp-reverse-sort-p (not bmkp-reverse-multi-sort-p))
                            ;;     "; reversed"
                            ;;   (if (and bmkp-reverse-multi-sort-p (not bmkp-reverse-sort-p))
                            ;;       "; reversed +"
                            ;;     ""))

                            ;; At least two PREDs.
                            (cond ((and bmkp-reverse-sort-p (not bmkp-reverse-multi-sort-p))
                                   "; REVERSED")
                                  ((and bmkp-reverse-multi-sort-p (not bmkp-reverse-sort-p))
                                   "; each predicate group reversed")
                                  ((and bmkp-reverse-multi-sort-p bmkp-reverse-sort-p)
                                   "; order of predicate groups reversed")
                                  (t ""))))))))
    (when prefix-msg (setq msg  (concat prefix-msg ".  " msg)))
    (when suffix-msg (setq msg  (concat msg ".  " suffix-msg)))
    (message msg)))


;;(@* "Sorting - Commands")
;;  *** Sorting - Commands ***

(defun bmkp-current-sort-order ()
  "Current sort order or sort function, as a string suitable in a message."
  (or (car (rassoc bmkp-sort-comparer bmkp-sort-orders-alist))  (format "%s" bmkp-sort-comparer)))


;;(@* "Sorting - General Predicates")
;;  *** Sorting - General Predicates ***

(defun bmkp-marked-cp (b1 b2)
  "True if bookmark B1 is marked and bookmark B2 is not.
B1 and B2 are bookmarks or bookmark names.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((m1  (bmkp-marked-bookmark-p b1))
        (m2  (bmkp-marked-bookmark-p b2)))
    (cond ((and m1 m2)  nil)
          (m1           '(t))
          (m2           '(nil))
          (t            nil))))

(defun bmkp-visited-more-cp (b1 b2)
  "True if bookmark B1 was visited more often than B2.
B1 and B2 are bookmarks or bookmark names.
True also if B1 was visited but B2 was not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((v1  (bmkp-get-visits-count b1))
        (v2  (bmkp-get-visits-count b2)))
    (cond ((and v1 v2)
           (cond ((> v1 v2)  '(t))
                 ((> v2 v1)  '(nil))
                 (t          nil)))
          (v1                '(t))
          (v2                '(nil))
          (t                 nil))))

(defun bmkp-bookmark-creation-cp (b1 b2)
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
           (setq t1  (bmkp-float-time t1)
                 t2  (bmkp-float-time t2))
           (cond ((> t1 t2)  '(t))
                 ((> t2 t1)  '(nil))
                 (t          nil)))
          (t1                '(t))
          (t2                '(nil))
          (t                 nil))))

;; Not used currently.
(defun bmkp-same-creation-time-p (b1 b2)
  "Return non-nil if `B1 and B2 have same `created' entry.
B1 and B2 are bookmarks or bookmark names.
If neither has a `created' entry (vanilla bookmarks), then return
non-nil if the full bookmarks are `equal'."
  (let ((time1  (bookmark-prop-get b1 'created))
        (time2  (bookmark-prop-get b2 'created)))
    (if (or time1 time2)
        (equal time1 time2)
      (equal b1 b2))))

(defun bmkp-bookmark-last-access-cp (b1 b2)
  "True if bookmark B1 was visited more recently than B2.
B1 and B2 are bookmarks or bookmark names.
True also if B1 was visited but B2 was not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if incomparable as described."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((t1  (bmkp-get-visit-time b1))
        (t2  (bmkp-get-visit-time b2)))
    (cond ((and t1 t2)
           (setq t1  (bmkp-float-time t1)
                 t2  (bmkp-float-time t2))
           (cond ((> t1 t2)  '(t))
                 ((> t2 t1)  '(nil))
                 (t          nil)))
          (t1                '(t))
          (t2                '(nil))
          (t                 nil))))

(defun bmkp-buffer-last-access-cp (b1 b2)
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
  (let ((buf1  (bmkp-get-buffer-name b1))
        (buf2  (bmkp-get-buffer-name b2))
        f1 f2 t1 t2)
    (setq buf1  (and buf1 (get-buffer buf1))
          buf2  (and buf2 (get-buffer buf2)))
    (cond ((and buf1 buf2)              ; Both buffers exist.   See whether they were accessed.
           (when buf1 (setq buf1  (member buf1 (buffer-list))
                            buf1  (length buf1)))
           (when buf2 (setq buf2  (member buf2 (buffer-list))
                            buf2  (length buf2)))
           (cond ((and buf1 buf2)       ; Both were accessed.  Priority to most recent access.
                  (cond ((< buf1 buf2)  '(t))
                        ((< buf2 buf1)  '(nil))
                        (t              nil)))
                 (buf1                  '(t)) ; Only buf1 was accessed.
                 (buf2                  '(nil)) ; Only buf2 was accessed.
                 (t                     nil))) ; Neither was accessed.

          (buf1                         '(t)) ; Only buf1 exists.
          (buf2                         '(nil)) ; Only buf2 exists.
          (t                            nil)))) ; Neither buffer exists

(defun bmkp-handler-cp (b1 b2)
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
           (when (eq h1 'bmkp-jump-woman) (setq h1  'bmkp-jump-man))
           (when (eq h2 'bmkp-jump-woman) (setq h2  'bmkp-jump-man))
           (setq h1  (symbol-name h1)
                 h2  (symbol-name h2))
           (when case-fold-search (setq h1  (bmkp-upcase h1)
                                        h2  (bmkp-upcase h2)))
           (cond ((string-lessp h1 h2)  '(t))
                 ((string-lessp h2 h1)  '(nil))
                 (t                     nil)))
          (h1                           '(t))
          (h2                           '(nil))
          (t                            nil))))

(defun bmkp-info-cp (b1 b2)
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
  (let ((i1  (bmkp-info-bookmark-p b1))
        (i2  (bmkp-info-bookmark-p b2)))
    (cond ((and i1 i2)
           (setq i1  (abbreviate-file-name (bookmark-get-filename b1))
                 i2  (abbreviate-file-name (bookmark-get-filename b2)))
           (when case-fold-search (setq i1  (bmkp-upcase i1)
                                        i2  (bmkp-upcase i2)))
           (cond ((string-lessp i1 i2)                  '(t)) ; Compare manuals (file names).
                 ((string-lessp i2 i1)                  '(nil))
                 (t                     ; Compare node names.
                  (setq i1  (bookmark-prop-get b1 'info-node)
                        i2  (bookmark-prop-get b2 'info-node))
                  (cond ((string-lessp i1 i2)           '(t))
                        ((string-lessp i2 i1)           '(nil))
                        (t
                         (setq i1  (bookmark-get-position b1)
                               i2  (bookmark-get-position b2))
                         (cond ((or (not i1) (not i2))  '(t)) ; Fallback if no `position' entry.
                               ((<= i1 i2)              '(t))
                               ((< i2 i1)               '(nil))))))))
          (i1                                           '(t))
          (i2                                           '(nil))
          (t                                            nil))))

(defun bmkp-gnus-cp (b1 b2)
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
  (let ((g1  (bmkp-gnus-bookmark-p b1))
        (g2  (bmkp-gnus-bookmark-p b2)))
    (cond ((and g1 g2)
           (setq g1  (bookmark-prop-get b1 'group)
                 g2  (bookmark-prop-get b2 'group))
           (cond ((string-lessp g1 g2)                '(t)) ; Compare groups.
                 ((string-lessp g2 g1)                '(nil))
                 (t                     ; Compare article numbers.
                  (setq g1  (bookmark-prop-get b1 'article)
                        g2  (bookmark-prop-get b2 'article))
                  (cond ((< g1 g2)                    '(t))
                        ((< g2 g1)                    '(nil))
                        (t
                         (setq g1  (bookmark-prop-get b1 'message-id)
                               g2  (bookmark-prop-get b2 'message-id))
                         (cond ((string-lessp g1 g2)  '(t)) ; Compare message IDs.
                               ((string-lessp g2 g1)  '(nil))
                               (t                     nil)))))))   
          (g1                                         '(t))
          (g2                                         '(nil))
          (t                                          nil))))

(defun bmkp-url-cp (b1 b2)
  "True if bookmark B1 sorts as a URL bookmark before B2.
B1 and B2 are bookmarks or bookmark names.
Two URL bookmarks are compared alphabetically, by their URLs.
True also if B1 is a URL bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((u1  (bmkp-url-bookmark-p b1))
        (u2  (bmkp-url-bookmark-p b2)))
    (cond ((and u1 u2)
           (setq u1  (or (bookmark-prop-get b1 'location) (bookmark-get-filename b1))
                 u2  (or (bookmark-prop-get b2 'location) (bookmark-get-filename b2)))
           (cond ((string-lessp u1 u2)  '(t))
                 ((string-lessp u2 u1)  '(nil))
                 (t                     nil)))
          (u1                           '(t))
          (u2                           '(nil))
          (t                            nil))))

;; Not used now.
(defun bmkp-w3m-cp (b1 b2)
  "True if bookmark B1 sorts as a W3M URL bookmark before B2.
B1 and B2 are bookmarks or bookmark names.
Two W3M URL bookmarks are compared alphabetically, by their URLs.
True also if B1 is a W3M bookmark but B2 is not.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((w1  (bmkp-w3m-bookmark-p b1))
        (w2  (bmkp-w3m-bookmark-p b2)))
    (cond ((and w1 w2)
           (setq w1  (bookmark-get-filename b1)
                 w2  (bookmark-get-filename b2))
           (cond ((string-lessp w1 w2)  '(t))
                 ((string-lessp w2 w1)  '(nil))
                 (t                     nil)))
          (w1                           '(t))
          (w2                           '(nil))
          (t                            nil))))

(defun bmkp-position-cp (b1 b2)
  "True if the `position' of B1 is not greater than that of B2.
B1 and B2 are bookmarks or bookmark names.
Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if B1 and B2 do not bookmark the same buffer or they have
the same `position' value."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((buf1  (bmkp-get-buffer-name b1))
        (buf2  (bmkp-get-buffer-name b2)))
    (and buf1 buf2 (equal buf1 buf2)
         (let ((i1  (bookmark-get-position b1))
               (i2  (bookmark-get-position b2)))
           (cond ((or (not i1) (not i2))  '(t)) ; Fallback if no `position' entry.
                 ((<= i1 i2)              '(t))
                 ((< i2 i1)               '(nil)))))))

(defun bmkp-alpha-cp (b1 b2)
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
    (when case-fold-search (setq s1  (bmkp-upcase s1)
                                 s2  (bmkp-upcase s2)))
    (cond ((string-lessp s1 s2)  '(t))
          ((string-lessp s2 s1)  '(nil))
          (t                     nil))))

;; Do not use `bmkp-make-plain-predicate', because it falls back on `bookmark-alpha-p'.
;; Return nil if `bookmark-alpha-cp' cannot decide.
(defun bmkp-alpha-p (b1 b2)
  "True if bookmark B1's name sorts alphabetically before B2's.
B1 and B2 are bookmarks or bookmark names.
The bookmark names are compared, respecting `case-fold-search'."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (car (bmkp-alpha-cp b1 b2)))


;;(@* "Sorting - File-Name Predicates")
;;  *** Sorting - File-Name Predicates ***

(defun bmkp-file-alpha-cp (b1 b2)
  "True if bookmark B1's file name sorts alphabetically before B2's.
B1 and B2 are bookmarks or bookmark names.
The file names are shortened using `abbreviate-file-name', then they
are compared respecting `case-fold-search'.

Reverse the roles of B1 and B2 for a false value.
A true value is returned as `(t)', a false value as `(nil)'.
Return nil if neither sorts before the other."
  (setq b1  (bookmark-get-bookmark b1)
        b2  (bookmark-get-bookmark b2))
  (let ((f1  (bmkp-file-bookmark-p b1))
        (f2  (bmkp-file-bookmark-p b2)))
    (cond ((and f1 f2)
           ;; Call `abbreviate-file-name' mainly to get letter case right per platform.
           (setq f1  (abbreviate-file-name (bookmark-get-filename b1))
                 f2  (abbreviate-file-name (bookmark-get-filename b2)))
           (when case-fold-search (setq f1  (bmkp-upcase f1)
                                        f2  (bmkp-upcase f2)))
           (cond ((string-lessp f1 f2)  '(t))
                 ((string-lessp f2 f1)  '(nil))
                 (t                     nil)))
          (f1                           '(t))
          (f2                           '(nil))
          (t                            nil))))

;; We define all file-attribute predicates, in case you want to use them.
;;
;; `bmkp-file-attribute-0-cp'  - type
;; `bmkp-file-attribute-1-cp'  - links
;; `bmkp-file-attribute-2-cp'  - uid
;; `bmkp-file-attribute-3-cp'  - gid
;; `bmkp-file-attribute-4-cp'  - last access time
;; `bmkp-file-attribute-5-cp'  - last update time
;; `bmkp-file-attribute-6-cp'  - last status change
;; `bmkp-file-attribute-7-cp'  - size
;; `bmkp-file-attribute-8-cp'  - modes
;; `bmkp-file-attribute-9-cp'  - gid change
;; `bmkp-file-attribute-10-cp' - inode
;; `bmkp-file-attribute-11-cp' - device
;;
(bmkp-define-file-sort-predicate 0) ; Type: file, symlink, dir
(bmkp-define-file-sort-predicate 1) ; Links
(bmkp-define-file-sort-predicate 2) ; Uid
(bmkp-define-file-sort-predicate 3) ; Gid
(bmkp-define-file-sort-predicate 4) ; Last access time
(bmkp-define-file-sort-predicate 5) ; Last modification time
(bmkp-define-file-sort-predicate 6) ; Last status-change time
(bmkp-define-file-sort-predicate 7) ; Size
(bmkp-define-file-sort-predicate 8) ; Modes
(bmkp-define-file-sort-predicate 9) ; Gid would change if re-created
(bmkp-define-file-sort-predicate 10) ; Inode
(bmkp-define-file-sort-predicate 11) ; Device

(defun bmkp-local-file-accessed-more-recently-cp (b1 b2)
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
  (cond ((and (bmkp-local-file-bookmark-p b1) (bmkp-local-file-bookmark-p b2))
         (bmkp-cp-not (bmkp-file-attribute-4-cp b1 b2)))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-local-file-updated-more-recently-cp (b1 b2)
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
  (cond ((and (bmkp-local-file-bookmark-p b1) (bmkp-local-file-bookmark-p b2))
         (bmkp-cp-not (bmkp-file-attribute-5-cp b1 b2)))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-local-file-size-cp (b1 b2)
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
  (cond ((and (bmkp-local-file-bookmark-p b1) (bmkp-local-file-bookmark-p b2))
         (bmkp-cp-not (bmkp-file-attribute-7-cp b1 b2)))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-local-file-type-cp (b1 b2)
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
  (cond ((and (bmkp-local-file-bookmark-p b1) (bmkp-local-file-bookmark-p b2))
         (bmkp-file-attribute-0-cp b1 b2))
        ((bmkp-local-file-bookmark-p b1)         '(t))
        ((bmkp-local-file-bookmark-p b2)         '(nil))
        ((and (bmkp-remote-file-bookmark-p b1)
              (bmkp-remote-file-bookmark-p b2))  nil)
        ((bmkp-remote-file-bookmark-p b1)        '(t))
        ((bmkp-remote-file-bookmark-p b2)        '(nil))
        (t                                       nil)))

(defun bmkp-cp-not (truth)
  "Return the negation of boolean value TRUTH.
If TRUTH is (t), return (nil), and vice versa.
If TRUTH is nil, return nil."
  (and truth (if (car truth) '(nil) '(t))))


;;(@* "Indirect Bookmarking Functions")
;;  *** Indirect Bookmarking Functions ***

;;;###autoload
(defun bmkp-url-target-set (url &optional prefix-only-p name/prefix) ; `C-x p c u'
  "Set a bookmark for a URL.  Return the bookmark.
Interactively you are prompted for the URL.  Completion is available.
Use `M-n' to pick up the url at point as the default.

You are also prompted for the bookmark name.  But with a prefix arg,
you are prompted only for a bookmark-name prefix.  In that case, the
bookmark name is the prefix followed by the URL."
  (interactive
   (list (if (require 'ffap nil t)
             (ffap-read-file-or-url "URL: " (or (thing-at-point 'url)  (and (fboundp 'url-get-url-at-point)
                                                                           (url-get-url-at-point))))
           (read-file-name "URL: " nil (or (thing-at-point 'url)  (and (fboundp 'url-get-url-at-point)
                                                                       (url-get-url-at-point)))))
         current-prefix-arg
         (if current-prefix-arg
             (read-string "Prefix for bookmark name: ")
           (bmkp-completing-read-lax "Bookmark name"))))
  (unless name/prefix (setq name/prefix  ""))
  (let ((bookmark-make-record-function  (if (eq major-mode 'w3m-mode)
                                            'bmkp-make-w3m-record
                                          (lambda () (bmkp-make-url-browse-record url))))
        bmk failure)
    (condition-case err
        (setq bmk  (bookmark-store (if prefix-only-p (concat name/prefix url) name/prefix)
                                   (cdr (bookmark-make-record)) nil))
      (error (setq failure  err)))
    (if (not failure)
        bmk                             ; Return the bookmark.
      (error "Failed to create bookmark for `%s':\n%s\n" url failure))))

;;; Bound to `C-x p c f'
;;;###autoload
(defun bmkp-file-target-set (file &optional prefix-only-p name/prefix no-overwrite msgp)
  "Set a bookmark for FILE.  Return the bookmark.
The bookmarked position is the beginning of the file.
Interactively you are prompted for FILE.  Completion is available.
You can use `M-n' to pick up the file name at point, or if none then
the visited file.

You are also prompted for the bookmark name.  But with a prefix arg,
you are prompted only for a bookmark-name prefix.  In that case, the
bookmark name is the prefix followed by the non-directory part of
FILE.

From Lisp code, optional arg NO-OVERWRITE is passed to
`bookmark-store': non-nil means do not overwrite an existing bookmark
that has the same name."
  (interactive
   (list (read-file-name "File: " nil
                         (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                 (run-hook-with-args-until-success 'file-name-at-point-functions)
                               (ffap-guesser))
                             (thing-at-point 'filename)
                             (buffer-file-name)))
         current-prefix-arg
         (if current-prefix-arg
             (read-string "Prefix for bookmark name: ")
           (bmkp-completing-read-lax "Bookmark name"))
         'MSG))
  (unless name/prefix (setq name/prefix  ""))
  (let ((bookmark-make-record-function  (bmkp-make-record-for-target-file file))
        bmk failure)
    (condition-case err
        (setq bmk  (bookmark-store
                    (if prefix-only-p (concat name/prefix (file-name-nondirectory file)) name/prefix)
                    (cdr (bookmark-make-record)) no-overwrite))
      (error (setq failure  (error-message-string err))))
    (if (not failure)
        (prog1 bmk                      ; Return the bookmark.
          (when (and msgp  (not (file-exists-p file)))
            (message "File name is now bookmarked, but no such file yet: `%s'"
                     (expand-file-name file))))
      (error "Failed to create bookmark for `%s':\n%s\n" file failure))))

(defun bmkp-make-record-for-target-file (file)
  "Return a function that creates a bookmark record for FILE.
The bookmarked position will be the beginning of the file."
  ;; $$$$$$ Maybe need a way to bypass default handler, at least for autofiles.
  ;;        Doesn't seem to make much sense to use a handler such as a shell cmd in this context. (?)
  (let ((default-handler  (condition-case nil (bmkp-default-handler-for-file file) (error nil))))
    (cond (default-handler              ; User default handler
              `(lambda () '((filename . ,file) (position . 0) (handler . ,default-handler))))
          ;; Non-user defaults.
          ((and (require 'image nil t) (require 'image-mode nil t) ; Image
                (condition-case nil (image-type file) (error nil)))
           'image-bookmark-make-record)
          ((let ((case-fold-search  t)) (string-match "\\([.]au$\\|[.]wav$\\)" file)) ; Sound
           `(lambda () '((filename . ,file) (handler . bmkp-sound-jump))))
          (t
           `(lambda () '((filename . ,file) (position . 0)))))))

;;;###autoload
(defalias 'bmkp-bookmark-a-file 'bmkp-autofile-set)
;;;###autoload
(defun bmkp-autofile-set (file &optional dir prefix msgp) ; Bound to `C-x p c a'
  "Set a bookmark for FILE, autonaming the bookmark for the file.
Return the bookmark.
Interactively, you are prompted for FILE.  You can use `M-n' to pick
up the file name at point, or if none then the visited file.

The bookmark name is the non-directory part of FILE, but with a prefix
arg you are also prompted for a PREFIX string to prepend to the
bookmark name.  The bookmarked position is the beginning of the file.

Note that if you provide PREFIX then the bookmark will not satisfy
`bmkp-autofile-bookmark-p' unless you provide the same PREFIX to that
predicate.

The bookmark's file name is FILE if absolute.  If relative then it is
FILE expanded in DIR, if non-nil, or in the current directory
\(`default-directory').

If a bookmark with the same name already exists for the same file name
then do nothing.

Otherwise, create a new bookmark for the file, even if a bookmark with
the same name already exists.  This means that you can have more than
one autofile bookmark with the same bookmark name and the same
relative file name (non-directory part), but with different absolute
file names."
  (interactive
   (list (read-file-name "File: " nil
                         (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                 (run-hook-with-args-until-success 'file-name-at-point-functions)
                               (ffap-guesser))
                             (thing-at-point 'filename)
                             (buffer-file-name)))
         nil
         (and current-prefix-arg (read-string "Prefix for bookmark name: "))
         'MSG))
  (let* ((dir-to-use  (if (file-name-absolute-p file)
                         (file-name-directory file)
                       (or dir default-directory)))
        ;; Look for existing bookmark with same name, same file, in `dir-to-use'.
         (bmk         (bmkp-get-autofile-bookmark file dir-to-use prefix)))
    ;; If BMK was found, then instead of doing nothing we could replace the existing BMK with a new
    ;; one, as follows:
    ;; (let ((bookmark-make-record-function (bmkp-make-record-for-target-file file)))
    ;;   (bmkp-replace-existing-bookmark bmk)) ; Update the existing bookmark.    
    (or bmk                             ; Do nothing, and return the bookmark.
        ;; Create a new bookmark, and return it.
        (bmkp-file-target-set (expand-file-name file dir-to-use) t prefix 'NO-OVERWRITE msgp))))

(defun bmkp-get-autofile-bookmark (file &optional dir prefix)
  "Return an existing autofile bookmark for FILE, or nil if there is none.
The bookmark name is the non-directory part of FILE, but if PREFIX is
non-nil then it is PREFIX prepended to the non-directory part of FILE.

The bookmark returned has FILE as the non-directory part of its
`filename' property.

The directory part of property `filename' is the directory part of
FILE, if FILE is absolute.  Otherwise, it is DIR, if non-nil, or
`default-directory' otherwise."
  (let* ((fname       (file-name-nondirectory file))
         (bname       (if prefix (concat prefix fname) fname))
         (dir-to-use  (if (file-name-absolute-p file)
                          (file-name-directory file)
                        (or dir default-directory))))
    ;; Look for existing bookmark with same name, same file, in `dir-to-use'.
    (catch 'bmkp-get-autofile-bookmark
      (dolist (bmk  bookmark-alist)
        (when (string= bname (bookmark-name-from-full-record bmk))
          (let* ((bfil  (bookmark-get-filename bmk))
                 (bdir  (and bfil (file-name-directory bfil))))
            (when (and bfil
                       (bmkp-same-file-p fname (file-name-nondirectory bfil))
                       (bmkp-same-file-p bdir dir-to-use))
              (throw 'bmkp-get-autofile-bookmark bmk))))) ; Return the bookmark.
      nil)))

;;;###autoload
(defalias 'bmkp-tag-a-file 'bmkp-autofile-add-tags) ; Bound to `C-x p t + a'
;;;###autoload
(defun bmkp-autofile-add-tags (file tags &optional dir prefix msgp no-cache-update-p)
  "Add TAGS to autofile bookmark for FILE.
Interactively, you are prompted for FILE and then TAGS.
When prompted for FILE you can use `M-n' to pick up the file name at
point, or if none then the visited file.

When prompted for tags, hit `RET' to enter each tag, then hit `RET'
again after the last tag.  You can use completion to enter each tag.
Completion is lax: you are not limited to existing tags.

TAGS is a list of strings. DIR, PREFIX are as for `bmkp-autofile-set'.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags added."
  (interactive
   (list (read-file-name "File: " nil
                         (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                                 (run-hook-with-args-until-success 'file-name-at-point-functions)
                               (ffap-guesser))
                             (thing-at-point 'filename)
                             (buffer-file-name)))
         (bmkp-read-tags-completing)
         nil
         (and current-prefix-arg (read-string "Prefix for bookmark name: "))
         'msg))
  (bmkp-add-tags (bmkp-autofile-set file dir prefix) tags msgp no-cache-update-p))
  
;;;###autoload
(defalias 'bmkp-untag-a-file 'bmkp-autofile-remove-tags) ; Bound to `C-x p t - a'
;;;###autoload
(defun bmkp-autofile-remove-tags (file tags &optional dir prefix msgp no-cache-update-p)
  "Remove TAGS from autofile bookmark for FILE.
Interactively, you are prompted for TAGS and then FILE.
With Emacs 22 and later, only files with at least one of the given
tags are candidates.

When prompted for tags, hit `RET' to enter each tag to be removed,
then hit `RET' again after the last tag.  You can use completion to
enter each tag.

When prompted for FILE you can use `M-n' to pick up the file name at
point, or if none then the visited file.

TAGS is a list of strings. DIR, PREFIX are as for `bmkp-autofile-set'.
Non-nil MSGP means display a message about the addition.
Non-nil NO-CACHE-UPDATE-P means do not update `bmkp-tags-alist'.
Return the number of tags removed."
  (interactive
   (let* ((pref  (and current-prefix-arg (read-string "Prefix for bookmark name: ")))
          (tgs   (bmkp-read-tags-completing))
          (fil   (condition-case nil
                     (read-file-name
                      "File: " nil
                      (or (if (boundp 'file-name-at-point-functions) ; In `files.el', Emacs 23.2+.
                              (run-hook-with-args-until-success 'file-name-at-point-functions)
                            (ffap-guesser))
                          (thing-at-point 'filename)
                          (buffer-file-name))
                      t nil
                      (lambda (ff)      ; PREDICATE - only for Emacs 22+.
                        (let* ((bmk   (bmkp-get-autofile-bookmark ff nil pref))
                               (btgs  (and bmk (bmkp-get-tags bmk))))
                          (and btgs  (catch 'bmkp-autofile-remove-tags
                                       (dolist (tag  tgs)
                                         (when (not (member tag btgs))
                                           (throw 'bmkp-autofile-remove-tags nil)))
                                       t)))))
                   (error (read-file-name
                           "File: " nil
                           (or (ffap-guesser)
                               (thing-at-point 'filename)
                               (buffer-file-name)))))))
     (list fil tgs nil pref 'MSG)))
  (bmkp-remove-tags (bmkp-autofile-set file dir prefix) tags msgp no-cache-update-p))

;;;###autoload
(defun bmkp-purge-notags-autofiles (&optional prefix) ; Not bound
  "Delete all autofile bookmarks that have no tags.
With a prefix arg, you are prompted for a PREFIX for the bookmark name."
  (interactive (if (not (y-or-n-p "Delete all autofile bookmarks that do not have tags? "))
                   (error "Deletion cancelled")
                 (list (and current-prefix-arg (read-string "Prefix for bookmark name: ")))))
  (let ((bmks  (bmkp-autofile-alist-only prefix))
        record tags)
    ;; Needs Bookmark+ version of `bookmark-delete', which accepts a bookmark, not just its name.
    (dolist (bmk  bmks)
      (when (and (setq tags  (assq 'tags (bookmark-get-bookmark-record bmk)))
                 (or (not tags) (null (cdr tags))))
        (bookmark-delete bmk)))
    (bmkp-tags-list)))                  ; Update the tags cache.

;; $$$$$$ Not used currently.
(defun bmkp-replace-existing-bookmark (bookmark)
  "Replace existing BOOKMARK with a new one of the same name.
Return the new bookmark.
BOOKMARK is a full bookmark record, not a bookmark name.
This just replaces the existing bookmark data with the data for a new
bookmark, based on `bookmark-make-record-function'.  The bookmark name
is unchanged."
  (let (failure)
    (condition-case err
        (progn                          ; Code similar to `bookmark-store'.
          (setcdr bookmark (cdr (bookmark-make-record)))
          (bmkp-maybe-save-bookmarks)
          (setq bookmark-current-bookmark  (bookmark-name-from-full-record bookmark))
          (bookmark-bmenu-surreptitiously-rebuild-list))
      (error (setq failure  (error-message-string err))))
    (if (not failure)
        bookmark                        ; Return the bookmark.
      (error "Failed to update bookmark `%s':\n%s\n"
             (bookmark-name-from-full-record bookmark) failure))))

(defun bmkp-default-handler-for-file (filename)
  "Return a default bookmark handler for FILENAME.
It is a Lisp function.  Typically it runs a shell command.

The shell command is the first one found by checking, in order:
`bmkp-default-handler-user', `dired-guess-default',
`mailcap-file-default-commands' (Emacs 23+).

Alternatively `bmkp-default-handler-user' can provide a Lisp function
\(a symbol or a lambda form) directly for FILENAME.  In that case, that
function is applied directly to FILENAME."
  (let* ((bmkp-user  (bmkp-default-handler-user filename))
         (shell-cmd  (or (and (stringp bmkp-user) bmkp-user)
                         (and (require 'dired-x nil t)
                              (let* ((case-fold-search
                                      (or (and (boundp 'dired-guess-shell-case-fold-search)
                                               dired-guess-shell-case-fold-search)
                                          case-fold-search))
                                     (default  (dired-guess-default (list filename))))
                                (if (consp default) (car default) default)))
                         (and (require 'mailcap nil t) ; Emacs 23+
                              (car (mailcap-file-default-commands (list filename)))))))
    (cond ((stringp shell-cmd) `(lambda (bmk)
                                 (dired-do-shell-command ,shell-cmd nil ',(list filename))))
          ((or (functionp bmkp-user) (and bmkp-user (symbolp bmkp-user)))
           `(lambda (bmk) (funcall #',bmkp-user ,filename)))
          (t nil))))    

(defun bmkp-default-handler-user (filename)
  "Return default handler for FILENAME.
The value is based on `bmkp-default-handler-associations'."
  (catch 'bmkp-default-handler-user
    (dolist (assn  bmkp-default-handler-associations)
      (when (string-match (car assn) filename)
        (throw 'bmkp-default-handler-user (cdr assn))))
    nil))

(defun bmkp-sound-jump (bookmark)
  "Handler for sound files: play the sound file that is BOOKMARK's file."
  (play-sound-file (bookmark-get-filename bookmark)))

(when (> emacs-major-version 21)
  (defun bmkp-compilation-target-set (&optional prefix) ; `C-c C-b'
    "Set a bookmark at the start of the line for this compilation hit.
You are prompted for the bookmark name.  But with a prefix arg, you
are prompted only for a PREFIX string.  In that case, and in Lisp
code, the bookmark name is PREFIX followed by the (relative) file name
of the hit, followed by the line number of the hit."
    (interactive "P")
    (let* ((file+line  (bmkp-compilation-file+line-at (line-beginning-position)))
           (file       (car file+line))
           (line       (cdr file+line)))
      (unless (and file line) (error "Cursor is not on a compilation hit"))
      (save-excursion
        (with-current-buffer (find-file-noselect file)
          (goto-char (point-min)) (forward-line (1- line))
          (if (not prefix)
              (call-interactively #'bookmark-set)
            (when (interactive-p)
              (setq prefix  (read-string "Prefix for bookmark name: ")))
            (unless (stringp prefix) (setq prefix  ""))
            (bookmark-set (format "%s%s, line %s" prefix (file-name-nondirectory file) line)
                          99 'INTERACTIVEP))))))

  (defun bmkp-compilation-file+line-at (&optional pos)
    "Return the file and position indicated by this compilation message.
These are returned as a cons: (FILE . POSITION).
POSITION is the beginning of the line indicated by the message."
    (unless pos (setq pos (point)))
    (let* ((loc        (car (get-text-property pos 'message)))
           (line       (cadr loc))
           (filename   (caar (nth 2 loc)))
           (directory  (cadr (car (nth 2 loc))))
           (spec-dir   (if directory (expand-file-name directory) default-directory)))
      (cons (expand-file-name filename spec-dir) line))))
    
(when (> emacs-major-version 21)
  (defun bmkp-compilation-target-set-all (prefix &optional msgp) ; `C-c C-M-b'
    "Set a bookmark for each hit of a compilation buffer.
NOTE: You can use `C-x C-q' to make the buffer writable and then
      remove any hits that you do not want to bookmark.  Only the hits
      remaining in the buffer are bookmarked.

You are prompted for a PREFIX string to prepend to each bookmark name,
the rest of which is the file name of the hit followed by its line
number."
    (interactive (list (read-string "Prefix for bookmark name: ") 'MSGP))
    (if (y-or-n-p "This will bookmark *EACH* hit in the buffer.  Continue? ")
        (let ((count  0))
          (save-excursion
            (goto-char (point-min))
            (when (get-text-property (point) 'message) ; Visible part of buffer starts with a hit
              (condition-case nil       ; because buffer is narrowed or header text otherwise removed.
                  (bmkp-compilation-target-set prefix) ; Ignore error here (e.g. killed buffer).
                (error nil))
              (setq count  (1+ count)))
            (while (and (condition-case nil (progn (compilation-next-error 1) t) (error nil))
                        (not (eobp)))
              (condition-case nil
                  (bmkp-compilation-target-set prefix) ; Ignore error here (e.g. killed buffer).
                (error nil))
              (setq count  (1+ count)))
            (when msgp (message "Set %d bookmarks" count))))
      (message "OK - canceled"))))


;; We could make the `occur' code work for Emacs 20 & 21 also, but you would not be able to
;; delete some occurrences and bookmark only the remaining ones.

(when (> emacs-major-version 21)
  (defun bmkp-occur-target-set (&optional prefix) ; `C-c C-b'
    "Set a bookmark at the start of the line for this `(multi-)occur' hit.
You are prompted for the bookmark name.  But with a prefix arg, you
are prompted only for a PREFIX string.  In that case, and in Lisp
code, the bookmark name is PREFIX followed by the buffer name of the
hit, followed by the line number of the hit.

You can use this only in `Occur' mode (commands such as `occur' and
`multi-occur')."
    (interactive "P")
    (unless (eq major-mode 'occur-mode) (error "You must be in `occur-mode'"))
    (let* ((line  (and prefix
                       (save-excursion
                         (forward-line 0)
                         ;; We could use [: ] here, to handle `moccur', but that loses anyway for
                         ;; `occur-mode-find-occurrence', so we would need other hoops too.
                         (re-search-forward "^\\s-+\\([0-9]+\\):" (line-end-position) 'NOERROR)
                         (or (format "%5d" (string-to-number (match-string 1))) ""))))
           (mkr   (occur-mode-find-occurrence))
           (buf   (marker-buffer mkr))
           (file  (or (buffer-file-name buf) bmkp-non-file-filename)))
      (save-excursion (with-current-buffer buf
                        (goto-char mkr)
                        (if (not prefix)
                            (call-interactively #'bookmark-set)
                          (when (interactive-p)
                            (setq prefix  (read-string "Prefix for bookmark name: ")))
                          (unless (stringp prefix) (setq prefix  ""))
                          (bookmark-set (format "%s%s, line %s" prefix buf line) 99 'INTERACTIVEP)))))))

(when (> emacs-major-version 21)
  (defun bmkp-occur-target-set-all (&optional prefix msgp) ; `C-c C-M-b'
    "Set a bookmark for each hit of a `(multi-)occur' buffer.
NOTE: You can use `C-x C-q' to make the buffer writable and then
      remove any hits that you do not want to bookmark.  Only the hits
      remaining in the buffer are bookmarked.

You are prompted for a PREFIX string to prepend to each bookmark name,
the rest of which is the buffer name of the hit followed by its line
number.

You can use this only in `Occur' mode (commands such as `occur' and
`multi-occur').

See also command `bmkp-occur-create-autonamed-bookmarks', which
creates autonamed bookmarks to all `occur' and `multi-occur' hits."
    (interactive (list (read-string "Prefix for bookmark name: ") 'MSGP))
    (if (y-or-n-p "This will bookmark *EACH* hit in the buffer.  Continue? ")
        (let ((count  0))
          (save-excursion
            (goto-char (point-min))
            (while (condition-case nil
                       (progn (occur-next) t) ; "No more matches" ends loop.
                     (error nil))
              (condition-case nil
                  (bmkp-occur-target-set prefix) ; Ignore error here (e.g. killed buffer).
                (error nil))
              (setq count  (1+ count)))
            (when msgp (message "Set %d bookmarks" count))))
      (message "OK - canceled"))))


;;(@* "Other Bookmark+ Functions (`bmkp-*')")
;;  *** Other Bookmark+ Functions (`bmkp-*') ***

;;;###autoload
(defun bmkp-describe-bookmark (bookmark &optional defn)
  "Describe BOOKMARK.
With a prefix argument, show the internal definition of the bookmark.
BOOKMARK is a bookmark name or a bookmark record.

Starting with Emacs 22, if the file is an image file then:
* Show a thumbnail of the image as well.
* If you have command-line tool `exiftool' installed and in your
  `$PATH' or `exec-path', then show EXIF data (metadata) about the
  image.  See standard Emacs library `image-dired.el' for more
  information about `exiftool'"
  (interactive (list (bookmark-completing-read
                      "Describe bookmark"
                      (or (and (fboundp 'bmkp-default-lighted) (bmkp-default-lighted))
                          (bmkp-default-bookmark-name)))
                     current-prefix-arg))
  (if defn
      (bmkp-describe-bookmark-internals bookmark)
    (setq bookmark     (bookmark-get-bookmark bookmark))
    (help-setup-xref (list #'bmkp-describe-bookmark bookmark) (interactive-p))
    (let ((help-text  (bmkp-bookmark-description bookmark)))
      (with-output-to-temp-buffer "*Help*" (princ help-text))
      (with-current-buffer "*Help*"
        (save-excursion
          (goto-char (point-min))
          (when (re-search-forward "@#%&()_IMAGE-HERE_()&%#@\\(.+\\)" nil t)
            (let* ((image-file        (match-string 1))
                   (image-string      (save-match-data
                                        (apply #'propertize "X"
                                               `(display
                                                 ,(append (image-dired-get-thumbnail-image image-file)
                                                          '(:margin 10))
                                                 rear-nonsticky (display)
                                                 mouse-face highlight
                                                 follow-link t
                                                 help-echo "`mouse-2' or `RET': Show full image"
                                                 keymap
                                                 (keymap
                                                  (mouse-2
                                                   . (lambda (e) (interactive "e")
                                                             (find-file ,image-file)))
                                                  (13
                                                   . (lambda () (interactive)
                                                             (find-file ,image-file))))))))
                   (buffer-read-only  nil))
              (replace-match image-string)))))
      help-text)))

(defun bmkp-bookmark-description (bookmark &optional no-image)
  "Help-text description of BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Starting with Emacs 22 and unless optional arg NO-IMAGE is non-nil, if
the file is an image file then the description includes the following:
* A placeholder for a thumbnail image: \"@#%&()_IMAGE-HERE_()&%#@\"
* EXIF data (metadata) about the image, provided you have command-line
  tool `exiftool' installed and in your `$PATH' or `exec-path'.  See
  standard Emacs library `image-dired.el' for more information about
  `exiftool'."
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (let ((bname            (bookmark-name-from-full-record bookmark))
        (buf              (bmkp-get-buffer-name bookmark))
        (file             (bookmark-get-filename bookmark))
        (image-p          (bmkp-bookmark-image-bookmark-p bookmark))
        (location         (bookmark-prop-get bookmark 'location))
        (start            (bookmark-get-position bookmark))
        (end              (bmkp-get-end-position bookmark))
        (created          (bookmark-prop-get bookmark 'created))
        (time             (bmkp-get-visit-time bookmark))
        (visits           (bmkp-get-visits-count bookmark))
        (tags             (mapcar #'bmkp-tag-name (bmkp-get-tags bookmark)))
        (sequence-p       (bmkp-sequence-bookmark-p bookmark))
        (function-p       (bmkp-function-bookmark-p bookmark))
        (variable-list-p  (bmkp-variable-list-bookmark-p bookmark))
        (desktop-p        (bmkp-desktop-bookmark-p bookmark))
        (bookmark-file-p  (bmkp-bookmark-file-bookmark-p bookmark))
        (dired-p          (bmkp-dired-bookmark-p bookmark))
        (gnus-p           (bmkp-gnus-bookmark-p bookmark))
        (info-p           (bmkp-info-bookmark-p bookmark))
        (man-p            (bmkp-man-bookmark-p bookmark))
        (url-p            (bmkp-url-bookmark-p bookmark))
        (w3m-p            (bmkp-w3m-bookmark-p bookmark))
        (annot            (bookmark-get-annotation bookmark))
        no-position-p)
    (setq no-position-p  (not start))
    (when (or sequence-p function-p variable-list-p) (setq no-position-p  t))
    (let* ((help-text
            (concat
             (format "Bookmark `%s'\n%s\n\n" bname (make-string (+ 11 (length bname)) ?-))
             (cond (sequence-p       (format "Sequence:\n%s\n"
                                             (pp-to-string
                                              (bookmark-prop-get bookmark 'sequence))))
                   (function-p       (let ((fn  (bookmark-prop-get bookmark 'function)))
                                       (if (symbolp fn)
                                           (format "Function:\t\t%s\n" fn)
                                         (format "Function:\n%s\n"
                                                 (pp-to-string
                                                  (bookmark-prop-get bookmark 'function))))))
                   (variable-list-p  (format "Variable list:\n%s\n"
                                             (pp-to-string (bookmark-prop-get bookmark 'variables))))
                   (gnus-p           (format "Gnus, group:\t\t%s, article: %s, message-id: %s\n"
                                             (bookmark-prop-get bookmark 'group)
                                             (bookmark-prop-get bookmark 'article)
                                             (bookmark-prop-get bookmark 'message-id)))
                   (man-p            (format "UNIX `man' page for:\t`%s'\n"
                                             (or (bookmark-prop-get bookmark 'man-args)
                                                 ;; WoMan has no variable for the cmd name.
                                                 (bookmark-prop-get bookmark 'buffer-name))))
                   (info-p           (format "Info node:\t\t(%s) %s\n"
                                             (file-name-nondirectory file)
                                             (bookmark-prop-get bookmark 'info-node)))
                   (w3m-p            (format "W3m URL:\t\t%s\n" file))
                   (url-p            (format "URL:\t\t%s\n" location))
                   (desktop-p        (format "Desktop file:\t\t%s\n"
                                             (bookmark-prop-get bookmark 'desktop-file)))
                   (bookmark-file-p  (format "Bookmark file:\t\t%s\n"
                                             (bookmark-prop-get bookmark 'bookmark-file)))
                   (dired-p          (let ((switches  (bookmark-prop-get bookmark 'dired-switches))
                                           (marked    (length (bookmark-prop-get bookmark
                                                                                 'dired-marked)))
                                           (inserted  (length (bookmark-prop-get bookmark
                                                                                 'dired-subdirs)))
                                           (hidden    (length
                                                       (bookmark-prop-get bookmark
                                                                          'dired-hidden-dirs))))
                                       (format "Dired%s:%s\t\t%s\nMarked:\t\t\t%s\n\
Inserted subdirs:\t%s\nHidden subdirs:\t\t%s\n"
                                               (if switches (format " `%s'" switches) "")
                                               (if switches "" (format "\t"))
                                               (expand-file-name file)
                                               marked inserted hidden)))
                   ((equal file bmkp-non-file-filename)
                    (format "Buffer:\t\t\t%s\n" (bmkp-get-buffer-name bookmark)))
                   (file        (concat (format "File:\t\t\t%s\n" (file-name-nondirectory file))
                                        (let ((dir   (file-name-directory (expand-file-name file))))
                                          (and dir (format "Directory:\t\t%s\n" dir)))))
                   (t           "Unknown\n"))
             (unless no-position-p
               (if (bmkp-region-bookmark-p bookmark)
                   (format "Region:\t\t\t%d to %d (%d chars)\n" start end (- end start))
                 (format "Position:\t\t%d\n" start)))
             (and visits  (format "Visits:\t\t\t%d\n" visits))
             (and time    (format "Last visit:\t\t%s\n" (format-time-string "%c" time)))
             (and created (format "Creation:\t\t%s\n" (format-time-string "%c" created)))
             (and tags    (format "Tags:\t\t\t%S\n" tags))
             (and annot   (format "\nAnnotation:\n%s" annot))
             (and (not no-image)
                  (fboundp 'image-file-name-regexp) ; In `image-file.el' (Emacs 22+).
                  (if (fboundp 'string-match-p)
                      (string-match-p (image-file-name-regexp) file)
                    (save-match-data
                      (string-match (image-file-name-regexp) file)))
                  (if (fboundp 'display-graphic-p) (display-graphic-p) window-system)
                  (require 'image-dired nil t)
                  (image-dired-get-thumbnail-image file)
                  (concat "\n@#%&()_IMAGE-HERE_()&%#@" file "\n"))
             (and (not no-image)
                  (fboundp 'image-file-name-regexp) ; In `image-file.el' (Emacs 22+).
                  (if (fboundp 'string-match-p)
                      (string-match-p (image-file-name-regexp) file)
                    (save-match-data
                      (string-match (image-file-name-regexp) file)))                       
                  (progn (message "Gathering image data...") t)
                  (condition-case nil
                      (let ((all  (bmkp-all-exif-data (expand-file-name file))))
                        (concat
                         (and all (not (zerop (length all)))
                              (format "\nImage Data (EXIF)\n-----------------\n%s"
                                      all))))
                    (error nil))))))
      help-text)))

;; This is the same as `help-all-exif-data' in `help-fns+.el', but we avoid requiring that library.
(defun bmkp-all-exif-data (file)
  "Return all EXIF data from FILE, using command-line tool `exiftool'."
  (with-temp-buffer
    (delete-region (point-min) (point-max))
    (unless (eq 0 (call-process shell-file-name nil t nil shell-command-switch
                                (format "exiftool -All \"%s\"" file)))
      (error "Could not get EXIF data"))
    (buffer-substring (point-min) (point-max))))


;;;###autoload
(defun bmkp-describe-bookmark-internals (bookmark)
  "Show the internal definition of the bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record."
  (interactive (list (bookmark-completing-read "Describe bookmark" (bmkp-default-bookmark-name))))
  (setq bookmark  (bookmark-get-bookmark bookmark))
  (help-setup-xref (list #'bmkp-describe-bookmark-internals bookmark) (interactive-p))
  (let* ((bname      (bookmark-name-from-full-record bookmark))
         (help-text  (format "Bookmark `%s'\n%s\n\n%s" bname (make-string (+ 11 (length bname)) ?-)
                             (pp-to-string bookmark))))
    (with-output-to-temp-buffer "*Help*" (princ help-text))
    help-text))

;;;###autoload
(defun bmkp-list-defuns-in-commands-file ()
  "List the functions defined in `bmkp-bmenu-commands-file'.
Typically, these are all commands."
  (interactive)
  (when (and bmkp-bmenu-commands-file (file-readable-p bmkp-bmenu-commands-file))
    (let ((fns  ())
          (buf  (let ((enable-local-variables  nil))
                  (find-file-noselect bmkp-bmenu-commands-file))))
      (help-setup-xref (list #'bmkp-list-defuns-in-commands-file) (interactive-p))
      (with-current-buffer buf
        (goto-char (point-min))
        (while (not (eobp))
          (when (re-search-forward "\\s-*(defun \\([^ \t\n(\"]+\\)[ \t\n(]" nil 'move)
            (push (match-string 1) fns)))
        (setq fns  (nreverse fns)
              fns  (sort fns 'string-lessp)))
      (when (buffer-live-p buf) (kill-buffer buf))
      (with-output-to-temp-buffer "*Help*"
        (princ "Bookmark Commands You Defined (in `bmkp-bmenu-commands-file')") (terpri)
        (princ "------------------------------------------------------------------") (terpri)
        (terpri)
        (let ((non-dups  (bmkp-remove-dups fns)))
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

(defun bmkp-root-or-sudo-logged-p ()
  "Return t if the user logged in using Tramp as `root' or `sudo'.
Otherwise, return nil."
  (catch 'break
    (dolist (ii  (mapcar #'buffer-name (buffer-list)))
      (when (string-match "*tramp/\\(su\\|sudo\\) ." ii) (throw 'break t)))))

(defun bmkp-position-post-context (breg)
  "Return `bookmark-search-size' chars, starting at position BREG.
Return nil if there are not that many chars.
This is text that follows the bookmark's `position'.
This is used for a non-region bookmark."
  (and (>= (- (point-max) breg) bookmark-search-size)
       (buffer-substring-no-properties breg (+ breg bookmark-search-size))))

(defun bmkp-position-post-context-region (breg ereg)
  "Return the region prefix, at BREG.
Return at most `bmkp-region-search-size' or (- EREG BREG) chars.
This is text that follows the bookmark's `position'.
This is used for a region bookmark."
  (buffer-substring-no-properties breg (+ breg (min bmkp-region-search-size (- ereg breg)))))

(defun bmkp-position-pre-context (breg)
  "Return `bookmark-search-size' chars that precede BREG.
Return nil if there are not that many chars.
This is text that precedes the bookmark's `position'.
This is used for a non-region bookmark."
  (and (>= (- breg (point-min)) bookmark-search-size)
       (buffer-substring-no-properties breg (- breg bookmark-search-size))))

(defun bmkp-position-pre-context-region (breg)
  "Return the text preceding the region beginning, BREG.
Return at most `bmkp-region-search-size' chars.
This is text that precedes the bookmark's `position'.
This is used for a region bookmark."
  (buffer-substring-no-properties (max (- breg bmkp-region-search-size) (point-min)) breg))

(defun bmkp-end-position-pre-context (breg ereg)
  "Return the region suffix, ending at EREG.
Return at most `bmkp-region-search-size' or (- EREG BREG) chars.
This is text that precedes the bookmark's `end-position'."
  (buffer-substring-no-properties (- ereg (min bmkp-region-search-size (- ereg breg))) ereg))

(defun bmkp-end-position-post-context (ereg)
  "Return the text following the region end, EREG.
Return at most `bmkp-region-search-size' chars.
This is text that follows the bookmark's `end-position'."
  (buffer-substring-no-properties ereg
                                  (+ ereg (min bmkp-region-search-size (- (point-max) (point))))))

(defun bmkp-position-after-whitespace (position)
  "Move forward from POSITION, skipping over whitespace.  Return point."
  (goto-char position)  (skip-chars-forward " \n\t" (point-max))  (point))

(defun bmkp-position-before-whitespace (position)
  "Move backward from POSITION, skipping over whitespace.  Return point."
  (goto-char position)  (skip-chars-backward " \n\t" (point-min))  (point))

(defun bmkp-save-new-region-location (bookmark beg end)
  "Update and save `bookmark-alist' for BOOKMARK, relocating its region.
BOOKMARK is a bookmark record.
BEG and END are the new region limits for BOOKMARK.
Do nothing and return nil if `bmkp-save-new-location-flag' is nil.
Otherwise, return non-nil if region was relocated."
  (and bmkp-save-new-location-flag
       (y-or-n-p "Region relocated.  Do you want to save new region limits? ")
       (progn
         (bookmark-prop-set bookmark 'front-context-string (bmkp-position-post-context-region
                                                            beg end))
         (bookmark-prop-set bookmark 'rear-context-string (bmkp-position-pre-context-region beg))
         (bookmark-prop-set bookmark 'front-context-region-string (bmkp-end-position-pre-context
                                                                   beg end))
         (bookmark-prop-set bookmark 'rear-context-region-string (bmkp-end-position-post-context end))
         (bookmark-prop-set bookmark 'position beg)
         (bookmark-prop-set bookmark 'end-position end)
         (bmkp-maybe-save-bookmarks)
         t)))

(defun bmkp-handle-region-default (bookmark)
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
         (end-pos          (bmkp-get-end-position bmk))
         (reg-retrieved-p  t)
         (reg-relocated-p  nil))
    (unless (and (string= bor-str (buffer-substring-no-properties (point) (+ (point)
                                                                             (length bor-str))))
                 (save-excursion
                   (goto-char end-pos)
                   (string= eor-str (buffer-substring-no-properties (point) (- (point)
                                                                               (length bor-str))))))
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
                    end  (and end (bmkp-position-before-whitespace end))))))
        ;; If failed to find END, go to eob and search backward for BEG.
        (unless end (goto-char (point-max)))
        (if (search-backward bor-str (point-min) t) ; Find BEG, using `bor-str'.
            (setq beg  (point))
          ;; Verify that region is not after context.
          (unless (search-backward ar-str (point-min) t)
            (when (search-backward br-str (point-min) t) ; Find BEG, using `br-str'.
              (setq beg  (match-end 0)
                    beg  (and beg (bmkp-position-after-whitespace beg))))))
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
           (when bmkp-show-end-of-region
             (let ((end-win  (save-excursion (forward-line (window-height)) (end-of-line) (point))))
               ;; Bounce point and mark.
               (save-excursion (sit-for 0.6) (exchange-point-and-mark) (sit-for 1))
               ;; Recenter if region end is not visible.
               (when (> end-pos end-win) (recenter 1))))
           ;; Maybe save region.
           (if (and reg-relocated-p (bmkp-save-new-region-location bmk pos end-pos))
               (message "Saved relocated region (from %d to %d)" pos end-pos)
             (message "Region is from %d to %d" pos end-pos)))
          (t                            ; No region.  Go to old start.  Don't push-mark.
           (goto-char pos) (forward-line 0)
           (message "No region from %d to %d" pos end-pos)))))

;; Same as `line-number-at-pos', which is not available until Emacs 22.
(defun bmkp-line-number-at-pos (&optional pos)
  "Buffer line number at position POS. Current line number if POS is nil.
Counting starts at (point-min), so any narrowing restriction applies."
  (1+ (count-lines (point-min) (save-excursion (when pos (goto-char pos)) (forward-line 0) (point)))))

(defun bmkp-goto-position (bookmark file buf bufname pos forward-str behind-str)
  "Go to a bookmark that has no region.
Update the recorded position if `bmkp-save-new-location-flag'.
Arguments are respectively the bookmark, its file, buffer, buffer
name, recorded position, and the context strings for the position."
  (if (and file (file-readable-p file) (not (buffer-live-p buf)))
      (with-current-buffer (find-file-noselect file) (setq buf  (buffer-name)))
    ;; No file found.  See if a non-file buffer exists for this.  If not, raise error.
    (unless (or (and buf (get-buffer buf))
                (and bufname (get-buffer bufname) (not (string= buf bufname))))
      (signal 'file-error `("Jumping to bookmark" "No such file or directory" ,file))))
  (set-buffer (or buf bufname))
  (when bmkp-jump-display-function
    (save-current-buffer (funcall bmkp-jump-display-function (current-buffer))))
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
  (when (and (/= pos (point))  bmkp-save-new-location-flag)
    (bookmark-prop-set bookmark 'position     (point))
    (bookmark-prop-set bookmark 'end-position (point))
    (bmkp-maybe-save-bookmarks))
  (/= pos (point)))                     ; Return value indicates whether POS was accurate.

(defun bmkp-jump-sequence (bookmark)
  "Handle a sequence bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for sequence bookmarks."
  (dolist (bmk  (bookmark-prop-get bookmark 'sequence))
    (bookmark--jump-via bmk bmkp-sequence-jump-display-function))
  (message "Done invoking bookmarks in sequence `%s'"
           (if (stringp bookmark) bookmark (bookmark-name-from-full-record bookmark))))

(defun bmkp-jump-function (bookmark)
  "Handle a function bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for function bookmarks."
  (funcall (bookmark-prop-get bookmark 'function)))

(defun bmkp-make-bookmark-list-record ()
  "Create and return a bookmark-list bookmark record.
This records the current state of buffer `*Bookmark List*': the sort
order, filter function, regexp pattern, title, and omit list."
  (let ((state  `((last-sort-comparer            . ,bmkp-sort-comparer)
                  (last-reverse-sort-p           . ,bmkp-reverse-sort-p)
                  (last-reverse-multi-sort-p     . ,bmkp-reverse-multi-sort-p)
                  (last-bmenu-filter-function    . ,bmkp-bmenu-filter-function)
                  (last-bmenu-filter-pattern     . ,bmkp-bmenu-filter-pattern)
                  (last-bmenu-omitted-bookmarks  . ,(bmkp-maybe-unpropertize-bookmark-names
                                                     bmkp-bmenu-omitted-bookmarks))
                  (last-bmenu-title              . ,bmkp-bmenu-title)
                  (last-bmenu-toggle-filenames   . ,bookmark-bmenu-toggle-filenames))))
    `(,@(bookmark-make-record-default 'no-file 'no-context)
      (filename      . ,bmkp-non-file-filename)
      (bookmark-list . ,state)
      (handler       . bmkp-jump-bookmark-list))))

(add-hook 'bookmark-bmenu-mode-hook
          #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                            'bmkp-make-bookmark-list-record)))

(defun bmkp-jump-bookmark-list (bookmark)
  "Jump to bookmark-list bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bmkp-make-bookmark-list-record'."
  (let ((state  (bookmark-prop-get bookmark 'bookmark-list)))
    (setq bmkp-sort-comparer               (cdr (assq 'last-sort-comparer            state))
          bmkp-reverse-sort-p              (cdr (assq 'last-reverse-sort-p           state))
          bmkp-reverse-multi-sort-p        (cdr (assq 'last-reverse-multi-sort-p     state))
          bmkp-bmenu-filter-function       (cdr (assq 'last-bmenu-filter-function    state))
          bmkp-bmenu-filter-pattern        (or (cdr (assq 'last-bmenu-filter-pattern state)) "")
          bmkp-bmenu-omitted-bookmarks     (cdr (assq 'last-bmenu-omitted-bookmarks  state))
          bmkp-bmenu-title                 (cdr (assq 'last-bmenu-title              state))
          bookmark-bmenu-toggle-filenames  (cdr (assq 'last-bmenu-toggle-filenames   state))))
  (let ((bookmark-alist  (if bmkp-bmenu-filter-function
                             (funcall bmkp-bmenu-filter-function)
                           bookmark-alist)))
    (setq bmkp-latest-bookmark-alist  bookmark-alist)
    (bookmark-bmenu-list 'filteredp)
    (when (get-buffer "*Bookmark List*") (pop-to-buffer "*Bookmark List*"))))

;; Bookmark-file bookmarks.
;;;###autoload
(defun bmkp-set-bookmark-file-bookmark (file &optional msgp) ; Bound to `C-x p x'
  "Create a bookmark that loads bookmark-file FILE when \"jumped\" to.
You are prompted for the names of the bookmark file and the bookmark."
  (interactive (list (let ((insert-default-directory  t))
                       (read-file-name
                        "Create bookmark to load bookmark file: " "~/"
                        ;; Default file as default choice, unless it's already current.
                        (and (not (bmkp-same-file-p bookmark-default-file bmkp-current-bookmark-file))
                             bookmark-default-file)
                        'confirm))
                     'MSG))
  (setq file  (expand-file-name file))
  (unless (file-readable-p file) (error "Unreadable bookmark file `%s'" file))
  (with-current-buffer (let ((enable-local-variables  ())) (find-file-noselect file))
    (goto-char (point-min))
    (condition-case nil                 ; Check whether it's a valid bookmark file.
        (progn (bookmark-maybe-upgrade-file-format)
               (unless (listp (bookmark-alist-from-buffer)) (error "")))
      (error (error "Not a valid bookmark file: `%s'" file))))
  (let ((bookmark-make-record-function  #'(lambda () (bmkp-make-bookmark-file-record file))))
    (call-interactively #'bookmark-set))
  (when msgp (message "Set bookmark-file bookmark")))

(defun bmkp-make-bookmark-file-record (bookmark-file)
  "Create and return a bookmark-file bookmark record.
Records the BOOKMARK-FILE name.
Adds a handler that tests the prefix arg and loads the bookmark file
either as a replacement for the current bookmark file or as a
supplement to it."
  `(,@(bookmark-make-record-default 'no-file 'no-context)
    (filename      . ,bookmark-file)
    (bookmark-file . ,bookmark-file)
    (handler       . bmkp-jump-bookmark-file)))

(defun bmkp-jump-bookmark-file (bookmark &optional switchp no-msg)
  "Jump to bookmark-file bookmark BOOKMARK, which loads the bookmark file.
BOOKMARK is a bookmark name or a bookmark record.
Non-nil SWITCHP means overwrite the current bookmark list.
Handler function for record returned by `bmkp-make-bookmark-file-record'."
  (let ((file        (bookmark-prop-get bookmark 'bookmark-file))
        (overwritep  (and (or switchp current-prefix-arg)
                          (y-or-n-p "Switch to new bookmark file, instead of just adding it? "))))
    (bookmark-load file overwritep))
  ;; This `throw' is only for the case where this handler is is called from `bookmark--jump-via'.
  ;; It just tells `bookmark--jump-via' to skip the rest of what it does after calling the handler.
  (condition-case nil
      (throw 'bookmark--jump-via 'BOOKMARK-FILE-JUMP)
    (no-catch nil)))

;;;###autoload
(defun bmkp-bookmark-file-jump (bookmark-name &optional switchp no-msg) ; `C-x j x'
  "Jump to a bookmark-file bookmark, which means load its bookmark file.
With a prefix argument, switch to the new bookmark file.
Otherwise, load it to supplement the current bookmark list."
  (interactive
   (let ((alist  (bmkp-bookmark-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "bookmark-file " alist nil nil 'bmkp-bookmark-file-history)
           current-prefix-arg)))
  (bmkp-jump-bookmark-file bookmark-name switchp no-msg))

;; Desktop bookmarks
;;;###autoload
(defun bmkp-set-desktop-bookmark (desktop-file) ; Bound globally to `C-x p K', `C-x r K', `C-x p c K'
  "Save the desktop as a bookmark.
You are prompted for the desktop-file location and the bookmark name."
  (interactive (list (read-file-name "Save desktop in file: ")))
  (set-text-properties 0 (length desktop-file) nil desktop-file)
  (unless (file-name-absolute-p desktop-file) (setq desktop-file  (expand-file-name desktop-file)))
  (unless (condition-case nil (require 'desktop nil t) (error nil))
    (error "You must have library `desktop.el' to use this command"))
  (let ((desktop-basefilename     (file-name-nondirectory desktop-file)) ; Emacs < 22
        (desktop-base-file-name   (file-name-nondirectory desktop-file)) ; Emacs 23+
        (desktop-dir              (file-name-directory desktop-file))
        (desktop-restore-eager    t)    ; Don't bother with lazy restore.
        (desktop-globals-to-save  (bmkp-remove-if #'(lambda (elt)
                                                      (memq elt bmkp-desktop-no-save-vars))
                                                  desktop-globals-to-save)))
    (if (< emacs-major-version 22)
        (desktop-save desktop-dir)      ; Emacs < 22 has no locking.
      (desktop-save desktop-dir 'RELEASE))
    (message "Desktop saved in `%s'" desktop-file)
    (let ((bookmark-make-record-function  #'(lambda () (bmkp-make-desktop-record desktop-file))))
      (call-interactively #'bookmark-set))))

(defun bmkp-make-desktop-record (desktop-file)
  "Create and return a desktop bookmark record.
DESKTOP-FILE is the absolute file name of the desktop file to use."
  `(,@(bookmark-make-record-default 'no-file 'no-context)
    (filename     . ,bmkp-non-file-filename)
    (desktop-file . ,desktop-file)
    (handler      . bmkp-jump-desktop)))

(defun bmkp-jump-desktop (bookmark)
  "Jump to desktop bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bmkp-make-desktop-record'."
  (let ((desktop-file  (bookmark-prop-get bookmark 'desktop-file)))
    (unless (condition-case nil (require 'desktop nil t) (error nil))
      (error "You must have library `desktop.el' to use this command"))
    ;; (unless desktop-file (error "Not a desktop-bookmark: %S" bookmark)) ; Shouldn't happen.
    (bmkp-desktop-change-dir desktop-file)
    (unless (bmkp-desktop-read desktop-file) (error "Could not load desktop file"))))

;; Derived from code in `desktop-change-dir'.
;;;###autoload
(defun bmkp-desktop-change-dir (desktop-file)
  "Change to desktop saved in DESKTOP-FILE.
Kill the desktop as specified by variables `desktop-save-mode' and
 `desktop-save' (starting with Emacs 22).
Clear the desktop and load DESKTOP-FILE DIRNAME."
  (interactive (list (read-file-name "Change to desktop file: ")))
  (set-text-properties 0 (length desktop-file) nil desktop-file)
  (unless (file-name-absolute-p desktop-file) (setq desktop-file  (expand-file-name desktop-file)))
  (unless (condition-case nil (require 'desktop nil t) (error nil))
    (error "You must have library `desktop.el' to use this command"))
  (let ((desktop-basefilename     (file-name-nondirectory desktop-file)) ; Emacs < 22
        (desktop-base-file-name   (file-name-nondirectory desktop-file)) ; Emacs 23+
        (desktop-dir              (file-name-directory desktop-file))
        (desktop-restore-eager    t)    ; Don't bother with lazy restore.
        (desktop-globals-to-save  (bmkp-remove-if #'(lambda (elt)
                                                      (memq elt bmkp-desktop-no-save-vars))
                                                  desktop-globals-to-save)))
    (bmkp-desktop-kill)
    (desktop-clear)
    (if (< emacs-major-version 22) (desktop-read) (desktop-read desktop-dir))))
    
;; Derived from code in `desktop-kill'.
(defun bmkp-desktop-kill ()
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
  (when (fboundp 'desktop-release-lock) (desktop-release-lock))) ; Not defined for Emacs 20.

;; Derived from code in `desktop-read'.
;;;###autoload
(defun bmkp-desktop-read (file)
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
                 (if (and (boundp 'desktop-buffer-args-list) desktop-buffer-args-list)
                     (format ", %d to be restored lazily" (length desktop-buffer-args-list))
                   "")))
      t)))                              ; Return t, meaning successfully loaded.

;;;###autoload
(defun bmkp-desktop-delete (bookmark-name)
  "Delete desktop bookmark BOOKMARK-NAME, and delete its desktop file.
Release the lock file in that desktop's directory.
\(This means that if you currently have locked a different desktop
in the same directory, then you will need to relock it.)"
  (interactive (let ((alist  (bmkp-desktop-alist-only)))
                 (list (bmkp-read-bookmark-for-type "desktop " alist nil nil 'bmkp-desktop-history
                                                    "Delete "))))
  (let ((desktop-file  (bookmark-prop-get bookmark-name 'desktop-file)))
    (unless desktop-file (error "Not a desktop-bookmark: `%s'" bookmark-name))
    ;; Release the desktop lock file in the same directory as DESKTOP-FILE.
    ;; This will NOT be the right thing to do if a desktop file different from DESKTOP-FILE
    ;; is currently locked in the same directory.
    (let ((desktop-dir  (file-name-directory desktop-file)))
      (when (fboundp 'desktop-release-lock) (desktop-release-lock))) ; Not defined for Emacs 20.
    (when (file-exists-p desktop-file) (delete-file desktop-file)))
  (bookmark-delete bookmark-name))

;; Variable-list bookmarks
(when (boundp 'wide-n-restrictions)
  (defun bmkp-set-restrictions-bookmark ()
    "Save the ring of restrictions for the current buffer as a bookmark.
You need library `wide-n.el' to use the bookmark created."
    (interactive)
    (let ((bookmark-make-record-function
           (lambda () (bmkp-make-variable-list-record
                       `((wide-n-restrictions
                          . ,(mapcar (lambda (x)
                                       (if (eq x 'all)
                                           'all
                                         (let ((beg  (car x)) ; Convert markers to number positions.
                                               (end  (cdr x)))
                                           (cons (if (markerp beg) (marker-position beg) beg)
                                                 (if (markerp end) (marker-position end) end)))))
                                     wide-n-restrictions)))))))
      (call-interactively #'bookmark-set)
      (unless (featurep 'wide-n) (message "Bookmark created, but you need `wide-n.el' to use it")))))

;;;###autoload
(defun bmkp-set-variable-list-bookmark (variables)
  "Save a list of variables as a bookmark.
Interactively, read the variables to save, using
`bmkp-read-variables-completing'."
  (interactive (list (bmkp-read-variables-completing)))
  (let ((bookmark-make-record-function  #'(lambda () (bmkp-make-variable-list-record variables))))
    (call-interactively #'bookmark-set)))

(defun bmkp-create-variable-list-bookmark (bookmark-name vars vals &optional buffer-name)
  "Create a variable-list bookmark named BOOKMARK-NAME from VARS and VALS.
VARS and VALS are corresponding lists of variables and their values.

Optional arg BUFFER-NAME is the buffer name to use for the bookmark (a
string).  This is useful if some of the variables are buffer-local.
If BUFFER-NAME is nil, the current buffer name is recorded."
  (eval `(multiple-value-bind ,vars ',vals
          (let ((bookmark-make-record-function
                 (lambda () (bmkp-make-variable-list-record ',vars ,buffer-name))))
            (bookmark-set ,bookmark-name nil t)))))

(defun bmkp-read-variables-completing (&optional option)
  "Read variable names with completion, and return them as a list of symbols.
Reads names one by one, until you hit `RET' twice consecutively.
Non-nil argument OPTION means read only user option names."
  (bookmark-maybe-load-default-file)
  (let ((var   (bmkp-read-variable "Variable (RET for each, empty input to finish): " option))
        (vars  ())
        old-var)
    (while (not (string= "" var))
      (add-to-list 'vars var)
      (setq var  (bmkp-read-variable "Variable: " option)))
    (nreverse vars)))

(defun bmkp-read-variable (prompt &optional option default-value)
  "Read name of a variable and return it as a symbol.
Prompt with string PROMPT.  
With non-nil OPTION, read the name of a user option.
The default value is DEFAULT-VALUE if non-nil, or the nearest symbol
to the cursor if it is a variable."
  (setq option  (if option 'user-variable-p 'boundp))
  (let ((symb                          (cond ((fboundp 'symbol-nearest-point) (symbol-nearest-point))
                                             ((fboundp 'symbol-at-point) (symbol-at-point))
                                             (t nil)))
        (enable-recursive-minibuffers  t))
    (when (and default-value (symbolp default-value))
      (setq default-value  (symbol-name default-value)))
    (intern (completing-read prompt obarray option t nil 'minibuffer-history
                             (or default-value (and (funcall option symb) (symbol-name symb)))
                             t))))

(defun bmkp-make-variable-list-record (variables &optional buffer-name)
  "Create and return a variable-list bookmark record.
VARIABLES is the list of variables to save.
Each entry in VARIABLES is either a variable (a symbol) or a cons
 whose car is a variable and whose cdr is the variable's value.

Optional arg BUFFER-NAME is the buffer to use for the bookmark.  This
is useful if some of the variables are buffer-local.  If BUFFER-NAME
is nil, the current buffer is used."
  (let ((record  `(,@(bookmark-make-record-default 'no-file 'no-context)
                   (filename     . ,bmkp-non-file-filename)
                   (variables    . ,(or (bmkp-printable-vars+vals variables)
                                        (error "No variables to bookmark")))
                   (handler      . bmkp-jump-variable-list))))
    (when buffer-name  (let ((bname  (assq 'buffer-name record)))  (setcdr bname buffer-name)))
    record))

(defun bmkp-printable-vars+vals (variables)
  "Return an alist of printable VARIABLES paired with their values.
Display a message for any variables that are not printable.
VARIABLES is the list of variables.  Each entry in VARIABLES is either
 a variable (a symbol) or a cons whose car is a variable and whose cdr
 is the variable's value."
  (let ((vars+vals     ())
        (unprintables  ()))
    (dolist (var  variables)
      (let ((val  (if (consp var) (cdr var) (symbol-value var))))
        (if (bmkp-printable-p val)
            (add-to-list 'vars+vals (if (consp var) var (cons var val)))
          (add-to-list 'unprintables var))))
    (when unprintables (message "Unsavable (unreadable) vars: %S" unprintables)  (sit-for 3))
    vars+vals))

;; Same as `savehist-printable', except added `print-circle' binding.
(defun bmkp-printable-p (value)
  "Return non-nil if VALUE would be Lisp-readable if printed using `prin1'."
  (or (stringp value) (numberp value) (symbolp value)
      (with-temp-buffer                 ; Print and try to read.
        (condition-case nil
            (let ((print-readably  t)
                  (print-level     nil)
                  (print-circle    t))
              (prin1 value (current-buffer))
              (read (point-min-marker))
              t)
          (error nil)))))

(defun bmkp-jump-variable-list (bookmark)
  "Jump to variable-list bookmark BOOKMARK, restoring the recorded values.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bmkp-make-variable-list-record'."
  (let ((buf        (bmkp-get-buffer-name bookmark))
        (vars+vals  (bookmark-prop-get bookmark 'variables)))
    (unless (get-buffer buf)
      (message "Bookmarked for non-existent buffer `%s', so using current buffer" buf) (sit-for 3)
      (setq buf (current-buffer)))
    (with-current-buffer buf
      (dolist (var+val  vars+vals)
        (set (car var+val)  (cdr var+val))))
    (message "Variables restored in buffer `%s': %S" buf (mapcar #'car vars+vals))
    (sit-for 3)))

;; URL browse support
(defun bmkp-make-url-browse-record (url) 
  "Create and return a url bookmark for `browse-url' to visit URL.
The handler is `bmkp-jump-url-browse'."
  (require 'browse-url)
  (let ((url-0  (copy-sequence url)))
    (set-text-properties 0 (length url) () url-0) 
    `((filename . ,bmkp-non-file-filename)
      (location . ,url-0)
      (handler  . bmkp-jump-url-browse))))

(defun bmkp-jump-url-browse (bookmark)
  "Handler function for record returned by `bmkp-make-url-browse-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (require 'browse-url)
  (let ((url  (bookmark-prop-get bookmark 'location)))
    (browse-url url)))

;; W3M support
(defun bmkp-make-w3m-record ()
  "Make a special entry for w3m buffers."
  (require 'w3m)                        ; For `w3m-current-url'.
  `(,w3m-current-title
    ,@(bookmark-make-record-default 'no-file)
    (filename . ,w3m-current-url)
    (handler . bmkp-jump-w3m)))

(add-hook 'w3m-mode-hook #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                                           'bmkp-make-w3m-record)))

(defun bmkp-w3m-set-new-buffer-name ()
  "Set the w3m buffer name according to the number of w3m buffers already open."
  (require 'w3m)                        ; For `w3m-list-buffers'.
  (let ((len  (length (w3m-list-buffers 'nosort))))
    (if (eq len 0)  "*w3m*"  (format "*w3m*<%d>" (1+ len)))))

(defun bmkp-jump-w3m-new-session (bookmark)
  "Jump to W3M bookmark BOOKMARK, setting a new tab."
  (require 'w3m)
  (let ((buf   (bmkp-w3m-set-new-buffer-name)))
    (w3m-browse-url (bookmark-prop-get bookmark 'filename) 'newsession)
    (while (not (get-buffer buf)) (sit-for 1)) ; Be sure we have the W3M buffer.
    (with-current-buffer buf
      (goto-char (point-min))
      ;; Wait until data arrives in buffer, before setting region.
      (while (eq (line-beginning-position) (line-end-position)) (sit-for 1)))
    (bookmark-default-handler
     `("" (buffer . ,buf) . ,(bookmark-get-bookmark-record bookmark)))))

(defun bmkp-jump-w3m-only-one-tab (bookmark)
  "Close all W3M sessions and jump to BOOKMARK in a new W3M buffer."
  (require 'w3m)
  (w3m-quit 'force)                     ; Be sure we start with an empty W3M buffer.
  (w3m-browse-url (bookmark-prop-get bookmark 'filename))
  (with-current-buffer "*w3m*" (while (eq (point-min) (point-max)) (sit-for 1)))
  (bookmark-default-handler
   `("" (buffer . ,(buffer-name (current-buffer))) . ,(bookmark-get-bookmark-record bookmark))))

(defalias 'bmkext-jump-w3m 'bmkp-jump-w3m)
(defun bmkp-jump-w3m (bookmark)
  "Handler function for record returned by `bmkp-make-w3m-record'.
BOOKMARK is a bookmark name or a bookmark record.
Use multi-tabs in W3M if `bmkp-w3m-allow-multi-tabs' is non-nil."
  (require 'w3m)
  (if bmkp-w3m-allow-multi-tabs
      (bmkp-jump-w3m-new-session bookmark)
    (bmkp-jump-w3m-only-one-tab bookmark)))


;; GNUS support for Emacs < 24.

(defun bmkp-make-gnus-record ()
  "Make a bookmark entry for a Gnus summary buffer."
  (require 'gnus)
  (unless (and (eq major-mode 'gnus-summary-mode) gnus-article-current)
    (error "Try again, from the Gnus summary buffer"))
  (let* ((grp   (car gnus-article-current))
         (art   (cdr gnus-article-current))
         (head  (gnus-summary-article-header art))
         (id    (mail-header-id head)))
    `((elt (gnus-summary-article-header) 1)
      ,@(bookmark-make-record-default 'no-file)
      (filename . ,bmkp-non-file-filename) (group . ,grp) (article . ,art) (message-id . ,id)
      (handler . bmkp-jump-gnus))))

(unless (> emacs-major-version 23)      ; Emacs 24 has `gnus-summary-bookmark-make-record'.
  (add-hook 'gnus-summary-mode-hook #'(lambda ()
                                        (set (make-local-variable 'bookmark-make-record-function)
                                             'bmkp-make-gnus-record))))

(unless (> emacs-major-version 23)      ; Emacs 24 has `gnus-summary-bookmark-make-record'.
  (add-hook 'gnus-article-mode-hook #'(lambda ()
                                        (set (make-local-variable 'bookmark-make-record-function)
                                             'bmkp-make-gnus-record))))

(defun bmkext-jump-gnus (bookmark)      ; Compatibility code.
  "`gnus-summary-bookmark-jump' if defined, else `bmkp-jump-gnus'."
  (if (fboundp 'gnus-summary-bookmark-jump)
      (gnus-summary-bookmark-jump bookmark) ; Emacs 24
    (bmkp-jump-gnus bookmark)))

(defun bmkp-jump-gnus (bookmark)
  "Handler function for record returned by `bmkp-make-gnus-record'.
BOOKMARK is a bookmark name or a bookmark record."
  (let ((group    (bookmark-prop-get bookmark 'group))
        (article  (bookmark-prop-get bookmark 'article))
        (id       (bookmark-prop-get bookmark 'message-id))
        (buf      (bookmark-prop-get bookmark 'buffer)))
    (if (< emacs-major-version 22) (gnus-fetch-group group) (gnus-fetch-group group (list article)))
    (gnus-summary-insert-cached-articles)
    (gnus-summary-goto-article id nil 'force)
    (bookmark-default-handler `("" (buffer . ,buf) . ,(bookmark-get-bookmark-record bookmark)))))


;; `man' and `woman' support for Emacs < 24.

(when (> emacs-major-version 20)
  (defun bmkp-make-woman-record ()
    "Create bookmark record for `man' page bookmark created by `woman'."
    `(,@(bookmark-make-record-default 'no-file)
      (filename . ,woman-last-file-name) (handler . bmkp-jump-woman)))

  (unless (> emacs-major-version 23)
    (add-hook 'woman-mode-hook #'(lambda ()
                                   (set (make-local-variable 'bookmark-make-record-function)
                                        'bmkp-make-woman-record)))))

(defun bmkp-make-man-record ()
  "Create bookmark record for `man' page bookmark created by `man'."
  `(,@(bookmark-make-record-default 'no-file)
    (filename . ,bmkp-non-file-filename)
    (man-args . ,Man-arguments) (handler . bmkp-jump-man)))

(unless (> emacs-major-version 23)
  (add-hook 'Man-mode-hook #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                                             'bmkp-make-man-record))))

(defun bmkext-jump-woman (bookmark)     ; Compatibility code.
  "`woman-bookmark-jump' if defined, else `bmkp-jump-woman'."
  (if (fboundp 'woman-bookmark-jump)
      (woman-bookmark-jump bookmark)    ; Emacs 24
    (bmkp-jump-woman bookmark)))
  
(defun bmkp-jump-woman (bookmark)
  "Handler function for `man' page bookmark created by `woman'."
  (unless (> emacs-major-version 20)
    (error "`woman' bookmarks are not supported in Emacs prior to Emacs 21"))
  (bookmark-default-handler
   `("" (buffer . ,(save-window-excursion (woman-find-file (bookmark-get-filename bookmark))
                                          (current-buffer)))
     . ,(bookmark-get-bookmark-record bookmark))))

(defun bmkext-jump-man (bookmark)       ; Compatibility code.
  "`Man-bookmark-jump' if defined, else `bmkp-jump-man'."
  (if (fboundp 'Man-bookmark-jump)
      (Man-bookmark-jump bookmark)      ; Emacs 24
    (bmkp-jump-man bookmark)))
  
(defun bmkp-jump-man (bookmark)
  "Handler function for `man' page bookmark created by `man'."
  (require 'man)
  (let ((Man-notify-method  (case bmkp-jump-display-function
                              ((nil display-buffer)                           'quiet)
                              (switch-to-buffer                               'pushy)
                              ((switch-to-buffer-other-window pop-to-buffer)  'friendly)
                              (t                                              'quiet))))
    (Man-getpage-in-background (bookmark-prop-get bookmark 'man-args))
    (while (get-process "man") (sit-for 0.2))
    (bookmark-default-handler (bookmark-get-bookmark bookmark))))

(defun bmkp-make-dired-record ()
  "Create and return a Dired bookmark record."
  (let ((hidden-dirs  (save-excursion (dired-remember-hidden))))
    (unwind-protect
         (let ((dir      (expand-file-name (if (consp dired-directory)
                                               (file-name-directory (car dired-directory))
                                             dired-directory)))
               (subdirs  (bmkp-dired-subdirs))
               (mfiles   (mapcar #'(lambda (mm) (car mm))
                                 (dired-remember-marks (point-min) (point-max)))))
           `(,dir
             ,@(bookmark-make-record-default 'no-file)
             (filename . ,dir) (dired-directory . ,dired-directory)
             (dired-marked . ,mfiles) (dired-switches . ,dired-actual-switches)
             (dired-subdirs . ,subdirs) (dired-hidden-dirs . ,hidden-dirs)
             (handler . bmkp-jump-dired)))
      (save-excursion			; Hide subdirs that were hidden.
        (dolist (dir  hidden-dirs)  (when (dired-goto-subdir dir) (dired-hide-subdir 1)))))))

;;;###autoload
(defun bmkp-dired-subdirs ()
  "Alist of inserted subdirectories, without their positions (markers).
This is like `dired-subdir-alist' but without the top-level dir and
without subdir positions (markers)."
  (interactive)
  (let ((subdir-alist      (cdr (reverse dired-subdir-alist))) ; Remove top.
        (subdirs-wo-posns  ()))
    (dolist (sub  subdir-alist)  (push (list (car sub)) subdirs-wo-posns))
    subdirs-wo-posns))

(add-hook 'dired-mode-hook #'(lambda () (set (make-local-variable 'bookmark-make-record-function)
                                             'bmkp-make-dired-record)))

(defun bmkp-jump-dired (bookmark)
  "Jump to Dired bookmark BOOKMARK.
BOOKMARK is a bookmark name or a bookmark record.
Handler function for record returned by `bmkp-make-dired-record'."
  (let ((dir          (bookmark-prop-get bookmark 'dired-directory))
        (mfiles       (bookmark-prop-get bookmark 'dired-marked))
        (switches     (bookmark-prop-get bookmark 'dired-switches))
        (subdirs      (bookmark-prop-get bookmark 'dired-subdirs))
        (hidden-dirs  (bookmark-prop-get bookmark 'dired-hidden-dirs)))
    (case bmkp-jump-display-function
      ((nil switch-to-buffer display-buffer)         (dired dir switches))
      ((pop-to-buffer switch-to-buffer-other-window) (dired-other-window dir switches))
      (t                                             (dired dir switches)))
    (let ((inhibit-read-only  t))
      (dired-insert-old-subdirs subdirs)
      (dired-mark-remembered (mapcar #'(lambda (mf) (cons (expand-file-name mf dir) 42)) mfiles))
      (save-excursion
        (dolist (dir  hidden-dirs) (when (dired-goto-subdir dir) (dired-hide-subdir 1)))))
    (goto-char (bookmark-get-position bookmark))))


(defun bmkp-read-bookmark-for-type (type alist &optional other-win pred hist action)
  "Read name of a bookmark of type TYPE.
TYPE is a string used only in the prompt: \"Jump to TYPE bookmark: \".
ALIST is the alist used for completion - nil means `bookmark-alist'.
Non-nil OTHER-WIN means append \" in another window\" to the prompt.
Non-nil PRED is a predicate used for completion.
Non-nil HIST is a history symbol.  Default is `bookmark-history'.
ACTION is the action to mention in the prompt.  `Jump to ', if nil."
  (unless alist (error "No bookmarks of type %s" type))
  (bookmark-completing-read
   (concat (or action "Jump to ") type "bookmark" (and other-win " in another window"))
   (bmkp-default-bookmark-name alist)
   alist pred hist))

;;;###autoload
(defun bmkp-jump-to-type (bookmark-name &optional use-region-p) ; `C-x j :'
  "Jump to a bookmark of a given type.  You are prompted for the type.
Otherwise, this is the same as `bookmark-jump' - see that, in
particular, for info about using a prefix argument."
  (interactive
   (let* ((completion-ignore-case  t)
          (type-cands              bmkp-types-alist)
          (type                    (completing-read "Type of bookmark: " type-cands nil t))
          (alist                   (funcall (intern (format "bmkp-%s-alist-only" type))))
          (history                 (assoc-default type type-cands))
          (bmk-name                (bmkp-read-bookmark-for-type (concat type " ") alist nil nil
                                                                history)))
     (list bmk-name  (or (equal type "Region") current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-jump-to-type-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j :'
  "`bmkp-jump-to-type', but in another window."
  (interactive
   (let* ((completion-ignore-case  t)
          (type-cands              bmkp-types-alist)
          (type                    (completing-read "Type of bookmark: " type-cands nil t))
          (alist                   (funcall (intern (format "bmkp-%s-alist-only" type))))
          (history                 (assoc-default type type-cands))
          (bmk-name                (bmkp-read-bookmark-for-type (concat type " ") alist t nil
                                                                history)))
     (list bmk-name (or (equal type "Region") current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-autonamed-jump (bookmark-name) ; `C-x j # #'
  "Jump to an autonamed bookmark.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-autonamed-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed " alist nil nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer nil))

;;;###autoload
(defun bmkp-autonamed-jump-other-window (bookmark-name) ; `C-x 4 j # #'
  "`bmkp-autonamed-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-autonamed-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed " alist t nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window nil))

;;;###autoload
(defun bmkp-autonamed-this-buffer-jump (bookmark-name) ; `C-x j # .'
  "Jump to an autonamed bookmark in the current buffer.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-autonamed-this-buffer-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed " alist nil nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer nil))

;;;###autoload
(defun bmkp-autonamed-this-buffer-jump-other-window (bookmark-name) ; `C-x 4 j # .'
  "`bmkp-autonamed-this-buffer-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-autonamed-this-buffer-alist-only)))
     (list (bmkp-read-bookmark-for-type "autonamed " alist t nil 'bmkp-autonamed-history))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window nil))

;;;###autoload
(defun bmkp-bookmark-list-jump (bookmark-name &optional use-region-p) ; `C-x j B'
  "Jump to a bookmark-list bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-bookmark-list-alist-only)))
     (list (bmkp-read-bookmark-for-type "bookmark-list " alist nil nil 'bmkp-bookmark-list-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-desktop-jump (bookmark-name &optional use-region-p) ; `C-x j K'
  "Jump to a desktop bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-desktop-alist-only)))
     (list (bmkp-read-bookmark-for-type "desktop " alist nil nil 'bmkp-desktop-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-dired-jump (bookmark-name &optional use-region-p) ; `C-x j d'
  "Jump to a Dired bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-dired-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired " alist nil nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-dired-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j d'
  "`bmkp-dired-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-dired-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired " alist t nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-dired-this-dir-jump (bookmark-name &optional use-region-p) ; `C-x j C-d'
  "Jump to a Dired bookmark for the `default-directory'.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-dired-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired-for-this-dir " alist nil nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-dired-this-dir-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j C-d'
  "`bmkp-dired-this-dir-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-dired-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "Dired-for-this-dir " alist t nil 'bmkp-dired-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-file-jump (bookmark-name &optional use-region-p) ; `C-x j f'
  "Jump to a file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "file " alist nil nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j f'
  "`bmkp-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "file " alist t nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-file-this-dir-jump (bookmark-name &optional use-region-p) ; `C-x j C-f'
  "Jump to a bookmark for a file or subdir in the `default-directory'.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-file-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "file-in-this-dir " alist nil nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-file-this-dir-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j C-f'
  "`bmkp-file-this-dir-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-file-this-dir-alist-only)))
     (list (bmkp-read-bookmark-for-type "file-in-this-dir " alist t nil 'bmkp-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-gnus-jump (bookmark-name &optional use-region-p) ; `C-x j g'
  "Jump to a Gnus bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-gnus-alist-only)))
     (list (bmkp-read-bookmark-for-type "Gnus " alist nil nil 'bmkp-gnus-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-gnus-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j g'
  "`bmkp-gnus-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-gnus-alist-only)))
     (list (bmkp-read-bookmark-for-type "Gnus " alist t nil 'bmkp-gnus-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-info-jump (bookmark-name &optional use-region-p) ; `C-x j i'
  "Jump to an Info bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-info-alist-only)))
     (list (bmkp-read-bookmark-for-type "Info " alist nil nil 'bmkp-info-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-info-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j i'
  "`bmkp-info-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-info-alist-only)))
     (list (bmkp-read-bookmark-for-type "Info " alist t nil 'bmkp-info-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-local-file-jump (bookmark-name &optional use-region-p) ; `C-x j l'
  "Jump to a local file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-local-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "local file " alist nil nil 'bmkp-local-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-local-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j l'
  "`bmkp-local-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-local-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "local file " alist t nil 'bmkp-local-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-man-jump (bookmark-name &optional use-region-p) ; `C-x j m'
  "Jump to a `man'-page bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-man-alist-only)))
     (list (bmkp-read-bookmark-for-type "`man' " alist nil nil 'bmkp-man-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-man-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j m'
  "`bmkp-man-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-man-alist-only)))
     (list (bmkp-read-bookmark-for-type "`man' " alist t nil 'bmkp-man-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-non-file-jump (bookmark-name &optional use-region-p) ; `C-x j b'
  "Jump to a non-file (buffer) bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-non-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "non-file (buffer) " alist nil nil 'bmkp-non-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-non-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j b'
  "`bmkp-non-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-non-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "non-file (buffer) " alist t nil 'bmkp-non-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-region-jump (bookmark-name) ; `C-x j r'
  "Jump to a region bookmark.
This is a specialization of `bookmark-jump', but without a prefix arg."
  (interactive (list (bmkp-read-bookmark-for-type "region " (bmkp-region-alist-only) nil nil
                                                  'bmkp-region-history)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer t))

;;;###autoload
(defun bmkp-region-jump-other-window (bookmark-name) ; `C-x 4 j r'
  "`bmkp-region-jump', but in another window."
  (interactive (list (bmkp-read-bookmark-for-type "region " (bmkp-region-alist-only) t nil
                                                  'bmkp-region-history)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window t))

;;;###autoload
(defun bmkp-remote-file-jump (bookmark-name &optional use-region-p) ; `C-x j n'
  "Jump to a remote file or directory bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-remote-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "remote file " alist nil nil 'bmkp-remote-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-remote-file-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j n'
  "`bmkp-remote-file-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-remote-file-alist-only)))
     (list (bmkp-read-bookmark-for-type "remote file " alist t nil 'bmkp-remote-file-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-specific-buffers-jump (buffers bookmark-name &optional use-region-p) ; `C-x j = b'
  "Jump to a bookmark for a buffer in list BUFFERS.
Interactively, read buffer names and bookmark name, with completion.

This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((buffs  ())
         buff)
     (while (and (setq buff  (bmkp-completing-read-buffer-name 'ALLOW-EMPTY)) (not (string= "" buff)))
       (add-to-list 'buffs buff))
     (let ((alist  (bmkp-specific-buffers-alist-only buffs)))
       (list buffs (bmkp-read-bookmark-for-type "specific-buffers " alist) current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-specific-buffers-jump-other-window (buffers bookmark-name
                                                &optional use-region-p) ; `C-x 4 j = b'
  "`bmkp-specific-buffers-jump', but in another window."
  (interactive
   (let ((buffs  ())
         buff)
     (while (and (setq buff  (bmkp-completing-read-buffer-name 'ALLOW-EMPTY)) (not (string= "" buff)))
       (add-to-list 'buffs buff))
     (let ((alist  (bmkp-specific-buffers-alist-only buffs)))
       (list buffs (bmkp-read-bookmark-for-type "specific-buffers " alist) current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-specific-files-jump (files bookmark-name &optional use-region-p) ; `C-x j = f'
  "Jump to a bookmark for a file in list FILES.
Interactively, read file names and bookmark name, with completion.

This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((use-file-dialog  nil)
         (files            ())
         file)
     (while (and (setq file  (bmkp-completing-read-file-name 'ALLOW-EMPTY)) (not (string= "" file)))
       (add-to-list 'files file))
     (let ((alist  (bmkp-specific-files-alist-only files)))
       (list files (bmkp-read-bookmark-for-type "specific-files " alist) current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-specific-files-jump-other-window (files bookmark-name
                                              &optional use-region-p) ; `C-x 4 j = f'
  "`bmkp-specific-files-jump', but in another window."
  (interactive
   (let ((use-file-dialog  nil)
         (files            ())
         file)
     (while (and (setq file  (bmkp-completing-read-file-name 'ALLOW-EMPTY)) (not (string= "" file)))
       (add-to-list 'files file))
     (let ((alist  (bmkp-specific-files-alist-only files)))
       (list files (bmkp-read-bookmark-for-type "specific-files " alist) current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-this-buffer-jump (bookmark-name &optional use-region-p) ; `C-x j .'
  "Jump to a bookmark for the current buffer.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-this-buffer-alist-only)))
     (unless alist  (error "No bookmarks for this buffer"))
     (list (bookmark-completing-read "Jump to bookmark for this buffer"
                                     (bmkp-default-bookmark-name alist) alist)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-this-buffer-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j .'
  "`bmkp-this-buffer-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-this-buffer-alist-only)))
     (unless alist  (error "No bookmarks for this buffer"))
     (list (bookmark-completing-read "Jump to bookmark for this buffer in another window"
                                     (bmkp-default-bookmark-name alist) alist)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;; ;;;###autoload
;;; (defun bmkp-this-file-jump (bookmark-name &optional use-region-p)
;;;   "Jump to a bookmark for the current file (absolute file name).
;;; This is a specialization of `bookmark-jump' - see that, in particular
;;; for info about using a prefix argument."
;;;   (interactive
;;;    (progn (unless (or (buffer-file-name) (and (eq major-mode 'dired-mode)
;;;                                               (if (consp dired-directory)
;;;                                                   (car dired-directory)
;;;                                                 dired-directory)))
;;;             (error "This buffer is not associated with a file"))
;;;           (let ((alist  (bmkp-this-file-alist-only)))
;;;             (unless alist  (error "No bookmarks for this file"))
;;;             (list (bookmark-completing-read "Jump to bookmark for this file"
;;;                                             (bmkp-default-bookmark-name alist) alist)
;;;                   current-prefix-arg))))
;;;   (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;; ;;;###autoload
;;; (defun bmkp-this-file-jump-other-window (bookmark-name &optional use-region-p)
;;;   "`bmkp-this-file-jump', but in another window."
;;;   (interactive
;;;    (progn (unless (or (buffer-file-name) (and (eq major-mode 'dired-mode)
;;;                                               (if (consp dired-directory)
;;;                                                   (car dired-directory)
;;;                                                 dired-directory)))
;;;             (error "This buffer is not associated with a file"))
;;;           (let ((alist  (bmkp-this-file-alist-only)))
;;;             (unless alist  (error "No bookmarks for this file"))
;;;             (list (bookmark-completing-read "Jump to bookmark for this file in another window"
;;;                                             (bmkp-default-bookmark-name alist) alist)
;;;                   current-prefix-arg))))
;;;   (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-variable-list-jump (bookmark-name) ; `C-x j v'
  "Jump to a variable-list bookmark.
This is a specialization of `bookmark-jump'."
  (interactive
   (let ((alist  (bmkp-variable-list-alist-only)))
     (list (bmkp-read-bookmark-for-type "variable-list " alist nil nil 'bmkp-variable-list-history))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer nil))

;;;###autoload
(defun bmkp-url-jump (bookmark-name &optional use-region-p) ; `C-x j u'
  "Jump to a URL bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (if (fboundp 'w3m-list-buffers)
                     (bmkp-url-alist-only)
                   (bmkp-url-browse-alist-only))))
     (list (bmkp-read-bookmark-for-type "URL " alist nil nil 'bmkp-url-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-url-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j u'
  "`bmkp-url-jump', but in another window."
  (interactive
   (let ((alist  (if (fboundp 'w3m-list-buffers)
                     (bmkp-url-alist-only)
                   (bmkp-url-browse-alist-only))))
     (list (bmkp-read-bookmark-for-type "URL " alist t nil 'bmkp-url-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-w3m-jump (bookmark-name &optional use-region-p) ; `C-x j w'
  "Jump to a W3M bookmark.
This is a specialization of `bookmark-jump' - see that, in particular
for info about using a prefix argument."
  (interactive
   (let ((alist  (bmkp-w3m-alist-only)))
     (list (bmkp-read-bookmark-for-type "W3M " alist nil nil 'bmkp-w3m-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-w3m-jump-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j w'
  "`bmkp-w3m-jump', but in another window."
  (interactive
   (let ((alist  (bmkp-w3m-alist-only)))
     (list (bmkp-read-bookmark-for-type "W3M " alist t nil 'bmkp-w3m-history)
           current-prefix-arg)))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-all-tags-jump (tags bookmark) ; `C-x j t *'
  "Jump to a BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-all-tags-alist-only tgs)))
     (unless alist (error "No bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t *'
  "`bmkp-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-all-tags-alist-only tgs)))
     (unless alist (error "No bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-all-tags-regexp-jump (regexp bookmark) ; `C-x j t % *'
  "Jump to a BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t % *'
  "`bmkp-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-some-tags-jump (tags bookmark) ; `C-x j t +'
  "Jump to a BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t +'
  "`bmkp-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-some-tags-regexp-jump (regexp bookmark) ; `C-x j t % +'
  "Jump to a BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t % +'
  "`bmkp-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "Bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-all-tags-jump (tags bookmark) ; `C-x j t f *'
  "Jump to a file or directory BOOKMARK that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t f *'
  "`bmkp-file-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-all-tags-regexp-jump (regexp bookmark) ; `C-x j t f % *'
  "Jump to a file or directory BOOKMARK that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t f % *'
  "`bmkp-file-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-some-tags-jump (tags bookmark) ; `C-x j t f +'
  "Jump to a file or directory BOOKMARK that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t f +'
  "`bmkp-file-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-some-tags-regexp-jump (regexp bookmark) ; `C-x j t f % +'
  "Jump to a file or directory BOOKMARK that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t f % +'
  "`bmkp-file-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-this-dir-all-tags-jump (tags bookmark) ; `C-x j t C-f *'
  "Jump to a file BOOKMARK in this dir that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag.
If you specify no tags, then every bookmark that has some tags is a
candidate."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-this-dir-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-this-dir-all-tags-jump-other-window (tags bookmark) ; `C-x 4 j t C-f *'
  "`bmkp-file-this-dir-all-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-this-dir-all-tags-alist-only tgs)))
     (unless alist (error "No file or dir bookmarks have all of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-this-dir-all-tags-regexp-jump (regexp bookmark) ; `C-x j t C-f % *'
  "Jump to a file BOOKMARK in this dir that has each tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-this-dir-all-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t C-f % *'
  "`bmkp-file-this-dir-all-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-all-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-this-dir-some-tags-jump (tags bookmark) ; `C-x j t C-f +'
  "Jump to a file BOOKMARK in this dir that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion to enter the bookmark name and each tag."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-this-dir-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-this-dir-some-tags-jump-other-window (tags bookmark) ; `C-x 4 j t C-f +'
  "`bmkp-file-this-dir-some-tags-jump', but in another window."
  (interactive
   (let* ((tgs    (bmkp-read-tags-completing))
          (alist  (bmkp-file-this-dir-some-tags-alist-only tgs)))
     (unless tgs (error "You did not specify any tags"))
     (unless alist (error "No file or dir bookmarks have any of the specified tags"))
     (list tgs (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

;;;###autoload
(defun bmkp-file-this-dir-some-tags-regexp-jump (regexp bookmark) ; `C-x j t C-f % +'
  "Jump to a file BOOKMARK in this dir that has a tag matching REGEXP.
You are prompted for the REGEXP.
Then you are prompted for the BOOKMARK (with completion)."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump bookmark))

;;;###autoload
(defun bmkp-file-this-dir-some-tags-regexp-jump-other-window (regexp bookmark) ; `C-x 4 j t C-f % +'
  "`bmkp-file-this-dir-some-tags-regexp-jump', but in another window."
  (interactive
   (let* ((rgx    (read-string "Regexp for tags: "))
          (alist  (bmkp-file-this-dir-some-tags-regexp-alist-only rgx)))
     (unless alist (error "No file or dir bookmarks have tags that match `%s'" rgx))
     (list rgx (bookmark-completing-read "File bookmark" (bmkp-default-bookmark-name alist) alist))))
  (bookmark-jump-other-window bookmark))

(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defalias 'bmkp-autofile-jump 'bmkp-find-file)
  (defun bmkp-find-file ()              ; `C-x j a'
    "Visit a file or directory that has an autofile bookmark."
    (interactive)
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff) (bmkp-get-autofile-bookmark ff))))
      (find-file (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defalias 'bmkp-autofile-jump-other-window 'bmkp-find-file)
  (defun bmkp-find-file-other-window () ; `C-x 4 j a'
    "`bmkp-find-file', but in another window."
    (interactive)
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff) (bmkp-get-autofile-bookmark ff))))
      (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags (tags) ; `C-x j t a *'
    "Visit a file or directory that has all of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion.
If you specify no tags, then every file that has some tags is a
candidate."
    (interactive (list (bmkp-read-tags-completing)))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-every #'(lambda (tag) (bmkp-has-tag-p bmk tag))
                                                         tags))))))
      (find-file (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21) ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags-other-window (tags) ; `C-x 4 j t a *'
    "`bmkp-find-file-all-tags', but in another window."
    (interactive (list (bmkp-read-tags-completing)))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-every #'(lambda (tag) (bmkp-has-tag-p bmk tag))
                                                         tags))))))
      (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

(when (> emacs-major-version 21) ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags-regexp (regexp) ; `C-x j t a % *'
    "Visit a file or directory that has each tag matching REGEXP.
You are prompted for the REGEXP."
    (interactive (list (read-string "Regexp for tags: ")))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-every
                                              #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                              btgs))))))
      (find-file (read-file-name "Find file: " nil nil t nil pred)))))

;;;###autoload
(when (> emacs-major-version 21) ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-all-tags-regexp-other-window (regexp) ; `C-x 4 j t a % *'
    "`bmkp-find-file-all-tags-regexp', but in another window."
    (interactive (list (read-string "Regexp for tags: ")))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-every
                                              #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                              btgs))))))
      (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

;;;###autoload
(when (> emacs-major-version 21) ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags (tags) ; `C-x j t a +'
    "Visit a file or directory that has at least one of the TAGS.
Hit `RET' to enter each tag, then hit `RET' again after the last tag.
You can use completion."
    (interactive (list (bmkp-read-tags-completing)))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags))))))
      (find-file (read-file-name "Find file: " nil nil t nil pred)))))

;;;###autoload
(when (> emacs-major-version 21) ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags-other-window (tags) ; `C-x 4 j t a +'
    "`bmkp-find-file-some-tags', but in another window."
    (interactive (list (bmkp-read-tags-completing)))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-some #'(lambda (tag) (bmkp-has-tag-p bmk tag)) tags))))))
      (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

;;;###autoload
(when (> emacs-major-version 21) ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags-regexp (regexp)  ; `C-x j t a % +'
    "Visit a file or directory that has a tag matching REGEXP.
You are prompted for the REGEXP."
    (interactive (list (read-string "Regexp for tags: ")))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-some
                                              #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                              btgs))))))
      (find-file (read-file-name "Find file: " nil nil t nil pred)))))

;;;###autoload
(when (> emacs-major-version 21)        ; Needs `read-file-name' with a PREDICATE arg.
  (defun bmkp-find-file-some-tags-regexp-other-window (regexp) ; `C-x 4 j t a % +'
    "`bmkp-find-file-some-tags-regexp', but in another window."
    (interactive (list (read-string "Regexp for tags: ")))
    (let ((use-file-dialog  nil)
          (pred             #'(lambda (ff)
                                (let* ((bmk   (bmkp-get-autofile-bookmark ff))
                                       (btgs  (and bmk (bmkp-get-tags bmk))))
                                  (and btgs  (bmkp-some
                                              #'(lambda (tag) (string-match regexp (bmkp-tag-name tag)))
                                              btgs))))))
      (find-file-other-window (read-file-name "Find file: " nil nil t nil pred)))))

;;;###autoload
(defun bmkp-jump-in-navlist (bookmark-name &optional use-region-p) ; `C-x j N'
  "Jump to a bookmark, choosing from those in the navigation list."
  (interactive
   (progn (unless bmkp-nav-alist
            (bookmark-maybe-load-default-file)
            (setq bmkp-nav-alist  bookmark-alist)
            (unless bmkp-nav-alist (error "No bookmarks"))
            (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
            (message "Bookmark navigation list is now the global bookmark list") (sit-for 2))
          (let ((bookmark-alist  bmkp-nav-alist))
            (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                            (bmkp-default-bookmark-name))
                  current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'switch-to-buffer use-region-p))

;;;###autoload
(defun bmkp-jump-in-navlist-other-window (bookmark-name &optional use-region-p) ; `C-x 4 j N'
  "Same as `bmkp-jump-in-navlist', but use another window."
  (interactive
   (progn (unless bmkp-nav-alist
            (bookmark-maybe-load-default-file)
            (setq bmkp-nav-alist  bookmark-alist)
            (unless bmkp-nav-alist (error "No bookmarks"))
            (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
            (message "Bookmark navigation list is now the global bookmark list") (sit-for 2))
          (let ((bookmark-alist  bmkp-nav-alist))
            (list (bookmark-completing-read "Jump to bookmark (in another window)"
                                            (bmkp-default-bookmark-name))
                  current-prefix-arg))))
  (bmkp-jump-1 bookmark-name 'bmkp-select-buffer-other-window use-region-p))

;;;###autoload
(defun bmkp-cycle (increment &optional other-window startoverp)
  "Cycle through bookmarks in the navlist by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value

Plain `C-u' also means start over at first bookmark.

You can set the navigation list using commands
 `bmkp-choose-navlist-from-bookmark-list' and
 `bmkp-choose-navlist-of-type'.

You can cycle among bookmarks in the current buffer using
 `bmkp-cycle-this-buffer' and
 `bmkp-cycle-this-buffer-other-window.'

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (unless bmkp-nav-alist
    (bookmark-maybe-load-default-file)
    (setq bmkp-nav-alist  bookmark-alist)
    (unless bmkp-nav-alist (error "No bookmarks"))
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist))
    (message "Bookmark navigation list is now the global bookmark list") (sit-for 2))
  (unless (and bmkp-current-nav-bookmark (not startoverp)
               (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR))
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (if (bmkp-cycle-1 increment other-window startoverp)
      (unless (or (bmkp-sequence-bookmark-p bmkp-current-nav-bookmark)
                  (bmkp-function-bookmark-p bmkp-current-nav-bookmark))
        (message "Position: %9d, Bookmark: `%s'"
                 (point) (bookmark-name-from-full-record bmkp-current-nav-bookmark)))
    (message "Invalid bookmark: `%s'" (bookmark-name-from-full-record bmkp-current-nav-bookmark))))

;;;###autoload
(defun bmkp-cycle-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle' but uses another window."
  (interactive "p")
  (bmkp-cycle increment 'OTHER-WINDOW startoverp))

;;;###autoload
(defun bmkp-cycle-this-buffer (increment &optional other-window startoverp)
  "Cycle through bookmarks in this buffer by INCREMENT (default: 1).
Positive INCREMENT cycles forward.  Negative INCREMENT cycles backward.
Interactively, the prefix arg determines INCREMENT:
 Plain `C-u': 1
 otherwise: the numeric prefix arg value 

Plain `C-u' also means start over at first bookmark.

You can cycle among bookmarks beyond the current buffer using
`bmkp-cycle' and `bmkp-cycle-other-window.'

You can set your preferred sort order for this-buffer bookmarks by
customizing option `bmkp-this-buffer-cycle-sort-comparer'.

To change the sort order without customizing, you can use \
`\\[bmkp-this-buffer-bmenu-list]' to
show the `*Bookmark List*' with only this buffer's bookmarks, sort
them there, and use `\\[bmkp-choose-navlist-from-bookmark-list]', choosing \
`CURRENT *Bookmark List*' as
the navigation list.

Then you can cycle the bookmarks using `bmkp-cycle'
\(`\\[bmkp-next-bookmark-repeat]' etc.), instead of `bmkp-cycle-this-buffer'.

In Lisp code:
 Non-nil OTHER-WINDOW means jump to the bookmark in another window.
 Non-nil STARTOVERP means reset `bmkp-current-nav-bookmark' to the
 first bookmark in the navlist."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) nil startovr)))
  (bookmark-maybe-load-default-file)
  (let ((bmkp-sort-comparer  bmkp-this-buffer-cycle-sort-comparer))
    (setq bmkp-nav-alist  (bmkp-sort-omit (bmkp-this-buffer-alist-only))))
  (unless bmkp-nav-alist (error "No bookmarks in this buffer"))
  (unless (and bmkp-current-nav-bookmark (not startoverp)
               (bookmark-get-bookmark bmkp-current-nav-bookmark 'NOERROR)
               (bmkp-this-buffer-p bmkp-current-nav-bookmark)) ; Exclude desktops etc.
    (setq bmkp-current-nav-bookmark  (car bmkp-nav-alist)))
  (if (bmkp-cycle-1 increment other-window startoverp)
      (unless (or (bmkp-sequence-bookmark-p bmkp-current-nav-bookmark)
                  (bmkp-function-bookmark-p bmkp-current-nav-bookmark))
        (message "Position: %9d, Bookmark: `%s'"
                 (point) (bookmark-name-from-full-record bmkp-current-nav-bookmark)))
    (message "Invalid bookmark: `%s'" (bookmark-name-from-full-record bmkp-current-nav-bookmark))))

;;;###autoload
(defun bmkp-cycle-this-buffer-other-window (increment &optional startoverp)
  "Same as `bmkp-cycle-this-buffer' but use other window."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-buffer increment 'OTHER-WINDOW startoverp))

(defun bmkp-cycle-1 (increment &optional other-window startoverp)
  "Helper for `bmkp-cycle' and `bmkp-cycle-this-buffer'.
Do nothing if `bmkp-current-nav-bookmark' is an invalid bookmark.
Return `bmkp-current-nav-bookmark', or nil if invalid.

NOTE: If `pop-up-frames' is non-nil, then cycling inhibits automatic
showing of annotations (`bookmark-automatically-show-annotations').
This is to prevent change of frame focus, so cycling can continue
properly.

See `bmkp-cycle' for descriptions of the arguments."
  (let ((bookmark-alist   bmkp-nav-alist)
        (bookmark         (bookmark-get-bookmark bmkp-current-nav-bookmark 'no-error))
        (bmkp-use-region  (eq 'cycling-too bmkp-use-region)))
    (unless bookmark-alist (error "No bookmarks for cycling"))
    (when bookmark                      ; Skip bookmarks with bad names.
      (setq bmkp-current-nav-bookmark
            (if startoverp
                (car bookmark-alist)
              (let ((index  (bmkp-list-position bookmark bookmark-alist #'eq)))
                (if index
                    (nth (mod (+ increment index) (length bookmark-alist)) bookmark-alist)
                  (message "bmkp-cycle-1: Bookmark `%s' is not in navlist"
                           (bookmark-name-from-full-record bmkp-current-nav-bookmark))
                  (car bookmark-alist)))))
      (let ((bookmark-automatically-show-annotations ; Prevent possible frame focus change.
             (and bookmark-automatically-show-annotations (not pop-up-frames))))
        (if other-window
            (bookmark-jump-other-window (bookmark-name-from-full-record bmkp-current-nav-bookmark))
          (save-selected-window (bookmark-name-from-full-record
                                 (bookmark-jump bmkp-current-nav-bookmark))))))
    (and bookmark bmkp-current-nav-bookmark))) ; Return nil if not a valid bookmark.

(defun bmkp-list-position (item items &optional test)
  "Find the first occurrence of ITEM in list ITEMS.
Return the index of the matching item, or nil if not found.
Items are compared using binary predicate TEST, or `equal' if TEST is
nil."
  (unless test (setq test  'equal))
  (let ((pos  0))
    (catch 'bmkp-list-position
      (dolist (itm  items)
        (when (funcall test item itm) (throw 'bmkp-list-position pos))
        (setq pos  (1+ pos)))
      nil)))

;;;###autoload
(defun bmkp-next-bookmark (n &optional startoverp) ; You can bind this to a repeatable key
  "Jump to the Nth next bookmark in the bookmark navigation list.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at first bookmark.
See also `bmkp-cycle'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle n nil startoverp))

;;;###autoload
(defun bmkp-previous-bookmark (n &optional startoverp) ; You can bind this to a repeatable key
  "Jump to the Nth previous bookmark in the bookmark navigation list.
See `bmkp-next-bookmark'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle (- n) nil startoverp))

;;;###autoload
(defun bmkp-next-bookmark-repeat (arg)  ; `C-x p right', `C-x p f', `C-x p C-f'
  "Jump to the Nth-next bookmark in the bookmark navigation list.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first bookmark (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark))

;;;###autoload
(defun bmkp-previous-bookmark-repeat (arg) ; `C-x p left', `C-x p b', `C-x p C-b'
  "Jump to the Nth-previous bookmark in the bookmark navigation list.
See `bmkp-next-bookmark-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark))

;;;###autoload
(defun bmkp-next-bookmark-this-buffer (n &optional startoverp) ; Bind to repeatable key, e.g. `S-f2'
  "Jump to the Nth-next bookmark in the current buffer.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-buffer n nil startoverp))

;;;###autoload
(defun bmkp-previous-bookmark-this-buffer (n &optional startoverp) ; Bind to repeatable key, e.g. `f2'
  "Jump to the Nth-previous bookmark in the current buffer.
See `bmkp-next-bookmark-this-buffer'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (bmkp-cycle-this-buffer (- n) nil startoverp))

;;;###autoload
(defun bmkp-next-bookmark-this-buffer-repeat (arg) ; `C-x p down', `C-x p n', `C-x p C-n'
  "Jump to the Nth next bookmark in the current buffer.
This is a repeatable version of `bmkp-next-bookmark-this-buffer'.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-next-bookmark-this-buffer))

;;;###autoload
(defun bmkp-previous-bookmark-this-buffer-repeat (arg) ; `C-x p up', `C-x p p', `C-x p C-p'
  "Jump to the Nth previous bookmark in the current buffer.
See `bmkp-next-bookmark-this-buffer-repeat'."
  (interactive "P")
  (require 'repeat)
  (bmkp-repeat-command 'bmkp-previous-bookmark-this-buffer))

;;;###autoload
(defun bmkp-next-bookmark-w32 (n &optional startoverp)       ; You can bind this to a repeatable key
  "Windows `Open' the Nth next bookmark in the bookmark navigation list.
MS Windows only.  Invokes the program associated with the file type.
N defaults to 1, meaning the next one.
Plain `C-u' means start over at the first one.
See also `bmkp-cycle'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-cycle n nil startoverp)))

;;;###autoload
(defun bmkp-previous-bookmark-w32 (n &optional startoverp)   ; You can bind this to a repeatable key
  "Windows `Open' the Nth previous bookmark in the bookmark navlist.
See `bmkp-next-bookmark-w32'."
  (interactive (let ((startovr  (consp current-prefix-arg)))
                 (list (if startovr 1 (prefix-numeric-value current-prefix-arg)) startovr)))
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-cycle (- n) nil startoverp)))

;;;###autoload
(defun bmkp-next-bookmark-w32-repeat (arg) ; `C-x p next'
  "Windows `Open' the Nth next bookmark in the bookmark navigation list.
This is a repeatable version of `bmkp-next-bookmark'.
N defaults to 1, meaning the next bookmark.
Plain `C-u' means start over at the first one (and no repeat)."
  (interactive "P")
  (require 'repeat)
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-repeat-command 'bmkp-next-bookmark)))

;;;###autoload
(defun bmkp-previous-bookmark-w32-repeat (arg) ; `C-x p prior'
  "Windows `Open' the Nth previous bookmark in the bookmark navlist.
See `bmkp-next-bookmark-w32-repeat'."
  (interactive "P")
  (require 'repeat)
  (let ((bmkp-use-w32-browser-p  t))  (bmkp-repeat-command 'bmkp-previous-bookmark)))

;; In spite of their names, `bmkp-cycle-specific-(buffers|files)*' just cycle bookmarks in the
;; current buffer or file.  There is no way to choose multiple buffers or files.
;;
;; `bmkp-cycle-autonamed', `bmkp-cycle-autonamed-other-window',
;; `bmkp-cycle-bookmark-list', `bmkp-cycle-bookmark-list-other-window',
;; `bmkp-cycle-desktop',
;; `bmkp-cycle-dired', `bmkp-cycle-dired-other-window',
;; `bmkp-cycle-file', `bmkp-cycle-file-other-window',
;; `bmkp-cycle-gnus', `bmkp-cycle-gnus-other-window',
;; `bmkp-cycle-info', `bmkp-cycle-info-other-window',
;; `bmkp-cycle-lighted', `bmkp-cycle-lighted-other-window',
;; `bmkp-cycle-local-file', `bmkp-cycle-local-file-other-window',
;; `bmkp-cycle-man', `bmkp-cycle-man-other-window',
;; `bmkp-cycle-non-file', `bmkp-cycle-non-file-other-window',
;; `bmkp-cycle-remote-file', `bmkp-cycle-remote-file-other-window',
;; `bmkp-cycle-specific-buffers', `bmkp-cycle-specific-buffers-other-window',
;; `bmkp-cycle-specific-files', `bmkp-cycle-specific-files-other-window',
;; `bmkp-cycle-variable-list',
;; `bmkp-cycle-url', `bmkp-cycle-url-other-window',
;; `bmkp-next-autonamed-bookmark', `bmkp-next-autonamed-bookmark-repeat',
;; `bmkp-next-bookmark-list-bookmark', `bmkp-next-bookmark-list-bookmark-repeat',
;; `bmkp-next-desktop-bookmark', `bmkp-next-desktop-bookmark-repeat',
;; `bmkp-next-dired-bookmark', `bmkp-next-dired-bookmark-repeat',
;; `bmkp-next-file-bookmark', `bmkp-next-file-bookmark-repeat',
;; `bmkp-next-gnus-bookmark', `bmkp-next-gnus-bookmark-repeat',
;; `bmkp-next-info-bookmark', `bmkp-next-info-bookmark-repeat',
;; `bmkp-next-lighted-bookmark', `bmkp-next-lighted-bookmark-repeat',
;; `bmkp-next-local-file-bookmark', `bmkp-next-local-file-bookmark-repeat',
;; `bmkp-next-man-bookmark', `bmkp-next-man-bookmark-repeat',
;; `bmkp-next-non-file-bookmark', `bmkp-next-non-file-bookmark-repeat',
;; `bmkp-next-remote-file-bookmark', `bmkp-next-remote-file-bookmark-repeat',
;; `bmkp-next-specific-buffers-bookmark', `bmkp-next-specific-buffers-bookmark-repeat',
;; `bmkp-next-specific-files-bookmark', `bmkp-next-specific-files-bookmark-repeat',
;; `bmkp-next-variable-list-bookmark', `bmkp-next-variable-list-bookmark-repeat',
;; `bmkp-next-url-bookmark', `bmkp-next-url-bookmark-repeat'.
;;
(bmkp-define-cycle-command "autonamed")
(bmkp-define-cycle-command "autonamed" 'OTHER-WINDOW)
(bmkp-define-cycle-command "bookmark-list") ; No other-window version needed
(bmkp-define-cycle-command "desktop")   ; No other-window version needed
(bmkp-define-cycle-command "dired")
(bmkp-define-cycle-command "dired" 'OTHER-WINDOW)
(bmkp-define-cycle-command "file")
(bmkp-define-cycle-command "file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "gnus")
(bmkp-define-cycle-command "gnus" 'OTHER-WINDOW)
(bmkp-define-cycle-command "info")
(bmkp-define-cycle-command "info" 'OTHER-WINDOW)
(when (featurep 'bookmark+-lit)
  (bmkp-define-cycle-command "lighted")
  (bmkp-define-cycle-command "lighted" 'OTHER-WINDOW))
(bmkp-define-cycle-command "local-file")
(bmkp-define-cycle-command "local-file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "man")
(bmkp-define-cycle-command "man" 'OTHER-WINDOW)
(bmkp-define-cycle-command "non-file")
(bmkp-define-cycle-command "non-file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "remote-file")
(bmkp-define-cycle-command "remote-file" 'OTHER-WINDOW)
(bmkp-define-cycle-command "specific-buffers")
(bmkp-define-cycle-command "specific-buffers" 'OTHER-WINDOW)
(bmkp-define-cycle-command "specific-files")
(bmkp-define-cycle-command "specific-files" 'OTHER-WINDOW)
(bmkp-define-cycle-command "variable-list") ; No other-window version needed
(bmkp-define-cycle-command "url")
(bmkp-define-cycle-command "url" 'OTHER-WINDOW)

(bmkp-define-next+prev-cycle-commands "autonamed")
(bmkp-define-next+prev-cycle-commands "bookmark-list")
(bmkp-define-next+prev-cycle-commands "desktop")
(bmkp-define-next+prev-cycle-commands "dired")
(bmkp-define-next+prev-cycle-commands "file")
(bmkp-define-next+prev-cycle-commands "gnus")
(bmkp-define-next+prev-cycle-commands "info")
(bmkp-define-next+prev-cycle-commands "lighted")
(bmkp-define-next+prev-cycle-commands "local-file")
(bmkp-define-next+prev-cycle-commands "man")
(bmkp-define-next+prev-cycle-commands "non-file")
(bmkp-define-next+prev-cycle-commands "remote-file")
(bmkp-define-next+prev-cycle-commands "specific-buffers")
(bmkp-define-next+prev-cycle-commands "specific-files")
(bmkp-define-next+prev-cycle-commands "variable-list")
(bmkp-define-next+prev-cycle-commands "url")

;;;###autoload
(defun bmkp-toggle-autonamed-bookmark-set/delete (position &optional allp) ; Bound to `C-x p RET'
  "If there is an autonamed bookmark at point, delete it, else create one.
The bookmark created has no region.  Its name is formatted according
to option `bmkp-autoname-bookmark-function'.

With a prefix arg, delete *ALL* autonamed bookmarks for this buffer.

Non-interactively, act at POSITION, not point."
  (interactive "d\nP")
  (if allp
      (bmkp-delete-all-autonamed-for-this-buffer)
    (let ((bmk-name  (funcall bmkp-autoname-bookmark-function position)))
      (if (not (bookmark-get-bookmark bmk-name 'noerror))
          (let ((mark-active  nil))     ; Do not set a region bookmark.
            (bookmark-set bmk-name)
            (message "Set bookmark `%s'" bmk-name))
        (bookmark-delete bmk-name)
        (message "Deleted bookmark `%s'" bmk-name)))))

;;;###autoload
(defun bmkp-set-autonamed-bookmark (position &optional msgp)
  "Set an autonamed bookmark at point.
The bookmark created has no region.  Its name is formatted according
to option `bmkp-autoname-bookmark-function'.
Non-interactively, act at POSITION, not point."
  (interactive (list (point) t))
  (let ((bmk-name     (funcall bmkp-autoname-bookmark-function position))
        (mark-active  nil))             ; Do not set a region bookmark.
    (bookmark-set bmk-name)
    (when msgp (message "Set bookmark `%s'" bmk-name))))

;;;###autoload
(defun bmkp-set-autonamed-bookmark-at-line (number)
  "Set an autonamed bookmark at the beginning of the given line NUMBER."
  (interactive "nSet bookmark on line: ")
  (save-excursion
    (goto-char (point-min))
    (unless (zerop (forward-line (1- number)))
      (error "No such line: %d (%d lines total)" number (1+ (count-lines (point-min) (point-max)))))
    (bmkp-set-autonamed-bookmark (point))))

(when (> emacs-major-version 21)
  (defun bmkp-occur-create-autonamed-bookmarks ( &optional msgp)
    "Create an autonamed bookmark for each `occur' hit.
You can use this only in `Occur' mode (commands such as `occur' and
`multi-occur')."
    (interactive (list 'MSG))
    (unless (eq major-mode 'occur-mode) (error "You must be in `occur-mode'"))
    (let ((count  0))
      (save-excursion
        (goto-char (point-min))
        (while (condition-case nil (progn (occur-next) t) (error nil))
          (let* ((pos   (get-text-property (point) 'occur-target))
                 (buf   (and pos (marker-buffer pos))))
            (when buf
              (with-current-buffer buf
                (goto-char pos)
                (bmkp-set-autonamed-bookmark (point)))
              (setq count  (1+ count))))))
      (when msgp (message "Created %d autonamed bookmarks" count)))))

;;;###autoload
(defun bmkp-set-autonamed-regexp-buffer (regexp &optional msgp)
  "Set autonamed bookmarks at matches for REGEXP in the buffer."
  (interactive (list (read-string "Regexp: " nil 'regexp-history)
                     t))
  (bmkp-set-autonamed-regexp-region regexp (point-min) (point-max) 'MSG))

;;;###autoload
(defun bmkp-set-autonamed-regexp-region (regexp beg end &optional msgp)
  "Set autonamed bookmarks at matches for REGEXP in the region."
  (interactive (list (read-string "Regexp: " nil 'regexp-history)
                     (region-beginning) (region-end)
                     t))
  (let ((count  0))
    (save-excursion
      (goto-char beg)
      (while (re-search-forward regexp end t)
	(bmkp-set-autonamed-bookmark (point))
        (setq count  (1+ count))
	(forward-line 1)))
    (when msgp (message "Set %d autonamed bookmarks" count))))

(defun bmkp-autoname-bookmark (position)
  "Return a bookmark name using POSITION and the current buffer name.
The name is composed as follows:
 POSITION followed by a space and then the buffer name.
 The position value is prefixed with zeros to comprise 9 characters.
 For example, for POSITION value 31416 and current buffer `my-buffer',
 the name returned would be `000031416 my-buffer'"
  (format "%09d %s" (abs position) (buffer-name)))

;;;###autoload
(defun bmkp-delete-all-autonamed-for-this-buffer ()
  "Delete all autonamed bookmarks for the current buffer.
To be deleted, a bookmark name must be an autonamed bookmark whose
buffer part names the current buffer."
  (interactive)
  (let ((bmks-to-delete  (mapcar #'bookmark-name-from-full-record
                                 (bmkp-autonamed-this-buffer-alist-only))))
    (if (null bmks-to-delete)
        (message "No autonamed bookmarks for buffer `%s'" (buffer-name))
      (when (y-or-n-p (format "Delete ALL autonamed bookmarks for buffer `%s'? " (buffer-name)))
        (dolist (bmk  bmks-to-delete)  (bookmark-delete bmk))
        (message "Deleted all bookmarks for buffer `%s'" (buffer-name))))))

;; You can use this in `kill-buffer-hook'.
(defun bmkp-delete-autonamed-this-buffer-no-confirm ()
  "Delete all autonamed bookmarks for this buffer, without confirmation."
  (when (and bookmarks-already-loaded bookmark-alist)
    (let ((bmks-to-delete  (mapcar #'bookmark-name-from-full-record
                                   (bmkp-autonamed-this-buffer-alist-only))))
      (dolist (bmk  bmks-to-delete)  (bookmark-delete bmk)))))

;; You can use this in `kill-emacs-hook'.
(defun bmkp-delete-autonamed-no-confirm ()
  "Delete all autonamed bookmarks for all buffers, without confirmation."
  (when (and bookmarks-already-loaded bookmark-alist)
    (dolist (buf  (buffer-list))
      (with-current-buffer buf (bmkp-delete-autonamed-this-buffer-no-confirm)))))

;;;###autoload
(defun bmkp-delete-bookmarks (position allp &optional alist) ; Bound to `C-x p delete'
  "Delete some bookmarks at point or all bookmarks in the buffer.
With no prefix argument, delete some bookmarks at point.
If there is more than one, require confirmation for each.

With a prefix argument, delete *ALL* bookmarks in the current buffer.

Non-interactively, delete at POSITION.
Optional arg ALIST is the alist of bookmarks.  It defaults to
`bookmark-alist'."
  (interactive "d\nP")
  (let ((bmks-to-delete  (and allp (mapcar #'bookmark-name-from-full-record
                                           (bmkp-this-buffer-alist-only))))
        (bmks-deleted    ())
        bmk-pos)
    (cond ((and bmks-to-delete  (y-or-n-p (format "Delete ALL bookmarks in buffer `%s'? "
                                                  (buffer-name))))
           (dolist (bmk bmks-to-delete) (bookmark-delete bmk))
           (message "Deleted all bookmarks in buffer `%s'" (buffer-name)))
          (bmks-to-delete (message "Canceled - nothing deleted"))
          (allp (message "No bookmarks in buffer `%s' to delete" (buffer-name)))
          (t
           (dolist (bmk  (or alist bookmark-alist))
             (when (eq (setq bmk-pos  (bookmark-get-position bmk)) position)
               (add-to-list 'bmks-to-delete (bookmark-name-from-full-record bmk))))
           (if bmks-to-delete
               (cond ((cadr bmks-to-delete)
                      (dolist (bmk  bmks-to-delete)
                        (when (y-or-n-p (format "Delete bookmark `%s'? " bmk))
                          (bookmark-delete bmk)
                          (add-to-list 'bmks-deleted bmk)))
                      (message (if bmks-deleted
                                   (format "Deleted bookmarks: %s" bmks-deleted)
                                 "No bookmarks deleted")))
                     (t
                      (bookmark-delete (car bmks-to-delete))
                      (message "Deleted bookmark `%s'" (car bmks-to-delete))))
             (when (interactive-p) (message "No bookmarks at point to delete")))))))


;;;;;;;;;;;;;;;;;;;;;;;

(provide 'bookmark+-1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-1.el ends here
