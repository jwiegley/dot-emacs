;;; bookmark+-chg.el - Change logs for Bookmark+ libraries.
;;
;; Filename: bookmark+-chg.el
;; Description: Change logs for Bookmark+ libraries.
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2011, Drew Adams, all rights reserved.
;; Created: Fri Sep 15 07:58:41 2000
;; Last-Updated: Mon Aug  1 09:00:40 2011 (-0700)
;;           By: dradams
;;     Update #: 13713
;; URL: http://www.emacswiki.org/cgi-bin/wiki/bookmark+-chg.el
;; Keywords: bookmarks, bookmark+
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Change log for the Bookmark+ libraries, which extend standard
;;    library `bookmark.el'.  This file contains no code, so you need
;;    not load it.
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) code library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit'    - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other (non-bmenu) required code
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc'    - documentation (comment-only file)
;;    `bookmark+-chg'    - change log (this file)
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
;;    (The commentary links in #1 and #3 work only if you put library
;;    `bookmark+-doc.el' in your `load-path'.)
;;
;;
;;    ****** NOTE ******
;;
;;      On 2010-06-18, I changed the prefix used by package Bookmark+
;;      from `bookmarkp-' to `bmkp-'.  THIS IS AN INCOMPATIBLE CHANGE.
;;      I apologize for the inconvenience, but the new prefix is
;;      preferable for a number of reasons, including easier
;;      distinction from standard `bookmark.el' names.
;;
;;      This change means that YOU MUST MANUALLY REPLACE ALL
;;      OCCURRENCES of `bookmarkp-' by `bmkp-' in the following
;;      places, if you used Bookmark+ prior to this change:
;;
;;      1. In your init file (`~/.emacs') or your `custom-file', if
;;         you have one.  This is needed if you customized any
;;         Bookmark+ features.
;;
;;      2. In your default bookmark file, `bookmark-default-file'
;;         (`.emacs.bmk'), and in any other bookmark files you might
;;         have.
;;
;;      3. In your `*Bookmark List*' state file,
;;         `bmkp-bmenu-state-file' (`~/.emacs-bmk-bmenu-state.el').
;;
;;      4. In your `*Bookmark List*' commands file,
;;         `bmkp-bmenu-commands-file' (`~/.emacs-bmk-bmenu-commands.el'),
;;         if you have one.
;;
;;      You can do this editing in a virgin Emacs session (`emacs
;;      -Q'), that is, without loading Bookmark+.
;;
;;      Alternatively, you can do this editing in an Emacs session
;;      where Bookmark+ has been loaded, but in that case you must
;;      TURN OFF AUTOMATIC SAVING of both your default bookmark file
;;      and your `*Bookmark List*' state file.  Otherwise, when you
;;      quit Emacs your manually edits will be overwritten.
;;
;;      To turn off this automatic saving, you can use `M-~' and `M-l'
;;      in buffer `*Bookmark List*' (commands
;;      `bmkp-toggle-saving-bookmark-file' and
;;      `bmkp-toggle-saving-menu-list-state' - they are also in the
;;      `Bookmark+' menu).
;;
;;
;;      Again, sorry for this inconvenience.
 
;;(@> "Index")
;;
;;  If you have library `linkd.el' and Emacs 22 or later, load
;;  `linkd.el' and turn on `linkd-mode' now.  It lets you easily
;;  navigate around the sections of this doc.  Linkd mode will
;;  highlight this Index, as well as the cross-references and section
;;  headings throughout this file.  You can get `linkd.el' here:
;;  http://dto.freeshell.org/notebook/Linkd.html.
;;
;;  (@> "CHANGE LOG FOR `bookmark+-1.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-bmu.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-key.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-lit.el'")
;;  (@> "CHANGE LOG FOR `bookmark+-mac.el'")
;;  (@> "CHANGE LOG FOR `bookmark+.el'")
 
;;;(@* "CHANGE LOG FOR `bookmark+-1.el'")
;;
;; 2011/05/08 dadams
;;     Just put some definitions in alphabetic order - no real change.
;; 2011/04/25 dadams
;;     bmkp-bookmark-description: Added optional arg NO-IMAGE.
;;     bmkp-url-target-set: Protect url-get-url-at-point with fboundp.
;;     bmkp-(file-target|autofile)-set, bmkp-autofile-(add|remove)-tags:
;;       Added buffer-file-name as a default possibility.  Removed URL functions for that purpose.
;; 2011/04/24 dadams
;;     Added: bmkp-purge-notags-autofiles.
;;     bookmark-delete: Redefined to accept either bookmark or name as arg.
;;     bmkp-(url|file|compilation|occur)-target-set(-all), bmkp-autofile-(set|(add|remove)-tags):
;;       Removed optional args when read prefix.
;;     bmkp-occur-target-set-all: Made PREFIX arg optional too.
;;     Added some missing autoload cookies.  Removed some from non-def sexps.
;; 2011/04/21 dadams
;;     Added: bmkp-copied-tags, bmkp-copy-tags, bmkp-paste-add-tags, bmkp-paste-replace-tags..
;; 2011/04/20 dadams
;;     bmkp-remove-all-tags: Added optional arg no-cache-update-p.
;; 2011/04/19 dadams
;;     bmkp-make-record-for-target-file: Fixed backquotes on lambdas.
;; 2011/04/17 dadams
;;     bmkp-edit-tags: Do not apply bmkp-full-tag to the tags.
;; 2011/04/16 dadams
;;     Added: bmkp-edit-tags(-send|-mode(-map)), bmkp-return-buffer.
;;     bookmark-(rename|relocate|send-edited-annotation), bmkp-update-autonamed-bookmark,
;;       bmkp-(add|remove(-all)-tags:
;;         Wrap with-current-buffer around bmkp-refresh-menu-list.
;;     bookmark-(store|rename|write-file): Test emacs-major-version, not just (boundp 'print-circle).
;;     bmkp-autofile-add-tags: Fix interactive args - forgot to include DIR arg (= nil).
;; 2011/04/15 dadams
;;     Added: bmkp-autofile-alist-only, bmkp-autofile-bookmark-p.
;; 2011/04/13 dadams
;;     Added: bmkp-autofile-jump(-other-window) (aliases), bmkp-find-file(-other-window).
;;     bmkp-find-file-(all|some)-tags(-regexp)(-other-window): Bind use-file-dialog to nil.
;; 2011/04/12
;;     Added: bmkp-bookmark-name-member, bmkp-names-same-bookmark-p, bmkp-sort-omit,
;;            bmkp-remove-omitted, bmkp-delete-bookmark-name-from-list, bmkp-bookmark-a-file (alias),
;;            bmkp-autofile-(add|remove)-tags, bmkp-(un)tag-a-file (aliases),
;;            bmkp-get-autofile-bookmark, bmkp-find-file-(all|some)-tags(-regexp)(-other-window).
;;     Removed: bmkp-remove-assoc-dups, bmkp-sort-and-remove-dups.
;;     Applied renaming: bmkp-bmenu-omitted-list to bmkp-bmenu-omitted-bookmarks.
;;     bookmark-store: Redefine for all Emacs versions now:
;;       Put the bookmark on the name as property bmkp-full-record.  Use bmkp-maybe-save-bookmarks.
;;       Return the bookmark.
;;     bookmark-get-bookmark: Redefine for all Emacs versions now:
;;       If BOOKMARK is a bookmark-name string that has property bmkp-full-record, return that value.
;;     bookmark-send-edited-annotation: Make sure it's the annotation buffer that gets killed.
;;     bookmark-default-handler: Return nil, like vanilla (but why?).
;;     bookmark-location: Pass full bookmark to the various "get" functions.
;;     bookmark-rename: Put bmkp-full-record property on new name.
;;     bookmark-delete:
;;       Use bmkp-delete-bookmark-name-from-list: If name has bmkp-full-record property, use that
;;         with name to find bookmark to delete.
;;       Pass full bookmark to unlight.
;;     bmkp-edit-bookmark: Save if either is non-empty, not if both are.  Thx to Michael Heerdegen.
;;     bmkp-edit-bookmark-record: Bind print-circle to t around pp.
;;     bmkp-default-bookmark-name:
;;       Use bookmark-name-from-full-record plus bookmark-get-bookmark, not assoc.
;;       If BNAME is nil (no default) then do not try to look it up in alist.
;;     bookmark-write-file: Unpropertize only for Emacs 20 or nil bmkp-propertize-bookmark-names-flag.
;;                          Bind print-circle to t around pp.
;;     bmkp-save-menu-list-state: Make it interactive (a command).  Bind print-circle.
;;                                Use bmkp-maybe-unpropertize-bookmark-names on alists and name lists.
;;                                Bind print-circle to t around pp.
;;     bmkp-unomit-all: Use bmkp-delete-bookmark-name-from-list, not delete.
;;     bmkp-dired-this-dir-bookmark-p: Use bmkp-same-file-p, not string=.
;;     bmkp-url-target-set, bmkp-replace-existing-bookmark:: Return the bookmark.
;;     bmkp-file-target-set:  Return bookmark.  Added arg MSGP: msg if no file yet.
;;     bmkp-autofile-set:
;;       Added DIR arg and MSGP arg: msg if no file yet.  Return the bookmark.
;;       If read absolute file name, create bmk in its dir, not in default-directory.  Else use DIR.
;;       Use bmkp-get-autofile-bookmark, so uses bmkp-same-file-p for each file part (not equal).
;;     bmkp-marked-bookmark-p, bmkp-omitted-bookmark-p: Use bmkp-bookmark-name-member, not member.
;;     bookmark-location: Pass full bookmark to the various "get" functions.
;;     bmkp-choose-navlist-from-bookmark-list, bmkp-cycle-this-buffer:
;;       Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;;     bmkp-bookmark-description, bmkp-describe-bookmark-internals: Add Bookmark `' to title.
;;     bmkp-make-bookmark-list-record: Use bmkp-maybe-unpropertize-bookmark-names on lists.
;;     bmkp-printable-p: Bind print-circle to t around prin1.
;;     bmkp-delete-autonamed(-this-buffer)-no-confirm:
;;       Do nothing if bookmarks not loaded.  Thx to Christoph Scholtes.
;; 2011/04/03 dadams
;;     Added: bmkp-make-record-for-target-file, bmkp-replace-existing-bookmark (not used).
;;     bmkp-file-this-dir-bookmark-p: Corrected it to compare directory to default-directory.
;;     bmkp-file-target-set: Added arg NO-OVERWRITE (pass to bookmark-store).
;;                           Use (new) bmkp-make-record-for-target-file.
;;     bmkp-autofile-set: Do nothing if bookmark with same name, file and dir exists.
;;                        Else create one, even if the bookmark name is the same.
;;                        You can have multiple autofile bookmarks with the same name (diff files).
;; 2011/04/02 dadams
;;     Added: bmkp-autofile-set, bmkp-file-this-dir-(all|some)-tags(-regexp)-jump(-other-window),
;;            bmkp-file-this-dir-(all|some)-tags(-regexp)-alist-only.
;; 2011/04/01 dadams
;;     Moved key and menu bindings to (new) bookmark+-key.el.
;;     Added: bmkp-(dired|file)-this-dir-alist-only, bmkp-(dired|file)-this-dir-bookmark-p,
;;            bmkp-file-this-dir-jump(-other-window).
;;     Renamed: bmkp-dired-jump-current(*) to bmkp-dired-this-dir-jump(*).
;;     bmkp-dired-this-dir-jump(-other-window): Use bmkp-dired-this-dir-alist-only.
;;     bmkp-types-alist: Added (dired|file)-this-dir.
;;     Bound bmkp-(dired|file)-this-dir-jump to C-d and C-f in bookmark-jump(-other-window)-map.
;;     bmkp-jump-dired, bmkp-jump-man: Treat null bmkp-jump-display-function as display-buffer.
;; 2011/03/26 dadams
;;     Added: bmkp-file-(all|some)-tags(-regexp)-(alist-only|jump(-other-window)).
;;     bmkp-jump-menu: Added the new commands, but not Emacs 20, to avoid crash if byte-compiled.
;;     bmkp-bookmark-jump*-other-window: Simplified doc strings - refer to same-window version. 
;; 2011/03/17 dadams
;;     bmkp-describe-bookmark: Added 10-pixel margin around thumbnail image.
;; 2011/03/11 dadams
;;     Protect use of mouse-wheel-*-event with boundp.  Thx to Chris Poole.
;; 2011/03/04 dadams
;;     bmkp-bookmark-description, bmkp-describe-bookmark: Added clickable thumbnail to the help.
;;     bmkp-bookmark-description: Split file name into dir & relname, so shorter line, in help.
;; 2011/03/03 dadams
;;     Added: bmkp-all-exif-data, bmkp-bookmark-image-bookmark-p.
;;     bmkp-bookmark-description: Handle image EXIF data.
;; 2011/01/03 dadams
;;     Removed autoload cookies from non def* sexps and from define-key and define-prefix-command.
;;     Added some missing autoload cookies for commands, in particular redefined standard commands.
;; 2010/12/10 dadams
;;     Added defalias for bookmark-name-from(-full)-record, to fix gratuitous Emacs name change.
;; 2010/10/22 dadams
;;     Uncommented key bindings for mouse wheel, since Emacs bug #6256 has now been fixed.
;;     bmkp-repeat-command: Don't bother to let-bind repeat-previous-repeated-command,
;;                          and use setq, not let, for last-repeatable-command. Thx to Stefan Monnier.
;; 2010/09/28 dadams
;;     Added: bmkp-delete-autonamed(-this-buffer)-no-confirm.
;; 2010/09/25 dadams
;;     Added: option bmkp-default-bookmark-name, bmkp-annotated-alist-only.
;;     Added: bmkp-(next|previous)-*(-repeat), using macro bmkp-define-next+prev-cycle-commands.
;;     bmkp-default-bookmark-name: Respect option.
;;     bookmark-edit-annotation-mode, bookmark-edit-annotation:
;;       Use bmkp-annotated-alist-only (and new bmkp-default-bookmark-name).
;;     bookmark-send-edited-annotation:
;;       End in orig buffer, not bmenu buffer.  Delete edit window.  Thx to Joe Bloggs.
;; 2010/09/24 dadams
;;     Added: bmkp-autonamed(-this-buffer)-jump(-other-window).  Bound to C-x j # (#|.) and menus.
;;     Added, using bmkp-define-cycle-command:
;;       bmkp-cycle-(autonamed|bookmark-list|desktop|dired|gnus|info|lighted|(local-|remote-)file|
;;                   man|non-file|remote-file|specific-(buffers|files)|variable-list|url)
;;                   (-other-window).
;;     Added redefinitions: bookmark-edit-annotation(-mode).
;;     Renamed: *varlist* to *variable-list*.
;;     bmkp-autoname-format: Added ^ to anchor numeral at beginning.
;;     bookmark--jump-via: Don't update autonamed if using w32 association.
;;     bmkp-update-autonamed-bookmark: bmkp-refresh-menu-list only if buffer list is displayed.
;;     *-(relocate|rename), *-update-autonamed-bookmark, *-remove-all-tags, *-(add|remove)-tags:
;;       Don't create bookmark-list buffer if doesn't exist.
;;     bookmark-show-(annotation|all-annotations): Restore selected window and frame focus.
;;     bmkp-completing-read-(buffer|file)-name: Added optional NO-DEFAULT-P arg.
;;     bmkp-describe-bookmark: Default to highlighted bookmarks on line, if there are any.
;;     bmkp-specific-(buffers|files)-jump(-other-window): Allow empty input, to end loop.
;;     bmkp-cycle: Ensure bmkp-current-nav-bookmark is a bookmark, else redefine.  Use %9d, not %d.
;;     bmkp-cycle-other-window: Added optional STARTOVERP arg here too.
;; 2010/09/20 dadams
;;     bmkp-choose-navlist-of-type: Empty input means "any".
;; 2010/09/16 dadams
;;     bmkp-read-bookmark-file-name:
;;       Removed extra default-filename in call to read-file-name.  Thx to Pedro Insua.
;; 2010/08/22 dadams
;;     Added: bmkp-regexp-filtered-annotation-alist-only.
;; 2010/08/20 dadams
;;     Added: bmkp-read-bookmark-file-name.
;;     bookmark-save, bookmark-load, bmkp-switch-bookmark-file, bmkp-use-bookmark-file-create:
;;       Use bmkp-read-bookmark-file-name.
;; 2010/08/19 dadams
;;     Require gnus-sum.el when compile (for macro).  Thx to S. Nemec.
;; 2010/08/18 dadams
;;     Removed eval-when-compile for bookmark+-lit.el.
;;     Replaced defvar of bmkp-edit-bookmark-record-mode-map with a define-key after derived mode.
;; 2010/08/17 dadams
;;     bmkp-edit-bookmark: Made interactive.  Bound to C-x p E.  Added optional INTERNALP arg.
;;     bmkp-info-bookmark-p: Return nil if a different handler.
;; 2010/08/15 dadams
;;     Moved bmkp-define-file-sort-predicate, bmkp-menu-bar-make-toggle to bookmark+-mac.el.
;;     Require: bookmark.el, bookmark+-mac.el.
;;     Require for compile: bookmark+-bmu.el, bookmark+-lit.el (soft).
;;     Ensure this file is loaded before compiling.
;;     bmkp-set-bookmark-file-bookmark: Added missing arg for error format string.
;; 2010/08/08 dadams
;;     bookmark-jump: Added optional arg DISPLAY-FUNCTION (Emacs 24).
;;     bookmark-handle-bookmark:
;;       Move non-default handler call outside condition-case.
;;       Updated for Emacs 24: Use error condition bookmark-error-no-filename.  Added props for it.
;;     bookmark-default-handler: Updated for Emacs 24: 
;;       Signal condition bookmark-error-no-filename, not file-error, and pass (stringp FILE).
;;     bookmark-make-record-default: Added optional args NO-CONTEXT, POSITION (Emacs 24), and VISITS.
;;     bookmark-load: Updated for Emacs 24: Wrap with abbreviate-file-name.
;;     bmkp-jump-1: Allow arg to be a bookmark or its name.
;;     bmkp-gnus-bookmark-p: Updated for Emacs 24: Added gnus-summary-bookmark-jump.
;;     bmkp-jump-gnus: Different gnus-fetch-group call for Emacs 20, 21.
;;     bmkp-make-(desktop|varlist|bookmark-(file|list))-record: Call *-record-default with NO-CONTEXT.
;;     w3m-current-title: Use w3m-current-title as bookmark name.
;;     bmkp-w3m-set-new-buffer-name, bmkp-jump-w3m*: Require w3m.
;;     bmkp-make-gnus-record: Get bookmark name from gnus-summary-article-header.
;;     Update for Emacs 24: Bypass bmkp specific Gnus, man, and woman code.
;; 2010/08/06 dadams
;;     Added (and bound the commands):
;;       bmkp-(compilation|occur)-target-set(-all), bmkp-(file|url)-target-set,
;;       bmkp-default-handler-associations, bmkp-compilation-file+line-at,
;;       bmkp-default-handler-(for-file|user), bmkp-sound-jump.
;;     bmkp-occur-create-autonamed-bookmarks: Do not define it  for Emacs < 22.  Protect wrt POS, BUF.
;;     Added to Bookmark menu: bmkp-(file|url)-target-set, bmkp-set-(bookmark-file|desktop)-bookmark.
;; 2010/08/04 dadams
;;     bmkp-edit-bookmark: Use new bookmark name for update of dired-directory.  Thx to Kai Tetzlaff.
;; 2010/08/03 dadams
;;     bmkp-make-url-browse-record: Remove text properties from URL arg.
;; 2010/07/17 dadams
;;     Added: bmkp-url-jump-(other-window), bmkp-url(-browse)-(alist-only|bookmark-p), bmkp-url-cp,
;;            bmkp-url-history, bmkp-make-url-browse-record, bmkp-jump-url-browse.
;;     bmkp-sort-comparer: Use bmkp-url-cp, not bmkp-w3m-cp.
;;     bmkp-types-alist: w3m -> url.
;;     bookmark-alist: Updated doc string to mention LOCATION.  W3M -> URL.
;;     bmkp-bookmark-description: Treat URL.  Set no-position-p depending on start.
;;     Bind bmkp-url-jump*.  Replace W3M by URL in menu items.
;; 2010/07/14 dadams
;;     Created from bookmark+.el code.
 
;;;(@* "CHANGE LOG FOR `bookmark+-bmu.el'")
;;
;; 2011/07/01 dadams
;;     bmkp-bmenu-change-sort-order, bmkp(-multi)-reverse-sort-order: Handle null CURRENT-BMK.
;; 2011/04/24 dadams
;;     Added to Tags menu: Purge Autofiles with No Tags.
;; 2011/04/23 dadams
;;     Bound bmkp-bmenu-set-tag-value-for-marked to T > v and added to bmkp-bmenu-tags-menu.
;;     bmkp-bmenu-mouse-3-menu: Added bmkp-rename-tag.
;; 2011/04/22 dadams
;;     Bound *-copy-tags to T c, T M-w, *-paste(-add|replace)-tags to T p, T C-y, T q.
;; 2011/04/21 dadams
;;     Added:  bmkp-bmenu-copy-tags, bmkp-bmenu-paste-add-tags(-to-marked),
;;             bmkp-bmenu-paste-replace-tags(-for-marked).
;;     Bound and added to menus: bmkp-bmenu-paste-add-tags-to-marked,
;;                               bmkp-bmenu-paste-replace-tags-for-marked.
;;     Added to This Bookmark menu: bmkp-bmenu-copy-tags, bmkp-bmenu-paste(-add|replace)-tags.
;; 2011/04/19 dadams
;;     Added: bmkp-bmenu-unmark-bookmarks-tagged-regexp.  Bound it to T u %.  Added it to menu.
;; 2011/04/16 dadams
;;     Added: bmkp-edit-tags-send.  Bound it to T e in bookmark-bmenu-mode-map.
;;     bookmark-bmenu-mode: Updated help text for tags editing.
;;     bmkp-maybe-unpropertize-bookmark-names:
;;       Test emacs-major-version, not just (boundp 'print-circle).
;; 2011/04/15 dadams
;;     Added: bmkp-bmenu-mark-autofile-bookmarks, bmkp-bmenu-show-only-autofiles.
;;       And added them to menus.
;;     bookmark-bmenu-mode-map:
;;       Bind bmkp-bmenu-mark-autofile-bookmarks, bmkp-bmenu-show-only-autofiles to A M, A S.
;;       Bind bookmark-bmenu-show-all-annotations to M-a, not A.
;;       Bind bmkp-bmenu-search-marked-bookmarks-regexp to M-s a M-s, not M-a.
;;       Bind *-mark-url-bookmarks, *-show-only-urls to M-u M-m, M-u M-s, not M-u M, M-u S.
;;     bookmark-bmenu-mode: Updated help to reflect latest bindings.
;; 2011/04/13 dadams
;;     bmkp-bmenu-tags-menu: Added: bmkp-(un)tag-a-file.
;; 2011/04/12
;;     Added: bmkp-propertize-bookmark-names-flag, bmkp-maybe-unpropertize-bookmark-names,
;;            bmkp-bmenu-get-marked-files.
;;     Renamed: bmkp-bmenu-omitted-list to bmkp-bmenu-omitted-bookmarks.
;;     bmkp-bmenu-define-full-snapshot-command:
;;       Bind print-circle to t around pp.  Use bmkp-maybe-unpropertize-bookmark-names on lists.
;;     bookmark-bmenu-(show|hide)-filenames, bmkp-bmenu-toggle-show-only-(un)marked,
;;       bmkp-bmenu-(un)omit-marked:
;;         Fit one-window frame only if selected window is *Bookmark List*.
;;     bookmark-bmenu-bookmark: Added optional arg FULL.  Non-nil means return full bookmark record.
;;     bookmark-bmenu-unmark, bookmark-bmenu-delete, bmkp-bmenu-unomit-marked:
;;       Use bmkp-delete-bookmark-name-from-list, not delete.
;;     bookmark-bmenu-execute-deletions: Pass full bookmark, not name, to delete, and don't use assoc.
;;     bookmark-bmenu-rename: Use bmkp-bmenu-goto-bookmark-named instead of just searching for name.
;;     bmkp-bmenu-toggle-marks, bmkp-bmenu-unomit-marked, bmkp-bmenu-define-jump-marked-command,
;;       bmkp-bmenu-mouse-3-menu:
;;         Use bmkp-bookmark-name-member, not member.
;;     bmkp-bmenu-make-sequence-from-marked: Do not invoke bookmark-bmenu-list when no displayed list.
;;     bmkp-bmenu-define-command: Use bmkp-maybe-unpropertize-bookmark-names on *-omitted-bookmarks.
;;     bmkp-bmenu-list-1: Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;;                        Pass full bookmark to bmkp-bmenu-propertize-item.
;;     bmkp-bmenu-propertize-item:
;;       First arg is now a full bookmark, not a bookmark name.  Get bookmark name from it.
;;       Put prop bmkp-bookmark-name on buffer text with propertized bookmark-name string as value.
;;       String has property bmkp-full-record with value the full bookmark record, with string as car.
;;       Return propertized bookmark-name string.
;;     bmkp-bmenu-isearch-marked-bookmarks(-regexp), bmkp-bmenu-dired-marked,
;;       bmkp-bmenu-(search|query-replace)-marked-bookmarks-regexp:
;;         Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;;     bmkp-bmenu-goto-bookmark-named:
;;       If NAME has property bmkp-full-record then go to the bookmark it indicates.  Otherwise, just
;;       go to the first bookmark with the same name.
;;     bookmark-bmenu-mode: Added bmkp-save-menu-list-state (now a command) to the mode help.
;; 2011/04/02 dadams
;;     bookmark-bmenu-mode: Added to mode help: bmkp-file-this-dir-(all|some)-tags(-regexp)-jump.,
;;                                              Create/Set section, with bmkp-autofile-set.
;; 2011/04/01 dadams
;;     bookmark-bmenu-mode: Added to mode help: bmkp-(dired|file)-this-dir-jump.
;; 2011/03/26 dadams
;;     bookmark-bmenu-mode: Added new file-with-tags jump commands to the help.
;; 2011/03/05 dadams
;;     bmkp-bmenu-edit-bookmark: Use bmkp-refresh-menu-list, not *-surreptitiously-rebuild-list.
;; 2011/02/11 dadams
;;     Faces: Better defaults for dark background.
;; 2011/01/03 dadams
;;     Removed autoload cookies from non def* sexps and from define-key.
;;     Added missing autoload cookies for commands, in particular redefined std commands & defalias.
;; 2010/12/10 dadams
;;     Added defalias for bookmark-name-from(-full)-record, to fix gratuitous Emacs name change.
;; 2010/09/24 dadams
;;     Added: bmkp-bmenu-show-only-autonamed.  Bound to # S.  Added to bmkp-bmenu-show-menu.
;;     bookmark-bmenu-mode: Updated doc string for autonamed jumps, show.
;;     Renamed varlist to variable-list everywhere.
;; 2010/08/22 dadams
;;     Added: bmkp-bmenu-filter-annotation-incrementally, bookmark-bmenu-relocate (Emacs 20, 21),
;;            bmkp-bmenu-filter-alist-by-annotation-regexp.  Bound, added to menus and help.
;; 2010/08/18 dadams
;;     Removed eval-when-compile for bookmark+-(lit|1).el.
;;     bmkp-bmenu-propertize-item: Inconsequential simplification.
;; 2010/08/17 dadams
;;     bmkp-bmenu-edit-bookmark: Added optional arg INTERNALP (prefix arg), for editing record.
;; 2010/08/15 dadams
;;     Moved to bookmark+-mac.el:
;;       bmkp-define-sort-command, bmkp-replace-regexp-in-string, bmkp-assoc-delete-all.
;;     Renamed: bmkp-barf-if-not-in-menu-list to bmkp-bmenu-barf-if-not-in-menu-list.
;;     Require bookmark.el, bookmark+-mac.el.
;;     Require when compile: bookmark+-1.el, bookmark+-lit.el (soft).
;; 2010/07/17 dadams
;;     Added: bmkp-bmenu-mark-url-bookmarks, bmkp-bmenu-show-only-urls, bmkp-bmenu-sort-by-url.
;;     Removed: bmkp-bmenu-sort-by-w3m-url.
;;     Replaced face bmkp-w3m by bmkp-url.
;;     bookmark-bmenu-mode: Added mark and show URL commands.
;;     bookmark-bmenu-mode, *-status-help, *-sort-by-bookmark-type, *-define-sort-command: w3m -> url.
;;     Bind bmkp-bmenu-sort-by-url, not bmkp-bmenu-sort-by-w3m-url.
;;     Bind bmkp-bmenu-mark-url-bookmarks, bmkp-bmenu-show-only-urls.
;;     Replace W3M by URL in menu items.
;; 2010/07/14 dadams
;;     Created from bookmark+.el code.
 
;;;(@* "CHANGE LOG FOR `bookmark+-key.el'")
;;
;; 2011/04/24 dadams
;;     Added to Bookmarks menu and its Tags submenu: Purge Autofiles with No Tags.
;; 2011/04/23 dadams
;;     bmkp-tags-menu:
;;       Added bmkp-set-tag-value, bmkp-(add|remove|copy)-tags, bmkp-paste-(add|replace)-tags.
;; 2011/04/21 dadams
;;     Bound: bmkp-copy-tags, bmkp-paste-add-tags, bmkp-paste-replace-tags.
;; 2011/04/16 dadams
;;     Added: bmkp-tags-map.  Bound tag commands to prefix C-x p t.
;; 2011/04/14 dadams
;;     Renamed menu Jump To Bookmark to just Jump To, in menu-bar-bookmark-map.
;; 2011/04/13 dadams
;;     Added:
;;       bmkp-find-file-menu (bmkp-find-file(-(all|some)-tags(-regexp)(-other-window)),
;;       bmkp-jump-tags-menu (what was in main, plus bmkp-find-file-*-tags-regexp*),
;;       bmkp-tags-menu (list all, rename, remove from all, (un)tag a file).
;;     bmkp-jump(-other-window)-map:
;;       Added bmkp-find-file(-other-window) to menu.
;;       Bound keys for bmkp-find-file-(all|some)-tags(-regexp)(-other-window): C-x (4) j t a...
;; 2011/04/02 dadams
;;     Added bindings for (new) bmkp-autofile-set,
;;                              bmkp-file-this-dir-(all|some)-tags(-regexp)-jump(-other-window).
;; 2011/04/01 dadams
;;     Added to bmkp-jump-menu: bmkp-(dired|file)-this-dir-jump-other-window.
;;     Created from code in bookmark+-1.el.
 
;;;(@* "CHANGE LOG FOR `bookmark+-lit.el'")
;;
;; 2011/04/12
;;     bmkp-cycle-lighted-this-buffer: Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;; 2011/04/01 dadams
;;     bmkp-light-bookmark(s): Don't call bookmark-handle-bookmark.  Wrap with with-current-buffer.
;; 2011/01/03 dadams
;;     Added autoload cookies: defcustoms and commands.
;; 2010/12/10 dadams
;;     Added defalias for bookmark-name-from(-full)-record, to fix gratuitous Emacs name change.
;; 2010/09/25 dadams
;;     Added: bmkp-set-lighting-for(bookmarks|(-this)-buffer).  Requested by Joe Bloggs.
;;     bmkp-set-lighting-for-bookmark: Added LIGHT-NOW-P arg (from prefix arg).
;; 2010/09/11 dadams
;;     Removed eval-when-compile for bookmark+-bmu, bookmark+-1.
;; 2010/08/15 dadams
;;     Require: bookmark.el.
;;     Require when compile: bookmark+-bmu.el, bookmark+-1.el, pp+.el (soft).
;;     Applied renaming of bmkp-barf-if-not-in-menu-list to bmkp-bmenu-barf-if-not-in-menu-list.
;;     bmkp-light-bookmark(s): Added missing arg to throw call.
;;     bmkp-light-bookmarks: Use bmkp-remove-if, not remove-if.
;;     bmkp-light-bookmarks-in-region, bmkp-light-non-autonamed-this-buffer:
;;       Use bmkp-remove-if-not, not remove-if-not.
;;     bmkp-read-set-lighting-args: Use pp-read-expression-map only if bound (pp+.el).
;; 2010/07/03 dadams
;;     bmkp-set-lighting-for-bookmark, bmkp-bmenu-set-lighting-for-marked:
;;       Use *-refresh-menu-list, not *-surreptitiously-*.
;; 2010/07/01 dadams
;;     Created.
 
;;;(@* "CHANGE LOG FOR `bookmark+-mac.el'")
;;
;; 2011/04/12
;;     bmkp-define-cycle-command: Use bmkp-sort-omit, not bmkp-sort-and-remove-dups.
;; 2011/01/03 dadams
;;     Added autoload cookies: defmacro.
;; 2010/09/25 dadams
;;     Added: bmkp-define-next+prev-cycle-commands.
;; 2010/09/24 dadams
;;     Added: bmkp-define-cycle-command.
;; 2010/08/18 dadams
;;     Removed eval-when-compile for bookmark+-(bmu|1).el.
;; 2010/08/15 dadams
;;     Created, from code in other Bookmark+ files.
 
;;;(@* "CHANGE LOG FOR `bookmark+.el'")
;;
;; 2011/04/12 dadams
;;     Version 3.2.2.
;; 2011/04/01 dadams
;;     Require bookmark+-key.el (new).  Version 3.2.1.
;; 2011/01/03 dadams
;;     Added autoload cookies: defconst, command.
;; 2010/08/19
;;     bmkp-version-number: Version 3.2.0.
;; 2010/08/15 dadams
;;     Require bookmark+-mac.el.
;;     Do not ensure loaded before compile (not needed here now).
;; 2010/07/14 dadams
;;     Version 3.1.1.
;;     Moved main content of bookmark+.el to new files bookmark+-1.el and bookmark+-bmu.el.
;; 2010/07/13 dadams
;;     Version 3.1.0.
;;     Added redefinitions: bookmark-bmenu-(1|2)-window, bookmark-bmenu-other-window-with-mouse,
;;                          bookmark-bmenu-this-window, bookmark-bmenu-switch-other-window.
;;     Added: bmkp-last-bookmark-file, bmkp-switch-to-last-bookmark-file.
;;     Removed pre-23 version of bookmark-bmenu-switch-other-window.
;;     bookmark-load: Use bmkp-last-bookmark-file when read file name.  Added missing prefix arg.
;;                    Save old current as bmkp-last-bookmark-file.
;;     bookmark-bmenu-list: If bookmark file has changed do not restore state saved from other file.
;;                          Save old current as bmkp-last-bookmark-file.
;;     bmkp-bmenu-list-1: Do not use bmkp-bmenu-title if it is empty ("").
;;     bookmark-bmenu-mode: Added to doc string: bmkp-switch-bookmark-file.
;;     bookmark-bmenu-other-window: Do not bind bookmark-automatically-show-annotations (per vanilla).
;;     bookmark-bmenu-show-annotation: Ensure in bmenu list and on a bookmark line.
;;     bmkp-switch-bookmark-file: Use bmkp-last-bookmark-file when read file name.
;;     bmkp-bmenu-define-full-snapshot-command: Set bmkp-last-bookmark-file.
;;     bmkp-bookmark-description: Fixed typo: bmkp-bookmark-file-bookmark-p (not desktop).
;;     bmkp-make-bookmark-file-record: Use arg file (not bmkp-non-file-filename) as filename entry.
;;     
;;     Added more autoload cookies.
;; 2010/07/09 dadams
;;     Added: bmkp-bmenu-mark-bookmark-file-bookmarks, bmkp-bmenu-show-only-bookmark-files,
;;            bmkp-bookmark-file-jump, bmkp-set-bookmark-file-bookmark, bmkp-bookmark-file-history,
;;            bmkp-use-bookmark-file-create, bmkp-bookmark-file, bmkp-bookmark-file-alist-only,
;;            bmkp-bookmark-file-bookmark-p, bmkp-jump-bookmark-file, bmkp-make-bookmark-file-record.
;;     bmkp-types-alist, bmkp-buffer-names, bmkp-bmenu-mode-status-help, bmkp-bmenu-propertize-item,
;;       bmkp-this-buffer-p, bmkp-last-specific-buffer-p, bmkp-specific-buffers-alist-only,
;;       bmkp-bookmark-description, bookmark-bmenu-mode:   Updated for bookmark-file bookmarks.
;;     bookmark--jump-via: Added a catch, so a handler can skip all other processing when it's done.
;;     bookmark-load: Final msg says whether overwritten.
;;     Bound and added to menus: bmkp-set-bookmark-file-bookmark,
;;                               bmkp-bmenu-mark-bookmark-file-bookmarks,
;;                               bmkp-bmenu-show-only-bookmark-files, bmkp-bookmark-file-jump.
;; 2010/07/07 dadams
;;     bookmark-handle-bookmark: Bind use-dialog-box, use-file-dialog to nil.
;;     bookmark-location: From Emacs 23: Use location property and -- Unknown location --.
;;     bmkp-switch-bookmark-file: Bind insert-default-directory to nil.
;;     bmkp-empty-file: Expand FILE.  Return FILE.
;; 2010/07/03 dadams
;;     Added: bmkp-bmenu-describe-marked, bmkp-bookmark-description.
;;     bmkp-describe-bookmark: Rewrote to use bmkp-bookmark-description.
;;     Bound bmkp-bmenu-describe-marked to C-h >.
;;     bmkp-bmenu-menubar-menu: Added bmkp-bmenu-describe-(marked|bookmark).
;;     Updated doc string of bookmark-alist.
;; 2010/07/01 dadams
;;     Added: bmkp-bmenu-mark-lighted-bookmarks, bmkp-bmenu-set-tag-value-for-marked,
;;            bmkp-bmenu-show-only-tagged, bmkp-occur-create-autonamed-bookmarks,
;;            bmkp-set-autonamed-bookmark, bmkp-set-autonamed-bookmark-at-line,
;;            bmkp-set-autonamed-regexp-buffer, bmkp-set-autonamed-regexp-region,
;;            bmkp-set-tag-value-for-navlist, bmkp-prompt-for-tags-flag, bmkp-menu-bar-make-toggle,
;;            bmkp-same-creation-time-p, bmkp-set-tag-value-for-bookmarks,
;;            bmkp(-bmenu)-highlight-menu, bmkp-options-menu.
;;     Renamed: bmkp-use-region-flag to bmkp-use-region,
;;              bmkp-bmenu-jump-menu to bmkp-jump-menu.
;;     Removed: bmkp-cycle-this-buffer-buff (unused).
;;     Soft-require new library bookmark+-lit.el.
;;     Split off new file bookmark+-chg.el from bookmark+-doc.el.
;;     Changed default values of faces bmkp->-mark, bmkp-t-mark.
;;     bmkp-crosshairs-flag: Added :set instead of add-hook at top level.
;;     bmkp-use-region: Changed from boolean to choice - added cycling-too value.
;;     bookmark-set: Added INTERACTIVEP arg.  Prompt for tags when bmkp-prompt-for-tags-flag.
;;                   Auto-highlight when set, per bmkp-auto-light-when-set.
;;     bookmark--jump-via: Auto-highlight when jump, per bmkp-auto-light-when-jump.
;;                         Set BOOKMARK to result of bmkp-update-autonamed-bookmark.
;;                         Bind orig-buff when running hook.
;;     bookmark-default-handler: Pass the bookmark too as an arg to bmkp-goto-position.
;;     bookmark-relocate, bookmark-rename, bmkp-bmenu-list-1, bmkp-remove(-all)-tags, bmkp-add-tags:
;;       Add 0 as FRAME arg to get-buffer-window.
;;     bookmark-delete: Remove any highlighting on bookmark.
;;     bmkp-bmenu-list-1: Add highlight-overrides indicator.
;;     bmkp-completing-read-1: Added (not laxp) guard for first branch of main if.
;;     bmkp-crosshairs-highlight: Assign a priority.  Make the cmd a no-op for Emacs 20-21.
;;     bmkp-choose-navlist-*, bmkp-navlist-bmenu-list, bmkp-jump-in-navlist*,
;;       bmkp-cycle(-this-buffer*):
;;         Set bmkp-current-nav-bookmark to bookmark, not to its name.
;;     bmkp-update-autonamed-bookmark: Do not set bmkp-current-nav-bookmark to the name.
;;                                     Call bmkp-refresh-menu-list even if menu list is not displayed.
;;                                     Pass the bookmark name to bmkp-refresh-menu-list.
;;                                     Return the updated BOOKMARK.
;;     bmkp-refresh-menu-list: Set window point also.
;;     bmkp-goto-position:
;;       Added BOOKMARK arg.  When bmkp-save-new-location-flag, update BOOKMARK.  Return indicator.
;;     bmkp-create-varlist-bookmark: Call bookmark-set with INTERACTIVEP arg.
;;     bmkp-cycle(-this-buffer*): Added STARTOVERP arg. Pass OTHER-WINDOW, STARTOVERP to bmkp-cycle-1.
;;     bmkp-cycle-1: Added STARTOVERP arg.  If non-nil pop-up-frames, then inhibit showing annotation.
;;                   Use region only if bmkp-use-region value is cycling-too.
;;                   Use eq for *-list-position test.  If *-list-position returns nil, then reset.
;;                   Use save-selected-window, unlesl OTHER-WINDOW.
;;     bmkp-(next|previous)-bookmark(-this-buffer|-w32): Added STARTOVERP arg.  C-u: start over at 1.
;;     Bind highlight cmds: *-map: h,H,u,U,C-u,=,C-up|down.  *-bmenu-*map: H+,H>+,H>H,HH,HS,H>U,HU.
;;                          *-jump-map: h.  Bind TS in *-bmenu-*map.
;;     Add bmkp-occur-create-autonamed-bookmarks to occur-mode-map as C-c b.
;;     Menus: Added Highlight, Toggle Option.  Added light to Jump To, Show, Mark, mouse.  Reorder.
;; 2010/06/23 dadams
;;     Split the change log off from file bookmark+-doc.el to new file bookmark+-chg.el.
;; 2010/06/21 dadams
;;     Renamed: bmkp-toggle-autoname-bookmark-set/delete to bmkp-toggle-autonamed-bookmark-set/delete,
;;              bmkp-autonamed-bookmarks-alist-only to bmkp-autonamed-this-buffer-alist-only,
;;              bmkp-bookmark-autoname-p to bmkp-autonamed-bookmark-for-buffer-p,
;;     Added: bmkp-autonamed-alist-only, bmkp-non-autonamed-alist-only, bmkp-autonamed-bookmark-p, 
;;     bmkp-completing-read-1: Use DEFAULT as default.  Use just (not lax) - no non-t.
;;                             Use DEFAULT if empty input only if DEFAULT is non-nil.
;;     bmkp-choose-navlist-of-type: Added pseudo-type "any".
;;     bmkp-specific-buffers-alist-only: Exclude desktop etc. bookmarks.
;;     bmkp-update-autonamed-bookmark: Arg can be a bookmark (not just name).
;; 2010/06/19 dadams
;;     RENAMED bookmarkp* TO bmkp*.  ***** THIS IS AN INCOMPATIBLE CHANGE ******
;;
;;       If you have existing customizations, or if you have bookmarks that have the (internal) tag
;;       "bmkp-jump", then YOU MUST REPLACE occurrences of "bookmarkp" by "bmkp" EVERYWHERE.  This
;;       includes replacing occurrences in (1) your bookmarks file (bookmark-default-file), (2) your
;;       state file (bmkp-bmenu-state-file), and (3) your command file (bmkp-bmenu-commands-file).
;;
;;     Changed *-bmenu-w32-open-select binding to M-o from M-v.
;; 2010/06/11 dadams
;;     Wrap all (require '* nil t) in condition-case.
;; 2010/06/07 dadams
;;     Fix deskstop bookmarks for Emacs < 22.  Protect:
;;       *-release-lock with fboundp, *-buffer-args-list with boundp, *-dir with Emacs version #, 
;; 2010/05/30 dadams
;;     Added: bookmarkp-(next|previous)-bookmark-w32(-repeat).  Bound to C-x p (next|prior).
;; 2010/05/29 dadams
;;     *-bmenu-list, *-choose-navlist-from-bookmark-list, *-bmenu-define(-full-snapshot)-command,
;;       *-save-menu-list-state, -make-bookmark-list-record:
;;         Add/restore bookmarkp-bmenu-filter-pattern to/from state.
;;     *-jump-bookmark-list: Set bookmarkp-latest-bookmark-alist to  bookmark-alist.
;;     Reordered Bookmark menu and added items:
;;       Set Bookmark, Delete Autonamed Bookmark, Delete All Autonamed Bookmarks Here,
;;       Delete Bookmarks Here, Delete Bookmark, Rename Bookmark, Bookmark List for This Buffer,
;;       Bookmark List for Navlist, Set Navlist to Bookmarks of Type,
;;       Set Navlist from Bookmark-List Bookmark, Insert Bookmark Contents, Insert Bookmark Location.
;;     Added to Bookmark+ menu: Set Navlist *.
;;     Added to bookmarkp-bmenu-jump-menu: In Navigation List. 
;;     Added :enable entries for menu items.
;;     Updated bookmark-bmenu-mode doc string for cycling, navlist, and options.
;;     Corrected bindings of bookmarkp-jump-in-navlist(-other-window).
;; 2010/05/26 dadams
;;     Added:
;;       bookmarkp-choose-navlist-(from-bookmark-list|of-type), bookmarkp-crosshairs-highlight,
;;       bookmarkp-cycle(-this-buffer)(-other-window), bookmarkp-delete-bookmarks, 
;;       bookmarkp-jump-in-navlist(-other-window), bookmarkp-navlist-bmenu-list,
;;       bookmarkp-(next|previous)-bookmark(-this-buffer)(-repeat),
;;       bookmarkp-toggle-autoname-bookmark-set/delete, bookmarkp-autoname-bookmark(-function),
;;       bookmarkp-autonamed-bookmarks-alist-only, bookmarkp-autoname-format,
;;       bookmarkp-bookmark-autoname-p, bookmarkp-crosshairs-flag,
;;       bookmarkp-this-buffer-cycle-sort-comparer, bookmarkp-current-bookmark-list-state,
;;       bookmarkp-cycle-1, bookmarkp-list-position, bookmarkp-position-cp,
;;       bookmarkp-current-nav-bookmark, bookmarkp-cycle-this-buffer-buff, bookmarkp-nav-alist,
;;       bookmarkp-update-autonamed-bookmark, bookmarkp-delete-all-autonamed-for-this-buffer.
;;    Bound:
;;       bookmarkp-choose-navlist-from-bookmark-list, bookmark-insert-location,
;;       bookmarkp-navlist-bmenu-list, bookmarkp-choose-navlist-of-type, bookmarkp-delete-bookmarks,
;;       bookmarkp-toggle-autoname-bookmark-set/delete, bookmarkp-jump-in-navlist(-other-window),
;;       bookmarkp-(next|previous)-bookmark(-this-buffer)-repeat.
;;    bookmark--jump-via: Update the name and position of an autonamed bookmark.
;; 2010/05/22 dadams
;;     *-this-buffer-p: Return nil for bookmarks not really associated with a buffer.
;;     *-default-handler, *-goto-position: Forgot comma to eval file-name when no-such-file error.
;;     *-show-annotation: Bind buffer-read-only to nil for updating.
;; 2010/05/19 dadams
;;     Added: bookmarkp-this-buffer-bmenu-list.  Bound to `C-x p .'.
;;     menu-bar-bookmark-map:
;;       Added bookmarkp-this-buffer-bmenu-list.  Added separators.
;;       Added vanilla items edit, write, load, to impose order.  Renamed item edit.
;; 2010/05/16 dadams
;;     bookmark-set: Quoted history arg.  Thx to S. Nemec.
;;     bookmarkp-bmenu-define-full-snapshot-command: Use quote comma, not quote, for *-specific-*.
;; 2010/05/15 dadams
;;     Replace *same-(buffer|file)-jump* by *specific-(buffers|files)-jump*: read multiple buff/files.
;;     Renamed: *same-(buffer|file)* to *-last-specific-(buffer|file)* for pred, alist, and var.
;;     Renamed: *same-(buffer|file)* to *specific-(buffer|file)* for hist, *types*, mark/show cmds.
;;     Renamed: *-selected-buffers-alist* to *-specific-buffers-alist*.
;;     Added: *-specific-files-alist*, *-(all|some)-tags(-regexp)-alist-only.
;;     *-completing-read-(buffer|file)-name: Use (buffer|file)-name-history, not *-same-*-history.
;;     *-read-tags-completing: Rewrote to correctly handle cons and string tags, error handling, etc.
;;     *-bmenu-(add|remove)-tags-*-marked: Error handling.
;;     *(all|some)-tags(-regexp)-jump*: Use *-(all|some)-tags(-regexp)-alist-only.
;; 2010/05/11 dadams
;;     Added: bookmarkp-bmenu-mark-same-(buffer|file)-bookmarks, bookmarkp-this-(buffer|file)-p,
;;            bookmarkp-this-(buffer|file)-alist-only, bookmarkp-bmenu-show-only-same-(buffer|file),
;;            bookmarkp-completing-read-(buffer|file)-name, bookmarkp-same-(buffer|file)-history,
;;            bookmarkp-(same|this)-(buffer|file)-alist-only, bookmarkp-last-same-(buffer|file),
;;            bookmarkp-(same|this)-(buffer|file)-jump(-other-window), bookmarkp-(buffer|file)-names,
;;            bookmarkp-same-(buffer|file)-as-last-p, bookmarkp-other-window-pop-to-flag,
;;            bookmarkp-select-buffer-other-window.
;;     Use bookmarkp-select-buffer-other-window instead of switch-to-buffer-other-window everywhere.
;;     Bound = (b|f) (M|S), C-x j (=|.) (b|f) to (same|current)-(buffer|file) commands.
;;     *-types-alist: Handle same-(buffer|file) too.
;;     *-bmenu-list, *-bmenu-define-full-snapshot-command, *-save-menu-list-state:
;;       Handle bookmarkp-last-same-(buffer|file) as part of state.
;; 2010/05/05 dadams
;;     bookmarkp-create-varlist-bookmark, bookmarkp-make-varlist-record:
;;       Added optional arg BUFFER-NAME.
;;     bookmark-alist: Corrected doc string wrt BUFFER-NAME and region context strings.
;; 2010/05/04 dadams
;;     Added: bookmarkp-create-varlist-bookmark.
;;     bookmarkp-jump-varlist: If bookmark's buffer doesn't exist, use current buffer and show msg.
;; 2010/04/24 adams
;;     Added: bookmarkp-bmenu-show-only-varlists, bookmarkp-set-restrictions-bookmark,
;;            bookmarkp-set-varlist-bookmark, bookmarkp-varlist-jump, bookmarkp-varlist,
;;            bookmarkp-jump-varlist, bookmarkp-make-varlist-record, bookmarkp-printable-p,
;;            bookmarkp-printable-vars+vals, bookmarkp-read-variables-completing,
;;            bookmarkp-read-variable, bookmarkp-varlist-alist-only, bookmarkp-varlist-bookmark-p,
;;            bookmarkp-varlist-history.
;;     Bound bookmarkp-bmenu-show-only-varlists to V S, bookmarkp-varlist-jump to C-x j v (and menu).
;;     *-types-alist: Added bookmarkp-varlist-history.
;;     *-bmenu-mode-status-help, *-bmenu-propertize-item, *-describe-bookmark: Handle varlist bmks.
;;     *-bmenu-w32-open-select: Changed binding to M-v from V.
;;     *-bmenu-mode: Updated doc string.
;; 2010/04/17 dadams
;;     bookmark-set: Numeric prefix arg means use all bookmarks as completion candidates.
;;                   Simplified the prompt.
;;     bookmarkp-completing-read-1:
;;       Use icicle-transform-multi-completion in icicle-delete-candidate-object
;;     Ensure loaded before byte-compile (put a require after provide).
;;     Move bookmarkp-replace-regexp-in-string before macro bookmarkp-define-sort-command (uses it).
;;     bookmarkp-bmenu-w32-open-with-mouse, bookmarkp-bmenu-mouse-3-menu:
;;       Use with-current-buffer, not save-excursion of set-buffer.
;;     bookmarkp-make-dired-record, bookmarkp-jump-dired: Use dolist, not mapcar (just side effect).
;;     bookmarkp-(some|all)-tags-jump(-other-window): Removed extraneous arg in error call.
;; 2010/04/16 dadams
;;     Added: bookmarkp-completing-read-1, bookmarkp-completing-read-lax,
;;            bookmarkp-selected-buffers-alist-only.
;;     bookmark-set: Use bookmark-completing-read-lax w/ buffer's bookmarks, not read-from-minibuffer.
;;     bookmark-completing-read: Define using bookmarkp-completing-read-1.
;; 2010/04/09 dadams
;;     bookmarkp-edit-bookmark: Update dired-directory property along with filename property. 
;; 2010/03/28 dadams
;;     bookmarkp-goto-position: Don't funcall bookmarkp-jump-display-function if it is nil.
;; 2010/03/28 dadams
;;     bookmark-default-handler: Don't funcall bookmarkp-jump-display-function if it is nil.
;; 2010/03/27 dadams
;;     Changed the customization group from bookmarkp to bookmark-plus.
;;     Moved doc and change history from bookmark+.el to this new file, bookmark+-doc.el.
;;     bookmarkp-commentary-button: Use bookmark+-doc.el, not bookmark+.el.
;; 2010/03/17 dadams
;;     Added: bookmarkp-toggle-bookmark-set-refreshes, bookmarkp-refresh-latest-bookmark-list,
;;            bookmarkp-after-set-hook.
;; 2010/03/16 dadams
;;     Fixed parens placement (typo) for last change to define *-jump-woman for Emacs 20.
;; 2010/03/11 dadams
;;     Define bookmarkp-jump-woman also for Emacs 20 (just raise an error).
;;     *-show-annotation: Typo: bookmark -> bmk-name.
;; 2010/03/10 dadams
;;     Added: bookmarkp-bookmark-creation-cp, bookmarkp-bmenu-sort-by-creation-time (bind: s0, menu).
;;     *-make-record-default: Add entry: created.
;;     *-describe-bookmark: Add creation time to description.
;; 2010/03/03 dadams
;;     *-sort-and-remove-dups: Do not set bookmarkp-sorted-alist to the result.
;;     *-bmenu-list-1: Set bookmarkp-sorted-alist to the result of calling *-sort-and-remove-dups.
;; 2010/03/02 dadams
;;     Added: bookmarkp-sorted-alist.
;;     *-bmenu-list-1: Use bookmarkp-sorted-alist.
;;     *-sort-and-remove-dups: Set bookmarkp-sorted-alist to the result.
;;     All *-cp (and hence *-define-file-sort-predicate):
;;       Accept bookmark names as args, in addition to bookmarks.
;;     bookmark-alpha-p: Don't use bookmarkp-make-plain-predicate, to avoid infinite recursion.
;; 2010/02/28 dadams
;;     Added: bookmarkp-send-bug-report.
;;     bookmarkp-bmenu-mode-status-help: Rewrote to provide only Bookmark+ help.  Added help buttons.
;;     Fixed Commentary typos.
;; 2010/02/26 dadams
;;     Added: bookmarkp-desktop-change-dir, bookmarkp-desktop-kill, bookmarkp-desktop-delete.
;;     *-jump-desktop: Call *-desktop-change-dir.
;;     *-read-bookmark-for-type: Added optional arg ACTION.
;; 2010/02/24 dadams
;;     *-bmenu-list: Handle case null last-bookmark-file (due to old file format).  Thx to Seb Luque.
;;     *-make-record-default: protect dired-buffers with boundp.  Thx to Janek Schwarz.
;; 2010/02/16 dadams
;;     bookmarkp-define-sort-command: Add msg suffix about repeating.
;;     bookmarkp-msg-about-sort-order: Added optional arg SUFFIX-MSG.
;; 2010/02/15 dadams
;;     Added: bookmark-bmenu-switch-other-window (redefinition for Emacs 20-22).
;;     *-bmenu-mode: Added redefinition, instead of advising.
;;     *-send-edited-annotation, *-relocate, *-rename, *-bmenu-refresh-menu-list,
;;       *-remove(-all)-tags, *-add-tags:
;;         Refresh the menu list, to pick up changes.
;;     *-refresh-menu-list: Added optional arg BOOKMARK: go to it.
;;     Do not bind bookmark-bmenu-relocate unless it's defined.
;;     *-handler-cp: Respect case-fold-search.
;; 2010/02/14 dadams
;;     Renamed bookmark-bmenu-list-1 to bookmarkp-bmenu-list-1.
;;     Added faces: bookmarkp-(a|t|>|D)-mark, bookmarkp-heading (don't use bookmark-menu-heading).
;;     Added redefinitions: bookmark-send-edited-annotation, bookmark(-bmenu)-show-annotation,
;;                          bookmark-show-all-annotations.
;;     *-bmenu-mark, *-bmenu-delete, *-bmenu-list-1: Add faces to marks.
;;     *-bmenu-list-1 and everywhere: Get rid of "% " before menu-list title.
;;     *-bmenu-list-1: Use "a", not "*", as annotation mark.
;;                     Add "t" mark for tags.  Add an extra space before bookmark name.
;;     *-bmenu-marks-width: change value from 2 to 4, for the tags column and the extra space.
;; 2010/02/13 dadams
;;     Added: bookmarkp-desktop-history,
;;            bookmarkp-desktop-jump (bound to C-x j K; added to menu),
;;            bookmarkp-bookmark-list-jump (bound to C-x j B; added to menu),
;;            bookmarkp-bookmark-list-alist-only, bookmarkp-bookmark-list-history.
;;     *-types-alist: Added entries for desktops and bookmark-lists.
;;     *-describe-bookmark: Added optional arg, to show full (internal) info.
;;                          Bind it to ? in bookmark-map.
;;     *-jump-bookmark-list: Pop to the bookmark-list (to show it).
;;     *-bmenu-mark-w3m-bookmarks: Typo: wrong predicate.
;;     *(-bmenu)-remove-all-tags: Raise error if no tags to remove.
;;     *-bmenu-remove-all-tags: Require confirmation if interactive.
;;     *-bmenu-remove-tags: Added optional arg MSGP.
;;     Menus: Added "..." as needed.
;;     *-bmenu-mouse-3-menu: Guard bookmark-bmenu-relocate with fboundp.
;; 2010/02/12 dadams
;;     Added: bookmarkp-bmenu-define-jump-marked-command.  Bound to M-c and added to menu.
;;     Changed bookmarkp-toggle-saving-bookmark-file binding to M-~ (M-s conflicts w isearch-multi).
;;     Updated bookmark-bmenu-mode doc string.
;; 2010/02/11 dadams
;;     Added: bookmarkp-types-alist,
;;            bookmarkp-(dired|gnus|info|man|region|w3m|(non-|local-|remote-)file)-history.
;;     bookmark-completing-read: Added optional HIST arg.
;;     *-(relocate|rename|insert(-location)): Added bookmark default for interactive use.
;;     *-jump-dired: Handle bookmarkp-jump-display-function.
;;     *-read-bookmark-for-type: Added optional HIST arg.
;;     *-jump-to-type(-other-window),
;;       *-(dired|file|gnus|info|man|region|w3m|(local-|non-|remote-)file)-jump*(-other-window):
;;         Use type-specific history var.
;; 2010/02/09 dadams
;;     Added: bookmarkp-get-tag-value.
;;     bookmark--jump-via: Handle special bookmark tag bookmarkp-jump.
;; 2010/02/08 dadams
;;     Renamed: bookmarkp-bmenu-dired-marked-local to bookmarkp-bmenu-dired-marked.
;;     bookmarkp-bmenu-dired-marked: Handle remote bookmarks if Emacs > 23.1.
;;     Support tags with values.
;;       Added: bookmarkp-tag-name, bookmarkp-full-tag, bookmarkp(-bmenu)-set-tag-value.
;;       Renamed variable (not fn) bookmarkp-tags-list to bookmarkp-tags-alist.
;;       Use bookmarkp-full-tag everywhere for tag completion.
;;       *-has-tag-p: Use assoc-default, not member.
;;       *-read-tag(s)-completing: CANDIDATE-TAGS is now an alist.
;;       *-list-all-tags: Added optional arg FULLP (prefix arg).
;;       *-tags-list: Added optional arg NAMES-ONLY-P.
;;       *-(add|remove|rename)-tags: Use copy-alist, not copy-sequence.  Alist, not list, membership.
;;       *-rename-tag: Raise error if no tag with old name.
;;       *-bmenu-mark-bookmarks-tagged-regexp, *-regexp-filtered-tags-alist-only, *-describe-bookmark,
;;         *-(all|some)-tags-regexp-jump(-other-window):
;;           Use bookmarkp-tag-name.
;;       *-bmenu-mark/unmark-bookmarks-tagged-(all|some)/(none|not-all), *-define-tags-sort-command:
;;         Use assoc-default, not member.
;;     Added: bookmarkp-bmenu-add-tags, bookmarkp-bmenu-remove(-all)-tags.
;;     *-bmenu-mouse-3-menu: Use bookmarkp-bmenu-add-tags, bookmarkp-bmenu-remove(-all)-tags.
;;                           Added bookmarkp-bmenu-set-tag-value.
;;     *-bmenu-mark-bookmarks-satisfying: Made it a command (interactive).
;; 2010/02/07 dadams
;;     *-write-file: Corrected handling of ALT-MSG.
;;     Cleanup.
;;       *-remove-tags: Don't call *-get-tags twice.
;;       *-bmenu-(un)mark-bookmarks-tagged(-not)-(all|none|some):
;;         Don't duplicate what bookmarkp-read-tags-completing does.
;;       *-add-tags, *-remove-tags(-from-all): TAGS arg must be a list from the beginning.
;;       *-remove-tags-from-all, *-rename-tag: Use bookmark-all-names - don't mapcar car over alist.
;;       *-all-tags-regexp-jump: Corrected to use same pred as *-all-tags-regexp-jump-other-window.
;;       *-(some|all)-tags-jump(-other-window): Use bookmarkp-has-tag-p - don't repeat the definition.
;;       *-read-tag(s)-completing: Removed unnecessary or.
;; 2010/02/06 dadams
;;     *-write-file, *-empty-file: Corrected handling of ALT-MSG.
;; 2010/02/05 dadams
;;     Added: bookmarkp-same-file-p, bookmarkp-empty-file.
;;     Bound bookmarkp-empty-file to C-x p 0, and added it to menus.
;;     *-bmenu-list, *-switch-bookmark-file: Use bookmarkp-same-file-p.
;;     bookmark-write-file: Added optional ALT-MSG arg.
;; 2010/02/04 dadams
;;     Added: bookmarkp-bmenu-omit, bookmarkp-list-all-tags.  Added to mouse-3 menu, Tags menus.
;; 2010/02/01 dadams
;;     Added: bookmarkp-current-bookmark-file, bookmarkp-switch-bookmark-file,
;;            (redefinition of) bookmark-load, (redefinition of) bookmark-save,
;;            bookmarkp-toggle-saving-bookmark-file, bookmarkp-last-save-flag-value.
;;     *-bmenu-list: Restore bookmarkp-current-bookmark-file if appropriate.
;;     *-bmenu-mode-status-help: Show bookmarkp-current-bookmark-file.
;;     *-bmenu-define-full-snapshot-command, *-save-menu-list-state:
;;       Save bookmarkp-current-bookmark-file.
;;     Bound bookmarkp-switch-bookmark-file to L and C-x r L.  Added both load commands to both menus.
;;     *-toggle-saving-menu-list-state: Changed binding to M-l.  Error if init value is nil.
;;     Bound *-toggle-saving-bookmark-file to M-s and added to menu.
;;     Added bookmark-write to bookmarkp-bmenu-menubar-menu (Save As).
;;     bookmarkp-bmenu-menubar-menu: Added :help strings everywhere.
;;     bookmarkp-bmenu-mode-status-help: Added face legend.
;; 2010/01/31 dadams
;;     Added: bookmarkp-tags-list, bookmarkp-read-tag-completing, bookmarkp-use-w32-browser-p,
;;            bookmarkp-bmenu-w32-open(-select|-with-mouse).  Bind *-w32* to M-RET, V, M-mouse-2.
;;     *-default-handler: Call w32-browser if bookmarkp-use-w32-browser-p.
;;     *-bmenu-unomit-marked: Don't try to return to original position (duh).
;;     *-bmenu-goto-bookmark-named: Use eobp as loop condition.  Call bookmark-bmenu-ensure-position.
;;     *-read-tags-completing:
;;       Added arg UPDATE-TAGS-LIST-P.  Call bookmark-maybe-load-default-file.
;;       Use bookmarkp-tags-list if CANDIDATE-TAGS is nil.  Update that var if UPDATE-TAGS-LIST-P.
;;     *-(add|remove)-tags: Added arg NO-CACHE-UPDATE-P.  If nil, call bookmarkp-tags-list.
;;     *-remove-tags-from-all, *-rename-tag, *-bmenu-(add|remove)-tags-(to|from)-marked:
;;       Call bookmarkp-tags-list.
;;     *-remove-tags-from-all: Pass nil as tags arg to bookmarkp-read-tags-completing.
;;     *-rename-tag: Use bookmarkp-read-tag-completing, not read-string.
;; 2010/01/29 dadams
;;     bookmarkp-describe-bookmark: Handle desktop bookmarks specifically.
;;     Added: bookmarkp-menu-popup-max-length.
;;     bookmark-completing-read: Use bookmarkp-menu-popup-max-length.
;;     bookmarkp-bmenu-state-file: Added missing default value for const.
;;     Don't add jump-other entry to menu-bar-bookmark-map (just use Jump To submenu).
;; 2010/01/28 dadams
;;     bookmarkp-(all|some)-tags(-regexp)-jump(-other-window): Error if no bookmarks with the tags.
;;     bookmarkp-(all|some)-tags-jump(-other-window): Handle case where user enters no tags.
;;     Use :advertised-binding property for bookmark-jump(-other-window).
;;     Added: bookmarkp-bmenu-jump-menu.
;;     Added bookmarkp-bmenu-jump-menu to menu-bar-bookmark-map and bookmarkp-bmenu-menubar-menu.
;; 2010/01/27 dadams
;;     Added: bookmarkp-every, bookmarkp-(all|some)-tags(-regexp)-jump(-other-window).
;; 2010/01/26 dadams
;;     Added: bookmarkp-bmenu-dired-marked-local.  Bound to M-d >.
;; 2010/01/23 dadams
;;     Added: bookmarkp-handler-cp, bookmarkp-desktop-no-save-vars, bookmarkp-set-desktop-bookmark,
;;            bookmarkp-make-desktop-record, bookmarkp-jump-desktop, bookmarkp-desktop-read,
;;            bookmarkp-desktop-alist-only, bookmarkp-desktop-bookmark-p,
;;            bookmarkp-bmenu-mark-desktop-bookmarks, bookmarkp-bmenu-show-only-desktops,
;;            face bookmarkp-desktop.
;;     bookmarkp-bmenu-sort-by-bookmark-type: Add bookmarkp-handler-cp to the list (last).
;;     bookmarkp-bmenu-propertize-item: Add face bookmarkp-desktop for desktop bookmarks.
;;     Bound: bookmarkp-set-desktop-bookmark to C-x p K, C-x r K,
;;            bookmarkp-bmenu-mark-desktop-bookmarks to K M (and Mark menu),
;;            bookmarkp-bmenu-show-only-desktops to K S (and Show menu).
;;     bookmark-bmenu-mode doc string: Updated for new commands.
;;     Added autoload cookies for all defcustoms.
;; 2010/01/20 dadams
;;     Added: bookmarkp-bmenu-mode-status-help.  Bound to C-h m, ?.
;; 2010/01/19 dadams
;;     bookmarkp-remote-file-bookmark-p: Include remote Dired bookmarks.  Thx to Simon Harrison.
;;     Added: bookmarkp-describe-bookmark-internals, bookmarkp-bmenu-describe-this+move-(down|up),
;;            defalias for list-bookmarks.
;;     bookmarkp-describe-bookmark: Reformatted help output.  Added more info about Dired bookmarks.
;;     bookmarkp-bmenu-describe-this-bookmark:
;;       C-u calls bookmarkp-describe-bookmark-internals.  Bound also to C-h C-RET.
;; 2010/01/18 dadams
;;     Added: bookmarkp-dired-subdirs.
;;     bookmarkp-make-dired-record, bookmarkp-jump-dired: Handle inserted and hidden dirs.
;;     bookmarkp-jump-dired: Use expand-file-name, not concat.
;; 2010/01/17 dadams
;;     Added:
;;       bookmarkp-jump(-other-window)-map, bookmarkp-jump-1, bookmark-all-names (redefined),
;;       bookmarkp-read-bookmark-for-type, bookmarkp-dired-jump-current(-other-window),
;;       bookmarkp-(dired|(local-|remote-|non-)file|gnus|info|man|region|w3m)-jump(-other-window),
;;       bookmarkp-jump-to-type(-other-window).
;;     bookmark-jump(-other-window): Use bookmarkp-jump-1.
;;     bookmark-completing-read: Added optional args ALIST and PRED.
;;     bookmarkp-default-bookmark-name: Added optional arg ALIST.
;; 2010/01/14 dadams
;;     bookmark-bmenu-surreptitiously-rebuild-list: Put back save-excursion & save-window-excursion.
;; 2010/01/02 dadams
;;     Renamed *-bmenu-check-position to *-bmenu-ensure-position, per Emacs 23.2.  Added defalias.
;; 2010/01/01 dadams
;;     *-bmenu-(un)mark, *-bmenu-other-window, *-bmenu-rename: Call bookmark-bmenu-check-position.
;;     *-bmenu-delete: Don't call bookmark-bmenu-check-position again at end.
;;     *-bmenu-edit-bookmark: Call bookmark-bmenu-check-position at beginning, not end.
;; 2009/12/30 dadams
;;     Added: bookmarkp-bmenu-header-lines, bookmarkp-bmenu-marks-width.  Use everywhere.
;; 2009/12/29 dadams
;;     Added: bookmarkp-make-bookmark-list-record, bookmarkp-jump-bookmark-list, face
;;            bookmarkp-bookmark-list.
;;     *-bmenu-propertize-item: Highlight bookmark-list bookmarks.
;;     *-bmenu-refresh-menu-list: Set bookmarkp-latest-bookmark-alist to refreshed list.
;;     Face *-local-directory: Made dark background version the inverse of light.
;;     *-bmenu-list-1: Use eq, not equal, test for bookmarkp-omitted-alist-only as filter fn.
;;     *-bmenu-define(-full-snapshot)-command: Include bookmarkp-bmenu-omitted-list in saved state.
;; 2009/12/26 dadams
;;     Added: bookmarkp-bmenu-omitted-list, bookmarkp-bmenu-show-only-omitted, bookmarkp-unomit-all,
;;            bookmarkp-bmenu-omit/unomit-marked, bookmarkp-bmenu-(un-)omit-marked,
;;            bookmarkp-omitted-alist-only.
;;            Bind *-bmenu-omit/unomit-marked, *-bmenu-show-only-omitted, *-unomit-all to O>,OS,OU.
;;     Added omit/un-omit stuff to Bookmark+ menu.
;;     bookmarkp-remove-assoc-dups, bookmarkp-sort-and-remove-dups: Added optional arg OMIT.
;;     bookmark-delete: Update bookmarkp-bmenu-omitted-list.
;;     bookmarkp-save-menu-list-state, bookmark-bmenu-list:
;;       Save/restore bookmarkp-bmenu-omitted-list as part of state.
;;     bookmark-bmenu-list-1: Treat omitted list when bookmarkp-omitted-alist-only.
;;     bookmarkp-marked-bookmark-p: Arg can now be a bookmark (or a bookmark name).
;;     bookmarkp-bmenu-unmark-all: Start by going forward 2 lines, not 1, if user hit RET.
;;     bookmarkp-bmenu-make-sequence-from-marked:
;;       Added optional arg DONT-OMIT-P.  If nil, omit marked bookmarks.
;;       If the seq bookmark already exists, prompt to add to it or replace it.
;;       Go to the new bookmark in the menu list.
;; 2009/12/15 dadams
;;     Added: bookmarkp-sequence-jump-display-function, bookmarkp-sequence, bookmarkp-function,
;;            bookmarkp-bmenu-make-sequence-from-marked, bookmarkp-jump-sequence,
;;            bookmarkp-sequence-bookmark-p, bookmarkp-make-function-bookmark,
;;            bookmarkp-jump-function, bookmarkp-function-bookmark-p.
;;     bookmarkp-describe-bookmark: Update for sequence and function bookmarks.
;;     bookmark-bmenu-list: Use condition-case when read from bookmarkp-bmenu-state-file.
;;                          Bind emacs-lisp-mode-hook to nil.
;;     bookmark-bmenu-surreptitiously-rebuild-list: Use save-current-buffer.
;;     bookmarkp-bmenu-propertize-item: Add faces to function and sequence bookmarks.
;;     bookmarkp-bmenu-menubar-menu: Add *-make-sequence-*-from-marked, *-make-function-bookmark.
;;     bookmark--jump-via: Call *-record-visit with BATCH arg, to preserver point in menu list.
;;     bookmark-bmenu-list-1: fit-frame only if buffer is *Bookmark List*.
;; 2009/12/13 dadams
;;     *-alist-only: Call bookmark-maybe-load-default-file.
;; 2009/12/11 dadams
;;     Added: bookmarkp-list-defuns-in-commands-file, bookmarkp-remove-dups.
;; 2009/12/06 dadams
;;     Added: bookmarkp-bmenu-mouse-3-menu (bound to mouse-3),
;;            bookmarkp-bmenu-(menubar|define-command|sort|show|tags|mark)-menu. 
;;     bookmark-bmenu-delete: Remove newly flagged bookmark from bookmarkp-bookmark-marked-list.
;;     bookmarkp-define-tags-sort-command: Save macroexpanded definition in
;;                                         bookmarkp-bmenu-commands-file.
;; 2009/12/04 dadams
;;     Added: bookmarkp-bmenu-define-full-snapshot-command (bound to C),
;;            bookmarkp-define-tags-sort-command.
;;     bookmarkp-bmenu-mark-bookmarks-tagged-regexp: Removed extra forward-line if we mark line.
;; 2009/12/03 dadams
;;     Added: bookmarkp-bmenu-define-command (bound to c), bookmarkp-bmenu-commands-file.
;;     bookmark-bmenu-list: Read bookmarkp-bmenu-commands-file.
;;     bookmarkp-sort-and-remove-dups: Bug fix - return the list even when null sort function.
;; 2009/11/01 dadams
;;     Added: *-bmenu-check-position (redefinition), bmkext-jump-* defaliases.
;;     *-(w3m|man|gnus)-bookmark-p: Recognize the aliases.
;;     *-jump-man: Bind Man-notify-method.
;;     *-bmenu-goto-bookmark-named: Check the text property, instead of searching.
;;     *-bmenu-bookmark: Wrap in condition-case.
;; 2009/10/31 dadams
;;     Added: bookmark-bmenu-list-1. bookmarkp-toggle-saving-menu-list-state (C-t),
;;            bookmarkp-bmenu-state-file, bookmarkp-bmenu-first-time-p,
;;            bookmarkp-last-bmenu-(bookmark|state-file), bookmark-exit-hook-internal
;;            (redefinition), bookmarkp-save-menu-list-state.
;;     bookmark-bmenu-list: Restore menu-list state if appropriate.  Call bookmark-bmenu-list-1.
;;     bookmarkp-bmenu-quit: If *-bmenu-state-file is non-nil, save the state.
;;     bookmark-write-file: Use case, not cond.
;;     bookmark-set: Use command name as default for man-page bookmark name.
;;     bookmark-delete: Update bookmarkp-latest-bookmark-alist.
;; 2009/10/28 dadams
;;     Renamed: bookmarkp-bookmark-marked-p to bookmarkp-marked-bookmark-p
;;              bookmarkp-bmenu-sort-by-gnus-thread to bookmarkp-bmenu-sort-by-Gnus-thread.
;;     Added: bookmarkp-man, bookmarkp-make-(wo)man-record, bookmarkp-jump-(wo)man,
;;            bookmarkp-man-bookmark-p, bookmarkp-bmenu-mark-man-bookmarks,
;;            bookmarkp-bmenu-show-only-man-pages, bookmarkp-man-alist-only.
;;     *-bmenu-propertize-item: Handle (wo)man bookmarks.  Use bookmarkp-info-bookmark-p.
;;     *-regexp-filtered-*: Use bookmarkp-remove-if-not.
;;     *-write-file: Remove text properties from file name also.
;;     *-regexp-filtered-(tags|(bookmark|file)-name)-alist-only: Use *-remove-if-not.
;; 2009/10/26 dadams
;;     Added: bookmarkp-bmenu-mark-*-bookmarks, bmenu-mark-bookmarks-satisfying.
;;     Bound those and *-show-only-* accordingly.
;;     bookmarkp-file-alist-only: Redefined to just use *-file-bookmark-p.
;; 2009/10/25 dadams
;;     bookmarkp-bmenu-propertize-item: Put bookmark name on line as text property.
;;     bookmark-bmenu-bookmark: Get bookmark name from text property bookmarkp-bookmark-name.
;;     Removed: bookmarkp-latest-sorted-alist.
;;     bookmark-bmenu-list: Use bookmarkp-bmenu-title only if defined.
;; 2009/10/21 dadams
;;     Added: bookmarkp-barf-if-not-in-menu-list.  Use in place of its body.
;;     Added: bookmarkp-bmenu-mark-bookmarks-tagged-regexp.  Bound to T m %.
;;     Added: bookmarkp-record-visit.  Use in *--jump-via.  Replaces next two removals.
;;     Removed: bookmarkp-add-or-update-time, bookmarkp-increment-visits.
;;     Renamed: *-record-(end|front|rear)-context(-region)-string'.
;;              New names: bookmarkp-(end-)position-(pre|post)-context(-region).
;;     *-bmenu-describe-this-bookmark: Added *-barf-if-not-in-menu-list.
;;     *-bmenu-(un)mark-all, *-bmenu-regexp-mark, *-bmenu-toggle-marks:
;;       Removed with-current-buffer.
;; 2009/10/20 dadams
;;     Added: bookmarkp-bmenu-filter-function, bookmarkp-bmenu-title.
;;     Removed: bookmarkp-bmenu-called-from-inside-p.
;;     *-bmenu-list:
;;       Removed TITLE arg.  Get title from bookmarkp-bmenu-title or default.
;;       Use interactive-p and absence of menu list, not *-bmenu-called-from-inside-p, as the
;;         criterion for removing marks.  Fixes bugs such as bookmark creation removing marks.
;;     *-define-sort-command, *-bmenu-execute-deletions, *-increment-visits,
;;       *-add-or-update-time, *-bmenu-show-only-*, *-bmenu-show-all,
;;       *-bmenu-refresh-menu-list, *-bmenu-toggle-show-only-(un)marked,
;;       *-bmenu-filter-alist-by-regexp, *-bmenu-reverse(-multi-sort)-order,
;;       *-bmenu-change-sort-order:
;;         Do not bind or set *-called-from-inside-p.
;;     *-bmenu-show-only-*, *-bmenu-show-all, *-bmenu-filter-alist-by-regexp:
;;       Set *-bmenu-filter-function, *-bmenu-title.
;;     *-bmenu-show-all:
;;       Set *-latest-bookmark-alist to bookmark-alist.
;;     *-bmenu-refresh-menu-list: Fix so that it in fact refreshes.
;;       Do not use *-bmenu-surreptitiously-rebuild-list and *-bmenu-check-position.
;;       Bind bookmark-alist to last alist (filtered or not), and call *-bmenu-list.
;;     *-bmenu-surreptitiously-rebuild-list:
;;       Do not use save*-excursion.  Do not get current title and pass it to *-bmenu-list.
;;     *-file-alist-only:
;;       Removed optional arg.  We have *-local-file-alist-only for that.
;;     *-regexp-filtered-alist-only, *-bmenu-filter-alist-by-regexp:
;;       Remove REGEXP arg - use bookmarkp-bmenu-filter-pattern.
;;     *-bmenu-filter-incrementally:
;;       Raise error if not in *Bookmark List*.
;;       Use just bookmarkp-bmenu-filter-alist-by-regexp in timer - pass no regexp arg.
;;     Added: bookmarkp-some, *-bmenu-filter-(file-name|tags)-incrementally,
;;            *-bmenu-filter-alist-by-(file-name|tags)-regexp,
;;            *-regexp-filtered-(file-name|tags)-alist-only.
;;     Renamed: *-bmenu-filter-incrementally to *-bmenu-filter-bookmark-name-incrementally,
;;              *-bmenu-filter-alist-by-regexp to *-bmenu-filter-alist-by-bookmark-name-regexp,
;;              *-regexp-filtered-alist-only to *-regexp-filtered-bookmark-name-alist-only.
;;     Bound these commands to P B, P F, and P T.  Updated bookmark-bmenu-mode doc string.
;; 2009/10/18 dadams
;;     Added: *-bmenu-filter-(incrementally|delay|prompt|pattern|timer|alist-by-regexp),
;;            *-bmenu-read-filter-input, *-regexp-filtered-alist-only,
;;            *-bmenu-cancel-incremental-filtering.
;;     *-bmenu-execute-deletions: Don't update menu list if this is a no-op.
;;     Updated Commentary.
;;     Thx to Thierry Volpiatto.
;;     Added: *-marked-cp, *-bmenu-sort-marked-before-unmarked.  Bound to s >.
;;     *-define-sort-command: Use copy-sequence for default value.
;; 2009/10/17 dadams
;;     Added: *-read-tags-completing, *-set-union, *-tag-history, *-describe-bookmark,
;;            *-bmenu-describe-this-bookmark.  Bound *-bmenu-describe-this-bookmark to C-h RET.
;;     Use *-read-tags-completing instead of *-read-tags.
;;     *-sort-orders-for-cycling-alist: Use copy-sequence.
;;     *-bmenu-change-sort-order: Use member, not memq.
;;     *-get-bookmark: Handle case of non-string, non-cons. Document NOERROR in doc string.
;;     *-bmenu-execute-deletions: Fix so marks aren't removed if when delete.  Thx to Thierry.
;;     Convert recorded time to an Emacs time spec:
;;       *-make-record-default, -add-or-update-time: Use current-time, not bookmark-float-time.
;;       *-get-visit-time: Convert a deprecated time entry to an Emacs time spec.
;;       *-bookmark-last-access-cp: Convert recorded time to a number for comparison.
;;     Added: *-bmenu-show-filenames (redef of vanilla: put props on whole line, fit frame).
;;     Removed: old-bookmark-insert-location.
;;     *-insert-location: Do not call original.  Redefined: do not add text properties.
;;     *-bmenu-list, *-bmenu-hide-filenames: Put properties on line up to max width.
;;     *-bmenu-goto-bookmark-named: Allow trailing whitespace, since we use the whole line now.
;;     *-bmenu-list: Use pop-to-buffer, not switch-to-buffer.  Use do-list, not mapcar.
;;     *-bmenu-hide-filenames: fit-frame-if-one-window.
;;     *-bmenu-propertize-item: Better help-echo text.
;;     Updated bookmark-alist doc string to mention visits, time, and tags entries.
;; 2009/10/16 dadams
;;     Added tags feature.
;;       Added: *-(get|read)-tags, *-has-tag-p, *-remove(-all)-tags(-from-all),
;;              *-bmenu-remove-tags-from-marked, *-add-tags(-to-marked), *-rename-tag,
;;              *-bmenu-(un)mark-bookmarks-tagged-(all|none|some|not-all),
;;              *-bmenu-mark/unmark-bookmarks-tagged-(all/none|some/not-all).
;;       Bound to prefix key T.
;;       *-bmenu-mode: Updated doc string.
;;     Added: bookmarkp-default-bookmark-name.  Use as default instead of *-current-bookmark.
;;     Renamed: *-maybe-save-bookmark to *-maybe-save-bookmarks.
;;     Menu-list commands: Raise an error if command is used outside the menu list.
;; 2009/10/15 dadams
;;     Added: *-bmenu-(search|query-replace)-marked-bookmarks-regexp.  Bound to M-a, M-q.
;;     Renamed: *-non-marked-bookmarks-only to *-unmarked-bookmarks-only,
;;              *-bookmark-marked-alist to *-bmenu-marked-bookmarks.
;;     *-increment-visits, *-add-or-update-time:
;;       Set *-bmenu-called-from-inside-p to t, so we don't remove marks.
;;     Redefined *-bmenu-bookmark to get name from *-latest-sorted-alist.  Thx to Thierry V.
;;       *-bmenu-surreptitiously-rebuild-list, *-bmenu-list:
;;         Removed optional arg DONT-TOGGLE-FILENAMES-P.
;;       *-bmenu-execute-deletions, *-bmenu-toggle-show-only-(un)marked, *-bmenu-(un)mark-all,
;;         *-bmenu-regexp-mark, *-bmenu-toggle-marks:
;;           Do not bother with *-bmenu-toggle-filenames and rebuilding the menu list.
;; 2009/10/14 dadams
;;     Added: *-bmenu-delete (redefinition), *-isearch-bookmarks,
;;            *-bmenu-isearch(-marked)-bookmarks(-regexp), *-isearch-next-bookmark-buffer.
;;            Bound multi-isearch commands to M-s a C(-M)-s.
;; 2009/10/13 dadams
;;     Added: *-make-dired-record, *-jump-dired, *-dired-bookmark-p, *-dired-alist-only,
;;            *-bmenu-show-only-dired.  Bound *-bmenu-show-only-dired to M-d.
;;     bookmarkp-file-bookmark-p: Include bookmarks that have the Dired handler.
;;     Moved *-sort-orders-for-cycling-alist defcustoms after *-define-sort-command calls.
;;     Call bookmarkp-msg-about-sort-order only when interactive.
;;     *-add-or-update-time, *-increment-visits: Do not save each time we access a bookmark.
;;     Updated doc string of bookmark-alist and Commentary.
;; 2009/10/09 dadams
;;     Added: bookmarkp-bmenu-delete-marked.  Bound it to D.
;;            bookmarkp-sort-orders-for-cycling-alist.
;;     Renamed: bookmarkp-sort-functions-alist to bookmarkp-sort-orders-alist,
;;              bookmarkp-sort-function to bookmarkp-sort-comparer.
;;     bookmark-bmenu-execute-deletions: Added optional arg, for *-bmenu-delete-marked.
;;     *-sort-function: Changed default value to sorting by bookmark type (`s k').
;;     *-bmenu-change-sort-order: Use *-sort-orders-for-cycling-alist, not all sort orders.
;;     Updated Commentary and doc string (bookmark-bmenu-mode).
;; 2009/10/08 dadams
;;     Added: *-bmenu-sort-by-(w3m-url|gnus-thread), *-(gnus|w3m)-cp, *-cp-not,
;;            *-local-file-(accessed|updated)-more-recently-cp, *-bmenu-sort-by-bookmark-type.
;;     Renamed: *-bmenu-sort-by(-last)-file-(size|type|access|update) to
;;              *-bmenu-sort-by(-last)-local-file-(size|typeaccess|update),
;;              *-file-visited-more-recently-cp to *-local-file-accessed-more-recently-cp,
;;              *-file-(size|type)-cp to *-local-file-(size|type)-cp.
;;     Removed: *-file-(device|gid(-chg)|inode|last-(access|update|status-change)|links|modes
;;                            |uid)-cp.
;;     Bound *-bmenu-sort-by-bookmark-type to `s k'.
;;     *-define-file-sort-predicate: Use *-file-bookmark-p, not *-local-file-bookmark-p.
;;     *-msg-about-sort-order: Added optional arg PREFIX-ARG.  Use in: *-show-(all|only-*).
;; 2009/10/07 dadams
;;     Renamed: *-bmenu-sort-by-last-visit-time to *-bmenu-sort-by-last-bookmark-access,
;;              *-bmenu-sort-by-visit-frequency to *-bmenu-sort-by-bookmark-visit-frequency,
;;              *-visited-more-recently-cp to *-bookmark-last-access-cp.
;; 2009/10/06 dadams
;;     Added: bookmarkp-msg-about-sort-order.
;;     bookmark-completing-read: Simple sort when use menu-bar menu.
;; 2009/10/05 dadams
;;     Added: *-make-plain-predicate, *-reverse-multi-sort-order, *-multi-sort,
;;            *-define-file-sort-predicate, *-bmenu-sort-by-file-*, *-file-attribute-*-cp,
;;            and aliases *-file-*-cp, *-current-sort-order.
;;     Redefined sorting to allow multi-predicates:
;;       Redefined: *-sort-function, *-sort-and-remove-dups, *-define-sort-command,
;;                  *-sort-functions-alist.
;;     Bound keys with `s f' prefix to file-sorting commands
;;     *-current-sort-order: Use rassoc instead of rassq now.
;;     Swap keys s and S.  S is now bookmark-bmenu-save.  s is not the sorting prefix key.
;;     bookmark-bmenu-mode: Mention S key explicitly here (even though it is also
;;                          mentioned in the vanilla part of the doc string).
;; 2009/10/04 dadams
;;     *-bmenu-change-sort-order-repeat: Require repeat.el.
;;     Renamed: bookmarkp-current-sec-time to bookmarkp-float-time.
;;     *-float-time: Added arg, so it's the same as float-time (for Emacs 20).
;;     Bind *-reverse-sort-order to `S R'.
;;     *-remote-file-bookmark-p: Removed extra rem-file in last and.
;;     *-non-file-bookmark-p: Ensure it's not a remote file, before calling file-exists-p.
;; 2009/10/03 dadams
;;     Added: bookmarkp-file-remote-p, bookmarkp-buffer (face).
;;     bookmarkp-non-file (face): Changed to gray.
;;     *-default-handler, *-bmenu-propertize-item, *-(info|file)-bookmark-p:
;;       Support Emacs 20-21 Info-node bookmarks.
;;     bookmarkp-bmenu-propertize-item: Use different face for existing buffers.
;;                                      Use bookmarkp-non-file-filename.
;;     bookmarkp-non-file-bookmark-p: Include buffer bookmarks for nonexistent buffers.
;;     bookmarkp-remote-file-bookmark-p: Use bookmarkp-file-remote-p.
;;     bookmark-handle-bookmark:
;;       Redefine for all Emacs versions.  Handle buffer (non-file) bookmarks.
;;     Reordered some function definitions.
;; 2009/10/02 dadams
;;     Added: bookmarkp-bmenu-goto-bookmark-named, bookmarkp-latest-sorted-alist.
;;     *-sort-and-remove-dups: Set *-latest-sorted-alist (not used yet).
;;     *-define-sort-command, *-bmenu-change-sort-order, *-reverse-sort-order:
;;       Bind *-bmenu-called-from-inside-p to t, to prevent losing marks.
;;       Restore cursor position to same bookmark after sorting - use *-goto-bookmark-named.
;;     *-bmenu-surreptitiously-rebuild-list, *-bmenu-list: Added arg DONT-TOGGLE-FILENAMES-P.
;;     *-bmenu-execute-deletions, *-bmenu-toggle-show-only-(un)marked:
;;       Call *-surreptitiously-* with arg DONT-TOGGLE-FILENAMES-P.
;;     *-bmenu-hide-filenames: Simplify - don't get to position by searching backward.
;;     *-handle-region-default: Use forward-line, not goto-line.
;;     Thx to Thierry V.
;; 2009/10/01 dadams
;;     Added: bookmarkp-some-unmarked-p.
;;     Renamed: *-bmenu-toggle-show-only-<TYPE> to *-bmenu-show-only-<TYPE>,
;;              *-bmenu-called-from-inside-flag to *-bmenu-called-from-inside-p.
;;     bookmarkp-some-marked-p: Do not test bookmarkp-bookmark-marked-alist.
;;                              Arg must be required (explicit).  Changed calls accordingly.
;;     bookmark-bmenu-mode: Cleaned up doc string.
;;     bookmark-bmenu-((un)mark|rename|edit-*|toggle-marks|surreptitiously-rebuild-list),
;;       bookmarkp-root-or-sudo-logged-p, bookmarkp-jump-w3m-(new-session|only-one-tab),
;;       bookmarkp-some-marked-p:
;;         Inline let vars used only once.
;;     bookmarkp-bmenu-toggle-show-only-marked:
;;       Test bookmarkp-some-unmarked-p, not bookmarkp-some-marked-p,
;;            and include *-before-hide-unmarked in the test.
;;     bookmarkp-bmenu(-toggle)-show-only-*: Display status message.
;;     bookmarkp-bmenu-toggle-show-only-(un)marked: Fit frame.
;;     bookmark-prop-set: Fixed, so it handles old bookmark format also.
;; 2009/10/01 Thierry Volpiatto
;;     Removed: bookmarkp-bmenu-restore-marks.
;;     bookmark-bmenu-list:
;;       Do the mark restoration in line, at the same time as the annotation * restoration.
;;       Simplify use of START and END.
;; 2009/09/30 dadams
;;     bookmarkp-bmenu-regexp-mark: Remove binding of bookmark-alist.
;;     bookmark-bmenu-(un)mark, bookmarkp-bmenu-edit-bookmark (remove first call only),
;;       bookmark-bmenu-other-window, bookmark-bmenu-rename, bookmarkp-bmenu-restore-marks:
;;         Remove bookmark-bmenu-check-position (done by bookmark-bmenu-bookmark anyway).
;;     bookmark-insert-location: Fix interactive spec for Emacs < 22.
;;     bookmark-location: Return "" instead of raising error, if no location found.
;;     bookmarkp-current-sec-time: Move the let: do not call current-time unless we need to.
;;     bookmarkp-bmenu-unmark-all: forward-line only 1, not 2.  Thx to Thierry.
;;     bookmark-bmenu-mode: Updated doc string - bindings and mention options.
;;     bookmarkp-bmenu-propertize-item: For buffer, check also against "   - no file -".
;; 2009/09/29 dadams
;;     bookmark-bmenu-unmark: Use delete, not remove.
;;     Removed: bookmark-bmenu-check-position, bookmarkp-maybe-sort.
;;     Added: bookmarkp-sort-and-remove-dups, bookmarkp-remove-assoc-dups,
;;            bookmarkp-face-prop, bookmarkp-bad-bookmark, bookmark-menu-heading (Emacs 20,21),
;;            bookmark-bmenu-bookmark (redefinition).
;;     *-bmenu-toggle-show-only-*: Do not call-interactively.
;;     bookmarkp-bmenu-(un)mark-all:
;;       Handle bookmark-bmenu-toggle-filenames (wrapper).
;;       Remove bookmark-bmenu-check-position - just ensure within menu list.
;;     bookmarkp-bmenu-mark-all: Move save-excursion so it applies to all movements.
;;                               Message stating number marked.
;;     bookmarkp-bmenu-unmark-all: Use with-current-buffer ensure in menu list.
;;                                 Use bookmark-bmenu-unmark.
;;     Fixed U bindings for bookmarkp-bmenu-unmark-all.
;;     bookmarkp-bmenu-regexp-mark:
;;       Remove bookmark-bmenu-check-position - just ensure in menu list.
;;     bookmarkp-bmenu-toggle-marks: Use forward-line 2, to ensure in menu list.
;;                                   Message stating number marked.
;;     bookmark-bmenu-list, bookmarkp-bmenu-propertize-item: Use bookmarkp-face-prop.
;;     bookmark-bmenu-list: Don't start applying the faces until column 2.
;;     Removed key bindings in bookmark-map for *-toggle-show-only-*.
;;     Redefined faces, esp. for a light background.
;;     Use font-lock-face or face property, depending on Emacs version.
;;
;; 2009-06-09 to 2009-09-27 Thierry Volpiatto and dadams
;;     New features, as follows.
;;       See also the change log at
;;         http://mercurial.intuxication.org/hg/bookmark-icicle-region/.
;;       2090-09-27 Rewrote sorting and unmarking code.  (+ Updates to doc, names.)
;;                    Unmarking is now like Dired & query-replace.
;;                    Sorting is via one sort function; sort predicates do all the sorting.
;;                    Can now cycle sort orders with S S S...
;;                    Sort cmds now cycle among normal, reverse, off.
;;                    Add: *-define-sort-command (macro), *-assoc-delete-all, *-upcase,
;;                         *-get-visits-count, *-get-visit-time, *-sort-functions-alist.
;;                  Remove docstring from defalias (for Emacs 20).
;;       2009-09-26 Fix *-bmenu-mode doc (defadvice).
;;       2009-09-25 *-bmenu-edit, *-bmenu-sort-1: Fix bmk retrieval code.
;;                  Redefine *-bmenu-unmark.  Add: *-bmenu-toggle-marks.
;;                  Bind *-bmenu-unmark-all-bookmarks to M-DEL.  Reorder code.
;;                  Rename: *-bmenu-unmark-all-(bookmarks|(delete|mark)-flag)',
;;                          *-bmenu-unmark-all-bookmarks-1.
;;                  Change sort predicates in defalias.  Rename bmk entry visit to visits.
;;                  Remove: *-bmenu-show-number-of-visit.
;;       2009-09-22 Rewrote sorting code.  Renamed unmarking fns.
;;       2009-09-21 Rename mark/unmark cmds to have -bmenu.
;;                  Add: *-bmenu-called-from-inside-flag - set it in (un)hide marks fns.
;;       2009-09-20 *-write-file: Remove text properties before saving.
;;                  Remove all marks only in current display.
;;       2009-09-19 *-current-sec-time: Protect with fboundp for Emacs 20.
;;                  *-bmenu-sort-1: Add msg showing sort method.
;;                  Change key S-A to S-S (A is annotations).
;;       2009-09-18 Improve sorting by visit frequency.  Always increment when jump.
;;                  Fix increment visit fn.  Allow sorting by last visited.
;;                  When visit values are equal, sort with string-lessp.
;;                  Add TIME bookmark-alist entry.  *-make-record-default: Add time entry.
;;                  Fix: bad parens, errors in sorting predicate.  Rename fns.  
;;                  Use single fn to sort using diff methods.
;;                  Add: *-bmenu-refresh-alist (bind to g).
;;       2009-09-16 Add: *-toggle-sorting-by-most-visited, *-reset-visit-flag,
;;                       *-bmenu-show-number-of-visit.
;;                  Redefine *-prop-set.  Improve *-toggle-sorting-by-most-visited.
;;                  Add auto-doc to header.  *-bmenu-mode: Add missing key.
;;                  Update menu-list after jumping.
;;                  Increment save counter when jump with visit flag.
;;       2009-09-15 Record number of visits.  Added sorting by most visits.
;;       2009-09-14 Add doc string.  Update defadvice doc string wrt keys.
;;       2009-09-12 Add: fns to mark all, unmark D or > or all, *-bmenu-reset-alist.
;;                  Fix keymap (Emacs 20).  *-unmark-all-bookmarks1: Move the save-excursion.
;;       2009-09-11 Add: *-bmenu-check-position (redef to improve performance),
;;                       *-unmark-all-bookmarks, *-current-list-have-marked-p,
;;                       *-bookmark-marked-p, *-(non-)marked-bookmarks-only.
;;                  *-bmenu-hide-unmarked: Add toggling.  Restore lost fn.
;;                  Reorder code.  Bind cmds in *-bmenu-mode-map.
;;                  *-bmenu-hide-marked: Do not hide if no marked in current filter.
;;                  Improve: *-bmenu-hide(-not)-marked-bookmark, (un)hide marked fns.
;;       2009-09-10 Fix *--restore-all-mark, *-bmenu-regexp-mark.
;;                  *-bmenu-list: Add *-restore-all-mark.
;;                  *-bmenu-mark: Push marked bmk to marked list.
;;                  Add: bookmarkp-bookmark-marked-list, *-bmenu-quit.
;;       2009-09-09 *-maybe-sort-alist: Use copy-sequence.
;;                  So remove fixes for *-rename, *-edit-bookmark.
;;                  *-yank, *-rename', *-set: Fix yanking.
;;                  Remove non-file bmks from file-only list.
;;                  Add: *-bmenu-list-only-non-file-bookmarks, *-maybe-message (Emacs 20),
;;                       *-bmenu-mark-bookmark-matching-regexp, *-bmenu-hide-marked-bookmark,
;;                       *-bmenu-hide-not-marked-bookmark, *-bmenu-mark (redefinition).
;;                  *-write-file: Improve performance.
;;                  *-non-file-alist-only: Remove unused def.
;;                  Fix: hide marked/unmarked with toggle-filenames, keymap for Emacs 20.
;;                  Improve comments, doc strings.
;;                  *-bmenu-mark-bookmark-matching-regexp: Fix while loop.
;;       2009-09-08 bookmark-store: Remove duplicate setq of *-current-bookmark.
;;       2009-09-07 Reorganize (reorder), add comments, improve doc strings.
;;                  Change binding of *-bmenu-relocate from R to M-r.
;;       2009-09-06 bookmark-rename: Redefine with new arg BATCH.
;;                  *-bmenu-rename: Go to new pos, not old.
;;                  *-edit-bookmark, bookmark-rename: Fix display update for Emacs 20.
;;       2009-09-05 Add: *-edit-bookmark, *-bmenu-edit-bookmark, *-maybe-save-bookmark.
;;       2009-09-04 Require cl.  Allow RET in Emacs 20.  Add doc string.
;;                  *-fix-bookmark-alist-and-save:
;;       2009-09-03 Fix *-fix-bookmark-alist-and-save:
;;                    Use error, not message.  Change value for setcdr.
;;                    Do not use push with non-var (cl).
;;                  bookmark-delete:
;;                    Redefine, to fix vanilla bug: increment count even when batch.
;;                  *-non-file-name: Change to - no file -.  *-bmenu-list: Add arg FILTER-ON.
;;                  *-bmenu-execute-deletions: Use delete, not remove.
;;                  Add: *-replace-regexp-in-string.
;;                  bookmark-set: Fix *-yank-point for region case.  Fix bad parens.
;;       2009-09-02 Add: *-non-file-filename.  *-fix-bookmark-alist-and-save: Fix msg.
;;                  Require cl (gensym).  *-at-bol/eol' -> line-*-position (for Emacs 20).
;;                  bookmark-delete: increment *-count if batch arg (fixes vanilla bug).
;;                  Redefine *-bmenu-execute-deletions,
;;                           *-bmenu-surreptitiously-rebuild-list. 
;;                  Update current filtered display - do not reload & display all bmks.
;;                  Add redefinitions of *-bmenu-rename', *-yank-word to fix vanilla bugs:
;;                    *-bmenu-rename: Do not call *-bmenu-list twice.
;;                  *-yank-word: Do not insert whitespace.
;;                  Rename *-last-bookmark-alist-in-use to *-latest-bookmark-alist.
;;       2009-09-01 Fix: Loading of new doc for bookmark-alist (add vacuous defvar).
;;                       *-bmenu-(list|hide-filenames): start -> end, end -> start.
;;                  Removed extraneous quote mark that caused problems.
;;                  Save only if condition-case exits OK.
;;       2009-08-31 Fixes: Test for non-file bmk.  Filename for Gnus bmks.
;;                         Compatibility of bookmark-alist with vanilla Emacs.
;;                         Require info.el and ffap.el when needed.
;;                  Add: *-line-number-at-pos (for Emacs 20),
;;                       *-bmenu-other-window (redefinition).
;;                  Rename *-propertize-bookmark-list to *-propertize-bmenu-item.
;;       2009-08-30 Fix: Increment *-alist-modification-count when relocate region,
;;                       and maybe save.
;;                  Move code adding properties to bookmarks out of *-bmenu-list.
;;                  mapc -> mapcar.  *-bmenu-hide-filenames: Redefine.
;;       2009-08-29 Remove refresh code.
;;       2009-08-27 Added: *-local-directory-bookmark-p, *-local-file-alist-only,
;;                         *-non-file-alist-only.
;;                  *-file-bookmark-p: Redefined to exclude bmks with handlers.
;;                  Renamed fns and faces.
;;       2009-08-25 Fit frame after display menu list.
;;                  Refresh list when toggle filename visibility.
;;       2009-08-24 Fix: *-bmenu-list for remote files, bookmark-set, *-remote-file-bookmark-p.
;;                  Ensure arg to file-remote-p is not nil.
;;                  Recenter region only if it is visible.
;;       2009-08-23 Remove old *-location.  *-bmenu-list: Add isw3m.
;;                  bookmark-set:
;;                    Redefine for older Emacs. Use a default prompt for gnus, w3m.
;;                    Use *-name-length-max for title when region is active.
;;                    Ensure bookmark is on one line.
;;       2009-08-22 Try to handle tramp ftp files.
;;                  Do not fail if bookmark has empty filename entry.
;;                  Show region end pos using exchange-point-and-mark.
;;       2009-08-21 Remove all cl stuff (list*, loop, etc.).  Add *-remove-if(-not).
;;                  Remove compile-time require of cl.
;;                  Add predicates *-(region|gnus|w3m|info|(remote-|local-)file)-bookmark-p.
;;                  Redefine alist-only functions to optimize and use new preds.
;;       2009-08-20 *--jump-via: Fix to show relocated region before ask whether to save.
;;                  *-relocate-region: Fix ar-str.  Rename a var.  Add: *-region-activated-p.
;;                  Revert chgs.
;;       2009-08-19 Update/fix commentary: bookmark-alist, linkd.
;;                  *-default-handler, *-handle-region-default:
;;                    Get bmk record from name only once.
;;                  *-save-new-region-location: Move t inside progn.
;;       2009-08-16 Use prefix bookmarkp where appropriate.
;;       2009-08-15 Improve comments, doc strings.  Rename fns, vars.
;;                  Add :group with prefix bookmarkp.
;;       2009-08-09 Fix doc strings.
;;       2009-08-08 bookmark-set: Update doc string.  Show keys in C-h m.
;;       2009-08-07 *-jump: Fix to jump in same window (thx to Henry Atting).
;;                  *-at-bol/eol' -> line-*-position.
;;       2009-08-01 bookmark-store: Fix for Emacs 20.
;;       2009-07-27 Ensure we start on an empty w3m buffer.  Add: *-w3m-allow-multi-tabs.
;;       2009-07-24 *-bmenu-mode-map: Define some new keys.
;;       2009-07-23 *-bmenu-list: Add path to file in help-echo.
;;       2009-07-19 Fix title underline.  Highlight bookmark if root logged with tramp.
;;                  Add face for sudo.
;;       2009-07-18 Add: filter functions, option for bookmark-bmenu-list.
;;                  Remove toggle region.
;;                  *-bmenu-list-only-files-entries: Add prefix arg to show remote.
;;       2009-07-14 Add a forgotten test.
;;       2009-07-13 Fix errors.  Give pos in msg even if no search.
;;                  *-from-bob/eob: Fixed like old strict.
;;                  Remove *-relocate-region-(method|from-limits).
;;                  Remove unused code in record fns.  Add: *-relocate-region-function.
;;       2009-07-12 Do not pass args to relocation routines.  Remove use of flet.
;;                  Use skip-chars-*ward.  Use forward-line, not beginning-of-line.
;;                  Remove save-excursion around message.  Correct typo f(ree var BMK).
;;       2009-07-11 Fix *-relocate-region-strict.  Rename fns, adjust defcustom.
;;                  Save relocated region after pushing mark.  Add comments.
;;       2009-07-10 New retrieve fn.  Add looking-* fns.
;;       2009-07-08 Simplify record fns.  Add doc strings.  Add: *-save-relocated-position.
;;                  Fix: updating when relocate (wrt new record fns), string closing,
;;                       free vars, parens, names.
;;       2009-07-06 Fix: *-bmenu-list wrt windows, Info colors.
;;       2009-07-04 Rename fns to record, vars, args of retrieve fns.  Big changes, fixes.
;;       2009-07-01 Fix comments.  *-retrieve-region-strict: improve when out of context.
;;       2009-06-30 Fix: free vars, *-retrieve-region, provide (name).
;;       2009-06-29 Fix: w3m handler, file name for non-file, *-simple-retrieve-position.
;;                  Add: *-retrieve-region-strict.
;;       2009-06-28 Add: *-retrieve-region-method-is, *-retrieve-region-lax,
;;                       fns to retrieve regions.
;;                  Use buffer again, not buffer-name.
;;       2009-06-27 Fix wrong-type error no such file.  Renamed faces.  Add: *-prop-set.
;;                  Load gnus at compile time.  Protect tramp-file-name-regexp with boundp.
;;       2009-06-25 Fixes for older Emacs compatibility.
;;       2009-06-24 Improve *-default-handler.
;;                  Add: *-always-save-relocated-position, *-prop-get.
;;       2009-06-23 Use search-regexp, not re-search-regexp.  Add Gnus bmks.  Add doc.
;;                  Fix *-bmenu-list.
;;       2009-06-21 Fix: *-default-handler for Info.  Improve doc strings, commentary.
;;                  Fixes to be compatible with Emacs 20-22.
;;                  Use defcustom for *-list-only-regions-flag.
;;                  *jump: Put prefix arg in interactive spec.  Use buffer-name, not buffer.
;;                  Remove require of Tramp and inline Tramp fns.
;;                  Remove tests for display-(color|mouse)-p.
;;                  w3m-bookmark-(jump|make-record): require w3m.
;;       2009-06-20 Update context strings when relocate.
;;                  Fix: bookmark-get-*: search from point-min.
;;       2009-06-19 Fix: *-make-record-default, *-toggle-use-only-regions, *-default-handler,
;;                       bookmarking Dired.
;;                  Handle 4 positions in *-default-handler.
;;       2009-06-17 Fix: case where some bookmarked text was removed, *-use-region.
;;       2009-06-15 Fix *-region-alist-only, *-get-buffername, *-location,
;;                      non-file (buffer) bookmarks.
;;                  Support w3m similar to Info.
;;       2009-06-14 Fix bookmark+version, region relocation.  Info support.  Error handling.
;;       2009-06-13 Fix: *-list-only-regions, *-region-handler, *-make-record, keymap, faces.
;;                  Put region & info handling in *-default-handler, not separate handlers.
;;                  Merge *-make-record-region to *-make-record-default.
;;                  *-jump now negates *-use-region if prefix arg.  Raise error if bad bmk.
;;       2009-06-12 Add: *-get-endposition, *-region-alist-only-names.
;;                  Add filter to show only region bookmarks.
;;                  Faces for menu list.  Change region color.
;;       2009-06-11 Add: *-region-search-size, *-get-buffername, *-use-region.
;;                  Redefine *-handle-bookmark, *-jump, to fit bookmark-use-region.
;;                  Add condtions to bookmark-make-record.  Support w3m.  Support t command.
;;       2009-06-10 Fix search regexp.  Fix region in Info. Save bookmark if region moves.
;;       2009-06-09 Added: bookmark-make-record(-region), bookmark-region-handler.
;;                  Relocation.
;; 2009/05/25 dadams
;;     Added redefinition of bookmark-get-bookmark-record.
;; 2008/10/16 dadams
;;     bookmark-jump-other-window: Don't define it for Emacs 23+ (not needed).
;; 2008/04/04 dadams
;;     bookmark-jump-other-window: Updated wrt Emacs 22.2.
;; 2007/10/07 dadams
;;     Added: bookmark-completing-read, bookmark-delete, bookmark-insert(-location),
;;            bookmark-jump, bookmark-relocate, bookmark-rename.
;;     bookmark-jump-other-window: Use new bookmark-completing-read.
;; 2007/07/13 dadams
;;     Replaced Emacs version tests to reflect Emacs 22 release.
;; 2006/03/08 dadams
;;     bookmark-jump-other-window: Handle nil arg.
;; 2005/05/17 dadams
;;     Updated to work with Emacs 22.x.
;; 2004/11/20 dadams
;;     Refined to deal with Emacs 21 < 21.3.50 (soon to be 22.x)
;; 2004/10/26 dadams
;;     Different menu-bar command, depending on Emacs version.
;; 2004/09/21 dadams
;;     Only define bookmark-menu-jump-other-window if < Emacs 22.
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

;; You need not load this file.  It contains only documentation.

(provide 'bookmark+-chg)                ; Not used.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-chg.el ends here

