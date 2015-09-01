;;; info+.el --- Extensions to `info.el'.
;;
;; Filename: info+.el
;; Description: Extensions to `info.el'.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 1996-2012, Drew Adams, all rights reserved.
;; Created: Tue Sep 12 16:30:11 1995
;; Version: 21.1
;; Last-Updated: Sun Jan 15 00:50:02 2012 (-0800)
;;           By: dradams
;;     Update #: 4495
;; URL: http://www.emacswiki.org/cgi-bin/wiki/info+.el
;; Keywords: help, docs, internal
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   `fit-frame', `info', `info+', `misc-fns', `strings',
;;   `thingatpt', `thingatpt+'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Extensions to `info.el'.
;;
;;  Faces defined here:
;;
;;    `info-command-ref-item', `info-file',
;;    `info-function-ref-item',`info-macro-ref-item', `info-menu',
;;    `info-node', `info-quoted-name', `info-reference-item',
;;    `info-single-quote', `info-special-form-ref-item',
;;    `info-string', `info-syntax-class-item',
;;    `info-user-option-ref-item', `info-variable-ref-item',
;;    `info-xref', `minibuffer-prompt'.
;;
;;  Options (user variables) defined here:
;;
;;    `Info-breadcrumbs-in-header-flag' (Emacs 23+),
;;    `Info-display-node-header-fn', `Info-fit-frame-flag',
;;    `Info-fontify-quotations-flag',
;;    `Info-fontify-reference-items-flag',
;;    `Info-fontify-single-quote-flag', `Info-saved-nodes',
;;    `Info-subtree-separator'.
;;
;;  Commands defined here:
;;
;;    `Info-breadcrumbs-in-mode-line-mode' (Emacs 23+),
;;    `info-emacs-manual', `Info-follow-nearest-node-new-window',
;;    `Info-merge-subnodes',
;;    `Info-mouse-follow-nearest-node-new-window',
;;    `Info-save-current-node', `Info-set-breadcrumbs-depth' (Emacs
;;    23+), `Info-toggle-breadcrumbs-in-header-line' (Emacs 23+),
;;    `Info-virtual-book', `menu-bar-read-lispref',
;;    `menu-bar-read-lispintro',
;;
;;  Non-interactive functions defined here:
;;
;;    `Info-display-node-default-header',
;;    `Info-display-node-time-header', `info-fontify-quotations',
;;    `info-fontify-reference-items',
;;    `Info-insert-breadcrumbs-in-mode-line' (Emacs 23+),
;;    `info-quotation-regexp'.
;;
;;  Internal variables defined here:
;;
;;    `Info-breadcrumbs-depth-internal' (Emacs 23+),
;;    `Info-merged-map', `Info-mode-syntax-table'.
;;
;;
;;  ***** NOTE: The following standard faces defined in `info.el'
;;              (Emacs 21+) have been REDEFINED HERE:
;;
;;  `info-title-1', `info-title-2', `info-title-3', `info-title-4'.
;;
;;
;;  ***** NOTE: The following standard functions defined in `info.el'
;;              have been REDEFINED HERE:
;;
;;  `info-display-manual' - Use completion to input manual name.
;;  `Info-find-emacs-command-nodes' - Added in-progress message.
;;  `Info-find-file' (Emacs 23+) - Handle virtual books.
;;  `Info-find-node', `Info-find-node-2' -
;;     Call `fit-frame' if `Info-fit-frame-flag'.
;;  `Info-fontify-node' -
;;     1. Show breadcrumbs in header line and/or mode line.
;;     2. File name in face `info-file'.
;;     3. Node names in face `info-node'.
;;     4. Menu items in face `info-menu'.
;;     5. Only 5th and 9th menu items have their `*' colored.
;;     6. Notes in face `info-xref'.
;;     7. If `Info-fontify-quotations-flag', then fontify `...' in
;;        face `info-quoted-name' and "..." in face `info-string'.
;;     8. If `Info-fontify-single-quote-flag' and
;;        `Info-fontify-quotations-flag', then fontify ' in face
;;        `info-single-quote'.
;;  `Info-goto-emacs-command-node' -
;;     1. Uses `completing-read' in interactive spec, with,
;;        as default, `symbol-nearest-point'.
;;     2. Message if single node found.
;;     3. Returns `num-matches' if found; nil if not.
;;  `Info-goto-emacs-key-command-node' -
;;     If key's command not found, then `Info-search's for key
;;     sequence in text and displays message about repeating.
;;  `Info-mode' - Doc string shows all bindings.
;;  `Info-read-node-name-1' - Treat file name entries, e.g. "(emacs)".
;;  `Info-search' - 1. Fits frame.
;;                  2. Highlights found regexp if `search-highlight'.
;;  `Info-set-mode-line' - Handles breadcrumbs in the mode line.
;;  `Info-mouse-follow-nearest-node' (Emacs 21+) -
;;     With prefix arg, show node in new info buffer.
;;
;;
;;  ***** NOTE: The following behavior defined in `info.el'
;;              has been changed.
;;
;;  "*info" has been removed from `same-window-buffer-names', so that
;;  a separate window can be used if the user so chooses.
;;
;;
;;  Suggestion: Use a medium-dark background for Info.  Try, for
;;  example, setting the background to "LightSteelBlue" in your
;;  `~/.emacs' file.  You can do this as follows:
;;
;;         (setq special-display-buffer-names
;;               (cons '("*info*" (background-color . "LightSteelBlue"))
;;                     special-display-buffer-names))
;;
;;  Alternatively, you can change the background value of
;;  `special-display-frame-alist' and set `special-display-regexps' to
;;  something matching "*info*":
;;
;;         (setq special-display-frame-alist
;;               (cons '(background-color . "LightSteelBlue")
;;                     special-display-frame-alist))
;;         (setq special-display-regexps '("[ ]?[*][^*]+[*]"))
;;
;;  If you do use a medium-dark background for Info, consider
;;  customizing face to a lighter foreground color - I use "Yellow".
;;
;;  Also, consider customizing face `link' to remove its underline
;;  attribute.
;;
;;
;;  The following bindings are made here for Info-mode:
;;
;;    `?'              `describe-mode' (replaces `Info-summary')
;;    `+'              `Info-merge-subnodes'
;;    `.'              `Info-save-current-node'
;;    `a'              `info-apropos'
;;    `v'              `Info-virtual-book'
;;    `mouse-4'        `Info-history-back'
;;    `mouse-5'        `Info-history-forward'
;;    `S-down-mouse-2' `Info-mouse-follow-nearest-node-new-window'
;;    `S-RET'          `Info-follow-nearest-node-new-window'
;;
;;  The following bindings are made here for merged Info buffers:
;;
;;    `.'              `beginning-of-buffer'
;;    `b'              `beginning-of-buffer'
;;    `q'              `quit-window'
;;    `s'              `nonincremental-re-search-forward'
;;    `M-s'            `nonincremental-re-search-forward'
;;    `TAB'            `Info-next-reference'
;;    `ESC TAB'        `Info-prev-reference'
;;
;;
;;
;;  This file should be loaded after loading the standard GNU file
;;  `info.el'.  So, in your `~/.emacs' file, do this:
;;  (eval-after-load "info" '(require 'info+))
;;
;;
;;  Acknowledgement:
;;
;;    Lennart Borgman and Stefan Monnier for regexp suggestions.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2012/01/15 dadams
;;     Added: info-display-manual (redefinition).
;;     Info-find-file: Do not define for < Emacs 23.2 - no virtual books.
;; 2011/11/15 dadams
;;     Added: redefinition of Info-find-file for Emacs 23+, to handle virtual books.
;; 2011/08/23 dadams
;;     Removed hard-code removal of info from same-window-(regexps|buffer-names).  Thx to PasJa.
;; 2011/02/06 dadams
;;     info-user-option-ref-item: Corrected background for light-bg case.
;; 2011/02/03 dadams
;;     All deffaces: Provided default values for dark-background screens too.
;; 2011/01/04 dadams
;;     Removed autoload cookies from non def* sexps.  Added for defgroup and defface.
;; 2010/05/27 dadams
;;     Added: Info-set-mode-line.
;;     Info-find-node-2:
;;       Added redefinition of it for Emacs 23.2 (sigh, they keep twiddling it).
;;       Do not call Info-insert-breadcrumbs-in-mode-line.  Do that in Info-set-mode-line now.
;; 2010/04/06 dadams
;;     Added: Info-breadcrumbs-in-header-flag, Info-toggle-breadcrumbs-in-header-line,
;;            Info-breadcrumbs-in-mode-line-mode, Info-set-breadcrumbs-depth,
;;            Info-insert-breadcrumbs-in-mode-line, Info-breadcrumbs-depth-internal.
;;     Added to Info-mode-menu (Emacs 23+): Info-breadcrumbs-in-mode-line-mode.
;;     Info-find-node-2 (Emacs 23+): Add breadcrumbs to header line & mode line only according to vars.
;;     Info-fontify-node (Emacs 23+): Handle breadcrumbs in header only if flag says to.
;; 2010/01/12 dadams
;;     Info-find-node for Emacs 20, Info-find-node-2 for Emacs 21, 22, Info-search:
;;       save-excursion + set-buffer -> with-current-buffer.
;; 2010/01/10 dadams
;;     Info-find-node-2 for Emacs 23+: Updated for Emacs 23.2 (pretest) - virtual function stuff.
;; 2009/12/13 dadams
;;     Typo: Incorrectly used Emacs 22 version for Emacs 21 also.
;; 2009/12/11 dadams
;;     info-fontify-(node|quotations|reference-items), Info-merge-subnodes:
;;       Use font-lock-face property, not face, if > Emacs 21.
;; 2009/08/03 dadams
;;     Updated for Emacs 23.1 release: Info-find-node-2, Info-fontify-node, Info-search: new version.
;; 2009/06/10 dadams
;;     Added: Info-fontify-reference-items-flag, Info-mode-syntax-table.
;;     Info-mode: Use Info-mode-syntax-table, not text-mode-syntax-table.
;;     Info-fontify-node: Fontify ref items if *-reference-items-flag, not just for Elisp manual.
;;     Renamed: info-elisp-* to info-*.
;; 2009/06/09 dadams
;;     info-fontify-quotations: Allow \ before ', just not before`.
;; 2009/06/08 dadams
;;     info-fontify-quotations: Rewrote, using better regexp.  Don't fontify escaped ` or '.
;;       Fontify `\', `\\', etc.  Respect Info-fontify-single-quote-flag.
;;     Added: info-single-quote, Info-fontify-single-quote-flag, info-quotation-regexp.
;;     info-quoted-name: Changed face spec to (:inherit font-lock-string-face :foreground "DarkViolet")
;; 2009/05/25 dadams
;;     Info-virtual-book: Treat info-node bookmarks too.
;; 2009/05/23 dadams
;;     Added: Info-mode for Emacs 23.
;;            They added Info-isearch-filter, Info-revert-buffer-function, Info-bookmark-make-record.
;; 2009/05/22 dadams
;;     Added: Info-saved-nodes, Info-save-current-node, Info-virtual-book.  Added to Info-mode-menu.
;;     Bind info-apropos, Info-save-current-node, Info-virtual-book to a, ., and v.
;;     Info-mode: Updated doc string.
;; 2009/04/26 dadams
;;     Info-merge-subnodes: Bind inhibit-field-text-motion to t, for end-of-line.
;; 2008/10/07 dadams
;;     Require cl.el at compile time for all Emacs versions, because of case.
;; 2008/10/05 dadams
;;     Added: Info-read-node-name-1, Info-read-node-name-2.
;; 2008-07-11 dadams
;;     Info-fontify-node (Emacs 22+): Protect histories when getting ancestor nodes for breadcrumbs.
;;     (Emacs 22+) Don't change faces info-menu-header, *-title-*, *(-header)-node, header-line.
;;     (Emacs 20, 21): Removed bold and italic attributes from info-node and info-xref.
;;     Removed commented out defface for info-xref and info-node.
;;     Face info-file: Blue, not DarkBlue, foreground, by default.
;; 2008/06/12 dadams
;;     Info-fontify-node (Emacs 22+):
;;       Prevent infinite recursion from Info-goto-node calling Info-fontify-node.
;;       Fixed for nil Info-hide-note-references.
;; 2008/06/10 dadams
;;     Info-fontify-node (Emacs 22+): Added breadcrumbs.
;; 2008/03/06 dadams
;;     info-mode:
;;       Use fboundp for Info-clone-buffer, not version test, for Emacs 22+. Thx to Sebastien Vauban.
;; 2008/02/01 dadams
;;     Info-mode: Renamed Info-clone-buffer-hook to Info-clone-buffer for Emacs 22.1.90.
;; 2008/01/08 dadams
;;     Info-search (Emacs 22): Removed phony pred arg.
;; 2008/01/06 dadams
;;     Removed soft require of Icicles due to cirular dependency.  Thx to Tennis Smith.
;; 2007/11/27 dadams
;;     Info-search: Use icicle-read-string-completing, if available.
;;     Added soft require Icicles.
;; 2007/11/20 dadams
;;     Info-subtree-separator: Escaped slashes in doc string: \f -> \\f.
;; 2007/09/26 dadams
;;     Better default color for info-quoted-name.  Added group face to all deffaces.
;; 2007/09/25 dadams
;;     Bound Info-mouse-*-new-* to S-down-mouse-2, not S-mouse-2, because of mouse-scan-lines-or-M-:.
;;     Info-goto-emacs-command-node: Convert completion default value to string.
;; 2007/08/27 dadams
;;     Info-fontify-node:
;;       Ensure Info-fontify-node is a string when fontifiy quotations. Updated for released Emacs 22.
;; 2007/07/13 dadams
;;     Info-find-node: Redefine only for Emacs < 21.
;; 2006/09/15 dadams
;;     Info-mouse-follow-nearest-node redefinition is only for Emacs >= 22.
;;     Changed Emacs 22 tests to just (>= emacs-major-version 22).
;;     Bind tool-bar-map for Emacs 21.  Otherwise, binding of [tool-bar] gives an error (why?).
;; 2006/08/18 dadams
;;     Everywhere: Corrected previous change: minibuffer-selected-window to window-minibuffer-p.
;; 2006/08/14 dadams
;;     Everywhere: fit-frame only if not a minibuffer window.
;; 2006/08/12 dadams
;;     Info-merge-subnodes: Bug fixes:
;;       Added concat for insertion of main node when recursive-display-p is negative.
;;       Don't recurse down Index menus.
;;       When checking for subnodes menu, check for nonfile menu item also.
;;       After come back from recursion, go back to Info buffer before trying to go back in history.
;;       Call fit-frame at end.
;; 2006/06/10 dadams
;;     Added: Info(-mouse)-follow-nearest-node-new-window.  Bound to S-RET, S-mouse-2.
;; 2006/03/31 dadams
;;     info-menu-header: Removed :underline, because links are underlined in Emacs 22.
;;     No longer use display-in-minibuffer.
;; 2006/01/08 dadams
;;      Added: redefinition of Info-mouse-follow-nearest-node.
;; 2006/01/07 dadams
;;      Added :link for sending bug report.
;; 2006/01/06 dadams
;;     Added defgroup Info-Plus and used it. Added :link.
;; 2005/12/30 dadams
;;     Moved everything from setup-info.el to here, after getting rid of some of it.
;;     Use defface for all faces.  Renamed faces, without "-face".
;;     Use minibuffer-prompt face, not info-msg-face.
;;     No longer require setup-info.el.  No longer require cl.el when compile.
;; 2005/11/21 dadams
;;     Info-search for Emacs 22: Don't display repeat `s' message if isearch-mode.
;; 2005/11/09 dadams
;;     Info-fontify-node: Updated to reflect latest CVS (replaced Info-escape-percent header).
;; 2005/10/31 dadams
;;     Use nil as init-value arg in calls to completing-read, everywhere.
;; 2005/07/04 dadams
;;     info-fontify-quotations: Use font-lock-face property, instead of face, for Emacs 22.
;;                              Wrap re-search-forward in condition-case for stack overflow.
;; 2005/07/02 dadams
;;     Info-search: fit-frame. Added Emacs 22 version too.
;;     Info-goto-emacs-command-node, Info-goto-emacs-key-command-node,
;;       Info-merge-subnodes: Use Info-history-back for Emacs 22.
;;     Info-mode: Added Emacs 22 version.
;; 2005/06/23 dadams
;;     Info-fontify-node: Fontify reference items if in Emacs-Lisp manual.
;;     Added: info-fontify-reference-items
;; 2005/05/17 dadams
;;     Updated to work with Emacs 22.x.
;; 2004/11/20 dadams
;;     Info-find-emacs-command-nodes: bug fix: regexp (cmd-desc) was only for Emacs 21.
;;     Refined to deal with Emacs 21 < 21.3.50 (soon to be 22.x)
;; 2004/10/09 dadams
;;     info-fontify-quotations:
;;       1) Allow all characters inside `...'.
;;       2) Treat case of "..." preceded by backslashes
;;     Info-fontify-node (for Emacs 21): Moved info-fontify-quotations
;;       before fontification of titles.
;; 2004/10/07 dadams
;;     Renamed Info-resize-frame-p to Info-fit-frame-flag.
;; 2004/10/05 dadams
;;     Improved regexp treatment further for fontifying quotations.
;; 2004/10/04 dadams
;;     Improved regexp treatment for fontifying quotations.
;;       Added info-fontify-quotations. Removed info-fontify-strings-p.
;;       Renamed Info-fontify-quotations-p to Info-fontify-quotations-flag.
;; 2004/10/03/dadams
;;     Major update: updated to work with Emacs 21 also.
;;     Made require of setup-info.el mandatory.
;;     Removed all variables and keys to setup-info.el.
;;     Renamed to Emacs 21 names and only define for Emacs < 21:
;;       emacs-info -> info-emacs-manual
;; 2004/09/28 dadams
;;     Removed dir-info (same as Info-directory).
;;     Renamed to Emacs 21 names and only define for Emacs < 21:
;;       emacs-lisp-info -> menu-bar-read-lispref
;; 2004/06/01 dadams
;;     Renamed:  Info-fit-frame-p to Info-resize-frame-p
;;               and shrink-frame-to-fit to resize-frame.
;; 2000/09/27 dadams
;;     1. Added: Info-fit-frame-p.
;;     2. Info-find-node: added shrink-frame-to-fit.
;; 1999/04/14 dadams
;;     Info-fontify-node: Fontify indexes too.
;; 1999/04/14 dadams
;;     1. Added vars: info-file-face, info-menu-face, info-node-face,
;;        info-quoted-name-face, info-string-face, info-xref-face.
;;     2. No longer use (or define) faces: info-node, info-file, info-xref,
;;        info-menu-5, info-quoted-name, info-string.
;;     3. Info-fontify-node: Use new face variables instead of faces in #2, above.
;;        Corrected: node names in info-node-face (was xref). Use info-menu-face
;;        for * and menu item.
;;     4. Info-mode: Redefined like original, but: no make-face's; use face vars.
;;        Added user options description to doc string.
;; 1999/04/08 dadams
;;     Info-goto-emacs-key-command-node: regexp-quote pp-key for Info-search.
;; 1999/04/07 dadams
;;     Info-goto-emacs-key-command-node: a) messages only if interactive,
;;         b) return nil if not found, else non-nil, c) "is undefined" -> "doc not
;;         found", d) use display-in-minibuffer more, e) corrected error handler.
;; 1999/04/01 dadams
;;     1. Added: (remove-hook 'same-window-buffer-names "*info*").
;;     2. Info-find-node: switch-to-buffer-other-window -> pop-to-buffer.
;; 1999/03/31 dadams
;;     1. Added (put 'Info-goto-emacs-(key-)command-node 'info-file "emacs").
;;     2. Info-find-node: Mention searched file in error messages.
;;     3. Added (replacement): Info-find-emacs-command-nodes, with progress msg.
;;     4. a. Info-goto-emacs-key-command-node: Use global-map, unless menu item.
;;        b. Added message "Not found using Index ...".
;; 1999/03/31 dadams
;;     1. Info-goto-emacs(-key)-command-node: Only display-in-minibuffer if
;;        interactive-p.
;;     2. Info-goto-emacs-key-command-node: Messages: "key"; other entries.
;; 1999/03/31 dadams
;;     1. Added (put 'info 'info-file "emacs") so find doc on `info' cmd.
;;     2. Info-goto-emacs-command-node:
;;        a. Added message when =< 1 match.
;;        b. Return num-matches if found.
;;        c. Uses `display-in-minibuffer' instead of `message'.
;;     3. a. Wrapped call to Info-search in condition-case, not if.
;;        b. Info-goto-emacs-key-command-node: Return num-matches if found.
;; 1999/03/30 dadams
;;     1. Added Info menu bar menu.
;;     2. Info-goto-emacs-command-node: Only error if interactive-p.
;;     3. Info-goto-emacs-key-command-node:
;;        a. Print key in msgs
;;        b. If Info-goto-emacs-command-node doesn't find it, then try
;;           Info-search. If found & interactive-p, then msg ("repeat").
;;           Else error.
;;     4. Info-search: Msg ("repeat") if found & interactive-p.
;; 1999/03/17 dadams
;;     1. Updated to correspond with Emacs 34.1 version.
;;     2. Protect with fboundp.
;; 1996/07/11 dadams
;;     Added redefinitions of Info-goto-emacs-(key-)command-node.
;; 1996/04/26 dadams
;;     Put escaped newlines on long-line strings.
;; 1996/04/16 dadams
;;     Added: info-file, info-quoted-name, info-string, Info-fontify-quotations-flag,
;;            info-fontify-strings-p.  Take into account in Info-fontify-node.
;; 1996/02/23 dadams
;;     1. Changed binding of Info-merge-subnodes back to `r', but now
;;        requires user confirmation when invoked.
;;     2. Info-subtree-separator: Incorporates "\n* ".  variable-interactive prop.
;; 1996/02/22 dadams
;;     display-Info-node-subtree:
;;       1. display-Info-node-subtree -> Info-merge-subnodes (renamed).
;;       2. Changed binding of Info-merge-subnodes from `r' to `C-d'.
;;       3. Don't pick up text between menu-item-line and "\n* ".  Hardwire "\n* ".
;;       4. Untabify menu-item-line, so can count chars to underline.
;;       5. indent-rigidly, not indent-region.
;; 1996/02/22 dadams
;;     1. Bind describe-mode and display-Info-node-subtree.
;;     2. Added redefinition of Info-mode: Only the doc string was changed.
;;     3. Added Info-subtree-separator.
;;     3. display-Info-node-subtree: Info-subtree-separator. Doc. Garbage-collect.
;; 1996/02/22 dadams
;;     Info-merge-subnodes: Rewrote it, adding optional args.  Renamed (defaliased) it
;;       to display-Info-node-subtree.
;; 1996/02/22 dadams
;;     Added redefinition of Info-merge-subnodes (cleanup, corrections).
;; 1996/02/20 dadams
;;     1. Make info-node, info-xref, info-menu-5 here. (Diff faces than before.)
;;     2. Added redefinition of Info-find-node.  (Uses other window.)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'info)
(eval-when-compile (require 'cl)) ;; case
                                  ;; Plus, for Emacs < 20, caar, cadr, when, unless

;; These are optional, for cosmetic purposes.
(require 'thingatpt nil t) ;; (no error if not found): symbol-at-point
(require 'thingatpt+ nil t) ;; (no error if not found): symbol-nearest-point
(require 'strings nil t) ;; (no error if not found): concat-w-faces
(require 'fit-frame nil t) ;; (no error if not found): fit-frame

;; Took this out because it leads to a circular `require' dependency.
;; (when (>= emacs-major-version 22)
;;   (require 'icicles nil t)) ;; (no error if not found): icicle-read-string-completing

;; Quiet the byte compiler a bit.
;;
;; (when (< emacs-major-version 21)
;;   (eval-when-compile
(defvar desktop-save-buffer)
(defvar header-line-format)
(defvar Info-breadcrumbs-in-mode-line-mode)
(defvar Info-fontify-visited-nodes)
(defvar Info-hide-note-references)
(defvar Info-history-list)
(defvar Info-isearch-initial-node)
(defvar Info-isearch-search)
(defvar Info-menu-entry-name-re)
(defvar Info-next-link-keymap)
(defvar Info-mode-line-node-keymap)
(defvar Info-node-spec-re)
(defvar Info-point-loc)
(defvar Info-prev-link-keymap)
(defvar Info-refill-paragraphs)
(defvar Info-saved-nodes)
(defvar Info-search-case-fold)
(defvar Info-search-history)
(defvar Info-search-whitespace-regexp)
(defvar info-tool-bar-map)
(defvar Info-up-link-keymap)
(defvar Info-use-header-line)
(defvar widen-automatically)

;; (when (< emacs-major-version 23)
;;   (eval-when-compile
(defvar Info-read-node-completion-table)
(defvar Info-breadcrumbs-depth)
(defvar Info-breadcrumbs-depth-internal)
(defvar Info-breadcrumbs-in-header-flag)
(defvar Info-current-node-virtual)
(defvar Info-last-search)
(defvar Info-title-face-alist)
(defvar isearch-filter-predicate)

;;; You will likely get byte-compiler messages saying that variable
;;; `node-name' is free.  In older Emacs versions, you might also get
;;; a byte-compiler message saying that some functions are not known
;;; to be defined.

;;;;;;;;;;;;;;;;;;;;

(provide 'info+)
(require 'info+) ;; Ensure loaded before compiling.

;;;;;;;;;;;;;;;;;;;;


;;; KEYS & MENUS ;;;;;;;;;;;;;;;;;;;;;;;;

(define-key Info-mode-map "?" 'describe-mode) ; Don't use `Info-summary'.
(define-key Info-mode-map "+" 'Info-merge-subnodes)

(when (> emacs-major-version 21)
  (define-key Info-mode-map "."               'Info-save-current-node)
  (define-key Info-mode-map "a"               'info-apropos)
  (define-key Info-mode-map "v"               'Info-virtual-book)
  ;; Mouse back and forward buttons
  (define-key Info-mode-map [S-down-mouse-2]  'Info-mouse-follow-nearest-node-new-window)
  (define-key Info-mode-map [S-return]        'Info-follow-nearest-node-new-window)
  (define-key Info-mode-map [mouse-4]         'Info-history-back)
  (define-key Info-mode-map [mouse-5]         'Info-history-forward))



;;; FACES ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defgroup Info-Plus nil
  "Various enhancements to Info."
  :group 'info
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
info+.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/cgi-bin/wiki/DrewsElispLibraries")
  :link '(url-link :tag "Download" "http://www.emacswiki.org/cgi-bin/wiki/info+.el")
  :link '(url-link :tag "Description" "http://www.emacswiki.org/cgi-bin/wiki/InfoPlus")
  :link '(emacs-commentary-link :tag "Commentary" "info+")
  )

;; This is defined in `faces.el', Emacs 22+.  This definition is adapted to Emacs 20.
(unless (facep 'minibuffer-prompt)
  (defface minibuffer-prompt
      '((((background dark)) (:foreground "cyan"))
        (t (:foreground "dark blue")))
    "*Face for minibuffer prompts."
    :group 'basic-faces))

;;;###autoload
(defface info-file
    '((((background dark)) (:foreground "Yellow" :background "DimGray"))
      (t (:foreground "Blue" :background "LightGray")))
  "*Face for file heading labels in `info'." :group 'Info-Plus :group 'faces)

;;;###autoload
(defface info-menu
    '((((background dark)) (:foreground "Yellow"))
      (t (:foreground "Blue")))
  "*Face used for menu items in `info'." :group 'Info-Plus :group 'faces)

;; FWIW, I use a `LightSteelBlue' background for `*info*', and I use `yellow' for this face.
;;;###autoload
(defface info-quoted-name               ; For `...'
    '((((background dark)) (:inherit font-lock-string-face :foreground "#6B6BFFFF2C2C")) ; ~ green
      (((background light)) (:inherit font-lock-string-face :foreground "DarkViolet"))
      (t (:foreground "yellow")))
  "*Face for quoted names (`...') in `info'."
  :group 'Info-Plus :group 'faces)

;; FWIW, I use a `LightSteelBlue' background for `*info*', and I use `red3' for this face.
;;;###autoload
(defface info-string                    ; For "..."
    '((((background dark)) (:inherit font-lock-string-face :foreground "Orange"))
      (t (:inherit font-lock-string-face :foreground "red3")))
  "*Face for strings (\"...\") in `info'."
  :group 'Info-Plus :group 'faces)

;;;###autoload
(defface info-single-quote              ; For '
    '((((background dark)) (:inherit font-lock-keyword-face :foreground "Green"))
      (t (:inherit font-lock-keyword-face :foreground "Magenta")))
  "*Face for isolated single-quote marks (') in `info'."
  :group 'Info-Plus :group 'faces)

;;; These are only for Emacs 20 and 21.
(unless (fboundp 'set-face-attribute)
  (set-face-foreground 'info-node "Blue")
  (set-face-background 'info-node "SkyBlue")
  (set-face-bold-p     'info-node nil)
  (set-face-italic-p   'info-node nil)
  (set-face-foreground 'info-xref "Blue")
  (set-face-bold-p     'info-xref nil))

;; Standard faces from vanilla Emacs `info.el', but without `:weight', `:height' and `:inherit'.
;;;###autoload
(defface info-title-1
    '((((type tty pc) (class color) (background dark))  :foreground "yellow" :weight bold)
      (((type tty pc) (class color) (background light)) :foreground "brown"  :weight bold))
  "*Face for info titles at level 1."
  :group (if (facep 'info-title-1) 'info 'Info-Plus))
;; backward-compatibility alias
(put 'Info-title-1-face 'face-alias 'info-title-1)

;;;###autoload
(defface info-title-2
    '((((type tty pc) (class color)) :foreground "lightblue" :weight bold))
  "*Face for info titles at level 2."
  :group (if (facep 'info-title-1) 'info 'Info-Plus))
;; backward-compatibility alias
(put 'Info-title-2-face 'face-alias 'info-title-2)

;;;###autoload
(defface info-title-3
    '((((type tty pc) (class color)) :weight bold))
  "*Face for info titles at level 3."
  :group (if (facep 'info-title-1) 'info 'Info-Plus))
;; backward-compatibility alias
(put 'Info-title-3-face 'face-alias 'info-title-3)

;;;###autoload
(defface info-title-4
    '((((type tty pc) (class color)) :weight bold))
  "*Face for info titles at level 4."
  :group (if (facep 'info-title-1) 'info 'Info-Plus))
;; backward-compatibility alias
(put 'Info-title-4-face 'face-alias 'info-title-4)

(when (<= emacs-major-version 21)
  (setq Info-title-face-alist  '((?* info-title-1 bold underline)
                                 (?= info-title-2 bold-italic underline)
                                 (?- info-title-4 italic underline))))

;;; Faces for highlighting reference items
;;;###autoload
(defface info-function-ref-item
    '((((background dark))
       (:foreground "#4D4DDDDDDDDD" :background "DimGray")) ; ~ cyan
      (t (:foreground "DarkBlue" :background "LightGray")))
  "*Face used for \"Function:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-variable-ref-item
    '((((background dark))
       (:foreground "Orange" :background "DimGray"))
      (t (:foreground "FireBrick" :background "LightGray")))
  "*Face used for \"Variable:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-special-form-ref-item
    '((((background dark))
       (:foreground "Yellow" :background "DimGray")) ; ~ light green
      (t (:foreground "DarkMagenta" :background "LightGray")))
  "*Face used for \"Special Form:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-command-ref-item
    '((((background dark)) (:foreground "#7474FFFF7474" :background "DimGray")) ; ~ light green
      (t (:foreground "Blue" :background "LightGray")))
  "*Face used for \"Command:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-user-option-ref-item
    '((((background dark)) (:foreground "Red" :background "DimGray"))
      (t (:foreground "Red" :background "LightGray")))
  "*Face used for \"User Option:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-macro-ref-item
    '((((background dark))
       (:foreground "Yellow" :background "DimGray")) ; ~ light green
      (t (:foreground "DarkMagenta" :background "LightGray")))
  "*Face used for \"Macro:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-syntax-class-item
    '((((background dark))
       (:foreground "#FFFF9B9BFFFF" :background "DimGray")) ; ~ pink
      (t (:foreground "DarkGreen" :background "LightGray")))
  "*Face used for \"Syntax Class:\" reference items in `info' manual."
  :group 'Info-Plus :group 'faces)
;;;###autoload
(defface info-reference-item
    '((((background dark)) (:background "DimGray"))
      (t (:background "LightGray")))
  "*Face used for reference items in `info' manual."
  :group 'Info-Plus :group 'faces)


;;; USER OPTIONS (VARIABLES) ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defcustom Info-fit-frame-flag t
  "*Non-nil means call `fit-frame' on Info buffer."
  :type 'boolean :group 'Info-Plus :group 'Fit-Frame)

;;;###autoload
(defcustom Info-fontify-quotations-flag t
  "*Non-nil means `info' fontifies text between quotes.
This applies to double-quote strings (\"...\") and text between
single-quotes (`...').

Note: This fontification can never be 100% reliable.  It aims to be
useful in most Info texts, but it can occasionally result in
fontification that you might not expect.  This is not a bug; it is
part of the design to be able to appropriately fontify a great variety
of texts.  Set this flag to nil if you do not find this fontification
useful."
  :type 'boolean :group 'Info-Plus)

;;;###autoload
(defcustom Info-fontify-single-quote-flag t
  "*Non-nil means `info' fontifies ' when not preceded by `....
A non-nil value has no effect unless `Info-fontify-quotations-flag' is
also non-nil.

Note: This fontification can never be 100% reliable.  It aims to be
useful in most Info texts, but it can occasionally result in
fontification that you might not expect.  This is not a bug; it is
part of the design to be able to appropriately fontify a great variety
of texts.  Set this flag to nil if you do not find this fontification
useful."
  :type 'boolean :group 'Info-Plus)

;;;###autoload
(defcustom Info-fontify-reference-items-flag t
  "*Non-nil means `info' fontifies reference items such as \"Function:\"."
  :type 'boolean :group 'Info-Plus)

;;;###autoload
(defcustom Info-display-node-header-fn 'Info-display-node-default-header
  "*Function to insert header by `Info-merge-subnodes'."
  :type 'function :group 'Info-Plus)

;;;###autoload
(defcustom Info-subtree-separator "\n* "
  "*A string used to separate Info node descriptions.
Inserted by `Info-merge-subnodes' just before each node title.
Setting this to a string that includes a form-feed (^L), such as
\"\\f\\n* \", will cause a page break before each node description.

Use command `set-variable' to set this, quoting any control characters
you want to include, such as form-feed (^L) and newline (^J), with ^Q.
For example, type `^Q^L^Q^J* ' to set this to \"\\f\\n* \"."
  :type 'string :group 'Info-Plus)

(when (> emacs-major-version 22)
  (defcustom Info-breadcrumbs-in-header-flag nil
    "*Non-nil means breadcrumbs are shown in the header line."
    :type 'boolean :group 'Info-Plus))


;;; NEW COMMANDS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(when (>= emacs-major-version 22)
  (defun Info-mouse-follow-nearest-node-new-window (click)
    "Open the link at the mouse pointer in a new window."
    (interactive "e")
    (Info-mouse-follow-nearest-node click t))
  (defun Info-follow-nearest-node-new-window ()
    "Open the link near the text cursor in a new window."
    (interactive)
    (Info-follow-nearest-node t)))


;;; INTERNAL VARIABLES ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I reported this as Emacs bug #3312.  If it gets fixed, this can be removed.
(defvar Info-mode-syntax-table
  (let ((table  (copy-syntax-table text-mode-syntax-table)))
    (modify-syntax-entry ?'    "." table) ; Punctuation syntax for apostrophe (').
    (modify-syntax-entry ?\240 "." table) ; Punctuation syntax for non-breaking space.
    table)
  "Syntax table for `info'.")

(defvar Info-merged-map nil "Keymap for merged Info buffer.")
(if Info-merged-map
    nil
  (setq Info-merged-map  (make-keymap))
  (suppress-keymap Info-merged-map)
  (define-key Info-merged-map "." 'beginning-of-buffer)
  (define-key Info-merged-map "\t" 'Info-next-reference)
  (define-key Info-merged-map "\e\t" 'Info-prev-reference)
  (define-key Info-merged-map "b" 'beginning-of-buffer)
  (define-key Info-merged-map "q" 'quit-window)
  (define-key Info-merged-map "s" 'nonincremental-re-search-forward)
  (define-key Info-merged-map "\M-s" 'nonincremental-re-search-forward))

(if (>= emacs-major-version 22)
    (easy-menu-define
     Info-mode-menu Info-mode-map
     "Menu for info files."
     '("Info"
       ["Table of Contents" Info-toc :help "Go to table of contents"]
       ["Virtual Book" Info-virtual-book
        :help "Open table of contents of a virtual book" :active Info-saved-nodes]
       ["Save Current Node" Info-save-current-node
        :help "Save current node name for virtual book"]
       ["Find...(Regexp)" Info-search
        :help "Search for regular expression in this Info file"]
       ["Find Case-Sensitively..." Info-search-case-sensitively
        :help "Search for regular expression case sensitively"]
       ["Find Again" Info-search-next
        :help "Search for another occurrence of same regular expression"]
       ("Index"
        ["Find with Index..." Info-index :help "Look for a string in the index"]
        ["Find Again with Index" Info-index-next :active Info-index-alternatives
         :help "Look for string again in index"]
        ["Find In All Indexes..." info-apropos
         :help "Look for a string in the indexes of all manuals"])
       "--"
       ["Back (History)" Info-history-back :active Info-history
        :help "Go back in history to the last node you were at"]
       ["Forward (History)" Info-history-forward :active Info-history-forward
        :help "Go forward in history"]
       ["History List" Info-history :active Info-history-list
        :help "Go to menu of visited nodes"]
       "--"
       ["Top" Info-directory :help "Go to the list of manuals (Info top level)"]
       ["Up" Info-up :active (Info-check-pointer "up") :help "Go up in the Info tree"]
       ["Next" Info-next :active (Info-check-pointer "next") :help "Go to the next node"]
       ["Previous" Info-prev :active (Info-check-pointer "prev[ious]*")
        :help "Go to the previous node"]
       ("Menu Item" ["You should never see this" report-emacs-bug t])
       ("Reference" ["You should never see this" report-emacs-bug t])
       ["Go to Node..." Info-goto-node :help "Go to a named node"]
       "--"
       ["Forward" Info-forward-node
        :help "Go forward one node, considering all as a sequence"]
       ["Backward" Info-backward-node
        :help "Go backward one node, considering all as a sequence"]
       ["First in File" Info-top-node :help "Go to top node of file"]
       ["Last in File" Info-final-node :help "Go to final node in this file"]
       ["Beginning of This Node" beginning-of-buffer :help "Go to beginning of this node"]
       "--"
       ["Clone Info Buffer" clone-buffer
        :help "Create a twin copy of the current Info buffer."]
       ["Copy Node Name" Info-copy-current-node-name
        :help "Copy the name of the current node into the kill ring"]
       ["Merge Subnodes" Info-merge-subnodes
        :help "Integrate current node with nodes referred to in its Menu"]
       ["Edit" Info-edit :help "Edit contents of this node" :active Info-enable-edit]
       "--"
       ["Quit Info" Info-exit :help "Exit from Info"]))
  (easy-menu-define
   Info-mode-menu
   Info-mode-map
   "Menu for Info files."
   '("Info"
     ["Back" Info-last Info-history]
     ("Menu item" ["You should never see this" report-emacs-bug t])
     ("Reference" ["You should never see this" report-emacs-bug t])
     "--"
     ["Up" Info-up (Info-check-pointer "up")]
     ["Next" Info-next (Info-check-pointer "next")]
     ["Previous" Info-prev (Info-check-pointer "prev[ious]*")]
     ["Top" Info-directory t]
     ["Goto Node..." Info-goto-node t]
     "--"
     ["Forward in File" Info-forward-node t]
     ["Backward in File" Info-backward-node t]
     ["First in File" Info-top-node t]
     ["Last in File" Info-final-node t]
     "--"
     ["Next Link in Node" Info-next-reference t]
     ["Previous Link in Node" Info-prev-reference t]
     "--"
     ["Search (regexp)" Info-search t]
     ["Info on Key" Info-goto-emacs-key-command-node t]
     ["Info on Command" Info-goto-emacs-command-node t]
     ["Find with Index" Info-index t]
     "--"
     ["Merge Subnodes" Info-merge-subnodes t]
     ["Edit Node" Info-edit t]
     "--"
     ["Tutorial" Info-help t]
     ["Quit Info" Info-exit t])))

(when (> emacs-major-version 22)
  (easy-menu-add-item
   Info-mode-menu nil 
   ["Toggle Breadcrumbs in Mode Line" Info-breadcrumbs-in-mode-line-mode
                                      :help "Toggle showing breadcrumbs in the mode line"]
   "Quit Info")
  (easy-menu-add-item
   Info-mode-menu nil 
   ["Toggle Breadcrumbs in Header Line" Info-toggle-breadcrumbs-in-header-line    
                                        :help "Toggle showing breadcrumbs in the header line"]
   "Quit Info"))

(when (> emacs-major-version 22)
  (defun Info-toggle-breadcrumbs-in-header-line ()
    "Toggle showing breadcrumbs in a header line."
    (interactive)
    (setq Info-breadcrumbs-in-header-flag  (not Info-breadcrumbs-in-header-flag))))

(easy-menu-define
 Info-merged-menu
 Info-merged-map
 "Menu for merged `info' buffers."
 '("Info"
   ["Next Link" Info-next-reference t]
   ["Previous Link" Info-prev-reference t]
   ["Search (regexp)" Info-search t]
   ["Quit" quit-window t]))


;; Make `Info-find-emacs-command-nodes' look for these commands in the
;; Emacs manual. In particular, don't look for command `info' in Info
;; manual, because that has no index.
(put 'info 'info-file "emacs")
(put 'Info-goto-emacs-command-node 'info-file "emacs")
(put 'Info-goto-emacs-key-command-node 'info-file "emacs")


(unless (>= emacs-major-version 22)
  ;; I previously called this `emacs-info', but Emacs 21 came out with this name.
  (defun info-emacs-manual ()
    "Access the Emacs manual via \"Info\"."
    (interactive) (info "emacs"))

  ;; I previously called this `emacs-lisp-info', but Emacs 21 came out with this name.
  (defun menu-bar-read-lispref ()
    "Access the Emacs Lisp manual via \"Info\"."
    (interactive) (info "elisp"))

  ;; From Emacs 21 `menu-bar.el'. Of course, the file `eintr.info' needs to be there.
  (defun menu-bar-read-lispintro ()
    "Display the Introduction to Emacs Lisp Programming in Info mode."
    (interactive) (info "eintr")))



;; REPLACE ORIGINAL in `info.el':
;; 
;; Added final clause to `cond', to handle virtual books.  (Emacs 23.2+)
;;
(when (or (> emacs-major-version 23) (and (= emacs-major-version 23) (> emacs-minor-version 1)))
  (defun Info-find-file (filename &optional noerror)
    "Return expanded FILENAME, or t if FILENAME is \"dir\".
Optional second argument NOERROR, if t, means if file is not found
just return nil (no error)."
    ;; Convert filename to lower case if not found as specified.
    ;; Expand it.
    (cond
      ((Info-virtual-call (Info-virtual-fun 'find-file filename nil) filename noerror))
      ((stringp filename)
       (let (temp temp-downcase found)
         (setq filename  (substitute-in-file-name filename))
         (let ((dirs  (if (string-match "^\\./" filename)
                          '("./")       ; If specified name starts with `./' then just try current dir.
                        (if (file-name-absolute-p filename)
                            '(nil)      ; No point in searching for an absolute file name
                          (if Info-additional-directory-list
                              (append Info-directory-list Info-additional-directory-list)
                            Info-directory-list)))))
           ;; Fall back on the installation directory if we can't find the info node anywhere else.
           (when installation-directory
             (setq dirs  (append dirs (list (expand-file-name "info" installation-directory)))))
           ;; Search the directory list for file FILENAME.
           (while (and dirs (not found))
             (setq temp           (expand-file-name filename (car dirs)))
             (setq temp-downcase  (expand-file-name (downcase filename) (car dirs)))
             ;; Try several variants of specified name.
             (let ((suffix-list  Info-suffix-list)
                   (lfn          (if (fboundp 'msdos-long-file-names) (msdos-long-file-names) t)))
               (while (and suffix-list (not found))
                 (cond ((info-file-exists-p
                         (info-insert-file-contents-1 temp (car (car suffix-list)) lfn))
                        (setq found temp))
                       ((info-file-exists-p
                         (info-insert-file-contents-1 temp-downcase (car (car suffix-list)) lfn))
                        (setq found temp-downcase))
                       ((and (fboundp 'msdos-long-file-names)
                             lfn
                             (info-file-exists-p
                              (info-insert-file-contents-1 temp (car (car suffix-list)) nil)))
                        (setq found  temp)))
                 (setq suffix-list  (cdr suffix-list))))
             (setq dirs  (cdr dirs))))
         (if found
             (setq filename  found)
           (if noerror
               (setq filename nil)
             (error "Info file %s does not exist" filename)))
         filename))
      ((member filename '(apropos history toc))  filename))) ; Handle virtual books - `toc'.
  )



;; REPLACE ORIGINAL in `info.el':
;;
;; Call `fit-frame' if `Info-fit-frame-flag'.
;;
(when (< emacs-major-version 21)
  (defun Info-find-node (filename nodename &optional no-going-back)
    ;; Go to an info node specified as separate FILENAME and NODENAME.
    ;; NO-GOING-BACK is non-nil if recovering from an error in this function;
    ;; it says do not attempt further (recursive) error recovery.

    ;; Convert filename to lower case if not found as specified.
    ;; Expand it.
    (if filename
        (let (temp temp-downcase found)
          (setq filename  (substitute-in-file-name filename))
          (if (string= (downcase  filename) "dir")
              (setq found  t)
            (let ((dirs  (if (string-match "^\\./" filename)
                             ;; If specified name starts with `./'
                             ;; then just try current directory.
                             '("./")
                           (if (file-name-absolute-p filename)
                               ;; No point in searching for an absolute file name.
                               '(nil)
                             (if Info-additional-directory-list
                                 (append Info-directory-list
                                         Info-additional-directory-list)
                               Info-directory-list)))))
              ;; Search the directory list for file FILENAME.
              (while (and dirs (not found))
                (setq temp           (expand-file-name filename (car dirs))
                      temp-downcase  (expand-file-name (downcase filename) (car dirs)))
                ;; Try several variants of specified name.
                (let ((suffix-list  Info-suffix-list))
                  (while (and suffix-list (not found))
                    (cond ((info-file-exists-p
                            (info-insert-file-contents-1 temp (caar suffix-list)))
                           (setq found  temp))
                          ((info-file-exists-p
                            (info-insert-file-contents-1 temp-downcase (caar suffix-list)))
                           (setq found  temp-downcase)))
                    (setq suffix-list  (cdr suffix-list))))
                (setq dirs  (cdr dirs)))))
          (if found (setq filename found) (error "Info file `%s' does not exist" filename))))
    ;; Record the node we are leaving.
    (when (and Info-current-file (not no-going-back))
      (setq Info-history  (cons (list Info-current-file Info-current-node (point)) Info-history)))
    ;; Go into info buffer.
    (or (eq major-mode 'Info-mode) (pop-to-buffer "*info*"))
    (buffer-disable-undo (current-buffer))
    (or (eq major-mode 'Info-mode) (Info-mode))
    (widen)
    (setq Info-current-node  nil)
    (unwind-protect
         ;; Bind case-fold-search in case the user sets it to nil.
         (let ((case-fold-search  t)
               anchorpos)
           ;; Switch files if necessary
           (or (null filename)
               (equal Info-current-file filename)
               (let ((buffer-read-only  nil))
                 (setq Info-current-file              nil
                       Info-current-subfile           nil
                       Info-current-file-completions  ()
                       buffer-file-name               nil)
                 (erase-buffer)
                 (if (eq filename t)
                     (Info-insert-dir)
                   (info-insert-file-contents filename t)
                   (setq default-directory  (file-name-directory filename)))
                 (set-buffer-modified-p nil)
                 ;; See whether file has a tag table.  Record the location if yes.
                 (goto-char (point-max))
                 (forward-line -8)
                 ;; Use string-equal, not equal, to ignore text props.
                 (if (not (or (string-equal nodename "*")
                              (not
                               (search-forward "\^_\nEnd tag table\n" nil t))))
                     (let (pos)
                       ;; We have a tag table.  Find its beginning.
                       ;; Is this an indirect file?
                       (search-backward "\nTag table:\n")
                       (setq pos  (point))
                       (if (save-excursion (forward-line 2) (looking-at "(Indirect)\n"))
                           ;; It is indirect.  Copy it to another buffer
                           ;; and record that the tag table is in that buffer.
                           (let ((buf     (current-buffer))
                                 (tagbuf  (or Info-tag-table-buffer
                                              (generate-new-buffer " *info tag table*"))))
                             (setq Info-tag-table-buffer  tagbuf)
                             (with-current-buffer tagbuf
                               (buffer-disable-undo (current-buffer))
                               (setq case-fold-search  t)
                               (erase-buffer)
                               (insert-buffer-substring buf))
                             (set-marker Info-tag-table-marker (match-end 0) tagbuf))
                         (set-marker Info-tag-table-marker pos)))
                   (set-marker Info-tag-table-marker nil))
                 (setq Info-current-file  (if (eq filename t) "dir" filename))))
           ;; Use string-equal, not equal, to ignore text props.
           (if (string-equal nodename "*")
               (progn (setq Info-current-node  nodename)
                      (Info-set-mode-line))
             ;; Possibilities:
             ;;
             ;; 1. Anchor found in tag table
             ;; 2. Anchor *not* in tag table
             ;;
             ;; 3. Node found in tag table
             ;; 4. Node *not* found in tag table, but found in file
             ;; 5. Node *not* in tag table, and *not* in file
             ;;
             ;; *Or* the same, but in an indirect subfile.

             ;; Search file for a suitable node.
             (let ((guesspos  (point-min))
                   (regexp    (concat "\\(Node:\\|Ref:\\) *\\(" (regexp-quote nodename)
                                      "\\) *[,\t\n\177]"))
                   (nodepos   nil))

               ;; First, search a tag table, if any
               (if (marker-position Info-tag-table-marker)
                   (let ((found-in-tag-table  t)
                         found-anchor found-mode
                         (m                   Info-tag-table-marker))
                     (with-current-buffer (marker-buffer m)
                       (save-excursion
                         (goto-char m)
                         (beginning-of-line) ; so re-search will work.
                         
                         ;; Search tag table
                         (catch 'foo
                           (while (re-search-forward regexp nil t)
                             (setq found-anchor  (string-equal "Ref:" (match-string 1)))
                             (or nodepos (setq nodepos (point))
                                 (and (string-equal (match-string 2) nodename) (throw 'foo t))))
                           (if nodepos (goto-char nodepos) (setq found-in-tag-table  nil)))
                         (when found-in-tag-table (setq guesspos  (1+ (read (current-buffer)))))
                         (setq found-mode  major-mode)))

                     ;; Indirect file among split files
                     (if found-in-tag-table
                         (progn
                           ;; If this is an indirect file, determine
                           ;; which file really holds this node and
                           ;; read it in.
                           (if (not (eq found-mode 'Info-mode))
                               ;; Note that the current buffer must be
                               ;; the *info* buffer on entry to
                               ;; Info-read-subfile.  Thus the hackery
                               ;; above.
                               (setq guesspos  (Info-read-subfile guesspos)))))

                     ;; Handle anchor
                     (if found-anchor
                         (goto-char (setq anchorpos guesspos))

                       ;; Else we may have a node, which we search for:
                       (goto-char (max (point-min) (- (byte-to-position guesspos) 1000)))
                       ;; Now search from our advised position
                       ;; (or from beg of buffer)
                       ;; to find the actual node.
                       ;; First, check whether the node is right
                       ;; where we are, in case the buffer begins
                       ;; with a node.
                       (setq nodepos  nil)
                       (or (and (string< "20.5" emacs-version) (Info-node-at-bob-matching regexp))
                           (catch 'foo
                             (while (search-forward "\n\^_" nil t)
                               (forward-line 1)
                               (let ((beg  (point)))
                                 (forward-line 1)
                                 (when (re-search-backward regexp beg t)
                                   (if (string-equal (match-string 2) nodename)
                                       (progn (beginning-of-line) (throw 'foo t))
                                     (unless nodepos (setq nodepos  (point)))))))
                             (if nodepos
                                 (progn (goto-char nodepos) (beginning-of-line))
                               (error "No such anchor in tag table or node in tag table \
or file: `%s'"
                                      nodename))))))
                 (goto-char (max (point-min) (- guesspos 1000)))
                 ;; Now search from our advised position (or from beg of buffer)
                 ;; to find the actual node.
                 ;; First, check whether the node is right where we are, in case
                 ;; the buffer begins with a node.
                 (setq nodepos  nil)
                 (or (and (string< "20.5" emacs-version)
                          (Info-node-at-bob-matching regexp))
                     (catch 'foo
                       (while (search-forward "\n\^_" nil t)
                         (forward-line 1)
                         (let ((beg  (point)))
                           (forward-line 1)
                           (when (re-search-backward regexp beg t)
                             (if (string-equal (match-string 2) nodename)
                                 (throw 'foo t)
                               (unless nodepos (setq nodepos  (point)))))))
                       (if nodepos (goto-char nodepos) (error "No such node: `%s'" nodename))))))
             (Info-select-node)
             (goto-char (or anchorpos (point-min))))
           (when (and (one-window-p t) (not (window-minibuffer-p))
                      (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                      Info-fit-frame-flag)
             (fit-frame)))
      ;; If we did not finish finding the specified node,
      ;; go back to the previous one.
      (or Info-current-node no-going-back (null Info-history)
          (let ((hist  (car Info-history)))
            (setq Info-history  (cdr Info-history))
            (Info-find-node (nth 0 hist) (nth 1 hist) t)
            (goto-char (nth 2 hist)))))))


;; REPLACE ORIGINAL in `info.el':
;; Call `fit-frame' if `Info-fit-frame-flag'.
;;
(when (eq emacs-major-version 21)
  (defun Info-find-node-2 (filename nodename &optional no-going-back)
    (buffer-disable-undo (current-buffer))
    (or (eq major-mode 'Info-mode)
        (Info-mode))
    (widen)
    (setq Info-current-node  nil)
    (unwind-protect
         (let ((case-fold-search  t)
               anchorpos)
           ;; Switch files if necessary
           (or (null filename)
               (equal Info-current-file filename)
               (let ((buffer-read-only  nil))
                 (setq Info-current-file              nil
                       Info-current-subfile           nil
                       Info-current-file-completions  ()
                       buffer-file-name               nil)
                 (erase-buffer)
                 (if (eq filename t)
                     (Info-insert-dir)
                   (info-insert-file-contents filename t)
                   (setq default-directory  (file-name-directory filename)))
                 (set-buffer-modified-p nil)
                 ;; See whether file has a tag table.  Record the location if yes.
                 (goto-char (point-max))
                 (forward-line -8)
                 ;; Use string-equal, not equal, to ignore text props.
                 (if (not (or (string-equal nodename "*")
                              (not (search-forward "\^_\nEnd tag table\n" nil t))))
                     (let (pos)
                       ;; We have a tag table.  Find its beginning.
                       ;; Is this an indirect file?
                       (search-backward "\nTag table:\n")
                       (setq pos  (point))
                       (if (save-excursion
                             (forward-line 2)
                             (looking-at "(Indirect)\n"))
                           ;; It is indirect.  Copy it to another buffer
                           ;; and record that the tag table is in that buffer.
                           (let ((buf     (current-buffer))
                                 (tagbuf  (or Info-tag-table-buffer
                                              (generate-new-buffer " *info tag table*"))))
                             (setq Info-tag-table-buffer  tagbuf)
                             (with-current-buffer tagbuf
                               (buffer-disable-undo (current-buffer))
                               (setq case-fold-search  t)
                               (erase-buffer)
                               (insert-buffer-substring buf))
                             (set-marker Info-tag-table-marker (match-end 0) tagbuf))
                         (set-marker Info-tag-table-marker pos)))
                   (set-marker Info-tag-table-marker nil))
                 (setq Info-current-file  (if (eq filename t) "dir" filename))))
           ;; Use string-equal, not equal, to ignore text props.
           (if (string-equal nodename "*")
               (progn (setq Info-current-node  nodename) (Info-set-mode-line))
             ;; Possibilities:
             ;;
             ;; 1. Anchor found in tag table
             ;; 2. Anchor *not* in tag table
             ;;
             ;; 3. Node found in tag table
             ;; 4. Node *not* found in tag table, but found in file
             ;; 5. Node *not* in tag table, and *not* in file
             ;;
             ;; *Or* the same, but in an indirect subfile.

             ;; Search file for a suitable node.
             (let ((guesspos  (point-min))
                   (regexp    (concat "\\(Node:\\|Ref:\\) *\\(" (if (stringp nodename)
                                                                    (regexp-quote nodename)
                                                                  "")
                                      "\\) *[,\t\n\177]"))
                   (nodepos   nil))

               (catch 'foo

                 ;; First, search a tag table, if any
                 (when (marker-position Info-tag-table-marker)
                   (let* ((m      Info-tag-table-marker)
                          (found  (Info-find-in-tag-table m regexp)))
                     (when found
                       ;; FOUND is (ANCHOR POS MODE).
                       (setq guesspos  (nth 1 found))

                       ;; If this is an indirect file, determine which
                       ;; file really holds this node and read it in.
                       (unless (eq (nth 2 found) 'Info-mode)
                         ;; Note that the current buffer must be the
                         ;; *info* buffer on entry to
                         ;; Info-read-subfile.  Thus the hackery above.
                         (setq guesspos  (Info-read-subfile guesspos)))

                       ;; Handle anchor
                       (when (nth 0 found)
                         (goto-char (setq anchorpos guesspos)) (throw 'foo t)))))

                 ;; Else we may have a node, which we search for:
                 (goto-char (max (point-min) (- (byte-to-position guesspos) 1000)))

                 ;; Now search from our advised position (or from beg of
                 ;; buffer) to find the actual node.  First, check
                 ;; whether the node is right where we are, in case the
                 ;; buffer begins with a node.
                 (let ((pos  (Info-find-node-in-buffer regexp)))
                   (when pos (goto-char pos) (throw 'foo t))
                   (error "No such anchor in tag table or node in tag table or file: %s" nodename)))
               (Info-select-node)
               (goto-char (or anchorpos (point-min)))))
           (when (and (one-window-p t) (not (window-minibuffer-p))
                      (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                      Info-fit-frame-flag)
             (fit-frame)))
      ;; If we did not finish finding the specified node,
      ;; go back to the previous one.
      (or Info-current-node no-going-back (null Info-history)
          (let ((hist  (car Info-history)))
            (setq Info-history  (cdr Info-history))
            (Info-find-node (nth 0 hist) (nth 1 hist) t)
            (goto-char (nth 2 hist)))))))



;; REPLACE ORIGINAL in `info.el':
;; Call `fit-frame' if `Info-fit-frame-flag'.
;;
(when (= emacs-major-version 22)
  (defun Info-find-node-2 (filename nodename &optional no-going-back)
    (buffer-disable-undo (current-buffer))
    (or (eq major-mode 'Info-mode)
        (Info-mode))
    (widen)
    (setq Info-current-node  nil)
    (unwind-protect
         (let ((case-fold-search  t)
               anchorpos)
           ;; Switch files if necessary
           (or (null filename)
               (equal Info-current-file filename)
               (let ((buffer-read-only  nil))
                 (setq Info-current-file              nil
                       Info-current-subfile           nil
                       Info-current-file-completions  ()
                       buffer-file-name               nil)
                 (erase-buffer)
                 (cond
                   ((eq filename t) (Info-insert-dir))
                   ((eq filename 'apropos) (insert-buffer-substring " *info-apropos*"))
                   ((eq filename 'history) (insert-buffer-substring " *info-history*"))
                   ((eq filename 'toc) (insert-buffer-substring " *info-toc*"))
                   (t (info-insert-file-contents filename nil)
                      (setq default-directory  (file-name-directory filename))))
                 (set-buffer-modified-p nil)
              
                 ;; Check makeinfo version for index cookie support
                 (let ((found  nil))
                   (goto-char (point-min))
                   (condition-case ()
                       (if (and (re-search-forward
                                 "makeinfo[ \n]version[ \n]\\([0-9]+.[0-9]+\\)"
                                 (line-beginning-position 3) t)
                                (not (version< (match-string 1) "4.7")))
                           (setq found  t))
                     (error nil))
                   (set (make-local-variable 'Info-file-supports-index-cookies) found))
              
                 ;; See whether file has a tag table.  Record the location if yes.
                 (goto-char (point-max))
                 (forward-line -8)
                 ;; Use string-equal, not equal, to ignore text props.
                 (if (not (or (string-equal nodename "*")
                              (not (search-forward "\^_\nEnd tag table\n" nil t))))
                     (let (pos)
                       ;; We have a tag table.  Find its beginning.
                       ;; Is this an indirect file?
                       (search-backward "\nTag table:\n")
                       (setq pos  (point))
                       (if (save-excursion (forward-line 2) (looking-at "(Indirect)\n"))
                           ;; It is indirect.  Copy it to another buffer
                           ;; and record that the tag table is in that buffer.
                           (let ((buf     (current-buffer))
                                 (tagbuf  (or Info-tag-table-buffer
                                              (generate-new-buffer " *info tag table*"))))
                             (setq Info-tag-table-buffer  tagbuf)
                             (with-current-buffer tagbuf
                               (buffer-disable-undo (current-buffer))
                               (setq case-fold-search  t)
                               (erase-buffer)
                               (insert-buffer-substring buf))
                             (set-marker Info-tag-table-marker (match-end 0) tagbuf))
                         (set-marker Info-tag-table-marker pos)))
                   (set-marker Info-tag-table-marker nil))
                 (setq Info-current-file  (cond ((eq filename t) "dir")
                                                (t filename)))))

           ;; Use string-equal, not equal, to ignore text props.
           (if (string-equal nodename "*")
               (progn (setq Info-current-node nodename) (Info-set-mode-line))
             ;; Possibilities:
             ;;
             ;; 1. Anchor found in tag table
             ;; 2. Anchor *not* in tag table
             ;;
             ;; 3. Node found in tag table
             ;; 4. Node *not* found in tag table, but found in file
             ;; 5. Node *not* in tag table, and *not* in file
             ;;
             ;; *Or* the same, but in an indirect subfile.

             ;; Search file for a suitable node.
             (let ((guesspos  (point-min))
                   (regexp    (concat "\\(Node:\\|Ref:\\) *\\(" (if (stringp nodename)
                                                                    (regexp-quote nodename)
                                                                  "")
                                      "\\) *[,\t\n\177]")))

               (catch 'foo

                 ;; First, search a tag table, if any
                 (when (marker-position Info-tag-table-marker)
                   (let* ((m      Info-tag-table-marker)
                          (found  (Info-find-in-tag-table m regexp)))

                     (when found
                       ;; FOUND is (ANCHOR POS MODE).
                       (setq guesspos  (nth 1 found))

                       ;; If this is an indirect file, determine which
                       ;; file really holds this node and read it in.
                       (unless (eq (nth 2 found) 'Info-mode)
                         ;; Note that the current buffer must be the
                         ;; *info* buffer on entry to
                         ;; Info-read-subfile.  Thus the hackery above.
                         (setq guesspos  (Info-read-subfile guesspos)))

                       ;; Handle anchor
                       (when (nth 0 found)
                         (goto-char (setq anchorpos guesspos)) (throw 'foo t)))))

                 ;; Else we may have a node, which we search for:
                 (goto-char (max (point-min) (- (byte-to-position guesspos) 1000)))

                 ;; Now search from our advised position (or from beg of
                 ;; buffer) to find the actual node.  First, check
                 ;; whether the node is right where we are, in case the
                 ;; buffer begins with a node.
                 (let ((pos  (Info-find-node-in-buffer regexp)))
                   (when pos (goto-char pos) (throw 'foo t)))

                 (when (string-match "\\([^.]+\\)\\." nodename)
                   (let (Info-point-loc)
                     (Info-find-node-2 filename (match-string 1 nodename) no-going-back))
                   (widen)
                   (throw 'foo t))

                 ;; No such anchor in tag table or node in tag table or file
                 (error "No such node or anchor: %s" nodename))

               (Info-select-node)
               (goto-char (point-min))
               (cond (anchorpos
                      (let ((new-history  (list Info-current-file (substring-no-properties nodename))))
                        ;; Add anchors to the history too
                        (setq Info-history-list  (cons new-history
                                                       (delete new-history Info-history-list))))
                      (goto-char anchorpos))
                     ((numberp Info-point-loc)
                      (forward-line (1- Info-point-loc))
                      (setq Info-point-loc  nil))
                     ((stringp Info-point-loc)
                      (Info-find-index-name Info-point-loc)
                      (setq Info-point-loc  nil)))
               (when (and (one-window-p t) (not (window-minibuffer-p))
                          (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                          Info-fit-frame-flag)
                 (fit-frame)))))
      ;; If we did not finish finding the specified node,
      ;; go back to the previous one.
      (or Info-current-node no-going-back (null Info-history)
          (let ((hist  (car Info-history)))
            (setq Info-history  (cdr Info-history))
            (Info-find-node (nth 0 hist) (nth 1 hist) t)
            (goto-char (nth 2 hist)))))))



;; REPLACE ORIGINAL in `info.el':
;; Call `fit-frame' if `Info-fit-frame-flag'.
;;
(when (> emacs-major-version 22)
  (defun Info-find-node-2 (filename nodename &optional no-going-back)
    (buffer-disable-undo (current-buffer))
    (or (eq major-mode 'Info-mode) (Info-mode))
    (widen)
    (setq Info-current-node  nil)
    (unwind-protect
         (let ((case-fold-search  t)
               (virtual-fun       (and (fboundp 'Info-virtual-fun) ; Emacs 23.2.
                                       (Info-virtual-fun 'find-node
                                                         (or filename Info-current-file)
                                                         nodename)))
               anchorpos)
           (cond ((functionp virtual-fun)
                  (let ((filename  (or filename Info-current-file)))
                    (setq buffer-read-only               nil
                          Info-current-file              filename
                          Info-current-subfile           nil
                          Info-current-file-completions  ()
                          buffer-file-name               nil)
                    (erase-buffer)
                    (Info-virtual-call virtual-fun filename nodename no-going-back)
                    (set-marker Info-tag-table-marker nil)
                    (setq buffer-read-only  t)
                    (set-buffer-modified-p nil)
                    (set (make-local-variable 'Info-current-node-virtual) t)))
                 ((not (and (or (not (boundp 'Info-current-node-virtual))
                                (not Info-current-node-virtual))
                            (or (null filename) (equal Info-current-file filename))))
                  ;; Switch files if necessary
                  (let ((inhibit-read-only  t))
                    (when (and (boundp 'Info-current-node-virtual) Info-current-node-virtual)
                      ;; When moving from a virtual node.
                      (set (make-local-variable 'Info-current-node-virtual) nil)
                      (unless filename (setq filename  Info-current-file)))
                    (setq Info-current-file              nil
                          Info-current-subfile           nil
                          Info-current-file-completions  ()
                          buffer-file-name               nil)
                    (erase-buffer)
                    (cond ((eq filename t)        (Info-insert-dir))
                          ((eq filename 'apropos) (insert-buffer-substring " *info-apropos*"))
                          ((eq filename 'history) (insert-buffer-substring " *info-history*"))
                          ((eq filename 'toc)     (insert-buffer-substring " *info-toc*"))
                          (t (info-insert-file-contents filename nil)
                             (setq default-directory  (file-name-directory filename))))
                    (set-buffer-modified-p nil)
                    (set (make-local-variable 'Info-file-supports-index-cookies)
                         (Info-file-supports-index-cookies filename))
                    
                    ;; See whether file has a tag table.  Record the location if yes.
                    (goto-char (point-max))
                    (forward-line -8)
                    ;; Use string-equal, not equal, to ignore text props.
                    (if (not (or (string-equal nodename "*")
                                 (not (search-forward "\^_\nEnd tag table\n" nil t))))
                        (let (pos)
                          ;; We have a tag table.  Find its beginning.
                          ;; Is this an indirect file?
                          (search-backward "\nTag table:\n")
                          (setq pos  (point))
                          (if (save-excursion (forward-line 2) (looking-at "(Indirect)\n"))
                              ;; It is indirect.  Copy it to another buffer
                              ;; and record that the tag table is in that buffer.
                              (let ((buf     (current-buffer))
                                    (tagbuf  (or Info-tag-table-buffer
                                                 (generate-new-buffer " *info tag table*"))))
                                (setq Info-tag-table-buffer  tagbuf)
                                (with-current-buffer tagbuf
                                  (buffer-disable-undo (current-buffer))
                                  (setq case-fold-search  t)
                                  (erase-buffer)
                                  (insert-buffer-substring buf))
                                (set-marker Info-tag-table-marker (match-end 0) tagbuf))
                            (set-marker Info-tag-table-marker pos)))
                      (set-marker Info-tag-table-marker nil))
                    (setq Info-current-file  filename))))
           ;; Use string-equal, not equal, to ignore text props.
           (if (string-equal nodename "*")
               (progn (setq Info-current-node  nodename) (Info-set-mode-line))
             ;; Possibilities:
             ;;
             ;; 1. Anchor found in tag table
             ;; 2. Anchor *not* in tag table
             ;;
             ;; 3. Node found in tag table
             ;; 4. Node *not* found in tag table, but found in file
             ;; 5. Node *not* in tag table, and *not* in file
             ;;
             ;; *Or* the same, but in an indirect subfile.
             ;;
             ;;
             ;; Search file for a suitable node.
             (let ((guesspos  (point-min))
                   (regexp    (concat "\\(Node:\\|Ref:\\) *\\("  (if (stringp nodename)
                                                                     (regexp-quote nodename)
                                                                   "")
                                      "\\) *[,\t\n\177]")))
               (catch 'foo
                 ;; First, search a tag table, if any
                 (when (marker-position Info-tag-table-marker)
                   (let* ((m      Info-tag-table-marker)
                          (found  (Info-find-in-tag-table m regexp)))
                     (when found
                       ;; FOUND is (ANCHOR POS MODE).
                       (setq guesspos  (nth 1 found))
                       ;; If this is an indirect file, determine which
                       ;; file really holds this node and read it in.
                       (unless (eq (nth 2 found) 'Info-mode)
                         ;; Note that the current buffer must be the
                         ;; *info* buffer on entry to
                         ;; Info-read-subfile.  Thus the hackery above.
                         (setq guesspos  (Info-read-subfile guesspos)))
                       ;; Handle anchor
                       (when (nth 0 found)
                         (goto-char (setq anchorpos  guesspos)) (throw 'foo t)))))
                 ;; Else we may have a node, which we search for:
                 (goto-char (max (point-min) (- (byte-to-position guesspos) 1000)))
                 ;; Now search from our advised position (or from beg of
                 ;; buffer) to find the actual node.  First, check
                 ;; whether the node is right where we are, in case the
                 ;; buffer begins with a node.
                 (let ((pos  (Info-find-node-in-buffer regexp)))
                   (when pos (goto-char pos) (throw 'foo t)))
                 (when (string-match "\\([^.]+\\)\\." nodename)
                   (let (Info-point-loc)
                     (Info-find-node-2 filename (match-string 1 nodename) no-going-back))
                   (widen)
                   (throw 'foo t))
                 ;; No such anchor in tag table or node in tag table or file
                 (error "No such node or anchor: %s" nodename))
               (Info-select-node)
               (goto-char (point-min))
               (forward-line 1)         ; skip header line
               (when (and (not (fboundp 'Info-breadcrumbs)) ; Before Emacs 23.2
                          Info-breadcrumbs-in-header-flag
                          (> Info-breadcrumbs-depth 0))
                 (forward-line 1))      ; skip breadcrumbs line
               (cond (anchorpos
                      (let ((new-history  (list Info-current-file (substring-no-properties nodename))))
                        ;; Add anchors to the history too
                        (setq Info-history-list  (cons new-history
                                                       (delete new-history Info-history-list))))
                      (goto-char anchorpos))
                     ((numberp Info-point-loc)
                      (forward-line (- Info-point-loc 2))
                      (setq Info-point-loc  nil))
                     ((stringp Info-point-loc)
                      (Info-find-index-name Info-point-loc)
                      (setq Info-point-loc  nil)))))
           (when (and (one-window-p t) (not (window-minibuffer-p))
                      (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                      Info-fit-frame-flag)
             (fit-frame)))
      ;; If we did not finish finding the specified node,
      ;; go back to the previous one.
      (or Info-current-node no-going-back (null Info-history)
          (let ((hist  (car Info-history)))
            (setq Info-history  (cdr Info-history))
            (Info-find-node (nth 0 hist) (nth 1 hist) t)
            (goto-char (nth 2 hist)))))
    (Info-set-mode-line)))



;; REPLACE ORIGINAL in `info.el':
;;
;; Handle `Info-breadcrumbs-in-mode-line-mode'.
;;
(when (> emacs-major-version 22)
  (defun Info-set-mode-line ()
    "Set the Info mode line.
If `Info-breadcrumbs-in-mode-line-mode' is non-nil, insert breadcrumbs."
    (if Info-breadcrumbs-in-mode-line-mode
        (Info-insert-breadcrumbs-in-mode-line)
      (setq mode-line-buffer-identification
            (nconc (propertized-buffer-identification "%b")
                   (list
                    (concat
                     " ("
                     (if (stringp Info-current-file)
                         (replace-regexp-in-string
                          "%" "%%" (file-name-nondirectory Info-current-file))
                       (format "*%S*" Info-current-file))
                     ") "
                     (if Info-current-node
                         (propertize (replace-regexp-in-string
                                      "%" "%%" Info-current-node)
                                     'face 'mode-line-buffer-id
                                     'help-echo
                                     "mouse-1: scroll forward, mouse-3: scroll back"
                                     'mouse-face 'mode-line-highlight
                                     'local-map Info-mode-line-node-keymap)
                       ""))))))))

(when (> emacs-major-version 22)
  (defun Info-insert-breadcrumbs-in-mode-line ()
    (let ((nodes   (Info-toc-nodes Info-current-file))
          (node    Info-current-node)
          (crumbs  ())
          (depth   Info-breadcrumbs-depth-internal)
          (text    ""))
      ;; Get ancestors from the cached parent-children node info
      (while (and (not (equal "Top" node)) (> depth 0))
        (setq node  (nth 1 (assoc node nodes)))
        (when node (push node crumbs))
        (setq depth  (1- depth)))
      ;; Add bottom node.
      (setq crumbs  (nconc crumbs (list Info-current-node)))
      (when crumbs
        ;; Add top node (and continuation if needed).
        (setq crumbs  (cons "Top" (if (member (pop crumbs) '(nil "Top"))
                                      crumbs
                                    (cons nil crumbs))))
        (dolist (node  crumbs)
          (let ((crumbs-map  (make-sparse-keymap))
                (menu-map    (make-sparse-keymap "Breadcrumbs in Mode Line")))
            (define-key crumbs-map [mode-line mouse-3] menu-map)
            (when node
              (define-key menu-map [Info-prev]
                `(menu-item "Previous Node" Info-prev
                  :visible ,(Info-check-pointer "prev[ious]*") :help "Go to the previous node"))
              (define-key menu-map [Info-next]
                `(menu-item "Next Node" Info-next
                  :visible ,(Info-check-pointer "next") :help "Go to the next node"))
              (define-key menu-map [separator] '("--"))
              (define-key menu-map [Info-breadcrumbs-in-mode-line-mode]
                `(menu-item "Toggle Breadcrumbs" Info-breadcrumbs-in-mode-line-mode
                  :help "Toggle displaying breadcrumbs in the Info mode-line"
                  :button (:toggle . Info-breadcrumbs-in-mode-line-mode)))
              (define-key menu-map [Info-set-breadcrumbs-depth]
                `(menu-item "Set Breadcrumbs Depth" Info-set-breadcrumbs-depth
                  :help "Set depth of breadcrumbs to show in the mode-line"))
              (setq node  (if (equal node Info-current-node)
                              (propertize
                               (replace-regexp-in-string "%" "%%" Info-current-node)
                               'face 'mode-line-buffer-id
                               'help-echo "mouse-1: Scroll back, mouse-2: Scroll forward, mouse-3: Menu"
                               'mouse-face 'mode-line-highlight
                               'local-map
                               (progn
                                 (define-key crumbs-map [mode-line mouse-1] 'Info-mouse-scroll-down)
                                 (define-key crumbs-map [mode-line mouse-2] 'Info-mouse-scroll-up)
                                      crumbs-map))
                            (propertize
                             node
                             'local-map (progn (define-key crumbs-map [mode-line mouse-1]
                                                 `(lambda () (interactive) (Info-goto-node ,node)))
                                               (define-key crumbs-map [mode-line mouse-2]
                                                 `(lambda () (interactive) (Info-goto-node ,node)))
                                               crumbs-map)
                             'mouse-face 'mode-line-highlight
                             'help-echo "mouse-1, mouse-2: Go to this node; mouse-3: Menu")))))
          (let ((nodetext  (if (not (equal node "Top"))
                               node
                             (concat (format "(%s)" (if (stringp Info-current-file)
                                                        (file-name-nondirectory Info-current-file)
                                                      ;; Some legacy code can still use a symbol.
                                                      Info-current-file))
                                     node))))
            (setq text  (concat text (if (equal node "Top") "" " > ") (if node nodetext "...")))))
        (make-local-variable 'mode-line-format) ; Needed for Emacs 21+.
        (setq mode-line-format  text)))))



;; REPLACE ORIGINAL in `info.el':
;; BUG FIX (bug reported 2008-10-04).
;; 1. Match closing paren, if present.
;; 2. If only opening paren and CODE = t, then wrap each file name in ().
;;
(when (> emacs-major-version 22)
  (defun Info-read-node-name-1 (string predicate code)
    (cond ((string-match "\\`(\\([^)]*\\))\\'" string) ; e.g. (emacs) or (emacs-mime)
           (cond ((eq code nil) string)
                 ((eq code t) (list string))
                 (t t)))
          ((string-match "\\`(\\([^)]*\\)\\'" string) ; e.g. (emacs
           (let ((ctwc  (completion-table-with-context
                         "("
                         (apply-partially
                          'completion-table-with-terminator ")"
                          (apply-partially 'Info-read-node-name-2
                                           Info-directory-list
                                           (mapcar 'car Info-suffix-list)))
                         (match-string 1 string)
                         predicate
                         code)))
             (cond ((eq code nil) ctwc)
                   ((eq code t) (mapcar (lambda (file) (concat "(" file ")")) ctwc))
                   (t t))))
          ((string-match "\\`(" string) ; e.g. (emacs)Mac OS or (jlkj - just punt.
           (cond ((eq code nil) string)
                 ((eq code t) nil)
                 (t t)))
          ;; Otherwise use Info-read-node-completion-table - e.g. Mac OS
          (t (complete-with-action code Info-read-node-completion-table string predicate)))))



;; REPLACE ORIGINAL in `info.el':
;; BUG FIX (bug reported 2008-10-04).
;; 1. Match closing paren, if present.
;; 2. If only opening paren and CODE = t, then wrap each file name in ().
;;
(when (= emacs-major-version 22)
  (defun Info-read-node-name-1 (string predicate code)
    (cond ((string-match "\\`(\\([^)]*\\))\\'" string) ; e.g. (emacs) or (emacs-mime)
           (cond ((eq code nil) string)
                 ((eq code t) (list string))
                 (t t)))
          ((string-match "\\`(\\([^)]*\\)\\'" string) ; e.g. (emacs
           (let ((file  (match-string 1 string)))
             (cond ((eq code nil)
                    (let ((comp  (try-completion file 'Info-read-node-name-2
                                                 (cons Info-directory-list
                                                       (mapcar #'car Info-suffix-list)))))
                      (cond ((eq comp t) (concat string ")"))
                            (comp (concat "(" comp)))))
                   ((eq code t)
                    (mapcar (lambda (file) (concat "(" file ")"))
                            (all-completions file 'Info-read-node-name-2
                                             (cons Info-directory-list
                                                   (mapcar #'car Info-suffix-list)))))
                   (t nil))))
          ((string-match "\\`(" string) ; e.g. (emacs)Mac OS or (jlkj - just punt.
           (cond ((eq code nil) string)
                 ((eq code t) nil)
                 (t t)))
          ;; Otherwise use Info-read-node-completion-table - e.g. Mac OS
          ((eq code nil)
           (try-completion string Info-read-node-completion-table predicate))
          ((eq code t)
           (all-completions string Info-read-node-completion-table predicate))
          (t (test-completion string Info-read-node-completion-table predicate)))))



(when (< emacs-major-version 22)

  ;; REPLACE ORIGINAL in `info.el':
  ;; 1. Match closing paren, if present.
  ;; 2. If only opening paren and CODE = t, then wrap each file name in ().
  ;;
  (defun Info-read-node-name-1 (string predicate code)
    (cond ((string-match "\\`(\\([^)]*\\))\\'" string) ; e.g. (emacs) or (emacs-mime)
           (cond ((eq code nil) string)
                 ((eq code t) (list string))
                 (t t)))
          ((string-match "\\`(\\([^)]*\\)\\'" string) ; e.g. (emacs
           (let ((file  (match-string 1 string)))
             (cond ((eq code nil)
                    (let ((comp  (try-completion file 'Info-read-node-name-2
                                                 (cons Info-directory-list
                                                       (mapcar #'car Info-suffix-list)))))
                      (cond ((eq comp t) (concat string ")"))
                            (comp (concat "(" comp)))))
                   ((eq code t)
                    (mapcar (lambda (file) (concat "(" file ")"))
                            (all-completions file 'Info-read-node-name-2
                                             (cons Info-directory-list
                                                   (mapcar #'car Info-suffix-list)))))
                   (t nil))))
          ((eq code nil) (try-completion string Info-read-node-completion-table predicate))
          ((eq code t) (all-completions string Info-read-node-completion-table predicate))
          (t (assoc string Info-read-node-completion-table))))

  ;; Adapted from Emacs 22 `Info-read-node-name-2' (there is normally no such function for 20, 21).
  (defun Info-read-node-name-2 (string path-and-suffixes action)
    "Virtual completion table for file names input in Info node names.
PATH-AND-SUFFIXES is a pair of lists, (DIRECTORIES . SUFFIXES)."
    (let* ((names       ())
           (suffixes    (remove "" (cdr path-and-suffixes)))
           (suffix      (concat (regexp-opt suffixes t) "\\'"))
           (string-dir  (file-name-directory string))
           (dirs        (if (file-name-absolute-p string)
                            (list (file-name-directory string))
                          (car path-and-suffixes))))
      (dolist (dir  dirs)
        (unless dir (setq dir  default-directory))
        (if string-dir (setq dir  (expand-file-name string-dir dir)))
        (when (file-directory-p dir)
          (dolist (file  (file-name-all-completions (file-name-nondirectory string) dir))
            ;; If the file name has no suffix or a standard suffix, include it.
            (and (or (null (file-name-extension file)) (string-match suffix file))
                 ;; But exclude subfiles of split Info files.
                 (not (string-match "-[0-9]+\\'" file))
                 ;; And exclude backup files.
                 (not (string-match "~\\'" file))
                 (push (if string-dir (concat string-dir file) file) names))
            ;; If the file name ends in a standard suffix,
            ;; add the unsuffixed name as a completion option.
            (when (string-match suffix file)
              (setq file  (substring file 0 (match-beginning 0)))
              (push (if string-dir (concat string-dir file) file) names)))))
      (cond ((eq action t) (all-completions string (mapcar #'list names)))
            ((null action) (try-completion string (mapcar #'list names)))
            (t             (assoc string Info-read-node-completion-table))))))



;; REPLACE ORIGINAL in `info.el':
;; 1. Added in-progress message ("Looking...")
;; 2, Return nil if not found.
;;
(defun Info-find-emacs-command-nodes (command)
  "Return a list of locations documenting COMMAND.
The `info-file' property of COMMAND says which Info manual to search.
If COMMAND has no property, the variable `Info-file-list-for-emacs'
defines heuristics for which Info manual to try.
The locations are of the format used in variable `Info-history', that
is, (FILENAME NODENAME BUFFERPOS\)."
  (let ((where     ())
        (cmd-desc  (concat "^\\* +" (regexp-quote (symbol-name command))
                           (if (< emacs-major-version 21)
                               ":\\s *\\(.*\\)\\.$"
                             "\\( <[0-9]+>\\)?:\\s *\\(.*\\)\\.$")))
        (info-file "emacs"))            ;default
    ;; Determine which info file this command is documented in.
    (if (get command 'info-file)
        (setq info-file  (get command 'info-file))
      ;; If it doesn't say explicitly, test its name against
      ;; various prefixes that we know.
      (let ((file-list  Info-file-list-for-emacs))
        (while file-list
          (let* ((elt     (car file-list))
                 (name    (if (consp elt) (car elt) elt))
                 (file    (if (consp elt) (cdr elt) elt))
                 (regexp  (concat "\\`" (regexp-quote name) "\\(\\'\\|-\\)")))
            (if (string-match regexp (symbol-name command))
                (setq info-file  file
                      file-list  ()))
            (setq file-list  (cdr file-list))))))
    (message "Looking for command `%s' in Info manual `%s'..."
             command (file-name-nondirectory info-file))

    (cond ((>= emacs-major-version 22)
           (save-excursion
             (condition-case nil
                 (progn (Info-find-node info-file "Top")
                        (or (and (search-forward "\n* menu:" nil t)
                                 (re-search-forward "\n\\* \\(.*\\<Index\\>\\)" nil t))
                            (error "Info file `%s' appears to lack an index" info-file)))
               (error nil))             ; Return nil: not found.
             (goto-char (match-beginning 1))
             ;; Bind Info-history to nil, to prevent the index nodes from
             ;; getting into the node history.
             (let ((Info-history       ())
                   (Info-history-list  ())
                   node
                   (nodes              (Info-index-nodes)))
               (Info-goto-node (car nodes))
               (while
                   (progn (goto-char (point-min))
                          (while (re-search-forward cmd-desc nil t)
                            (setq where  (cons (list Info-current-file
                                                     (match-string-no-properties 2)
                                                     0)
                                               where)))
                          (and (setq nodes  (cdr nodes)
                                     node   (car nodes))))
                 (Info-goto-node node)))
             where))
          ((>= emacs-major-version 21)
           (save-excursion
             (condition-case nil
                 (progn (Info-find-node info-file "Top")
                        (or (and (search-forward "\n* menu:" nil t)
                                 (re-search-forward "\n\\* \\(.*\\<Index\\>\\)" nil t))
                            (error "Info file `%s' appears to lack an index" info-file)))
               (error nil))             ; Return nil: not found.
             (goto-char (match-beginning 1))
             ;; Bind Info-history to nil, to prevent the index nodes from
             ;; getting into the node history.
             (let ((Info-history  ())
                   (exact         nil)
                   node found)
               (Info-goto-node (Info-extract-menu-node-name))
               (while
                   (progn
                     (goto-char (point-min))
                     (while (re-search-forward cmd-desc nil t)
                       (setq where  (cons (list Info-current-file (match-string-no-properties 2) 0)
                                          where)))
                     (and (setq node  (Info-extract-pointer "next" t))
                          (string-match "\\<Index\\>" node)))
                 (Info-goto-node node)))
             where))
          (t
           (save-excursion
             (condition-case nil
                 (Info-find-node info-file "Command Index")
               ;; Some manuals may not have a separate Command Index node,
               ;; so try just Index instead.
               (error (condition-case nil
                          (Info-find-node info-file "Index")
                        (error nil))))  ; Return nil: not found.
             ;; Take the index node off the Info history.
             (setq Info-history  (cdr Info-history))
             (goto-char (point-max))
             (while (re-search-backward cmd-desc nil t)
               (setq where  (cons (list Info-current-file
                                        (buffer-substring (match-beginning 1) (match-end 1))
                                        0)
                                  where)))
             where)))))


;; REPLACES ORIGINAL in `info.el':
;; 1. Uses `completing-read' in interactive spec, with `symbol-nearest-point'
;;    (defined in `thingatpt+.el') or `symbol-at-point' (defined in `thingatpt.el').
;; 2. Message if single node found.
;; 3. Returns `num-matches' if found; nil if not.
;;
;;;###autoload
(defun Info-goto-emacs-command-node (command)
  "Go to the Info node in the Emacs manual for command COMMAND.
The command is found by looking it up in Emacs manual's indexes,
or in another manual found via COMMAND's `info-file' property or
the variable `Info-file-list-for-emacs'.
COMMAND must be a symbol or string."
  (interactive
   (let ((symb  (cond ((fboundp 'symbol-nearest-point) (symbol-nearest-point))
                      ((fboundp 'symbol-at-point)      (symbol-at-point))
                      (t nil)))
         (enable-recursive-minibuffers t))
     (list (intern (completing-read "Find documentation for command: "
                                    obarray 'commandp t nil nil (symbol-name symb) t)))))
  (unless (commandp command)
    (signal 'wrong-type-argument (list 'commandp command)))
  (let ((where  (Info-find-emacs-command-nodes command)))
    (if where
        (let ((num-matches  (length where)))
          ;; Get Info running, and pop to it in another window.
          (save-window-excursion (info))
          (or (eq major-mode 'Info-mode) (pop-to-buffer "*info*"))
          ;; Bind Info-history to nil, to prevent the last Index node
          ;; visited by Info-find-emacs-command-nodes from being
          ;; pushed onto the history.
          (let ((Info-history       ())
                (Info-history-list  ()))
            (Info-find-node (car (car where)) (car (cdr (car where)))))
          (if (<= num-matches 1)
              (when (interactive-p) (message "This info node documents command `%s'." command))

            ;; (car where) will be pushed onto Info-history
            ;; when/if they go to another node.  Put the other
            ;; nodes that were found on the history.
            (setq Info-history  (nconc (cdr where) Info-history))
            (when (interactive-p)
              (message "Found %d other entr%s.  Use %s to see %s."
                       (1- num-matches) (if (> num-matches 2) "ies" "y")
                       (substitute-command-keys (if (>= emacs-major-version 22)
                                                    "\\<Info-mode-map>\\[Info-history-back]"
                                                  "\\<Info-mode-map>\\[Info-last]"))
                       (if (> num-matches 2) "them" "it"))))
          num-matches)                  ; Return num-matches found.
      (and (interactive-p)              ; Return nil for unfound.
           (error "No documentation found for command `%s'" command)))))


;; REPLACES ORIGINAL in `info.el':
;; If key's command is not found, then `Info-search' for key sequence in text.
;; Message for repeating.
;;
;;;###autoload
(defun Info-goto-emacs-key-command-node (key)
  "Go to the node in the Emacs manual describing command bound to KEY.
KEY is a string.

Interactively, if the binding is `execute-extended-command', then a
command is read.

The command is found by looking it up in Emacs manual's indexes,
or in another manual's index found via COMMAND's `info-file' property
or the variable `Info-file-list-for-emacs'.

If key's command cannot be found by looking in indexes, then
`Info-search' is used to search for the key sequence in the info text."
  (interactive "kFind documentation for key: ")
  (let ((command  (lookup-key global-map key))
        (pp-key   (key-description key)))
    (when (natnump command) (setq command  (key-binding key))) ; E.g. menu item.
    (cond ((null command)
           (when (interactive-p) (message "No doc found for key sequence `%s'." pp-key))
           nil)                         ; RETURN nil: not found.
          ((and (interactive-p) (eq command 'execute-extended-command)) ; Read a new command name.
           (Info-goto-emacs-command-node (read-command "Find documentation for command: ")))
          (t
           (let ((this-file        Info-current-file)
                 (this-node        Info-current-node)
                 (num-cmd-matches  (Info-goto-emacs-command-node command)))
             (cond (num-cmd-matches
                    ;; Found key's command via a manual index.
                    (when (interactive-p)
                      (if (<= num-cmd-matches 1)
                          (message "This info node documents key `%s'." pp-key)
                        (message
                         (substitute-command-keys
                          (concat "Found %d other entr%s.  Use "
                                  (if (>= emacs-major-version 22)
                                      "\\<Info-mode-map>`\\[Info-history-back]' to see %s."
                                    "\\<Info-mode-map>`\\[Info-last]' to see %s.")))
                         (1- num-cmd-matches) (if (> num-cmd-matches 2) "ies" "y")
                         (if (> num-cmd-matches 2) "them" "it"))))
                    num-cmd-matches)    ; RETURN num-cmd-matches: found.
                   (t;; Couldn't find key's command via a manual index.
                    ;; Get back to where we were.
                    ;; Would be better if there were a save-xxx-excursion-xxx
                    ;; that would work.
                    (Info-goto-node (concat "(" this-file ")" this-node))
                    ;; Would be better to now try looking for the key in indexes (e.g. Key
                    ;; Index). Instead, just look for the key sequence in the text.
                    (when (interactive-p)
                      (message "Not found using Index. Searching for \"%s\" in text..." pp-key)
                      (sit-for 3))
                    (condition-case err
                        (progn
                          (Info-search (regexp-quote pp-key))
                          (when (interactive-p)
                            (message (substitute-command-keys
                                      "Use \\<Info-mode-map>`\\[Info-search] RET' \
to search again for `%s'.")
                                     pp-key))
                          t)            ; RETURN t: found.
                      (search-failed (message "No documentation found for key `%s'." pp-key)
                                     nil))))))))) ; RETURN nil: not found.


;; REPLACES ORIGINAL in `info.el':
;; 1. File name in face `info-file'.
;; 2. Node names in face `info-node'.
;; 3. Menu items in face `info-menu'.
;; 4. Only 5th and 9th menu items have their `*' colored.
;; 5. Notes in face `info-xref'.
;; 6. If `Info-fontify-quotations-flag', fontify `...' in face `info-quoted-name',
;;    "..." in face `info-string', and ' in face `info-single-quote'.
;;
(unless (> emacs-major-version 21)
  (defun Info-fontify-node ()
    (save-excursion
      (let ((buffer-read-only  nil)
            (case-fold-search  t))
        (goto-char (point-min))
        ;; Header line.
        (when (looking-at "^File: \\([^,: \t]+\\),?[ \t]+")
          (put-text-property (match-beginning 1) (match-end 1) 'face 'info-file)
          (goto-char (match-end 0))
          ;; Node names in menu at top of buffer.
          (while (looking-at "[ \t]*\\([^:, \t\n]+\\):[ \t]+\\([^:,\t\n]+\\),?")
            (goto-char (match-end 0))
            (if (save-excursion
                  (goto-char (match-beginning 1))
                  (save-match-data (looking-at "Node:")))
                (put-text-property (match-beginning 2) (match-end 2) 'face 'info-node)
              (put-text-property (match-beginning 2) (match-end 2) 'face 'info-xref)
              (put-text-property (match-beginning 2) (match-end 2) 'mouse-face 'highlight))))
        (goto-char (point-min))
        ;; Text headings: replace ***'s, ---'s, ==='s by faces.
        (while (re-search-forward "\n\\([^ \t\n].+\\)\n\\(\\*+\\|=+\\|-+\\)$"
                                  nil t)
          (put-text-property (match-beginning 1) (match-end 1)
                             'face
                             (cdr (assq (preceding-char) Info-title-face-alist)))
          ;; This is a serious problem for trying to handle multiple
          ;; frame types at once.  We want this text to be invisible
          ;; on frames that can display the font above.
          (if (memq (framep (selected-frame)) '(x pc w32 win32))
              (put-text-property (match-end 1) (match-end 2) 'invisible t)))
        (goto-char (point-min))
        ;; Cross references.
        (while (re-search-forward "\\*Note[ \n\t]+\\([^:]*\\):" nil t)
          (unless (= (char-after (1- (match-beginning 0))) ?\") ; hack
            (put-text-property (match-beginning 1) (match-end 1) 'face 'info-xref)
            (put-text-property (match-beginning 1) (match-end 1) 'mouse-face 'highlight)))
        (goto-char (point-min))
        ;; Menus.
        (when (and (search-forward "\n* Menu:" nil t)
                   ;; Fontify indexes too.
                   ;;(not (string-match "\\<Index\\>" Info-current-node))
                   ;; Don't take time to annotate huge menus
                   (< (- (point-max) (point)) Info-fontify-maximum-menu-size))
          (let ((n  0))
            (while (re-search-forward "^\\* +\\([^:\t\n]*\\):" nil t)
              (setq n  (1+ n))
              (when (memq n '(5 9))     ; visual aids to help with 1-9 keys
                (put-text-property (match-beginning 0) (1+ (match-beginning 0))
                                   'face 'info-menu)) ; was: info-menu-5
              (put-text-property (match-beginning 1) (match-end 1) 'face 'info-menu) ; was: info-xref
              (put-text-property (match-beginning 1) (match-end 1)
                                 'mouse-face 'highlight))))

        ;; Fontify `...' and "..."
        (goto-char (point-min))
        (when Info-fontify-quotations-flag (info-fontify-quotations)) ; Fontify `...' and "..."
        ;;  Fontify reference items: `-- Function:', `-- Variable:', etc.
        (goto-char (point-min))
        (when Info-fontify-reference-items-flag (info-fontify-reference-items))
        (set-buffer-modified-p nil)))))


;; REPLACES ORIGINAL in `info.el':
;; 1. File name in face `info-file'.
;; 2. If `Info-fontify-quotations-flag', fontify `...' in face `info-quoted-name',
;;    "..." in face `info-string', and ' in face `info-single-quote'.
;;
(when (= emacs-major-version 22)
  (defun Info-fontify-node ()
    "Fontify the node."
    (save-excursion
      (let* ((inhibit-read-only  t)
             (case-fold-search   t)
             paragraph-markers
             (not-fontified-p           ; the node hasn't already been fontified
              (not (let ((where  (next-property-change (point-min))))
                     (and where (not (= where (point-max)))))))
             (fontify-visited-p         ; visited nodes need to be re-fontified
              (and Info-fontify-visited-nodes
                   ;; Don't take time to refontify visited nodes in huge nodes
                   Info-fontify-maximum-menu-size
                   (< (- (point-max) (point-min)) Info-fontify-maximum-menu-size)))
             rbeg rend)

        ;; Fontify header line
        (goto-char (point-min))
        (when (and not-fontified-p (looking-at "^File: \\([^,: \t]+\\),?[ \t]+"))
          (put-text-property (match-beginning 1) (match-end 1) 'font-lock-face 'info-file))
        (goto-char (point-min))
        (when (and not-fontified-p (looking-at "^\\(File: [^,: \t]+,?[ \t]+\\)?"))
          (while (looking-at "[ \t]*\\([^:, \t\n]+\\):[ \t]+\\([^:,\t\n]+\\),?")
            (goto-char (match-end 0))
            (let* ((nbeg  (match-beginning 2))
                   (nend  (match-end 2))
                   (tbeg  (match-beginning 1))
                   (tag   (match-string 1)))
              (if (string-equal (downcase tag) "node")
                  (put-text-property nbeg nend 'font-lock-face 'info-header-node)
                (put-text-property nbeg nend 'font-lock-face 'info-header-xref)
                (put-text-property tbeg nend 'mouse-face 'highlight)
                (put-text-property tbeg nend
                                   'help-echo
                                   (concat "mouse-2: Go to node "
                                           (buffer-substring nbeg nend)))
                ;; Always set up the text property keymap.
                ;; It will either be used in the buffer
                ;; or copied in the header line.
                (put-text-property tbeg nend 'keymap
                                   (cond
                                     ((string-equal (downcase tag) "prev") Info-prev-link-keymap)
                                     ((string-equal (downcase tag) "next") Info-next-link-keymap)
                                     ((string-equal (downcase tag) "up"  ) Info-up-link-keymap))))))
          ;; Add breadcrumbs - my version.
          (unless (string= "Top" Info-current-node)
            (let ((nod     Info-current-node)
                  (onode   Info-current-node)
                  (crumbs  ())
                  (done    nil))
              (while (not done)
                (let ((up  (Info-extract-pointer "up")))
                  (cond ((string= "Top" up)
                         (setq crumbs  (if crumbs
                                           (concat "*Note Top:: > " crumbs)
                                         "*Note Top::")
                               done    t))
                        (t
                         (let ((Info-fontify-maximum-menu-size  nil) ; Prevents infinite recursion
                               (Info-history                    Info-history)
                               (Info-history-list               Info-history-list))
                           (Info-goto-node up))
                         (setq nod  Info-current-node)
                         (when crumbs (setq crumbs  (concat " > " crumbs)))
                         (setq crumbs  (concat "*Note " nod ":: " crumbs))))))
              (let ((Info-fontify-maximum-menu-size  nil) ; Prevents infinite recursion
                    (Info-history                    Info-history)
                    (Info-history-list               Info-history-list))
                (Info-goto-node onode))
              (forward-line 1)
              (insert (concat crumbs "\n\n"))))
          
          ;; Treat header line
          (when Info-use-header-line
            (goto-char (point-min))
            (let* ((header-end  (line-end-position))
                   (header
                    ;; If we find neither Next: nor Prev: link, show the entire
                    ;; node header.  Otherwise, don't show the File: and Node:
                    ;; parts, to avoid wasting precious space on information that
                    ;; is available in the mode line.
                    (if (re-search-forward "\\(next\\|up\\|prev[ious]*\\): "
                                           header-end t)
                        (progn (goto-char (match-beginning 1))
                               (buffer-substring (point) header-end))
                      (if (re-search-forward "node:[ \t]*[^ \t]+[ \t]*" header-end t)
                          (concat "No next, prev or up links  --  "
                                  (buffer-substring (point) header-end))
                        (buffer-substring (point) header-end)))))
              (put-text-property (point-min) (1+ (point-min))
                                 'header-line
                                 (replace-regexp-in-string
                                  "%"
                                  ;; Preserve text properties on duplicated `%'.
                                  (lambda (s) (concat s s)) header))
              ;; Hide the part of the first line
              ;; that is in the header, if it is just part.
              (unless (bobp)
                ;; Hide the punctuation at the end, too.
                (skip-chars-backward " \t,")
                (put-text-property (point) header-end 'invisible t)))))

        ;; Fontify `...' and "..."
        (goto-char (point-min))
        (when Info-fontify-quotations-flag (info-fontify-quotations))

        ;;  Fontify reference items: `-- Function:', `-- Variable:', etc.
        (goto-char (point-min))
        (when Info-fontify-reference-items-flag (info-fontify-reference-items))

        ;; Fontify titles
        (goto-char (point-min))
        (when (and font-lock-mode not-fontified-p)
          (while (and (re-search-forward "\n\\([^ \t\n].+\\)\n\\(\\*\\*+\\|==+\\|--+\\|\\.\\.+\\)$"
                                         nil t)
                      ;; Only consider it as an underlined title if the ASCII
                      ;; underline has the same size as the text.  A typical
                      ;; counter example is when a continuation "..." is alone
                      ;; on a line.
                      (= (string-width (match-string 1))
                         (string-width (match-string 2))))
            (let* ((c     (preceding-char))
                   (face  (cond ((= c ?*) 'Info-title-1-face)
                                ((= c ?=) 'Info-title-2-face)
                                ((= c ?-) 'Info-title-3-face)
                                (t        'Info-title-4-face))))
              (put-text-property (match-beginning 1) (match-end 1) 'font-lock-face face))
            ;; This is a serious problem for trying to handle multiple
            ;; frame types at once.  We want this text to be invisible
            ;; on frames that can display the font above.
            (when (memq (framep (selected-frame)) '(x pc w32 mac))
              (add-text-properties (1- (match-beginning 2)) (match-end 2)
                                   '(invisible t front-sticky nil rear-nonsticky t)))))

        ;; Fontify cross references
        (goto-char (point-min))
        (when (or not-fontified-p fontify-visited-p)
          (while (re-search-forward
                  "\\(\\*Note[ \n\t]+\\)\\([^:]*\\)\\(:[ \t]*\\([^.,:(]*\\)\\(\\(([^)]\
*)\\)[^.,:]*\\)?[,:]?\n?\\)"
                  nil t)
            (let ((start  (match-beginning 0))
                  (next   (point))
                  other-tag)
              (when not-fontified-p
                (when (or Info-hide-note-references (<= (line-number-at-pos) 4))
                  (when (and (not (eq Info-hide-note-references 'hide))
                             (> (line-number-at-pos) 4)) ; Skip breadcrumbs
                    ;; *Note is often used where *note should have been
                    (goto-char start)
                    (skip-syntax-backward " ")
                    (when (memq (char-before) '(?\( ?\[ ?\{))
                      ;; Check whether the paren is preceded by
                      ;; an end of sentence
                      (skip-syntax-backward " ("))
                    (setq other-tag  (cond ((save-match-data (looking-back "\\<see"))
                                            "")
                                           ((save-match-data (looking-back "\\<in"))
                                            "")
                                           ((memq (char-before) '(nil ?\. ?! ??))
                                            "See ")
                                           ((save-match-data
                                              (save-excursion (search-forward "\n\n" start t)))
                                            "See ")
                                           (t "see "))))
                  (goto-char next)
                  (add-text-properties
                   (match-beginning 1)
                   (or (save-match-data
                         ;; Don't hide \n after *Note
                         (let ((start1  (match-beginning 1)))
                           (and (string-match "\n" (match-string 1))
                                (+ start1 (match-beginning 0)))))
                       (match-end 1))
                   (if other-tag
                       `(display ,other-tag front-sticky nil rear-nonsticky t)
                     '(invisible t front-sticky nil rear-nonsticky t))))
                (add-text-properties
                 (match-beginning 2) (match-end 2)
                 (list
                  'help-echo (if (or (match-end 5)
                                     (not (equal (match-string 4) "")))
                                 (concat "mouse-2: go to " (or (match-string 5)
                                                               (match-string 4)))
                               "mouse-2: go to this node")
                  'mouse-face 'highlight)))
              (when (or not-fontified-p fontify-visited-p)
                (setq rbeg  (match-beginning 2)
                      rend  (match-end 2))
                (put-text-property
                 rbeg rend
                 'font-lock-face
                 ;; Display visited nodes in a different face
                 (if (and Info-fontify-visited-nodes
                          (save-match-data
                            (let* ((node
                                    (replace-regexp-in-string
                                     "^[ \t]+" ""
                                     (replace-regexp-in-string
                                      "[ \t\n]+" " "
                                      (or (match-string-no-properties 5)
                                          (and (not (equal (match-string 4) ""))
                                               (match-string-no-properties 4))
                                          (match-string-no-properties 2)))))
                                   (external-link-p  (string-match "(\\([^)]+\\))\\([^)]*\\)" node))
                                   (file             (if external-link-p
                                                         (file-name-nondirectory
                                                          (match-string-no-properties 1 node))
                                                       Info-current-file))
                                   (hl               Info-history-list)
                                   res)
                              (when external-link-p
                                (setq node  (if (equal (match-string 2 node) "")
                                                "Top"
                                              (match-string-no-properties 2 node))))
                              (while hl
                                (if (and (string-equal node (nth 1 (car hl)))
                                         (equal file
                                                (if (and external-link-p (stringp (caar hl)))
                                                    (file-name-nondirectory (caar hl))
                                                  (caar hl))))
                                    (setq res  (car hl)
                                          hl   nil)
                                  (setq hl  (cdr hl))))
                              res))) 'info-xref-visited 'info-xref))
                ;; For multiline ref, unfontify newline and surrounding whitespace
                (save-excursion
                  (goto-char rbeg)
                  (save-match-data
                    (while (re-search-forward "\\s-*\n\\s-*" rend t nil)
                      (remove-text-properties (match-beginning 0)
                                              (match-end 0)
                                              '(font-lock-face t))))))
              (when not-fontified-p
                (when (or (memq Info-hide-note-references '(t hide))
                          (<= (line-number-at-pos) 4))
                  (add-text-properties (match-beginning 3) (match-end 3)
                                       '(invisible t front-sticky nil rear-nonsticky t))
                  ;; Unhide the file name of the external reference in parens
                  (if (and (match-string 6)
                           (not (eq Info-hide-note-references 'hide))
                           (> (line-number-at-pos) 4))
                      (remove-text-properties
                       (match-beginning 6) (match-end 6)
                       '(invisible t front-sticky nil rear-nonsticky t)))
                  ;; Unhide newline because hidden newlines cause too long lines
                  (save-match-data
                    (let ((beg3  (match-beginning 3))
                          (end3  (match-end 3)))
                      (if (and (string-match "\n[ \t]*" (match-string 3))
                               (not (save-match-data (save-excursion (goto-char (1+ end3))
                                                                     (looking-at "[.)]*$")))))
                          (remove-text-properties
                           (+ beg3 (match-beginning 0))
                           (+ beg3 (match-end 0))
                           '(invisible t front-sticky nil rear-nonsticky t))))))
                (when (and Info-refill-paragraphs
                           (or Info-hide-note-references
                               (<= (line-number-at-pos) 4)))
                  (push (set-marker (make-marker) start) paragraph-markers))))))

        ;; Refill paragraphs (experimental feature)
        (when (and not-fontified-p
                   Info-refill-paragraphs
                   paragraph-markers)
          (let ((fill-nobreak-invisible          t)
                (fill-individual-varying-indent  nil)
                (paragraph-start                 "\f\\|[ \t]*[-*]\\|[ \t]*$")
                (paragraph-separate              ".*\\.[ \t]*\n[ \t]\\|[ \t]*[-*]\\|[ \t\f]*$")
                (adaptive-fill-mode              nil))
            (goto-char (point-max))
            (dolist (m paragraph-markers)
              (when (< m (point))
                (goto-char m)
                (beginning-of-line)
                (let ((beg  (point)))
                  (when (zerop (forward-paragraph))
                    (fill-individual-paragraphs beg (point) nil nil)
                    (goto-char beg))))
              (set-marker m nil))))

        ;; Fontify menu items
        (goto-char (point-min))
        (when (and (or not-fontified-p fontify-visited-p)
                   (search-forward "\n* Menu:" nil t)
                   ;; Don't take time to annotate huge menus
                   Info-fontify-maximum-menu-size
                   (< (- (point-max) (point)) Info-fontify-maximum-menu-size))
          (let ((n  0)
                cont)
            (while (re-search-forward
                    (concat "^\\* Menu:\\|\\(?:^\\* +\\(" Info-menu-entry-name-re "\\)\\(:"
                            Info-node-spec-re "\\([ \t]*\\)\\)\\)")
                    nil t)
              (when (match-beginning 1)
                (when not-fontified-p
                  (setq n  (1+ n))
                  (if (and (<= n 9) (zerop (% n 3))) ; visual aids to help with 1-9 keys
                      (put-text-property (match-beginning 0)
                                         (1+ (match-beginning 0))
                                         'font-lock-face 'info-menu-5)))
                (when not-fontified-p
                  (add-text-properties
                   (match-beginning 1) (match-end 1)
                   (list
                    'help-echo (if (and (match-end 3)
                                        (not (equal (match-string 3) "")))
                                   (concat "mouse-2: go to " (match-string 3))
                                 "mouse-2: go to this node")
                    'mouse-face 'highlight)))
                (when (or not-fontified-p fontify-visited-p)
                  (put-text-property
                   (match-beginning 1) (match-end 1)
                   'font-lock-face
                   ;; Display visited menu items in a different face
                   (if (and Info-fontify-visited-nodes
                            (save-match-data
                              (let* ((node             (if (equal (match-string 3) "")
                                                           (match-string-no-properties 1)
                                                         (match-string-no-properties 3)))
                                     (external-link-p  (string-match "(\\([^)]+\\))\\([^)]*\\)" node))
                                     (file             (if external-link-p
                                                           (file-name-nondirectory
                                                            (match-string-no-properties 1 node))
                                                         Info-current-file))
                                     (hl               Info-history-list)
                                     res)
                                (when external-link-p
                                  (setq node  (if (equal (match-string 2 node) "")
                                                  "Top"
                                                (match-string-no-properties 2 node))))
                                (while hl
                                  (if (and (string-equal node (nth 1 (car hl)))
                                           (equal file (if (and external-link-p (stringp (caar hl)))
                                                           (file-name-nondirectory (caar hl))
                                                         (caar hl))))
                                      (setq res  (car hl)
                                            hl   nil)
                                    (setq hl  (cdr hl))))
                                res))) 'info-xref-visited 'info-xref)))
                (when (and not-fontified-p
                           (or (memq Info-hide-note-references '(t hide))
                               (<= (line-number-at-pos) 4))
                           (not (Info-index-node)))
                  (put-text-property (match-beginning 2) (1- (match-end 6))
                                     'invisible t)
                  ;; Unhide the file name in parens
                  (if (and (match-end 4) (not (eq (char-after (match-end 4)) ?.)))
                      (remove-text-properties (match-beginning 4) (match-end 4)
                                              '(invisible t)))
                  ;; We need a stretchable space like :align-to but with
                  ;; a minimum value.
                  (put-text-property (1- (match-end 6)) (match-end 6) 'display
                                     (if (>= 22 (- (match-end 1)
                                                   (match-beginning 0)))
                                         '(space :align-to 24)
                                       '(space :width 2)))
                  (setq cont  (looking-at "."))
                  (while (and (= (forward-line 1) 0)
                              (looking-at "\\([ \t]+\\)[^*\n]"))
                    (put-text-property (match-beginning 1) (1- (match-end 1))
                                       'invisible t)
                    (put-text-property (1- (match-end 1)) (match-end 1)
                                       'display
                                       (if cont
                                           '(space :align-to 26)
                                         '(space :align-to 24)))
                    (setq cont  t)))))))

        ;; Fontify menu headers
        ;; Add the face `info-menu-header' to any header before a menu entry
        (goto-char (point-min))
        (when (and not-fontified-p (re-search-forward "^\\* Menu:" nil t))
          (put-text-property (match-beginning 0) (match-end 0)
                             'font-lock-face 'info-menu-header)
          (while (re-search-forward "\n\n\\([^*\n ].*\\)\n\n?[*]" nil t)
            (put-text-property (match-beginning 1) (match-end 1)
                               'font-lock-face 'info-menu-header)))

        ;; Hide index line numbers
        (goto-char (point-min))
        (when (and not-fontified-p (Info-index-node))
          (while (re-search-forward "[ \t\n]*(line +[0-9]+)" nil t)
            (put-text-property (match-beginning 0) (match-end 0)
                               'invisible t)))

        ;; Fontify http and ftp references
        (goto-char (point-min))
        (when not-fontified-p
          (while (re-search-forward "\\(https?\\|ftp\\)://[^ \t\n\"`({<>})']+" nil t)
            (add-text-properties (match-beginning 0) (match-end 0)
                                 '(font-lock-face info-xref
                                   mouse-face highlight
                                   help-echo "mouse-2: go to this URL"))))

        (set-buffer-modified-p nil)))))


;; REPLACES ORIGINAL in `info.el':
;; 1. File name in face `info-file'.
;; 2. If `Info-fontify-quotations-flag', fontify `...' in face `info-quoted-name',
;;    "..." in face `info-string', and ' in face `info-single-quote'.
;;
(when (and (> emacs-major-version 22) (not (fboundp 'Info-breadcrumbs))) ; Emacs 23.1, not 23.2+
  (defun Info-fontify-node ()
    "Fontify the node."
    (save-excursion
      (let* ((inhibit-read-only  t)
             (case-fold-search   t)
             paragraph-markers
             (not-fontified-p           ; the node hasn't already been fontified
              (not (let ((where  (next-single-property-change (point-min) 'font-lock-face)))
                     (and where (not (= where (point-max)))))))
             (fontify-visited-p         ; visited nodes need to be re-fontified
              (and Info-fontify-visited-nodes
                   ;; Don't take time to refontify visited nodes in huge nodes
                   Info-fontify-maximum-menu-size
                   (< (- (point-max) (point-min)) Info-fontify-maximum-menu-size)))
             rbeg rend)

        ;; Fontify header line
        (goto-char (point-min))
        (when (and not-fontified-p (looking-at "^File: \\([^,: \t]+\\),?[ \t]+"))
          (put-text-property (match-beginning 1) (match-end 1) 'font-lock-face 'info-file))
        (goto-char (point-min))
        (when (and not-fontified-p (looking-at "^\\(File: [^,: \t]+,?[ \t]+\\)?"))
          (while (looking-at "[ \t]*\\([^:, \t\n]+\\):[ \t]+\\([^:,\t\n]+\\),?")
            (goto-char (match-end 0))
            (let* ((nbeg  (match-beginning 2))
                   (nend  (match-end 2))
                   (tbeg  (match-beginning 1))
                   (tag   (match-string 1)))
              (if (string-equal (downcase tag) "node")
                  (put-text-property nbeg nend 'font-lock-face 'info-header-node)
                (put-text-property nbeg nend 'font-lock-face 'info-header-xref)
                (put-text-property tbeg nend 'mouse-face 'highlight)
                (put-text-property tbeg nend
                                   'help-echo
                                   (concat "mouse-2: Go to node "
                                           (buffer-substring nbeg nend)))
                ;; Always set up the text property keymap.
                ;; It will either be used in the buffer
                ;; or copied in the header line.
                (put-text-property tbeg nend 'keymap
                                   (cond
                                     ((string-equal (downcase tag) "prev") Info-prev-link-keymap)
                                     ((string-equal (downcase tag) "next") Info-next-link-keymap)
                                     ((string-equal (downcase tag) "up"  ) Info-up-link-keymap))))))
          (when (and Info-breadcrumbs-in-header-flag (> Info-breadcrumbs-depth 0))
            (Info-insert-breadcrumbs))
          
          ;; Treat header line.
          (when Info-use-header-line
            (goto-char (point-min))
            (let* ((header-end  (line-end-position))
                   (header
                    ;; If we find neither Next: nor Prev: link, show the entire
                    ;; node header.  Otherwise, don't show the File: and Node:
                    ;; parts, to avoid wasting precious space on information that
                    ;; is available in the mode line.
                    (if (re-search-forward "\\(next\\|up\\|prev[ious]*\\): " header-end t)
                        (progn (goto-char (match-beginning 1))
                               (buffer-substring (point) header-end))
                      (if (re-search-forward "node:[ \t]*[^ \t]+[ \t]*" header-end t)
                          (concat "No next, prev or up links  --  "
                                  (buffer-substring (point) header-end))
                        (buffer-substring (point) header-end)))))
              (put-text-property (point-min) (1+ (point-min))
                                 'header-line (replace-regexp-in-string
                                               "%"
                                               ;; Preserve text properties on duplicated `%'.
                                               (lambda (s) (concat s s)) header))
              ;; Hide the part of the first line that is in the header, if it is just part.
              (cond ((and Info-breadcrumbs-in-header-flag (> Info-breadcrumbs-depth 0))
                     (put-text-property (point-min) (1+ header-end) 'invisible t))
                    ((not (bobp))
                     ;; Hide the punctuation at the end, too.
                     (skip-chars-backward " \t,")
                     (put-text-property (point) header-end 'invisible t))))))

        ;; Fontify `...' and "..."
        (goto-char (point-min))
        (when Info-fontify-quotations-flag (info-fontify-quotations))

        ;;  Fontify reference items: `-- Function:', `-- Variable:', etc.
        (goto-char (point-min))
        (when Info-fontify-reference-items-flag (info-fontify-reference-items))

        ;; Fontify titles
        (goto-char (point-min))
        (when (and font-lock-mode not-fontified-p)
          (while (and (re-search-forward "\n\\([^ \t\n].+\\)\n\\(\\*\\*+\\|==+\\|--+\\|\\.\\.+\\)$"
                                         nil t)
                      ;; Only consider it as an underlined title if the ASCII
                      ;; underline has the same size as the text.  A typical
                      ;; counter example is when a continuation "..." is alone
                      ;; on a line.
                      (= (string-width (match-string 1))
                         (string-width (match-string 2))))
            (let* ((c     (preceding-char))
                   (face  (cond ((= c ?*) 'Info-title-1-face)
                                ((= c ?=) 'Info-title-2-face)
                                ((= c ?-) 'Info-title-3-face)
                                (t        'Info-title-4-face))))
              (put-text-property (match-beginning 1) (match-end 1)
                                 'font-lock-face face))
            ;; This is a serious problem for trying to handle multiple
            ;; frame types at once.  We want this text to be invisible
            ;; on frames that can display the font above.
            (when (memq (framep (selected-frame)) '(x pc w32 ns))
              (add-text-properties (1- (match-beginning 2)) (match-end 2)
                                   '(invisible t front-sticky nil rear-nonsticky t)))))

        ;; Fontify cross references
        (goto-char (point-min))
        (when (or not-fontified-p fontify-visited-p)
          (while (re-search-forward
                  "\\(\\*Note[ \n\t]+\\)\\([^:]*\\)\\(:[ \t]*\\([^.,:(]*\\)\\(\\(([^)]\
*)\\)[^.,:]*\\)?[,:]?\n?\\)"
                  nil t)
            (let ((start  (match-beginning 0))
                  (next   (point))
                  other-tag)
              (when not-fontified-p
                (when Info-hide-note-references
                  (when (and (not (eq Info-hide-note-references 'hide))
                             (> (line-number-at-pos) 4)) ; Skip breadcrumbs
                    ;; *Note is often used where *note should have been
                    (goto-char start)
                    (skip-syntax-backward " ")
                    (when (memq (char-before) '(?\( ?\[ ?\{))
                      ;; Check whether the paren is preceded by
                      ;; an end of sentence
                      (skip-syntax-backward " ("))
                    (setq other-tag  (cond ((save-match-data (looking-back "\\<see"))
                                            "")
                                           ((save-match-data (looking-back "\\<in"))
                                            "")
                                           ((memq (char-before) '(nil ?\. ?! ??))
                                            "See ")
                                           ((save-match-data
                                              (save-excursion (search-forward "\n\n" start t)))
                                            "See ")
                                           (t "see "))))
                  (goto-char next)
                  (add-text-properties
                   (match-beginning 1)
                   (or (save-match-data
                         ;; Don't hide \n after *Note
                         (let ((start1  (match-beginning 1)))
                           (and (string-match "\n" (match-string 1))
                                (+ start1 (match-beginning 0)))))
                       (match-end 1))
                   (if other-tag
                       `(display ,other-tag front-sticky nil rear-nonsticky t)
                     '(invisible t front-sticky nil rear-nonsticky t))))
                (add-text-properties
                 (match-beginning 2) (match-end 2)
                 (list
                  'help-echo (if (or (match-end 5)
                                     (not (equal (match-string 4) "")))
                                 (concat "mouse-2: go to " (or (match-string 5)
                                                               (match-string 4)))
                               "mouse-2: go to this node")
                  'mouse-face 'highlight)))
              (when (or not-fontified-p fontify-visited-p)
                (setq rbeg  (match-beginning 2)
                      rend  (match-end 2))
                (put-text-property
                 rbeg rend
                 'font-lock-face
                 ;; Display visited nodes in a different face
                 (if (and Info-fontify-visited-nodes
                          (save-match-data
                            (let* ((node
                                    (replace-regexp-in-string
                                     "^[ \t]+" ""
                                     (replace-regexp-in-string
                                      "[ \t\n]+" " "
                                      (or (match-string-no-properties 5)
                                          (and (not (equal (match-string 4) ""))
                                               (match-string-no-properties 4))
                                          (match-string-no-properties 2)))))
                                   (external-link-p  (string-match "(\\([^)]+\\))\\([^)]*\\)" node))
                                   (file             (if external-link-p
                                                         (file-name-nondirectory
                                                          (match-string-no-properties 1 node))
                                                       Info-current-file))
                                   (hl               Info-history-list)
                                   res)
                              (when external-link-p
                                (setq node  (if (equal (match-string 2 node) "")
                                                "Top"
                                              (match-string-no-properties 2 node))))
                              (while hl
                                (if (and (string-equal node (nth 1 (car hl)))
                                         (equal file (if (and external-link-p (stringp (caar hl)))
                                                         (file-name-nondirectory (caar hl))
                                                       (caar hl))))
                                    (setq res  (car hl)
                                          hl   nil)
                                  (setq hl  (cdr hl))))
                              res))) 'info-xref-visited 'info-xref))
                ;; For multiline ref, unfontify newline and surrounding whitespace
                (save-excursion
                  (goto-char rbeg)
                  (save-match-data
                    (while (re-search-forward "\\s-*\n\\s-*" rend t nil)
                      (remove-text-properties (match-beginning 0) (match-end 0)
                                              '(font-lock-face t))))))
              (when not-fontified-p
                (when (memq Info-hide-note-references '(t hide))
                  (add-text-properties (match-beginning 3) (match-end 3)
                                       '(invisible t front-sticky nil rear-nonsticky t))
                  ;; Unhide the file name of the external reference in parens
                  (if (and (match-string 6)
                           (not (eq Info-hide-note-references 'hide)))
                      (remove-text-properties
                       (match-beginning 6) (match-end 6)
                       '(invisible t front-sticky nil rear-nonsticky t)))
                  ;; Unhide newline because hidden newlines cause too long lines
                  (save-match-data
                    (let ((beg3  (match-beginning 3))
                          (end3  (match-end 3)))
                      (if (and (string-match "\n[ \t]*" (match-string 3))
                               (not (save-match-data (save-excursion (goto-char (1+ end3))
                                                                     (looking-at "[.)]*$")))))
                          (remove-text-properties
                           (+ beg3 (match-beginning 0))
                           (+ beg3 (match-end 0))
                           '(invisible t front-sticky nil rear-nonsticky t))))))
                (when (and Info-refill-paragraphs Info-hide-note-references)
                  (push (set-marker (make-marker) start) paragraph-markers))))))

        ;; Refill paragraphs (experimental feature)
        (when (and not-fontified-p Info-refill-paragraphs paragraph-markers)
          (let ((fill-nobreak-invisible          t)
                (fill-individual-varying-indent  nil)
                (paragraph-start                 "\f\\|[ \t]*[-*]\\|[ \t]*$")
                (paragraph-separate              ".*\\.[ \t]*\n[ \t]\\|[ \t]*[-*]\\|[ \t\f]*$")
                (adaptive-fill-mode              nil))
            (goto-char (point-max))
            (dolist (m  paragraph-markers)
              (when (< m (point))
                (goto-char m)
                (beginning-of-line)
                (let ((beg  (point)))
                  (when (zerop (forward-paragraph))
                    (fill-individual-paragraphs beg (point) nil nil)
                    (goto-char beg))))
              (set-marker m nil))))

        ;; Fontify menu items
        (goto-char (point-min))
        (when (and (or not-fontified-p fontify-visited-p)
                   (search-forward "\n* Menu:" nil t)
                   ;; Don't take time to annotate huge menus
                   Info-fontify-maximum-menu-size
                   (< (- (point-max) (point)) Info-fontify-maximum-menu-size))
          (let ((n  0)
                cont)
            (while (re-search-forward
                    (concat "^\\* Menu:\\|\\(?:^\\* +\\(" Info-menu-entry-name-re "\\)\\(:"
                            Info-node-spec-re "\\([ \t]*\\)\\)\\)")
                    nil t)
              (when (match-beginning 1)
                (when not-fontified-p
                  (setq n  (1+ n))
                  (if (and (<= n 9) (zerop (% n 3))) ; visual aids to help with 1-9 keys
                      (put-text-property (match-beginning 0) (1+ (match-beginning 0))
                                         'font-lock-face 'info-menu-5)))
                (when not-fontified-p
                  (add-text-properties
                   (match-beginning 1) (match-end 1)
                   (list 'help-echo (if (and (match-end 3)
                                             (not (equal (match-string 3) "")))
                                        (concat "mouse-2: go to " (match-string 3))
                                      "mouse-2: go to this node")
                         'mouse-face 'highlight)))
                (when (or not-fontified-p fontify-visited-p)
                  (put-text-property
                   (match-beginning 1) (match-end 1)
                   'font-lock-face
                   ;; Display visited menu items in a different face
                   (if (and Info-fontify-visited-nodes
                            (save-match-data
                              (let* ((node             (if (equal (match-string 3) "")
                                                           (match-string-no-properties 1)
                                                         (match-string-no-properties 3)))
                                     (external-link-p  (string-match "(\\([^)]+\\))\\([^)]*\\)" node))
                                     (file             (if external-link-p
                                                           (file-name-nondirectory
                                                            (match-string-no-properties 1 node))
                                                         Info-current-file))
                                     (hl               Info-history-list)
                                     res)
                                (when external-link-p
                                  (setq node  (if (equal (match-string 2 node) "")
                                                  "Top"
                                                (match-string-no-properties 2 node))))
                                (while hl
                                  (if (and (string-equal node (nth 1 (car hl)))
                                           (equal file (if (and external-link-p (stringp (caar hl)))
                                                           (file-name-nondirectory (caar hl))
                                                         (caar hl))))
                                      (setq res  (car hl)
                                            hl   nil)
                                    (setq hl  (cdr hl))))
                                res))) 'info-xref-visited 'info-xref)))
                (when (and not-fontified-p
                           (memq Info-hide-note-references '(t hide))
                           (not (Info-index-node)))
                  (put-text-property (match-beginning 2) (1- (match-end 6)) 'invisible t)
                  ;; Unhide the file name in parens
                  (if (and (match-end 4) (not (eq (char-after (match-end 4)) ?.)))
                      (remove-text-properties (match-beginning 4) (match-end 4)
                                              '(invisible t)))
                  ;; We need a stretchable space like :align-to but with
                  ;; a minimum value.
                  (put-text-property (1- (match-end 6)) (match-end 6) 'display
                                     (if (>= 22 (- (match-end 1)
                                                   (match-beginning 0)))
                                         '(space :align-to 24)
                                       '(space :width 2)))
                  (setq cont  (looking-at "."))
                  (while (and (= (forward-line 1) 0)
                              (looking-at "\\([ \t]+\\)[^*\n]"))
                    (put-text-property (match-beginning 1) (1- (match-end 1))
                                       'invisible t)
                    (put-text-property (1- (match-end 1)) (match-end 1)
                                       'display
                                       (if cont
                                           '(space :align-to 26)
                                         '(space :align-to 24)))
                    (setq cont  t)))))))

        ;; Fontify menu headers
        ;; Add the face `info-menu-header' to any header before a menu entry
        (goto-char (point-min))
        (when (and not-fontified-p (re-search-forward "^\\* Menu:" nil t))
          (put-text-property (match-beginning 0) (match-end 0)
                             'font-lock-face 'info-menu-header)
          (while (re-search-forward "\n\n\\([^*\n ].*\\)\n\n?[*]" nil t)
            (put-text-property (match-beginning 1) (match-end 1)
                               'font-lock-face 'info-menu-header)))

        ;; Hide index line numbers
        (goto-char (point-min))
        (when (and not-fontified-p (Info-index-node))
          (while (re-search-forward "[ \t\n]*(line +[0-9]+)" nil t)
            (put-text-property (match-beginning 0) (match-end 0)
                               'invisible t)))

        ;; Fontify http and ftp references
        (goto-char (point-min))
        (when not-fontified-p
          (while (re-search-forward "\\(https?\\|ftp\\)://[^ \t\n\"`({<>})']+" nil t)
            (add-text-properties (match-beginning 0) (match-end 0)
                                 '(font-lock-face info-xref
                                   mouse-face highlight
                                   help-echo "mouse-2: go to this URL"))))

        (set-buffer-modified-p nil)))))


;; REPLACES ORIGINAL in `info.el':
;; 1. File name in face `info-file'.
;; 2. If `Info-fontify-quotations-flag', fontify `...' in face `info-quoted-name',
;;    "..." in face `info-string', and ' in face `info-single-quote'.
;;
(when (and (> emacs-major-version 22) (fboundp 'Info-breadcrumbs)) ; Emacs 23.2+
  (defun Info-fontify-node ()
    "Fontify the node."
    (save-excursion
      (let* ((inhibit-read-only  t)
             (case-fold-search   t)
             paragraph-markers
             (not-fontified-p           ; the node hasn't already been fontified
              (not (let ((where  (next-single-property-change (point-min) 'font-lock-face)))
                     (and where (not (= where (point-max)))))))
             (fontify-visited-p         ; visited nodes need to be re-fontified
              (and Info-fontify-visited-nodes
                   ;; Don't take time to refontify visited nodes in huge nodes
                   Info-fontify-maximum-menu-size
                   (< (- (point-max) (point-min)) Info-fontify-maximum-menu-size)))
             rbeg rend)

        ;; Fontify header line
        (goto-char (point-min))
        (when (and not-fontified-p (looking-at "^File: \\([^,: \t]+\\),?[ \t]+"))
          (put-text-property (match-beginning 1) (match-end 1) 'font-lock-face 'info-file))
        (goto-char (point-min))
        (when (and not-fontified-p (looking-at "^\\(File: [^,: \t]+,?[ \t]+\\)?"))
          (while (looking-at "[ \t]*\\([^:, \t\n]+\\):[ \t]+\\([^:,\t\n]+\\),?")
            (goto-char (match-end 0))
            (let* ((nbeg  (match-beginning 2))
                   (nend  (match-end 2))
                   (tbeg  (match-beginning 1))
                   (tag   (match-string 1)))
              (if (string-equal (downcase tag) "node")
                  (put-text-property nbeg nend 'font-lock-face 'info-header-node)
                (put-text-property nbeg nend 'font-lock-face 'info-header-xref)
                (put-text-property tbeg nend 'mouse-face 'highlight)
                (put-text-property tbeg nend
                                   'help-echo
                                   (concat "mouse-2: Go to node "
                                           (buffer-substring nbeg nend)))
                ;; Always set up the text property keymap.
                ;; It will either be used in the buffer
                ;; or copied in the header line.
                (put-text-property tbeg nend 'keymap
                                   (cond
                                     ((string-equal (downcase tag) "prev") Info-prev-link-keymap)
                                     ((string-equal (downcase tag) "next") Info-next-link-keymap)
                                     ((string-equal (downcase tag) "up"  ) Info-up-link-keymap))))))
          
          ;; Treat header line.
          (when Info-use-header-line
            (goto-char (point-min))
            (let* ((header-end  (line-end-position))
                   (header
                    ;; If we find neither Next: nor Prev: link, show the entire
                    ;; node header.  Otherwise, don't show the File: and Node:
                    ;; parts, to avoid wasting precious space on information that
                    ;; is available in the mode line.
                    (if (re-search-forward "\\(next\\|up\\|prev[ious]*\\): " header-end t)
                        (progn (goto-char (match-beginning 1))
                               (buffer-substring (point) header-end))
                      (if (re-search-forward "node:[ \t]*[^ \t]+[ \t]*" header-end t)
                          (concat "No next, prev or up links  --  "
                                  (buffer-substring (point) header-end))
                        (buffer-substring (point) header-end)))))
              (put-text-property (point-min) (1+ (point-min))
                                 'header-line (replace-regexp-in-string
                                               "%"
                                               ;; Preserve text properties on duplicated `%'.
                                               (lambda (s) (concat s s)) header))
              ;; Hide the part of the first line that is in the header, if it is just part.
              (cond ((and Info-breadcrumbs-in-header-flag (> Info-breadcrumbs-depth 0))
                     (let ((ov (make-overlay (point-min) (1+ header-end))))
                       (overlay-put ov 'display (Info-breadcrumbs))
                       (overlay-put ov 'evaporate t)))
                    ((not (bobp))
                     ;; Hide the punctuation at the end, too.
                     (skip-chars-backward " \t,")
                     (put-text-property (point) header-end 'invisible t))))))

        ;; Fontify `...' and "..."
        (goto-char (point-min))
        (when Info-fontify-quotations-flag (info-fontify-quotations))

        ;;  Fontify reference items: `-- Function:', `-- Variable:', etc.
        (goto-char (point-min))
        (when Info-fontify-reference-items-flag (info-fontify-reference-items))

        ;; Fontify titles
        (goto-char (point-min))
        (when (and font-lock-mode not-fontified-p)
          (while (and (re-search-forward "\n\\([^ \t\n].+\\)\n\\(\\*\\*+\\|==+\\|--+\\|\\.\\.+\\)$"
                                         nil t)
                      ;; Only consider it as an underlined title if the ASCII
                      ;; underline has the same size as the text.  A typical
                      ;; counter example is when a continuation "..." is alone
                      ;; on a line.
                      (= (string-width (match-string 1))
                         (string-width (match-string 2))))
            (let* ((c     (preceding-char))
                   (face  (cond ((= c ?*) 'Info-title-1-face)
                                ((= c ?=) 'Info-title-2-face)
                                ((= c ?-) 'Info-title-3-face)
                                (t        'Info-title-4-face))))
              (put-text-property (match-beginning 1) (match-end 1)
                                 'font-lock-face face))
            ;; This is a serious problem for trying to handle multiple
            ;; frame types at once.  We want this text to be invisible
            ;; on frames that can display the font above.
            (when (memq (framep (selected-frame)) '(x pc w32 ns))
              (add-text-properties (1- (match-beginning 2)) (match-end 2)
                                   '(invisible t front-sticky nil rear-nonsticky t)))))

        ;; Fontify cross references
        (goto-char (point-min))
        (when (or not-fontified-p fontify-visited-p)
          (while (re-search-forward
                  "\\(\\*Note[ \n\t]+\\)\\([^:]*\\)\\(:[ \t]*\\([^.,:(]*\\)\\(\\(([^)]\
*)\\)[^.,:]*\\)?[,:]?\n?\\)"
                  nil t)
            (let ((start  (match-beginning 0))
                  (next   (point))
                  other-tag)
              (when not-fontified-p
                (when Info-hide-note-references
                  (when (and (not (eq Info-hide-note-references 'hide))
                             (> (line-number-at-pos) 4)) ; Skip breadcrumbs
                    ;; *Note is often used where *note should have been
                    (goto-char start)
                    (skip-syntax-backward " ")
                    (when (memq (char-before) '(?\( ?\[ ?\{))
                      ;; Check whether the paren is preceded by
                      ;; an end of sentence
                      (skip-syntax-backward " ("))
                    (setq other-tag  (cond ((save-match-data (looking-back "\\<see"))
                                            "")
                                           ((save-match-data (looking-back "\\<in"))
                                            "")
                                           ((memq (char-before) '(nil ?\. ?! ??))
                                            "See ")
                                           ((save-match-data
                                              (save-excursion (search-forward "\n\n" start t)))
                                            "See ")
                                           (t "see "))))
                  (goto-char next)
                  (add-text-properties
                   (match-beginning 1)
                   (or (save-match-data
                         ;; Don't hide \n after *Note
                         (let ((start1  (match-beginning 1)))
                           (and (string-match "\n" (match-string 1))
                                (+ start1 (match-beginning 0)))))
                       (match-end 1))
                   (if other-tag
                       `(display ,other-tag front-sticky nil rear-nonsticky t)
                     '(invisible t front-sticky nil rear-nonsticky t))))
                (add-text-properties
                 (match-beginning 2) (match-end 2)
                 (list
                  'help-echo (if (or (match-end 5)
                                     (not (equal (match-string 4) "")))
                                 (concat "mouse-2: go to " (or (match-string 5)
                                                               (match-string 4)))
                               "mouse-2: go to this node")
                  'mouse-face 'highlight)))
              (when (or not-fontified-p fontify-visited-p)
                (setq rbeg  (match-beginning 2)
                      rend  (match-end 2))
                (put-text-property
                 rbeg rend
                 'font-lock-face
                 ;; Display visited nodes in a different face
                 (if (and Info-fontify-visited-nodes
                          (save-match-data
                            (let* ((node
                                    (replace-regexp-in-string
                                     "^[ \t]+" ""
                                     (replace-regexp-in-string
                                      "[ \t\n]+" " "
                                      (or (match-string-no-properties 5)
                                          (and (not (equal (match-string 4) ""))
                                               (match-string-no-properties 4))
                                          (match-string-no-properties 2)))))
                                   (external-link-p  (string-match "(\\([^)]+\\))\\([^)]*\\)" node))
                                   (file             (if external-link-p
                                                         (file-name-nondirectory
                                                          (match-string-no-properties 1 node))
                                                       Info-current-file))
                                   (hl               Info-history-list)
                                   res)
                              (when external-link-p
                                (setq node  (if (equal (match-string 2 node) "")
                                                "Top"
                                              (match-string-no-properties 2 node))))
                              (while hl
                                (if (and (string-equal node (nth 1 (car hl)))
                                         (equal file (if (and external-link-p (stringp (caar hl)))
                                                         (file-name-nondirectory (caar hl))
                                                       (caar hl))))
                                    (setq res  (car hl)
                                          hl   nil)
                                  (setq hl  (cdr hl))))
                              res))) 'info-xref-visited 'info-xref))
                ;; For multiline ref, unfontify newline and surrounding whitespace
                (save-excursion
                  (goto-char rbeg)
                  (save-match-data
                    (while (re-search-forward "\\s-*\n\\s-*" rend t nil)
                      (remove-text-properties (match-beginning 0) (match-end 0)
                                              '(font-lock-face t))))))
              (when not-fontified-p
                (when (memq Info-hide-note-references '(t hide))
                  (add-text-properties (match-beginning 3) (match-end 3)
                                       '(invisible t front-sticky nil rear-nonsticky t))
                  ;; Unhide the file name of the external reference in parens
                  (if (and (match-string 6)
                           (not (eq Info-hide-note-references 'hide)))
                      (remove-text-properties
                       (match-beginning 6) (match-end 6)
                       '(invisible t front-sticky nil rear-nonsticky t)))
                  ;; Unhide newline because hidden newlines cause too long lines
                  (save-match-data
                    (let ((beg3  (match-beginning 3))
                          (end3  (match-end 3)))
                      (if (and (string-match "\n[ \t]*" (match-string 3))
                               (not (save-match-data (save-excursion (goto-char (1+ end3))
                                                                     (looking-at "[.)]*$")))))
                          (remove-text-properties
                           (+ beg3 (match-beginning 0))
                           (+ beg3 (match-end 0))
                           '(invisible t front-sticky nil rear-nonsticky t))))))
                (when (and Info-refill-paragraphs Info-hide-note-references)
                  (push (set-marker (make-marker) start) paragraph-markers))))))

        ;; Refill paragraphs (experimental feature)
        (when (and not-fontified-p Info-refill-paragraphs paragraph-markers)
          (let ((fill-nobreak-invisible          t)
                (fill-individual-varying-indent  nil)
                (paragraph-start                 "\f\\|[ \t]*[-*]\\|[ \t]*$")
                (paragraph-separate              ".*\\.[ \t]*\n[ \t]\\|[ \t]*[-*]\\|[ \t\f]*$")
                (adaptive-fill-mode              nil))
            (goto-char (point-max))
            (dolist (m  paragraph-markers)
              (when (< m (point))
                (goto-char m)
                (beginning-of-line)
                (let ((beg  (point)))
                  (when (zerop (forward-paragraph))
                    (fill-individual-paragraphs beg (point) nil nil)
                    (goto-char beg))))
              (set-marker m nil))))

        ;; Fontify menu items
        (goto-char (point-min))
        (when (and (or not-fontified-p fontify-visited-p)
                   (search-forward "\n* Menu:" nil t)
                   ;; Don't take time to annotate huge menus
                   Info-fontify-maximum-menu-size
                   (< (- (point-max) (point)) Info-fontify-maximum-menu-size))
          (let ((n  0)
                cont)
            (while (re-search-forward
                    (concat "^\\* Menu:\\|\\(?:^\\* +\\(" Info-menu-entry-name-re "\\)\\(:"
                            Info-node-spec-re "\\([ \t]*\\)\\)\\)")
                    nil t)
              (when (match-beginning 1)
                (when not-fontified-p
                  (setq n  (1+ n))
                  (if (and (<= n 9) (zerop (% n 3))) ; visual aids to help with 1-9 keys
                      (put-text-property (match-beginning 0) (1+ (match-beginning 0))
                                         'font-lock-face 'info-menu-5)))
                (when not-fontified-p
                  (add-text-properties
                   (match-beginning 1) (match-end 1)
                   (list 'help-echo (if (and (match-end 3)
                                             (not (equal (match-string 3) "")))
                                        (concat "mouse-2: go to " (match-string 3))
                                      "mouse-2: go to this node")
                         'mouse-face 'highlight)))
                (when (or not-fontified-p fontify-visited-p)
                  (put-text-property
                   (match-beginning 1) (match-end 1)
                   'font-lock-face
                   ;; Display visited menu items in a different face
                   (if (and Info-fontify-visited-nodes
                            (save-match-data
                              (let* ((node             (if (equal (match-string 3) "")
                                                           (match-string-no-properties 1)
                                                         (match-string-no-properties 3)))
                                     (external-link-p  (string-match "(\\([^)]+\\))\\([^)]*\\)" node))
                                     (file             (if external-link-p
                                                           (file-name-nondirectory
                                                            (match-string-no-properties 1 node))
                                                         Info-current-file))
                                     (hl               Info-history-list)
                                     res)
                                (when external-link-p
                                  (setq node  (if (equal (match-string 2 node) "")
                                                  "Top"
                                                (match-string-no-properties 2 node))))
                                (while hl
                                  (if (and (string-equal node (nth 1 (car hl)))
                                           (equal file (if (and external-link-p (stringp (caar hl)))
                                                           (file-name-nondirectory (caar hl))
                                                         (caar hl))))
                                      (setq res  (car hl)
                                            hl   nil)
                                    (setq hl  (cdr hl))))
                                res))) 'info-xref-visited 'info-xref)))
                (when (and not-fontified-p
                           (memq Info-hide-note-references '(t hide))
                           (not (Info-index-node)))
                  (put-text-property (match-beginning 2) (1- (match-end 6)) 'invisible t)
                  ;; Unhide the file name in parens
                  (if (and (match-end 4) (not (eq (char-after (match-end 4)) ?.)))
                      (remove-text-properties (match-beginning 4) (match-end 4)
                                              '(invisible t)))
                  ;; We need a stretchable space like :align-to but with
                  ;; a minimum value.
                  (put-text-property (1- (match-end 6)) (match-end 6) 'display
                                     (if (>= 22 (- (match-end 1)
                                                   (match-beginning 0)))
                                         '(space :align-to 24)
                                       '(space :width 2)))
                  (setq cont  (looking-at "."))
                  (while (and (= (forward-line 1) 0)
                              (looking-at "\\([ \t]+\\)[^*\n]"))
                    (put-text-property (match-beginning 1) (1- (match-end 1))
                                       'invisible t)
                    (put-text-property (1- (match-end 1)) (match-end 1)
                                       'display
                                       (if cont
                                           '(space :align-to 26)
                                         '(space :align-to 24)))
                    (setq cont  t)))))))

        ;; Fontify menu headers
        ;; Add the face `info-menu-header' to any header before a menu entry
        (goto-char (point-min))
        (when (and not-fontified-p (re-search-forward "^\\* Menu:" nil t))
          (put-text-property (match-beginning 0) (match-end 0)
                             'font-lock-face 'info-menu-header)
          (while (re-search-forward "\n\n\\([^*\n ].*\\)\n\n?[*]" nil t)
            (put-text-property (match-beginning 1) (match-end 1)
                               'font-lock-face 'info-menu-header)))

        ;; Hide index line numbers
        (goto-char (point-min))
        (when (and not-fontified-p (Info-index-node))
          (while (re-search-forward "[ \t\n]*(line +[0-9]+)" nil t)
            (put-text-property (match-beginning 0) (match-end 0)
                               'invisible t)))

        ;; Fontify http and ftp references
        (goto-char (point-min))
        (when not-fontified-p
          (while (re-search-forward "\\(https?\\|ftp\\)://[^ \t\n\"`({<>})']+" nil t)
            (add-text-properties (match-beginning 0) (match-end 0)
                                 '(font-lock-face info-xref
                                   mouse-face highlight
                                   help-echo "mouse-2: go to this URL"))))

        (set-buffer-modified-p nil)))))

(when (> emacs-major-version 22)
  (defvar Info-breadcrumbs-depth-internal Info-breadcrumbs-depth
    "Current breadcrumbs depth for Info."))


;; 1. I made this a global minor mode and turned it on by default, contrary to "the rules".
;;    I did this so (a) users could easily customize it but (b) it would be on by default, otherwise.
;;
;; 2. Macro `define-minor-mode' is not defined in Emacs 20, so in order to be able to byte-compile
;;    this file in Emacs 20, prohibit byte-compiling of the `define-minor-mode' call.
;;
(when (> emacs-major-version 22)
  (eval '(define-minor-mode Info-breadcrumbs-in-mode-line-mode
          "Toggle the use of breadcrumbs in Info mode line.
With arg, show breadcrumbs iff arg is positive.
Change the default behavior by customizing option
`Info-breadcrumbs-in-mode-line-mode'."
          :init-value t :global t :group 'mode-line :group 'Info-Plus
          (if (not Info-breadcrumbs-in-mode-line-mode)
              (setq Info-breadcrumbs-depth-internal  0
                    mode-line-format                 default-mode-line-format)
            (setq Info-breadcrumbs-depth-internal  Info-breadcrumbs-depth)
            (Info-insert-breadcrumbs-in-mode-line)))))

(when (> emacs-major-version 22)
  (defun Info-set-breadcrumbs-depth ()
    "Set current breadcrumbs depth to a value read from user.
Update breadcrumbs display in mode line accordingly."
    (interactive)
    (setq Info-breadcrumbs-depth-internal  (read-number "New breadcrumbs depth: "
                                                        Info-breadcrumbs-depth-internal))
    (when Info-breadcrumbs-in-mode-line-mode (Info-insert-breadcrumbs-in-mode-line))))


;; Match has, inside "..." or `...', zero or more of these characters:
;;   - any character except " or ', respectively
;;   - \ followed by any character
;;
;; The `... in `...' is optional, so the regexp can also match just '. 
;;
;; The regexp matches also `...' and "..." where at least one of the `, ', or "
;; is escaped by a backslash.  So we check those cases explicitly and don't highlight them.
(defvar info-quotation-regexp
  (if (< emacs-major-version 21)
      (concat "\"\\([^\"]\\|\\\\\\(.\\|[\n]\\)\\)*\"\\|" ; "..."
              "\\(`[^']*\\|\\\\\\(.\\|[\n]\\)\\)*'") ; `...'
    (concat "\"\\(?:[^\"]\\|\\\\\\(?:.\\|[\n]\\)\\)*\"\\|" ; "..."
            "\\(`[^']*\\|\\\\\\(.\\|[\n]\\)\\)*'")) ; `...'

  "Regexp to match `...', \"...\", or just '.
If ... contains \" or ' then that character must be backslashed.")

(defun info-fontify-quotations ()
  "Fontify `...', \"...\", and if `Info-fontify-single-quote-flag', just '.
 `...'\t- use face `info-quoted-name'
 \"...\"\t- use face `info-string'
 '\t- use face `info-single-quote'"
  (let ((regexp    info-quotation-regexp)
        (property  (if (> emacs-major-version 21) 'font-lock-face 'face)))
    (while (condition-case nil (re-search-forward regexp nil t) (error nil))
      (cond ((and (eq ?` (aref (match-string 0) 0)) ; Single-quoted backslashes: `\', `\\', `\\\', etc.
                  (goto-char (match-beginning 0))
                  (save-match-data (looking-at "\\(`\\\\+'\\)")))
             (put-text-property (1+ (match-beginning 0)) (1- (match-end 0)) property 'info-quoted-name)
             (goto-char (match-end 0)))
            ((and (eq ?` (aref (match-string 0) 0)) ; `...': If ` is preceded by \, then skip it
                  (goto-char (match-beginning 0))
                  (< (save-excursion (skip-chars-backward "\\\\")) 0))
             (goto-char (1+ (match-beginning 0))))
            ((eq ?` (aref (match-string 0) 0)) ; `...'
             (put-text-property (1+ (match-beginning 0)) (1- (match-end 0)) property 'info-quoted-name)
             (goto-char (match-end 0)) (forward-char 1))
            ((and (goto-char (match-beginning 0)) ; "...": If " preceded by \, then skip it
                  (< (save-excursion (skip-chars-backward "\\\\")) 0))
             (goto-char (1+ (match-beginning 0))))
            ((and Info-fontify-single-quote-flag
                  (string= "'" (buffer-substring (match-beginning 0) (match-end 0)))) ; Single ': 'foo
             (put-text-property (match-beginning 0) (match-end 0)
                                property 'info-single-quote)
             (goto-char (match-end 0)) (forward-char 1))
            (t                          ; "..."
             (put-text-property (match-beginning 0) (match-end 0)
                                property 'info-string)
             (goto-char (match-end 0)) (forward-char 1))))))

(defun info-fontify-reference-items ()
  "Fontify reference items such as \"Function:\" in Info buffer."
  (while
      (re-search-forward
       "^ --? \\(Function:\\|Variable:\\|Special Form:\\|\
Command:\\|User Option:\\|Macro:\\|Syntax class:\\)\\(.*\\)"
       nil t)
    (let ((symb  (intern (match-string 1))))
      (put-text-property (match-beginning 1)
                         (match-end 1)
                         (if (> emacs-major-version 21) 'font-lock-face 'face)
                         (case symb
                           ('Function:       'info-function-ref-item)
                           ('Variable:       'info-variable-ref-item)
                           ('Special\ Form:  'info-special-form-ref-item)
                           ('Command:        'info-command-ref-item)
                           ('User\ Option:   'info-user-option-ref-item)
                           ('Macro:          'info-macro-ref-item)
                           ('Syntax\ class:  'info-syntax-class-item)))
      (put-text-property (match-beginning 2) (match-end 2)
                         (if (> emacs-major-version 21) 'font-lock-face 'face)
                         'info-reference-item))))


;; REPLACES ORIGINAL in `info.el':
;; 1. Fits frame if `one-window-p'.
;; 2. Highlights the found regexp if `search-highlight'.
;;
(unless (>= emacs-major-version 22)
  (defun Info-search (regexp)
    "Search for REGEXP, starting from point, and select node it's found in.
Fits frame if `one-window-p'.
Highlights current location of found regexp if `search-highlight'.
Note that the highlighting remains, after the search is over.
To remove the highlighting, just start an incremental search: \
`\\[isearch-forward]'."
    (interactive "sSearch (regexp): ")
    (when transient-mark-mode (deactivate-mark))
    (if (equal regexp "") (setq regexp  Info-last-search) (setq Info-last-search  regexp))
    (when regexp
      (prog1
          (let ((found     ()) current
                (onode     Info-current-node)
                (ofile     Info-current-file)
                (opoint    (point))
                (ostart    (window-start))
                (osubfile  Info-current-subfile))
            (save-excursion
              (save-restriction
                (widen)
                (if (null Info-current-subfile)
                    (progn (re-search-forward regexp) (setq found  (point)))
                  (condition-case err
                      (progn (re-search-forward regexp) (setq found  (point)))
                    (search-failed nil)))))
            ;; Can only happen in subfile case -- else would have erred.
            (unless found
              (unwind-protect
                   (let ((list  ()))
                     (with-current-buffer (marker-buffer Info-tag-table-marker)
                       (goto-char (point-min))
                       (search-forward "\n\^_\nIndirect:")
                       (save-restriction
                         (narrow-to-region (point) (progn (search-forward "\n\^_") (1- (point))))
                         (goto-char (point-min))
                         (search-forward (concat "\n" osubfile ": "))
                         (beginning-of-line)
                         (while (not (eobp))
                           (re-search-forward "\\(^.*\\): [0-9]+$")
                           (goto-char (+ (match-end 1) 2))
                           (setq list  (cons (cons (read (current-buffer))
                                                   (buffer-substring (match-beginning 1)
                                                                     (match-end 1)))
                                             list))
                           (goto-char (1+ (match-end 0))))
                         (setq list     (nreverse list)
                               current  (caar list)
                               list     (cdr list))))
                     (while list
                       (message "Searching subfile `%s'..." (cdr (car list)))
                       (Info-read-subfile (car (car list)))
                       (setq list  (cdr list))
                       ;; (goto-char (point-min))
                       (when (re-search-forward regexp nil t)
                         (setq found  (point)
                               list   ())))
                     (if found (message "") (signal 'search-failed (list regexp))))
                (unless found
                  (Info-read-subfile osubfile)
                  (goto-char opoint)
                  (Info-select-node)
                  (set-window-start (selected-window) ostart))))
            (widen)
            (goto-char found)
            (when search-highlight
              (isearch-highlight (match-beginning 0) (match-end 0)))
            (Info-select-node)
            ;; Use string-equal, not equal, to ignore text props.
            (or (and (string-equal onode Info-current-node)
                     (equal ofile Info-current-file))
                (setq Info-history  (cons (list ofile onode opoint) Info-history)))
            (when (and (one-window-p t) (not (window-minibuffer-p))
                       (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                       Info-fit-frame-flag)
              (fit-frame)))
        (when (interactive-p)
          (message (substitute-command-keys
                    "Use \\<Info-mode-map>`\\[Info-search] RET' to search again for `%s'.")
                   regexp))))))


;; REPLACES ORIGINAL in `info.el':
;; 1. Fits frame if `one-window-p'.
;; 2. Highlights the found regexp if `search-highlight'.
;;
(when (= emacs-major-version 22)
  (defun Info-search (regexp &optional bound noerror count direction)
    "Search for REGEXP, starting from point, and select node it's found in.
If DIRECTION is `backward', search in the reverse direction.
Fits frame if `one-window-p'.
Highlights current location of found regexp if `search-highlight'.
Note that the highlighting remains, after the search is over.
To remove the highlighting, just start an incremental search: \
`\\[isearch-forward]'."
    (interactive
     (list (let ((prompt  (if Info-search-history
                              (format "Regexp search%s (default `%s'): "
                                      (if case-fold-search "" " case-sensitively")
                                      (car Info-search-history))
                            (format "Regexp search%s: "
                                    (if case-fold-search "" " case-sensitively")))))
             (if (fboundp 'icicle-read-string-completing)
                 (icicle-read-string-completing prompt nil nil 'Info-search-history)
               (read-string prompt nil 'Info-search-history)))))
    (when transient-mark-mode (deactivate-mark))
    (when (equal regexp "") (setq regexp  (car Info-search-history)))
    (when regexp
      (prog1
          (let (found beg-found give-up
                      (backward    (eq direction 'backward))
                      (onode       Info-current-node)
                      (ofile       Info-current-file)
                      (opoint      (point))
                      (opoint-min  (point-min))
                      (opoint-max  (point-max))
                      (ostart      (window-start))
                      (osubfile    Info-current-subfile))
            (setq Info-search-case-fold  case-fold-search) ; `Info-search-case-fold' is free here.
            (save-excursion
              (save-restriction
                (widen)
                (when backward
                  ;; Hide Info file header for backward search
                  (narrow-to-region (save-excursion
                                      (goto-char (point-min))
                                      (search-forward "\n\^_")
                                      (1- (point)))
                                    (point-max)))
                (while (and (not give-up)
                            (save-match-data
                              (or (null found)
                                  (if backward
                                      (isearch-range-invisible found beg-found)
                                    (isearch-range-invisible beg-found found))
                                  ;; Skip node header line
                                  (and (save-excursion (forward-line -1)
                                                       (looking-at "\^_"))
                                       (forward-line (if backward -1 1)))
                                  ;; Skip Tag Table node
                                  (save-excursion
                                    (and (search-backward "\^_" nil t)
                                         (looking-at "\^_\nTag Table"))))))
                  (let ((search-spaces-regexp  Info-search-whitespace-regexp)) ; `Info-*' is free here.
                    (if (if backward
                            (re-search-backward regexp bound t)
                          (re-search-forward regexp bound t))
                        (setq found      (point)
                              beg-found  (if backward (match-end 0) (match-beginning 0)))
                      (setq give-up  t))))))

            (when (and isearch-mode Info-isearch-search ; `Info-isearch-search' is free here.
                       (not Info-isearch-initial-node) ; `Info-isearch-initial-node' is free here.
                       (not bound)
                       (or give-up (and found (not (and (> found opoint-min)
                                                        (< found opoint-max))))))
              (signal 'search-failed (list regexp "initial node")))

            ;; If no subfiles, give error now.
            (if give-up
                (if (null Info-current-subfile)
                    (let ((search-spaces-regexp  Info-search-whitespace-regexp)) ; `Info-*' free here.
                      (if backward (re-search-backward regexp) (re-search-forward regexp)))
                  (setq found  nil)))

            (if (and bound (not found))
                (signal 'search-failed (list regexp)))

            (unless (or found bound)
              (unwind-protect
                   ;; Try other subfiles.
                   (let ((list  ()))
                     (with-current-buffer (marker-buffer Info-tag-table-marker)
                       (goto-char (point-min))
                       (search-forward "\n\^_\nIndirect:")
                       (save-restriction
                         (narrow-to-region (point)
                                           (progn (search-forward "\n\^_")
                                                  (1- (point))))
                         (goto-char (point-min))
                         ;; Find the subfile we just searched.
                         (search-forward (concat "\n" osubfile ": "))
                         ;; Skip that one.
                         (forward-line (if backward 0 1))
                         (if backward (forward-char -1))
                         ;; Make a list of all following subfiles.
                         ;; Each elt has the form (VIRT-POSITION . SUBFILENAME).
                         (while (not (if backward (bobp) (eobp)))
                           (if backward
                               (re-search-backward "\\(^.*\\): [0-9]+$")
                             (re-search-forward "\\(^.*\\): [0-9]+$"))
                           (goto-char (+ (match-end 1) 2))
                           (setq list  (cons (cons (+ (point-min) (read (current-buffer)))
                                                   (match-string-no-properties 1))
                                             list))
                           (goto-char (if backward
                                          (1- (match-beginning 0))
                                        (1+ (match-end 0)))))
                         ;; Put in forward order
                         (setq list  (nreverse list))))
                     (while list
                       (message "Searching subfile %s..." (cdr (car list)))
                       (Info-read-subfile (car (car list)))
                       (when backward
                         ;; Hide Info file header for backward search
                         (narrow-to-region (save-excursion
                                             (goto-char (point-min))
                                             (search-forward "\n\^_")
                                             (1- (point)))
                                           (point-max))
                         (goto-char (point-max)))
                       (setq list     (cdr list)
                             give-up  nil
                             found    nil)
                       (while (and (not give-up)
                                   (save-match-data
                                     (or (null found)
                                         (if backward
                                             (isearch-range-invisible found beg-found)
                                           (isearch-range-invisible beg-found found))
                                         ;; Skip node header line
                                         (and (save-excursion (forward-line -1)
                                                              (looking-at "\^_"))
                                              (forward-line (if backward -1 1)))
                                         ;; Skip Tag Table node
                                         (save-excursion
                                           (and (search-backward "\^_" nil t)
                                                (looking-at "\^_\nTag Table"))))))
                         (let ((search-spaces-regexp  Info-search-whitespace-regexp)) ; Free var.
                           (if (if backward
                                   (re-search-backward regexp nil t)
                                 (re-search-forward regexp nil t))
                               (setq found      (point)
                                     beg-found  (if backward (match-end 0) (match-beginning 0)))
                             (setq give-up  t))))
                       (when give-up (setq found  nil))
                       (when found (setq list  ())))
                     (if found (message "") (signal 'search-failed (list regexp))))
                (if (not found)
                    (progn (Info-read-subfile osubfile)
                           (goto-char opoint)
                           (Info-select-node)
                           (set-window-start (selected-window) ostart)))))

            (if (and (string= osubfile Info-current-subfile)
                     (> found opoint-min)
                     (< found opoint-max))
                ;; Search landed in the same node
                (goto-char found)
              (widen)
              (goto-char found)
              (save-match-data (Info-select-node)))

            ;; Highlight regexp.
            (when search-highlight
              (isearch-highlight (match-beginning 0) (match-end 0)))

            ;; Use string-equal, not equal, to ignore text props.
            (or (and (string-equal onode Info-current-node)
                     (equal ofile Info-current-file))
                (and isearch-mode isearch-wrapped
                     (eq opoint (if isearch-forward opoint-min opoint-max)))
                (setq Info-history  (cons (list ofile onode opoint) Info-history)))
            (when (and (one-window-p t) (not (window-minibuffer-p))
                       (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                       Info-fit-frame-flag)
              (fit-frame)))
        (unless isearch-mode
          (message (substitute-command-keys
                    "Use \\<Info-mode-map>`\\[Info-search] RET' to search again for `%s'.")
                   regexp))))))


;; REPLACES ORIGINAL in `info.el':
;; 1. Fits frame if `one-window-p'.
;; 2. Highlights the found regexp if `search-highlight'.
;;
(when (> emacs-major-version 22)
  (defun Info-search (regexp &optional bound noerror count direction)
    "Search for REGEXP, starting from point, and select node it's found in.
If DIRECTION is `backward', search in the reverse direction.
Fits frame if `one-window-p'.
Highlights current location of found regexp if `search-highlight'.
Note that the highlighting remains, after the search is over.
To remove the highlighting, just start an incremental search: \
`\\[isearch-forward]'."
    (interactive
     (list (let ((prompt  (if Info-search-history
                              (format "Regexp search%s (default `%s'): "
                                      (if case-fold-search "" " case-sensitively")
                                      (car Info-search-history))
                            (format "Regexp search%s: "
                                    (if case-fold-search "" " case-sensitively")))))
             (if (fboundp 'icicle-read-string-completing)
                 (icicle-read-string-completing prompt nil nil 'Info-search-history)
               (read-string prompt nil 'Info-search-history)))))
    (deactivate-mark)
    (when (equal regexp "")
      (setq regexp  (car Info-search-history)))
    (when regexp
      (prog1
          (let (found beg-found give-up
                      (backward    (eq direction 'backward))
                      (onode       Info-current-node)
                      (ofile       Info-current-file)
                      (opoint      (point))
                      (opoint-min  (point-min))
                      (opoint-max  (point-max))
                      (ostart      (window-start))
                      (osubfile    Info-current-subfile))
            (setq Info-search-case-fold  case-fold-search) ; `Info-search-case-fold' is free here.
            (save-excursion
              (save-restriction
                (widen)
                (when backward
                  ;; Hide Info file header for backward search
                  (narrow-to-region (save-excursion
                                      (goto-char (point-min))
                                      (search-forward "\n\^_")
                                      (1- (point)))
                                    (point-max)))
                (while (and (not give-up)
                            (or (null found)
                                (not (funcall isearch-filter-predicate beg-found found))))
                  (let ((search-spaces-regexp  (and (or (not isearch-mode) isearch-regexp)
                                                    ;; `Info-*' is free here.
                                                    Info-search-whitespace-regexp)))
                    (if (if backward
                            (re-search-backward regexp bound t)
                          (re-search-forward regexp bound t))
                        (setq found      (point)
                              beg-found  (if backward (match-end 0) (match-beginning 0)))
                      (setq give-up  t))))))

            (when (and isearch-mode Info-isearch-search ; `Info-isearch-search' is free here.
                       (not Info-isearch-initial-node) ; `Info-isearch-initial-node' is free here.
                       (not bound)
                       (or give-up (and found (not (and (> found opoint-min) (< found opoint-max))))))
              (signal 'search-failed (list regexp "initial node")))

            ;; If no subfiles, give error now.
            (if give-up
                (if (null Info-current-subfile)
                    (let ((search-spaces-regexp  (and (or (not isearch-mode) isearch-regexp)
                                                      ;; `Info-*' is free here.
                                                      Info-search-whitespace-regexp)))
                      (if backward (re-search-backward regexp) (re-search-forward regexp)))
                  (setq found  nil)))

            (when (and bound (not found)) (signal 'search-failed (list regexp)))

            (unless (or found bound)
              (unwind-protect
                   ;; Try other subfiles.
                   (let ((list  ()))
                     (with-current-buffer (marker-buffer Info-tag-table-marker)
                       (goto-char (point-min))
                       (search-forward "\n\^_\nIndirect:")
                       (save-restriction
                         (narrow-to-region (point)
                                           (progn (search-forward "\n\^_")
                                                  (1- (point))))
                         (goto-char (point-min))
                         ;; Find the subfile we just searched.
                         (search-forward (concat "\n" osubfile ": "))
                         ;; Skip that one.
                         (forward-line (if backward 0 1))
                         (if backward (forward-char -1))
                         ;; Make a list of all following subfiles.
                         ;; Each elt has the form (VIRT-POSITION . SUBFILENAME).
                         (while (not (if backward (bobp) (eobp)))
                           (if backward
                               (re-search-backward "\\(^.*\\): [0-9]+$")
                             (re-search-forward "\\(^.*\\): [0-9]+$"))
                           (goto-char (+ (match-end 1) 2))
                           (setq list  (cons (cons (+ (point-min) (read (current-buffer)))
                                                   (match-string-no-properties 1))
                                             list))
                           (goto-char (if backward
                                          (1- (match-beginning 0))
                                        (1+ (match-end 0)))))
                         ;; Put in forward order
                         (setq list  (nreverse list))))
                     (while list
                       (message "Searching subfile %s..." (cdr (car list)))
                       (Info-read-subfile (car (car list)))
                       (when backward
                         ;; Hide Info file header for backward search
                         (narrow-to-region (save-excursion
                                             (goto-char (point-min))
                                             (search-forward "\n\^_")
                                             (1- (point)))
                                           (point-max))
                         (goto-char (point-max)))
                       (setq list     (cdr list)
                             give-up  nil
                             found    nil)
                       (while (and (not give-up)
                                   (or (null found)
                                       (not (funcall isearch-filter-predicate beg-found found))))
                         (let ((search-spaces-regexp  (and (or (not isearch-mode) isearch-regexp)
                                                           ;; `Info-*' is free here.
                                                           Info-search-whitespace-regexp)))
                           (if (if backward
                                   (re-search-backward regexp nil t)
                                 (re-search-forward regexp nil t))
                               (setq found      (point)
                                     beg-found  (if backward (match-end 0) (match-beginning 0)))
                             (setq give-up  t))))
                       (when give-up (setq found  nil))
                       (when found (setq list  ())))
                     (if found (message "") (signal 'search-failed (list regexp))))
                (unless found
                  (Info-read-subfile osubfile)
                  (goto-char opoint)
                  (Info-select-node)
                  (set-window-start (selected-window) ostart))))

            (if (and (string= osubfile Info-current-subfile)
                     (> found opoint-min) (< found opoint-max))
                ;; Search landed in the same node
                (goto-char found)
              (widen)
              (goto-char found)
              (save-match-data (Info-select-node)))

            ;; Highlight regexp.
            (when search-highlight (isearch-highlight (match-beginning 0) (match-end 0)))

            ;; Use string-equal, not equal, to ignore text props.
            (or (and (string-equal onode Info-current-node) (equal ofile Info-current-file))
                (and isearch-mode isearch-wrapped
                     (eq opoint (if isearch-forward opoint-min opoint-max)))
                (setq Info-history  (cons (list ofile onode opoint) Info-history)))

            ;; Fit the frame, if appropriate.
            (when (and (one-window-p t) (not (window-minibuffer-p))
                       (fboundp 'fit-frame) ; Defined in `fit-frame.el'.
                       Info-fit-frame-flag)
              (fit-frame)))
        (unless isearch-mode
          (message (substitute-command-keys
                    "Use \\<Info-mode-map>`\\[Info-search] RET' to search again for `%s'.")
                   regexp))))))


;; REPLACES ORIGINAL in `info.el':
;; Added optional arg FORK.
;;
(when (>= emacs-major-version 22)
  (defun Info-mouse-follow-nearest-node (click &optional fork)
    "\\<Info-mode-map>Follow a node reference near point.
Like \\[Info-menu], \\[Info-follow-reference], \\[Info-next], \\[Info-prev] or \\[Info-up] \
command, depending on where you click.
At end of the node's text, moves to the next node, or up if none.

With a prefix argument, open the node in a separate window."
    (interactive "e\nP")
    (mouse-set-point click)
    (and (not (Info-try-follow-nearest-node fork))
         (save-excursion (forward-line 1) (eobp))
         (Info-next-preorder))))


;; REPLACES ORIGINAL in `info.el':
;; Use `Info-mode-syntax-table' (bug #3312).
;; Doc string changed: displays all bindings.
;;
(when (< emacs-major-version 21)
  (defun Info-mode ()
    "\\<Info-mode-map>
Info mode provides commands for browsing through the Info doc tree.
Documentation in Info is divided into \"nodes\", each of which discusses
one topic and contains hyperlink references to other nodes which
discuss related topics.  Info has commands to follow the references.
The most important commands to know are: \
`\\[Info-mouse-follow-nearest-node]', `\\[Info-last]', and `\\[Info-search]'.

Help commands
-------------
\\[describe-mode]\tDisplay this help.
\\[Info-help]\tThe Info tutorial.  Learn about Info while using it.

Selecting other nodes (basic)
-----------------------------
\\[Info-mouse-follow-nearest-node]\tFollow a node reference you click.
\tThis works with menu items, cross references, \"Next\",
\t\"Previous\" and \"Up\" references.
\tAt end of node's text, goes to \"Next\", or \"Up\" if no \"Next\".
\\[Info-follow-nearest-node]\tLike `\\[Info-mouse-follow-nearest-node]', \
except cursor location, not mouse location.
\\[Info-last]\tGo back to the last node you were at. (chronological)

Structural navigation commands
------------------------------
\\[Info-menu]\tGo to a menu item's node.  Completion available for its name.
1\tGo to first menu item's node.
2, 3, 4, 5, 6, 7, 8, 9\tGo to second...ninth menu item's node.
\\[Info-next]\tGo to this node's \"Next\" node.
\\[Info-prev]\tGo to this node's \"Previous\" node.  (*not* chronological)
\\[Info-up]\tGo \"Up\" from this node to its parent node.
\\[Info-directory]\tGo to the Info directory (root) node.
\\[Info-index]\tLook up a topic in this file's Index and move to its node.
\\[Info-index-next]\t(comma) Go to the next match from a previous \
`\\[Info-index]' command.
\\[Info-follow-reference]\tFollow a cross reference. Prompts for name.

Moving within a node
--------------------
\\[Info-scroll-up]\tNormally, scroll forward a full screen.  If end of \
buffer is
\talready visible, try to go to next menu entry, or up if none.
\\[Info-scroll-down]\tNormally, scroll backward.  If beginning of buffer is \
already
\tvisible, try to go to previous menu entry, or up if none.
\\[beginning-of-buffer]\tGo to beginning of node.
\\[Info-next-reference]\tMove cursor to next cross-reference or menu item in \
this node.
\\[Info-prev-reference]\tMove cursor to previous cross-reference or menu item.

Other navigation commands
-------------------------
\\[Info-goto-node]\tGo to a node with a given name.
\tYou may include a filename as well, as \"(FILENAME)NODENAME\".
\\[universal-argument] \\[info]\tGo to a new Info file.  (Completion \
available.)
\\[Info-top-node]\tGo to first node (\"Top\") of current Info file.
\\[Info-final-node]\tGo to final node of current Info file.
\\[Info-forward-node]\tGo forward a node, considering all nodes as one \
sequence.
\\[Info-backward-node]\tGo backward a node, considering all nodes as one \
sequence.

Other commands
--------------
\\[Info-search]\tSearch this Info manual for a regexp.
\\[Info-edit]\tEdit contents of current node.  \
\(\\<Info-edit-map>`\\[Info-cease-edit]'\\<Info-mode-map> to end editing.)
\tEditing is enabled only if `Info-enable-edit' is non-nil.
\\[Info-merge-subnodes]\tIntegrate current node with nodes referred to \
in its Menu.
\tDisplay the result outside of Info.  `\\[universal-argument]': Recursively.
\\[Info-exit]\tQuit Info.

User options you can customize
------------------------------
`Info-fontify-quotations-flag' -
  Fontify quoted names (`...') and strings (\"...\")
`Info-subtree-separator' - See `Info-merge-subnodes'.

Faces you can customize
-----------------------
`info-file'   - Face used for file heading labels
`info-node'   - Face used for node heading labels
`info-menu'   - Face used for menu items
`info-xref'   - Face used for cross reference \"Note\" links
`info-string'       - Face used for strings (e.g. \"toto\").
`info-quoted-name'  - Face used for quoted names (e.g. `toto').
`info-single-quote' - Face used for isolated single-quote (e.g. 'foo).

These are all of the current Info Mode bindings:

\\{Info-mode-map}"
    (kill-all-local-variables)
    (setq major-mode  'Info-mode
          mode-name   "Info"
          tab-width   8)
    (use-local-map Info-mode-map)
    (make-local-hook 'activate-menubar-hook)
    (add-hook 'activate-menubar-hook 'Info-menu-update nil t)
    (set-syntax-table Info-mode-syntax-table)
    (setq local-abbrev-table  text-mode-abbrev-table
          case-fold-search    t
          buffer-read-only    t)
    (make-local-variable 'Info-current-file)
    (make-local-variable 'Info-current-subfile)
    (make-local-variable 'Info-current-node)
    (make-local-variable 'Info-tag-table-marker)
    (setq Info-tag-table-marker  (make-marker))
    (make-local-variable 'Info-tag-table-buffer)
    (setq Info-tag-table-buffer  nil)
    (make-local-variable 'Info-history)
    (make-local-variable 'Info-index-alternatives)
    ;; This is for the sake of the invisible text we use handling titles.
    (make-local-variable 'line-move-ignore-invisible)
    (setq line-move-ignore-invisible  t)
    (Info-set-mode-line)
    (run-hooks 'Info-mode-hook)))


;; REPLACES ORIGINAL in `info.el':
;; Use `Info-mode-syntax-table' (bug #3312).
;; Doc string changed: displays all bindings.
;;
(when (= emacs-major-version 21)

  ;; For some reason, this doesn't seem to be bound when `tool-bar.el' is loaded (?) in Emacs 21.
  (defvar tool-bar-map (make-sparse-keymap) ; Taken from `tool-bar.el'.
    "Keymap for the tool bar.
Define this locally to override the global tool bar.")

  (defun Info-mode ()
    "Info mode provides commands for browsing through the Info doc tree.
Documentation in Info is divided into \"nodes\", each of which discusses
one topic and contains hyperlink references to other nodes that discuss
related topics.  Info has commands to follow the references.
The most important commands to know are: \
\\<Info-mode-map>\
`\\[Info-exit]', `\\[Info-mouse-follow-nearest-node]', `\\[Info-last]', and `\\[Info-search]'.

Help commands
-------------
\\[describe-mode]\tDisplay this help.
\\[Info-help]\tThe Info tutorial.  Learn about Info while using it.

Selecting other nodes (basic)
-----------------------------
\\[Info-mouse-follow-nearest-node]\tFollow a node reference you click.
\tThis works with menu items, cross references, \"Next\",
\t\"Previous\" and \"Up\" references.
\tAt end of node's text, goes to \"Next\", or \"Up\" if no \"Next\".
\\[Info-follow-nearest-node]\tLike `\\[Info-mouse-follow-nearest-node]', \
except cursor location, not mouse location.
\\[Info-last]\tGo back to the last node you were at. (chronological)
\\[Info-history]\tGo to menu of visited nodes.
\\[Info-toc]\tGo to table of contents of the current Info file.
\\[Info-index]\tLook up a topic in this file's Index and move to its node.
\\[Info-index-next]\t(comma) Go to the next match from a previous \
`\\[Info-index]' command.

Structural navigation commands
------------------------------
\\[Info-menu]\tGo to a menu item's node.  Completion available for its name.
1\tGo to first menu item's node.
2, 3, 4, 5, 6, 7, 8, 9\tGo to second...ninth menu item's node.
\\[Info-next]\tGo to this node's \"Next\" node.
\\[Info-prev]\tGo to this node's \"Previous\" node.  (*not* chronological)
\\[Info-up]\tGo \"Up\" from this node to its parent node.
\\[Info-directory]\tGo to the Info directory (root) node.
\\[Info-follow-reference]\tFollow a cross reference. Prompts for name.

Moving within a node
--------------------
\\[Info-scroll-up]\tNormally, scroll forward a full screen.
\tIf node's menu appears below cursor, go to first menu item.
\tIf node's menu appears above cursor, go to parent node.
\\[Info-scroll-down]\tNormally, scroll backward.  If beginning of buffer is \
already
\tvisible, go to previous menu entry, or up if there is none.
\\[beginning-of-buffer]\tGo to beginning of node.
\\[Info-next-reference]\tMove cursor to next cross-reference or menu item in \
this node.
\\[Info-prev-reference]\tMove cursor to previous cross-reference or menu item.

Other navigation commands
-------------------------
\\[Info-exit]\tQuit Info.
\\[Info-goto-node]\tGo to a node with a given name.
\tYou may include a filename as well, as \"(FILENAME)NODENAME\".
\\[universal-argument] \\[info]\tGo to a new Info file.  (Completion \
available.)
\\[universal-argument] N \\[info]\tOpen Info with number in buffer name: *info*<N>.
\\[Info-top-node]\tGo to first node (\"Top\") of current Info file.
\\[Info-final-node]\tGo to final node of current Info file.
\\[Info-forward-node]\tGo forward a node, considering all nodes as one \
sequence.
\\[Info-backward-node]\tGo backward a node, considering all nodes as one \
sequence.

Other commands
--------------
\\[Info-search]\tSearch this Info manual for a regexp.
\\[Info-search-case-sensitively]\tLike \\[Info-search], but case-sensitive.
\\[Info-copy-current-node-name]\tPut name of current info node in the kill ring.
\\[clone-buffer]\tSelect a new cloned Info buffer in another window.
\\[Info-merge-subnodes]\tIntegrate current node with nodes referred to \
in its Menu.
\tDisplay the result outside of Info.  `\\[universal-argument]': Recursively.
\\[Info-edit]\tEdit contents of current node.  \
\(\\<Info-edit-map>`\\[Info-cease-edit]'\\<Info-mode-map> to end editing.)
\tEditing is enabled only if `Info-enable-edit' is non-nil.

User options you can customize
------------------------------
`Info-fontify-quotations-flag' -
  Fontify quoted names (`...') and strings (\"...\").
`Info-subtree-separator' - See `Info-merge-subnodes'.

Faces you can customize
-----------------------
`info-file'   - Face used for file heading labels
`info-string'       - Face used for strings (e.g. \"toto\").
`info-quoted-name'  - Face used for quoted names (e.g. `toto').
`info-single-quote' - Face used for isolated single-quote (e.g. 'foo).

These are all of the current Info Mode bindings:

\\{Info-mode-map}"
    (kill-all-local-variables)
    (setq major-mode  'Info-mode
          mode-name   "Info"
          tab-width   8)
    (use-local-map Info-mode-map)
    (add-hook 'activate-menubar-hook 'Info-menu-update nil t)
    (set-syntax-table Info-mode-syntax-table)
    (setq local-abbrev-table  text-mode-abbrev-table
          case-fold-search    t
          buffer-read-only    t)
    (make-local-variable 'Info-current-file)
    (make-local-variable 'Info-current-subfile)
    (make-local-variable 'Info-current-node)
    (make-local-variable 'Info-tag-table-marker)
    (setq Info-tag-table-marker  (make-marker))
    (make-local-variable 'Info-tag-table-buffer)
    (setq Info-tag-table-buffer  nil)
    (make-local-variable 'Info-history)
    (make-local-variable 'Info-index-alternatives)
    (set (make-local-variable 'tool-bar-map) info-tool-bar-map)
    ;; This is for the sake of the invisible text we use handling titles.
    (make-local-variable 'line-move-ignore-invisible)
    (setq line-move-ignore-invisible  t)
    (add-hook 'clone-buffer-hook 'Info-clone-buffer-hook nil t)
    (Info-set-mode-line)
    (run-hooks 'Info-mode-hook)))


;; REPLACES ORIGINAL in `info.el':
;; Use `Info-mode-syntax-table' (bug #3312).
;; Doc string changed: displays all bindings.
;;
(when (= emacs-major-version 22)
  (defun Info-mode ()
    "Provides commands for browsing through the Info documentation tree.
Documentation in Info is divided into \"nodes\", each of which discusses
one topic and contains hyperlink references to other nodes that discuss
related topics.  Info has commands to follow the references.
The most important commands to know are: \
\\<Info-mode-map>\
`\\[Info-exit]', `\\[Info-mouse-follow-nearest-node]', `\\[Info-history-back]', and `\\[Info-search]'.

Help commands
-------------
\\[describe-mode]\tDisplay this help.
\\[Info-help]\tThe Info tutorial.  Learn about Info while using it.

Selecting other nodes (basic)
-----------------------------
\\[Info-mouse-follow-nearest-node]\tFollow a node reference you click.
\tThis works with menu items, cross references, \"Next\",
\t\"Previous\" and \"Up\" references.
\tAt end of node's text, goes to \"Next\", or \"Up\" if no \"Next\".
\\[Info-follow-nearest-node]\tLike `\\[Info-mouse-follow-nearest-node]', \
except cursor location, not mouse location.
\\[Info-history-back]\tGo back to the last node you were at. (chronological)
\\[Info-history-forward]\tGo forward to where you were before using \\[Info-history-back].
\\[Info-history]\tGo to menu of visited nodes.
\\[Info-toc]\tGo to table of contents of the current Info file.
\\[Info-index]\tLook up a topic in this file's Index and move to its node.
\\[Info-index-next]\t(comma) Go to the next match from a previous \
`\\[Info-index]' command.

Structural navigation commands
------------------------------
\\[Info-menu]\tGo to a menu item's node.  Completion available for its name.
1\tGo to first menu item's node.
2, 3, 4, 5, 6, 7, 8, 9\tGo to second...ninth menu item's node.
\\[Info-next]\tGo to this node's \"Next\" node.
\\[Info-prev]\tGo to this node's \"Previous\" node.  (*not* chronological)
\\[Info-up]\tGo \"Up\" from this node to its parent node.
\\[Info-directory]\tGo to the Info directory (root) node.
\\[Info-follow-reference]\tFollow a cross reference. Prompts for name.

Moving within a node
--------------------
\\[Info-scroll-up]\tNormally, scroll forward a full screen.
\tIf node's menu appears below cursor, go to first menu item.
\tIf node's menu appears above cursor, go to parent node.
\\[Info-scroll-down]\tNormally, scroll backward.  If beginning of buffer is \
already
\tvisible, go to previous menu entry, or up if there is none.
\\[beginning-of-buffer]\tGo to beginning of node.
\\[Info-next-reference]\tMove cursor to next cross-reference or menu item in \
this node.
\\[Info-prev-reference]\tMove cursor to previous cross-reference or menu item.

Other navigation commands
-------------------------
\\[Info-exit]\tQuit Info.
\\[Info-goto-node]\tGo to a node with a given name.
\tYou may include a filename as well, as \"(FILENAME)NODENAME\".
\\[universal-argument] \\[info]\tGo to a new Info file.  (Completion \
available.)
\\[universal-argument] N \\[info]\tOpen Info with number in buffer name: *info*<N>.
\\[Info-top-node]\tGo to first node (\"Top\") of current Info file.
\\[Info-final-node]\tGo to final node of current Info file.
\\[Info-forward-node]\tGo forward a node, considering all nodes as one \
sequence.
\\[Info-backward-node]\tGo backward a node, considering all nodes as one \
sequence.

Other commands
--------------
\\[Info-save-current-node]\tSave current node name for use by `\\[Info-virtual-book]'.
\\[Info-virtual-book]\tOpen a virtual book saved using `\\[Info-save-current-node]' \
\(`C-u': bookmarks too).
\\[Info-search]\tSearch this Info manual for a regexp.
\\[Info-search-case-sensitively]\tLike \\[Info-search], but case-sensitive.
\\[info-apropos]\tLook for a string in the indexes of all manuals.
\\[Info-copy-current-node-name]\tPut name of current info node in the kill ring.
\\[clone-buffer]\tSelect a new cloned Info buffer in another window.
\\[Info-merge-subnodes]\tIntegrate current node with nodes referred to \
in its Menu.
\tDisplay the result outside of Info.  `\\[universal-argument]': Recursively.
\\[Info-edit]\tEdit contents of current node.  \
\(\\<Info-edit-map>`\\[Info-cease-edit]'\\<Info-mode-map> to end editing.)
\tEditing is enabled only if `Info-enable-edit' is non-nil.

User options you can customize
------------------------------
`Info-fontify-quotations-flag' -
  Fontify quoted names (`...') and strings (\"...\").
`Info-saved-nodes' - Node names you can visit using `\\[Info-virtual-book]'.
`Info-subtree-separator' - See `Info-merge-subnodes'.

Faces you can customize
-----------------------
`info-file'   - Face used for file heading labels
`info-string'       - Face used for strings (e.g. \"toto\").
`info-quoted-name'  - Face used for quoted names (e.g. `toto').
`info-single-quote' - Face used for isolated single-quote (e.g. 'foo).

These are all of the current Info Mode bindings:

\\{Info-mode-map}"
    (kill-all-local-variables)
    (setq major-mode  'Info-mode
          mode-name   "Info"
          tab-width   8)
    (use-local-map Info-mode-map)
    (add-hook 'activate-menubar-hook 'Info-menu-update nil t)
    (set-syntax-table Info-mode-syntax-table)
    (setq local-abbrev-table  text-mode-abbrev-table
          case-fold-search    t
          buffer-read-only    t)
    (make-local-variable 'Info-current-file)
    (make-local-variable 'Info-current-subfile)
    (make-local-variable 'Info-current-node)
    (make-local-variable 'Info-tag-table-marker)
    (setq Info-tag-table-marker  (make-marker))
    (make-local-variable 'Info-tag-table-buffer)
    (setq Info-tag-table-buffer  nil)
    (make-local-variable 'Info-history)
    (make-local-variable 'Info-history-forward)
    (make-local-variable 'Info-index-alternatives)
    (setq header-line-format  (if Info-use-header-line
                                  '(:eval (get-text-property (point-min) 'header-line))
                                nil))   ; so the header line isn't displayed
    (set (make-local-variable 'tool-bar-map) info-tool-bar-map)
    ;; This is for the sake of the invisible text we use handling titles.
    (make-local-variable 'line-move-ignore-invisible)
    (setq line-move-ignore-invisible  t)
    (make-local-variable 'desktop-save-buffer)
    (make-local-variable 'widen-automatically)
    (setq widen-automatically  nil      ; `widen-automatically' is free here.
          desktop-save-buffer  'Info-desktop-buffer-misc-data)
    (add-hook 'kill-buffer-hook 'Info-kill-buffer nil t)
    (if (fboundp 'Info-clone-buffer)
        (add-hook 'clone-buffer-hook 'Info-clone-buffer nil t) ; Emacs 22.1.90+
      (add-hook 'clone-buffer-hook 'Info-clone-buffer-hook nil t))
    (add-hook 'change-major-mode-hook 'font-lock-defontify nil t)
    (add-hook 'isearch-mode-hook 'Info-isearch-start nil t)
    ;; The `Info-*' variables are free here.
    (set (make-local-variable 'isearch-search-fun-function) 'Info-isearch-search)
    (set (make-local-variable 'isearch-wrap-function) 'Info-isearch-wrap)
    (set (make-local-variable 'isearch-push-state-function) 'Info-isearch-push-state)
    (set (make-local-variable 'search-whitespace-regexp) Info-search-whitespace-regexp)
    (Info-set-mode-line)
    (run-mode-hooks 'Info-mode-hook)))


;; REPLACES ORIGINAL in `info.el':
;; Use `Info-mode-syntax-table' (bug #3312).
;; Doc string changed: displays all bindings.
;;
(when (> emacs-major-version 22)
  (defun Info-mode ()
    "Provides commands for browsing through the Info documentation tree.
Documentation in Info is divided into \"nodes\", each of which discusses
one topic and contains hyperlink references to other nodes that discuss
related topics.  Info has commands to follow the references.
The most important commands to know are: \
\\<Info-mode-map>\
`\\[Info-exit]', `\\[Info-mouse-follow-nearest-node]', `\\[Info-history-back]', and `\\[Info-search]'.

Help commands
-------------
\\[describe-mode]\tDisplay this help.
\\[Info-help]\tThe Info tutorial.  Learn about Info while using it.

Selecting other nodes (basic)
-----------------------------
\\[Info-mouse-follow-nearest-node]\tFollow a node reference you click.
\tThis works with menu items, cross references, \"Next\",
\t\"Previous\" and \"Up\" references.
\tAt end of node's text, goes to \"Next\", or \"Up\" if no \"Next\".
\\[Info-follow-nearest-node]\tLike `\\[Info-mouse-follow-nearest-node]', \
except cursor location, not mouse location.
\\[Info-history-back]\tGo back to the last node you were at. (chronological)
\\[Info-history-forward]\tGo forward to where you were before using \\[Info-history-back].
\\[Info-history]\tGo to menu of visited nodes.
\\[Info-toc]\tGo to table of contents of the current Info file.
\\[Info-index]\tLook up a topic in this file's Index and move to its node.
\\[Info-index-next]\t(comma) Go to the next match from a previous \
`\\[Info-index]' command.

Structural navigation commands
------------------------------
\\[Info-menu]\tGo to a menu item's node.  Completion available for its name.
1\tGo to first menu item's node.
2, 3, 4, 5, 6, 7, 8, 9\tGo to second...ninth menu item's node.
\\[Info-next]\tGo to this node's \"Next\" node.
\\[Info-prev]\tGo to this node's \"Previous\" node.  (*not* chronological)
\\[Info-up]\tGo \"Up\" from this node to its parent node.
\\[Info-directory]\tGo to the Info directory (root) node.
\\[Info-follow-reference]\tFollow a cross reference. Prompts for name.

Moving within a node
--------------------
\\[Info-scroll-up]\tNormally, scroll forward a full screen.
\tIf node's menu appears below cursor, go to first menu item.
\tIf node's menu appears above cursor, go to parent node.
\\[Info-scroll-down]\tNormally, scroll backward.  If beginning of buffer is \
already
\tvisible, go to previous menu entry, or up if there is none.
\\[beginning-of-buffer]\tGo to beginning of node.
\\[Info-next-reference]\tMove cursor to next cross-reference or menu item in \
this node.
\\[Info-prev-reference]\tMove cursor to previous cross-reference or menu item.

Other navigation commands
-------------------------
\\[Info-exit]\tQuit Info.
\\[Info-goto-node]\tGo to a node with a given name.
\tYou may include a filename as well, as \"(FILENAME)NODENAME\".
\\[universal-argument] \\[info]\tGo to a new Info file.  (Completion \
available.)
\\[universal-argument] N \\[info]\tOpen Info with number in buffer name: *info*<N>.
\\[Info-top-node]\tGo to first node (\"Top\") of current Info file.
\\[Info-final-node]\tGo to final node of current Info file.
\\[Info-forward-node]\tGo forward a node, considering all nodes as one \
sequence.
\\[Info-backward-node]\tGo backward a node, considering all nodes as one \
sequence.

Other commands
--------------
\\[Info-save-current-node]\tSave current node name for use by `\\[Info-virtual-book]'.
\\[Info-virtual-book]\tOpen a virtual Info book of nodes saved using `\\[Info-save-current-node]'.
\\[isearch-forward]\tIsearch this Info manual for a literal string.
\\[isearch-forward-regexp]\tIsearch this Info manual for a regexp.
\\[Info-search]\tSearch this Info manual for a regexp
\\[Info-search-case-sensitively]\tLike `\\[Info-search]', but case-sensitive.
\\[info-apropos]\tLook for a string in the indexes of all manuals.
\\[Info-copy-current-node-name]\tPut name of current info node in the kill ring.
\\[clone-buffer]\tSelect a new cloned Info buffer in another window.
\\[Info-merge-subnodes]\tIntegrate current node with nodes referred to \
in its Menu.
\tDisplay the result outside of Info.  `\\[universal-argument]': Recursively.
\\[Info-edit]\tEdit contents of current node.  \
\(\\<Info-edit-map>`\\[Info-cease-edit]'\\<Info-mode-map> to end editing.)
\tEditing is enabled only if `Info-enable-edit' is non-nil.

User options you can customize
------------------------------
`Info-fontify-quotations-flag' -
  Fontify quoted names (`...') and strings (\"...\").
`Info-saved-nodes' - Node names you can visit using `\\[Info-virtual-book]'.
`Info-subtree-separator' - See `Info-merge-subnodes'.

Faces you can customize
-----------------------
`info-file'   - Face used for file heading labels
`info-string'       - Face used for strings (e.g. \"toto\").
`info-quoted-name'  - Face used for quoted names (e.g. `toto').
`info-single-quote' - Face used for isolated single-quote (e.g. 'foo).

These are all of the current Info Mode bindings:

\\{Info-mode-map}"
    (kill-all-local-variables)
    (setq major-mode  'Info-mode
          mode-name   "Info"
          tab-width   8)
    (use-local-map Info-mode-map)
    (add-hook 'activate-menubar-hook 'Info-menu-update nil t)
    (set-syntax-table Info-mode-syntax-table)
    (setq local-abbrev-table  text-mode-abbrev-table
          case-fold-search    t
          buffer-read-only    t)
    (make-local-variable 'Info-current-file)
    (make-local-variable 'Info-current-subfile)
    (make-local-variable 'Info-current-node)
    (make-local-variable 'Info-tag-table-marker)
    (setq Info-tag-table-marker  (make-marker))
    (make-local-variable 'Info-tag-table-buffer)
    (setq Info-tag-table-buffer  nil)
    (make-local-variable 'Info-history)
    (make-local-variable 'Info-history-forward)
    (make-local-variable 'Info-index-alternatives)
    (when Info-use-header-line          ; do not override global header lines
      (setq header-line-format  '(:eval (get-text-property (point-min) 'header-line))))
    (set (make-local-variable 'tool-bar-map) info-tool-bar-map)
    ;; This is for the sake of the invisible text we use handling titles.
    (make-local-variable 'line-move-ignore-invisible)
    (setq line-move-ignore-invisible  t)
    (make-local-variable 'desktop-save-buffer)
    (make-local-variable 'widen-automatically)
    (setq widen-automatically  nil)     ; `widen-automatically' is free here.
    (setq desktop-save-buffer  'Info-desktop-buffer-misc-data)
    (add-hook 'kill-buffer-hook 'Info-kill-buffer nil t)
    (add-hook 'clone-buffer-hook 'Info-clone-buffer nil t)
    (add-hook 'change-major-mode-hook 'font-lock-defontify nil t)
    (add-hook 'isearch-mode-hook 'Info-isearch-start nil t)
    ;; The `Info-*' variables are free here.
    (set (make-local-variable 'isearch-search-fun-function) 'Info-isearch-search)
    (set (make-local-variable 'isearch-wrap-function) 'Info-isearch-wrap)
    (set (make-local-variable 'isearch-push-state-function) 'Info-isearch-push-state)
    (set (make-local-variable 'isearch-filter-predicate) 'Info-isearch-filter)
    (set (make-local-variable 'search-whitespace-regexp) Info-search-whitespace-regexp)
    (set (make-local-variable 'revert-buffer-function) 'Info-revert-buffer-function)
    (Info-set-mode-line)
    (set (make-local-variable 'bookmark-make-record-function) 'Info-bookmark-make-record)
    (run-mode-hooks 'Info-mode-hook)))


;; REPLACES ORIGINAL in `info.el':
;;
;; Use completion for inputting the manual name. 
;;
(when (> emacs-major-version 22)
  (defun info-display-manual (manual)
    "Go to Info buffer that displays MANUAL, creating it if none already exists."
    ;;  (interactive "sManual name: ")
    (interactive
     (let ((manuals  ()))
       (condition-case nil
           (with-temp-buffer
             (Info-mode)
             (Info-directory)
             (goto-char (point-min))
             (re-search-forward "\\* Menu: *\n" nil t)
             (let (manual)
               (while (re-search-forward "\\*.*: *(\\([^)]+\\))" nil t)
                 ;; `add-to-list' ensures no dups in `manuals', so the `dolist' runs faster.
                 (setq manual  (match-string 1))
                 (set-text-properties 0 (length manual) nil manual)
                 (add-to-list 'manuals (list manual)))))
         (error nil))
       (list (completing-read "Display manual: " manuals))))
    (let ((blist (buffer-list))
          (manual-re (concat "\\(/\\|\\`\\)" manual "\\(\\.\\|\\'\\)"))
          (case-fold-search t)
          found)
      (dolist (buffer blist)
        (with-current-buffer buffer
          (when (and (eq major-mode 'Info-mode)
                     (stringp Info-current-file)
                     (string-match manual-re Info-current-file))
            (setq found  buffer
                  blist  ()))))
      (if found
          (switch-to-buffer found)
        (info-initialize)
        (info (Info-find-file manual))))))

(defun Info-display-node-default-header ()
  "Insert node name as header."
  ;; `node-name' is free here - bound in `Info-merge-subnodes'.
  (insert (if (fboundp 'concat-w-faces)
              (concat-w-faces (if (< emacs-major-version 21)
                                  (list 'info-node node-name)
                                (list 'Info-title-1-face node-name)))
            node-name)
          "\n")
  (beginning-of-buffer)
  (center-line 2))

;; Not currently used.
(defun Info-display-node-time-header ()
  "Insert current time and node name as header."
  ;; `node-name' is free here - bound in `Info-merge-subnodes'.
  (insert (current-time-string) "    " node-name)
  (beginning-of-buffer)
  (center-line))

(when (> emacs-major-version 21)
  (defcustom Info-saved-nodes ()
    "*List of Info node names you can visit using `\\<Info-mode-map>\\[Info-virtual-book]'.
Each node name is a string.  The node name can be absolute, including
a filename, such as \"(emacs)Basic\", or it can be relative, such as
\"Basic\".
You can customize this option, but you can also add node names to it
easily using `\\<Info-mode-map>\\[Info-save-current-node]'."
    :type '(repeat (string :tag "Node name")) :group 'info))

(when (> emacs-major-version 21)
  (defun Info-virtual-book (book nodes &optional include-bookmark-nodes-p)
    "Open a virtual Info BOOK, with a menu of Info NODES.
BOOK is a string naming the virtual book.
NODES is a list of strings naming Info nodes.
  Each node name is normally absolute, that is, a
  filename-plus-nodename string such as \"(emacs)Basic\".  But if you
  call this command from an Info buffer, then a node name can be
  relative, such as \"Basic\".
Non-nil optional arg INCLUDE-BOOKMARK-NODES-P means that all Info
nodes recorded as bookmarks are included in the virtual book.

Interactively, you are prompted for the name of the virtual book, and
the nodes are those in `Info-saved-nodes'.  Interactively, a prefix
argument says to include Info nodes recorded as bookmarks."
    (interactive (list (read-from-minibuffer "Virtual book name: " nil nil nil nil "Virtual Book")
                       Info-saved-nodes
                       current-prefix-arg))
    (unless nodes (setq nodes  Info-saved-nodes))
    (when include-bookmark-nodes-p
      (unless (require 'bookmark+ nil t) (require 'bookmark nil t))
      (bookmark-maybe-load-default-file)
      (let ((bm-nodes  ())
            node file)
        (dolist (bm  bookmark-alist)
          (when (setq node  (cdr (assq 'info-node bm)))
            (setq file  (bookmark-get-filename bm))
            (push (concat "(" (file-name-nondirectory (cdr (assq 'filename bm))) ")" node) bm-nodes)))
        (setq nodes  (append nodes bm-nodes))))
    (unless (and nodes (stringp (car nodes))) ; Minimal sanity check.
      (error (if (interactive-p) "No saved Info nodes" "No Info nodes")))
    (unless (stringp book) (setq book  "Virtual Book")) ; Non-interactive - NODESET is a list.
    (let ((file  (and (stringp Info-current-file)
                      (concat "(" (file-name-nondirectory Info-current-file) ")"))))
      (with-current-buffer (get-buffer-create " *info-toc*")
        (let ((inhibit-read-only  t)
              sans-file filep)
          (erase-buffer)
          (goto-char (point-min))
          (insert "\n\^_\nFile: toc,  Node: Top,  Up: (dir)\n\n")
          (insert book "\n" (make-string (length book) ?*) "\n\n")
          (insert "* Menu:\n\n")
          (while nodes
            (if (setq filep  (string-match "^([^)]+)" (car nodes)))
                (setq sans-file  (substring (car nodes) (match-end 0)))
              (setq sans-file  (car nodes)))
            ;; (insert "* " sans-file ": " (car nodes) ".\n")
            (insert "* " sans-file ": "
                    (concat (and (not filep) (or file "(**INFO FILE UNKNOWN**)")) (car nodes))
                    ".\n")
            (setq nodes  (cdr nodes))))
        (if (not (bobp))
            (let ((Info-hide-note-references   'hide)
                  (Info-fontify-visited-nodes  ()))
              (Info-mode)
              (setq Info-current-file 'toc Info-current-node "Top")
              (goto-char (point-min))
              (narrow-to-region (or (re-search-forward "\n[\^_\f]\n" nil t) (point-min)) (point-max))
              (Info-fontify-node)
              (widen)))))
    (info)
    (Info-find-node 'toc "Top")))

(when (> emacs-major-version 21)
  (defun Info-save-current-node ()
    "Save name of current Info node to list `Info-saved-nodes'."
    (interactive)
    (unless (eq major-mode 'Info-mode) (error "You must be in Info to use this command"))
    (unless Info-current-node (error "No current Info node"))
    (unless Info-current-file (error "No Info file"))
    (add-to-list 'Info-saved-nodes (concat "(" (file-name-nondirectory Info-current-file) ")"
                                           Info-current-node))
    (message (format "Node `%s' saved" Info-current-node))))


;; Note: This is not super-clean code (it's kind of a hack job).
;;;###autoload
(defun Info-merge-subnodes (&optional recursive-display-p recursive-call-p)
  "Integrate current node with nodes referred to in its Menu.

Displays the current Info node, together with the nodes in its Menu.
Buffer `*Info: NODE*' is used for the display, where NODE is the name
of the current node.  The contents of this node's subnodes (the nodes
named in this node's Menu) are included in the buffer, following the
contents of the current node.

Optional arg RECURSIVE-DISPLAY-P (prefix arg if interactive) governs
the way menus of subnodes are treated:

  If nil, nothing additional happens.  Subnode menus are not explored.
  Only the current node and its immediate subnodes are documented, in
  the single display buffer `*Info: NODE*'.

  If non-nil, then the subnodes of a node are treated in the same way
  as the parent node, recursively: If any of them has, itself, a Menu,
  then that menu's subnodes are also explored, and so on.

    If RECURSIVE-DISPLAY-P is zero, then a single display buffer is
    used for all of the nodes explored.  Otherwise, a separate display
    buffer is used for each subnode that has a Menu (see next).

      Use this when you want a single, flat compilation of the current
      node and all of its subnodes.  It is less appropriate when the
      current node has several levels of subnodes: The flattened
      result can be difficult to read.

    If RECURSIVE-DISPLAY-P is positive, then the contents of each
    subnode are displayed twice: once in the parent node's display,
    and once in the subnode's own display.

      Use this when the current node has several levels of subnodes
      and you want each display buffer to be self-contained.

    If RECURSIVE-DISPLAY-P is negative, then there is no redundancy: A
    subnode's contents are only displayed in its parent's buffer.  The
    subnode's own display buffer only contains the contents of its own
    subnodes.

      Use this when the current node has several levels of subnodes
      and you want no redundancy between the display buffers.

The user option (variable) `Info-subtree-separator' is a string to be
inserted by `Info-merge-subnodes' just before the title of each
node (preceding its description).  By default it is \"\\n* \", producing
a node title resembling a menu item.  Setting this to \"\\f\\n* \" will
cause a page break before each node description.  For more on setting
this variable, type \\<Info-mode-map>`\\[describe-variable] Info-subtree-separator'.

------

Optional second arg RECURSIVE-CALL-P is only for internal use.  It is
used to indicate whether (non-nil) or not (nil) this is a recursive
\(i.e. not a top-level) call to `Info-merge-subnodes'.  Non-nil
means that this is a subnode, and that its contents should only be
included in the present display if RECURSIVE-DISPLAY-P is also
non-nil.  For proper operation when RECURSIVE-DISPLAY-P is zero, the
non-nil value of RECURSIVE-CALL-P should be the node name of the
top-level call to `Info-merge-subnodes'."
  (interactive "P")
  (when (interactive-p)
    (unless (y-or-n-p "Do you really want to integrate this node with its \
subnodes (outside Info)? ")
      (error (substitute-command-keys
              "OK.  If you are not sure what this command is about, type \
`\\[describe-function] Info-merge-subnodes'.")))) ; Defined in `help.el'.
  (garbage-collect)
  (setq recursive-display-p  (and recursive-display-p (prefix-numeric-value recursive-display-p)))
  (let* ((buf                        (current-buffer)) ; Info buffer
         (single-buf-p               (and recursive-display-p (zerop recursive-display-p)))
         (node-name                  (or (and single-buf-p recursive-call-p)
                                         Info-current-node))
         (rep-buf                    (get-buffer-create (concat "*Info: " ; Merge buffer.
                                                                node-name "*")))
         (more                       t)
         (inhibit-field-text-motion  t) ; Just to be sure, for `end-of-line'.
         token oldpt strg menu-item-line ind)

    (when (interactive-p)
      (message "Processing node `%s' and %ssubnodes..." node-name
               (if recursive-display-p "all of its " "its immediate ")))
    (save-window-excursion
      (goto-char (point-min))
      (forward-line 1)
      (setq strg  (buffer-substring (point) (point-max))) ; Node contents.
      (goto-char (point-min))
      (setq more  (search-forward "* menu" nil t))
      (forward-line 1)

      ;; Merge buffer: Insert buffer header and main node's contents, if not recursive or
      ;;                                                              do want redundancy.
      ;;               Then insert each subnode (unless this is an Index).
      (switch-to-buffer-other-window rep-buf)
      (unless (and recursive-call-p single-buf-p)
        (erase-buffer)
        (funcall Info-display-node-header-fn) ; Insert header.
        (insert (concat "\n\n" (and (or (not recursive-call-p) ; Top-level call.
                                        (and recursive-display-p ; Redundancy desired.
                                             (> recursive-display-p 0)))
                                    strg)))) ; Insert main node's contents.

      (unless  (string-match "\\s-*Index$" node-name) ; Don't recurse down Index menus.
        
        ;; Insert menu items and possibly their subnodes.
        (save-excursion
          (while more
          
            ;; Info buffer: Get menu item token.
            (set-buffer buf)
            (end-of-line)
            (setq oldpt  (point)
                  more   (search-forward "\n* " nil t)) ; Possible next menu item.
            (unless more (goto-char (point-max)))
            (while (and (not (eobp))    ; Search for a real menu item.
                        (not (setq token  (Info-get-token ; File menu item.
                                           (point) "\\* " "\\* \\([^:]*\\)::")))
                        (not (setq token  (Info-get-token ; Nonfile menu item.
                                           (point) "\\* "
                                           "\\* [^:]*:[ \t]+\\([^\t,.\n]+\\)[\t,.\n]"))))
              (setq more  (search-forward "\n* " nil t)))
            (unless token (setq more  nil)) ; No menu item. Done.

            ;; Treat subnode (menu item).
            (when more

              ;; Merge buffer: Insert separator line.
              (set-buffer rep-buf)
              (goto-char (point-max))
              (insert Info-subtree-separator) ; Ready for next menu item.

              ;; Info buffer: Go to subnode.
              (set-buffer buf)
              (Info-goto-node token)
              (goto-char (point-min))
              (forward-line 1)
              (setq strg  (buffer-substring (point) (point-max))) ; Pick up subnode contents.

              ;; Go back to parent node and get menu-item line.
              (if (>= emacs-major-version 22) (Info-history-back) (Info-last))
              (let ((inhibit-read-only  t)) ; Get untabified menu-item line, so can count 
                (buffer-enable-undo) (undo-start) ; chars to underline.
                (untabify (point) (save-excursion (forward-line 1) (point)))
                (setq menu-item-line  (buffer-substring-no-properties
                                       (save-excursion (beginning-of-line) (forward-char 2) (point))
                                       (save-excursion (forward-line 1) (point))))
                (when pending-undo-list (undo-more 1)) ; Only if did something.
                (buffer-disable-undo))

              ;; Merge buffer: Insert menu-item line, underline it, and insert subnode contents.
              (set-buffer rep-buf)
              (insert menu-item-line)
              (setq ind  (1+ (length menu-item-line)))
              (while (> ind 0) (insert "=") (setq ind  (1- ind))) ; Underline menu item.
              (insert "\n")
              (put-text-property (save-excursion (forward-line -2) (point))
                                 (save-excursion (forward-line 1) (point))
                                 (if (> emacs-major-version 21) 'font-lock-face 'face)
                                 'info-file)
              (setq oldpt  (point))
              (insert strg)             ; Insert subnode contents.
              (indent-rigidly oldpt (point) 2)

              ;; Recursive call: Insert subnode's subnodes, if there are any.
              ;; Again, though, don't recurse down Index menus.
              (when (and recursive-display-p (not (string-match "\\s-*Index$" token)))
                (save-excursion
                
                  ;; Info buffer: Go back to subnode.
                  ;; If it has a menu, then treat its subnodes, recursively.
                  (set-buffer buf)
                  (Info-goto-node token)
                  (when (search-forward "* menu" nil t)
                    (forward-line 1) (end-of-line)
                    (when (and (search-forward "\n* " nil t)
                               (or (Info-get-token ; file menu item
                                    (point) "\\* " "\\* \\([^:]*\\)::")
                                   (Info-get-token ; nonfile menu item
                                    (point) "\\* "
                                    "\\* [^:]*:[ \t]+\\([^\t,.\n]+\\)[\t,.\n]")))
                      (Info-merge-subnodes recursive-display-p node-name)))
                
                  ;; Info buffer: Go back to parent node.
                  (set-buffer buf)
                  (if (>= emacs-major-version 22)
                      (Info-history-back)
                    (Info-last))))
            
              ;; Info buffer
              (set-buffer buf))))))

    ;; Merge buffer
    (switch-to-buffer-other-window rep-buf)
    (when (and (one-window-p t) (not (window-minibuffer-p))
               (fboundp 'fit-frame)     ; Defined in `fit-frame.el'.
               Info-fit-frame-flag)
      (fit-frame))
    (goto-char (point-min))
    (set-buffer-modified-p nil)
    (use-local-map Info-merged-map)
    (when (interactive-p)
      (message "Processing node `%s' and %ssubnodes... done" node-name
               (if recursive-display-p "all of its " "its immediate ")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; info+.el ends here
