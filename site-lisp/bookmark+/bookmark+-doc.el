;;; bookmark+-doc.el - Documentation for package Bookmark+.
;;
;; Filename: bookmark+-doc.el
;; Description: Documentation for package Bookmark+
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2000-2011, Drew Adams, all rights reserved.
;; Created: Fri Sep 15 07:58:41 2000
;; Last-Updated: Mon Aug  1 09:00:07 2011 (-0700)
;;           By: dradams
;;     Update #: 13833
;; URL: http://www.emacswiki.org/cgi-bin/wiki/bookmark+-doc.el
;; Keywords: bookmarks, bookmark+, placeholders, annotations, search,
;;           info, url, w3m, gnus
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
;;    Documentation for the Bookmark+ package, which provides
;;    extensions to standard library `bookmark.el'.
;;
;;    The Bookmark+ libraries are these:
;;
;;    `bookmark+.el'     - main (driver) library
;;    `bookmark+-mac.el' - Lisp macros
;;    `bookmark+-lit.el' - (optional) code for highlighting bookmarks
;;    `bookmark+-bmu.el' - code for the `*Bookmark List*' (bmenu)
;;    `bookmark+-1.el'   - other required code (non-bmenu)
;;    `bookmark+-key.el' - key and menu bindings
;;
;;    `bookmark+-doc.el' - documentation (comment-only - this file)
;;    `bookmark+-chg.el' - change log (comment-only file)
;;
;;    The documentation includes how to byte-compile and install
;;    Bookmark+.  It is also available in these ways:
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
;;    (The commentary links in #1 and #3 work only if put you this
;;    library, `bookmark+-doc.el', in your `load-path'.)
;;
;;    More description below.
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
;;  (@> "Documentation")
;;    (@> "Installing Bookmark+")
;;    (@> "Bookmark+ Features")
;;    (@> "Different Types of Jump Commands")
;;    (@> "Bookmark Tags")
;;    (@> "Bookmark Tags Can Have Values")
;;    (@> "Function, Sequence, and Variable-List Bookmarks")
;;    (@> "Editing Bookmarks")
;;    (@> "Bookmark-List Views - Saving and Restoring State")
;;      (@> "Quitting Saves the Bookmark-List State")
;;      (@> "State-Restoring Commands and Bookmarks")
;;    (@> "Bookmarking without Visiting the Target")
;;      (@> "Bookmarking a File or a URL")
;;      (@> "Autofile Bookmarks")
;;      (@> "Bookmarking the Marked Files in Dired")
;;      (@> "Bookmarking Compilation, Grep, and Occur Hits")
;;      (@> "Bookmarking Files That You Cannot Visit")
;;      (@> "Opening Bookmarks Using Windows File Associations")
;;    (@> "Using Multiple Bookmark Files")
;;      (@> "Bookmark-File Bookmarks")
;;    (@> "The Bookmark List (Display)")
;;      (@> "Tag Commands and Keys")
;;      (@> "Tags: Sets of Bookmarks")
;;      (@> "Open Dired for the Marked File Bookmarks")
;;      (@> "Marking and Unmarking Bookmarks")
;;      (@> "Filtering Bookmarks (Hiding and Showing)")
;;      (@> "Only Visible Bookmarks Are Affected")
;;      (@> "Omitting Bookmarks from Display")
;;      (@> "Sorting Bookmarks")
;;    (@> "Bookmarks for Specific Files or Buffers")
;;    (@> "Cycling, Navigation List, Autonaming")
;;      (@> "The Bookmark Navigation List")
;;      (@> "Cycling the Navigation List")
;;      (@> "Cycling Dynamic Sets of Bookmarks")
;;      (@> "Cycling in the Current Buffer")
;;      (@> "Autonamed Bookmarks - Easy Come Easy Go")
;;    (@> "Highlighting Bookmark Locations")
;;      (@> "Defining How to Highlight")
;;      (@> "Highlighting On Demand")
;;      (@> "Highlighting Automatically")
;;      (@> "Using Highlighted Bookmarks")
;;    (@> "Use Bookmark+ with Icicles")
;;    (@> "If you use Emacs 20 and Also a More Recent Version")
;;    (@> "Bookmark Compatibility with Vanilla Emacs (`bookmark.el')")
;;    (@> "New Bookmark Structure")
 
;;(@* "Documentation")
;;
;;  Documentation
;;  -------------
;;
;;(@* "Installing Bookmark+")
;;  ** Installing Bookmark+ **
;;
;;  The main Bookmark+ library is `bookmark+.el'.  The other required
;;  libraries are `bookmark+-mac.el', `bookmark+-bmu.el',
;;  `bookmark+-1.el', and `bookmark+-key.el'.  If you want to be able
;;  to highlight bookmarks then you will also need library
;;  `bookmark+-lit.el'.  I recommend that you byte-compile all of the
;;  libraries, after loading the source files (in particular, load
;;  `bookmark+-mac.el').
;;
;;  Put the directory of these libraries in your `load-path' and add
;;  this to your init file (~/.emacs):
;;
;;  (require 'bookmark+)
;;
;;  That will load all of the Bookmark+ libraries.  If you do not care
;;  about bookmark highlighting then simply do not put
;;  `bookmark+-lit.el' in your `load-path'.
;;
;;  By default (see option `bmkp-crosshairs-flag'), when you visit a
;;  bookmark that has no region it is highlighted temporarily using
;;  crosshairs, for easy recognition.  (This temporary highlighting is
;;  independent of the highlighting provided by `bookmark+-lit.el'.)
;;
;;  For this optional crosshairs feature you also need library
;;  `crosshairs.el', which in turn requires libraries `col-highlight',
;;  `hl-line', `hl-line+', and `vline'.  Library `hl-line' comes with
;;  vanilla Emacs.  The others are available from the Emacs Wiki web
;;  site: http://www.emacswiki.org/.  You also need Emacs 22 or later
;;  for this feature.
 
;;(@* "Bookmark+ Features")
;;  ** Bookmark+ Features **
;;
;;  Here is an overview of some of the features that Bookmark+
;;  provides.  Some of these are detailed in other sections, below.
;;
;;  * Richer bookmarks.  They record more.  They are more accurate.
;;
;;     - You can tag bookmarks, a la del.icio.us.  In effect, tags
;;       define bookmark sets.  A bookmark can have any number of
;;       tags, and multiple bookmarks can have the same tag.  You can
;;       sort, show/hide, or mark bookmarks based on their tags.
;;
;;     - Bookmark+ tags can be more than just names.  They can be
;;       full-fledged user-defined attributes, with Emacs-Lisp objects
;;       as their values.
;;
;;     - You can have multiple bookmarks with the same name.  This is
;;       particularly useful for autofile bookmarks, which are
;;       bookmarks that have the same name as their target files.
;;       They give you the effect of using files themselves as
;;       bookmarks.  In particular, they let you, in effect, tag
;;       files.  See (@> "Autofile Bookmarks") and
;;       (@> "Tagging Files").
;;
;;       (In vanilla Emacs you can also, in theory, have multiple
;;       bookmarks with the same name.  But you cannot really use them
;;       in any practical way.  Vanilla Emacs cannot distinguish among
;;       them: the most recent one shadows all others with the same
;;       name.)
;;
;;     - Bookmarks record the number of times you have visited them
;;       and the time of the last visit.  You can sort, show/hide, or
;;       mark bookmarks based on this info.
;;
;;     - You can combine bookmarks, to make composite, or sequence,
;;       bookmarks.  Invoking a sequence bookmark invokes each of its
;;       component bookmarks in turn.  A component bookmark can itself
;;       be a sequence bookmark.
;;
;;     - You can bookmark a region of text, not just a position.  When
;;       you jump to a bookmark that records a region, the region is
;;       activated (see option `bmkp-use-region').  (Region activation
;;       is not supported for Gnus bookmarks.)
;;
;;     - Bookmarks are relocated better than for vanilla Emacs when
;;       the contextual text changes.
;;
;;  * Additional types of bookmarks.
;;
;;     - Autofile bookmarks.  You can bookmark a file without visiting
;;       it or naming the bookmark.  The bookmark name is the same as
;;       the file name (non-directory part).  You can have multiple
;;       such bookmarks with the same name, to bookmark files with the
;;       same name but in different directories.
;;
;;     - Dired bookmarks.  You can bookmark a Dired buffer, recording
;;       and restoring its `ls' switches, which files are marked,
;;       which subdirectories are inserted, and which (sub)directories
;;       are hidden.
;;
;;     - Bookmark-list bookmarks.  You can bookmark the current state
;;       of buffer `*Bookmark List*' - a list of bookmarks.  Jumping
;;       to such a bookmark restores the recorded sort order, filter,
;;       title, and omit list.  See (@> "Omitting Bookmarks from Display").
;;
;;     - Bookmark-file bookmarks.  You can bookmark a bookmark file.
;;       Jumping to such a bookmark loads the bookmarks in the file.
;;       See (@> "Bookmark-File Bookmarks").
;;
;;     - Desktop bookmarks.  You can bookmark the current Emacs
;;       desktop, as defined by library `desktop.el' - use command
;;       `bmkp-set-desktop-bookmark' (`C-x p K').  You can "jump" to
;;       (that is, restore) a saved desktop.  A desktop includes:
;;
;;         - Some global variables.  To exclude variables normally
;;           saved, see option `bmkp-desktop-no-save-vars'.
;; 	   - The current set of buffers and their associated files.
;;           For each: its mode, point, mark, & some local variables.
;;
;;     - Gnus bookmarks.  You can bookmark a Gnus article, a URL, a
;;       PDF file (DocView), a UNIX manual page (from the output of
;;       Emacs command `man' or `woman'), an image, or a piece of
;;       music.
;;
;;     - Non-file (buffer) bookmarks.  You can bookmark a buffer that
;;       is not associated with a file.
;;
;;     - Function bookmarks.  A bookmark can represent a Lisp
;;       function, which is invoked when you "jump" to the bookmark.
;;
;;     - Sequence (composite) bookmarks.  A bookmark can represent a
;;       sequence of other bookmarks.
;;
;;     - Lisp variable bookmarks.  A bookmark can represent a set of
;;       variables and their values.
;;
;;     In particular, note that you can use the following kinds of
;;     bookmarks to quickly switch among different projects (sets of
;;     bookmarks): Dired, bookmark-list, bookmark-file, and desktop
;;     bookmarks.
;;
;;  * Additional ways to bookmark.
;;
;;     - You can bookmark the file or URL named at point (or any other
;;       file or URL), without first visiting it.
;;
;;     - You can bookmark the targets of the hits in a compilation
;;       buffer or an `occur' buffer, without first visiting them.
;;
;;     - You can bookmark all of the marked files in Dired at once.
;;
;;  * Extensive menus.
;;
;;     - In the `*Bookmark List*' display, a `mouse-3' popup menu has
;;       actions for the individual bookmark that you point to when
;;       you click the mouse.
;;
;;     - In the `*Bookmark List*' display, a complete menu-bar menu,
;;       `Bookmark+', is available.  The same menu is available on
;;       `C-mouse-3'.  It has submenus `Jump To', `Mark', `Omit',
;;       `Show', `Sort', `Tags', `Highlight' (needs library
;;       `bookmark+-lit.el), and `Define Command'.
;;
;;     - The vanilla `Bookmarks' menu, which is typically a submenu of
;;       the menu-bar `Edit' menu, is modified by adding several items
;;       from the `Bookmark+' menu, including submenus `Jump To',
;;       `Tags', and `Highlight'.
;;
;;  * Improvements for the bookmark list.
;;
;;    This is buffer `*Bookmark List*', aka the bookmark "menu list"
;;    (a misnomer), which you display using `C-x r l'.  See
;;    (@> "The Bookmark List (Display)").
;;
;;     - The last display state is saved (by default), and is restored
;;       the next time you show the list.  (Tip: Use the bookmark list
;;       as your "Home" page at Emacs startup.)
;;
;;     - You can save the current bookmark-list state at any time and
;;       return to it later.  There are a few ways to do this,
;;       including bookmarking the list itself.
;;       See (@> "Bookmark-List Views - Saving and Restoring State").
;;
;;     - Marking/unmarking is enhanced.  It is similar to Dired's.
;;
;;     - You can easily mark or show different classes of bookmarks.
;;
;;     - Faces distinguish bookmarks by type.
;;
;;     - You can sort bookmarks in many ways.  You can easily define
;;       your own sort orders, even complex ones.
;;
;;     - You can regexp-search (`M-a') or query-replace (`M-q') the
;;       targets (destination file or buffers) of the marked
;;       bookmarks, in the current bookmark-list sort order.  For
;;       Emacs 23 and later, you can even search incrementally (`M-s a
;;       C-s', or `M-s a C-M-s' for regexp).
;;
;;     - You can use `M-d >' to open Dired for just the local file
;;       bookmarks that are marked (`>').
;;
;;     - If you use Emacs on Microsoft Windows, you can open bookmarks
;;       according to Windows file associations.  (You will also need
;;       library `w32-browser.el'.)
;;
;;     - You can use (lax) completion when you set a bookmark using
;;       `bookmark-set' (`C-x r m'), choosing from existing bookmarks
;;       for the same buffer.  This makes it easy to update a nearby
;;       bookmark (e.g. relocate it).  With a numeric prefix argument
;;       (or if there are no bookmarks for the buffer), you can choose
;;       from all bookmarks.
;;
;;     - You can edit a bookmark: its name and file name/location, its
;;       tags, or its complete defining internal Lisp record.
;;
;;  * Multiple bookmark files.
;;
;;     - Although vanilla Emacs lets you load different bookmark
;;       files, this feature is not well supported, if not
;;       contradictory.  With Bookmark+ you can easily (a) switch
;;       among alternative bookmark files or (b) load multiple files
;;       into the same session, accumulating their bookmark
;;       definitions.  The last file you used is the default, so it is
;;       easy to go back and forth between two bookmark files.
;;       See (@> "Using Multiple Bookmark Files").
;;
;;  * Type-specific jump commands.
;;
;;     - When you want to jump to a bookmark of a specific type
;;       (e.g. Dired), you can use a command that offers only such
;;       bookmarks as completion candidates.
;;
;;  * Dedicated keymaps as prefix keys.
;;
;;     - Prefix `C-x p' is used for bookmark keys, in general.  The
;;       vanilla keys on prefix `C-x r' are still available also, but
;;       that prefix is shared with register commands, making it less
;;       convenient for bookmarks.  Using `C-x p' lets you focus on
;;       bookmarks.
;;
;;     - Prefix `C-x p c' is for setting various kinds of bookmarks.
;;
;;     - Prefixes `C-x j' and `C-x 4 j' (for other-window) are used
;;       for bookmark jump commands.  Again, a dedicated prefix key
;;       helps you focus on one kind of action (jumping).
;;
;;     All of these prefix keys correspond to prefix-map variables, so
;;     you need not use these particular prefixes.  You can bind these
;;     maps to any prefix keys you want.  These are the maps, together
;;     with their predefined bindings.  (Note that the keymap for
;;     setting bookmarks is bound to a prefix in `bookmark-map'.)
;;
;;       `bookmark-map'               - `C-x p' 
;;       `bmkp-set-map'               - `C-x p c'
;;       `bmkp-jump-map'              - `C-x j'
;;       `bmkp-jump-other-window-map' - `C-x 4 j'
;;
;;     In addition, mode-specific bookmarking commands are bound in
;;     some other modes: Occur, Compilation (including Grep),
;;     Buffer-menu, Gnus, Info, Man, Woman, W3M, and Dired (if you use
;;     Dired+).  These keys let you set or jump to bookmarks specific
;;     to the modes.
;;
;;  * Helpful help.
;;
;;     - Information about individual bookmarks.
;;
;;       . Anywhere in Emacs, `C-x p ?'  (command
;;         `bmkp-describe-bookmark') describes any bookmark.  With a
;;         prefix argument, it shows you the full information that
;;         defines it (internal form).
;;
;;       . In the bookmark list, `C-h RET' (or `C-h C-RET') describes
;;         the bookmark under the cursor.  The description is as
;;         complete as possible - for example, for an image-file
;;         bookmark the complete EXIF image metadata is shown.  (This
;;         is only for Emacs 22 and later, and only if you have
;;         command-line tool `exiftool' installed.  See standard Emacs
;;         library `image-dired.el' for more information about
;;         `exiftool'.)
;;
;;         And again, a prefix arg (`C-u C-h RET') means show the full
;;         (internal) bookmark information.
;;
;;     - General Bookmark+ documentation.
;;
;;       . Anywhere in Emacs, `M-x bmkp-bmenu-mode-status-help' shows
;;         detailed information about the current state of the
;;         bookmark list.  Click button `Doc in Commentary' or button
;;         `Doc on the Web' to access the complete documentation.
;;
;;         (Use button `Customize' to customize all '''Bookmark+'''
;;         faces and options.)
;;
;;       . In the bookmark list, `?' and `C-h m' are the same as `M-x
;;         bmkp-bmenu-mode-status-help'.  (`C-h m' in the bookmark
;;         list does not show you info about minor modes.  If you want
;;         that, use `M-x describe-mode'.)
;;
;;       . In the `bookmark-plus' group customization buffer (`M-x
;;         customize-group bookmark-plus'), click button `Commentary'.
;;
;;       . From the Emacs-Wiki Web site,
;;         http://www.emacswiki.org/cgi-bin/wiki/BookmarkPlus.
;;
;;  * Jump-destination highlighting.
;;
;;     - When you jump to a bookmark, the destination (position) is
;;       highlighted temporarily using crosshairs, to make it stand
;;       out.  Option `bmkp-crosshairs-flag' controls this, and this
;;       feature is available only if you also use library
;;       `crosshairs.el'.
;;
;;  * Visual bookmarks (highlighting).
;;
;;     - You can highlight the locations of bookmarks, either
;;       automatically or on demand.  You control what kind of
;;       highlighting, if any, is used for which bookmarks.  This
;;       feature requires that you have library `bookmark+-lit.el' in
;;       your `load-path' (it will then be loaded by `bookmark+.el).
;;    
;;  * Synergy with Icicles.
;;
;;     - Icicles works with Bookmark+ to provide enhanced bookmark
;;       jumping (visiting), setting, and help.  It gives you a
;;       bookmark browser.  See (@> "Use Bookmark+ with Icicles") and
;;       http://www.emacswiki.org/cgi-bin/wiki/Icicles.
 
;;(@* "Different Types of Jump Commands")
;;  ** Different Types of Jump Commands **
;;
;;  When you jump to a bookmark, you can use completion to specify the
;;  bookmark name.  `bookmark-jump' and `bookmark-jump-other-window',
;;  bound to `C-x j j' and `C-x 4 j j', are general commands.  Their
;;  completion candidates include all of your bookmarks.  With
;;  Bookmark+ you can easily have a large number of bookmarks.
;;
;;  To provide more specificity, Bookmark+ provides many different
;;  bookmark jump commands.  If you want to jump to a bookmark of a
;;  specific type, such as Info, you can use a Bookmark+ command that
;;  is specific to bookmarks of that type: only those bookmarks are
;;  completion candidates.
;;
;;  There are thus type-specific commands: `bmkp-dired-jump',
;;  `bmkp-info-jump', and so on, bound to `C-x j d', `C-x j i', and so
;;  on.  There are also commands to jump to bookmarks for the current
;;  buffer or for particular buffers or files
;;  (see (@> "Bookmarks for Specific Files or Buffers")).
;;
;;  All bookmark jump commands are bound to keys that have the prefix
;;  `C-x j'.  There is an other-window version of most jump commands,
;;  and it is bound to the same key as the same-window command, except
;;  the prefix is `C-x 4 j', not `C-x j'.  For instance,
;;  `bmkp-dired-jump-other-window' is bound to `C-x 4 j d'.
;;
;;  More precisely, the bookmark jump commands are on the prefix maps
;;  `bmkp-jump-map' and `bmkp-jump-other-window-map', which have the
;;  default bindings `C-x j' and `C-x 4 j'.  You can bind these maps
;;  to any keys you like.
;;
;;  If you do not remember the different type-specfic bindings, you
;;  can use commands `bmkp-jump-to-type' and
;;  `bmkp-jump-to-type-other-window' (`C-x j :' and `C-x 4 j :').
;;  They work for any type, prompting you first for the type, then for
;;  a bookmark of that type (only).
;;
;;  There are several commands for jumping to a bookmark with tags.
;;  The completion candidates can be those bookmarks that have all
;;  tags in a given set, some tags in a given set, all tags matching a
;;  regexp, or some tags matching a regexp.  You are prompted for the
;;  set of tags or the regexp to match.
;;
;;  These commands all have the prefix key `C-x j t'.  The suffix key
;;  is `*' for "all" and `+' for "some".  The regexp-matching commands
;;  precede the suffix key with `%'.  For example, `C-x j t % +' jumps
;;  to a bookmark you choose that has one or more tags that match the
;;  regexp you input.
;;
;;  There are some type-specific jump commands for bookmarks with
;;  tags.  The key sequences for these include a key that indicates
;;  the bookmark type, after the `t' indicating tags.  For example,
;;  commands for jumping to a file or directory bookmark having
;;  certain tags use the prefix `C-x j t f' (`f' for file).  Similar
;;  commands for autofile bookmarks have prefix `C-x j t a' (`a' for
;;  autofile).
;;
;;  For example, `C-x j t f % *' jumps to a file or directory bookmark
;;  you choose, where all of its tags match a regexp, and `C-x j t a
;;  +' finds a file tagged with at least one of the tags you input.
;;  The autofile "jump" commands are really `find-file' commands: they
;;  read a file name using `read-file-name' - see (@> "Autofile Bookmarks").
;;
;;  Bookmark names are global.  File names are not; that is, the
;;  non-directory portion is not.  Suppose you have two similar
;;  directories with some like-named files, perhaps tagged in similar
;;  ways.  Imagine image files of your vacations organized in
;;  different directories by year.  It is sometimes useful to narrow
;;  your focus to the file bookmarks in one directory.
;;
;;  Commands such as `bmkp-file-this-dir-jump' (`C-x j C-f') offer as
;;  completion candidates only bookmarks for files and subdirs in the
;;  current directory (`default-directory').  For tags, there are
;;  equivalent commands.  For example, `C-x j t C-f % *' is the same
;;  as `C-x j t f % *', but the destinations are limited to files in
;;  the current directory.  All of the "this-dir" file jump commands
;;  are bound to the same keys as the general file jump commands, but
;;  with `C-f' instead of `f'.
;;
;;  Remember that Bookmark+ collects lots of commands on only a few
;;  predefined prefix keys, primarily as a mnemonic device.  Nothing
;;  requires you to use the long key sequence `C-x j t f % *' to visit
;;  a file that has a given set of tags.  It is expected that you will
;;  bind short key sequences to commands that you use often.
;;
;;  The `C-x j' and `C-x 4 j' bindings are global.  In addition, in
;;  some modes `j' is bound to the corresponding type-specific jump
;;  command.  For example, in Info mode, `j' is bound to
;;  `bmkp-info-jump'.  (Dired is an exception here: `J' is used
;;  instead of `j', since `j' is already taken for `dired-goto-file'.)
;;  These commands are also added to the mode's menu-bar menu.
;;
;;  In Dired mode, `C-j' is bound to a special Dired-specific jump
;;  command, `bmkp-dired-this-dir-jump', whose destinations all use
;;  the current directory (`default-directory').  The aim of `C-j' is
;;  not to change directories but to change to a different set of
;;  Dired markings, switches, inserted subdirectories, or hidden
;;  subdirectories for the same Dired directory.
;;
;;  In addition to the predefined bookmark types, which you can use as
;;  described above, you can define a "type"-specific jump command for
;;  any set of bookmarks.  That is, you can use any specific set of
;;  bookmarks as the completion candidates for a new jump command.
;;  Such a set is really only a pseudo-type: the actual bookmarks can
;;  each be of any type.
;;
;;  You could use this feature, for example, to define a jump command
;;  for the bookmarks that belong to a given project.
;;
;;  One way to define such a command is to first mark the bookmarks
;;  that you want to be the completion candidates, then use `M-c'
;;  (command `bmkp-bmenu-define-jump-marked-command') in the bookmark
;;  list.
;;
;;  The `*Bookmark List*' display defines a set of bookmarks, even
;;  without markings.  So does each bookmark of type bookmark list,
;;  that is, a bookmark corresponding to a particular `*Bookmark
;;  List*' display state - see
;;  (@> "State-Restoring Commands and Bookmarks").
;;
;;  You can capture the set of bookmarks corresponding to a `*Bookmark
;;  List*' display for use in navigation, that is, as the current
;;  "navigation list".  Navigation here includes jumping and cycling
;;  - see (@> "Cycling, Navigation List, Autonaming").
;;
;;  To capture in the navigation list the bookmarks corresponding to
;;  either the current `*Bookmark List*' display or a bookmark-list
;;  bookmark, use `C-x p B', which is bound to command
;;  `bmkp-choose-navlist-from-bookmark-list'.  To then jump to a
;;  bookmark from such a navigation list, use `C-x j N' or `C-x 4 j N'
;;  (`bmkp-jump-in-navlist' or `bmkp-jump-in-navlist-other-window').
 
;;(@* "Bookmark Tags")
;;  ** Bookmark Tags **
;;
;;  With Bookmark+ you can bookmark many kinds of Emacs object.
;;  Bookmarks record locations - that is their primary purpose.  They
;;  can also record annotations: general free-text descriptions of
;;  your choosing.
;;
;;  Bookmark+ bookmarks can also be tagged, as a way to organize them,
;;  which also means as a way to organize the objects that are
;;  bookmarked.
;;
;;  By "tagging" and "tag" in this context is meant associating
;;  keywords or other text with an object, typically in order to
;;  classify or characterize it.  Tags are metadata about an object.
;;  This notion of tagging is sometimes called "delicious" tagging
;;  after the Web site www.delicious.com that popularized it
;;  (`http://en.wikipedia.org/wiki/Delicious_(website)').
;;
;;  Be aware that there is another notion of "tag" associated with
;;  Emacs: that involving Emacs tags files, which record the locations
;;  of function, variable, etc. definitions in source files.  There is
;;  no relation between the two notions of "tag".
;;
;;  A bookmark tag is a string (or a cons whose car is a string - see
;;  (@> "Bookmark Tags Can Have Values")).  You can add as many tags
;;  as you like to any bookmark, and multiple bookmarks can have the
;;  same tag(s).  In fact, that's the whole idea behind using them for
;;  organizing.
;;
;;  This feature is unrelated to the fact that bookmarks record
;;  locations and are useful for navigating.  You can, if you want,
;;  use bookmarks to tag files in various ways purely for purposes of
;;  organizing them (e.g. into projects), whether or not you ever use
;;  the bookmarks as a way to visit them.
;;
;;  For example, if you use Dired+ (library `dired+.el'), then you can
;;  use `M-b' (`diredp-do-bookmark') in Dired to create an autofile
;;  bookmark for each of the marked files in the Dired buffer.  Even
;;  if you never use those bookmarks for navigating to the files, you
;;  can use them with tags to organize the files and thus operate on
;;  subsets of them.
;;
;;  By default, you create bookmarks without tags and add tags to them
;;  later.  If you prefer, you can customize option
;;  `bmkp-prompt-for-tags-flag' to non-nil so that you are prompted to
;;  add tags immediately whenever you set (create) a bookmark.  There
;;  are also some commands, such as `bmkp-tag-a-file' (`C-x p t + a')
;;  and `bmkp-untag-a-file' (`C-x p t - a'), that always prompt for
;;  tags to add or remove.  (In general, the key `a' is used in key
;;  sequences for autofile bookmarks.)
;;
;;  When you are prompted to enter a tag, you type some text then hit
;;  `RET'.  If you want to include a newline character in the tag
;;  itself, use `C-q C-j' (`C-j' is the newline character).  You can
;;  use `C-q' this way to enter any character.  If you do use complex
;;  strings as tags then you might prefer to simply edit a bookmark's
;;  tags in a separate buffer.  You can do that using `C-x p t e' (or
;;  `T e' in the bookmark-list display).
;;
;;  To make tags more useful, Bookmark+ provides *lots* of commands:
;;  commands for adding, removing, copying, pasting, and renaming
;;  tags; commands for jumping to bookmarks with particular sets of
;;  tags; and commands for marking or unmarking (in buffer `*Bookmark
;;  List*') bookmarks that are tagged in various ways.
;;
;;  Most commands pertaining to tags are by default on prefix key `C-x
;;  p t' - use `C-x p t C-h' to see them.  In buffer `*Bookmark
;;  List*', commands pertaining to tags are on prefix key `T' - use `T
;;  C-h' to see them.
;;
;;  When combined with other Bookmark+ commands (e.g. search,
;;  query-replace) that apply to the marked bookmarks in the
;;  `*Bookmark List*' window, you can really do quite a lot using
;;  bookmark tags.  Use your imagination!
;;
;;  See Also:
;;
;;  * (@> "Bookmarking the Marked Files in Dired")
;;  * (@> "Opening Bookmarks Using Windows File Associations")
;;  * (@> "Tag Commands and Keys")
 
;;(@* "Bookmark Tags Can Have Values")
;;  ** Bookmark Tags Can Have Values **
;;
;;  Bookmark tags are simply names (strings) when you create them.
;;  Nearly all of the predefined operations that use tags use these
;;  names: sorting, marking, jumping, and so on.  But you can in fact
;;  add an associated value to any tag.  This means that a tag can act
;;  just like an object attribute or property: it can be a name/value
;;  pair.
;;
;;  To add a value to a tag that has none, or to change the current
;;  value of a tag, you use command `bmkp-set-tag-value', which is
;;  bound to `T v' in the bookmark list and bound to `C-x p t v'
;;  globally.  You are prompted for the bookmark, the tag, and the new
;;  value.
;;
;;  A tag value can be a number, symbol, string, list, vector, and so
;;  on.  It can be as complex as you like.  It can be any Emacs-Lisp
;;  object that has read syntax, that is, that is readable by the Lisp
;;  reader.  (Everything that is saved as part of a bookmark must be
;;  readable; otherwise, your bookmark file could not be read
;;  (loaded).)
;;
;;  Because tag values can be pretty much anything, you are pretty
;;  much on your own when it comes to making use of them.  Bookmark+
;;  does not provide predefined functions for using tag values.  In
;;  general, tag values are something you will use with home-grown
;;  Lisp code for your own purposes.
;;
;;  However, you can easily make some interactive use of tag values
;;  with little effort.  You can, for example, define a predicate that
;;  tests whether a bookmark has a tag value that satisfies some
;;  property (e.g. is a number greater than 3.14159265358979), and
;;  then you can use command `bmkp-bmenu-mark-bookmarks-satisfying' to
;;  mark those bookmarks.
;;
;;  Tags that have the prefix "bmkp-" are reserved - do not name your
;;  own tags using this prefix.
;;
;;  Currently, "bmkp-jump" is the only predefined bookmark tag.  You
;;  can give this tag a value that is a function - it is called
;;  whenever the tagged bookmark is visited.  Any Lisp-readable
;;  function value is allowed: a symbol or a lambda expression.
;;
;;  For example, to display `Hello!' when a bookmark is visited you
;;  can use this:
;;
;;    T v bookmark-jump RET (lambda () (message "Hello!"))
;;
;;  The function that is the value of a "bmkp-jump" tag is called just
;;  after the the standard hook `bookmark-after-jump-hook' is invoked.
;;  You can use this tag to invoke functions that are specific to
;;  individual bookmarks; bookmarks can thus have their own, extra
;;  jump functions.
 
;;(@* "Function, Sequence, and Variable-List Bookmarks")
;;  ** Function, Sequence, and Variable-List Bookmarks **
;;
;;  Bookmarks are typically thought of only as recorded locations.
;;  Invoking a bookmark, called "jumping" to it, traditionally means
;;  just visiting its location.  Bookmark+ looks at bookmarks in a
;;  more general way than that.  A bookmark is a shortcut of some
;;  kind - nothing more.
;;
;;  A given type of bookmark is defined by its handler function, which
;;  really could do anything you like.  We've already seen the
;;  examples of region bookmarks, which restore the active region, and
;;  Dired bookmarks, which restore a set of Dired markings, switches,
;;  inserted subdirectories, and hidden (sub)directories.
;;
;;  A "function bookmark" simply invokes some function - any function.
;;  You can, for instance, define a window or frame configuration and
;;  record that as a bookmark.  Then jump to the bookmark to switch
;;  contexts.  (You can also bookmark a desktop and jump to that.)
;;
;;  Function bookmarks might not seem too interesting, since we have
;;  other ways of invoking functions in Emacs.  But the other features
;;  of Bookmark+ combine with this feature.  You can, for instance,
;;  tag such bookmarks.
;;
;;  And you can combine them, invoking the functions sequentially.
;;  This is just a particular case of using a "sequence bookmark",
;;  which simply records a sequence of bookmarks.  The bookmarks in a
;;  sequence can be of any kind, including other sequence bookmarks.
;;
;;  Command `bmkp-make-function-bookmark' creates a function bookmark
;;  - you give it a function symbol or a lambda expression.  Command
;;  `bmkp-bmenu-make-sequence-from-marked' creates a sequence from the
;;  marked bookmarks in the bookmark list, in their current order.
;;
;;  A variable-list bookmark saves and restores the values of a set of
;;  variables.  Command `bmkp-set-variable-list-bookmark' prompts you
;;  for the variables to include in the list and then sets the
;;  bookmark.  Command `bmkp-jump-variable-list' (`C-x j v') restores
;;  the recorded variable values for the bookmark's buffer.  You can
;;  also create variable-list bookmarks non-interactively, using
;;  function `bmkp-create-variable-list-bookmark'.
;;
;;  If you use library `wide-n.el', then you can move among multiple
;;  restrictions (narrowings) in a buffer.  The restrictions are
;;  stored in buffer-local variable `wide-n-restrictions'.  Command
;;  `bmkp-set-restrictions-bookmark' bookmarks this value for the
;;  current buffer.  Jumping to such a bookmark restores the saved
;;  ring/stack of restrictions.
 
;;(@* "Editing Bookmarks")
;;  ** Editing Bookmarks **
;;
;;  In vanilla Emacs, you can use `e' in the bookmark list display to
;;  edit the annotation associated with a bookmark.  And you can use
;;  `r' to rename a bookmark.  But that is all.  There is no easy way
;;  to really edit a bookmark.
;;
;;  With Bookmark+, in addition to `e' and `r', you can use `E' in the
;;  bookmark list, or `C-x p E' anywhere, to edit the bookmark name
;;  and the target file name (bookmarked location).  You are prompted
;;  for the new names.
;;
;;  If you use a prefix argument (`C-u E' in the bookmark list or `C-u
;;  C-x p E' elsewhere), then you can edit the complete internal
;;  bookmark record - the Lisp definition.  This is the same internal
;;  definition that you see when you use `C-u C-h RET' in the bookmark
;;  list.
;;
;;  Use `C-c C-c' when you are done editing the bookmark record, to
;;  save your changes.  The number of visits and the time last visited
;;  for the bookmark are updated automatically (unless you use a
;;  prefix argument: `C-u C-c C-c').
;;
;;  When you use `C-c C-c', Bookmark+ does a quick check to see if it
;;  recognizes the bookmark type as valid.  This is not a complete
;;  bookmark validity check, but it can help to let you know if you
;;  make an editing mistake that renders the bookmark record invalid.
;;
;;  In that case, you are asked whether you want to save the changes
;;  anyway.  Remember that you can use `undo' to reverse particular
;;  changes or simply kill the edit buffer to abandon all changes.
;;
;;  In a similar way, you can use `T e' in the bookmark list or `C-x p
;;  t e' elsewhere, to edit a bookmark's tags.
 
;;(@* "Bookmark-List Views - Saving and Restoring State")
;;  ** Bookmark-List Views - Saving and Restoring State **
;;
;;  The bookmark list (buffer `*Bookmark List*') provides a view into
;;  the set of bookmarks.  You can mark, sort, and hide (filter, omit)
;;  bookmarks - see (@> "The Bookmark List (Display)").  The state of
;;  the displayed bookmark list can thus change.
;;
;;  At different times, and in different contexts, different views can
;;  be useful.  Bookmark+ lets you save the current state of the
;;  displayed list and later restore it.  There are a couple of
;;  different ways to do this.
;;
;;
;;(@* "Quitting Saves the Bookmark-List State")
;;  *** Quitting Saves the Bookmark-List State ***
;;
;;  If option `bmkp-bmenu-state-file' is non-nil, which it is by
;;  default, then Bookmark+ remembers the last state of the bookmark
;;  list when you quit it or you quit Emacs, and it restores that
;;  state when you show the list again (which could be in the next
;;  Emacs session).  You can think of this feature as your "Home" page
;;  for bookmarks, giving you a stepping stone to the files and
;;  directories you use most.
;;
;;  If, for example, when you quit the bookmark list you are showing
;;  only bookmarks to Info nodes and UNIX manual pages, sorted in a
;;  particular way, and with some of them marked for particular
;;  processing, then the next time you open the list the same state is
;;  restored: the same set of bookmarks is shown, in the same order,
;;  with the same markings.
;;
;;  You can turn off this automatic bookmark-list display state
;;  saving, if you want, by customizing option `bmkp-bmenu-state-file'
;;  to nil.  And you can toggle this option at any time, using `M-l'
;;  in the bookmark list (command
;;  `bmkp-toggle-saving-menu-list-state').  In particular, if you want
;;  your next visit to the bookmark list to start out with a
;;  previously recorded state instead of the current state, just hit
;;  `M-l' before quitting the bookmark list.
;;
;;
;;(@* "State-Restoring Commands and Bookmarks")
;;  *** State-Restoring Commands and Bookmarks ***
;;
;;  In addition to automatically saving/restoring the final
;;  bookmark-list display state, you can save this state at any time,
;;  any number of times, for later restoration.  This gives you the
;;  ability to create multiple persistent views of your bookmarks.
;;
;;  There are two ways to do this:
;;
;;  * Create a bookmark for the `*Bookmark List*' buffer itself: a
;;    bookmark-list bookmark.
;;
;;  * Define a command that restores the bookmark-list state.
;;
;;  When you use `C-x r m' (`bookmark-set') in buffer `*Bookmark
;;  List*' to create a bookmark-list bookmark, the current sort order,
;;  filter, regexp pattern, title, and omit list are saved as part of
;;  the bookmark.  (These concepts are described below - see
;;  (@> "Bookmark List (Display)").)  Jumping to such a bookmark
;;  restores all of these.
;;
;;  Alternatively, you can define a command that does the same thing,
;;  but without creating another bookmark - use `c'
;;  (`bmkp-bmenu-define-command') in the bookmark list to do this.
;;  You are prompted for the name of the new command.  Use the command
;;  anytime (including in another Emacs session) to restore the
;;  bookmark list.
;;
;;  Define any number of such commands for the views you use.  The
;;  file for saving the definitions (see option
;;  `bmkp-bmenu-commands-file') is never overwritten, so you can also
;;  add other code to it manually, if you want.  The file is read the
;;  first time the bookmark list is displayed in a given Emacs
;;  session.
;;
;;  The state that is saved and restored using a bookmark-list
;;  bookmark or a command defined using `c' is only a partial state.
;;  The current set of markings and some other information are not
;;  saved, in order to save disk space and save/restore time.
;;
;;  Sometimes, however, you really want to save the entire
;;  bookmark-list state, creating a full snapshot.  You can use `C'
;;  (`bmkp-bmenu-define-full-snapshot-command') to do that.  This
;;  defines a command that restores the bookmark list completely.
;;  That is the same thing that happens automatically (by default)
;;  whenever you quit the bookmark list (or Emacs), but defining
;;  snapshot commands lets you have multiple saved states and switch
;;  to them at will.
;;
;;  Be aware, however, that full-snapshot command definitions can be
;;  quite large, since they each contain a copy of the current
;;  bookmark list and any accessory lists (hidden and marked bookmarks
;;  etc.).
;;
;;  Whether you use `c' or `C' to define a state-restoring command or
;;  you create a bookmark-list bookmark, you can create a sequence
;;  bookmark that combines such bookmark-list restoration with
;;  activation of other bookmarks.  (To include a state-restoring
;;  command in a sequence, you need to first create a function
;;  bookmark that uses the command, and then include that bookmark in
;;  the sequence.)
 
;;(@* "Bookmarking without Visiting the Target")
;;  ** Bookmarking without Visiting the Target **
;;
;;  There are several use cases for bookmarking a target without first
;;  visiting it:
;;
;;  1. In an Emacs buffer you come across a reference or a link to a
;;     file or a URL.  You bookmark the target without bothering to
;;     visit it first.  You do not really care which position in the
;;     file is bookmarked.
;;
;;  2. In Dired, you mark certain files and then bookmark all (each)
;;     of them, in one operation.
;;
;;  3. As a special case of #1 and #2, you bookmark a file that you
;;     cannot visit in Emacs (in the sense of editing it in a buffer)
;;     - for example, a music file.  "Jumping" to the bookmark
;;     performs an operation appropriate to the file - for example,
;;     playing music.
;;
;;  4. In a compilation buffer (e.g. `*grep*', `*compile*') or an
;;     occur or multi-occur buffer (`*Occur*'), you bookmark one or
;;     more of the hits.  Such a bookmark takes you to the appropriate
;;     position in the target file or buffer.
;;
;; 
;;(@* "Bookmarking a File or a URL")
;;  *** Bookmarking a File or a URL ***
;;
;;  You can use commands `bmkp-file-target-set' and
;;  `bmkp-url-target-set', bound by default to `C-x p c f' and `C-x p
;;  c u', to bookmark any file or URL.  Completion is available, the
;;  default file name or URL being determined by the text at point.
;;  In addition to the file or URL, you are prompted for the bookmark
;;  name.  (In general, the keys `f' and `u' are used in key sequences
;;  for file and URL bookmarks, respectively.)
;;
;;
;;(@* "Autofile Bookmarks")
;;  *** Autofile Bookmarks ***
;;
;;  Autofile bookmarking represents a special case of bookmarking a
;;  file without visiting it.  For an autofile bookmark you need not
;;  provide the bookmark name - you specify only the file to bookmark.
;;  You can create a new autofile bookmark, or set an existing one,
;;  using `bmkp-bookmark-a-file' (aka `bmkp-autofile-set'), which is
;;  bound by default to `C-x p c a'.  (In general, the key `a' is used
;;  in key sequences for autofile bookmarks.)
;;
;;  If user option `bmkp-propertize-bookmark-names-flag' is non-nil,
;;  which it is by default with Emacs 21 and later, then you can have
;;  multiple bookmarks with the same name.  This is important for
;;  autofile bookmarks because the bookmark name is only the
;;  non-directory part of the file name.  This Bookmark+ feature lets
;;  you have different autofile bookmarks for files of the same name
;;  in different directories.
;;
;;  Because an autofile bookmark name is the same as its
;;  (non-directory) file name, you can define and use file-visiting
;;  commands where the file name is read using `read-file-name' with a
;;  predicate that tests various bookmark fields.
;;
;;  For example, by default (for Emacs 21 or later), you can use `C-x
;;  j a' or `C-x 4 j a' to visit an autofile bookmark.  These keys are
;;  bound to `bmkp-find-file' and `bmkp-find-file-other-window',
;;  respectively (which are also known as `bmkp-autofile-jump' and
;;  `bmkp-autofile-jump-other-window').
;;
;;  Similarly, you can use prefix key `C-x j t a' followed by the
;;  usual tags-command suffix keys (e.g. `+', `% *') to visit a file
;;  or directory (that is, jump to an autofile bookmark) that is
;;  tagged in a particular way.  See (@> "Tagging Files").  All of the
;;  autofile "jump" commands are really `find-file' commands: they
;;  read a file name using `read-file-name', letting you navigate up
;;  and down the file hierarchy.
;;
;;  In addition to the single autofile bookmark you can create for a
;;  given absolute file location, you can of course create additional
;;  bookmarks to the same file, using different bookmark names.  Among
;;  other things, this lets you tag the same file in different ways.
;;
;;  
;;(@* "Bookmarking the Marked Files in Dired")
;;  *** Bookmarking the Marked Files in Dired ***
;;
;;  If you use Dired+ (library `dired+.el'), then you can bookmark all
;;  of the marked files in a Dired buffer at once, as autofiles, even
;;  if you normally do not or cannot visit those files in Emacs.
;;  These keys are available in Dired:
;;
;;    `M-b'                   - Bookmark each marked file
;;    `C-M-S-b' (aka `C-M-B') - Bookmark each marked file in a
;;                              bookmark-file that you specify
;;    `C-M-b'                 - Bookmark each marked file in a
;;                              bookmark-file you specify, and create
;;                              a bookmark for that bookmark-file
;;
;;  Each of these commands bookmarks each of the marked files as an
;;  autofile.  By default, the bookmark file used for the latter two
;;  commands is in the current directory.
;;
;;  If you use multiple `C-u' as a prefix arg for these commands, then
;;  you can bookmark all of the files in Dired, regardless of
;;  markings, as follows:
;;
;;    `C-u C-u'         - Use all files in Dired, except directories
;;    `C-u C-u C-u'     - Use all files and dirs, except `.' and `..'
;;    `C-u C-u C-u C-u' - Use all files and all directories
;;
;;  `C-M-b' not only bookmarks each of the marked files, it also
;;  creates a bookmark-file bookmark for that set of bookmarks.  See
;;  (@> "Bookmark-File Bookmarks"), below.
;;
;;  You can later "jump" to that bookmark to load its set of
;;  bookmarks.  If you use `C-u' when you jump to it, then you switch
;;  bookmark files, so that `C-x r l' displays only the bookmarks
;;  created from the marked files.  Without `C-u', jumping to the
;;  bookmark-file bookmark simply loads its bookmarks into the current
;;  set of bookmarks.
;;
;;  
;;(@* "Bookmarking Compilation, Grep, and Occur Hits")
;;  *** Bookmarking Compilation, Grep, and Occur Hits ***
;;
;;  In a similar way, you can bookmark the file or buffer positions of
;;  selected hits in a compilation buffer (including `*grep*') or an
;;  `occur' or `multi-occur' buffer.
;;
;;  `C-c C-b' in such a buffer bookmarks the target of the hit at
;;  point.  `C-c C-M-b' bookmarks the target of each hit in the
;;  buffer.
;;
;;  `C-c C-M-b' in these buffers is thus similar to `M-b' in a Dired
;;  buffer.  Unlike Dired, however, there is no way to mark such hits.
;;  Every hit is bookmarked.
;;
;;  Nevertheless, you can get the same effect.  Just use `C-x C-q' to
;;  make the buffer writable (e.g. temporarily), and then remove any
;;  hits that you do not want to bookmark.  You can remove hits anyway
;;  you like, including by `C-k' and by regexp (`M-x flush-lines' or
;;  `M-x keep-lines').
;;
;;  See also: (@> "Autonamed Bookmarks - Easy Come Easy Go"),
;;  bookmarking occur hits using autonamed bookmarks.
;;
;;
;;(@* "Bookmarking Files That You Cannot Visit")
;;  *** Bookmarking Files That You Cannot Visit ***
;;
;;  There are lots of files that you use that you never visit, but
;;  that you might like to keep track of or access in other ways
;;  besides opening them in Emacs: music files, image files, whatever.
;;
;;  You can define a new kind of bookmark for any file type you are
;;  interested in, implementing a bookmark handler for it that
;;  performs the appropriate action on it when you "jump" to it.  That
;;  action needs to be expressible using an Emacs function, but it
;;  need not have anything to do with visiting the file in Emacs.
;;
;;  When you bookmark a target file that Emacs recognizes as an image
;;  or sound file, an appropriate handler is used automatically.
;;
;;  After you create individual bookmarks for, say, music or image
;;  files, you can use `P B' in the bookmark-list display to show only
;;  those bookmarks, and then use `C-x r m' to bookmark that state of
;;  the bookmark-list.
;;
;;  That bookmark-list bookmark in effect becomes a music playlist or
;;  an image library or slideshow.  Jump to it anytime you want to
;;  listen to that set of music pieces or view those images.  And you
;;  can use `C-x p B' and then `C-x p next' to cycle among the music
;;  pieces or images (slideshow).  (See (@> "Cycling the Navigation List").)
;;
;;  Together with the use of bookmark tags, this gives you a handy way
;;  to organize and access objects of any kind.  See (@> "Bookmark Tags").
;;
;;  You use option `bmkp-default-handler-associations' to control
;;  which operation (bookmark handler) to use for which file type.
;;  This is a set of associations (an alist) with key a regexp
;;  matching a file name and with value a Lisp sexp that evaluates to
;;  a shell command (a string) or an Emacs function (a symbol or
;;  lambda form).
;;
;;  The handler for the bookmark created invokes the shell command or
;;  the Emacs function with the file name as argument.
;;
;;  Here is an example option value:
;;
;;   (("\\.ps$" . "gsview32.exe")
;;    ("\\.html?$" . browse-url))
;;
;;  This value creates a bookmark that, when you jump to it, invokes
;;  shell command `gsview32.exe' on the bookmark's target file if it
;;  is PostScript (extension `.ps'), and invokes Emacs Lisp function
;;  `browse-url' on the file if it is HTML (extension `.htm' or
;;  `.html').
;;
;;  The default value of `bmkp-default-handler-associations' is taken
;;  from the value of option `dired-guess-shell-alist-user' (from
;;  Dired-X).  If no matching file association is found in
;;  `bmkp-default-handler-associations', then the associations in
;;  `bmkp-default-handler-associations' are used to find a shell
;;  command appropriate to the target file type.
;;
;;
;;(@* "Opening Bookmarks Using Windows File Associations")
;;  *** Opening Bookmarks Using Windows File Associations ***
;;
;;  If you use Microsoft Windows there is no need to define new
;;  bookmark types and handlers, if the action you want is the one
;;  that Windows associates with the file.  You already have a set of
;;  file/program associations, and Bookmark+ recognizes these as
;;  alternative handlers.
;;
;;  You can thus take advantage of Windows file associations to open
;;  bookmarks for files of all kinds.  To do this, you also need
;;  library `w32-browser.el'.  In the bookmark list, the following
;;  keys are bound to commands that open bookmarks using the
;;  associated Windows `Open' applications:
;;
;;    `M-RET'     - `bmkp-bmenu-w32-open'
;;    `M-mouse-2' - `bmkp-bmenu-w32-open-with-mouse'
;;    `M-o'       - `bmkp-bmenu-w32-open-select'
;;
;;  Windows file associations are always available to you, in addition
;;  to any other file associations that you define using
;;  `bmkp-default-handler-associations' (see
;;  (@> "Bookmarking Files That You Cannot Visit")).
;;
;;  You can thus have two different programs associated with the same
;;  kind of file.  Your MS Windows file association for PostScript
;;  might, for example, use Adobe Distiller to create a PDF file from
;;  PostScript, while your `bmkp-default-handler-associations'
;;  association for PostScript might use GhostView to display it
;;  directly.
 
;;(@* "Tagging Files")
;;  ** Tagging Files **
;;
;;  Section (@> "Tags: Sets of Bookmarks") covers bookmark tags, which
;;  are persistent metadata that you define to help you organize
;;  bookmarks into meaningful sets.
;;
;;  Section (@> "Autofile Bookmarks") describes autofile bookmarks,
;;  which, in effect, let you treat files generally as if they were
;;  bookmarks.  You can choose a file to visit or act on by its name
;;  and location, but also by its bookmark metadata.
;;
;;  In particular, you can tag a file - that is, specify tags for its
;;  associated autofile bookmark.  And you can then visit a file that
;;  has a given set of tags.  Bookmark+ provides file commands that
;;  automatically create and manipulate autofile bookmarks, that is,
;;  bookmarks that have the same name as the files they tag.
;;
;;  Command `bmkp-tag-a-file' (aka `bmkp-autofile-add-tags'), bound by
;;  default to `C-x p t + a', prompts you for a set of tags and a file
;;  location, and creates or sets the corresponding autofile bookmark.
;;  Command `bmkp-untag-a-file' (aka `bmkp-autofile-remove-tags'),
;;  bound by default to `C-x p t - a', similarly lets you remove
;;  specified tags from a file.
;;
;;  If you also use library Icicles, then you can act on multiple
;;  files during the same command (a "multi-command").  You can thus
;;  all at once tag a set of files the same way, or act on a set of
;;  files that are tagged similarly.
;;
;;  If you also use library Dired+ (`dired+.el') then you can use
;;  `C-+' to add tags to the marked files and `C--' to remove tags
;;  from them.  You can use `C-M-+' and `C-M--' to do the same thing
;;  for the current file.  You can also use items from the Dired menus
;;  to do these things.
;;
;;  Bookmark+ provides two kinds of command for visiting files
;;  associated with bookmarks that have tags.
;;
;;  The first kind uses bookmarks directly: you choose a bookmark
;;  name, not a file name, but the candidates are only file and
;;  directory bookmarks.  These commands have the prefix `bmkp-file-'.
;;
;;  As a special case, commands with the prefix `bmkp-file-this-dir-'
;;  limit the choices to bookmarks for files and subdirectories of the
;;  current directory.  By default, the commands across all
;;  directories are on prefix key `C-x 4 j t f' and those for the
;;  current directory only are on prefix key `C-x j t C-f'.  See
;;  (@> "Different Types of Jump Commands") for more about these
;;  commands.
;;
;;  The second kind of command is for visiting tagged files, that is,
;;  autofile bookmarks.  These commands are available only for Emacs
;;  21 and later (because they use `read-file-name' with a PREDICATE
;;  argument, not available for Emacs 20).  The candidates are file
;;  names, not bookmark names.  These commands have the prefix
;;  `bmkp-find-file-', and by default they are on the prefix key `C-x
;;  j t a'.  (In general, the keys `f' and `a' are used in key
;;  sequences for file and autofile bookmarks, respectively.)
;;
;;  For example:
;;
;;    `C-x j t f % +'   is `bmkp-file-some-tags-regexp-jump'
;;    `C-x j t C-f % +' is `bmkp-file-this-dir-some-tags-regexp-jump'
;;    `C-x j t a % +'   is `bmkp-find-file-some-tags-regexp'
;;
;;  * The first of these visits any file bookmark that has at least
;;    one tag among the tags you specify, and you choose among
;;    bookmark names.  The files can be in any directories.
;;
;;  * The second is similar to the first, but only bookmarks for files
;;    in the current directory are candidates.
;;
;;  * The third is similar regarding tags, but it uses
;;    `read-file-name', so you can browse among all files, up and down
;;    the file hierarchy.  The candidates are file names, not bookmark
;;    names.
;;
;;  If you use Icicles, there are similar sets of commands, but they
;;  all let you act on multiple files at the same time
;;  (multi-commands).  For example, you can delete (or byte-compile
;;  or...) a set of files according to their tags.
;;
;;  Remember that you can create multiple bookmarks for the same file,
;;  providing them with different sets of tags.  (Only one of the
;;  bookmarks is the autofile bookmark.)
;;
;;  You can also use multiple bookmark files (the files that record
;;  bookmarks).  Different projects can thus have different tags for
;;  the same sets of files, even using just autofile bookmarks.  See
;;  (@> "Using Multiple Bookmark Files").
;;
;;  A file bookmark can have any number of tags, and multiple file
;;  bookmarks can have the same tag.  You can sort, show/hide, or mark
;;  files based on their tags.
 
;;(@* "Using Multiple Bookmark Files")
;;  ** Using Multiple Bookmark Files **
;;
;;  Bookmark-list views (see
;;  (@> "Bookmark-List Views - Saving and Restoring State")) provide
;;  one way to switch among various sets of bookmarks that you use.
;;  But that feature affects only the bookmarks that you see displayed
;;  in buffer `*Bookmark List*', not the actual set of available
;;  bookmarks.
;;
;;  The bookmarks available to you are defined in a bookmark file.  By
;;  default, they are stored in the file named by option
;;  `bookmark-default-file' (`~/.emacs.bmk', by default).  You do not
;;  need to load or save this file manually; Emacs does that for you
;;  automatically.
;;
;;  But you can also have extra, alternative bookmark files if you
;;  want, and at any time you can change the bookmark file that is
;;  current.  To do that, use `C-x p L' (uppercase `L'), which is
;;  bound to command `bmkp-switch-bookmark-file'.
;;
;;  Having multiple bookmark files gives you an added degree of
;;  flexibility.  You can see which file is current at any time by
;;  using `?' or `C-h m' in the buffer `*Bookmark List*' (or anywhere
;;  else using `M-x bmkp-bmenu-mode-status-help').
;;
;;  When you switch to another bookmark file, the default file to
;;  switch to is the last bookmark file you used (in the same
;;  session).  So it is trivial to toggle back and forth between two
;;  bookmark files: just hit `RET' to accept the default.
;;
;;  When bookmarks are saved automatically, or when you save them
;;  using `bookmark-save' (`S' in the bookmark list or `C-x p s'
;;  globally) and you don't use a prefix argument, they are saved in
;;  the current bookmark file.
;;
;;  You can turn off the automatic saving of the current bookmark
;;  file, by customizing option `bookmark-save-flag' to nil.  And you
;;  can toggle this option at any time, using `M-~' in the bookmark
;;  list (command `bmkp-toggle-saving-bookmark-file').
;;
;;  Besides using multiple bookmark files as *alternatives*, you can
;;  combine them, using them as component bookmark subsets (like
;;  modules).  To do that, use command `C-x p l' (lowercase `l'),
;;  which is bound to `bookmark-load', and do not use a prefix
;;  argument.  (Using a prefix argument with `C-x p l' is the same as
;;  using `C-x p L': it switches bookmark files.)  Here too the
;;  default is the name of the last bookmark file that you used.
;;
;;  To create additional bookmark files, to use either as alternatives
;;  or as components, you can either copy an existing bookmark file or
;;  use `bmkp-empty-file' (`C-x p 0') to create a new, empty bookmark
;;  file.  If you use `C-x p 0' with an existing bookmark file, then
;;  its bookmarks are all deleted - it is emptied.
;;
;;  Instead of simply copying a bookmark file, you can use
;;  `bookmark-save' with a prefix argument, or use `bookmark-write'
;;  (bound to `C-x p w'), to save the currently defined bookmarks to a
;;  different bookmark file.
;;
;;  However a bookmark file was created, you can switch to it and then
;;  add or delete bookmarks selectively, to change its content.
;;  Remember that you can delete bookmarks from the current set using
;;  command `bookmark-delete' (`C-x p d') or, in the bookmark list,
;;  using `d' plus `x' or marking then `D'.
;;
;;
;;(@* "Bookmark-File Bookmarks")
;;  *** Bookmark-File Bookmarks ***
;;
;;  A bookmark file is an excellent, persistent way to represent a set
;;  of bookmarks.  In particular, it can represent a project or a
;;  project component.  Switch among bookmark files to access
;;  different projects.  Load project components as you need them.
;;
;;  You can load a bookmark file using `C-x p L' (switch) or `C-x p l'
;;  (accumulate).  As a convenience, you can also load a bookmark file
;;  by jumping to a bookmark-file bookmark.
;;
;;  You use command `bmkp-set-bookmark-file-bookmark', bound to `C-x p
;;  x', to create a bookmark-file bookmark.  Jumping to such a
;;  bookmark just loads the bookmark file that it records.  With `C-u'
;;  (e.g. `C-u C-x p j project-foo'), jumping switches bookmark files.
;;  Without `C-u' it accumulates the loaded bookmarks.
;;
;;  A bookmark-file bookmark is not only an added convenience.  You
;;  can also use it in combination with other Bookmark+ features, such
;;  as tagging.
;;
;;  As a shortcut, in Dired (if you use library Dired+), `C-M-b'
;;  creates a bookmark-file bookmark.  The bookmark file that it
;;  records contains autofile bookmarks to each of the files that was
;;  marked in Dired at the time it was created.  Jumping to that
;;  bookmark-file bookmark makes those (marked) files available as
;;  bookmarks.  See also
;;  (@> "Use Dired to Bookmark Files without Visiting Them").
;;
;;  Note that the bookmark file in which a bookmark-file bookmark is
;;  recorded is not the same as the bookmark file recorded in that
;;  bookmark.
;;
;;  For example, when you use `C-M-b' in Dired, the bookmark-file for
;;  the marked files is, by default, file `.emacs.bmk' in the Dired
;;  directory.  So if you are in directory `/foo/bar' the default
;;  bookmark file for the marked files is `/foo/bar/.emacs.bmk'.  But
;;  the new bookmark-file bookmark created is recorded in the current
;;  bookmark file, whatever that might be (e.g. `~/.emacs.bmk').
 
;;(@* "The Bookmark List (Display)")
;;  ** The Bookmark List (Display) **
;;
;;  Bookmark+ enhances the bookmark list (aka the bookmark "menu
;;  list", a misnomer) that is displayed in buffer `*Bookmark List*'
;;  when you use `C-x r l' (command `bookmark-bmenu-list').
;;
;;  Bookmarks are highlighted to indicate their type. You can mark and
;;  unmark bookmarks, show or hide bookmarks of particular types, and
;;  more.  Bookmarks that have tags are marked with a `t'.  Bookmarks
;;  that have an annotation are marked with an `a' (not with a `*' as
;;  in vanilla `bookmark.el').  Bookmarks that have bookmark-highlight
;;  override settings (see (@> "Defining How to Highlight")) are
;;  marked with a one-character pink background.
;;
;;  Use `?' or `C-h m' in buffer `*Bookmark List*' for more
;;  information about the bookmark list, including the following:
;;
;;  * The current status of sorting, filtering, and marking.
;;
;;  * A legend for the faces used for different bookmark types.
;;
;;
;;(@* "Tag Commands and Keys")
;;  *** Tag Commands and Keys ***
;;
;;  There are lots of tag-related bookmark commands, and most are
;;  bound to keys in buffer `*Bookmark List*' as well as to other keys
;;  outside it.  How can you keep the commands straight or remember
;;  their keys?
;;
;;  In the bookmark list display, tags-command keys begin with prefix
;;  key `T'.  Elsewhere, they begin with prefix key `C-x p t' (or `C-x
;;  j t', for jump commands - see (@> "Different Types of Jump Commands")).
;;
;;  `C-h m' (or `?') is your friend, of course.  Likewise `T C-h' and
;;  `C-x p t C-h'.  Beyond that, the tag-related keys that are more
;;  than two keystrokes are organized as follows:
;;
;;    They all have the prefix key `T'.
;;
;;    `m' means mark
;;    `u' means unmark
;;    `>' stands for the marked bookmarks
;;    `*' means AND (set intersection; all)
;;    `+' means OR  (set union; some/any)
;;    `~' means NOT (set complement)
;;
;;  The key `T m *', for instance, marks (`m') the bookmarks that are
;;  tagged with all (`*' = AND) of a given set of tags.  It prompts you
;;  for one or more tags that the bookmarks must have, and it marks
;;  all bookmarks that have all of the tags you enter.
;;
;;  The key `T u ~ +' unmarks (`u') the bookmarks that do not (`~')
;;  have any (`+' = OR) of the tags you specify.  And so on.
;;
;;  The marking and unmarking commands for tags compare the tags a
;;  bookmark has with tags that you enter.  Any bookmarks that have no
;;  tags are ignored - they are neither marked nor unmarked by these
;;  commands.
;;
;;  `+' and `-' can also mean add and remove tags, respectively, and
;;  `>' stands for the marked bookmarks.  So `T > +' adds (`+') one or
;;  more tags to each of the marked (`>') bookmarks.
;;
;;  In general, the tag-related commands let you enter a set of tags,
;;  one at a time.  Thus, instead of having a command that adds a
;;  single tag to the current bookmark, you have a command that adds
;;  any number of tags to it.  To add just a single tag, hit `RET'
;;  twice: once to enter the tag, and once again to indicate that it
;;  is the last (i.e., the only) one.
;;
;;  If you just hit `RET' immediately, specifying an empty set of
;;  tags, then each of the commands does something appropriate.  For
;;  `T m *', for instance, an empty list of tags means to mark (only)
;;  the bookmarks that have any tags at all.
;;
;;  Finally, for the marking/unmarking tags commands, a prefix
;;  argument flips the sense of the command, in this way:
;;
;;  "some are" -> "some are NOT", i.e., "not all are" (and vice versa)
;;  "all are"  -> "all are NOT",  i.e., "none are"    (and vice versa)
;;
;;  In other words:
;;
;;    C-u T m *    =  T m ~ +  (all are NOT      = not some are)
;;    C-u T m ~ +  =  T m *    (not some are NOT = all are)
;;    C-u T m +    =  T m ~ *  (some are NOT     = not all are)
;;    C-u T m ~ *  =  T m +    (not all are NOT  = some are)
;;
;;  You'll figure it out ;-).
;;
;;  Other important keys pertaining to tags (the keys in parentheses
;;  work in any buffer, not just buffer `*Bookmark List*'):
;;
;;  * `C-h RET' (`C-x p ?') shows you the tags that belong to a
;;    bookmark.  With a prefix argument it shows you the full internal
;;    form of the tags, that is, the name+value pairs.
;;
;;  * `T e' (`C-x p t e') lets you edit a bookmark's tags.
;;
;;  * `T l' (`C-x p t l') lists all tags currently known to Emacs
;;     (across all bookmarks).
;;
;;  * `T +' (`C-x p t + b') adds some tags to a bookmark.
;;    `T -' (`C-x p t - b') removes some tags from a bookmark.
;;    `T 0' (`C-x p t 0) removes all tags from a bookmark.
;;    `T d' (`C-x p t d) removes a set of tags from all bookmarks.
;;
;;  In the bookmark list display you can also sort bookmarks according
;;  to how they are tagged, even in complex ways.  See
;;  (@> "Sorting Bookmarks").
;;
;;
;;(@* "Tags: Sets of Bookmarks")
;;  *** Tags: Sets of Bookmarks ***
;;
;;  The best way to think about tags is as names of sets.  All
;;  bookmarks tagged `blue' constitute the bookmark set named `blue'.
;;
;;  The bookmarks visible in the bookmark list at any time also
;;  constitute an unnamed set.  Likewise, the marked bookmarks and the
;;  unmarked bookmarks are unnamed sets.  Bookmark+ is all about
;;  helping you act on sets of Emacs objects.  Bookmarks are named,
;;  persistent pointers to objects such as files and file sets.
;;  Bookmark tags are named, persistent sets of bookmarks (and hence
;;  of their target objects).
;;
;;  The marking commands make it easy to combine sets as unions or
;;  intersections.  And you can give the result a name for quick
;;  access later, just by adding a new tag.  in other words, do the
;;  set-definition work only once, and name the result.
;;
;;  How would you tag as `Java IDE Projects' the bookmarks that are
;;  already tagged both `Java' and `ide'?
;;
;;  1. `T m * Java RET ide RET RET', to mark them.
;;  2. `T > + Java IDE Projects RET RET, to tag them.
;;
;;  How would you sort your bookmarks, to show all those tagged both
;;  `blue' and `moon' first?
;;
;;  1. `T m * blue RET moon RET RET', to mark them.
;;  2. `s >' to sort the marked bookmarks first
;;     (see (@> "Sorting Bookmarks"), below).
;;
;;  If you wanted to show only the marked bookmarks, instead of
;;  sorting to put them first in the list, you would use `>'
;;  instead of `s >'.
;;
;;  How would you query-replace the set of files that are tagged with
;;  any of the tags `alpha', `beta', and `gamma', but are not tagged
;;  `blue' or `moon'?
;;
;;    1. `F S', to show only the file bookmarks.
;;    2. `T m + alpha RET beta RET gamma RET RET', to mark the
;;       bookmarks that have at least one of those tags.
;;    3. `T u + blue RET moon RET RET', to unmark those that are
;;       tagged `blue' or `moon'.
;;    4. `M-q' to query-replace the marked files.
;;
;;  If that were a set of files that you used often, then you would
;;  name the set by giving the files a new tag.
;;
;;  The point is that bookmarks, and bookmark tags in particular, let
;;  you define and manipulate sets of Emacs objects.  It doesn't
;;  matter how you define such a set: regexp matching (marking,
;;  filtering), by object type, by tag combinations...  Sets need not
;;  be named to act on them, but you can provide them with persistent
;;  names (tags) to avoid redefining them over and over.  Manipulation
;;  of bookmarked objects includes visiting, searching, and
;;  query-replacing.  And you can define your own bookmark types
;;  (using bookmark handlers) and associated manipulations.
;;
;;
;;(@* "Open Dired for the Marked File Bookmarks")
;;  *** Open Dired for the Marked File Bookmarks ***
;;
;;  You've seen that the bookmark list has many features that are
;;  similar to Dired features.  But Dired is specialized for files and
;;  directories, and it has many more features for manipulating them.
;;  The bookmark list is not intended to replace Dired.
;;
;;  You can, however, use the bookmark list to take advantage of
;;  arbitrary Dired features for file and directory bookmarks.
;;  Command `bmkp-bmenu-dired-marked' (`M-d >') weds Bookmark+'s
;;  set-defining and set-manipulating features (tagging, marking,
;;  filtering etc.) to Dired's file-manipulating features.
;;
;;  `M-d >' opens a Dired buffer that is specialized for just the
;;  files and directories whose bookmarks are marked in the bookmark
;;  list.  (Other marked bookmarks are ignored by the command.)  The
;;  files and directories can be located anywhere; they need not be in
;;  the same directory.  They are listed in Dired using absolute file
;;  names.
;;
;;  (In Emacs versions prior to release 23.2, only local files and
;;  directories can be handled, due to Emacs bug #5478.  In such
;;  versions, remote-file bookmarks are ignored by `M-d >'.)
;;
;;  This Bookmark+ feature makes sets of files and directories
;;  immediately amenable to all of the operations provided by Dired.
;;
;;  It is particularly useful in conjunction with tags.  Use bookmark
;;  tags and marks to define a possibly complex set of file and
;;  directory bookmarks.  Then hit `M-d >' to list them in a Dired
;;  buffer.  Then use any Dired commands you want to act on any of
;;  them.
;;
;;  For example, to compress bookmarked files that are tagged with
;;  both `blue' and `moon':
;;
;;  1. Mark them using `T m * blue RET moon RET RET'.
;;  2. Open Dired for them using `M-d >'.
;;  3. Mark them in Dired, then compress them using `Z'.
;;
;;  Since tags are persistent, Bookmark+ gives you a good way to
;;  define an arbitrary set of files as a project and then open them
;;  in Dired at any time to operate on them.
;;
;;  If you use Dired+ (library `dired+.el'), then a similar feature is
;;  available for the marked files and directories: You can use
;;  `C-M-*' in Dired to open a separate Dired buffer for them only.
;;  You can of course then bookmark that resulting Dired buffer, if
;;  you like.
;;
;;  If you use Icicles, then whenever you use a command that reads a
;;  file (or directory) name, you can use `M-|' during file-name
;;  completion to open Dired on the currently matching set of file
;;  names.  That is, this is the same kind of special Dired buffer
;;  that is provided for file and directory bookmarks by `M-d >' in
;;  the bookmark list.
;;
;;
;;(@* "Marking and Unmarking Bookmarks")
;;  *** Marking and Unmarking Bookmarks ***
;;
;;  Bookmark+ enhances the marking and unmarking of bookmarks in the
;;  bookmark list in several ways.  These enhancements are similar to
;;  features offered by Dired and Dired-X.  You can use:
;;
;;  * `% m' to mark the bookmarks that match a regexp.  The entire
;;    line in the bookmark list is checked for a match, that is, both
;;    the bookmark name and the file name, if shown.
;;
;;  * `M-DEL' (or `U') to unmark all bookmarks, or all that are marked
;;    `>', or all that are flagged `D' for deletion.
;;
;;  * `t' to toggle (swap) the marked and unmarked bookmarks: those
;;    that are marked become unmarked, and vice versa.
;;
;;  * `>' to show only the marked bookmarks or `<' to show only the
;;    unmarked bookmarks.  Repeat to show them all again.
;;
;;  * `F M', `I M' etc. to mark only the file bookmarks, Info
;;    bookmarks etc.  (The first key here is the same as the
;;    corresponding filter key, e.g. `F' for files - see next topic.)
;;
;;
;;(@* "Filtering Bookmarks (Hiding and Showing)")
;;  *** Filtering Bookmarks (Hiding and Showing) ***
;;
;;  You can hide and show different sets of bookmarks in the bookmark
;;  list.  There are commands to show only bookmarks of a particular
;;  type - e.g. `I S' to show only Info bookmarks.  These are, in
;;  effect, shortcuts for first marking those bookmarks and then
;;  showing only the marked bookmarks (and then unmarking).  For
;;  example, `F S' is a shortcut for `F M >' (and then `U RET').
;;
;;  You can also filter to show only the bookmarks that match a given
;;  regexp.  There are two ways to do this:
;;
;;  * Use `P B' (for "pattern", "bookmark") and type a regexp.  The
;;    bookmarks are filtered incrementally, as you type.  Only the
;;    bookmark name is matched (not the file name).  Hit any
;;    non-inserting key, such as `RET', to finish defining the
;;    pattern.
;;
;;    Similarly, hit `P F' for bookmarks whose file names match a
;;    regexp, `P A' for bookmarks whose annotations match a regexp,
;;    and `P T' for bookmarks with one or more tags that match a
;;    regexp.  See (@> "Bookmark Tags"), above, for information about
;;    tags.
;;
;;  * Just as in Dired, use `% m' to mark the bookmarks that match a
;;    regexp.  Then use `>' to show only the marked bookmarks.  See
;;    (@> "Marking and Unmarking Bookmarks"), above.
;;
;;    This method has the advantage that you can show the complement,
;;    the bookmarks that do *not* match the regexp, by using `<'
;;    instead of `>'.  It also has the advantage that matching checks
;;    the combination of bookmark name and file name (use `M-t' to
;;    toggle showing file names).
;;
;;
;;(@* "Only Visible Bookmarks Are Affected")
;;  *** Only Visible Bookmarks Are Affected ***
;;
;;  Commands that operate on the current bookmark or on the marked or
;;  the unmarked bookmarks act only on bookmarks that are displayed
;;  (not hidden).  This includes the commands that mark or unmark
;;  bookmarks.  This means that you can easily define any given set of
;;  bookmarks.
;;
;;  For example:
;;
;;    Use `F S' to show only bookmarks associated with files.
;;    Use `% m' to mark those that match a particular regexp.
;;    Use `R S' to show only bookmarks that have regions.
;;    Use `m' to mark some of those region bookmarks individually.
;;    Use `.' to show all bookmarks.
;;    Use `t' to swap marked and unmarked (so unmarked are now marked)
;;    Use `D' to delete all of the marked bookmarks (after confirming)
;;
;;  Together, steps 1-7 delete all file bookmarks that match the
;;  regexp and all region bookmarks that you selectively marked.
;;
;;
;;(@* "Omitting Bookmarks from Display")
;;  *** Omitting Bookmarks from Display ***
;;
;;  In sections (@> "Marking and Unmarking Bookmarks") and
;;  (@> "Filtering Bookmarks (Hiding and Showing)") you learned how
;;  to hide and show bookmarks in the bookmark list.  This section is
;;  about a different kind of hiding, called "omitting".
;;
;;  Omitted bookmarks are not shown in the bookmark list, no matter
;;  what filtering is used.  The only way to show omitted bookmarks is
;;  to show all of them and only them, using `O S', which is bound to
;;  command `bmkp-bmenu-show-only-omitted'.
;;
;;  Omitted bookmarks are still available even if they are not shown,
;;  and you can still jump to them (e.g. using `C-x r b').  You just
;;  don't see them in the bookmark list.  And that's the reason for
;;  this feature: to hide those bookmarks that you don't care to see.
;;
;;  One use for this feature is to hide the component bookmarks that
;;  make up a sequence bookmark (see
;;  (@> "Function, Sequence, and Variable-List Bookmarks")).  The
;;  default behavior when you create a sequence bookmark is in fact to
;;  omit its component bookmarks from the displayed list.
;;
;;  You can omit any bookmarks by marking them and then using `O >'
;;  (`bmkp-bmenu-omit/unomit-marked').  If you are looking at the
;;  omitted bookmarks (after using `O S'), then `O >' un-omits the
;;  bookmarks marked there.  Think of two complementary spaces: the
;;  normal bookmark list and the omitted bookmark list.  When you use
;;  `O >', the marked bookmarks that are currently shown are moved to
;;  the opposite space.
;;
;;  You can un-omit all of the omitted bookmarks at once, using `O U'
;;  (`bmkp-unomit-all').  You can also call this command from outside
;;  the bookmark-list display.
;;
;;
;;(@* "Sorting Bookmarks")
;;  *** Sorting Bookmarks ***
;;
;;  Filtering hides certain kinds of bookmarks.  Sometimes, you want
;;  to see bookmarks of various kinds, but you want them to be grouped
;;  or sorted in different ways, for easy recognition, comparison, and
;;  access.
;;
;;  Bookmarks shown in the bookmark list are sorted using the current
;;  value of option `bmkp-sort-comparer'.  (If that is nil, they are
;;  unsorted, which means they appear in reverse chronological order
;;  of their creation.)
;;
;;  You can use `s s'... (repeat hitting the `s' key) to cycle among
;;  the various sort orders possible, updating the display
;;  accordingly.  By default, you cycle among all available sort
;;  orders, but you can shorten the cycling list by customizing option
;;  `bmkp-sort-orders-for-cycling-alist'.
;;
;;  You can also change directly to one of the main sort orders
;;  (without cycling) using `s n', `s f n', etc. - use `C-h m' or `?'
;;  for more info.
;;
;;  You can reverse the current sort direction (ascending/descending)
;;  using `s r'.  Also, repeating any of the main sort-order commands
;;  (e.g. `s n') cycles among that order, the reverse, and unsorted.
;;
;;  For a complex sort, which involves composing several sorting
;;  conditions, you can also use `s C-r' to reverse the order of
;;  bookmark sorting groups or the order within each group (depending
;;  on whether `s r' is also used).  Be aware that this can be a bit
;;  unintuitive.  If it does not do what you expect or want, or if it
;;  confuses you, then don't use it ;-).  (`s C-r' has no noticeable
;;  effect on simple sorting.)
;;
;;  Remember that you can combine sorting with filtering different
;;  sets of bookmarks - bookmarks of different kinds (e.g. Info) or
;;  bookmarks that are marked or unmarked.
;;
;;  Finally, you can easily define your own sorting commands and sort
;;  orders.  See macro `bmkp-define-sort-command' and the
;;  documentation for option `bmkp-sort-comparer'.  (Bookmark+ uses
;;  option `bmkp-sort-comparer'; it *ignores* vanilla Emacs option
;;  `bookmark-sort-flag'.)
;;
;;  Of particular note is that you can interactively define commands
;;  that sort by a given list of tags - you use keys `T s' (command
;;  `bmkp-define-tags-sort-command') to do that.  You are prompted for
;;  the tags to sort by.  Bookmarks are sorted first according to
;;  whether they are tagged with the first tag, then the second tag,
;;  and so on.  Otherwise, sorting is by bookmark name.
;;
;;  The tags you specify are used, in order, in the name of the new
;;  command.  For example, if you enter tags `alpha', `beta', and
;;  `gamma', in that order, then the sorting command created is
;;  `bmkp-bmenu-sort-alpha-beta-gamma'.  The new command is saved in
;;  your bookmark commands file (`bmkp-bmenu-commands-file').
;;
;;  Note that because you can add a new tag to all bookmarks that have
;;  some given set of tags, you can use that single (new) tag to
;;  represent the entire tag set.  Sorting by that tag is then the
;;  same as sorting by the tag set.  You can of course use overlapping
;;  sets in the composite sort command.  You can, for example, sort
;;  first according to tag `tag1', which represents the set of tags
;;  `alpha', `beta', `gamma', `delta', and then sort according to tag
;;  `tag2', which represents the set of tags `beta', `delta'.
;;
;;  See also (@> "Use Bookmark+ with Icicles") - the same technique is
;;  used in Icicles for sorting bookmarks as completion candidates.
 
;;(@* "Bookmarks for Specific Files or Buffers")
;;  ** Bookmarks for Specific Files or Buffers **
;;
;;  A bookmark typically records a position or a region in a file or
;;  buffer.  Sometimes you are interested in accessing or examining
;;  only the bookmarks for particular files or buffers.  For example,
;;  you might want to navigate among the bookmarks for the current
;;  buffer.  Or you might want to search the regions recorded in the
;;  bookmarks for a particular file.
;;
;;  For a bookmark, the recorded file and buffer name differ in that
;;  the file name is absolute.  Bookmarks for buffer `foo.el' include
;;  all files named `foo.el', whereas bookmarks for file
;;  `/project1/lisp/foo.el' include only the files in that one
;;  directory.
;;
;;  Bookmark+ provides some commands to handle these use cases.  The
;;  keys bound to these commands use `f' for file and `b' for buffer.
;;  In the bookmark-list display, the following keys affect the
;;  bookmarks for a particular file or buffer whose name you provide
;;  (with completion).
;;
;;  * `= f M' and `= b M' - mark 
;;  * `= f S' and `= b S' - show (only)
;;
;;  For navigation, the following keys jump to bookmarks for
;;  particular files or buffers.  (Use `C-x 4 j' for other-window.)
;;
;;  * `C-x j .'                   - current buffer
;;  * `C-x j = f' and `C-x j = b' - specified file(s) or buffer(s)
;;
;;  For the `=' keys you are prompted for one or more file names or
;;  buffer names.
;;
;;  Finally, because the bookmarks in the current buffer can be of
;;  particular interest, `C-x p .' opens the bookmark-list display for
;;  only those bookmarks.
 
;;(@* "Cycling, Navigation List, Autonaming")
;;  ** "Cycling, Navigation List, Autonaming" **
;;
;;  Using completion to jump to a bookmark is handy.  It lets you
;;  choose a bookmark by its name and gives you direct ("random")
;;  access to it.
;;
;;  Sometimes, however, you don't much care what a bookmark is named,
;;  and you want to cycle quickly among relatively few, related
;;  bookmarks.  Obviously, the smaller the number of bookmarks in the
;;  set, the more convenient cycling is - with many bookmarks cycling
;;  can become tedious.
;;
;;  An analogy: If your TV has lots of channels, then the channel
;;  up/down buttons on the remote control are not so useful: 32, 33,
;;  34, ..., 79!  Unless the channel you want happens to be near the
;;  current channel, cycling around a huge ring of channels is not the
;;  way to go.  And just because your TV receives lots of channels
;;  does not mean that you watch them all or that you are equally
;;  interested in them all.
;;
;;  Some TV remote controls have a feature that mitigates this
;;  problem.  You can define a ring of favorite channels, and there
;;  are two additional buttons that let you cycle forward and backward
;;  around the ring, skipping the channels in between.  The number of
;;  favorites is relatively small, so cycling is not tedious.  More
;;  importantly, all of the channels in the ring are ones you are
;;  interested in.
;;
;;  Extend this idea to allow for assigning different sets of channels
;;  to the favorites ring at different times: choose the ring you want
;;  at any time: sports, music, films, science, art, history, and so
;;  on.  Add the possibility of sorting those sets in various ways, to
;;  further facilitate cycling, and you arrive at the idea behind the
;;  Bookmark+ navigation list.
;;
;;  Another analogy is a music playlist.  You can use Bookmark+ as a
;;  simple music player by bookmarking music files.  Similarly, you
;;  can use Bookmark+ to create slideshows by bookmarking image files.
;;  Cycle the navigation list to move through the slide show.
;;
;;  If you use MS Windows, you can take advantage of your existing
;;  file associations to open your bookmarks using the appropriate
;;  program - no need to define a new bookmark type and handler.  See
;;  (@> "Bookmarking Files That You Cannot Visit").
;;
;;  Note: The default value of option `bmkp-use-region' is `t', not
;;  `cycling-too', which means that when you cycle to a bookmark its
;;  recorded region (if any) is not activated.  This is probably what
;;  you want most of the time.  Cycling is a repetitive action, and if
;;  you cycle to a bookmark with no recorded region then an already
;;  active region is just extended.  Customize the value to
;;  `cycling-too' if you prefer that behavior.
;;
;;
;;(@* "The Bookmark Navigation List")
;; *** "The Bookmark Navigation List ***
;;
;;  Bookmark+ is all about letting you define and manipulate sets of
;;  bookmarks.  When a bookmark set can be used for cycling (as well
;;  as jumping) it is called the "navigation list" or "navlist", for
;;  short.
;;
;;  In other words, Bookmark+ lets you cycle among any set of
;;  bookmarks.  When you cycle, it is the set that currently
;;  constitutes the navigation list that is cycled.
;;
;;  Here are two ways to define the navigation list:
;;
;;  * `C-x p :' (`bmkp-choose-navlist-of-type') - As the set of all
;;    bookmarks of a certain type (`any' or empty input means use all
;;    bookmarks).
;;
;;  * `C-x p B' (`bmkp-choose-navlist-from-bookmark-list') - As the
;;    set of all bookmarks corresponding to a bookmark-list bookmark,
;;    that is the bookmarks corresponding to a given recorded state of
;;    buffer `*Bookmark List*'.
;;
;;  Each of these lets you choose a set of bookmarks using completion.
;;  For `C-x p :' you are prompted for the type of bookmark
;;  (e.g. `dired').
;;
;;  For `C-x p B' you are prompted for the name of a bookmark-list
;;  bookmark that you created.  But you can also choose the candidate
;;  `CURRENT *Bookmark List*' to capture the bookmarks that would be
;;  shown currently in the `*Bookmark List*' (even if the list is not
;;  displayed now).  See (@> "State-Restoring Commands and Bookmarks")
;;  for information about bookmark-list bookmarks.
;;
;;  If you do not define the navigation list before you start cycling,
;;  it is automatically defined as follows:
;;
;;  * If you cycle using a current-buffer cycling key such as `C-x p
;;    down' (see (@> "Cycling in the Current Buffer")) then the
;;    bookmarks in the current buffer are used as the navlist.
;;
;;  * Otherwise, a snapshot is taken of the the bookmarks currently in
;;    the global bookmark list (the value of variable
;;    `bookmark-alist') as the navlist.
;;
;;  However the navlist is defined, it is important to remember this:
;;  it is a static snapshot of some set of bookmarks taken at a given
;;  time.  Subsequent changes to the bookmark list that was copied are
;;  not reflected in the navlist.  If you add a bookmark it will not
;;  be among those cycled.  But see also
;;  (@> "Cycling Dynamic Sets of Bookmarks") for how to cycle dynamic
;;  sets.
;;
;;  You can update the navlist at any time by taking another snapshot
;;  of the same bookmark list you used for the last snapshot.  For the
;;  global bookmark list just use `C-x p : RET'.  (You can of course
;;  bind that action to a shorter key sequence if you like.)
;;
;;  Besides cycling among the bookmarks of the navlist (see next),
;;  once you have defined the navigation list you can use `C-x j N' or
;;  `C-x 4 j N' to jump to its bookmarks, as mentioned in section
;;  (@> "Different Types of Jump Commands").
;;
;;  Note that just because you might have used `C-x p B' to define the
;;  navlist using a particular bookmark-list bookmark or the current
;;  `*Bookmark List*' state, that does not mean that the `*Bookmark
;;  List*' state at any given time necessarily reflects the navlist
;;  bookmarks.  The two are separate.  You can, however, open the
;;  `*Bookmark List*' so that it reflects the bookmarks currently in
;;  the navigation list, using `C-x p N' (`bmkp-navlist-bmenu-list').
;;  
;;
;;(@* "Cycling the Navigation List")
;; *** "Cycling the Navigation List" ***
;;
;;  So you choose a navigation list.  How do you then cycle among its
;;  bookmarks?
;;
;;  Commands `bmkp-next-bookmark' and `bmkp-previous-bookmark' cycle
;;  to the next and previous bookmark in the navigation list (with
;;  wraparound).
;;
;;  You can bind these to any keys you like, but it's obviously better
;;  to choose keys that are easily repeatable (e.g. by holding them
;;  pressed).  Some people who are used to using MS Visual Studio
;;  might want to use `f2' and `S-f2' to cycle forward and backward.
;;
;;  Bookmark+ does not define such key bindings, but you can.  What it
;;  does is define repeatable keys on the `bookmark-map' keymap, which
;;  has prefix `C-x p'.  To do this it binds similar commands that can
;;  be repeated by simply repeating the key-sequence suffix.  These
;;  are the keys:
;;
;;  Forward:  `C-x p f', `C-x p C-f', `C-x p right'
;;  Backward: `C-x p b', `C-x p C-b', `C-x p left'
;;
;;  (If you use an Emacs version prior to Emacs 22, you cannot use
;;  this prefix-key repeatable feature.)
;;
;;  In addition, if you use MS Windows then you can invoke the Windows
;;  `Open' action on each bookmark when you cycle, to act on its file
;;  using the program associated with the file type.  This lets you
;;  play music or display images in a playlist or slideshow fashion.
;;  These are the keys to do that:
;;
;;  Forward:  `C-x p next'   (PageDown key)
;;  Backward: `C-x p prior'  (PageUp key)
;;
;;  Being able to cycle among an arbitrary set of bookmarks is the
;;  most important feature of Bookmark+ cycling.  The other important
;;  feature is that if the navigation list is defined by `*Bookmark
;;  List*' then the characteristics of that bookmark display are
;;  respected for navigation.  Only the bookmarks visible in
;;  `*Bookmark List*' are included, and the `*Bookmark List*' sort
;;  order is used for navigation.
;;
;;  So you can not only choose any set of bookmarks for cycling at any
;;  given time, you can also cycle among them in an order you choose.
;;  For example, if in the bookmark list display (`C-x r l') you show
;;  only those file bookmarks that belong to a given project, and you
;;  have them sorted by file size, then cycling moves among only those
;;  files, in file-size order.
;;
;;  This is a main reason you will want to define bookmark-list
;;  bookmarks, which record a specific set of bookmarks and their sort
;;  order: to later choose given sets in different contexts for
;;  cycling.
;;  
;;
;;(@* "Cycling Dynamic Sets of Bookmarks")
;; *** "Cycling Dynamic Sets of Bookmarks" ***
;;
;;  The fact that the navlist is a static snapshot is a useful
;;  feature, but sometimes you might want to cycle among a particular
;;  dynamic set of bookmarks, that is, to have cycling take changes to
;;  the bookmark set into account automatically.  For that, Bookmark+
;;  provides separate cycling commands for most types of bookmark.
;;
;;  By default, these different kinds of cycling commands are not
;;  bound to any keys, with the exception of the commands for cycling
;;  the current buffer.  This exception includes cycling all bookmarks
;;  for the current buffer (see (@> "Cycling in the Current Buffer")
;;  and cycling only the highlighted bookmarks for the current buffer
;;  (see (@> "Using Highlighted Bookmarks")).  Keys `C-x p down' and
;;  `C-x p C-down' are defined for these two kinds of current-buffer
;;  cycling.
;;
;;  If you often want to cycle among the bookmarks of some other
;;  particular kind (e.g. only the autonamed bookmarks), then you can
;;  bind the relevant commands
;;  (e.g. `bmkp-next-autonamed-bookmark-repeat',
;;  `bmkp-previous-autonamed-bookmark-repeat') to handy keys.
;;  Otherwise, you can just use the cycling commands without binding
;;  them.
;;
;;
;;(@* "Cycling in the Current Buffer")
;; *** "Cycling in the Current Buffer" ***
;;
;;  You can navigate the bookmarks in the current buffer by cycling as
;;  well as jumping.  It is convenient to have dedicated keys for
;;  this, separate from the keys to cycle the navigation list.  The
;;  following keys are defined, corresponding to commands
;;  `bmkp-next-bookmark-this-buffer-repeat' and
;;  `bmkp-previous-bookmark-this-buffer-repeat':
;;
;;  Next:     `C-x p n', `C-x p C-n', `C-x p down'
;;  Previous: `C-x p p', `C-x p C-p', `C-x p up'
;;
;;  Starting with Emacs 23.3 (Emacs fix for bug #6256), you can also
;;  use the mouse wheel to cycle: `C-x p' then just rotate the wheel.
;;
;;  Again, you can bind any keys you want to these commands
;;  (e.g. `f2', `S-f2').  If you do not need to use a prefix key, then
;;  bind commands `bmkp-next-bookmark-this-buffer' and
;;  `bmkp-previous-bookmark-this-buffer' (no -repeat).
;;
;;  You can also cycle among just the highlighted bookmarks in the
;;  current buffer - see (@> "Using Highlighted Bookmarks").
;;
;;  Current-buffer cycling (all bookmarks or only the highlighted
;;  ones) is dynamic: the current set of bookmarks is cycled, not a
;;  static snapshot.  The navlist is automatically updated to the
;;  current dynamic set each time you cycle.  This is different from
;;  the usual cycling of the navlist, where it is taken as a static
;;  snapshot - see (@> "The Bookmark Navigation List").
;;
;;  By default, you cycle the current-buffer bookmarks in order of
;;  their positions in the buffer, top to bottom.  If you want a
;;  different order, you can customize option
;;  `bmkp-this-buffer-cycle-sort-comparer'.
;;
;;  Alternatively, you can use `C-x p .' to display the `*Bookmark
;;  List*' with only the current buffer's bookmarks, sort them there,
;;  and then use `C-x p B' to set the navigation list to `CURRENT
;;  *Bookmark List*'.  In that case, you use the navlist cycling keys
;;  (e.g. `C-x p f', not `C-x p n'), and the cycled set is a static
;;  snapshot.
;;
;;
;;(@* "Autonamed Bookmarks - Easy Come Easy Go")
;; *** "Autonamed Bookmarks - Easy Come Easy Go" ***
;;
;;  Sometimes it is convenient to quickly create and delete bookmarks
;;  whose names you don't really care about.  That is the purpose of
;;  "autonamed" bookmarks.  An autonamed bookmark has a simple name
;;  provided automatically, and it does not record any region
;;  information - it records only a position.  It is nevertheless an
;;  ordinary, persistent bookmark.
;;
;;  `C-x p RET' creates a bookmark at point without prompting you for
;;  the name.  It is named using the current buffer name preceded by
;;  the position in the buffer.  For example, the autonamed bookmark
;;  in buffer `foo.el' at position 58356 is `000058356 foo.el'.
;;
;;  (You can customize the format of autonamed bookmarks using options
;;  `bmkp-autoname-bookmark-function' and `bmkp-autoname-format'.)
;;
;;  When you jump to any bookmark, the actual destination can differ
;;  from the recorded position, because the buffer text might have
;;  changed.  In that case, the position you jump to has been
;;  automatically relocated using the recorded bookmark context (some
;;  buffer text surrounding the original position).
;;
;;  If option `bmkp-save-new-location-flag' is non-nil then, after
;;  jumping, the recorded position of the bookmark is automatically
;;  updated to reflect the new location jumped to.  This is true for
;;  any bookmark.
;;
;;  In the case of an autonamed bookmark, the bookmark name reflects
;;  the recorded position when you create it.  And when you jump to
;;  it, both the name and the recorded position are updated to reflect
;;  the jump destination.  So jumping to an autonamed bookmark keeps
;;  its persistent record in sync with the buffer location.
;;
;;  You will thus notice that the names of autonamed bookmarks can
;;  change as you visit them (e.g. cycling).  The bookmarks are
;;  automatically repositioned following their recorded contexts, and
;;  their names reflect that repositioning.
;;
;;  `C-x p RET' is `bmkp-toggle-autonamed-bookmark-set/delete', and it
;;  does double duty.  If an autonamed bookmark is under the cursor,
;;  then `C-x p RET' deletes it.  Easy creation, easy deletion.
;;  Because of this toggle behavior, there is at most one autonamed
;;  bookmark at any given buffer position.
;;
;;  `C-x p RET' has a third use: With a prefix argument, it prompts
;;  you to confirm the deletion of *all* autonamed bookmarks for the
;;  current buffer.
;;
;;  (You can also use `C-x p delete' (that's the `delete' key), bound
;;  to `bmkp-delete-bookmarks', to delete individual bookmarks under
;;  the cursor or all bookmarks in the buffer.  This is not limited to
;;  autonamed bookmarks.)
;;
;;  In addition to `C-x p RET', you can create autonamed bookmarks
;;  using these commands:
;;
;;  * `bmkp-set-autonamed-bookmark-at-line' - At a line beginning
;;  * `bmkp-set-autonamed-regexp-buffer'    - At buffer matches
;;  * `bmkp-set-autonamed-regexp-region'    - At region matches
;;  * `bmkp-occur-create-autonamed-bookmarks' (`C-c b' in *Occur*) -
;;    At `occur' and `multi-occur' hits
;;
;;  Autonamed bookmarks are normal bookmarks.  In particular, they are
;;  persisted.  If you do not care to persist them, you can ensure
;;  that they are automatically deleted by adding
;;  `bmkp-delete-autonamed-this-buffer-no-confirm' to
;;  `kill-buffer-hook' and `bmkp-delete-autonamed-no-confirm' to
;;  `kill-emacs-hook':
;;
;;    (add-hook 'kill-buffer-hook
;;              'bmkp-delete-autonamed-this-buffer-no-confirm)
;;    (add-hook 'kill-emacs-hook
;;              'bmkp-delete-autonamed-no-confirm)
 
;;(@* "Highlighting Bookmark Locations")
;;  ** Highlighting Bookmark Locations **
;;
;;  You can highlight the location (destination) of a bookmark.  For
;;  this feature you need library `bookmark+-lit.el' in addition to
;;  the other Bookmark+ libraries.
;;
;;  You might never want to highlight a bookmark, or you might want to
;;  highlight most or even all bookmarks, or your use of highlighting
;;  might fall somewhere between.  It depends on what kind of
;;  bookmarks you have and how you use them.  Bookmark+ lets you
;;  choose.  By default, no bookmarks are highlighted.
 
;;(@* "Defining How to Highlight")
;;  ** Defining How to Highlight **
;;
;;  By default, autonamed bookmarks are highlighted differently from
;;  non-autonamed bookmarks.  Bookmark highlighting uses a style and a
;;  face.  The available styles are these:
;;
;;  * Line                - Highlight line of the bookmark position
;;  * Position            - Highlight character at bookmark position
;;  * Line Beginning      - Highlight first character on line
;;  * Left Fringe         - Highlight only the left fringe
;;  * Left Fringe + Line  - Highlight the left fringe and the line
;;  * Right Fringe        - Highlight only the right fringe
;;  * Right Fringe + Line - Highlight the right fringe and the line
;;
;;  You can customize the default styles and faces to use for
;;  autonamed and non-autonamed bookmarks.  You can also customize the
;;  fringe bitmaps to use.
;;
;;  * `bmkp-light-autonamed'           (face)
;;  * `bmkp-light-non-autonamed'       (face)
;;  * `bmkp-light-style-autonamed'     (option)
;;  * `bmkp-light-style-non-autonamed' (option)
;;  * `bmkp-light-left-fringe-bitmap'  (option)
;;  * `bmkp-light-right-fringe-bitmap' (option)
;;
;;  In addition to the default highlighting, which you can customize,
;;  you can set the highlighting for individual bookmarks and
;;  particular sets of bookmarks (overriding their default
;;  highlighting).  These individual settings are saved as part of the
;;  bookmarks themselves.
;;
;;  In the bookmark list (buffer `*Bookmark List*'):
;;
;;  * `H +'    - Set the highlighting for this line's bookmark
;;  * `H > +'  - Set the highlighting for the marked bookmarks
;;
;;  Globally, you can use `M-x bmkp-set-lighting-for-bookmark' to set
;;  the highlighting for a given bookmark.
;;
;;  Each of these commands prompts you (with completion) for the style
;;  and face to set, as well as for a condition that controls whether
;;  to highlight.  Each of these is optional - just hit `RET' (empty
;;  input) at its prompt to skip setting it.
;;
;;  The condition is an Emacs-Lisp sexp that is evaluated whenever an
;;  attempt is made to highlight the bookmark.  Any resulting value
;;  except `:no-light' highlights the bookmark.  The sexp can refer to
;;  the variables `this-bookmark' and `this-bookmark-name', whose
;;  values are the bookmark to be highlighted and its name,
;;  respectively.
;;
;;  So, for example, if you wanted to be prompted each time before
;;  highlighting a certain bookmark you might set its highlighting
;;  condition to a sexp such as this:
;;
;;  (or (y-or-n-p (format "Highlight `%s' " this-bookmark-name))
;;      :no-light)
;;
;;  If you hit `n' at the prompt then `:no-light' is returned and the
;;  bookmark is not highlighted.
;;
;;  In the bookmark-list display, a pink-background, one-character
;;  highlight is used next to each bookmark that has a highlight
;;  override wrt the default.  You can see what that override setting
;;  is by using `C-u C-h RET' - look for the `lighting' entry in the
;;  bookmark definition.
;;
;;
;;(@* "Highlighting On Demand")
;;  *** Highlighting On Demand ***
;;
;;  You can highlight or unhighlight a bookmark or a set of bookmarks
;;  on demand.
;;
;;  In the bookmark list (buffer `*Bookmark List*'):
;;
;;  * `H H',   `H U'   - Highlight, unhighlight this line's bookmark
;;
;;  * `H > H', `H > U' - Highlight, unhighlight the marked bookmarks
;;
;;  Globally:
;;
;;  * `C-x p C-u'          - Unhighlight a highlighted bookmark at
;;                           point or on the same line (in that order)
;;
;;  * `C-x p h', `C-x p u' - Highlight, unhighlight a bookmark in the
;;                           current buffer (with completion).
;;
;;  * `C-x p H', `C-x p U' - Highlight, unhighlight bookmarks:
;;
;;                           With plain `C-u': all bookmarks
;;
;;                           With `C-u C-u': navigation-list bookmarks
;;
;;                           Otherwise, bookmarks in current buffer:
;;                            No prefix arg:  all bookmarks
;;                            Prefix arg > 0: autonamed bookmarks
;;                                       < 0: non-autonamed bookmarks
;;
;;  The default bookmark for `C-x p u' is the same bookmark that is
;;  unhighlighted by `C-x p C-u': a (highlighted) bookmark at point
;;  (preferably) or on the same line.  The latter key binding just
;;  saves you having to hit `RET' to pick the default.
;;
;;  When you use `C-x p h', you can use a prefix argument to override
;;  both the default highlighting and any highlighting that is
;;  recorded for the bookmark itself.  You are prompted for the style
;;  or face to use:
;;
;;  * Negative arg:     prompted for style
;;  * Non-negative arg: prompted for face
;;  * Plain `C-u':      prompted for style and face
;;
;;
;;(@* "Highlighting Automatically")
;;  *** Highlighting Automatically ***
;;
;;  You can also highlight automatically, whenever you set (create) a
;;  bookmark or jump to one.  This is controlled by these options:
;;
;;  * `bmkp-auto-light-when-set'
;;  * `bmkp-auto-light-when-jump'
;;
;;  You can choose any of these values for either option:
;;
;;  * Autonamed bookmark
;;  * Non-autonamed bookmark
;;  * Any bookmark
;;  * Autonamed bookmarks in buffer
;;  * Non-autonamed bookmarks in buffer
;;  * All bookmarks in buffer
;;  * None (no automatic highlighting) - the default
;;
;;  The first three values highlight only the bookmark being set or
;;  jumped to.
 
;;(@* "Using Highlighted Bookmarks")
;;  ** Using Highlighted Bookmarks **
;;
;;  Once you have highlighted bookmarks, what can you do with them?
;;  Obviously, the highlighting can help you distinguish and find
;;  bookmarks visually.  But highlighting also serves as yet another
;;  way to define sets: the highlighted vs unhighlighted bookmarks.
;;
;;  Any command that operates on a set of bookmarks can be applied to
;;  one or the other of these two sets.  Bookmark+ defines only a few
;;  such operations, but you can easily define others.
;;
;;  In addition to such specific commands, you can also apply general
;;  operations to the highlighted or unhighlighted bookmarks, using
;;  the bookmark-list display (`*Bookmark List*').  `H S' shows only
;;  the bookmarks that are currently highlighted, and `H M' marks
;;  them.  You can then perform any of the available bookmark-list
;;  operations on them.
;;
;;  Globally, you can use these keys:
;;
;;  * `C-x p ='                    - List the bookmarks that are
;;                                   highlighted at point.  With a
;;                                   prefix arg, show the full data.
;;
;;  * `C-x j h', `C-x 4 j h'       - Jump to a highlighted bookmark.
;;                                   Only highlighted bookmarks are
;;                                   completion candidates.
;;
;;  * `C-x p C-down', `C-x p C-up' - Cycle to the next and previous
;;                                   highlighted bookmark.
 
;;(@* "Use Bookmark+ with Icicles")
;;  ** Use Bookmark+ with Icicles **
;;
;;  Icicles (http://www.emacswiki.org/cgi-bin/wiki/Icicles) enhances
;;  your use of Bookmark+ in several ways.
;;
;;  When jumping to a bookmark, you can narrow the completion
;;  candidates to bookmarks of a particular type (e.g. Info, using
;;  `C-M-i'; remote, using `C-M-@'; region, using `C-M-r').  You can
;;  narrow again (and again), to another bookmark type, to get the
;;  intersection (e.g. remote Info bookmarks that define a region).
;;
;;  You can also narrow against different bookmark-name patterns
;;  (e.g. regexps) - so-called "progressive completion".  And take the
;;  complement (e.g., bookmarks whose names do not match
;;  `foo.*2010.*bar').  (This is not special to bookmarks; it is
;;  standard Icicles practice.)
;;
;;  In Icicle mode, several of the Bookmark+ keys are remapped to
;;  corresponding Icicles multi-commands.  A bookmark jump key thus
;;  becomes a bookmarks browser.  For example, `C-x j d' browses among
;;  any number of Dired bookmarks.
;;
;;  A single key can set a bookmark or visit bookmarks.  This key is
;;  whatever command `bookmark-set' would normally be bound to -
;;  e.g. `C-x r m'.  A prefix arg controls what it does.  If negative
;;  (`M--'), jump to (browse) bookmarks.  Otherwise, set a bookmark,
;;  as follows:
;;
;;  * Numeric prefix arg (non-negative): No prompt.  Use the buffer
;;    name plus the text of the region (if active) or the current line
;;    as the bookmark name.  Quickest way to set a bookmark.
;;
;;  * No prefix arg (as usual): Prompt for bookmark name.  But if the
;;    region is active, use the buffer name plus the region text as
;;    the default name.
;;
;;  * Plain `C-u' (as usual): Prompt for name; no bookmark overwrite.
;;
;;  During completion of a bookmark name, many features of the
;;  bookmark-list display (see (@> "The Bookmark List (Display)")) are
;;  available on the fly.  Buffer `*Completions*' acts like a dynamic
;;  version of `*Bookmark List*':
;;
;;  * Candidates are highlighted in the `*Completions*' window
;;    according to their bookmark type.
;;
;;  * Candidates are Icicles multi-completions with up to three parts:
;;
;;     a. the bookmark name
;;     b. the bookmark file or buffer name
;;     c. any tags
;;
;;    You can match any or all of the parts.  For example, you can
;;    match bookmarks that have tags by typing this regexp:
;;
;;    C-M-j . * C-M-j S-TAB
;;
;;    Each `C-M-j' inserts `^G\n', which is `icicle-list-join-string',
;;    the string used to join the parts.  This regexp says, "match the
;;    completion candidates that have all three parts (two join
;;    strings)", hence some tags.
;;
;;    You can turn off the use of multi-completion candidates for
;;    subsequent commands, so only bookmark names are used, by hitting
;;    `M-m' in the minibuffer.  You can think of this as similar to
;;    using `M-t' in `*Bookmark List*' to toggle showing file names.
;;    You can make not showing files and tags the default behavior by
;;    customizing `icicle-show-multi-completion-flag'.
;;
;;  * You can sort completion candidates using the Bookmark+ sort
;;    orders.  Use `C-,' to cycle among sort orders.
;;
;;  * You can use Icicles candidate-help keys (`C-M-RET', `C-M-down',
;;    etc.) to get detailed information about the current bookmark
;;    candidate.  `C-u C-M-RET' shows the complete, internal info
;;    defining the bookmark.  And without doing anything, summary info
;;    about the current candidate is available in the mode line of
;;    buffer `*Completions*'.
;;
;;  * You can use Icicles candidate-action keys (`C-RET', `C-mouse-2',
;;    `C-down', etc.) to visit any number of bookmarks.  For example,
;;    holding down `C-down' cycles among the current bookmark
;;    candidates, opening each in turn.
;;
;;  * You can use `S-delete' to delete the bookmark named by the
;;    current candidate.  You can delete any number of bookmarks this
;;    way, during a single invocation of a bookmark command.
;;
;;  * You can define Icicles sets of bookmarks, persistent or not, and
;;    act on their members in various ways.
 
;;(@* "If you use Emacs 20 and Also a More Recent Version")
;;  ** If you use Emacs 20 and Also a More Recent Version **
;;
;;  This section pertains to you *ONLY* in the rare case that you use
;;  both Emacs 20 and a later version, and you share the same bookmark
;;  file or bookmark-list display state file between the versions.
;;
;;  By default starting with Emacs 21, Bookmark+ uses bookmark names
;;  that are propertized with the full bookmark information, in order
;;  to let you use multiple bookmarks with the same bookmark name.  An
;;  example of this is having two autofile bookmarks for files with
;;  the same name in different directories.
;;
;;  When you save the bookmark list (`bookmark-alist') or a full
;;  snapshot of the bookmark-list display state (e.g., using command
;;  `bmkp-bmenu-define-full-snapshot-command'), these propertized
;;  names are saved.
;;
;;  However, Emacs 20 cannot read a serialized version of the bookmark
;;  list if it has such propertized names (the property value is a
;;  list that contains the propertized string, hence circular) - it
;;  will raise a read error.  To avoid this, when Bookmark+ in Emacs
;;  20 saves bookmarks or a full snapshot of the bookmark-list display
;;  state, it unpropertizes the bookmark names.  You can read the
;;  resulting files in any Emacs version.
;;
;;  But if you happen to save bookmark information using a later
;;  version of Emacs (e.g. Emacs 23) and you then read that recorded
;;  state using Emacs 20, the read will fail.  If this happens then
;;  you will need to re-save the affected file(s) using a later Emacs
;;  version. In the later Emacs version:
;;
;;  1. `M-x set-variable bmkp-propertize-bookmark-names-flag nil',
;;     to stop using propertized bookmark names.
;;  2. `C-x r l' to display the bookmark list.
;;  3. `g', to refresh the display.
;;  4. `S' to save the bookmark list.
;;  5. `M-x bmkp-save-menu-list-state', to save the display state.
;;
;;  You will now be able to use your bookmarks in Emacs 20 again.
;;
;;  If you will often be going back and forth between Emacs 20 and a
;;  later version, then you may prefer to simply turn off the use of
;;  propertized bookmark names, to avoid the hassle mentioned above.
;;  You can do that by customizing user option
;;  `bmkp-propertize-bookmark-names-flag' to nil.
;;
;;  Be aware, however, that if you do that you will not be able to
;;  take full advantage of Bookmark+ features such as autofile
;;  bookmarks, which require the ability to have multiple bookmarks
;;  with the same name.  See (@> "Autofile Bookmarks").
 
;;(@* "Bookmark Compatibility with Vanilla Emacs (`bookmark.el')")
;;  ** Bookmark Compatibility with Vanilla Emacs (`bookmark.el') **
;;
;;  Bookmark+ is generally compatible with GNU Emacs versions 20
;;  through 23.
;;
;;  1. All bookmarks created using any version of vanilla Emacs
;;     (library `bookmark.el') continue to work with Bookmark+.
;;
;;  2. All bookmarks created using Bookmark+ will work with all Emacs
;;     versions (20-23), provided you use Bookmark+ to access them.
;;
;;  3. Most bookmarks created using Bookmark+ will not interfere with
;;     the behavior of vanilla Emacs, versions 21-23.  The new
;;     bookmark types are simply ignored by vanilla Emacs.  For
;;     example:
;;
;;     - A bookmark with a region is treated like a simple position
;;       bookmark: the destination is the region start position.
;;
;;     - A Gnus bookmark does not work; it is simply ignored.
;;
;;     However, there are two cases in which Bookmark+ bookmarks will
;;     raise an error in vanilla Emacs:
;;
;;     * You cannot use non-file (e.g. buffer-only) bookmarks with any
;;       version of vanilla Emacs.
;;
;;     * You cannot use any bookmarks created using Bookmark+ with
;;       vanilla Emacs 20.
;;
;;     The Emacs bookmark data structure has changed from version to
;;     version.  Bookmark+ always creates bookmarks that have the most
;;     recent structure (Emacs 23).  As is the case for any bookmarks
;;     that have the Emacs 23 structure, these bookmarks will not work
;;     in vanilla Emacs 20 (that is, without Bookmark+).
;;
;;  Bottom line: Use `bookmark+.el' to access bookmarks created using
;;  `bookmark+.el'.
 
;;(@* "New Bookmark Structure")
;;  ** New Bookmark Structure **
;;
;;  The bookmark data structure, variable `bookmark-alist', has been
;;  enhanced to support new bookmark types.  For a description of this
;;  enhanced structure, use `C-h v bookmark-alist'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;; You need not load this file.  It contains only documentation.

(provide 'bookmark+-doc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bookmark+-doc.el ends here

