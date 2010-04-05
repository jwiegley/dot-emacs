;;; crypt++.el -- handle all sorts of compressed and encrypted files
;;; (may also be installed as crypt.el)

;; Authors: Lawrence R. Dodd <dodd@roebling.poly.edu>
;;	Rod Whitby <rwhitby@research.canon.oz.au>
;;	Kyle E. Jones <kyle@uunet.uu.net>
;; Maintainer: <karl@gnu.org>
;; Created: crypt.el in 1988, crypt++.el on 18 Jan 1993.
;; Version: 2.92
;; Keywords: extensions
;; $Id: crypt++.el,v 1.31 2003/01/17 18:52:17 karl Exp $

;;; Copyright (C) 1998, 1999, 2000, 2001, 2003 Free Software Foundation, Inc.
;;; Copyright (C) 1994 Lawrence R. Dodd
;;; Copyright (C) 1993 Lawrence R. Dodd and Rod Whitby
;;; Copyright (C) 1988, 1989, 1990 Kyle E. Jones
;;;
;;; This program is free software; you can redistribute it and/or modify
;;; it under the terms of the GNU General Public License as published by
;;; the Free Software Foundation; either version 2 of the License, or
;;; (at your option) any later version.
;;;
;;; This program is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.
;;;
;;; You should have received a copy of the GNU General Public License
;;; along with this program; if not, write to the Free Software
;;; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Please see notes on INSTALLATION and USAGE on the pages below.

;;; LCD Archive Entry:
;;; crypt++|Rod Whitby and Lawrence R. Dodd|karl@gnu.org|
;;; Handle compressed and encrypted files.|
;;; 2003-01-17|2.92|~/misc/crypt++.el.Z|

;;; AVAILABLE:
;;; http://www.cs.umb.edu/~karl/crypt++/
;;; news:gnu.emacs.sources

;;; BUG REPORTS:
;;; Type M-x crypt-submit-report to generate a bug report template or put your
;;; cursor at the end of this line and type C-x C-e: (crypt-submit-report)
;;;
;;; Please note that this bug-report facility (crypt-submit-report) uses
;;; Barry Warsaw's reporter.el which is part of GNU Emacs v19 and
;;; bundled with many other packages.  If needed, you can obtain a copy
;;; of reporter.el at the elisp-archive.  In fact, crypt-submit-report
;;; will attempt to ange-ftp a copy for you if you do not
;;; have one accessible.
;;;
;;; Main author:
;;; Lawrence R. Dodd
;;; Polytechnic University
;;; Brooklyn, New York USA


;;; INSTALLATION:
;;;
;;; To use this package, simply put it in a file called "crypt++.el" in a Lisp
;;; directory known to Emacs (see `load-path'), byte-compile it (ignore
;;; warnings about undefined functions), and put the line:
;;;
;;;    (require 'crypt++)
;;;
;;; in your ~/.emacs file or in the file default.el in the ../lisp directory
;;; of the Emacs distribution.
;;;
;;; For reliable operation with Emacs versions with coding system
;;; support, you also need:
;;;
;;;    (modify-coding-system-alist 'file "\\.bz\\'" 'no-conversion)
;;;    (modify-coding-system-alist 'file "\\.bz2\\'" 'no-conversion)
;;;    (modify-coding-system-alist 'file "\\.gpg\\'" 'no-conversion)
;;;    (modify-coding-system-alist 'file "\\.gz\\'" 'no-conversion)
;;;    (modify-coding-system-alist 'file "\\.Z\\'" 'no-conversion)
;;;
;;; With XEmacs, you need 'no-conversion-unix instead of 'no-conversion.
;;; (Thanks to Jose M. Vidal <vidal@sc.edu>.)
;;;
;;; Otherwise, Emacs tampers with the bytes before crypt++ gets them.
;;; The above won't help for files without those extensions.  You just
;;; have to specify the no-conversion coding system manually when
;;; visiting those files, or set no-conversion for all files if that suits you.
;;;
;;; Do not bother trying to autoload this package; it uses find-file and
;;; write-file hooks and thus should be loaded the first time you visit
;;; any sort of file.  Any package loaded after this one that appends
;;; something to `write-file-hooks' will not be executed because this
;;; package writes out the file.  Other packages that append to
;;; `write-file-hooks' should either be modified to prepend to that hook
;;; or be loaded before this one (preferably the former).
;;;
;;; An alternative is to stick (require 'crypt) in your ~/.emacs, if it is not
;;; already there, and then make a symbolic link from crypt++.el to crypt.el
;;; with "ln -s crypt++.el crypt.el".  This will make crypt++ act like a
;;; drop-in replacement for the original crypt since any package requiring
;;; crypt will find crypt++ instead.

;;; NOTE: encryption users should set `crypt-encryption-type' to one of the
;;; values in `crypt-encryption-alist' (see USAGE below).

;;; SPECIAL NOTES:
;;;
;;; If crypt++ is dumped with the emacs executable, or if it has already been
;;; loaded in an emacs session, then modifying the variables used in building
;;; the encryption and encoding tables will have no effect until these tables
;;; are rebuilt.  This may be done with `M-x crypt-rebuild-tables'.  See USAGE
;;; below to determine variables for which this is needed.  For example,
;;; post-load changes to `crypt-encryption-file-extension' or
;;; `crypt-freeze-vs-fortran' can be incorporated into the encryption table
;;; via `M-x crypt-rebuild-tables'.  Similarly, post-load changes to
;;; `crypt-bind-insert-file' are handled with `M-x crypt-bind-insert-file'.

;;; DUMPING CRYPT++ WITH GNU EMACS 18:
;;;
;;; If crypt++ has been dumped with emacs then calls to `crypt-rebuild-tables'
;;; and `crypt-bind-insert-file' will be needed in the user's ~/.emacs or
;;; ../lisp/default.el file in order to assure the changes take effect.  For
;;; example,
;;;
;;;           ;; Set my own preferences...
;;;           (setq crypt-encryption-type 'des
;;;                 crypt-encryption-file-extension "\\(\\.e\\)$"
;;;                 crypt-bind-insert-file nil
;;;                 crypt-freeze-vs-fortran nil)
;;;
;;;           ;; Has crypt++ been loaded already?
;;;           (if (featurep 'crypt++)
;;;
;;;               ;; Yes.  Just rebuild the encryption and encoding tables
;;;               ;; and key binding.
;;;               (progn
;;;                 (crypt-rebuild-tables)
;;;                 (crypt-bind-insert-file))
;;;
;;;             ;; No.  Load the whole thing.
;;;             (require 'crypt++))
;;;
;;; This guarantees that the users preferences will be incorporated into
;;; crypt++ without having to reload all of crypt++.el to do it.
;;;
;;; In GNU Emacs 19 and Lucid Emacs 19.8 the execution of
;;; `crypt-rebuild-tables' and `crypt-bind-insert-file' is done automatically
;;; through `after-init-hook'.  So, for the above example, all that is needed
;;; is
;;;
;;;           ;; Set my own preferences...
;;;           (setq crypt-encryption-type 'des
;;;                 crypt-encryption-file-extension "\\(\\.e\\)$"
;;;                 crypt-bind-insert-file nil
;;;                 crypt-freeze-vs-fortran nil)
;;;
;;;           (require 'crypt++)
;;;
;;; There is an `after-init-hook' in Lucid Emacs v 19.8 but in early versions
;;; of Lucid Emacs it will use `term-setup-hook' instead.


;;; USAGE:
;;;
;;; By default, intended to be transparent.  User-defined variables
;;;
;;;     controlling ENCRYPTION are:
;;;        crypt-encryption-type
;;;        crypt-encryption-file-extension
;;;        crypt-never-ever-decrypt
;;;        crypt-auto-write-buffer-encrypted
;;;        crypt-confirm-password
;;;        crypt-encrypted-disable-auto-save
;;;        crypt-encryption-alist
;;;        crypt-pgp-pub-multirecipients
;;;
;;;     controlling ENCODING are:
;;;        crypt-auto-decode-buffer
;;;        crypt-auto-write-buffer
;;;        crypt-query-if-interactive
;;;        crypt-no-extension-implies-plain
;;;        crypt-freeze-vs-fortran
;;;        crypt-compact-vs-C++
;;;        crypt-ignored-filenames
;;;        crypt-default-encoding
;;;        crypt-encoded-disable-auto-save
;;;        crypt-encoding-alist
;;;
;;;     controlling file insertion are:
;;;        crypt-bind-insert-file
;;;        crypt-auto-decode-insert
;;;
;;; To find out more about these variables, load this file, put your cursor at
;;; the end of any of the variable names, and hit C-h v [RET].
;;;
;;; NOTE: encryption users should set `crypt-encryption-type' to one of the
;;; values in `crypt-encryption-alist'.
;;;
;;; Although rarely needed, the following may be called interactively:
;;;        (crypt-encoded-mode)
;;;        (crypt-encode-region)
;;;        (crypt-encrypted-mode)
;;;        (crypt-encrypt-region)
;;;        (crypt-set-encryption-key)
;;;        (crypt-rebuild-tables)
;;;        (crypt-insert-file)
;;;        (crypt-bind-insert-file)
;;;        (crypt-submit-report)
;;;        (crypt-pgp-pub-clear-recipients)
;;;
;;; To find out more about these functions, load this file, put your cursor
;;; inside any of the `()' of the above lines, and hit C-h f [RET].
;;;
;;; You may wish to use mailcrypt in conjunction with crypt++.
;;; http://mailcrypt.sourceforge.net/


;;; NOTES ON INTERFACES WITH OTHER PROGRAMS AND PACKAGES:
;;;
;;; GZIP: the environment variable GZIP of gzip can cause an error if it
;;; contains `--verbose' because standard output messages will be appended to
;;; gzip'ed files.  This corrupts the files.  The cleanest solution is to pass
;;; the `--quiet' switch in `crypt-encoding-alist' to override this.  Use gzip
;;; version 1.0.4 or higher from ftp://ftp.gnu.org/pub/gnu/gzip-*.tar.gz.
;;;
;;; TAR-MODE: works properly with version 1.28 (or higher) with v19 emacs.
;;;
;;; RMAIL and CHANGING MAJOR MODE (for v18 ONLY): in v18 emacs
;;; crypt++.el's buffer local variables are smashed whenever the major
;;; mode is changed of a buffer or whenever RMAIL is run on an encrypted
;;; and/or compressed file.  This screws things up.  No smashing occurs
;;; with v19 Emacs.  for v18 emacs Joe Wells' "kill-fix.el" is needed to
;;; prevent this.  Get a copy of kill-fix.el from
;;; archive.cis.ohio-state.edu, store it where emacs can find it, stick
;;; a "(require 'kill-fix)" anywhere in your ~/.emacs, and the problem
;;; will be fixed.
;;;
;;; LISPDIR: if you save this file as crypt++.el then the "(require 'crypt)"
;;; in lispdir.el needs to be replaced with "(require 'crypt++)"
;;; or the symbolic link suggested above can be used.


;;; DESCRIPTION:
;;;
;;; The basic purpose of this package of Lisp functions is to recognize
;;; automatically encrypted and encoded (i.e., compressed) files when they are
;;; first visited or written.  The BUFFER corresponding to the file is decoded
;;; and/or decrypted before it is presented to the user.  The file itself is
;;; unchanged on the disk.  When the buffer is subsequently saved to disk, a
;;; hook function re-encodes the buffer before the actual disk write takes
;;; place.
;;;
;;; This package recognizes all sorts of compressed files by a magic number at
;;; the beginning of these files but uses a heuristic to detect encrypted
;;; files.  If you are asked for an encryption key for a file that is in fact
;;; not encrypted, just hit RET and the file will be accepted as is, and the
;;; crypt minor mode will not be entered.
;;;
;;; Other types of encoding programs may be added to this package by using the
;;; variable `crypt-encoding-alist' which contains a table of encoding
;;; programs such as compress, gzip (GNU zip), freeze, and compact.
;;;
;;; This new extended version of crypt now monitors the filename extensions of
;;; buffers that are written out using write-file (C-x C-w).  If the filename
;;; extension matches one of the extensions listed in `crypt-encoding-alist,'
;;; then this package will write the file out using the corresponding encoding
;;; (compression) method. This is done whether or not the buffer originated
;;; from a previously encoded (compressed) file.
;;;
;;; Thus, if the user is editing a file that may or may not have been encoded
;;; originally (e.g., foobar.Z or foobar) and decides to write it to a
;;; different file (e.g., barfoo or barfoo.z or barfoo.C).  This package will
;;; examine the filename extension and write the buffer in plain format or an
;;; alternate encoding (compression) format by searching through the entries
;;; in the table of encoding methods `crypt-encoding-alist.'  This change in
;;; encoding state is done automatically if the variable
;;; `crypt-auto-write-buffer' is t otherwise the user is asked.


;;; TO DO/KNOWN BUGS/HELP WANTED/APPLY WITHIN:
;;;
;;; All users/hackers out there are strongly encouraged to pursue any of these
;;; matters further (especially those that concern encryption and decryption!).
;;; It is important to future programmers and modifiers of crypt++.el to know
;;; about its perceived limitations.  Since necessity drives invention, users
;;; who find any of the following features of crypt++.el annoying are asked to
;;; make suggestions and send patches (again, especially those that concern
;;; encryption and decryption!).
;;;
;;; * currently crypt++ assumes that if a file is both encrypted and encoded
;;;   (i.e., compressed) that the order in which it was done was encryption
;;;   first _then_ compression.  As has been pointed by many people compression
;;;   following encryption is useless since the encrypted file is basically
;;;   random.  On the other hand, many agree that doing encryption _following_
;;;   compression is better since it makes it harder to crack the encryption.
;;;   We would like to make the ordering of these two user-configurable or if
;;;   nothing else change the order.
;;;
;;;   Having read the above however, Francois Pinard <pinard@iro.umontreal.ca>
;;;   writes that encryption following compression may not be harder to crack
;;;   since "the fact that the first few uncrypted bytes are expected (the
;;;   compress signature) facilitates a serious attempt at uncrypting."
;;;   jwz agrees with Francois.
;;;
;;; * get write-region and append-to-file to handle encoded and encrypted
;;;   files.  There is an interesting low-level encoding package by Jay Adams
;;;   <jka@ece.cmu.edu> called jka-compr.el that might address some of these
;;;   issues.  We encourage hackers out there to come up with crypt++ versions
;;;   of write-region and append-to-file.  The difficulty is creating versions
;;;   that mimic the originals as closely as possible.
;;;
;;; * instead of using call-process-region (which can fail badly if the region
;;;   is large and there's not much room in /tmp), write the region to a temp
;;;   file (with a customisable location) and use call-process directly.
;;;
;;; * users have mentioned trouble using crypt++ and hilit simultaneously since
;;;   the functions in write-file-hook for both write the file to disk and
;;;   return t.  A possible solution is to have one of them write to a
;;;   scratch buffer instead of to disk and return nil and then allow the
;;;   other to do its work on the scratch buffer and write it to disk.  Thanks
;;;   to Wayne Folta <folta@cs.UMD.EDU> and Amir J Katz <amir@matis.ingr.com>.
;;;   It would be nice to have another way in emacs to have an
;;;   after-write-file-hook and a before-write-file-hook of some sort.
;;;   Lucid Emacs has an after-write-file-hook.  Recent versions of hilit19.el
;;;   do not automatically attach to `write-file-hooks' and return t.
;;;   However, the general problem of multiple packages returning t still
;;;   remains.  dos-mode.el and crypt++.el also conflict.
;;;
;;; * another possible source of trouble is with encryption (and encoding)
;;;   programs sticking verbose output into buffers prior to being written to
;;;   disk.  This was definitely occurring with gzip because of --verbose in
;;;   the GZIP environment variable and is solved/hidden with the --quiet
;;;   switch.  However, I suspect that some encryption problems out there are
;;;   capable of similar things so the user should be careful.
;;;
;;; * integrating crypt++ with a backgrounding package such as Olin Shivers'
;;;   `background.el' might be useful too.  thanks to Mark Borges
;;;   <mdb@noaacrd.Colorado.EDU> for suggesting this.
;;;
;;; * Performing M-x crypt-encode-buffer or M-x crypt-encrypt-buffer and then
;;;   saving the file would possibly cause errors.  It is better to toggle
;;;   `crypt-encoded-mode' (or `crypt-encrypted-mode') and simply save the
;;;   file.  It is for this reason that `crypt-encode-buffer' and
;;;   `crypt-encrypt-buffer' are not interactive.
;;;
;;; * use plists instead of alists replacing calls to `nth' with `get'
;;;
;;; * merge encryption code completely into encoding code making encryption
;;;   just a special case of encoding.


;;; Change log:
;;;
;;; 1.1 - original version of crypt.el
;;; 1.2 -
;;;   jwz: works with tar-mode.el
;;;   jwz: applied patch from piet, merged with Lawrence Dodd's gzip version
;;; 1.3 -
;;;   lrd: fixed compress-magic-regexp
;;; 1.4, 1.5, 1.6 -
;;;   lrd: write-file compresses or gzips based on file extension
;;; 2.1 -
;;;   lrd: merged with Rod Whitby's table-driven version (major upgrade)
;;; 2.2 -
;;;   rjw: Changed file name to crypt++.el, so archie and lispdir can find it.
;;; 2.3 -
;;;   rjw: Separated the hook additions and minor mode alist additions.
;;; 2.4 -
;;;   rjw: Fixed the interactive form for crypt-buffer.
;;; 2.5 -
;;;   lrd: doc mods, changed GNU free software notice (was out of date), added
;;;   anonymous ftp information
;;; 2.6 -
;;;   lrd: added back in definition of `buffer' in defun crypt-buffer caused
;;;   an error when trying to read encrypted file; modified check for minor
;;;   mode alist addition; added gzip magic number warning
;;; 2.7 - [posted to gnu.emacs.sources]
;;;   lrd: added `TO DO' and `KNOW BUGS' section to header
;;; 2.8 -
;;;   lrd: added note about updating to v 1.24 of tar-mode.el
;;;   Thanks to Mark Borges <mdb@noaacrd.Colorado.EDU>
;;; 2.9 -
;;;   lrd: moved query about `crypt-freeze-vs-fortran' out of defvar for
;;;   `crypt-encoding-alist,' an erroneous value of nil was being stuck into
;;;   alist when user set `crypt-freeze-vs-fortran' was nil, doc mod.
;;;   Thanks to Mark Borges <mdb@noaacrd.Colorado.EDU>
;;; 2.10 -
;;;   rjw: moved query about `crypt-freeze-vs-fortran' back into defvar for
;;;   `crypt-encoding-alist,' - used append to ignore the erroneous nil.
;;; 2.11 -
;;;   rjw: fixed a bug in my fix :-(
;;; 2.12 -
;;;   rjw: Defvar crypt-magic-regexp and crypt-magic-regexp-inverse and
;;;   allow either a regexp or an elisp expression.
;;;   Suggested by Franc,ois Pinard <pinard@iro.umontreal.ca>.
;;; 2.13 -
;;;   lrd: added in info on lispdir.el, doc mods and some puttering while
;;;   looking over rjw's v 2.12 mods.
;;; 2.14 -
;;;   lrd: doc mod - trivial huh? switched `compact' and  `gzip' in
;;;   `crypt-encoding-alist' - want gzip near top
;;; 2.15 -
;;;   lrd: added in LCD Archive Entry and modified comments on tar-mode.el
;;;   since the version at the elisp-archive now works with crypt++.el
;;; 2.16 -
;;;   lrd: provide `crypt' as well as `crypt++' allowing something like `ln -s
;;;   crypt++.el crypt.el' to be meaningful
;;;   Suggested (by|as) Per Abrahamsen <amanda@iesd.auc.dk>
;;; 2.17 -
;;;   lrd: clarified bug report procedure, added fancy pseudo-graphics, added
;;;   to the `TO DO' list, put RCS tags in LCD Archive entry
;;; 2.18 - [posted to gnu.emacs.sources]
;;;   lrd: included pointer to elisp archive in crypt-version description,
;;;   changed "Decode buffer %s? " to "Decode %s? " in crypt-find-file-hook
;;;   to be more general (mainly for crypt-insert-file)
;;; 2.19 -
;;;   rjw: Added the crypt-compact-vs-C++ switch to distinguish compacted and
;;;   C++ files.
;;; 2.20 -
;;;   lrd: (1) modified interactive form of crypt-buffer. (2) made search
;;;   case-insensitive in crypt-submit-report. (3) modified encoded-mode and
;;;   crypt-mode so that buffer-modified is not unconditionally set to nil
;;;   when the mode is not changed. Thanks to Gerd Hillebrand
;;;   <ggh@cs.brown.edu> for suggesting (2) and (3).
;;; 2.21 -
;;;   rjw: Added an entry to the TODO list about the hazards of using
;;;   call-process-region on a large region and not much room in /tmp
;;;   (David Carlisle <carlisle@computer-science.manchester.ac.uk>).
;;; 2.22 -
;;;   lrd: allow write-file-hooks to contain functions as well as lists.
;;;   Contributed by Ken Laprade <laprade@trantor.harris-atd.com>.
;;; 2.23 -
;;;   lrd: made crypt-submit-report list values of more user-defined variables
;;; 2.24 -
;;;   lrd: pass the -q switch to gzip to thwart the possibility of a --verbose
;;;   in the GZIP environment variable
;;; 2.25 -
;;;   lrd: added some more to the TO DO list, clarified some things, also
;;;   untabified the entire file (I got tired of the control I's)
;;; 2.26 -
;;;   lrd: use the long-named options for GNU zip (self-documenting)
;;; 2.27 -
;;;   lrd: included observation by Francois Pinard <pinard@iro.umontreal.ca>
;;;   and worked on text in TO DO/KNOWN BUGS list
;;; 2.28 -
;;;   lrd: added two new variables in (crypt-submit-report) to the list stuck
;;;   at the bottom of the mail message; changed the comments regarding the
;;;   user-defined variables.  added in default values in user defined
;;;   variables.  added to and removed stuff to the `TO DO' list.
;;;
;;;   (encoded-mode):
;;;   added in code to remove any auto-save-files that may have been formed
;;;   before becoming an encoded buffer (for example a plain file saved to
;;;   disk encoded had orphan auto-save-files left behind).  turning off
;;;   auto-save-mode disables the creation of auto-save-files, but it also
;;;   disables the possibility of these being removed when the buffer is
;;;   saved.
;;;
;;;   (crypt-region):
;;;   now call the encryption and decryption program directly instead of
;;;   through the shell.  this is more secure since the shell will expose the
;;;   password (key).  thanks to Jon Cargille <jcargill@cs.wisc.edu>.  defined
;;;   two new variables `crypt-decryption-args' and `crypt-encryption-args' to
;;;   take the arguments separately.  removed (let ((opoint)...)) construct
;;;   this was a throw back to some old dead code and was not being used.
;;; 2.29 -
;;;   lrd: added three new variables in (crypt-submit-report); added to the
;;;   `TO DO' list.
;;;
;;;   (encode-region,encode-buffer,encoded-mode): fixed interactive forms -
;;;   the conversion to table version had eliminated some of the interactive
;;;   features of these.  thanks to Kimball Collins <kpc@ptolemy.arc.nasa.gov>
;;;   for point this out.  new interactive form uses functions
;;;   `crypt-get-encoding-type' and `crypt-symbol-alist-to-table' and variable
;;;   `crypt-default-encoding' to generate completion list of encoding types.
;;;
;;;   (crypt-write-file-hook): two new user-defined variables
;;;   `crypt-query-if-interactive' and `crypt-no-extension-implies-plain' and
;;;   the buffer-local variable `buffer-interactive-mode' are used to help
;;;   determined whether or not plain output is really desired for files
;;;   without a compression file-name extension.  the default behavior is the
;;;   same as before.
;;; 2.30 -
;;;   lrd: added test for user-defined variable `crypt-never-ever-decrypt'
;;;   when finding a file.  some users may never wish to decrypt files
;;;   and like to edit binary files.  thanks to Nelson Minar
;;;   <nelson@reed.edu>.  added to doc-strings of
;;;   `crypt-magic-regexp[-inverse]' -- these can be set to nil[t] and
;;;   accomplish the same thing as setting `crypt-never-ever-decrypt' to t
;;; 2.31 -
;;;   rjw: Updated the comments in the encryption check section.
;;; 2.32 - [posted to gnu.emacs.sources]
;;;   lrd: added warning about `crypt-(de|en)cryption-program'; doc mod.
;;; 2.33 -
;;;   lrd: if `crypt-(de|en)cryption-args' are nil then don't pass any
;;;   arguments to (de|en)cryption program, nil is the default instead of
;;;   "".  Thanks to Joe Ilacqua <spike@world.std.com>, David J. Schur
;;;   <djs@idm.com>, Peter Nuth <nuth@ai.mit.edu>, and Greg Larson
;;;   <glarson@bnr.ca>.  `-q' exists in gzip 1.0.3 but not `--quiet' changed
;;;   GZIP NOTE.  Thanks to Chris Moore <moore@src.bae.co.uk>.
;;; 2.34 -
;;;   lrd: allow `crypt-(de|en)cryption-args' to be a list of strings -- more
;;;   robust.  query for password (key), if none is set, when writing out file
;;;   for which `buffer-save-encrypted' is t.  Thanks to John Interrante
;;;   <interran@uluru.Stanford.EDU>.  (crypt-write-file-hook): check filename
;;;   extension against regexp `crypt-encryption-file-extension' and query for
;;;   encryption, unless `crypt-auto-write-buffer-encrypted' is t (don't
;;;   bother doing reverse check, encrypted to plain, not a common request).
;;;   (crypt-mode): delete auto-save files (cf., encoded-mode), may exist now.
;;;   (read-string-no-echo): applied patch from Piet van Oostrum
;;;   <piet@cs.ruu.nl> -- set `cursor-in-echo-area' _after_ setting buffer
;;;   (this was screwing up gnews).
;;; 2.35 -
;;;   lrd: doc mod
;;; 2.36 -
;;;   lrd: fixed typo, added RMAIL note.
;;; 2.37 - [posted to gnu.emacs.sources]
;;;   lrd:
;;;   (crypt-write-file-hook): search user-defined list
;;;   `crypt-ignored-filenames' for possible match with `buffer-filename'
;;;   before attempting conversion from compressed to plain format; useful for
;;;   compressed incoming mail files (e.g., RMAIL, INBOX).
;;;
;;;   (crypt-mode): query for key if not set already; need to switch order of
;;;   recovering key and toggling crypt-mode in crypt-find-file-hook (thanks
;;;   to Piet van Oostrum <piet@cs.ruu.nl>).
;;;
;;;   (crypt-buffer) and (encode-buffer): remove interactive form; use
;;;   (crypt-mode) and (encoded-mode) instead so encryption and compression
;;;   are done at the very end; leave interactive form in (crypt-region) and
;;;   (encode-region) may still be used.
;;;
;;;   (set-encryption-key): remove from `command-history' if called
;;;   interactively - thanks to George M. Georgiou
;;;   <georgiou@silicon.csci.csusb.edu>.
;;; 2.38 -
;;;   lrd: added `crypt-' prefix to `(read-string-no-echo)' and `(save-point)'
;;;   changed file extension for gzip files to `.z' _or_ `.gz' (future release
;;;   of gzip with use later extension by default and so this should be
;;;   changed to just `.gz' someday).
;;; 2.39 -
;;;   lrd: doc mod. added in patch from jwz - `(crypt-read-string-no-echo)' is
;;;   more secure, put property 'permanent-local on buffer-locals works for
;;;   Lucid Emacs and doesn't harm v18 emacs, change `buffer-interactive-mode'
;;;   to `buffer-interactive-encoded-mode.'
;;; 2.40 -
;;;   lrd: put property 'preserved in case kill-fix.el is being used.
;;; 2.41 -
;;;   lrd: all functions and variables now start with `crypt-', moved REVISION
;;;   HISTORY to bottom of header, interactive version of
;;;   `(crypt-encrypt-region)' clearer, `(crypt-read-string-no-echo)' now
;;;   echos `.'
;;; 2.42 -
;;;   lrd: (crypt-check-extension-for-encoding): broke out of
;;;   `(crypt-write-file-hook)'.  setting user variables
;;;   `crypt-compact-vs-C++' and `crypt-freeze-vs-fortran' to nil no longer
;;;   completely disables the reading compact'ed and frozen files but just
;;;   disables the use of the file-extension tricks of
;;;   `(crypt-check-extension-for-encoding).'  (crypt-encode-region): allow
;;;   for a single line message from encoding program at top of region; if it
;;;   is there, then remove it; kludge for `compact' program.
;;; 2.43 -
;;;   lrd: (crypt-encode-region): generalize the clean up procedure; add
;;;   element to `crypt-encoding-alist' and introduce new function
;;;   `(crypt-encoding-cleanup-regexp)' to extract a compression specific
;;;   regexp for erroneous message or lisp expression for cleanup.
;;; 2.44 -
;;;   lrd: new element for `crypt-encoding-alist' handles whether or not
;;;   file-name extension tricks may be play with encoding method; compact and
;;;   freeze values default to `crypt-compact-vs-C++' and
;;;   `crypt-freeze-vs-fortran' (thanks to rjw);
;;;   (crypt-encoding-extension-tricks): new defun to handle this;
;;;   (crypt-check-extension-for-encoding): monitors "tricks" entry of
;;;   `crypt-encoding-alist' and adjust the bag of tricks it can apply.
;;; 2.45 -
;;;   lrd: (crypt-encode-region): delete entire match of cleanup regexp by
;;;   requiring newlines in GARBAGE-REGEXP-OR-LISPEXP.  (crypt-submit-report):
;;;   use Warsaw's reporter.el.
;;; 2.46 -
;;;   lrd: (crypt-find-file-hook, crypt-write-file-hook): cleaned, documented,
;;;   and replaced occurrences of `(cond (C BODY))' with `(if C BODY)';
;;;   changed `crypt-magic-regexp' to `crypt-encryption-magic-regexp' and
;;;   `crypt-magic-regexp-inverse' to `crypt-encryption-magic-regexp-inverse'
;;;   for consistency with other variable names. new user-defined variable
;;;   `crypt-encryption-minor-mode-name' instead of always "Crypt".  grouped
;;;   all encryption variables together.
;;; 2.47 -
;;;   lrd: somewhat major change - put program-specific encryption variables
;;;   into a single table `crypt-encryption-alist' and let the variable
;;;   `crypt-encryption-type' define the appropriate entry to use; new
;;;   user-defined variable `crypt-confirm-password,' thanks to Jeff Clark
;;;   <jclark@src.honeywell.com>. (crypt-submit-report): improved error
;;;   handling, thanks to baw. (crypt-write-file-hook): fixed bug with
;;;   `crypt-encoding-extension-tricks'
;;; 2.48 -
;;;   lrd: added dummy argument to `crypt-encoding-alist' and
;;;   `crypt-encryption-alist' and merged all defuns that work on their
;;;   elements into defuns that all start with `crypt-get-' and look through
;;;   both lists.  simplifies some of code and closer to treating encryption
;;;   as a special case of encoding; crypt-minor-mode-alist: replaced (nth *)
;;;   with `(crypt-get-minor-mode)' call; (crypt-encode-region): allow
;;;   arguments to be list of strings; renamed (crypt-get-encoding-type) to
;;;   (crypt-read-encoding-type) for clarity.
;;; 2.49 - [posted to gnu.emacs.sources]
;;;   lrd: (crypt-encode-region): ignore `args' if set to t
;;; 2.50 -
;;;   lrd: (crypt-write-file-hook): in v19 we need to call `backup-buffer'
;;;   ourselves -- we write out the file and return t so `basic-save-buffer'
;;;   does not do it; also call `set-file-modes'
;;; 2.51 -
;;;   lrd: some `defvar's are now `defconst's and tar-mode note was changed.
;;; 2.52 -
;;;   lrd: make doc strings conform to GNU standards.
;;; 2.53 -
;;;   lrd: made header conform to GNU Conventional Headers standard.
;;; 2.54 -
;;;   lrd: `crypt-encryption-file-extension', `crypt-freeze-vs-fortran',
;;;   `crypt-compact-vs-C++', `crypt-encryption-magic-regexp', and
;;;   `crypt-encryption-magic-regexp-inverse' are used in defining the tables
;;;   `crypt-encoding-alist' and `crypt-encryption-alist' and so need to be set
;;;   _before_ loading crypt++.  use `add-hook' if it is available.
;;; 2.55 -
;;;   lrd: new interactive function `crypt-insert-file' mimics `insert-file'
;;;   but attempts to decode or decrypt before insertion; bound `C-x i' if
;;;   `crypt-bind-insert-file' is non-nil.  comment out doc-strings from
;;;   internal subroutines, saves space.
;;; 2.56 -
;;;   tfb: change the definitions of crypt-{encoding,encryption}-alist, to
;;;   call the functions crypt-make-{encoding,encryption}-alist resp.
;;;   Added crypt-reinit which regenerates these variables from their
;;;   functions, thus allowing this stuff to be preloaded even if people
;;;   set things in their init files.
;;;   Tim Bradshaw <tim.bradshaw@mid-heidelberg.de>
;;; 2.57 -
;;;   lrd: untabify; remove duplicate entry in `crypt-make-encoding-alist';
;;;   change name of `crypt-make-*-alist' to `crypt-build-*-alist' and
;;;   `crypt-reinit' to `crypt-rebuild-tables'; (crypt-read-string-no-echo):
;;;   change local variable `form' to `help-form' so it is defined;
;;;   `crypt-encryption-alist' and `crypt-encoding-alist' must be defined with
;;;   `defconst' since we wish crypt++ to initialize these variables
;;;   unconditionally; modify INSTALLATION section to reflect these changes.
;;; 2.58 -
;;;   lrd: doc mod.
;;; 2.59 - [posted to gnu.emacs.sources]
;;;   lrd: (crypt-bind-insert-file): new function for changing "C-x i" in
;;;   initialization file or interactively.
;;; 2.60 -
;;;   lrd: add `crypt-rebuild-tables' and `crypt-bind-insert-file' to
;;;   `after-init-hook' in GNU emacs v19 and to `term-setup-hook' in Lucid
;;;   emacs.  Change INSTALLATION notes.
;;; 2.61 - [posted to gnu.emacs.sources]
;;;   lrd: Doc mod.  Clean up the installation of minor mode indicators.
;;; 2.62 - [posted to gnu.emacs.sources]
;;;   lrd: installed patch from stig@hackvan.com to simplify crypt-get-* defuns
;;;   (now defmacros).  Don't add to `term-setup-hook' unless no
;;;   `after-init-hook' _and_ definitely running v19, otherwise Rod gets an
;;;   error at home :-<.  Don't assume C-x i had `insert-file' bound to it:
;;;   store old binding in `crypt-old-binding' before overwriting and use in
;;;   function `crypt-bind-insert-file.'
;;; 2.63 -
;;;   lrd: (crypt-encode-buffer, crypt-encode-region, crypt-encrypt-buffer,
;;;   crypt-encrypt-region): changed argument list putting optional buffer
;;;   last and making default action to encode or encrypt. (crypt-encoded-p,
;;;   crypt-encrypted-p): new functions that do the actual testing of file
;;;   contents.  (crypt-find-file): uses these new functions.
;;;   (crypt-rebuild-minor-modes-alist): new function to rebuild
;;;   `minor-mode-alist' called by function crypt-rebuild-tables.
;;;   (crypt-build-minor-mode-alist): new function called by
;;;   `crypt-minor-mode-alist' to create itself.  `crypt-minor-mode-encrypted'
;;;   removed because defined in function crypt-build-minor-mode-alist.
;;; 2.64 -
;;;   lrd: (crypt-find-file-hook): temporarily remove the encrytion file
;;;   extension to help determine the major mode, just like is done with the
;;;   encoding file extension.  In order for this to work properly the file
;;;   extension in `crypt-encryption-file-extension' and
;;;   `crypt-encryption-alist' needs to be inside a pair of \\( \\).
;;; 2.65 -
;;;   lrd: (crypt-find-file-hook): move determination of key, password, into
;;;   (crypt-encrypted-p).
;;; 2.66 -
;;;   lrd: (crypt-set-encryption-key): improve prompt string for encryption
;;;   key.
;;; 2.67 -
;;;   lrd: (crypt-write-file-hook): make check for encryption file-name
;;;   extension case-sensitive.
;;; 2.68 -
;;;   lrd: fixed check for previous addition to `minor-mode-alist' -- was not
;;;   working. Check for an `add-hook' function; if one does not exist then
;;;   use a copy of one from GNU Emacs 19.  When using `add-hook' to append to
;;;   the `write-file-hooks' make sure that the version accepts the optional
;;;   APPEND argument -- v19's does but the one in the elisp archive by Dan
;;;   LaLiberte <liberte@cs.uiuc.edu> does not append.  This causes problems.
;;;   Thanks to Francesco Potorti` <pot@fly.CNUCE.CNR.IT> for pointing this
;;;   out.
;;; 2.69 - [posted to gnu.emacs.sources]
;;;   lrd: doc mod with regards `after-init-hook' and Lucid Emacs.  Add
;;;   pointer to crypt++-fnf.el for people who might be interested.
;;; 2.70 -
;;;   lrd: narrow conditions under which crypt-encryption-magic-regexp
;;;   matches.  Thanks to Philippe Michel <michel@thomson-lcr.fr> and Francois
;;;   Pinard <pinard@iro.umontreal.ca> for helping explain this with regards
;;;   to ISO/Latin-1.
;;; 2.71 -
;;;   lrd: applied patches from Darrin Jewell <jewell@bdi.com> for DOS to UNIX
;;;   support.  DOS entry added to crypt-build-encoding-alist.
;;;   (crypt-dos-to-unix-region, crypt-unix-to-dos-region): New
;;;   functions. (crypt-dos-has-ctrl-z): New buffer-local variable.
;;;   (crypt-encode-region): allow for encoding and decoding programs to be
;;;   elisp expressions.  If they are then apply them directly to region.
;;;   Point out that crypt++.el conflicts with dos-mode.el.
;;; 2.72 -
;;;   lrd: The limit for the regular expression search done by
;;;   `crypt-encrypted-p' is extended to 100 by default.  The enlargement of
;;;   search field is needed because of previous reduction in size of regexp
;;;   being searched for.  (crypt-magic-search-limit): New variable defining
;;;   this new limit.  (crypt-encrypted-p): Uses it and cleaned up.  Doc mod.
;;;   Thanks to Philippe Michel <michel@thomson-lcr.fr>, Francois Pinard
;;;   <pinard@iro.umontreal.ca>, and Dave Goldberg <dsg@blackbird.mitre.org>.
;;; 2.73 - [posted to gnu.emacs.sources]
;;;   lrd: Apply patch from Kevin Rodgers <kevin@traffic.den.mmc.com> that
;;;   uses more verbose messages and capitals.  Doc mod.
;;; 2.74 -
;;;   lrd: Untabify.  (crypt-encrypted-p): Check value of
;;;   `crypt-never-ever-decrypt' before anything else.
;;; 2.75 -
;;;   lrd: (crypt-version): Remove call to `substring'.
;;; 2.76 -
;;;   lrd: (crypt-encryption-magic-regexp-inverse): Add in regexp that will
;;;   match ksh `.sh_history' files so that they are not interpreted as
;;;   encrypted files.  Thanks to Francesco Potorti` <pot@fly.CNUCE.CNR.IT>.
;;; 2.77 - [posted to gnu.emacs.sources]
;;;   lrd: (crypt-bind-insert-file): Use substitute-key-definition to bind
;;;   crypt-insert-file to whatever key insert-file is bound to (not
;;;   necessarily C-x i).  Call crypt-bind-insert-file directly in
;;;   file. Variable crypt-bind-insert-file: Doc mod.  Remove
;;;   crypt-old-binding.  Replace `M-x foobar' in doc strings with
;;;   `\\[foobar]'.
;;; 2.78 -
;;;   lrd: (crypt-auto-write-answer-local): New internal variable.  Holds
;;;   answer to query about file-extension tricks question per buffer.  Thanks
;;;   to George Forman <forman@cs.washington.edu>.  Remove Rod from list of
;;;   maintainers...he's busy enough.  Merge multiple setq forms into single
;;;   setq forms.
;;; 2.79 -
;;;   lrd: (crypt-y-or-n-p): New internal function for querying.  Tests the
;;;   internal variable crypt-auto-write-answer-local to ensure single query.
;;;   (crypt-check-extension-for-encoding): Replace all occurrences of queries
;;;   involving y-or-no-p constructs with crypt-y-or-n-p.
;;; 2.80 - [posted to gnu.emacs.sources]
;;;   lrd: (crypt-set-encryption-key): Shorten interactive prompt.  Change
;;;   documentation.
;;; 2.81 -
;;;   lrd: (crypt-variable-list): Add shell and path variables.
;;;   (crypt-confirm-password): Fix spelling error in doc.
;;; 2.82 -
;;;   lrd: Applied patch from Noah Friedman <friedman@prep.ai.mit.edu>.
;;;   (crypt-encoded-disable-auto-save, crypt-encrypted-disable-auto-save):
;;;   New user-defined variables. (crypt-encoded-mode, crypt-encrypted-mode):
;;;   Use them.
;;; 2.83 - 2feb98
;;;   kb: Changed occurrences of roebling.  Do (set-visited-file-name).
;;;   Incorporate patches from David Rosinger <dsrosing@ingr.com> for win32.
;;; 2.84 - 20mar98
;;;   kb: Applied XEmacs 2.83 patch by hniksic to add custom support.
;;;   Support .tgz as .tar.gz.
;;;   Add bzip support.
;;;   Merge pgp support from John Heidemann <johnh@isi.edu>,
;;;    http://www.isi.edu/~johnh/SOFTWARE/index.html.
;;;    Requires either mailcrypt or "PEM - PGP Enhanced Messaging for
;;;    GNU Emacs" from Roy Frederick Busdiecker, III (Rick).
;;;   Merge Mac support from Daniel M. German <dmg@csg.uwaterloo.ca>.
;;; 2.85 - 5jun98
;;;    cro@nca.asu.edu: Add support in pgp-pub for encrypting files with
;;;     multiple user's keys.  New variables: crypt-pgp-pub-multirecipients,
;;;     crypt-pgp-pub-recipients, crypt-pgp-pub-recipients-history.
;;;     This support is on by default.
;;;    nosuzuki@e-mail.ne.jp: defvar shell-command-switch.
;;;    knabe@cs.virginia.edu: crypt-pgp variable names.
;;; 2.86 - 17jan99
;;;    nmg97r@ecs.soton.ac.uk: Discard stderr from subprocesses instead
;;;    of inserting into the current buffer.
;;; 2.87 - 21apr99
;;;    add crypt-decode-{dos,mac}-p.
;;; 2.88 - 2jun00
;;;    kifer@cs.sunysb.edu: (coding-system-for-write 'no-conversion)
;;;    ryk@coho.net: (buffer-file-coding-system 'no-conversion)
;;;    johnh@isi.edu: mailcrypt & pgp/pgp5.0/gpg.
;;; 2.89 - 11may01
;;;    joerg@plate.cx (Joerg Plate): bzip != bzip2.
;;;    plord@hgmp.mrc.ac.uk (Phillip Lord) (crypt-file-write-hook):
;;;      (let inhibit-read-only t) so we can save with read-only properties.
;;;    cro@nca.asu.edu (Charles R. Oldham) (crypt-pgp-pub-encrypt-region):
;;;      typo, pgp used in gpg block.
;;;    hull@paracel.com (David Hull): gpg file support, also
;;;      set coding-system-for-read to 'no-conversion, fixes decryption
;;;      bug with files beginning with a blank line.
;;;    kb (crypt-encode-region): set coding-system-for-*.  This
;;;      backwards incompatibility sure has been painful.
;;; 2.90 - 19may01
;;;    kb: pattern for .elc files.
;;; 2.91 - 15nov01
;;;	forcer@debian.org (Jorgen Schaefer): mcrypt entry.
;;;	doc fixes from dmagda@magda.ca (David Magda)
;;;	  and vidal@sc.edu (Jose Vidal).
;;; 2.92 - 17jan03
;;;     kb: no more ftp.cs.umb.edu.
;;;	mernst@alum.mit.edu (Michael Ernst): rc4 encoding.


;;; Code:

;;;; User definable variables.
(defvar shell-command-switch "-c") ; in case it isn't defined yet.

(defvar crypt-encryption-type 'crypt
  "*Method of encryption.  Must be an element of `crypt-encryption-alist.'
If you change this after crypt++ is loaded then do \\[crypt-rebuild-tables].")

(defvar crypt-encryption-file-extension nil
  "*Regexp for extension of files encrypted with `crypt-encryption-type.'
Should be of the form \"\\\\(\\\\.foo\\\\)$\".  nil says use default values in
`crypt-encryption-alist.'  If you change this after crypt++ is loaded then do
\\[crypt-rebuild-tables].")

(defvar crypt-never-ever-decrypt nil
  "*t says never attempt to decrypt a buffer.")

(defvar crypt-auto-write-buffer-encrypted nil
  "*t says files with `crypt-encryption-alist' file extension auto-encrypted.
nil says query.  See `crypt-auto-write-buffer.'")

(defvar crypt-confirm-password nil
  "*t says confirm new passwords and when writing a newly encrypted buffer.")

(defvar crypt-encoded-disable-auto-save t
  "*If t, turn off auto-save-mode for buffers which are encoded.
If non-nil but not t, then no message is displayed.

The default is t is because there isn't any way to tell emacs to encode the
autosave file, so the autosave would be in a different format from the
original.  The disadvantage of turning off autosaves is that any work you
do in that buffer will be completely lost if the changes are not explicitly
saved.

It is probably best to set this variable to nil and use buffer-local
variables in files for which you don't actually care about autosaves.
Unencoded recovery data is better than none at all.")

(defvar crypt-encrypted-disable-auto-save t
  "*If t, turn off auto-save-mode for buffers which are encrypted.
If non-nil but not t, then no message is displayed.

The default is t is because there isn't any way to tell emacs to encrypt
the autosave file, so the autosave would be in cleartext form.  The
disadvantage of turning off autosaves is that any work you do in that
buffer will be completely lost if the changes are not explicitly saved.

You might consider setting this variable to nil and use buffer-local
variables in files for which security is more important than data
recovery.")

;;; ENCRYPTION

;;; Encrypted files have no magic number, so we have to hack a way of
;;; determining when a buffer should be decrypted.  we do this only buffers
;;; that match a MAGIC-REGEXP very close to beginning of buffer and that do
;;; _NOT_ match a MAGIC-REGEXP-INVERSE.
;;;
;;; Currently MAGIC-REGEXP matches non-ASCII characters and
;;; MAGIC-REGEXP-INVERSE will match Sun OS, 4.x BSD, and Ultrix executable
;;; magic numbers, so binaries can still be edited (heh) without headaches.

(defconst crypt-encryption-magic-regexp "[\000\200-\237]\\|^-----BEGIN PGP MESSAGE\\|^Salted__"
  "Regexp that must be found very close to beginning of encrypted buffer.
This is intended to be an internal variable \(not user-visible\).  If you
change this after crypt++ is loaded then do \\[crypt-rebuild-tables].")

(defconst crypt-encryption-magic-regexp-inverse
  "\\`\201\001\\|^\\(..\\)?\\([\007\010\013]\001\\|\001[\007\010\013]\\)\\|^From \\|^;ELC"
  "Regexp that must *not* be found very close to beginning of encrypted buffer.
This is intended to be an internal variable \(not user-visible\).  If you
change this after crypt++ is loaded then do \\[crypt-rebuild-tables].")

(defconst crypt-magic-search-limit 100
  "Limit of regular expression search used to recognize encrypted files.
Maximum position in file for presence of `crypt-encryption-magic-regexp' and
absence of `crypt-encryption-magic-regexp-inverse'.")

(defun crypt-build-encryption-alist ()
  ;; Returns the encryption alist
  (list
   ;; crypt
   (list 'crypt
	 crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	 (or crypt-encryption-file-extension "\\(\\.e\\)$")
	 "crypt" "crypt"
	 nil
	 nil
	 "Crypt"
	 nil
	 t
	 nil
	 )
   ;; DES (Cipher Block Chaining - CBC) [DES' default]
   (list 'des
	 crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	 (or crypt-encryption-file-extension "\\(\\.des\\)$")
	 "des" "des"
	 '("-e" "-k")
	 '("-d" "-k")
	 "DES-CBC"
	 nil
	 t
	 nil
	 )
   ;; DES (Electronic Code Book - ECB)
   (list 'des-ecb
	 crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	 (or crypt-encryption-file-extension "\\(\\.des\\)$")
	 "des" "des"
	 '("-e" "-b" "-k")
	 '("-d" "-b" "-k")
	 "DES-ECB"
	 nil
	 t
	 nil
	 )
   ;; PGP
   (list 'pgp
	 crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	 (or crypt-encryption-file-extension "\\(\\.pgp\\)$")
	 "pgp" "pgp"
	 '("+batchmode" "+verbose=0" "-c" "-f" "-z")
	 '("+batchmode" "+verbose=0" "-f" "-z")
	 "PGP"
	 nil
	 t
	 nil
	 )
   ;; PGP with public-key encryption
   (list 'pgp-pub
	 crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	 (or crypt-encryption-file-extension "\\(\\.pgp\\)$")
	 "pgp" "pgp"
	 nil
	 nil
	 "PGP-PUB"
	 nil
	 t
	 nil
	 )
   ;; GPG
   (list 'gpg
	 crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	 (or crypt-encryption-file-extension "\\(\\.gpg\\)$")
	 "gpg" "gpg"
	 '("--batch" "--quiet" "-c" "-o" "-" "--passphrase-fd" "0")
	 '("--batch" "--quiet" "-o" "-" "--passphrase-fd" "0")
	 "GPG"
	 nil
	 t
	 t
	 )
  (list 'mcrypt
	crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	(or crypt-encryption-file-extension "\\(\\.nc\\)$")
	"mcrypt" "mcrypt"
	'("-k")
	'("-d" "-k")
	"Rijndael-128"
	nil
	t
	nil
	)
  (list 'rc4
	crypt-encryption-magic-regexp crypt-encryption-magic-regexp-inverse
	(or crypt-encryption-file-extension "\\(\\.rc4\\)$")
	"openssl" "openssl"
	'("enc" "-rc4" "-e" "-k")
	'("enc" "-rc4" "-d" "-k")
	"RC4"
	nil
	t
	nil
	)
   ;; Add new elements here ...
   ))

(defconst crypt-encryption-alist (crypt-build-encryption-alist)
  "List of elements describing the encryption methods available.
each element looks like
	\(ENCRYPTION-TYPE
	  MAGIC-REGEXP MAGIC-REGEXP-INVERSE
	  FILE-EXTENSION
	  ENCRYPT-PROGRAM DECRYPT-PROGRAM
	  ENCRYPT-ARGS
	  DECRYPT-ARGS
	  MINOR-MODE
	  GARBAGE-REGEXP-OR-LISPEXP
	  FILE-EXTENSION-TRICKS
	  ENCRYPTION-KEY-STDIN
	 \)
ENCRYPTION-TYPE is a symbol denoting the encryption type.

MAGIC-REGEXP regexp that must match very close to the beginning of an
encrypted buffer.  This may also be some elisp expression to be evaluated at
\(point-min\) that will return t for an encrypted buffer.  If this is set to
nil then crypt++ will never try to decrypt a buffer.  Currently set to the
internal variable `crypt-encryption-magic-regexp' which will match non-ASCII
characters.

MAGIC-REGEXP-INVERSE regexp that must _NOT_ match very close to the beginning
of an encrypted buffer.  This may also be some elisp expression to be
evaluated at \(point-min\) that will return t for a NON-encrypted buffer.
If this is set to t then crypt++ will never try to decrypt a buffer.
Currently set to the internal variable `crypt-encryption-magic-regexp-inverse'
which will match Sun OS, 4.x BSD, and Ultrix executable magic numbers, so
binaries can still be edited (heh) without headaches.

FILE-EXTENSION regexp denoting the file extension usually appended the
filename of files encrypted with ENCRYPT-PROGRAM.  The variable
`crypt-encryption-file-extension' will over ride the default.

ENCRYPT-PROGRAM name of executable file to be used for encryption.

DECRYPT-PROGRAM name of executable file to be used for decryption.

ENCRYPT-ARGS arguments to be passed to ENCRYPT-PROGRAM may be a string or a
list of strings or nil.

DECRYPT-ARGS arguments to be passed to DECRYPT-PROGRAM may be a string or a
list of strings or nil.

MINOR-MODE string denoting the name for the encrypted minor mode as it will
appear in the mode line.

GARBAGE-REGEXP-OR-LISPEXP dummy variable for compatibility with encoding.

FILE-EXTENSION-TRICKS is t or nil depending on whether or not tricks
converting between different encryption types can be done based on
FILE-EXTENSION; typically t.

ENCRYPTION-KEY-STDIN is t if the encryption key should be passed to the
encryption program on stdin, or nil if it should be appended to the end
of the command line.  It is more secure to pass it on stdin.
")


;;; ENCODING

(defvar crypt-auto-decode-buffer t
  "*t says buffers visiting encoded files will be decoded automatically.
nil means to ask before doing the decoding.")

(defvar crypt-auto-write-buffer nil
  "*t says save files with `crypt-encoding-alist' file extensions as encoded.
nil says to ask before doing this encoding.  Similarly, buffers originating
from encoded files to be written to files not ending in `crypt-encoding-alist'
file extensions will be written in plain format automatically.  nil says to
ask before doing this decoding.")

;; This is an internal variable documented here and not in a DOCSTRING in
;; order to save memory.  If this variable's value has been changed from its
;; default, then it contains the answer to the question "Write out buffer
;; foobar using `compression-type'?".  This question is asked only if *plain*
;; buffer foobar is being written to disk *and* it has a provocative
;; `compression-type' file-name extension (see DOCSTRING for variable
;; crypt-auto-write-buffer).  The variable is local to all buffers with a
;; default value of 'ask so if the situation described above arises, then the
;; question is asked at least once, unless the user-defined variable
;; crypt-auto-write-buffer is non-nil.
(defvar crypt-auto-write-answer-local 'ask)
(make-variable-buffer-local 'crypt-auto-write-answer-local)
(setq-default crypt-auto-write-answer-local 'ask)
(put 'crypt-auto-write-answer-local 'permanent-local t) ; for v19 Emacs
(put 'crypt-auto-write-answer-local 'preserved t)       ; for kill-fix.el

(defvar crypt-query-if-interactive t
  "*t says ask when saving buffers where `crypt-encoded-mode' was toggled.
nil says that even if filename extension is plain (i.e., not listed in
`crypt-encoding-alist') buffer will be written in an encoded format without
asking.

This variable is designed for users that edit a plain file (with plain
extension) and then toggle `(crypt-encoded-mode)' and do not wish to be
queried every time that they save the buffer.

NOTE: if `(crypt-encoded-mode)' was not called interactively (the usual
scenario) then the value of this variable has no effect on how the buffer is
written to disk.  In such a case `crypt-no-extension-implies-plain' is then
the relevant variable.")

(defvar crypt-no-extension-implies-plain t
  "*t says file extensions not in `crypt-encoding-alist' may be written plain.
if `crypt-auto-write-buffer' is also t then any file ending in a plain
extension is written in plain format automatically, otherwise query user.

nil says user works with encoded (compressed) files without file extensions
and will not be queried each time they save these files.

NOTE: (1) this does not affect find-file (C-x C-f) since that works with a
magic regexp.  (2) there is no way to distinguish between write-file and
save-buffer so nil will mean that neither will query.")

(defvar crypt-freeze-vs-fortran t
  "*t says `.F' file extension denotes a frozen file not a Fortran file.
If you change this variable after crypt++ has been loaded then do
\\[crypt-rebuild-tables].")

(defvar crypt-compact-vs-C++ nil
  "*t says `.C' file extension denotes a compacted file not a C++ file.
If you change this variable after crypt++ has been loaded then do
\\[crypt-rebuild-tables].")

(defvar crypt-ignored-filenames nil
  "*List of regexp filenames for which encoded to plain conversion is not done.
A filename with a plain extension, in encoded format, that is matched by one of
these elements will be saved in encoded format without a query for conversion to
plain format.

This variable is provided for users that want to compress their incoming mail
for RMAIL and VM which look for files `RMAIL' and `INBOX,' respectively, to
store incoming mail.  For example, the gzip extensions on `RMAIL.gz' and
`INBOX.gz' can be removed, this variable set to '\(\"INBOX$\" \"RMAIL$\"\) and
no query about conversion to plain format will be made.")

(defvar crypt-default-encoding "gzip"
  "*Default encoding type as string used when `crypt-encoded-mode' is toggled.
Must match one of the elements of `crypt-encoding-alist'.")

(defvar crypt-dos-has-ctrl-z nil
  "t if this buffer had a ctrl-z stripped from end, otherwise, nil.
Buffer local and set by `crypt-dos-to-unix-region'")
(make-variable-buffer-local 'crypt-dos-has-ctrl-z)
(setq-default crypt-dos-has-ctrl-z nil)
(put 'crypt-dos-has-ctrl-z 'permanent-local t) ; for v19 Emacs
(put 'crypt-dos-has-ctrl-z 'preserved t)       ; for kill-fix.el

(defvar crypt-decode-dos-p t "Says whether to decode DOS (\r\n) files.")
(defvar crypt-decode-mac-p t "Says whether to decode Mac (\r) files.")

(defun crypt-build-encoding-alist ()
  ;; Returns the encoding alist
  (list
   ;; compress
   (list 'compress
	 "\037\235" nil
	 "\\(\\.Z\\)$"
	 "compress" "uncompress"
	 nil nil
	 "Compress"
	 nil
	 t
	 nil)
   ;; gzip (GNU zip, http://www.gzip.org)
   (list 'gzip
	 "\037\213" nil
	 "\\(\\.g?z\\)$"
	 "gzip" "gzip"
	 "--quiet" "--decompress --quiet"
	 "Gzip"
	 nil
	 t
	 nil)
   ;; bzip
   (list 'bzip
	 "BZ0" nil
	 "\\(\\.bz\\)$"
	 "bzip" "bzip"
	 "" "--decompress"
	 "Bzip"
	 nil
	 t
	 nil)
   ;; bzip2 (block-sorting, http://www.digistar.com/bzip2/)
   (list 'bzip2
	 "BZh" nil
	 "\\(\\.bz2\\)$"
	 "bzip2" "bzip2"
	 "" "--decompress"
	 "Bzip2"
	 nil
	 t
	 nil)
   ;; freeze
   (list 'freeze
	 "\037\236\\|\037\237" nil
	 "\\(\\.F\\)$"
	 "freeze" "freeze"
	 "" "-d"
	 "Freeze"
	 nil
	 crypt-freeze-vs-fortran
	 nil)
   ;; compact
   (list 'compact
	 "\377\037" nil
	 "\\(\\.C\\)$"
	 "compact" "uncompact"
	 nil nil
	 "Compact"
	 "^Compression *:.*\n"
	 crypt-compact-vs-C++
	 nil)
   ;; DOS (crlf)
   (and crypt-decode-dos-p (list 'dos
	 "[^\n\r]*\r\n" nil
	 "\\(\\.DOS\\)$"
	 'crypt-unix-to-dos-region 'crypt-dos-to-unix-region
	 nil nil
	 "Dos"
	 nil
	 nil
	 nil))
    ;; Mac (cr)
    (and crypt-decode-mac-p (list 'mac
	  "[ -~]*\r[ -~]" nil
	  "\\(\\.MAC\\)$"
	  'crypt-unix-to-mac-region 'crypt-mac-to-unix-region
	  nil nil
	  "Mac"
	  nil
	  nil
	  nil))
   )
)

(defconst crypt-encoding-alist (crypt-build-encoding-alist)
  "List of elements describing the encoding methods available.
each element looks like
	\(ENCODING-TYPE
	  MAGIC-REGEXP MAGIC-REGEXP-INVERSE
	  FILE-EXTENSION
	  ENCODE-PROGRAM DECODE-PROGRAM
	  ENCODE-ARGS DECODE-ARGS
	  MINOR-MODE
	  GARBAGE-REGEXP-OR-LISPEXP
	  FILE-EXTENSION-TRICKS
	  ENCRYPTION-KEY-STDIN
	 \)
ENCODING-TYPE is a symbol denoting the encoding type.  Currently known
encodings are (compress compact freeze gzip).

MAGIC-REGEXP is a regexp that matches the magic number at the
beginning of files encoded with ENCODING-TYPE.

MAGIC-REGEXP-INVERSE dummy variable for compatibility with encryption.

FILE-EXTENSION is a string denoting the file extension usually
appended the filename of files encoded with ENCODING-TYPE.

ENCODE-PROGRAM is a string denoting the name of the executable used to
encode files.

DECODE-PROGRAM is a string denoting the name of the executable used to
decode files.

ENCODE-ARGS arguments to be passed to ENCODE-PROGRAM may be a string or a
list of strings or nil.

DECODE-ARGS arguments to be passed to DECODE-PROGRAM may be a string or a
list of strings or nil.

MINOR-MODE is a string denoting the name for the encoded minor mode as
it will appear in the mode line.

GARBAGE-REGEXP-OR-LISPEXP is (1) a regexp that matches any extraneous text
that is produced by the ENCODE-COMMAND including any newlines and will be
removed from the buffer before saving to disk; (2) a lisp expression that will
clean up extraneous material in the buffer or nil.  This is normally not
needed but can be derived for any ENCODE-COMMAND by checking the standard
error that results from `sh -c \"cat foo | ENCODE-COMMAND > bar\"'.

FILE-EXTENSION-TRICKS is t or nil depending on whether or not tricks
converting between different encoding types can be done based on
FILE-EXTENSION; typically t.

ENCRYPTION-KEY-STDIN is a dummy variable for compatibility with encryption.
")


;;; This allows the user to alter contents of the encoding and encryption
;;; table variables without having to reload all of crypt++.
(defun crypt-rebuild-tables ()
  "Rebuilds the encryption and encoding tables and `minor-mode-alist'.
Allows user to alter variables used in building these tables.  May be called
interactively or in an initialization file.  Part of `after-init-hook'."
  (interactive)
  (setq crypt-encryption-alist (crypt-build-encryption-alist)
	crypt-encoding-alist (crypt-build-encoding-alist))
  (crypt-rebuild-minor-modes-alist))


;;; Buffer locals.

(defvar crypt-buffer-save-encrypted nil
  "*non-nil says save buffer encrypted with `crypt-encryption-type.'
local to all buffers.")
(make-variable-buffer-local 'crypt-buffer-save-encrypted)
(put 'crypt-buffer-save-encrypted 'permanent-local t) ; for v19 Emacs
(put 'crypt-buffer-save-encrypted 'preserved t)       ; for kill-fix.el

(defvar crypt-buffer-encryption-key nil
  "*Key used for encryption of current buffer.  Local to all buffers.")
(make-variable-buffer-local 'crypt-buffer-encryption-key)
(put 'crypt-buffer-encryption-key 'permanent-local t) ; for v19 Emacs
(put 'crypt-buffer-encryption-key 'preserved t)       ; for kill-fix.el

(defvar crypt-buffer-save-encoded nil
  "*non-nil says buffer will be saved encoded.  Local to all buffers.")
(make-variable-buffer-local 'crypt-buffer-save-encoded)
(put 'crypt-buffer-save-encoded 'permanent-local t)   ; for v19 Emacs
(put 'crypt-buffer-save-encoded 'preserved t)         ; for kill-fix.el

(defvar crypt-buffer-encoding-type nil
  "*non-nil says buffer is encoded with ENCODING-TYPE.  Local to all buffers.")
(make-variable-buffer-local 'crypt-buffer-encoding-type)
(put 'crypt-buffer-encoding-type 'permanent-local t)  ; for v19 Emacs
(put 'crypt-buffer-encoding-type 'preserved t)        ; for kill-fix.el

(defvar crypt-buffer-interactive-encoded-mode nil
  "t says `crypt-encoded-mode' was toggled interactively, almost always nil.
Local to all buffers.")
(make-variable-buffer-local 'crypt-buffer-interactive-encoded-mode)
(put 'crypt-buffer-interactive-encoded-mode 'permanent-local t) ; v19 Emacs
(put 'crypt-buffer-interactive-encoded-mode 'preserved t)       ; kill-fix.el


;;; Functions and macros that search `crypt-encryption-alist' and
;;; `crypt-encoding-alist'.

(defun crypt-get-alist-member (type n)
  ;; Returns TYPE's Nth element
  (nth n (or (assoc type crypt-encryption-alist)
	     (assoc type crypt-encoding-alist))))

(defmacro crypt-get-magic-regexp (type)
  ;; Returns regexp found at top of files encoded/encrypted with TYPE.
  (list 'crypt-get-alist-member type 1))

(defmacro crypt-get-magic-regexp-inverse (type)
  ;; Returns regexp *not* found at top of files encoded/encrypted with TYPE.
  (list 'crypt-get-alist-member type 2))

(defmacro crypt-get-file-extension (type)
  ;; Returns regexp matching extension of files encoded/encrypted with TYPE.
  (list 'crypt-get-alist-member type 3))

(defmacro crypt-get-encoding-program (type)
  ;; Returns name of program, as string, used to encode/encrypt with TYPE.
  (list 'crypt-get-alist-member type 4))

(defmacro crypt-get-decoding-program (type)
  ;; Returns name of program, as string, used to decode/decrypt with TYPE.
  (list 'crypt-get-alist-member type 5))

(defmacro crypt-get-encoding-args (type)
  ;; Returns arguments passed to program used to encode/encrypt with TYPE.
  (list 'crypt-get-alist-member type 6))

(defmacro crypt-get-decoding-args (type)
  ;; Returns arguments passed to program used to decode/decrypt with TYPE.
  (list 'crypt-get-alist-member type 7))

(defmacro crypt-get-minor-mode-name (type)
  ;; Returns minor mode name, as string, for encoding/encrypting with TYPE.
  (list 'crypt-get-alist-member type 8))

(defmacro crypt-get-cleanup-regexp (type)
  ;; Returns regexp or lisp-exp for cleaning up encoding/encrypting with TYPE.
  (list 'crypt-get-alist-member type 9))

(defmacro crypt-get-extension-tricks (type)
  ;; Returns t if file extension tricks doable for encoding/encrypting with
  ;; TYPE.
  (list 'crypt-get-alist-member type 10))

(defmacro crypt-get-encryption-key-stdin (type)
  ;; Returns t if encryption program takes passphrase on stdin, or nil
  ;; if at end of command line.
  (list 'crypt-get-alist-member type 11))

(defun crypt-buffer-save-name (type)
  ;; Returns variable `crypt-buffer-save-TYPE', set to t if encoding with TYPE.
  ;; local to all buffers.
  (intern (concat "crypt-buffer-save-" (symbol-name type))))


;;; Create a buffer-local variable for each type of encoding.
;;; These variables are used to trigger the minor mode names.

(defun crypt-build-minor-mode-alist ()
  ;; Returns minor mode alist entries for encoded and encrypted buffers.
  (append
   ;; First the encrypted minor mode -- only one.
   (list (list 'crypt-buffer-save-encrypted
	       (concat " " (crypt-get-minor-mode-name crypt-encryption-type))))
   ;; Now the encoding minor modes.
   (mapcar
    (function
     (lambda (element)
       (let ((variable (crypt-buffer-save-name (car element))))
	 (make-variable-buffer-local variable)
	 (put variable 'permanent-local t) ; for v19 Emacs
	 (put variable 'preserved t)       ; for kill-fix.el
	 (list variable
	       (concat " " (crypt-get-minor-mode-name (car element)))))))
    crypt-encoding-alist)))

(defconst crypt-minor-mode-alist (crypt-build-minor-mode-alist)
  "Alist containing encoded and encrypted minor modes.
Derived from variable `crypt-encoding-alist' and function
`crypt-build-minor-mode-encrypted'")

(defun crypt-rebuild-minor-modes-alist ()
  ;; Rebuilds the encryption and encoding minor modes and `minor-mode-alist.'
  ;; Allows user to alter variables used in building this alist. Called by
  ;; `crypt-rebuild-tables' and so part of `after-init-hook'."

  ;; First remove old crypt minor mode entries from `minor-mode-alist'.
  (if (memq (car crypt-minor-mode-alist) minor-mode-alist)
      (let ((alist crypt-minor-mode-alist) elt)
	(while (and alist (setq elt (car alist)))
	  (setq minor-mode-alist (delq elt minor-mode-alist)
		alist (cdr alist)))))

  ;; Get new crypt minor mode entries and add to minor-mode-alist.
  (setq crypt-minor-mode-alist (crypt-build-minor-mode-alist)
	minor-mode-alist (append crypt-minor-mode-alist minor-mode-alist)))


(defmacro crypt-save-point (&rest body)
  ;; Save value of point, evaluate FORMS, and restore value of point.  If the
  ;; saved value of point is no longer valid go to (point-max).  This macro
  ;; exists because, save-excursion loses track of point during some types of
  ;; deletions.
  (let ((var (make-symbol "saved-point")))
    (list 'let (list (list var '(point)))
	  (list 'unwind-protect
		(cons 'progn body)
		(list 'goto-char var)))))


;; Hook run for decoding and/or decrypting the contents of a buffer.  Meant
;; to be called as part of `find-file-hooks'.
;;
(defun crypt-find-file-hook ()
  ;(message "starting crypt-find-file-hook")
  ;(message "buffer at file hook:\n%s\n--end" (buffer-string))
  (let ((buffer-file-name buffer-file-name)
	(old-buffer-file-name buffer-file-name)
	(old-buffer-modified-p (buffer-modified-p))
	(case-fold-search nil) ; case-sensitive
	(binary-process-input t) ; Win32
	(binary-process-output t) ; Win32
	encrypted encoded buffer-read-only)


    ;; DECODE AND/OR DECRYPT
    (crypt-save-point

     ;; Do we have to DECODE? If not, then move on.
     (if (and (crypt-encoded-p)
	      (or crypt-auto-decode-buffer
		  (y-or-n-p (format "Decode %s? " (buffer-name)))))

	 ;; Decode, uncompress, the buffer.
	 (progn

	 ;; This is ugly, but it makes tar-mode recognize and decode the
	 ;; buffer after we uncompress it.  We should at least use the
	 ;; regexps already defined in the table.
	 (if (and (not (null buffer-file-name))
		  (string-match "\\.Z$" buffer-file-name))
	     (set-visited-file-name
	      (substring buffer-file-name 0 (match-beginning 0))))
	 (if (and (not (null buffer-file-name))
		  (string-match "\\.g?z$" buffer-file-name))
	     (set-visited-file-name
	      (substring buffer-file-name 0 (match-beginning 0))))
	 (if (and (not (null buffer-file-name))
		  (string-match "\\.bz2?$" buffer-file-name))
	     (set-visited-file-name
	      (substring buffer-file-name 0 (match-beginning 0))))
	 (if (and (not (null buffer-file-name))
		  (string-match "\\.tgz$" buffer-file-name))
	     (set-visited-file-name (concat
	      (substring buffer-file-name 0 (match-beginning 0)) ".tar")))
	 (if (and (not (null buffer-file-name))
		  (string-match "\\.tbz$" buffer-file-name))
	     (set-visited-file-name (concat
	      (substring buffer-file-name 0 (match-beginning 0)) ".tar")))

	   (message "Decoding %s..." (buffer-name))
	   (crypt-encode-buffer t)

	   ;; Store the encoding mode.

	   ;; We can not yet go into the minor modes because the major mode
	   ;; may change later on and blow away all local variables (and thus
	   ;; the minor modes).  Only needed for vanilla v18.  Our
	   ;; buffer-locals defined 'permanent-local for v19 Emacs and
	   ;; 'preserved for kill-fix.el.

	   (setq encoded crypt-buffer-encoding-type)

	   ;; Strip encoded file's extension so later we can set buffer's
	   ;; major mode based on its file-name sans encoding extension.
	   (if (string-match (crypt-get-file-extension
			      crypt-buffer-encoding-type) buffer-file-name)
	       (setq buffer-file-name
		     (substring buffer-file-name 0 (match-beginning 1))))

	   ;; Decoding ends.
	   (if (not (input-pending-p))
	       (message "Decoding %s... done" (buffer-name)))))

     ;; Do we have to DECRYPT? If not, then move on.
     (if (crypt-encrypted-p)

	 ;; Decrypt buffer.
	 (progn

	   (message "Decrypting %s..." (buffer-name))
	   (crypt-encrypt-buffer crypt-buffer-encryption-key t)

	   ;; Save key in case major mode blows all buffer-locals.

	   ;; Only needed for vanilla v18.  Our buffer-locals defined
	   ;; 'permanent-local for v19 Emacs and 'preserved for
	   ;; kill-fix.el.

	   (setq encrypted crypt-buffer-encryption-key)

	   ;; Strip encrypted file's extension so later we can set buffer's
	   ;; major mode based on its file-name sans encrypting extension.
	   (if (and (crypt-get-extension-tricks crypt-encryption-type)
		    (string-match (crypt-get-file-extension
				   crypt-encryption-type) buffer-file-name))
	       (setq buffer-file-name
		     (substring buffer-file-name 0 (match-beginning 1))))

	   (if (not (input-pending-p))
	       (message "Decrypting %s... done" (buffer-name))))))

    ;; MAJOR AND MINOR MODES

    ;; OK, if any changes have been made to the buffer we need to rerun the
    ;; code the does automatic selection of major mode.

    (if (or encoded encrypted)

	(progn

	  ;; Set the major mode.
	  (set-auto-mode)
	  (hack-local-variables)

	  ;; Now set our own minor mode(s).
	  (if encoded
	      ;; Recover encoding type, may have been smashed by major mode,
	      ;; and toggle encoded mode.
	      (progn (setq crypt-buffer-encoding-type encoded)
		     (crypt-encoded-mode 1)))

	  (if encrypted
	      ;; Recover encryption key, may have been smashed by major mode,
	      ;; and toggle encrypted mode.
	      (progn (setq crypt-buffer-encryption-key encrypted)
		     (crypt-encrypted-mode 1)))

	  ;; Restore buffer file name now, so that lock file entry is removed
	  ;; properly.
	  (setq buffer-file-name old-buffer-file-name)

	  ;; Restore buffer modified flag to its previous value.  Will also
	  ;; remove lock file entry for buffer if previous value was nil.
	  ;; This is why buffer-file-name had to be restored manually above.
	  (set-buffer-modified-p old-buffer-modified-p)))))

(defun crypt-encoded-p (&optional buffer)
  ;; Returns t if current buffer, or optionally BUFFER, is encoded.
  ;; Sets `crypt-buffer-encoding-type' to encoding method.
  (save-excursion
    (and buffer (set-buffer buffer))
    (save-restriction
      (widen)
      (goto-char (point-min))
      (let ((alist crypt-encoding-alist) elt found)
	(while (and alist (setq elt (car alist)) (not found))
	  (if (looking-at (nth 1 elt))
	      (setq crypt-buffer-encoding-type (nth 0 elt)
		    found t)
	    ;; Decrement
	    (setq alist (cdr alist))))
	found))))

(defun crypt-encrypted-p (&optional buffer)
  ;; Returns t if current buffer, or optionally BUFFER, is encrypted.
  ;; Look for MAGIC-REGEXP and absence of MAGIC-REGEXP-INVERSE.  If so, then
  ;; assume it is an encrypted buffer.
  ;; Sets `crypt-buffer-encryption-key' to password if not set already.

  ;; Do not try to decrypt buffer if not wanted.
  (if (not crypt-never-ever-decrypt)

      (save-excursion
	(and buffer (set-buffer buffer))

	(save-restriction
	  (widen)
	  (goto-char (point-min))

	  (let ((magic-regexp (crypt-get-magic-regexp crypt-encryption-type))
		(magic-regexp-inverse (crypt-get-magic-regexp-inverse
				       crypt-encryption-type))
		(limit (min (point-max) crypt-magic-search-limit)))

	    ;; Check all encryption conditions.  If any fail, then return nil
	    ;; value of this if-form, else check for password.
	    (if (and

		 ;; Check for existence of MAGIC-REGEXP.
		 (if (stringp magic-regexp)
		     ;; regular expression
		     (re-search-forward magic-regexp limit t)
		   ;; lisp expression
		   (eval magic-regexp))

		 (goto-char (point-min))

		 ;; Check for absence of MAGIC-REGEXP-INVERSE.
		 (not (if (stringp magic-regexp-inverse)
			  ;; regular expression
			  (re-search-forward magic-regexp-inverse limit t)
			;; lisp expression
			(eval magic-regexp-inverse))))

		(progn

		  ;; Get key, i.e., the password?
		  (or crypt-buffer-encryption-key
		      ;; Do not confirm on reading an encrypted file.
		      (let ((crypt-confirm-password nil))
			(call-interactively 'crypt-set-encryption-key)))

		  ;; Do not turn on encryption mode if no key: may be a binary
		  ;; file.  Thanks to Paul Dworkin (paul@media-lab.media.mit.edu).
		  (if (equal crypt-buffer-encryption-key "")
		      ;; Return nil.
		      (progn
			(message "No key given.  Assumed normal.")
			nil)
		    ;; Return t.
		    t))))))))


;;;

(defun crypt-check-extension-for-encoding ()

  ;; Checks file extensions for possible toggling of encoding modes.  Used for
  ;; buffers to be written to disk and called by `crypt-write-file-hook'

  ;; We try to flag a buffer to be written out in encoded form if the file
  ;; ends in one of the file-extensions in `crypt-encoding-alist' even if
  ;; `crypt-buffer-save-encoded' is nil.  Conversely, we try to write out a
  ;; buffer as a plain file if it does _not_ end in one of these
  ;; file-extensions even if `crypt-buffer-save-encoded' is non-nil.

  (let ((alist crypt-encoding-alist)
	(case-fold-search nil)
	found elt)

    ;; Search through the file name extensions for a match.
    (while (and alist (setq elt (car alist)) (not found))
      (if (string-match (nth 3 elt) buffer-file-name)
	  (setq found t)
	;; Decrement.
	(setq alist (cdr alist))))

    ;; Did we find a match?
    (if found

	;; File name ends in a very provocative extension.

	;; Check to see if already an encoded file.
	(if crypt-buffer-save-encoded

	    ;; Already encoded - do the methods of encoding match?
	    (if (not (eq (nth 0 elt) crypt-buffer-encoding-type))

		;; A new encoding method is desired.

		;; Can we play some filename extension tricks with the
		;; destination extension?
		(if (crypt-get-extension-tricks (nth 0 elt))

		    ;; Can play tricks.
		    ;; Change the method of encoding?
		    (if (crypt-y-or-n-p (format "Write %s using %s? "
					 (buffer-name) (nth 4 elt)))

			;; Case one.
			;; Turn off original encoding and turn on new encoding.
			(progn (crypt-encoded-mode -1)
			       (setq crypt-buffer-encoding-type (nth 0 elt))
			       (crypt-encoded-mode 1)))

		  ;; Can not play tricks - maybe wants a plain file?
		  (if (crypt-y-or-n-p (format "Write %s a plain file? "
					      (buffer-name)))

		      ;; Case three.
		      ;; Turn off the minor mode and _then_ the flags.
		      (progn
			(crypt-encoded-mode -1)
			(setq crypt-buffer-save-encoded nil
			      crypt-buffer-encoding-type nil)))))

	  ;; Was a plain file.
	  (if (and
	       ;; Can we play some filename extension tricks?
	       ;; If not then we must abort.
	       (crypt-get-extension-tricks (nth 0 elt))

	       (crypt-y-or-n-p (format "Write %s using %s? "
				       (buffer-name) (nth 4 elt))))

	      ;; Case two.
	      ;; Turn on encoding flags and _then_ the minor mode.
	      (progn
		(setq crypt-buffer-save-encoded t
		      crypt-buffer-encoding-type (nth 0 elt))
		(crypt-encoded-mode 1))))

      ;; No match - a plain-jane file extension - but if the encoded flag is
      ;; non-nil then the user may really want it written out in plain
      ;; format so we must override this flag.
      (if (and crypt-buffer-save-encoded

	       ;; Search the list of files to be ignored.
	       ;; If `crypt-ignored-filenames' is nil then this let form
	       ;; will return t.  If a match is found this form will return
	       ;; nil.  Otherwise it will return t.
	       (let ((tlist crypt-ignored-filenames)
		     case-fold-search found elt)

		 ;; Search through the list of filenames for a match.
		 (while (and tlist (setq elt (car tlist)) (not found))
		   (if (string-match elt buffer-file-name)
		       (setq found t)
		     ;; Decrement.
		     (setq tlist (cdr tlist))))

		 ;; Return t if we can _not_ find a match.
		 (not found))

	       ;; If `(crypt-encoded-mode)' was called interactively, then
	       ;; there is a high probability that no matter what the file
	       ;; name extension the user wishes to write the file out in some
	       ;; encoded format.  Thanks to Kimball Collins
	       ;; <kpc@ptolemy.arc.nasa.gov> for pointing out the need for
	       ;; this.  Unfortunately, still can not distinguish between
	       ;; write-file and save-buffer.  In the former the user may want
	       ;; to write in plain format (or indeed some other format).

	       (if crypt-buffer-interactive-encoded-mode
		   ;; Interactive
		   crypt-query-if-interactive
		 ;; Non-interactive but still may want encoded format.
		 crypt-no-extension-implies-plain)

	       (crypt-y-or-n-p (format "Write %s as a plain file? "
				       (buffer-name))))

	  ;; Case three.
	  ;; Turn off the minor mode and _then_ the flags.
	  (progn
	    (crypt-encoded-mode -1)
	    (setq crypt-buffer-save-encoded nil
		  crypt-buffer-encoding-type nil))))))


(defun crypt-y-or-n-p (prompt)
  ;; Queries user based on `crypt-auto-write-buffer' and internal buffer-local
  ;; variable `crypt-auto-write-answer-local'.  Returns value of
  ;; `crypt-auto-write-answer-local', which is t or nil.

  ;; Check if we need to ask user.  Should be 'ask, nil, or t.
  (if (eq crypt-auto-write-answer-local 'ask) ; Default value.
      ;; We may need to ask.
      (or crypt-auto-write-buffer
	  ;; Ask and store the answer.
	  ;; Note: we only store if we asked.
	  (setq crypt-auto-write-answer-local (y-or-n-p prompt)))
    ;; Use previous answer.
    crypt-auto-write-answer-local)) ; Will be nil or t.


;;; This function should be called ONLY as a write-file hook.
;;; Odd things will happen if it is called elsewhere.

(defun crypt-write-file-hook ()

  ;; Hook for possibly writing out file, and backup file, in a non-plain
  ;; format.  Terminates calls in `write-file-hooks' and should be at end of
  ;; list.

  (let ((binary-process-input t)  ; Win32
	(binary-process-output t) ; Win32
	(inhibit-read-only t)     ; else we lose on read-only properties
       )

  ;; Check file-extension for possible toggling of encoding modes.
  (crypt-check-extension-for-encoding)

  ;; Check extension for encryption.
  (if (and

       ;; Maybe file ends with provocative extension w.r.t. encryption?
       (stringp (crypt-get-file-extension crypt-encryption-type))
       (let ((case-fold-search nil)) ; Make case-sensitive.
	 (string-match (crypt-get-file-extension crypt-encryption-type)
		       buffer-file-name))

       ;; Can we play tricks?
       (crypt-get-extension-tricks crypt-encryption-type)

       ;; Match of filename extension - is file in plain format?
       (not crypt-buffer-save-encrypted)

       ;; Query?
       (or crypt-auto-write-buffer-encrypted
	   (y-or-n-p
	    (format "Write %s as an encrypted file? " (buffer-name)))))

      (progn
	;; Set password and toggle `crypt-encrypted-mode'
	(if (eq crypt-encryption-type 'pgp-pub)
	    (crypt-set-encryption-key "dummy-key")
	  (call-interactively 'crypt-set-encryption-key))
	(crypt-encrypted-mode 1)))

  ;; Now decide whether or not we need to continue with this defun. Does the
  ;; buffer need to be saved in a non-plain form?  If not then writing is not
  ;; done here but later in the write-file-hooks - probably at the end.

  (if (or crypt-buffer-save-encoded crypt-buffer-save-encrypted)

      (save-excursion
	(save-restriction

	  (let

	      ;; BINDINGS
	      ((copy-buffer (get-buffer-create " *crypt copy buffer*"))
	       (selective-display selective-display)
	       (buffer-read-only))

	    ;; FORMS
	    (copy-to-buffer copy-buffer 1 (1+ (buffer-size)))
	    (narrow-to-region (point) (point))

	    (unwind-protect

		;; BODYFORM
		(let (setmodes)

		  ;; As of v19, if one of functions of the `write-file-hooks'
		  ;; returns a non-nil value, then `basic-save-buffer' no
		  ;; longer creates a backup file.  We must do it ourselves.
		  ;; this should be a no-op in v18.
		  (or buffer-backed-up
		      (setq setmodes (backup-buffer)))

		  (insert-buffer-substring copy-buffer)
		  (kill-buffer copy-buffer)

		  ;; "Who would cross the Bridge of Death
		  ;;  Must answer me
		  ;;  These questions three
		  ;;  Ere the other side he see."
		  ;;
		  ;; Bridgekeeper from Monty Python and the Holy Grail

		  ;; [1] selective-display non-nil means we must convert
		  ;; carriage returns to newlines now, and set the variable
		  ;; selective-display temporarily to nil.
		  (if selective-display
		      (progn
			(goto-char (point-min))
			(subst-char-in-region (point-min) (point-max) ?\r ?\n)
			(setq selective-display nil)))

		  ;; [2] encryption
		  (if crypt-buffer-save-encrypted
		      (progn
			;; check for password
			(if (not crypt-buffer-encryption-key)
			    (call-interactively 'crypt-set-encryption-key))
			(if (null crypt-buffer-encryption-key)
			    (error "No encryption key set for buffer %s"
				   (buffer-name)))
			(if (not (stringp crypt-buffer-encryption-key))
			    (error "Encryption key is not a string"))
			(message "Encrypting %s..." (buffer-name))
			(crypt-encrypt-buffer crypt-buffer-encryption-key)))

		  ;; [3] encoding
		  (if crypt-buffer-save-encoded
		      (progn
			(message "Encoding %s..." (buffer-name))
			(crypt-encode-buffer)))

		  ;; Now write buffer/region to disk.
		  (write-region (point-min) (point-max) buffer-file-name nil t)
		  (delete-region (point-min) (point-max))
		  (set-buffer-modified-p nil)

		  ;; Now that the file is written, set its modes.
		  (if setmodes
		      (condition-case ()
			  (set-file-modes buffer-file-name setmodes)
			(error nil)))

		  ;; Return t so that `basic-save-buffer' will know that the
		  ;; save has already been done.

		  ;; NOTE: this TERMINATES write-file-hooks so any hooks
		  ;; following this one will not be executed.

		  t )

	      ;; UNWINDFORMS
	      ;; unwind...sit back...take a load off...have a beer

	      ;; If the encoded and encrypted stuff has already been removed
	      ;; then this is a no-op.  This form is executed if BODYFORM
	      ;; completes normally but the value of BODYFORM is returned -
	      ;; i.e., t is returned.

	      (delete-region (point-min) (point-max)))))))))


;;;; ENCRYPTION

(defvar crypt-pgp-pub-library 'mailcrypt
  "What PGP library to use.
Bind to 'npgp to use \"PEM - PGP Enhanced Messaging for GNU Emacs\"
from Roy Frederick Busdiecker, III (Rick)
or to 'mailcrypt (see also crypt-pgp-pub-sub-library).")

(defvar crypt-pgp-pub-sub-library 'pgp50
  "What variant of mailcrypt 3.5.x to use: 'pgp, 'pgp50, 'gpg.")

(defvar crypt-pgp-pub-npgp-userid nil
  "PGP key for the current user.")

(defvar crypt-pgp-pub-npgp-key-id nil
  "Keyid of PGP key for the current user.
Useful if your \\[user-full-name] doesn't match a unique key.
Should have a leading 0x.")

(defvar crypt-pgp-pub-multirecipients t
  "If t, enables prompts for user so when a file is saved, he/she has the opportunity to enter users for whom the file should be encrypted. nil encrypts only with the user's public key without prompts")

(defvar crypt-pgp-pub-recipient-history ""
  "History list of previous entered recipients")

(defvar crypt-pgp-pub-recipients nil
  "Comma-separated string containing the names of all the people who's private keys could decrypt this file (e.g. recipients, if the file was an email)")

(defun crypt-pgp-pub-clear-recipients ()
  "Clear the recipient list, forcing crypt++ to ask you for the people who's public keys you wish to encrypt the message with"
  (interactive)
  (setq crypt-pgp-pub-recipients nil)
)

(defun crypt-pgp-pub-npgp-userid ()
  "Return crypt-pgp-pub-npgp-userid, initializing it if necessary."
  (require 'pam)
  (if (and crypt-pgp-pub-npgp-userid
	   npgp:*pass-phrases*)
      crypt-pgp-pub-npgp-userid
    (setq crypt-pgp-pub-npgp-userid
	  (list
	   (if crypt-pgp-pub-npgp-key-id
	       (npgp:get-key-by-key-id crypt-pgp-pub-npgp-key-id)
	     (pam:read-name-key (user-full-name)))))))

(defun crypt-pgp-pub-mailcrypt-userid ()
  "Do the right thing."
  (require 'mailcrypt)
  (cond
   ((eq crypt-pgp-pub-sub-library 'pgp)
    (car (mc-pgp-lookup-key mc-pgp-user-id)))
   ((eq crypt-pgp-pub-sub-library 'pgp50)
    (car (mc-pgp50-lookup-key mc-pgp50-user-id)))
   ((eq crypt-pgp-pub-sub-library 'gpg)
    (car (mc-gpg-lookup-key mc-gpg-user-id)))
   (t (error "crypt-pgp-pub-mailcrypt-userid: no pgp sub-library."))))


(defun crypt-pgp-pub-load-mailcrypt ()
  (require 'mailcrypt)
  ;; ick ick ick this code needs to be cleaned up
  (cond
   ((null (eq crypt-pgp-pub-library 'mailcrypt))
    t)
   ((eq crypt-pgp-pub-sub-library 'pgp)
    (load-library "mc-pgp"))
   ((eq crypt-pgp-pub-sub-library 'pgp50)
    (load-library "mc-pgp5"))
   ((eq crypt-pgp-pub-sub-library 'gpg)
    (load-library "mc-gpg"))
   (t (error "crypt-pgp-pub-load-mailcrypt: no pgp sub-library."))))

(defun crypt-pgp-pub-decrypt-region (start end)
  (cond
   ((eq crypt-pgp-pub-library 'npgp) (npgp:decrypt-region start end))
   ((eq crypt-pgp-pub-library 'mailcrypt)
    (crypt-pgp-pub-load-mailcrypt)
    (cond
     ((eq crypt-pgp-pub-sub-library 'pgp)
      (mc-pgp-decrypt-region start end))
     ((eq crypt-pgp-pub-sub-library 'pgp50)
      (mc-pgp50-decrypt-region start end))
     ((eq crypt-pgp-pub-sub-library 'gpg)
      (mc-gpg-decrypt-region start end))
     (t (error "crypt-pgp-pub-decrypt-region: no decryption sub-library."))))
   (t (error "crypt-pgp-pub-decrypt-region: no decryption library."))))

(defun crypt-pgp-pub-encrypt-region (start end)
  (cond
   ((eq crypt-pgp-pub-library 'npgp)
    (npgp:encrypt-region (crypt-pgp-pub-npgp-userid) start end))
   ((eq crypt-pgp-pub-library 'mailcrypt)
    (crypt-pgp-pub-load-mailcrypt)
    (let ((old-sign mc-pgp-always-sign)
	  old-comment recipients)
      (if crypt-pgp-pub-multirecipients
	  (if (eq (length crypt-pgp-pub-recipients) 0)
	      (progn
		(if (y-or-n-p
		     (concat "Encrypt with your public key ("
			      (crypt-pgp-pub-mailcrypt-userid)
			      ")? "))
		    (setq crypt-pgp-pub-recipients
			  (concat (crypt-pgp-pub-mailcrypt-userid) ","))
		  (setq crypt-pgp-pub-recipients ""))
		(setq crypt-pgp-pub-recipients
		      (concat crypt-pgp-pub-recipients
			      (read-string
			       "Recipients: " nil crypt-pgp-pub-recipient-history)))))
	(setq crypt-pgp-pub-recipients (crypt-pgp-pub-mailcrypt-userid)))
      (setq mc-pgp-always-sign 'never
	    recipients (mc-split "\\([ \t\n]*,[ \t\n]*\\)+" crypt-pgp-pub-recipients))
      (cond
       ((eq crypt-pgp-pub-sub-library 'pgp)
	(setq old-comment mc-pgp-comment
	      mc-pgp-comment nil)
	(mc-pgp-encrypt-region recipients start end
			       (crypt-pgp-pub-mailcrypt-userid) nil)
	(setq mc-pgp-comment old-comment))
       ((eq crypt-pgp-pub-sub-library 'pgp50)
	(setq old-comment mc-pgp50-comment
	      mc-pgp50-comment nil)
	(mc-pgp50-encrypt-region recipients start end
			       (crypt-pgp-pub-mailcrypt-userid) nil)
	(setq mc-pgp50-comment old-comment))
       ((eq crypt-pgp-pub-sub-library 'gpg)
	(setq old-comment mc-gpg-comment
	      mc-gpg-comment nil)
	(mc-gpg-encrypt-region recipients start end
			       (crypt-pgp-pub-mailcrypt-userid) nil)
	(setq mc-gpg-comment old-comment))
       (t (error "crypt-pgp-pub-decrypt-region: no encryption sub-library.")))
      (setq mc-pgp-always-sign old-sign)))
   (t (error "crypt-pgp-pub-encrypt-region: no encryption library."))))

(defun crypt-encrypt-region (start end key &optional decrypt)
  "Encrypt region START to END using KEY and `crypt-encryption-type'.  When
called interactively START and END default to point and mark \(START being the
lesser of the two\), and KEY is prompted for.  With optional DECRYPT non-nil,
decryption is done."

  (interactive
   (let (decrypt)
     (barf-if-buffer-read-only)
     (list (region-beginning)
	   (region-end)
	   (crypt-read-string-no-echo
	    (concat (if (setq decrypt (y-or-n-p "Decrypt region? ")) "De" "En")
		    "crypt buffer using key: ")
	    ;; Do not confirm on decrypting region.
	    (if (not decrypt) crypt-confirm-password))
	   decrypt)))

  (crypt-save-point

   ;; We define the PROGRAM as the encryption program or decryption program
   ;; listed for `crypt-encryption-type' of `crypt-encryption-alist.'  These
   ;; should be just the name of the executable and should _not_ contain any
   ;; arguments.  `(call-process-region)' would be confused if we tried to
   ;; pass the arguments as part of the PROGRAM.  The arguments are passed
   ;; through the encryption args or decryption args listed for
   ;; `crypt-encryption-type' of `crypt-encryption-alist.'

   ;; Thanks to Joe Ilacqua <spike@world.std.com> and others for pointing out
   ;; an error that occurs with some encryption programs (e.g., the crypt from
   ;; Sun Microsystems, HPUX-8, and BSD) if `args' is `"".'  This will allow
   ;; nil values and lists of strings for argument.

   (let ((coding-system-for-write 'no-conversion)
	 (coding-system-for-read 'no-conversion)
	 prog args)

     ;; Get the proper program and arguments.
     (if decrypt
	 (setq prog (crypt-get-decoding-program crypt-encryption-type)
	       args (crypt-get-decoding-args crypt-encryption-type))
       (setq prog (crypt-get-encoding-program crypt-encryption-type)
	     args (crypt-get-encoding-args crypt-encryption-type)))

     ;; Either pass encryption key as first line of region, or
     ;; as last argument to program.
     (cond
      ((crypt-get-encryption-key-stdin crypt-encryption-type)
	 (progn
	   (goto-char start)
	   (insert key "\n")
	   (setq end (+ end (length key) 1))))
      ((listp args)
       (setq args (append args (list key))))
      ;; nil or "" args - don't pass.
      ((or (not args) (equal "" args))
       (setq args key))
      (t
       (setq args (concat args " " key))))

     ;; Check arguments.
     (cond

      ;; special-case pgp-pub
      ;; (Yes, this hack is gross.)
      ((eq crypt-encryption-type 'pgp-pub)
       (if decrypt
	   (crypt-pgp-pub-decrypt-region start end)
	 (crypt-pgp-pub-encrypt-region start end)))

      ;(message "start=%d end=%d prog=%s args=%s" start end prog args)
      ;; Check if the args are in the form of a list - must use apply.
      ((listp args)
       (apply 'call-process-region
	      (append (list start end prog t (list t nil) nil) args)))

      ;; Default - just a non-null string.
      (t
       (call-process-region start end prog t '(t nil) nil args))))))


(defun crypt-encrypt-buffer (key &optional decrypt buffer)

  ;; Use KEY to encrypt current buffer and with optional DECRYPT decrypt.
  ;; With optional BUFFER, encrypt or decrypt that buffer.  Not meant to be
  ;; called interactively, toggle `crypt-encrypted-mode' to encrypt an entire
  ;; buffer.

  (or buffer (setq buffer (current-buffer)))
  (save-excursion (set-buffer buffer)
		  (crypt-encrypt-region (point-min) (point-max) key decrypt)))


;;;; ENCODING

(defun crypt-encode-region (start end &optional decode)

  "Encode region START to END.  When called interactively START and END
default to point and mark \(START being the lesser of the two\).  With
optional DECODE non-nil, decoding is done.

If encoding is attempted, then checks for correct magic number at start of
newly-encoded region.  If not found, then searches and deletes a user-defined
regexp, or executes a user-defined lisp expression, as defined in
`crypt-encoding-alist,' and checks again for magic number."

  (interactive "*r\nP")

  ;; If called interactively then we may need to determine the encoding type.
  (if (and (interactive-p) (not crypt-buffer-encoding-type))
      (crypt-read-encoding-type))

  (crypt-save-point

   ;; We define the PROGRAM as `shell-file-name' and have it call the encoding
   ;; or decoding program with the arguments.

   (let ((coding-system-for-write 'no-conversion)
	 (coding-system-for-read 'no-conversion)
	 prog args)

     ;; Get the proper program and arguments.
     (if decode
	 (setq prog (crypt-get-decoding-program crypt-buffer-encoding-type)
	       args (crypt-get-decoding-args crypt-buffer-encoding-type))
       (setq prog (crypt-get-encoding-program crypt-buffer-encoding-type)
	     args (crypt-get-encoding-args crypt-buffer-encoding-type)))

     (cond

      ;; prog is a string?
      ((stringp prog)

       ;; Check arguments.
       (cond

	;; Check if the args are in the form of a list, will catch 'nil.
	((listp args)

	 ;; Cat all the strings together.
	 (while args
	   (setq prog (concat prog " " (car args))
		 args (cdr args))))

	;; Check if a non-null string.
	((and (not (string= "" args))
	      (not (eq args t))) ; just in case...
	 (setq prog (concat prog " " args))))

       ;(message "start=%d end=%d prog+args=%s" start end prog)
       ;(message "buffer before:\n%s\n--end" (buffer-string))
       (call-process-region start end shell-file-name t '(t nil) nil
			    shell-command-switch prog)
       ;(message "buffer after:\n%s\n--end" (buffer-string))
      )

      ;; Otherwise try and eval it.
      (t
       ;(message "eval prog=%s args=%s" prog args)
       (eval (if args
		 (list prog start end args)
	       (list prog start end))))))

   ;; Encoding or decoding region?
   (if (not decode)

       ;; Check if encoded region starts with magic number.
       (let ((magic (crypt-get-magic-regexp crypt-buffer-encoding-type))
	     (clean (crypt-get-cleanup-regexp crypt-buffer-encoding-type))
	     (case-fold-search nil))

	 ;; Top of region.
	 (goto-char start)

	 ;; Check for magic number.
	 (if (not (looking-at magic))

	     ;; Magic number not there.

	     ;; Some compression programs produce an (inane) standard error
	     ;; message that gets piped into the buffer.  For example, some
	     ;; versions of compact output "Compression : 35.50%."  There may
	     ;; be some way to clean up buffer and check again.

	     (cond

	      ;; No mechanism to clean up - failed.
	      ((eq clean nil)
	       (error "Encoding failed!"))

	      ;; Cleanup a regexp string?
	      ((stringp clean)

	       ;; Is regexp there?
	       (if (looking-at clean)

		   (progn
		     ;; Delete the match.
		     (delete-region (match-beginning 0) (match-end 0))

		     ;; Check for magic again.
		     (if (not (looking-at magic))
			 (error "Encoding failed!")))))

	      ;; Default: evaluate a lisp expression and check again.
	      (t (eval clean)
		 (if (not (looking-at magic))
		     (error "Encoding failed!")))))))))

(defun crypt-encode-buffer (&optional decode buffer)

  ;; Encode current buffer.  With optional DECODE non-nil decode and optional
  ;; BUFFER, encode or decode that buffer.  Not meant to be called
  ;; interactively, toggle `crypt-encoded-mode' to encode an entire buffer.

  (or buffer (setq buffer (current-buffer)))
  (save-excursion (set-buffer buffer)
		  (crypt-encode-region (point-min) (point-max) decode)))


;;;; DOS <--> UNIX
(defun crypt-dos-to-unix-region (start end)
  "Converts region from START to END, from dos to unix format.
Replaces \"\\r\\n\" with \"\\n\" and, if exists, removes ^Z at end of file.
Sets `crypt-dos-has-ctrl-z'."
  (save-excursion
    ;(message "doing dos to unix")
    (save-restriction
      (let ((remove-ctrl-z (equal end (point-max))))
	(narrow-to-region start end)
	(goto-char (point-min))
	(while (search-forward "\r\n" nil t)
	  (replace-match "\n" nil t))
	(if remove-ctrl-z
	    (progn
	      (goto-char (1- (point-max)))
	      (setq crypt-dos-has-ctrl-z (looking-at "\C-z"))
	      (if crypt-dos-has-ctrl-z (replace-match ""))))))))

(defun crypt-unix-to-dos-region (start end)
  "Converts region from START to END, from dos to unix format.
Replaces \"\\n\" with \"\\r\\n\" and adds a ^Z at end of file if
`crypt-dos-has-ctrl-z' is non-nil."
  (save-excursion
    ;(message "doing unix to dos")
    (save-restriction
      (let ((add-ctrl-z (and crypt-dos-has-ctrl-z
			    (equal end (point-max)))))
	(narrow-to-region start end)
	(goto-char (point-min))
	(while (search-forward "\n" nil t)
	  (replace-match "\r\n" nil t))
	(if add-ctrl-z
	    (progn
	      (goto-char (point-max))
	      (insert "\C-z")))))))

;;;; MAC <--> UNIX
(defun crypt-mac-to-unix-region (start end)
  "Converts region from START to END, from mac to unix format.
Replaces \"\\r\" with \"\\n\"."
  (save-excursion
    ;(message "doing mac to unix")
    (save-restriction
      (narrow-to-region start end)
      (goto-char (point-min))
      (while (search-forward "\r" nil t)
	(replace-match "\n" nil t))
      )))

(defun crypt-unix-to-mac-region (start end)
  "Converts region from START to END, from mac to unix format.
Replaces \"\\n\" with \"\\r\"."
  (save-excursion
    ;(message "doing unix to mac")
    (save-restriction
      (narrow-to-region start end)
      (goto-char (point-min))
      (while (search-forward "\n" nil t)
	(replace-match "\r" nil t))
      )))


;;;; MODES

(defun crypt-encrypted-mode (&optional arg)

  "Toggle encrypted mode.  With ARG, turn on iff positive, otherwise turn off.
minor mode in which buffers are automatically encrypted before being written.
if toggled and a key has been set for the current buffer, then the current
buffer is marked modified, since it needs to be rewritten with or without
encryption.

Entering encrypted mode causes auto-saving to be turned off in the current
buffer, as there is no way in Emacs Lisp to force auto save files to be
encrypted."

  (interactive "P")
  (let ((oldval crypt-buffer-save-encrypted))
    (setq crypt-buffer-save-encrypted
	  (if arg (> arg 0) (not crypt-buffer-save-encrypted)))

    (if crypt-buffer-save-encrypted
	;; We are going to save as encrypted, we will turn off auto-saving.
	(progn
;; NEVER do this.  Turning off auto-saving is one thing.  But if there's
;; already an autosave for some other reason, what business does this
;; package have tampering with it?
;          ;; If an auto-save file already exists, then delete it.
;          (if (and (stringp buffer-auto-save-file-name)
;                   (file-exists-p buffer-auto-save-file-name))
;              (delete-file buffer-auto-save-file-name))
	  ;; If the key is not set then ask for it.
	  (if (not crypt-buffer-encryption-key)
	      (call-interactively 'crypt-set-encryption-key))
	  ;; Encrypted files should not be converted.
	  (setq buffer-file-coding-system 'no-conversion)
	  ;; Turn-off auto-saving if crypt-encrypted-disable-auto-save non-nil.
	  (and crypt-encrypted-disable-auto-save
	       auto-save-default
	       (progn
		 (auto-save-mode 0)
		 (if (eq crypt-encrypted-disable-auto-save t)
		     (message "Auto-save off (in this buffer)")))))

      ;; We are not going to save as encrypted, we will turn on auto-saving
      ;; but only if we are editing a file and the default says we should.
      (auto-save-mode (if (and auto-save-default buffer-file-name) 1 0)))

    (if crypt-buffer-encryption-key
	;; Set buffer-modified flag to t only if the mode has been changed,
	;; old code set unconditionally to nil if mode was not changed .
	;; Modification suggested by: Gerd Hillebrand <ggh@cs.brown.edu>
	(if (not (eq oldval crypt-buffer-save-encrypted))
	    (set-buffer-modified-p t)))))


;;; Originally `tek-symbol-alist-to-table' from tek-highlight.el.
(defun crypt-symbol-alist-to-table (list)
  ;; Converts an alist of symbols to a table suitable for `completing-read.'
  ;; Called by `crypt-read-encoding-type'
  (mapcar (function (lambda (x) (list (symbol-name (car x)))))
	  list))

(defun crypt-read-encoding-type ()

  ;; Function called to query user for `crypt-buffer-encoding-type' uses
  ;; contents of `crypt-encoding-alist' and `crypt-default-encoding.'

  ;; Use poor man's gmhist (i.e., we could have used gmhist's
  ;; `completing-read-with-history-in' instead).
  (let (
	;; Find the encoding type desired by user.
	(type
	 (completing-read
	  (concat "encoding type (? for list): [" crypt-default-encoding "] ")
	  (crypt-symbol-alist-to-table crypt-encoding-alist))))

    ;; Test length of object returned by `completing-read'.
    (if (zerop (length type))

	;; Nothing there, i.e., user hit return -- use default.
	(setq crypt-buffer-encoding-type (intern crypt-default-encoding))

      ;; Use the value from mini-buffer and update the default value.
      (setq crypt-buffer-encoding-type (intern type)
	    crypt-default-encoding type))))

(defun crypt-encoded-mode (&optional arg)

  "Toggle encoded mode.  With ARG, turn on iff positive, otherwise turn off.
minor mode in which buffers are automatically encoded before being written.  if
toggled then current buffer is marked modified, since it needs to be written
with or without encoding.

Entering encoded mode causes auto-saving to be turned off in the current
buffer, as there is no way in Emacs Lisp to force auto save files to be
encoded."

  (interactive "P")

  ;; Set flag indicating whether or not `(crypt-encoded-mode)' was called
  ;; interactively.
  (setq crypt-buffer-interactive-encoded-mode (interactive-p))

  ;; If called interactively then need to determine encoding type.
  (if (and crypt-buffer-interactive-encoded-mode
	   (not crypt-buffer-encoding-type))
      (crypt-read-encoding-type))

  ;; Save old value of `crypt-buffer-save-encoded'.
  (let ((oldval crypt-buffer-save-encoded))

    ;; Set the variable `crypt-buffer-save-encoded' to t if the argument is
    ;; positive, otherwise toggle its current value.
    (setq crypt-buffer-save-encoded
	  (if arg (> arg 0) (not crypt-buffer-save-encoded)))

    ;; Set the variable generated by `(crypt-buffer-save-name)' to the value
    ;; stored in `crypt-buffer-save-encoded.'
    (set-variable (crypt-buffer-save-name crypt-buffer-encoding-type)
		  crypt-buffer-save-encoded)

    (if crypt-buffer-save-encoded
	;; We are going to save as encoded, we might turn off auto-saving.
	(progn
;; NEVER do this.  Turning off auto-saving is one thing.  But if there's
;; already an autosave for some other reason, what business does this
;; package have tampering with it?
;          ;; If an auto-save file already exists, then delete it.
;          (if (and (stringp buffer-auto-save-file-name)
;                   (file-exists-p buffer-auto-save-file-name))
;              (delete-file buffer-auto-save-file-name))
	  ;; Turn-off auto-saving if crypt-encoded-disable-auto-save non-nil.
	  (and crypt-encoded-disable-auto-save
	       auto-save-default
	       (progn
		 (auto-save-mode 0)
		 (if (eq crypt-encoded-disable-auto-save t)
		     (message "Auto-save off (in this buffer)")))))

      ;; We are not going to save as encoded, we will turn on auto-saving but
      ;; only if we are editing a file and the default says we should.
      (auto-save-mode (if (and auto-save-default buffer-file-name) 1 0)))

    ;; Have we toggled the mode?

    ;; If yes, then mark buffer as modified.  If not, then leave
    ;; buffer-modified flag alone.

    ;; The old code previously set the variable `set-buffer-modified-p' to a
    ;; value of t if there was a mode change and (unconditionally) to nil
    ;; if there was not a mode change.

    ;; Modification suggested by: Gerd Hillebrand <ggh@cs.brown.edu>.

    (if (not (eq oldval crypt-buffer-save-encoded))
	(set-buffer-modified-p t))))


;;;; Additional encryption functions

;; For Emacs V18 compatibility
(and (not (fboundp 'buffer-disable-undo))
     (fboundp 'buffer-flush-undo)
     (fset 'buffer-disable-undo 'buffer-flush-undo))

(defun crypt-read-string-no-echo (prompt &optional confirm)

  ;; Read a string from minibuffer, prompting with PROMPT, echoing periods.
  ;; Optional second argument CONFIRM non-nil means that the user will be
  ;; asked to type the string a second time for confirmation and if there is a
  ;; mismatch, the whole process is repeated.
  ;;
  ;;         Line editing keys are --
  ;;           C-h, DEL      rubout
  ;;           C-u, C-x      line kill
  ;;           C-q, C-v      literal next

  (catch 'return-value
    (save-excursion

      (let ((input-buffer (get-buffer-create (make-temp-name " *password*")))
	    char hold-password help-form kill-ring)

	(set-buffer input-buffer)
	;; Don't add to undo ring.
	(buffer-disable-undo input-buffer)

	(let ((cursor-in-echo-area t)
	      (echo-keystrokes 0))

	  (unwind-protect

	      ;; BODYFORM
	      ;; Repeat until we get a `throw'.
	      (while t
		(erase-buffer)
		(message "%s" prompt)	; avoid errors if "%" in prompt

		;; Read string.
		(while (not (memq (setq char (read-char)) '(?\C-m ?\C-j)))
		  (if (setq help-form
			    (cdr
			     (assq char
				   '((?\C-h . (delete-char -1))
				     (?\C-? . (delete-char -1))
				     (?\C-u . (delete-region 1 (point)))
				     (?\C-x . (delete-region 1 (point)))
				     (?\C-q . (quoted-insert 1))
				     (?\C-v . (quoted-insert 1))))))
		      (condition-case error-data
			  (eval help-form)
			(error t))
		    ;; Just a plain character - insert into password buffer.
		    (insert char))

		  ;; I think crypt-read-string-no-echo should echo asterisks.
		  ;; -- Jamie. How about periods like in ange-ftp? -- lrd
		  ;;
		  (message "%s%s" prompt (make-string (buffer-size) ?.)))

		;; Do we have to confirm password?
		(cond

		 ;; No confirmation requested - terminate.
		 ((not confirm)
		  (throw 'return-value (buffer-string)))

		 ;; Can we compare (confirm) password values yet?
		 (hold-password
		  (if (string= hold-password (buffer-string))
		      ;; The two passwords match - terminate.
		      (throw 'return-value hold-password)

		    ;; Mismatch - start over.
		    (progn
		      (message (concat prompt "[Mismatch. Start over]"))
		      (beep)
		      (sit-for 2)
		      (fillarray hold-password 0) ; destroy extra copy now
		      (setq hold-password nil))))

		 ;; Store password and read again.
		 (t
		  (setq hold-password (buffer-string))
		  (message (concat prompt "[Retype to confirm]"))
		  (sit-for 2))))

	    ;; UNWINDFORMS
	    ;; Clean up.
	    (set-buffer input-buffer)
	    (set-buffer-modified-p nil)
	    (buffer-disable-undo input-buffer) ; redundant, but why not be safe.
	    (widen)
	    (goto-char (point-min))
	    (while (not (eobp)) (delete-char 1) (insert "*")) ; destroy now
	    (kill-buffer input-buffer)))))))

(defun crypt-set-encryption-key (key &optional buffer)

  "Set the encryption KEY, a string, for current buffer or optionally BUFFER.
If buffer is in encrypted mode, then it is also marked as modified, since it
needs to be saved with the new key."

  (interactive
   (progn
     (barf-if-buffer-read-only)
     (list
      (if (eq crypt-encryption-type 'pgp-pub)
	  "dummy-key"
	(crypt-read-string-no-echo
	 (format "Encryption key for %s? [RET to ignore]: " (buffer-name))
	 crypt-confirm-password)))))

  ;; For security reasons we remove `(crypt-set-encryption-key "password")'
  ;; from the `command-history' list if called interactively.
  (if (interactive-p)
      (setq command-history (cdr command-history)))

  (or buffer (setq buffer (current-buffer)))

  (save-excursion
    (set-buffer buffer)
    (if (equal key crypt-buffer-encryption-key)
	(message "Key is identical to original, no change.")

      (progn
	;; #### Smash contents of old crypt-buffer-encryption-key string here?
	;; That wouldn't be ok if some other buffer held a pointer to it.
	(setq crypt-buffer-encryption-key key)

	;; Don't touch the modify flag unless we're in `(crypt-encrypted-mode)'.
	(if crypt-buffer-save-encrypted
	    (set-buffer-modified-p t))))))


;;;; Install hooks and mode indicators.

;;; Check if mode indicators are not already installed and then prepend them.
(and (not (assq 'crypt-buffer-save-encrypted minor-mode-alist))
     (setq minor-mode-alist (append crypt-minor-mode-alist minor-mode-alist)))

;;; Install the hooks.

;;; If add-hook isn't already defined overwrite it with our own.
;;; Note the `add-hook' function must take the optional APPEND argument.
(if (not (fboundp 'add-hook))
    ;; No add-hook found.
    ;; Use `add-hook' from GNU Emacs v19.
    (defun add-hook (hook function &optional append)
      "Add to the value of HOOK the function FUNCTION.
FUNCTION is not added if already present.
FUNCTION is added (if necessary) at the beginning of the hook list
unless the optional argument APPEND is non-nil, in which case
FUNCTION is added at the end.

HOOK should be a symbol, and FUNCTION may be any valid function.  If
HOOK is void, it is first set to nil.  If HOOK's value is a single
function, it is changed to a list of functions."
      (or (boundp hook) (set hook nil))
      ;; If the hook value is a single function, turn it into a list.
      (let ((old (symbol-value hook)))
	(if (or (not (listp old)) (eq (car old) 'lambda))
	    (set hook (list old))))
      (or (if (consp function)
	      ;; Clever way to tell whether a given lambda-expression
	      ;; is equal to anything in the hook.
	      (let ((tail (assoc (cdr function) (symbol-value hook))))
		(equal function tail))
	    (memq function (symbol-value hook)))
	  (set hook
	       (if append
		   (nconc (symbol-value hook) (list function))
		 (cons function (symbol-value hook)))))))

;;; Attach ourselves to the find-file-hooks and find-file-not-found-hooks.
(add-hook 'find-file-hooks 'crypt-find-file-hook)
(add-hook 'find-file-not-found-hooks 'crypt-find-file-hook)

;; Take care when appending to write-file-hook.  User's version of add-hook
;; may not have APPEND option.  If it fails then do it by hand.  I wish
;; everyone would upgrade - lrd 8/31/93.
(condition-case err
    (add-hook 'write-file-hooks 'crypt-write-file-hook t) ; *must* append this
  (error
   ;; Do it by hand.  Not as robust as `add-hook'.

   ;; Contributed by Ken Laprade <laprade@trantor.harris-atd.com>
   ;; Really should use some sort of add-hook - 16 Feb 93 - KCL
   (or (and (listp write-file-hooks) (not (eq (car write-file-hooks) 'lambda)))
       (setq write-file-hooks (list write-file-hooks)))

   (cond
    ((not (memq 'crypt-write-file-hook write-file-hooks))
     ;; make this hook last on purpose
     (setq write-file-hooks (append write-file-hooks
				    (list 'crypt-write-file-hook)))))))

;; In order that the tables and key-binding correctly reflect user's
;; preferences we add ourselves to the `after-init-hook' GNU Emacs v19 and
;; Lucid Emacs v 19.8 (or later) or `term-setup-hook' in Lucid Emacs v 19.7
;; (or earlier).  These are run *after* ~/.emacs and ../lisp/default.el are
;; loaded.  Unfortunately, v18 does not have `after-init-hook' and
;; `term-setup-hook' is just a single function.  It is a bit of a pain trying
;; to work our functions in properly without overwriting the user's value.
;; Therefore, we do nothing and hope they upgrade to v19 soon.

(cond ((boundp 'after-init-hook)
       ;; Must be running GNU Emacs v19 :->
       (add-hook 'after-init-hook 'crypt-rebuild-tables)
       (add-hook 'after-init-hook 'crypt-rebuild-minor-modes-alist)
       (add-hook 'after-init-hook 'crypt-bind-insert-file))

      ((and (string-match "^19" emacs-version) t)
       ;; Probably running Lucid Emacs v19.7 (or earlier) since it,
       ;; unfortunately, does not have `after-init-hook'.  Use
       ;; `term-setup-hook' instead and hope they upgrade to Lucid 19.8 or GNU
       ;; Emacs 19.
       (add-hook 'term-setup-hook 'crypt-rebuild-tables)
       (add-hook 'term-setup-hook 'crypt-rebuild-minor-modes-alist)
       (add-hook 'term-setup-hook 'crypt-bind-insert-file)))


;;; Code for conditionally decoding/decrypting an inserted file

(defvar crypt-bind-insert-file t
  "*t value means bind `crypt-insert-file' over `insert-file'.
If you wish to change this variable after crypt++ has been loaded then do
\\[crypt-bind-insert-file].")

(defvar crypt-auto-decode-insert nil
  "*t says decode/decrypt files that are inserted with `crypt-insert-file'.
nil says to ask before doing this.")

;;; Bind `crypt-insert-file' over wherever `insert-file' is bound?
(defun crypt-bind-insert-file ()
  "Bind `crypt-insert-file' in place of `insert-file' or reverse based on
`crypt-bind-insert-file'.  Part of `after-init-hook'."

  (interactive)

  (if (interactive-p)
      (setq crypt-bind-insert-file
	    (y-or-n-p "Bind crypt-insert-file over insert-file? ")))

  (if crypt-bind-insert-file
      (substitute-key-definition
       'insert-file 'crypt-insert-file (current-global-map))
    (substitute-key-definition
     'crypt-insert-file 'insert-file (current-global-map))))

;;; Now call it.
(crypt-bind-insert-file)

;;; crypt++ replacement for `insert-file'
(defun crypt-insert-file (filename)
  "Insert decoded/decrypted contents of file FILENAME into buffer after point.
Set mark after the inserted text.

This function is meant for the user to run interactively.
Don't call it from programs!  Use `insert-file-contents' instead.
\(Its calling sequence is different; see its documentation\).

This version will attempt to decrypt and/or decode file before inserting.
see variable `crypt-auto-decode-insert'."
  (interactive "fInsert file: ")
  (if (file-directory-p filename)
      (signal 'file-error (list "Opening input file" "file is a directory"
				filename)))
  (let ((tem (crypt-insert-file-contents filename))) ; use crypt++ to insert
    (push-mark (+ (point) (car (cdr tem))))))

;; Similar to `insert-file-contents' except decoding/decrypting of FILE
;; attempted.  See `crypt-insert-file' and `crypt-auto-decode-insert'
;;
(defun crypt-insert-file-contents (file)
  (let (temp-buffer
	temp-list
	(crypt-auto-decode-buffer crypt-auto-decode-insert)
	(orig-buffer (current-buffer)))

    ;; Create a temporary buffer and decode and decrypt it.
    (save-excursion

      ;; Temporary buffer, use the same name as the file to be inserted.
      (setq temp-buffer (generate-new-buffer (file-name-nondirectory file)))
      (set-buffer temp-buffer)

      ;; Original insert-file-contents - save list.
      (setq temp-list (insert-file-contents file nil))

      ;; Make temp-buffer unmodified.
      (set-buffer-modified-p nil)

      ;; Need to set buffer name to file name for crypt++.
      (setq buffer-file-name file)

      ;; Decode and decrypt, if necessary.
      (crypt-find-file-hook)

      ;; Find the length of the file to be inserted. `insert-file-contents'
      ;; returns it for the original encoded/encrypted file.
      (setcdr temp-list (cons (buffer-size) ()))

      ;; Now insert temp-buffer into original buffer.
      (set-buffer orig-buffer)
      (insert-buffer temp-buffer)

      ;; Kill the temporary buffer.
      (kill-buffer temp-buffer))

    ;; Return modified list from `insert-file-contents'.
    temp-list))


;;;; BUG REPORTS

;;; This section is provided for reports.
;;; Using Barry A. Warsaw's reporter.el

(defconst crypt-version "2.92"
  "Revision number of crypt++.el -- handles compressed and encrypted files.
Type \\[crypt-submit-report] to send a bug report.  Available via anonymous
ftp at ftp://ftp.cs.umb.edu/pub/misc/crypt++.el")

(defconst crypt-help-address
  "kb@cs.umb.edu"
  "Address(es) accepting submission of reports on crypt++.el.")

(defconst crypt-maintainer "Karl"
  "First name(s) of people accepting submission of reports on crypt++.el.")

(defconst crypt-file "crypt++.el"
  "Name of file containing emacs lisp code.")

(defconst crypt-variable-list
  (list 'shell-file-name ; These
	'load-path       ; are
	'exec-path       ; useful.
	'crypt-encryption-type
	'crypt-encryption-file-extension
	'crypt-never-ever-decrypt
	'crypt-auto-write-buffer-encrypted
	'crypt-confirm-password
	'crypt-encrypted-disable-auto-save
	'crypt-auto-decode-buffer
	'crypt-auto-write-buffer
	'crypt-query-if-interactive
	'crypt-no-extension-implies-plain
	'crypt-freeze-vs-fortran
	'crypt-compact-vs-C++
	'crypt-ignored-filenames
	'crypt-default-encoding
	'crypt-encoded-disable-auto-save
	'crypt-bind-insert-file
	'crypt-auto-decode-insert
	'crypt-encoding-alist
	'crypt-encryption-alist
	)
  "List of variables to be appended to reports sent by `crypt-submit-report.'")

(defun crypt-submit-report ()
  "Submit via reporter.el a bug report on program.  Send report on `crypt-file'
version `crypt-version,' to `crypt-maintainer' at address `crypt-help-address'
listing variables `crypt-variable-list' in the message."
  (interactive)

  ;; In case we can't find reporter...
  (condition-case err
      (progn
	;; Get it if we can.
	(require 'reporter)

	(reporter-submit-bug-report
	 crypt-help-address                     ; address
	 (concat crypt-file " " crypt-version)  ; pkgname
	 crypt-variable-list                    ; varlist
	 nil nil                                ; pre-hooks and post-hooks
	 (concat "Yo! " crypt-maintainer ","))) ; salutation

    ;; ...fail gracefully.
    (error
     (beep)

     ;; Do they have ange-ftp?
     (if (and (featurep 'ange-ftp)
	      (y-or-n-p (concat "Sorry, reporter.el not found.  "
				"Can I ange-ftp it for you? ")))

	 ;; Yes.  Then Ange-ftp a copy.
	 (let ((ange-ftp-generate-anonymous-password t))
	   ;; Might want to use the elisp archive official site?  But
	   ;; then it would have to be uncompressed, etc. Ick!
	   (find-file-other-window
"/anonymous@archive.cis.ohio-state.edu:/pub/gnu/emacs/elisp-archive/misc/reporter.el.Z")
	   (eval-current-buffer)
	   (message (concat "Save reporter.el somewhere in `load-path' "
			    "and try again.")))

       ;; No ange-ftp.
       (message "Sorry, reporter.el not found.")
       (sit-for 3)
       (message "Get it from archive.cis.ohio-state.edu.")))))

;;; Provide the many forms of this package.
(provide 'crypt+pgp-pub)
(provide 'crypt++)
(provide 'crypt)

;;; crypt++.el ends here.
