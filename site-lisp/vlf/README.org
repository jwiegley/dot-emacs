* View Large Files

Emacs minor mode that allows viewing, editing, searching and comparing
large files in batches, trading memory for processor time.  Batch size
can be adjusted on the fly and bounds the memory that is to be used
for operations on the file.  This way multiple large files (like
terabytes or whatever) can be instantly and simultaneously accessed
without swapping and degraded performance.

This is development version of the GNU ELPA [[https://elpa.gnu.org/packages/vlf.html][VLF]] package.  Here's what
it offers in a nutshell:

- automatic adjustment of batch size for optimal performance and
  responsiveness
- regular expression search and replace over whole file
- [[http://www.emacswiki.org/emacs/OccurMode][Occur]] like indexing
- by batch [[http://www.emacswiki.org/emacs/EdiffMode][Ediff]] comparison
- automatic scrolling of batches
- chunk editing (save is immediate if size hasn't changed, done in
  constant memory determined by current batch size otherwise)
- options to jump to beginning, end or arbitrary file chunk
- proper dealing with multibyte encodings
- smooth integration with [[http://www.emacswiki.org/emacs/HexlMode][hexl-mode]], just turn it on and the HEX
  editing will work in batches just the same
- works with [[http://www.emacswiki.org/emacs/TrampMode][TRAMP]] so accessing network files is fine and quick
- newly added content is acknowledged if file has changed size
  meanwhile
- as it's a minor mode, font locking and functionality of the
  respective major mode and other minor modes is also present
- can be added as option to automatically open large files

GNU Emacs 23 and 24 are supported.

* Overview and tips

M-x vlf PATH-TO-FILE

** Unicode

Emacs' Unicode support is leveraged so you'll not see bare bytes but
characters decoded as if file is normally opened.  This holds for
editing, search, indexing and comparison.

** 32-bit GNU Emacs

Regular Emacs integers are used, so if you use 32-bit Emacs without
bignum support, *VLF* will not work with files over 512 MB (maximum
integer value).

* Detail usage

** Applicability

To have *vlf* offered as choice when opening large files:

#+BEGIN_SRC emacs-lisp
  (require 'vlf-setup)
#+END_SRC

You can control when *vlf-mode* is invoked or offered with the
*vlf-application* customization option.  By default it will offer
*VLF* when opening large files.  There are also options to never use
it (you can still call *vlf* command explicitly); to use it without
asking for large files or to invoke it on all files.  Here's example
setup such that *vlf-mode* automatically launches for large files:

#+BEGIN_SRC emacs-lisp
  (custom-set-variables
   '(vlf-application 'dont-ask))
#+END_SRC

*** Disable for specific mode

To disable automatic usage of *VLF* for a major mode, add it to
*vlf-forbidden-modes-list*.

*** Disable for specific function

To disable automatic usage of *VLF* for a function, for example named
*func* defined in file *file.el*:

#+BEGIN_SRC emacs-lisp
  (vlf-disable-for-function func "file")
#+END_SRC

** Keymap

All *VLF* operations are grouped under the *C-c C-v* prefix by
default.  Here's example how to add another prefix (*C-x v*):

#+BEGIN_SRC emacs-lisp
  (eval-after-load "vlf"
    '(define-key vlf-prefix-map "\C-xv" vlf-mode-map))
#+END_SRC

** Overall position indicators

To see which part of the file is currently visited and how many
batches there are in overall (using the current batch size), look at
the VLF section in the mode line, file size is also there.

** Batch size control

By default *VLF* gathers statistics over how primitive operations
perform over file and gradually adjusts batch size for better user
experience.  Operations involving multiple batches are tuned more
adventurously.  Overall the more jumping around, searching, indexing,
the better performance should get.

The *vlf-tune-max* option specifies maximum size in bytes a batch
could eventually get while tuning.

Profiling and tuning can be disabled by:

#+BEGIN_SRC emacs-lisp
  (custom-set-variables
     '(vlf-tune-enabled nil))
#+END_SRC

Or set *vlf-tune-enabled* to '*stats* to profile but not change batch
size.

Use *M-x vlf-set-batch-size* to change batch size and update chunk
immediately.  Default size offered is the best according to tune
statistics so far.

*C-c C-v +* and *C-c C-v -* control current batch size by factors
of 2.

** Move around

Scrolling automatically triggers move to previous or next chunk at the
beginning or end respectively of the current one.

*C-c C-v n* and *C-c C-v p* move batch by batch.  With positive
prefix argument they move prefix number of batches.  With negative -
append prefix number of batches.

*C-c C-v SPC* displays batch starting from current point.

*C-c C-v [* and *C-c C-v ]* take you to the beginning and end of file
respectively.

*C-c C-v j* jumps to particular batch number.

** Follow point

Continuous chunk recenter around point in current buffer can be
toggled with *C-c C-v f*.

** Search and/or replace whole file

*C-c C-v s* and *C-c C-v r* search forward and backward respectively
over the whole file, batch by batch.  *C-c C-v %* does search and
query replace saving intermediate changes.

** Occur over whole file

*C-c C-v o* builds index over whole file for given regular expression
just like *M-x occur*.  Note that even if you prematurely stop it with
*C-g*, it will still show what's found so far.

Result buffer uses *vlf-occur-mode* which allows to optionally open
new *VLF* buffer on jump to match (using *C-u* before hitting RET or
*o*), thus having multiple simultaneous views of the same file.  Also
results can be serialized to file for later reuse.

** Jump to line

*C-c C-v l* jumps to given line in file.  With negative argument,
lines are counted from the end of file.

** Edit and save

If editing doesn't change size of the chunk, only this chunk is saved.
Otherwise the remaining part of the file is adjusted batch by batch.
*vlf-save-in-place* customization option controls if temporary file
should be used in such case.

** By batch Ediff

Use *M-x vlf-ediff-files* and *M-x vlf-ediff-buffers* to compare
files/buffers batch by batch (batch size is queried in case of files
or taken from the first buffer in case of buffers).  Moving after the
last difference in current chunk searches for following one with
difference.  The other way around if looking for difference before the
first one.

* Extend

** Move hooks

A couple of hooks are run whenever updating chunk:
*vlf-before-chunk-update-hook* and *vlf-after-chunk-update-hook*.

** Batch move hooks

Some operations may trigger multiple chunk moves.  There are a couple
of hooks that run in such cases: *vlf-before-batch-functions* and
*vlf-after-batch-functions*.  They are passed one argument which
specifies type of operation that runs.  Possible values are the
symbols: *write*, *ediff*, *occur*, *search* and *goto-line*.
