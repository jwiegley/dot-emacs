;;; DO NOT MODIFY THIS FILE
(if (featurep 'x-symbol-autoloads) (error "Already loaded"))

;;;### (autoloads nil "_pkg" "lisp/_pkg.el")

(if (fboundp 'package-provide) (package-provide 'x-symbol :version 4.5 :type 'regular))

;;;***

;;;### (autoloads (x-symbol-initialize x-symbol-register-language x-symbol-fontify turn-on-x-symbol-conditionally x-symbol-mode x-symbol-key-autoload x-symbol-auto-mode-suffixes) "x-symbol-hooks" "lisp/x-symbol-hooks.el")

(autoload 'x-symbol-auto-mode-suffixes "x-symbol-hooks" "\
Return REGEXPs of three-value elements in `auto-mode-alist'.
These REGEXPs are added to SUFFIXES." nil nil)

(autoload 'x-symbol-key-autoload "x-symbol-hooks" "\
Initialize package x-symbol and use the keys for this command again.
Package x-symbol and the functions in `x-symbol-load-hook' should
re-bind all key-sequence which invoke this command.  You should provide
a prefix argument ARG to this command if `x-symbol-auto-key-autoload' is
nil." t nil)

(defalias 'x-symbol-map-autoload 'x-symbol-key-autoload)

(autoload 'x-symbol-mode "x-symbol-hooks" "\
Toggle X-Symbol mode.
If ARG is a cons, e.g., when \\[x-symbol-mode] is preceded by one or
more \\[universal-argument]'s with no digits, turn on X-Symbol mode
conditionally, see MODE-ON in `x-symbol-auto-mode-alist'.  Otherwise,
turn X-Symbol mode on if ARG is positive, else turn it off.  If some
X-Symbol specific local variables are not buffer-local, set them to
reasonable values according to `x-symbol-buffer-mode-alist' and
`x-symbol-auto-mode-alist'.

Turning X-Symbol mode on requires a valid `x-symbol-language' and also
decodes tokens if the mode was turned off before, see
\\[x-symbol-decode].  Turning X-Symbol mode off also encodes x-symbol
characters if the mode was turned on before, see \\[x-symbol-encode].
If argument INIT is non-nil, the old mode status is assumed to be off." t nil)

(autoload 'turn-on-x-symbol-conditionally "x-symbol-hooks" "\
Turn on x-symbol mode conditionally, see `x-symbol-mode'.
Call `x-symbol-mode' with a cons for ARG and a non-nil INIT.  Used in
`hack-local-variables-hook'." nil nil)

(autoload 'x-symbol-fontify "x-symbol-hooks" "\
Re-fontify region between BEG and END." t nil)

(autoload 'x-symbol-register-language "x-symbol-hooks" "\
Register token language LANGUAGE.
FEATURE is a feature which `provide's LANGUAGE.  MODES are major modes
which typically use LANGUAGE.  Using LANGUAGE's accesses will initialize
LANGUAGE, see `x-symbol-language-value'." nil nil)

(autoload 'x-symbol-initialize "x-symbol-hooks" "\
Initialize package X-Symbol.
See variable `x-symbol-initialize' and function `x-symbol-after-init'.
Also allocate colormap, see `x-symbol-image-colormap-allocation'.
Unless optional argument ARG is non-nil, do not initialize package
X-Symbol twice." t nil)

;;;***

;;;### (autoloads (x-symbol-image-editor x-symbol-image-delete-extents x-symbol-image-after-change-function x-symbol-image-parse-buffer) "x-symbol-image" "lisp/x-symbol-image.el")

(autoload 'x-symbol-image-parse-buffer "x-symbol-image" "\
*Parse buffer to find image insertion commands.
Parse buffer to display glyphs at the end of image insertion commands.
Image files are converted to \"image cache files\" with images not
bigger than `x-symbol-image-max-width' and `x-symbol-image-max-height'
having a image format XEmacs understands.  The conversion is done by a
program determined by `x-symbol-image-converter', currently you need
\"convert\" from ImageMagick.  To make this conversion fast, we use
asynchronous processes and two cache hierarchies:

 * Memory cache (`x-symbol-image-memory-cache'): buffer-local alist
   FILE.eps -> GLYPH, see also `x-symbol-image-use-remote'.
 * File cache: the image cache file, mentioned above, are kept, see also
   `x-symbol-image-update-cache', which is shadowed by a non-nil
   UPDATE-CACHE and `x-symbol-image-cache-directories'.

When the mouse is over an image insertion command, it is highlighted.
button2 starts an image editor, see `x-symbol-image-editor-alist'.
button3 pops up a menu, see `x-symbol-image-menu'.

The image insertion commands are recognized by keywords in the language
access `x-symbol-image-keywords' whose value have the form
  (IMAGE-REGEXP KEYWORD ...)
IMAGE-REGEXP should match all images files and is used to initialize the
buffer local memory cache, see `x-symbol-image-init-memory-cache'.

Each KEYWORD looks like (REGEXP [FUNCTION] ARG...).  Image insertion
commands matched by REGEXP are highlighted.  FUNCTION, which defaults to
`x-symbol-image-default-file-name', is called with ARGs to get the file
name of the corresponding image file.  If FUNCTION returns nil, the
command is not highlighted.

Relative image file names are expanded in the directory returned by the
function in the language access `x-symbol-master-directory', value nil
means function `default-directory'.  Implicitly relative image file
names are searched in a search path, see `x-symbol-image-use-remote'." t nil)

(autoload 'x-symbol-image-after-change-function "x-symbol-image" "\
Function in `after-change-functions' for image insertion commands." nil nil)

(autoload 'x-symbol-image-delete-extents "x-symbol-image" "\
Delete x-symbol image extents covering text between BEG and END.
See also `x-symbol-image-buffer-extents'." nil nil)

(autoload 'x-symbol-image-editor "x-symbol-image" "\
Start image editor for the image file FILE used in BUFFER.
If BUFFER is nil, just return string describing the command.  See
`x-symbol-image-editor-alist' and `x-symbol-image-current-marker'." t nil)

;;;***

;;;### (autoloads (x-symbol-tex-auto-coding-alist) "x-symbol-tex" "lisp/x-symbol-tex.el")

(autoload 'x-symbol-tex-auto-coding-alist "x-symbol-tex" "\
Find encoding in file `x-symbol-tex-coding-master'.
For ALIST and LIMIT, see `x-symbol-auto-coding-alist'." nil nil)

;;;***

;;;### (autoloads (x-symbol-variable-interactive) "x-symbol-vars" "lisp/x-symbol-vars.el")

(autoload 'x-symbol-variable-interactive "x-symbol-vars" "\
Provide interactive specification for `set-variable'.
VAR's options has been defined with `x-symbol-define-user-options'." nil nil)

;;;***

;;;### (autoloads (x-symbol-init-input x-symbol-rotate-key x-symbol-modify-key x-symbol-grid x-symbol-read-language x-symbol-init-language-interactive x-symbol-mode-internal x-symbol-auto-8bit-search x-symbol-auto-coding-alist x-symbol-unalias x-symbol-encode x-symbol-encode-recode x-symbol-decode x-symbol-decode-recode x-symbol-encode-all x-symbol-encode-string x-symbol-decode-single-token x-symbol-decode-all x-symbol-decode-region x-symbol-package-reply-to-report x-symbol-package-bug x-symbol-package-info x-symbol-package-web x-symbol-translate-to-ascii) "x-symbol" "lisp/x-symbol.el")

(autoload 'x-symbol-translate-to-ascii "x-symbol" "\
Translate STRING to an ascii string.
Non-ascii characters in STRING are converted to charsyms.  Their ascii
representation is determined by:

 * If CHARSYM is a key in `x-symbol-charsym-ascii-alist', use its ASCII.
 * Charsym is defined in the table to have an ascii representation, see
   ASCII in `x-symbol-init-cset'.
 * Compute ascii representation according to the CHARSYM's GROUP,
   SUBGROUP and `x-symbol-charsym-ascii-groups'.
 * Use \"\" otherwise." nil nil)

(autoload 'x-symbol-package-web "x-symbol" "\
Ask a WWW browser to load URL `x-symbol-package-url'." t nil)

(autoload 'x-symbol-package-info "x-symbol" "\
Read documentation for package X-Symbol in the info system." t nil)

(autoload 'x-symbol-package-bug "x-symbol" "\
Send a bug/problem report to the maintainer of package X-Symbol.
Please try to contact person in `x-symbol-installer-address' first.
Normal reports are sent without prefix argument ARG.

If you are sure that the problem cannot be solved locally, e.g., by
contacting the person who has installed package X-Symbol, use prefix
argument 2 to send the message to `x-symbol-maintainer-address'.

If your message has nothing to do with a problem or a bug, use prefix 9
to send a short message to `x-symbol-maintainer-address'." t nil)

(autoload 'x-symbol-package-reply-to-report "x-symbol" "\
Reply to a bug/problem report not using \\[x-symbol-package-bug]." t nil)

(autoload 'x-symbol-decode-region "x-symbol" "\
Decode all tokens between BEG and END.
Make sure that X-Symbol characters are correctly displayed under
XEmacs/no-Mule even when font-lock is disabled." nil nil)

(autoload 'x-symbol-decode-all "x-symbol" "\
Decode all tokens in buffer to characters.
Use executables for decoding if buffer is larger than EXEC-THRESHOLD
which defaults to `x-symbol-exec-threshold'.  Before decoding, decode
8bit characters in CODING which defaults to `x-symbol-coding'." nil nil)

(autoload 'x-symbol-decode-single-token "x-symbol" nil nil nil)

(autoload 'x-symbol-encode-string "x-symbol" nil nil nil)

(autoload 'x-symbol-encode-all "x-symbol" "\
Encode all characters in buffer to tokens.
Use executables for decoding if buffer is larger than EXEC-THRESHOLD
which defaults to `x-symbol-exec-threshold'.  If CODING is non-nil, do
not encode 8bit characters in CODING.  Otherwise, do not encode 8bit
characters in `x-symbol-coding' or `x-symbol-default-coding' if
`x-symbol-8bits' is non-nil.  If BUFFER is non-nil, copy contexts
between START and END to BUFFER, make BUFFER current and do conversion
there.  If BUFFER is non-nil, START and END must be buffer positions or
START is a string, see kludgy feature of `write-region'." nil nil)

(autoload 'x-symbol-decode-recode "x-symbol" "\
Decode all tokens in active region or buffer to characters.
If called interactively and if the region is active, BEG and END are the
boundaries of the region.  BEG and END default to the buffer boundaries.
8bit characters are treated according to `x-symbol-coding'.  See also
commands `x-symbol-encode' and `x-symbol-mode'.

Note that in most token languages, different tokens might be decoded to
the same character, e.g., \\neq and \\ne in `tex', &Auml; and &#196;
in `sgml'!" t nil)

(autoload 'x-symbol-decode "x-symbol" nil t nil)

(autoload 'x-symbol-encode-recode "x-symbol" "\
Encode all characters in active region or buffer to tokens.
If called interactively and if the region is active, BEG and END are the
boundaries of the region.  BEG and END default to the buffer boundaries.
Variables `x-symbol-8bits' and `x-symbol-coding' determine whether to
encode 8bit characters.  See also commands `x-symbol-decode' and
`x-symbol-mode'." t nil)

(autoload 'x-symbol-encode "x-symbol" nil t nil)

(autoload 'x-symbol-unalias "x-symbol" "\
Resolve all character aliases in active region or buffer.
A char alias is a character which is also a character in a font with
another registry, e.g., `adiaeresis' is defined in all supported latin
fonts.  XEmacs distinguish between these four characters.  In package
x-symbol, one of them, with `x-symbol-default-coding' if possible, is
supported by the input methods, the other ones are char aliases to the
supported one.  The character and all the aliases are represented by the
same charsym.  The info in the minibuffer displays char aliases, you can
resolve a single character before point with \\[x-symbol-modify-key].

8bit characters in files with a file coding `x-symbol-coding' other than
`x-symbol-default-coding' are converted to the \"normal\" form.  E.g.,
if you have a latin-1 font by default, the `adiaeresis' in a latin-2
encoded file is a latin-1 `adiaeresis' in the buffer.  When saving the
buffer, its is again the right 8bit character in the latin-2 encoded
file.  But note: CHAR ALIASES ARE NOT ENCODED WHEN SAVING THE FILE.
Invoke this command before, if your buffers have char aliases!  Seven
positions in latin-3 fonts are not used, the corresponding 8bit bytes in
latin-3 encoded files are not changed.

In normal cases, buffers do not have char aliases: in XEmacs/Mule, this
is only possible if you copy characters from buffers with characters
considered as char aliases by package x-symbol, e.g., from the Mule file
\"european.el\".  In XEmacs/no-Mule, this is only possible if you use
commands like `\\[universal-argument] 2 3 4'.

The reason why package x-symbol does not support all versions of
`adiaeresis'es:
 * It is confusing to the user to choose among four similar characters.
 * These four versions are not distinguished in Unicode.
 * There are not different tokens for them, neither in the token
   language \"TeX macro\", nor \"SGML entity\"." t nil)

(autoload 'x-symbol-auto-coding-alist "x-symbol" "\
Return first match for ALIST in buffer limited by LIMIT.
Each element in ALIST looks like
  (REGEXP . RESULT) or (REGEXP MATCH (KEY . RESULT)...)

Search forward from the start of the buffer for a match with REGEXP.
With the first form, return RESULT.  With the second form, return RESULT
where KEY is equal to the MATCH'th regexp group of the match." nil nil)

(autoload 'x-symbol-auto-8bit-search "x-symbol" nil nil nil)

(autoload 'x-symbol-mode-internal "x-symbol" "\
Setup X-Symbol mode according to buffer-local variables.
If CONVERSION is non-nil, do conversion with EXEC-THRESHOLD.  See
command `x-symbol-mode' for details." nil nil)

(autoload 'x-symbol-init-language-interactive "x-symbol" "\
Initialize token language LANGUAGE.
See `x-symbol-init-language'." t nil)

(autoload 'x-symbol-read-language "x-symbol" "\
Read token language in the minibuffer with completion.
Use PROMPT in minibuffer.  If the inserted string is empty, use DEFAULT
as return value.  If PREDICATE non-nil, only match languages if
PREDICATE with argument (NAME . LANGUAGE) returns non-nil." nil nil)

(autoload 'x-symbol-grid "x-symbol" "\
Displays characters in a grid-like fashion for mouse selection.
Display global or language dependent grid, see `x-symbol-local-grid'.
See `x-symbol-list-mode' for key and mouse bindings.  Without optional
argument ARG and non-nil `x-symbol-grid-reuse', just popup old grid
buffer if it already exists, but is not displayed.  Store window
configuration current before the invocation if `x-symbol-temp-grid' is
non-nil, see `x-symbol-list-restore'." t nil)

(autoload 'x-symbol-modify-key "x-symbol" "\
Modify key for input method CONTEXT.
If character before point is a char alias, resolve alias, see
\\[x-symbol-unalias].  If character before point is a character
supported by package x-symbol, replace it by the next valid character in
the modify-to chain.

Otherwise replace longest context before point by a character which
looks similar to it.  See also \\[x-symbol-rotate-key] and
`x-symbol-electric-input'.  If called interactively and if the region is
active, restrict context to the region between BEG and END." t nil)

(autoload 'x-symbol-rotate-key "x-symbol" "\
Rotate key for input method CONTEXT.
If character before point is a char alias, resolve alias, see
\\[x-symbol-unalias].  If character before point is a character
supported by package x-symbol, replace it by the next valid character in
the rotate-to chain.  With optional prefix argument ARG, the
\"direction\" of the new character should be according to ARG and
`x-symbol-rotate-prefix-alist'.

Otherwise replace longest context before point by a character which
looks similar to it, assuming an additional context suffix
`x-symbol-rotate-suffix-char'.  See also \\[x-symbol-modify-key] and
`x-symbol-electric-input'.  If called interactively and if the region is
active, restrict context to the region between BEG and END." t nil)

(autoload 'x-symbol-init-input "x-symbol" "\
Initialize all input methods for all charsyms defined so far.
Run `x-symbol-after-init-input-hook' afterwards.  This function should
be called if new charsyms have been added, but not too often since it
takes some time to complete.  Input methods TOKEN and READ-TOKEN are
defined with `x-symbol-init-language'.

As explained in the docstring of `x-symbol-init-cset', charsyms are
defined with \"character descriptions\" which consist of different
\"aspects\" and \"contexts\", which can also be inherited from a
\"parent\" character.  All characters which are connected with parents,
form a \"component\".  Aspects and contexts are used to determine the
Modify-to and Rotate-to chain for characters, the contexts for input
method CONTEXT and ELECTRIC, the key bindings, and the position in the
MENU and the GRID.

If a table entry of a charsym does not define its own contexts, they are
the same as the contexts of the charsym in an earlier position in the
\"modify chain\" (see below), or the contexts of the first charsym with
defined contexts in the modify chain.  The modify context of a charsym
is the first context.

Characters in the same component whose aspects only differ by their
\"direction\" (east,...), a key in `x-symbol-rotate-aspects-alist', are
circularly connected by \"rotate-to\".  The sequence in the \"rotate
chain\" is determined by rotate scores depending on the values in the
rotate aspects.  Charsyms with the same \"rotate-aspects\" are not
connected (charsyms with the smallest modify scores are preferred).

Characters in the same components whose aspects only differ by their
\"size\" (big,...), \"shape\" (round, square,...) and/or \"shift\" (up,
down,...), keys in `x-symbol-modify-aspects-alist', are circularly
connected by \"modify-to\", if all their modify contexts are used
exclusively, i.e., no other modify chain uses any of them.  The sequence
in the \"modify chain\" is determined by modify scores depending on the
values in the modify aspects and the charsym score.

Otherwise, the \"modify chain\" is divided into modify subchains, which
are those charsyms sharing the same modify context.  All modify
subchains using the same modify context, build a \"horizontal chain\"
whose charsyms are circularly connected by \"modify-to\".

We build a \"key chain\" for all contexts (not just modify contexts),
consisting of all charsyms (sorted according to modify scores) having
the context.  Input method CONTEXT modifies the context to the first
charsym in the \"key chain\".

If there is only one charsym in the key chain, `x-symbol-compose-key'
plus the context inserts the charsym.  Otherwise, we use a digit (1..9,
0) as a suffix for each charsym in the key chain.
`x-symbol-compose-key' plus the context plus the optional suffix inserts
the charsym." nil nil)

;;;***

(provide 'x-symbol-autoloads)
