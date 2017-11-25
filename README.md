# Fence Edit #

Fence Edit provides a convenient way to edit the contents of "fenced code
blocks" used by markup formats like Markdown in a dedicated window set to the
major mode appropriate for its language.

Simply bind a key to `fence-edit-code-at-point` and call it from within any code
block matching one of the patterns described in `fence-edit-blocks`.

Based on a language symbol extracted from the fence block pattern, the
corresponding mode in `fence-edit-lang-modes` will be set for the edit buffer.

## Configuration ##

The key configurable components in Fence Edit are available through the
`customize` facility within Emacs, though of course you can also set the
appropriate variables in your configuration scripts if you so desire.

Fundamentally, Fence Edit provides a way to recognize a block of code "fenced"
by patterns defined in regular expressions and to associate that with a language
symbol. The language symbol, in turn, is associated with a mode name, and the
code (without its fencing text) will be edited in a split window using that
mode.

This is useful to edit code appearing in Markdown files, for example, which I
use to author blog posts. It is very useful to have the syntax highlighting,
indenting, and other helpful features of the language's major mode when editing
custom code for blog posts.

Since the code block "fence" patterns are configurable, there is no limitation
to how you can use Fence Edit.

## Essential Usage ##

When `fence-edit-code-at-point` is called, it attempts to find a code block
around point using the patterns in `fence-edit-blocks`. If one is found, a new
window is opened containing the code between the fences, set to the major mode
activated by the language symbol with `-mode` appended, or, for languages
without a direct `-mode` suffix mode, the mode defined in
`fence-edit-lang-modes`.

Within the code editing window, you can press `C-c '` to copy the edited code
back to its original location, or `C-c C-k` to discard your edits. In both
situations, the new window is destroyed and you are returned to a convenient
cursor location.
