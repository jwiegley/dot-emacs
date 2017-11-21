shackle
=======

.. image:: https://raw.githubusercontent.com/wasamasa/shackle/master/img/shackle.gif

About
-----

``shackle`` gives you the means to put an end to popped up buffers not
behaving they way you'd like them to.  By setting up simple rules you
can for instance make Emacs always select help buffers for you or make
everything reuse your currently selected window.

Installation
------------

Install from `Marmalade <https://marmalade-repo.org/>`_ or `MELPA
(stable) <http://melpa.org/>`_ via ``M-x package-install RET shackle``
or download ``shackle.el``, place it into a suitable location such as
``~/.emacs.d/vendor/`` and add the following to your init file:

.. code:: elisp

    (add-to-list 'load-path (expand-file-name "~/.emacs.d/vendor/"))

Usage
-----

First you need to customize ``shackle-rules``, this can be done via
``M-x customize-group RET shackle`` or in your init file.

As the name of the variable suggests, it's a list of rules.  Each rule
consists of a condition and a set of key-value combinations that tell
what to do with the buffer in question.

The condition can be either a symbol, a string or a list of either.  A
symbol is interpreted as the major mode of the buffer to match, a
string as the name of the buffer (which can be turned into regexp
matching by using the ``:regexp`` key with a value of ``t`` in the
key-value part) and a list groups either symbols or strings (as
described earlier) while requiring at least one element to match.
It's possible to supply a custom predicate by using ``(:custom
function)`` as condition.  The predicate is called with the buffer to
be displayed and is interpreted as a match given a non-nil return
value.

The following key-value pairs are available:

- ``:select`` and ``t``:

  Select the popped up window.  The ``shackle-select-reused-windows``
  option makes this the default for windows already displaying the
  buffer.

- ``:inhibit-window-quit`` and ``t``:

  Special buffers usually have ``q`` bound to ``quit-window`` which
  commonly buries the buffer *and* deletes the window.  This option
  inhibits the latter which is especially useful in combination with
  ``:same`` (as ``q`` deleting the reused window is weird behaviour
  for more than one visible window), but can also be used with other
  keys like ``:other`` as well.

- ``:custom`` and a function name or lambda expression:

  Override with a custom action.  The specified function is called
  with ``BUFFER-OR-NAME``, ``ALIST`` and ``PLIST`` as argument.  It's
  possible to reuse existing actions as defined in the sources, but
  dispatch based on more specific conditions such as the currently
  opened windows or selected buffer.

- ``:ignore`` and ``t``:

  Skip handling the display of the buffer in question.  Keep in mind
  that while this avoids switching buffers, popping up windows and
  displaying frames, it does not inhibit what may have preceded this
  command, such as the creation or update of the buffer to be
  displayed.

- ``:other`` and ``t``:

  Reuse the window ``other-window`` would select if there's more than
  one window open, otherwise pop up a new window.  When used in
  combination with the ``:frame`` key, do the equivalent with
  ``other-frame`` or a new frame.

- ``:same`` and ``t``:

  Display buffer in the current window.

- ``:popup`` and ``t``:

  Pop up a new window instead of displaying the buffer in the current
  one.

- ``:align`` and ``'above``, ``'below``, ``'left``, ``'right``, or
  ``t`` or a function:

  Align a new window at the respective side of the current frame or
  with the default alignment (customizable with
  ``shackle-default-alignment``) by splitting the root window.  If a
  function is specified, it is called with zero arguments and must
  return any of the above alignments.

- ``:size`` and number greater than zero:

  Aligned window use a default ratio of 0.5 to split up the original
  window in half (customizable with ``shackle-default-size``), the
  ratio can be changed on a per-case basis by providing a different
  floating point value between 0 and 1.  A value of 0.33 for example
  would make it occupy a third of the original window's size.
  Alternatively you can use an integer value of 1 or greater to
  display a window of the specified width or height instead.

- ``:frame`` and ``t``:

  Pop buffer to a frame instead of a window.

A default rule can be set up by customizing ``shackle-default-rule``.
Its format follows the plist as used by ``shackle-rules`` and the
default rule is used in case none of the rules in ``shackle-rules``
yield a match.  To have an exception to the default rule, you can use
the condition of your choice and either don't list the key-value pair
at all, use a different value (like ``nil`` for the keys taking
boolean values) or use a placeholder key with any value (like
``:noselect`` instead of ``:select``).  This is merely done to clearly
indicate the purpose of the respective rule, not following this
recommendation is another fine option.

Once you're done customizing ``shackle-rules``, use ``M-x
shackle-mode`` to enable ``shackle`` interactively.  To enable it
automatically on startup, add ``(shackle-mode)`` to your init file.

Grammar
-------

The above section expressed as EBNF:

.. code::

    RULES = "(" , { RULE } , ")" .
    RULE = "(" , CONDITION , PLIST , ")" .
    DEFAULT_RULE = "(" , PLIST , ")" .

    CONDITION = SIMPLE_CONDITION | LIST_CONDITION | FUNCTION_CONDITION .
    SIMPLE_CONDITION = SYMBOL | STRING .
    LIST_CONDITION = "(" , { SIMPLE_CONDITION } , ")" .
    FUNCTION_CONDITION = "(:custom" , FUNCTION , ")" .
    T_OR_NIL = "t" | "nil" .

    PLIST = "(" , [ ":regexp" , T_OR_NIL ] , ACTIONS , ")" .
    ACTIONS = EXCLUSIVE_ACTION , [ OPTIONAL_ACTIONS ] .

    EXCLUSIVE_ACTION = CUSTOM_ACTION | IGNORE_ACTION | OTHER_ACTION | POPUP_ACTION | SAME_ACTION | ALIGN_ACTION | FRAME_ACTION .
    CUSTOM_ACTION = ":custom" , FUNCTION .
    IGNORE_ACTION = ":ignore" , T_OR_NIL .
    OTHER_ACTION = ":other" , T_OR_NIL , [":frame" , T_OR_NIL] .
    POPUP_ACTION = ":popup" , T_OR_NIL .
    SAME_ACTION = ":same" , T_OR_NIL .
    ALIGN_ACTION = ":align" , ALIGN_VALUE , [":size" , SIZE_VALUE] .
    ALIGN_VALUE = T_OR_NIL | "above" | "below" | "left" | "right" | FUNCTION .
    SIZE_VALUE = FLOAT | INT .
    FRAME_ACTION = ":frame" , T_OR_NIL .

    OPTIONAL_ACTIONS = { OPTIONAL_ACTION } .
    OPTIONAL_ACTION = SELECT_ACTION | INHIBIT_WINDOW_QUIT_ACTION .
    SELECT_ACTION = ":select" , T_OR_NIL .
    INHIBIT_WINDOW_QUIT_ACTION = ":inhibit-window-quit" , T_OR_NIL .

Troubleshooting
---------------

In case your rules don't have any effect on a package, you can enable
tracing of calls to ``display-buffer`` and other functions using it
with ``M-x shackle-trace-functions``, perform the action displaying
the buffer and check the ``*shackle trace*`` buffer for the displayed
buffer.  If nothing shows up, the package isn't using
``display-buffer`` at all, there isn't much you can do in that case
other than asking its author to reconsider using it.  If it does,
one of the following might be the case:

- Your rule fails matching the buffer.  This might be due to a typo in
  the buffer name, an erroneous regular expression when used with
  ``:regex t`` or in the case of a major mode, the major mode not
  being enabled at the time of the matching.  The latter must be fixed
  for the package.
- The package overrides ``display-buffer-alist``.  I believe this to
  be a fundamental misunderstanding on the behalf of package authors
  as this variable is a user customizable option, tampering with it
  is questionable and should ideally be resolved by themselves.
- The package relies on the displayed buffer not being selected,
  therefore breaking once someone customizes their Emacs to select
  displayed buffers by default.  I also believe this to be an error on
  behalf of package authors, albeit not as grave as the previous one.
  Please contact them so that the package gets fixed.

Examples
--------

The following example configuration enables the rather radical
behaviour of always reusing the current window in order to avoid
unwanted window splitting:

.. code:: elisp

    (setq shackle-default-rule '(:same t))

This one on the other hand provides a less intrusive user experience
to select all windows by default unless they are spawned by
``compilation-mode`` and demonstrates how to use exceptions:

.. code:: elisp

    (setq shackle-rules '((compilation-mode :noselect t))
          shackle-default-rule '(:select t))

My final example tames `Helm <https://github.com/emacs-helm/helm>`_
windows by aligning them at the bottom with a ratio of 40%:

.. code:: elisp

    (setq helm-display-function 'pop-to-buffer) ; make helm play nice
    (setq shackle-rules '(("\\`\\*helm.*?\\*\\'" :regexp t :align t :size 0.4)))

Breaking Changes
----------------

- 0.5.0:

  ``:same`` does no longer use ``:inhibit-window-quit`` implicitly,
  you'll need to make explicitly use of it.  So, to get the old
  behaviour for ``(condition :same t)`` use ``(condition :same t
  :inhibit-window-quit t)`` instead.  Alternatively you can customize
  the 0.7.0 ``shackle-inhibit-window-quit-on-same-windows`` option to
  have it for all buffers.

- 0.6.0:

  As suggested by @Benaiah, explicitly customizing a default rule
  would be much less confusing for users than knowing about ``t``
  being special-cased in ``shackle-rules``.  Therefore, a rule with
  ``t`` as condition should be removed from ``shackle-rules`` and
  ``shackle-default-rule`` customized to hold its action instead.
  Here's a demonstration of what would change for the second example:

  .. code:: elisp

      (setq shackle-rules
            '((compilation-mode :noselect t))
            shackle-default-rule
            '(:select t))

Internals
---------

``shackle`` adds an extra entry to ``display-buffer-alist``, a
customizable variable in Emacs that specifies what to do with buffers
displayed with the ``display-buffer`` function.  It's used by quite a
lot of Emacs packages, including very essential ones like the built-in
help and compilation package.

This means other Emacs packages that neither use the
``display-buffer`` function directly nor indirectly won't be
influenced by ``shackle``.  If you should ever come across a package
that ought to use it, but doesn't conform, chances are you'll have to
speak with upstream instead of me to have it fixed.  Another thing to
be aware of is that if you've set up a fallback rule, it may take over
the Emacs defaults which can play less well with packages (such as
`Magit <http://github.com/magit/magit>`_ or `Helm
<https://github.com/emacs-helm/helm>`_).  Once you find out what's
causing the problem, you can add an exception rule to fix it.

Limitations
-----------

This package assumes that every case of altering the buffer display
rules can be caught by checking for the buffer name or major mode of
the respective buffer.  While this is true in most cases, there are
obviously exceptions to this rule.  For example
``find-function-at-point`` ends up displaying a file buffer containing
the function definition in another window, but you can't infer this
from that buffer alone.  The simple workaround is just replacing
``find-function-at-point`` with something directly using your prefered
flavour of ``display-buffer``.  If you're hell-bent on making it work
with ``shackle`` though, you could check whether using custom
conditions/actions works for you.  In case they aren't enough,
advise the function displaying the buffer to alter it so that it can
be detected by them.

Contributing
------------

If you find bugs, have suggestions or any other problems, feel free to
report an issue on the issue tracker or hit me up on IRC, I'm always on
``#emacs``.  Patches are welcome, too, just fork, work on a separate
branch and open a pull request with it.

Alternatives
------------

This package is heavily inspired by `popwin
<https://github.com/m2ym/popwin-el>`_ and was hacked together after
discovering it being hard to debug, creating overly many timers and
exposing rather baffling bugs.  ``shackle`` being intentionally
simpler and easier to understand is considered a debugging-friendly
feature, not a bug.  However if you prefer less rough edges, a
sensible default configuration and having more options for
customizing, give ``popwin`` a try.
