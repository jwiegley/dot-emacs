discover.el
===========

Discover more of emacs using context menus.

For in-depth information, including screenshots, please read my article on "discover.el: discover more of Emacs using context menus" here:

http://www.masteringemacs.org/articles/2013/12/21/discoverel-discover-emacs-context-menus/


Installation
------------

Install it from MELPA. It's called ``discover``.


Third-party module support
--------------------------
If you want to support ``discover.el`` you must use the function ``discover-add-context-menu``, like so::

  (discover-add-context-menu
   :context-menu '(isearch
                (description "Isearch, occur and highlighting")
                (lisp-switches
                 ("-cf" "Case should fold search" case-fold-search t nil))
                (lisp-arguments
                 ("=l" "context lines to show (occur)"
                  "list-matching-lines-default-context-lines"
                  (lambda (dummy) (interactive) (read-number "Number of context lines to show: "))))
                (actions
                 ("Isearch"
                  ("_" "isearch forward symbol" isearch-forward-symbol)
                  ("w" "isearch forward word" isearch-forward-word))
                 ("Occur"
                  ("o" "occur" occur))
                 ("More"
                  ("h" "highlighters ..." makey-key-mode-popup-isearch-highlight))))
   :bind "M-s")


This will create a keybinding ``M-s`` against ``discover-mode``, making it generally available.
   
Under the hood a command is dynamically created to set the key when ``discover-mode-hook`` is called.

To create a context menu that is only available to a specific mode is very easy, and is essentially an extension of the example above. This time I will use ``dired`` to demonstrate this::

  (discover-add-context-menu
   :context-menu '(dired ...)
   :bind "?"
   :mode 'dired-mode
   :mode-hook 'dired-mode-hook
  )

As you can see, there is not much else to it. This will bind another dynamic command, but this time it will be against the hook specified in the property ``:mode-hook``. You must ensure you pick the correct mode hook; usually it is named after the major mode.

The string you give in ``:bind`` will be passed directly to ``kbd`` -- so no need to escape anything!

You may want to check if ``discover`` is present before you call ``discover-add-context-menu``. The easiest way is to check for its presence, like so::

  (when (featurep 'discover)
    (discover-add-context-menu
       ... ))

Useful Helper Commands
~~~~~~~~~~~~~~~~~~~~~~
You can get the name of the command that reveals a given context menu by calling ``discover-get-context-menu-command-name``. If you just want to funcall the returned symbol, the function ``discover-show-context-menu`` will do this for you.


Long-term Goals
===============

#. Replace makey.el with the rewritten version proposed by the Magit team.
