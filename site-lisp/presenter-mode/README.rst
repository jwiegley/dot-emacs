====================
 ``presenter-mode``
====================

Presenter-mode lets you page trough source code in Emacs as if it were a slide deck. Special comments indicate slide boundaries, titles, and parts of the code that you do not want to see in the slides.

Keybindings
===========

In ``presenter-design-mode``
----------------------------

===========  ===========================
Key          Action
===========  ===========================
``C-c C-0``  Insert hidden block markers
``C-c C-1``  Insert a level-1 title
``C-c C-2``  Insert a level-2 title
``C-c C-3``  Insert a level-3 title
``C-c C--``  Insert a slide separator
===========  ===========================

In ``presenter-mode``
---------------------

===========  ===============================
Key          Action
===========  ===============================
``<prior>``  (Page Up)  Go to previous slide
``<next>``   (Page Down)  Go to next slide
``<f5>``     Recenter titles
===========  ===============================
