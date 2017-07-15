=============================
 Using esh2tex with Org-mode
=============================

Code blocks
===========

Make sure that ``org-latex-listings`` is nil::

  (setq org-latex-listings nil)

Add the following to the beginning of your org file::

  #+LATEX_HEADER: \input{esh-preamble}

Then before each Org source block::

  #+LATEX: %% ESH: <lang>

Inline code
===========

For inline code, start with this to ensure that you get ``\verb`` in the output
when you use verbatim (``~…~``) in the input:

.. code:: lisp

   (with-eval-after-load 'ox-latex
     (setcdr (assoc 'code org-latex-text-markup-alist) 'verb))

The prefix each inline code block like this::

  This is an example of C++ code: @c++ ~int main() { return 0; }~.
  This, on the other hand, is Python: @python ~def main(): return 0~.

And add the following lines to your ``esh-init.el``::

  (esh-latex-add-inline-verb "@c++ \\verb" 'c++-mode)
  (esh-latex-add-inline-verb "@python \\verb" 'python-mode)

Preamble
========

Get rid of inputenc, fontenc, babel, etc:

.. code:: emacs-lisp

   (with-eval-after-load 'org
    (setq org-latex-default-packages-alist
          '(("AUTO" "polyglossia" t)
            ("" "fontspec" t)
            ("" "fixltx2e" nil)
            ("" "graphicx" t)
            ("" "grffile" t)
            ("" "longtable" nil)
            ("" "wrapfig" nil)
            ("" "rotating" nil)
            ("normalem" "ulem" t)
            ("" "amsmath" t)
            ("" "textcomp" t)
            ("" "amssymb" t)
            ("" "capt-of" nil)
            ("" "hyperref" nil))))


Full example
============

::

   #+LATEX_HEADER: \input{esh-preamble}

   * Code blocks

     Here's a block of code:

     #+LATEX: %% ESH: c++
     #+BEGIN_SRC c++
     int main() {
       return 0;
     }
     #+END_SRC

   * Inline code

     This is an example of C++ code: (c++) ~int main() { return 0; }~.
     This, on the other hand, is Python: (python) ~def main(): return 0~.

   # Local Variables:
   # org-latex-listings: nil
   # End:

Automating
==========

There's some code to automate this in `esh-org.el <esh-org.el>`_.
