* macrostep: interactive macro-expander

   =macrostep= is an Emacs minor mode for interactively stepping
   through the expansion of macros in Emacs Lisp source code.  It lets
   you see exactly what happens at each step of the expansion process
   by pretty-printing the expanded forms inline in the source buffer,
   which is temporarily read-only while macro expansions are visible.
   You can expand and collapse macro forms one step at a time, and
   evaluate or instrument the expansions for debugging with Edebug as
   normal (but see "Bugs and known limitations", below).
   Single-stepping through the expansion is particularly useful for
   debugging macros that expand into another macro form.  These can be
   difficult to debug with Emacs' built-in =macroexpand=, which
   continues expansion until the top-level form is no longer a macro
   call.

   Both globally-visible macros as defined by =defmacro= and local
   macros bound by =(cl-)macrolet= or another macro-defining form can
   be expanded.  Within macro expansions, calls to macros and compiler
   macros are fontified specially: macro forms using
   =macrostep-macro-face=, and functions with compiler macros using
   =macrostep-compiler-macro-face=.  Uninterned symbols (gensyms) are
   fontified based on which step in the expansion created them, to
   distinguish them both from normal symbols and from other gensyms
   with the same print name.

   As of version 0.9, it is also possible to extend =macrostep= to
   work with other languages with macro systems in addition to Emacs
   Lisp.  An extension for Common Lisp (via SLIME) is in the works;
   contributions for other languages are welcome.  See "Extending
   macrostep" below for details.

** Key-bindings and usage
   The standard keybindings in =macrostep-mode= are the following:
 
    - e, =, RET  :: expand the macro form following point one step
    - c, u, DEL  :: collapse the form following point
    - q, C-c C-c :: collapse all expanded forms and exit macrostep-mode
    - n, TAB     :: jump to the next macro form in the expansion
    - p, M-TAB   :: jump to the previous macro form in the expansion

    It's not very useful to enable and disable macrostep-mode
    directly.  Instead, bind =macrostep-expand= to a key in
    =emacs-lisp-mode-map=, for example C-c e:

#+BEGIN_SRC emacs-lisp
  (define-key emacs-lisp-mode-map (kbd "C-c e") 'macrostep-expand)
#+END_SRC

    You can then enter macrostep-mode and expand a macro form
    completely by typing =C-c e e e ...= as many times as necessary.

    Exit macrostep-mode by typing =q= or =C-c C-c=, or by successively
    typing =c= to collapse all surrounding expansions.

** Customization options
   Type =M-x customize-group RET macrostep RET= to customize options
   and faces.

   To display macro expansions in a separate window, instead of inline
   in the source buffer, customize
   =macrostep-expand-in-separate-buffer= to =t=.  The default is
   =nil=.  Whichever default behavior is selected, the alternative
   behavior can be obtained temporarily by giving a prefix argument to
   =macrostep-expand=.

   To have =macrostep= ignore compiler macros, customize
   =macrostep-expand-compiler-macros= to =nil=.  The default is =t=.

   Customize the faces =macrostep-macro-face=,
   =macrostep-compiler-macro-face=, and =macrostep-gensym-1= through
   =macrostep-gensym-5= to alter the appearance of macro expansions.

** Locally-bound macros
   As of version 0.9, =macrostep= can expand calls to a locally-bound
   macro, whether defined by a surrounding =(cl-)macrolet= form, or by
   another macro-defining macro.  In other words, it is possible to
   expand the inner =local-macro= forms in both the following
   examples, whether =local-macro= is defined by an enclosing
   =cl-macrolet= --
   
   #+BEGIN_SRC emacs-lisp
     (cl-macrolet ((local-macro (&rest args)
                     `(expansion of ,args)))
       (local-macro (do-something)))
   #+END_SRC

   -- or by a macro which expands into =cl-macrolet=, provided that
   its definition of macro is evaluated prior to calling
   =macrostep-expand=:

   #+BEGIN_SRC emacs-lisp
     (defmacro with-local-macro (&rest body)
       `(cl-macrolet ((local-macro (&rest args)
                        `(expansion of ,args)))
          ,@body))

     (with-local-macro
         (local-macro (do something (else)))
   #+END_SRC

   See the =with-js= macro in Emacs's =js.el= for a real example of
   the latter kind of macro.

   Expansion of locally-bound macros is implemented by instrumenting
   Emacs Lisp's macro-expander to capture the environment at point.  A
   similar trick is used to detect macro- and compiler-macro calls
   within expanded text so that they can be fontified accurately.

** Expanding sub-forms
   By moving point around in the macro expansion using
   =macrostep-next-macro= and =macrostep-prev-macro= (bound to the =n=
   and =p= keys), it is possible to expand other macro calls within
   the expansion before expanding the outermost form.  This can
   sometimes be useful, although it does not correspond to the real
   order of macro expansion in Emacs Lisp, which proceeds by fully
   expanding the outer form to a non-macro form before expanding
   sub-forms.

   The main reason to expand sub-forms out of order is to help with
   debugging macros which programmatically expand their arguments in
   order to rewrite them.  Expanding the arguments of such a macro
   lets you visualise what the macro definition would compute via
   =macroexpand-all=.

** Extending macrostep for other languages
   Since version 0.9, it is possible to extend macrostep to work with
   other languages besides Emacs Lisp.  In typical Emacs fashion, this
   is implemented by setting buffer-local variables to different
   function values.  Six buffer-local variables define the
   language-specific part of the implementation:

   - =macrostep-sexp-bounds-function=
   - =macrostep-sexp-at-point-function=
   - =macrostep-environment-at-point-function=
   - =macrostep-expand-1-function=
   - =macrostep-print-function=
   - =macrostep-macro-form-p-function=

   Typically, an implementation for another language would set these
   variables in a major-mode hook.  See the docstrings of each
   variable for details on how each one is called and what it should
   return.  At a minimum, another language implementation needs to
   provide =macrostep-sexp-at-point-function=,
   =macrostep-expand-1-function=, and =macrostep-print-function=.
   Lisp-like languages may be able to reuse the default
   =macrostep-sexp-bounds-function= if they provide another
   implementation of =macrostep-macro-form-p-function=.  Languages
   which do not implement locally-defined macros can set
   =macrostep-environment-at-point-function= to =ignore=.
   
   Note that the core =macrostep= machinery only interprets the return
   value of =macrostep-sexp-bounds-function=, so implementations for
   other languages can use any internal representations of code and
   environments which is convenient.  Although the terminology is
   Lisp-specific, there is no reason that implementations could not be
   provided for non-Lisp languages with macro systems, provided there
   is some way of identifying macro calls and calling the compiler /
   preprocessor to obtain their expansions.

** Bugs and known limitations
   You can evaluate and edebug macro-expanded forms and step through
   the macro-expanded version, but the form that =eval-defun= and
   friends read from the buffer won't have the uninterned symbols of
   the real macro expansion.  This will probably work OK with CL-style
   gensyms, but may cause problems with =make-symbol= symbols if they
   have the same print name as another symbol in the expansion. It's
   possible that using =print-circle= and =print-gensym= could get
   around this.

   Please send other bug reports and feature requests to the author.

** Acknowledgements
   Thanks to:
   - John Wiegley for fixing a bug with the face definitions under
     Emacs 24 & for plugging macrostep in his [[http://youtu.be/RvPFZL6NJNQ][EmacsConf presentation]]!
   - George Kettleborough for bug reports, and patches to highlight
     the expanded region and properly handle backquotes.
   - Nic Ferrier for suggesting support for local definitions within
     macrolet forms
   - Luís Oliveira for suggesting and implementing SLIME support

   =macrostep= was originally inspired by J. V. Toups's 'Deep Emacs
   Lisp' articles ([[http://dorophone.blogspot.co.uk/2011/04/deep-emacs-part-1.html][part 1]], [[http://dorophone.blogspot.co.uk/2011/04/deep-emacs-lisp-part-2.html][part 2]], [[http://dorophone.blogspot.co.uk/2011/05/monadic-parser-combinators-in-elisp.html][screencast]]).

** Changelog
   - v0.9, 2015-10-01:
     - separate into Elisp-specific and generic components
     - highlight and expand compiler macros
     - improve local macro expansion and macro form identification by
       instrumenting =macroexpand(-all)=
   - v0.8, 2014-05-29: fix a bug with printing the first element of
     lists
   - v0.7, 2014-05-11: expand locally-defined macros within
     =(cl-)macrolet= forms
   - v0.6, 2013-05-04: better handling of quote and backquote
   - v0.5, 2013-04-16: highlight region, maintain cleaner buffer state
   - v0.4, 2013-04-07: only enter macrostep-mode on successful
     macro-expansion
   - v0.3, 2012-10-30: print dotted lists correctly. autoload
     definitions.

#+OPTIONS: author:nil email:nil toc:nil timestamp:nil
