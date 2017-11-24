;;; lentic-rot13.el --- rot13 support for lentic

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2015, 2016, Phillip Lord, Newcastle University

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:

;; At some point in your life you may find yourself thinking, what would the
;; text that I am writing now look like in rot13? Of course, you could just
;; convert it, but really is to see the visualisation as you type. That
;; would be useful!

;; Now you can.

;; Or more seriously, this is meant as a minimal example of how do implement a
;; new lentic-buffer-configuration.


;;; Code:

;; #+BEGIN_SRC emacs-lisp
(require 'lentic)
(require 'rot13)
;; #+end_src

;; Lentic uses EIEIO objects to define the transformation between lentic buffers.
;; In this case, we extend the default configuration class. We need to add
;; nothing to the base class or constructor; all changes happen with the generic
;; methods.

;; #+begin_src emacs-lisp
(defclass lentic-rot13-configuration (lentic-default-configuration) ())

;; #+end_src

;; The clone method defines how to keep the buffers in sync. We defer most of the
;; work to the superclass method, and then simply rot13 the region that has
;; changed.

;; The semantics of the parameters are a little complex. The =start= and =stop=
;; parameters define the region in =this= buffer that has been changed, while
;; =start-converted= and =stop-converted= define the equivalent region *before*
;; the change in =that= buffer.

;; In this example, we are making implicit use of the fact that we can convert
;; directly between a location in the two buffers. In future versions of
;; =lentic-clone= will probably return the changed region directly.

;; #+begin_src emacs-lisp
(defmethod lentic-clone ((conf lentic-rot13-configuration)
                         &optional start stop _length-before
                         start-converted stop-converted)
  (call-next-method conf start stop _length-before
                    start-converted stop-converted)
  ;; and rot13 it!
  (with-current-buffer
      (lentic-that conf)
    (save-restriction
      (rot13-region
       (or start (point-min))
       (or stop (point-max))))))

;; #+end_src

;; Lentic buffers have a bi-directional link between them. So, while /this/
;; buffer may create /that/ buffer, after the initial creation, the two are
;; equivalent lenticular views of each other. In terms of lentic, therefore, at
;; creation time, we need to be able to /invert/ the configuration of /this/
;; buffer to create a configuration for /that/ buffer which defines the
;; transformation from /that/ to /this/.

;; In this case, the rot13 transformation is symmetrical, so the conversion from
;; /that/ to /this/ uses an object of the same class as from /this/ to /that/.

;; #+begin_src emacs-lisp
(defmethod lentic-invert ((conf lentic-rot13-configuration))
  (lentic-rot13-configuration
   "rot13-config"
   :this-buffer (lentic-that conf)
   :that-buffer (lentic-this conf)))
;; #+end_src

;; And, finally, we need to create a function which will construct a new object.
;; This has to be no-args because it is added as a symbol to `lentic-config'. It
;; is this function which creates the configuration for initial buffer.

;; #+begin_src emacs-lisp
(defun lentic-rot13-init ()
  (lentic-rot13-configuration
   "rot13"
   :this-buffer (current-buffer)))

(provide 'lentic-rot13)
;;; lentic-rot13.el ends here
;; #+END_SRC
