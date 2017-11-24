;;; lentic.el --- One buffer as a view of another -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>
;; Version: 0.11
;; Package-Requires: ((emacs "24.4")(m-buffer "0.13")(dash "2.5.0")(f "0.17.2")(s "1.9.0"))

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014, 2015, 2016, Phillip Lord, Newcastle University

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

;; `lentic' enables /lenticular text/: simultaneous editing and viewing of the
;; same (or closely related) text in two or more buffers, potentially in
;; different modes. Lenticular text is named after lenticular printing, which
;; produce images which change depending on the angle at which they are
;; viewed.

;; Sometimes, it would be nice to edit a file in two ways at once. For
;; instance, you might have a source file in a computational language with
;; richly marked documentation. As Emacs is a modal editor, it would be nice
;; to edit this file both in a mode for the computational language and for the
;; marked up documentation.

;; One solution to this is to use a single-mode which supports both types of
;; editing. The problem with this is that it is fundamentally difficult to
;; support two types of editing at the same time; more over, you need a new
;; mode for each combination. Another solution is to use one of the
;; multiple-mode tools which are available. The problem with this is that they
;; generally need some support from the modes in question. And, again, the
;; difficulty is supporting both forms of editing in the same environment. A
;; final problem is that it is not just the editing environment that needs to
;; be adapted; the programmatic environment needs to be untroubled by the
;; documentation, and the documentation environment untroubled by the program
;; code.

;; Lenticular text provides an alternative solution. Two lentic buffers, by
;; default, the share content but are otherwise independent. Therefore,
;; you can have two buffers open, each showing the content in different modes;
;; to switch modes, you simply switch buffers. The content, location of point,
;; and view are shared.

;; Moreover, lentic buffers can also perform a bi-directional transformation
;; between the two. If this is done, then the two can have different but
;; related text. This also solves the problem of integration with a
;; tool-chain; each lentic buffer can be associated with a different file and
;; a different syntax. For example, this file is, itself, lenticular text. It
;; can be viewed either as Emacs-Lisp or in Org-Mode. In Emacs-Lisp mode, this
;; text is commented out, in org-mode it is not.

;; In fact, although the default behaviour of lentic appears to keep the same
;; text in each buffer, even it uses this bi-directional transformation
;; capability; while the text is shared, the text properties are not. This is
;; a behaviour which differs between lentic buffers and indirect buffers. The
;; lentic buffers can therefore be in different modes without fighting each
;; other to set the text properties.

;; It is possible to configure the transformation for any two buffers in a
;; extensible way. Mostly I have concentrated on mode-specific operation,
;; but, for instance, I have also used this ability on a per-project basis
;; controlling, for instance, the location of the lentic-file.

;;; Usage:

;; lentic can be installed through MELPA/Marmalade then add

;; (global-lentic-mode)

;; to your .emacs.

;; The main user entry points are accessible through the lentic edit menu, or
;; through `global-lentic-mode' which adds keybindings to create and manipulate
;; new lentic buffers. See `lentic-mode' commentary for more information.

;; By default, the lentic buffer created contains exactly the same contents as
;; the original buffer, but is otherwise separate; it can have a different major
;; modes, different syntax highlighting, invisible regions and even different
;; narrowing. Saving one buffer will save the other; killing the lentic buffer
;; does not affect the original, but killing the original also kills the lentic.

;; While this is somewhat useful, more generally a buffer will be configured to
;; produce a particular transformation. This can control many features of the
;; lentic, including the file name, major mode and an arbitrary transformation
;; between the two. Configuration is considered next.

;;; Configuration:

;; lentic buffers are configurable in a large number of ways. It is possible
;; to control the nature of the transformation, the default buffer name that a
;; lentic buffer takes, and the file location (or not) of the lentic buffer.
;; Lentic now supports any number of lentic buffers, in relatively arbitrary
;; geometries, although this requires additional support from the
;; configuration objects.

;; Configuration of a buffer happens in one of two places. First,
;; `lentic-init' is run when a lentic buffer is first created. This function
;; should return the configuration object, and is mostly designed for use as a
;; file-local or dir-local variable. This object is stored in the `lentic-config'
;; and all subsequent operation happens through this.

;; There are now a number of different configurations, which can be used for
;; general-purposes use as well as an extension points for subclass
;; configurations. The two most general configurations are:

;;  - default: this copies all text exactly, but does not transfer
;;    text-properties (which is the behaviour of indirect buffers). It is
;;    possible to configure the default file or mode on a per-object basis.
;;  - chunk: this is designed for programmatic syntaxes where chunks of code are
;;    demarcated by start and end tags, and everything else is commented by
;;    line-start comments. Comments are added or removed between the two buffers.

;; The second of these is extended in lentic-org.el to provide the
;; configuration for this file: there is a normal emacs-lisp file in one buffer
;; and an org-mode version in another. Other programmatic and documentation modes
;; are supported in other files.

;;; Status:

;; This is a beta release, but is now nearly feature complete. The core lentic
;; libraries should hopefully be fairly stable now, however, there is the
;; possibility that it will behave badly and may result in data loss. Please
;; use with care on files with backups.

;; Previous releases of this package were called "linked-buffer". I changed
;; this because I wanted a name for the general idea of text with two
;; visualisations; "linked text" doesn't work because it is sounds like
;; hyperlinked text.

;; Although it is still too early to guarantee, I hope that the current
;; configuration scheme will remain fixed, and subclass extensions should
;; require little change for the future.

;;; Code:

;; #+BEGIN_SRC emacs-lisp
(require 'eieio)
(require 'm-buffer)
(require 'm-buffer-at)
(require 'f)

(defvar lentic-doc "lenticular.org")
(defvar lentic-doc-html-files '("lenticular.css"))
;; #+end_src

;; ** State

;; This section defines all of the variables that the basic state for lentic
;; is stored in. We deliberately have as few of these as possible, as this
;; makes re-initializing the state during development as straight-forward as
;; possible.

;; We start with `lentic-init' which provides the ability to define some default
;; configuration for a buffer. These are just functions which return
;; `lentic-configuration' objects. This is a slight step of indirection but is
;; essentially there to allow the use of file- or dir-local variables to define
;; the default behaviour for a given buffer. All the values have to be defined by
;; the user as safe, so we do not want too many different values.

;; #+begin_src emacs-lisp
(defvar lentic-init nil
  "Function that initializes lentics for this buffer.

This should be one or a list of functions that each return a
`lentic-configuration' object.")

(make-variable-buffer-local 'lentic-init)
;; #+end_src

;; The `lentic-config' variable stores all of the configuration objects for each
;; lentic-buffer of this-buffer. Each lentic-buffer should have one configuration
;; object and is this configuration object that controls the behaviour and
;; updating of that lentic. As lentics are bi-directional, the `lentic-config'
;; variable should be -- for each lentic-configuration object in this-buffer
;; pointing to that-buffer there should be one in that-buffer pointing to
;; this-buffer. This variable has to `permanent-local' otherwise a new mode (or
;; typing `normal-mode') would break everything.

;; #+begin_src emacs-lisp
(defvar lentic-config nil
  "Configuration for lentic.

This is a list of objects of the class `lentic-configuration'
lentic-configuration', which defines the way in which the text in
the different buffers is kept synchronized. This configuration is
resilient to changes of mode in the current buffer.")

(make-variable-buffer-local 'lentic-config)
(put 'lentic-config 'permanent-local t)

(defvar lentic-counter 0)
(defun lentic-config-name (buffer)
  "Given BUFFER, return a name for the configuration object."
  (format "lentic \"%s:%s\"" buffer (setq lentic-counter (+ 1 lentic-counter))))

;;;###autoload
(defvar lentic-init-functions nil
  "All functions that can be used as `lentic-init' function.")
;; #+end_src

;; ** Base Configuration

;; This section defines the base class and generic methods for all
;; lentic-configuration objects. Most of the properties of this class define the
;; behaviour of the lentic-buffer -- in other words they are configuration.
;; However, there are a few properties which store state about the last
;; before-change event that occured which are used to percolate the changes
;; correctly. This is a handy place to store these, but are not really
;; end-user properties.

;; #+begin_src emacs-lisp
(defclass lentic-configuration ()
  ((this-buffer
    :initarg :this-buffer
    :documentation
    "The this-buffer for this configuration. This should be the
    current-buffer when this configuration is present in `lentic-config'." )
   (that-buffer
    :initarg :that-buffer
    :documentation
    "The that-buffer for this configuration. The that-buffer (if
    live) should a lentic-configuration object for this-buffer in
    its `lentic-config'." )
   (creator
    :initarg :creator
    :initform nil
    :documentation
    "Non-nil if this lentic-configuration was used to create a
    lentic view. This is used to determine the behaviour when the
    buffer is killed: killing the creator kills all views, but killing
    a view does not kill the creator.")
   (delete-on-exit
    :initarg :delete-on-exit
    :initform nil
    :documentation
    "Non-nil if the file associated with this should be deleted on exit.")
   (singleton
    :initarg :singleton
    :initform nil
    :documentation
    "Non-nil if only one lentic (and therefore object) of this type
    can exist for a given buffer.")
   (sync-point
    :initarg :sync-point
    :initform t
    :documentation
    "Non-nil if changes to the location of point in this-buffer
    should be percolated into that-buffer.")
   (last-change-start
    :initarg :last-change-start
    :initform nil
    :documentation
    "The location of the start of the last before-change event.
    This should only be set by lentic.")
   (last-change-start-converted
    :initarg :last-change-start-converted
    :initform nil
    :documentation
    "The location of the start of the last before-change event,
    converted into the equivalent location in that-buffer. This
    should only be set by lentic.")
   (last-change-stop
    :initarg :last-change-stop
    :initform nil
    :documentation
    "The location of the stop of the last before-change event.
    This should only be set by lentic." )
   (last-change-stop-converted
    :initarg :last-change-stop-converted
    :initform nil
    "The location of the stop of the last before-change event,
    converted into the equivalent location in that-buffer. This
    should only be set by lentic."))
  "Configuration object for lentic which defines the behavior of
  the lentic buffer.")
;; #+end_src

;; We define a set of generic methods. I am not entirely sure what the purpose of
;; generic methods are and whether I need them or not; I think it's just a place
;; to put the documentation.

;; #+begin_src emacs-lisp
(defgeneric lentic-create (conf)
  "Create the lentic for this configuration.
Given a `lentic-configuration' object, create the lentic
appropriate for that configurationuration. It is the callers
responsibility to check that buffer has not already been
created.")

(defgeneric lentic-convert (conf location)
  "Convert LOCATION in this-buffer to an equivalent location in
that-buffer. LOCATION is a numeric location, rather than a
marker. By equivalent, we mean the same semantic location as
determined by the transformation between the buffers. It is
possible that a given LOCATION could map to more than one
location in the lentic buffer.")

(defgeneric lentic-clone (conf)
  "Updates that-buffer to reflect the contents in this-buffer.

Updates at least the region that has been given between start and
stop in the this-buffer, into the region start-converted and
stop-converted in that-buffer.

Returns a list of the start location in that-buffer of the
change, the stop location in that-buffer of the change and the
length-before in that buffer of the region changed before the
change, if and only if the changes are exactly that suggested by
the START, STOP, _LENGTH-BEFORE, START-CONVERTED and
STOP-CONVERTED. Otherwise, this should return nil.")
;; #+end_src

;; We need an invert method because we can create the configuration object for a
;; this-buffer without actually creating that-buffer. This may happen at any
;; point in the future. So, the configuration object needs to be able to return
;; it's own inverse. This can be a configuration object of the same class which
;; is normal when the lentic transformation is symmetrical, or a different class
;; which is normal when the lentic transformation is asymmetrical.

;; #+begin_src emacs-lisp
(defgeneric lentic-invert (conf)
  "Return a new configuration object for the lentic buffer.
This method is called at the time that the lentic is created. It
is the callers responsibility to ensure that this is only called
at creation time and not subsequently. The invert function should
only return the configuration object and NOT create the lentic
buffer.")

;; #+end_src

;; `lentic-coexist?' has been created to cope with the case when a buffer has two
;; or more default views. We may wish to re-initialize all the default lentic
;; views. However, this is going to be problematic if some are already there --
;; we will end up with two many. In general, configurations which have been
;; created as a result of calls to the `lentic-init' functions should return
;; false here if there is another call to the same function. Lentic buffers which
;; are being used as a persistent view should generally return true here so that
;; as many can be created as required.

;; #+begin_src emacs-lisp
(defgeneric lentic-coexist? (this-conf that-conf)
  "Return non-nil if THIS-CONF and co-exist with THAT-CONF.
By co-exist this means that both configurations are valid for a
given buffer at the same time. A nil return indicates that there
should only be one of these two for a given buffer.")
;; #+end_src

;; I've implemented `lentic-this' and `lentic-that' as methods although I think I
;; have only over-ridden the implementation once in lentic-delayed which has
;; since been deleted anyway.

;; #+begin_src emacs-lisp
(defmethod lentic-this ((conf lentic-configuration))
  "Returns this-buffer for this configuration object.
In most cases, this is likely to be the `current-buffer' but
this should not be relied on."
  (oref conf :this-buffer))

(defmethod lentic-that ((conf lentic-configuration))
  "Returns the that-buffer for this configuration object.
This may return nil if there is not that-buffer, probably because
it has not been created."
  (and (slot-boundp conf :that-buffer)
       (oref conf :that-buffer)))

(defmethod lentic-ensure-that ((conf lentic-configuration))
  "Get the lentic for this configuration
or create it if it does not exist."
  (or (lentic-that conf)
      (lentic-create conf)))
;; #+end_src

;; This part of the user interface is not ideal at the moment. I need something
;; which allows me to see all the currently active lentic-buffers, but I am far
;; from convinced that the mode-line is the best place, since the mode-line gets
;; overly full for most users.

;; As a second problem, supporting mode-line display directly in the
;; configuration object seems right, and breaks the encapsulation between
;; lentic.el and lentic-mode.el. Probably this needs to be replaced by some sort
;; of status keyword return value.

;; #+begin_src emacs-lisp
(defmethod lentic-mode-line-string ((conf lentic-configuration))
  "Returns a mode-line string for this configuration object."
  (when (slot-boundp conf :that-buffer)
    (let ((that (oref conf :that-buffer)))
      (if
          (and that
               (buffer-live-p that))
          "on"
        ""))))
;; #+end_src

;; ** Default Configuration

;; This is the default implementation of a lentic configuration. It provides an
;; identity transformation at that string level -- the two buffers will (should!)
;; have identical `buffer-string' at all times. Or, more strictly, identical
;; without properties, so identical ~(buffer-substring-no-properties (point-min)
;; (point-max))~, which is not nearly so snappy.

;; We add two more properties to this class -- perhaps these should be pushed upwards.

;; #+begin_src emacs-lisp
(defclass lentic-default-configuration (lentic-configuration)
  ((lentic-file
    :initform nil
    :initarg :lentic-file
    :documentation
    "The name of the file that will be associated with that lentic buffer.")
   (lentic-mode
    :initform nil
    :initarg :lentic-mode
    :documentation
    "The mode for that lentic buffer."))
  "Configuration which maintains two lentics with the same contents.")
;; #+end_src

;; We add in a string transformation function here. There has no actual
;; function within lentic per se, but it is used in lentic-dev as something we
;; can advice. This avoids bulking up the code in lentic, while still allows
;; me to affect the transformation during development of new transforms.

;; #+begin_src emacs-lisp
(defun lentic-insertion-string-transform (string)
  "Transform the STRING that is about to be inserted.
This function is not meant to do anything. It's useful to
advice."
  string)
;; #+end_src

;; The default methods should be self-explanatory!

;; #+begin_src emacs-lisp
(defmethod lentic-create ((conf lentic-default-configuration))
  "Create an new lentic buffer. This creates the new buffer sets
the mode to the same as the main buffer or which ever is
specified in the configuration. The current contents of the main
buffer are copied."
  ;; make sure the world is ready for lentic buffers
  (lentic-ensure-hooks)
  ;; create lentic
  (let* ((this-buffer
          (lentic-this conf))
         (that-buffer
          (generate-new-buffer
           (format "*lentic: %s*"
                   (buffer-name
                    this-buffer))))
         (sec-file (oref conf :lentic-file))
         (sec-mode
          (or
           ;; the specified normal mode
           (oref conf :lentic-mode)
           ;; if we have a file try normal mode
           (if sec-file
               'normal-mode
             ;; otherwise the same mode as the main file
             major-mode))))
    (oset conf :creator t)
    ;; make sure this-buffer knows about that-buffer
    (oset conf :that-buffer that-buffer)
    ;; init that-buffer with mode, file and config
    ;; the mode must be init'd after adding content in case there are any
    ;; file-local variables need to be evaled
    ;; insert the contents
    (lentic-update-contents conf)
    (with-current-buffer that-buffer
      (when sec-mode
        (funcall sec-mode))
      (when sec-file
        (set-visited-file-name sec-file))
      (setq lentic-config
            (list (lentic-invert conf))))
    that-buffer))

(defmethod lentic-coexist? ((this-conf lentic-default-configuration)
                            that-conf)
  "By default, we can have multiple lentic buffers with the same
configuration, unless specifically disallowed, or unless it has
the same associated file as pre-existing buffer (which is going
to break!)."
  (and
   (not (oref this-conf :singleton))
   (not
    (and (oref this-conf :lentic-file)
         (oref that-conf :lentic-file)
         (f-equal? (oref this-conf :lentic-file)
                   (oref that-conf :lentic-file))))))

(defmethod lentic-invert ((conf lentic-default-configuration))
  "By default, return a clone of the existing object, but switch
the this and that buffers around. "
  (clone
   conf
   :this-buffer (lentic-that conf)
   :that-buffer (lentic-this conf)
   :sync-point (oref conf :sync-point)))

(defmethod lentic-convert ((conf lentic-default-configuration)
                           location)
  "The two buffers should be identical, so we just return the
  same location."
  location)

(defmethod lentic-clone ((conf lentic-configuration)
                                &optional start stop _length-before
                                start-converted stop-converted)
  "The default clone method cuts out the before region and pastes
in the new."
  (let ((this-b (lentic-this conf))
        (that-b (lentic-that conf)))
    (with-current-buffer this-b
      ;;(lentic-log "this-b (point,start,stop)(%s,%s,%s)" (point) start stop)
      (save-window-excursion
        (save-restriction
          (widen)
          (let* ((start (or start (point-min)))
                 (stop (or stop (point-max))))
            (with-current-buffer that-b
              (save-restriction
                (widen)
                ;; get the start location that we converted before the change.
                ;; lentic-convert is not reliable now, because the two
                ;; buffers do not share state until we have percolated it
                (let ((converted-start
                       (max (point-min)
                            (or start-converted
                                (point-min))))
                      (converted-stop
                       (min (point-max)
                            (or stop-converted
                                (point-max)))))
                  (delete-region converted-start
                                 converted-stop)
                  (save-excursion
                    (goto-char converted-start)
                    ;; so this insertion is happening at the wrong place in block
                    ;; comment -- in fact, it's happening one too early
                    (insert
                     (with-current-buffer this-b
                       ;; want to see where it goes
                       ;; hence the property
                       (lentic-insertion-string-transform
                        (buffer-substring-no-properties
                         start stop))))
                    (list converted-start
                          (+ converted-start (- stop start))
                          (- converted-stop converted-start))))))))))))

;;;###autoload
(defun lentic-default-init ()
  "Default init function.
see `lentic-init' for details."
  (lentic-default-configuration
   (lentic-config-name (current-buffer))
   :this-buffer (current-buffer)))

(add-to-list 'lentic-init-functions
             'lentic-default-init)

;; #+end_src

;; ** Basic Operation

;; In this section, we define some utility functions and the hooks we need into
;; the core Emacs operations.

;; *** Utility

;; We start with some utility macros. These deal with the fact that a buffer can
;; have a lentic or not, and that even if it does that lentic does not need to be
;; live. This happens for instance if a lentic buffer is deleted -- the buffer
;; object will still be live (because the configuration object hangs on to it).

;; At some point, the hook system needs to clean this up by detecting the
;; buffer-kill and removing the configuration objection.

;; #+begin_src emacs-lisp
(defmacro lentic-when-lentic (&rest body)
  "Evaluate BODY when the `current-buffer' has a lentic buffer."
  (declare (debug t))
  `(when (and
          lentic-config
          (-any?
           (lambda (conf)
             (-when-let
                 (buf (lentic-that conf))
               (buffer-live-p buf)))
           lentic-config))
     ,@body))

(defmacro lentic-when-buffer (buffer &rest body)
  "When BUFFER is a live buffer eval BODY."
  (declare (debug t)
           (indent 1))
  `(when (and ,buffer
              (buffer-live-p ,buffer))
     ,@body))

(defmacro lentic-when-with-current-buffer (buffer &rest body)
  "When BUFFER is a live buffer eval BODY with BUFFER current."
  (declare (debug t)
           (indent 1))
  `(lentic-when-buffer
    ,buffer
    (with-current-buffer
        ,buffer
      ,@body)))

(defmacro lentic-with-lentic-buffer (buffer &rest body)
  "With BUFFER as current, eval BODY when BUFFER has a lentic."
  (declare (debug t)
           (indent 1))
  `(lentic-when-with-current-buffer
       buffer
     (when lentic-config
       ,@body)))


(defvar lentic-condition-case-disabled
  noninteractive
  "If non-nil throw exceptions from errors.

By default this is set to the value of noninteractive, so that
Emacs crashes with backtraces in batch." )

(defmacro lentic-condition-case-unless-disabled (var bodyform &rest handlers)
  "Like `condition-case' but can be disabled like `condition-case-unless-debug'."
  (declare (debug condition-case) (indent 2))
  `(if lentic-condition-case-disabled
       ,bodyform
     (condition-case-unless-debug ,var
         ,bodyform
       ,@handlers)))

(defmacro lentic-widen (conf &rest body)
  "Widen both buffers in CONF, then evaluate BODY."
  (declare (debug t)
           (indent 1))
  `(with-current-buffer
       (lentic-that ,conf)
     (save-restriction
       (widen)
       (with-current-buffer
           (lentic-this ,conf)
         (save-restriction
           (widen)
           ,@body)))))
;; #+end_src

;; Recurse down the lentic tree to all lentic views.

;; #+begin_src emacs-lisp
(defun lentic-each (buffer fn &optional seen-buffer)
  "Starting at BUFFER, call FN on every lentic-buffer.
FN should take a single argument which is the buffer.
SEEN-BUFFER is a list of buffers to ignore."
  (lentic-with-lentic-buffer buffer
    (setq seen-buffer (cons buffer seen-buffer))
    (-map
     (lambda (conf)
       (let ((that
              (lentic-that conf)))
         (when (and (not (-contains? seen-buffer that))
                  (buffer-live-p that))
           (funcall fn that)
           (lentic-each that fn seen-buffer))))
     lentic-config)))

(defun lentic-garbage-collect-config ()
  "Remove non-live configs in current-buffer."
  (setq lentic-config
        (--filter
         (buffer-live-p
          (lentic-that it))
         lentic-config)))
;; #+end_src

;; *** Initialisation

;; #+begin_src emacs-lisp
(defun lentic-ensure-init ()
  "Ensure that the `lentic-init' has been run."
  (lentic-garbage-collect-config)
  (setq lentic-config
        ;; and attach to lentic-config
        (-concat
         lentic-config
         ;; return only those that can co-exist
         (-filter
          (lambda (this-conf)
            (-all?
             (lambda (that-conf)
               (lentic-coexist? this-conf that-conf))
             lentic-config))
          (-map
           (lambda (init)
             ;; instantiate a new conf object (but do not create the buffer)
             (funcall init))
           (if (not lentic-init)
               '(lentic-default-init)
             (-list lentic-init)))))))

(defun lentic-init-all-create ()
  "Create all lentics fo the current buffer."
  (lentic-ensure-init)
  (-map
   (lambda (conf)
     (if (and
          (slot-boundp conf :that-buffer)
          (buffer-live-p
           (lentic-that conf)))
         (lentic-that conf)
       (lentic-create conf)))
   (-list lentic-config)))
;; #+end_src

;; *** Hook System

;; The lentic hook system is relatively involved, unfortunately, and will
;; probably become more so. In so far as possible, though, all of the complexity
;; should be here, using the methods provided in the lentic-configuration object.

;; The complexity of the hook system and the fact that it is hooked deeply into
;; the core of Emacs can make it quite hard to debug. There are a number of
;; features put in place to help deal with this. These are:

;;  - A logging system
;;  - An emergency detection system.
;;  - Two part hooks


;; Start by enabling hooks!

;; #+begin_src emacs-lisp
(defun lentic-ensure-hooks ()
  "Ensures that the hooks that this mode requires are in place."
  (add-hook 'post-command-hook
            'lentic-post-command-hook)
  ;; after and before-change functions are hooks (with args) even if they are
  ;; not named as such.
  (add-hook 'after-change-functions
            'lentic-after-change-function)
  (add-hook 'before-change-functions
            'lentic-before-change-function)
  (add-hook 'after-save-hook
            'lentic-after-save-hook)
  (add-hook 'kill-buffer-hook
            'lentic-kill-buffer-hook)
  (add-hook 'kill-emacs-hook
            'lentic-kill-emacs-hook))

;; #+end_src

;; The logging system which allows post-mortem analysis of what lentic has done.
;; Originally, my plan was to leave logging in place so aid analysis of bug
;; reports, but this requires so much logging that it the log buffer becomes
;; impossible to analyse.

;; #+begin_src emacs-lisp
(defvar lentic-log nil)
(defmacro lentic-log (&rest rest)
  "Log REST."
  `(when lentic-log
     (lentic-when-lentic
      (let ((msg
             (concat
              (format ,@rest)
              "\n")))
        (princ msg #'external-debugging-output)))))
;; #+end_src

;; An emergency detection system. Several of the hooks in use (post-command-hook,
;; and the before- and after-change-functions) automatically remove hook
;; functions which give errors. In development, this means that all errors are
;; silently ignored and, worse, lentic continues in an inconsistent state with
;; some hooks working and some not. Lentic catches all errors, therefore, and
;; then drops into an "lentic-emergency" state, where all lentic functionality is
;; disabled. This is still a dangerous state as changes do not percolate, but at
;; least it should be predictable. The emergency state can be changed with
;; `lentic-unemergency' and `lentic-emergency'.

;; #+begin_src emacs-lisp

(defvar lentic-emergency  nil
  "Iff non-nil halt all lentic activity.

This is not the same as disabling lentic mode. It stops all
lentic related activity in all buffers; this happens as a result
of an error condition. If lentic was to carry on in these
circumstances, serious data loss could occur. In normal use, this
variable will only be set as a result of a problem with the code;
it is not recoverable from a user perspective.

It is useful to toggle this state on during development. Once
enabled, buffers will not update automaticaly but only when
explicitly told to. This is much easier than try to debug errors
happening on the after-change-hooks. The
function `lentic-emergency' and `lentic-unemergency' functions
enable this.")

(defvar lentic-emergency-debug nil
  "Iff non-nil, lentic will store change data, even
during a `lentic-emergency'.

Normally, `lentic-emergency' disables all activity, but this makes
testing incremental changes charge. With this variable set, lentic will
attempt to store enough change data to operate manually. This does require
running some lentic code (notably `lentic-convert'). This is low
risk code, but may still be buggy, and so setting this variable can cause
repeated errors.")

(defun lentic-emergency ()
  "Stop lentic from working due to code problem."
  (interactive)
  (setq lentic-emergency t)
  (lentic-update-all-display))

(defun lentic-unemergency ()
  "Start lentic working after stop due to code problem."
  (interactive)
  (setq lentic-emergency nil)
  (lentic-update-all-display))

(defun lentic-hook-fail (err hook)
  "Give an informative message when we have to fail.
ERR is the error. HOOK is the hook type."
  (message "lentic mode has failed on \"%s\" hook: %s "
           hook (error-message-string err))
  (lentic-emergency)
  (with-output-to-temp-buffer "*lentic-fail*"
    (princ "There has been an error in lentic-mode.\n")
    (princ "The following is debugging information\n\n")
    (princ (format "Hook: %s\n" hook))
    (princ (error-message-string err)))
  (select-window (get-buffer-window "*lentic-fail*")))
;; #+end_src

;; As a byproduct of the last, lentic also has two part hooks: the real hook
;; function which just handles errors and calls the second function which does
;; the work. This make it possible to call the second function interactively,
;; without catching errors (so that they can be debugged) or causing the
;; lentic-emergency state. There are some utility functions in lentic-dev for
;; running hooks which require arguments.

;; **** General Hook

;; Start by handling saving, killing and general connecting with the Emacs
;; behaviour.

;; #+begin_src emacs-lisp
(defun lentic-after-save-hook ()
  "Error protected call to real after save hook."
  (unless lentic-emergency
    (lentic-condition-case-unless-disabled err
        (lentic-after-save-hook-1)
      (error
       (lentic-hook-fail err "after-save-hook")))))

(defun lentic-after-save-hook-1 ()
  "Respond to a save in the `current-buffer'.
This also saves every lentic which is file-associated."
  (lentic-each
   (current-buffer)
   (lambda (buffer)
     (with-current-buffer
         buffer
       (when (buffer-file-name)
         (save-buffer))))))

(defvar lentic-kill-retain nil
  "If non-nil retain files even if requested to delete on exit.")

(defun lentic-kill-buffer-hook ()
  "Error protected call to real `kill-buffer-hook'."
  (unless lentic-emergency
    (lentic-condition-case-unless-disabled err
        (lentic-kill-buffer-hook-1)
      (error
       (lentic-hook-fail err "kill-buffer-hook")))))

(defvar lentic--killing-p nil)

(defun lentic-kill-buffer-hook-1 ()
  "Respond to any buffer being killed.
If this killed buffer is lentic and is :creator, then kill all
lentic-buffers recursively. If the buffer is :delete-on-exit,
then remove any associated file."
  (lentic-when-lentic
   (when
       (and
        (--any?
         (oref it :delete-on-exit)
         lentic-config)
        ;; might not exist if we not saved yet!
        (file-exists-p buffer-file-name)
        ;; if we are cloning in batch, we really do not want to kill
        ;; everything at the end
        (not noninteractive)
        ;; or we have blocked this anyway
        (not lentic-kill-retain))
     (delete-file (buffer-file-name)))
   ;; if we were the creator buffer, blitz the lentics (which causes their
   ;; files to delete also).
   (let ((lentic-killing-p t))
     (when
         (and
          (not lentic-killing-p)
          (--any?
           (oref it :creator)
           lentic-config))
       (lentic-each
        (current-buffer)
        (lambda (buffer)
          (kill-buffer buffer)))))))

(defun lentic-kill-emacs-hook ()
  "Error protected call to real `kill-emacs-hook'."
  (unless lentic-emergency
    (lentic-condition-case-unless-disabled err
        (lentic-kill-emacs-hook-1)
      (error
       (lentic-hook-fail err "kill-emacs-hook")))))

(defun lentic-kill-emacs-hook-1 ()
  "Respond to `kill-emacs-hook.
This removes any files associated with lentics which are
marked as :delete-on-exit."
  (-map
   (lambda (buffer)
     (lentic-with-lentic-buffer
         buffer
       (-map
        (lambda (conf)
          (and
           (oref conf :delete-on-exit)
           (file-exists-p buffer-file-name)
           (not noninteractive)
           (delete-file (buffer-file-name))))
        lentic-config)))
   (buffer-list)))
;; #+end_src

;; **** Change Hooks

;; Handling and percolating changes is the most complex part of lentic, made more
;; complex still by the decision to support multiple buffers (why did I do that
;; to myself?).

;; The `post-command-hook' just percolates location of point through all the
;; lentic buffers.

;; #+begin_src emacs-lisp
(defun lentic-post-command-hook ()
  "Update point according to config, with error handling."
  (unless lentic-emergency
    (lentic-condition-case-unless-disabled err
        (progn
          ;; we test for this later anyway, but this makes it easier to debug.
          (when lentic-config
            (lentic-post-command-hook-1 (current-buffer))))
      (error
       (lentic-hook-fail err "post-command-hook")))))

(defun lentic-post-command-hook-1 (buffer &optional seen-buffer)
  "Update point in BUFFER according to config.
SEEN-BUFFER is a list of lentics that have already been updated."
  (lentic-with-lentic-buffer
      buffer
    ;; now we have seen this buffer don't look again
    (setq seen-buffer (cons buffer seen-buffer))
    ;; for all configurations
    (-map
     (lambda (config)
       (let ((that
              (lentic-that config)))
         ;; check for the termination condition
         (unless (-contains? seen-buffer that)
           (lentic-when-buffer
               that
             ;; then update and recurse
             (lentic-update-point config))
           (lentic-post-command-hook-1 (lentic-that config) seen-buffer))))
     lentic-config)))
;; #+end_src

;; The `after-change-function' is by far the most complex of the hooks. This is because
;; we have to percolate the changes from the buffer that has changed as a result
;; of the user doing something to all the other buffers. In theory, this should be
;; straight-forward: combined with the `before-change-function', the data from
;; the `after-change-function' defines a "dirty region" which we need to update
;; by copying from the parent and then doing what ever transformation needs to
;; happen. The problem is that that the contract from the configuration objects'
;; `lentic-clone' method is that *at least* the dirty region will be replaced.
;; `lentic-clone' can actually replace much more than this, and often needs to do
;; so, to ensure a consistent transformation.

;; So, when a lentic-buffer updates it needs to update it's own dirty region but
;; also return the dirty region that it has created, so that any lentic buffers
;; that it in turn has that are still to be updated can be so. Or, if it doesn't,
;; we just assume the whole buffer is dirty which is safe but inefficient.

;; The main after-change-function also stores the its arguments if we are in
;; debug mode which allows me to run `lentic-after-change-function-1'
;; interactively with the correct arguments.

;; #+begin_src emacs-lisp
(defvar lentic-emergency-last-change nil)
(make-variable-buffer-local 'lentic-emergency-last-change)

(defun lentic-after-change-transform (buffer start stop length-before)
  "Function called after every change percolated by lentic.
This function does nothing and is meant for advising. See
lentic-dev."
)

(defun lentic-after-change-function (start stop length-before)
  "Run change update according to `lentic-config'.
Errors are handled.
START is at most the start of the change.
STOP is at least the end of the change.
LENGTH-BEFORE is the length of the area before the change."
  ;; store values in case we want to use them
  (when lentic-emergency-debug
    (setq lentic-emergency-last-change (list start stop length-before)))
  (unless lentic-emergency
    (lentic-condition-case-unless-disabled err
        (lentic-after-change-function-1
         (current-buffer) start stop length-before)
      (error
       (lentic-hook-fail err "after change")))))

(defun lentic-after-change-function-1
    (buffer start stop
            length-before &optional seen-buffer)
  "Run change update according to `lentic-config'.
BUFFER is the changed buffer.
START is at most the start of the change.
STOP is at least the end of the change.
LENGTH-BEFORE is the length of the area before the change.
SEEN-BUFFER is a list of buffers to which we have already percolated
the change."
  (lentic-with-lentic-buffer buffer
    (setq seen-buffer (cons buffer seen-buffer))
    (-map
     (lambda (config)
       (unless
           (or (-contains? seen-buffer (lentic-that config))
               (not (buffer-live-p (lentic-that config))))
         (let ((updates
                (or
                 (lentic-update-contents config
                                         start stop length-before)
                 '(nil nil nil))))
           (apply 'lentic-after-change-transform
                  (lentic-that config)
                  updates)
           (lentic-after-change-function-1
            (lentic-that config)
            (nth 0 updates)
            (nth 1 updates)
            (nth 2 updates)
            seen-buffer))))
     lentic-config)))
;; #+end_src

;; We also need to store the location of the area to be changed before the change
;; happens. Further, we need to convert this at this time to the cognate
;; positions in the lentic buffers. This is because it is only before the change
;; that this-buffer and the lentic buffers are in a consistent state; after the
;; change, this-buffer will have changes not percolated to other buffers. By
;; making this conversion now, we can ease the implementation of the
;; `lentic-convert' function because it does not have to cope with buffers with
;; inconsistent content.


;; #+begin_src emacs-lisp
(defun lentic-before-change-function (start stop)
  "Error protected call to real `before-change-function'.
START is at most the start of the change.
STOP is at least the end of the change."
  (unless (and
           lentic-emergency
           (not lentic-emergency-debug))
    (lentic-condition-case-unless-disabled err
        (lentic-before-change-function-1 (current-buffer) start stop)
      (error
       (lentic-hook-fail err "before change")))))

(defun lentic-before-change-function-1 (buffer start stop &optional seen-buffer)
  "Calculate change position in all lentic buffers.
BUFFER is the buffer being changed.
START is at most the start of the change.
STOP is at least the end of the change.
SEEN-BUFFER is a list of buffers to which the change has been percolated."
  (lentic-with-lentic-buffer buffer
    (setq seen-buffer (cons buffer seen-buffer))
    (-map
     (lambda (config)
       (unless
           (or (-contains? seen-buffer (lentic-that config))
               ;; convert uses that buffer
               (not (buffer-live-p (lentic-that config))))
         (lentic-widen
             config
           (oset config :last-change-start start)
           (oset config
                 :last-change-start-converted
                 (lentic-convert
                  config
                  start))
           (oset config :last-change-stop stop)
           (oset config
                 :last-change-stop-converted
                 (lentic-convert
                  config
                  stop))
           (lentic-before-change-function-1
            (lentic-that config)
            (oref config :last-change-start-converted)
            (oref config :last-change-stop-converted)
            seen-buffer))))
     lentic-config)))
;; #+end_src

;; The `lentic-update-contents' actually transfers changes from one buffer to all
;; the lentics. Unfortunately before-change-function and after-change-function
;; are not always consistent with each other. So far the main culprit I have
;; found is `subst-char-in-region', which is used under the hood of
;; `fill-paragraph'. On the b-c-f this reports the real start of the change and
;; the *maximal* end, while on the a-c-f it reports both the real start and real
;; end. Unfortunately, we did our conversion to the cognate positions in the
;; b-c-f *and* we need these values.

;; The overestimate give inconsistency between the length before on a-c-f (which
;; is the actual length) and the difference between b-c-f start and stop (which
;; is the maximal change). Unfortunately, this can also occur in some correct
;; circumstances -- replace-match for example can both insert and change
;; simultaneously.

;; So, the only solution that I have is to use a heuristic to detect /skew/ --
;; when I think the b-c-f and a-c-f are inconsistent, and if it finds it, then
;; use a full clone (i.e. the whole buffer is dirty).

;; I need to do a full survey of all the functions that call b-c-f/a-c-f (there
;; are not that many of them!) and rewrite them to all do-the-right thing. Need
;; to learn C first!

;; #+begin_src emacs-lisp
(defun lentic-update-contents (conf &optional start stop length-before)
  "Update the contents of that-buffer with the contents of this-buffer.
update mechanism depends on CONF.
START is at most the start of the change.
STOP is at least the end of the change.
LENGTH-BEFORE is the length of area before the change."
  (let ((inhibit-read-only t)
        (no-fall-back
         (and start stop length-before)))
    (when
        (and no-fall-back
             (< (+ start length-before) (oref conf :last-change-stop)))
      (let ((diff
             (- (oref conf :last-change-stop)
                (+ start length-before))))
        (lentic-log "Skew detected %s" this-command)
        (cl-incf length-before diff)
        (cl-incf end diff)))
    (m-buffer-with-markers
        ((start-converted
          (when
              (and no-fall-back
                   (oref conf :last-change-start-converted))
            (set-marker (make-marker)
                        (oref conf :last-change-start-converted)
                        (lentic-that conf))))
         (stop-converted
          (when
              (and no-fall-back
                   (oref conf :last-change-stop-converted))
            (set-marker (make-marker)
                        (oref conf :last-change-stop-converted)
                        (lentic-that conf)))))
      ;; used these, so dump them
      (oset conf :last-change-start nil)
      (oset conf :last-change-start-converted nil)
      (oset conf :last-change-stop nil)
      (oset conf :last-change-stop-converted nil)
      (lentic-widen
          conf
        (if (not no-fall-back)
            (lentic-clone conf)
          (lentic-clone conf start stop length-before
                        start-converted stop-converted))))))

(defun lentic-update-point (conf)
  "Update the location of point in that-buffer to reflect this-buffer.
This also attempts to update any windows so that they show the
same top-left location. Update details depend on CONF."
  ;; only sync when we are told to!
  (when (oref conf :sync-point)
    (let* ((from-point
            (lentic-convert
             conf
             (m-buffer-at-point
              (lentic-this conf))))
           (from-window-start
            (lentic-convert
             conf
             (window-start
              (get-buffer-window
               (lentic-this conf))))))
      ;; clone point in buffer important when the buffer is NOT visible in a
      ;; window at all
      ;;(lentic-log "sync(front-point)(%s)" from-point)
      (with-current-buffer
          (lentic-that conf)
        (goto-char from-point))
      ;; now clone point in all the windows that are showing the buffer
      ;; and set the start of the window which is a reasonable attempt to show
      ;; the same thing.
      (mapc
       (lambda (window)
         (with-selected-window window
           (progn
             (goto-char from-point)
             (set-window-start window from-window-start))))
       (get-buffer-window-list (lentic-that conf))))))

;; #+end_src

;; Ugly, ugly, ugly. Not happy with mode-line behaviour anyway, so this will
;; probably change into the future.

;; #+begin_src emacs-lisp
;; put this here so we don't have to require lentic-mode to ensure that the
;; mode line is updated.
(defun lentic-update-display ()
  "Update the display with information about lentic's state."
  (when (fboundp 'lentic-mode-update-mode-line)
    (lentic-mode-update-mode-line)))

(defun lentic-update-all-display ()
  (when (fboundp 'lentic-mode-update-all-display)
    (lentic-mode-update-all-display)))
;; #+end_src


;; *** Utility

;; Just a couple of convenience functions for operating on eieio objects. The
;; native `oset' only allows setting a single property-value pair which is
;; irritating syntactically, and it does not return the object which prevents
;; function chaining. Taken together, these really simplify construction of
;; objects.

;; #+begin_src emacs-lisp
(defun lentic-m-oset (obj &rest plist)
  "On OBJ set all properties in PLIST.
Returns OBJ. See also `lentic-a-oset'"
  (lentic-a-oset obj plist))

(defun lentic-a-oset (obj plist)
  "On OBJ, set all properties in PLIST.
This is a utility function which just does the same as oset, but
for lots of things at once. Returns OBJ."
  (-map
   (lambda (n)
     (eieio-oset
      obj
      (car n)
      (cadr n)))
   (-partition 2 plist))
  obj)
;; #+end_src

;; ** Batch Functions

;; These functions are for batch operation on lentic buffers. Mostly, these
;; are useful for writing tests, but they can be useful for generating
;; the lentic form of a file during any automated pipeline.

;; #+begin_src emacs-lisp
(defun lentic-batch-clone-and-save-with-config (filename init)
  "Open FILENAME, set INIT function, then clone and save.

This function does potentially evil things if the file or the
lentic is open already."
  (let ((retn))
    (with-current-buffer
        (find-file-noselect filename)
      (setq lentic-init init)
      (with-current-buffer
          (car
           (lentic-init-all-create))
        (setq retn lentic-config)
        (save-buffer)
        (kill-buffer))
      (kill-buffer))
    retn))

(defun lentic-batch-clone-with-config
  (filename init)
  "Open FILENAME, set INIT function, then clone.

Return the lentic contents without properties."
  (let ((retn nil))
    (with-current-buffer
        (find-file-noselect filename)
      (setq lentic-init init)
      (with-current-buffer
          (car
           (lentic-init-all-create))
        (setq retn
              (buffer-substring-no-properties
               (point-min)
               (point-max)))
        (set-buffer-modified-p nil)
        ;; don't delete -- we haven't saved but there
        ;; might already be a file with the same name,
        ;; which will get deleted
        (oset (car lentic-config) :delete-on-exit nil)
        (kill-buffer))
      (set-buffer-modified-p nil)
      (kill-buffer))
    retn))

(provide 'lentic)

;;; lentic.el ends here
;; #+END_SRC
