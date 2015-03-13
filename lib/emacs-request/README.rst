================================================
 Request.el -- Easy HTTP request for Emacs Lisp
================================================

.. sidebar:: Links

   * `Documentation <http://tkf.github.com/emacs-request/>`_ (at GitHub Pages)

     * `Manual <http://tkf.github.com/emacs-request/manual.html>`_

   * `Repository <https://github.com/tkf/emacs-request>`_ (at GitHub)
   * `Issue tracker <https://github.com/tkf/emacs-request/issues>`_ (at GitHub)
   * `Travis CI <https://travis-ci.org/#!/tkf/emacs-request>`_ |build-status|


What is it?
===========

Request.el is a HTTP request library with multiple backends.  It
supports url.el which is shipped with Emacs and curl command line
program.  User can use curl when s/he has it, as curl is more reliable
than url.el.  Library author can use request.el to avoid imposing
external dependencies such as curl to users while giving richer
experience for users who have curl.

As request.el is implemented in extensible manner, it is possible to
implement other backend such as wget.  Also, if future version of
Emacs support linking with libcurl, it is possible to implement a
backend using it.  Libraries using request.el automatically can
use these backend without modifying their code.

Request.el also patches url.el dynamically, to fix bugs in url.el.
See `monkey patches for url.el`_ for the bugs fixed by request.el.


Examples
========

GET::

  (request
   "http://search.twitter.com/search.json"
   :params '((q . "emacs awesome"))
   :parser 'json-read
   :success (function*
             (lambda (&key data &allow-other-keys)
               (let* ((tweet (elt (assoc-default 'results data) 0))
                      (text (assoc-default 'text tweet))
                      (user (assoc-default 'from_user_name tweet)))
                 (message "%s says %s" user text)))))

POST::

  (request
   "http://httpbin.org/post"
   :type "POST"
   :data '(("key" . "value") ("key2" . "value2"))
   ;; :data "key=value&key2=value2"  ; this is equivalent
   :parser 'json-read
   :success (function*
             (lambda (&key data &allow-other-keys)
               (message "I sent: %S" (assoc-default 'form data)))))

POST file (**WARNING**: it will send the contents of the current buffer!)::

  (request
   "http://httpbin.org/post"
   :type "POST"
   :files `(("current buffer" . ,(current-buffer))
            ("data" . ("data.csv" :data "1,2,3\n4,5,6\n")))
   :parser 'json-read
   :success (function*
             (lambda (&key data &allow-other-keys)
               (message "I sent: %S" (assoc-default 'files data)))))

Rich callback dispatch (like `jQuery.ajax`)::

  (request
   "http://httpbin.org/status/418"     ; try other codes, for example:
   ;; "http://httpbin.org/status/200"  ; success callback will be called.
   ;; "http://httpbin.org/status/400"  ; you will see "Got 400."
   :parser 'buffer-string
   :success
   (function* (lambda (&key data &allow-other-keys)
                (when data
                  (with-current-buffer (get-buffer-create "*request demo*")
                    (erase-buffer)
                    (insert data)
                    (pop-to-buffer (current-buffer))))))
   :error
   (function* (lambda (&key error-thrown &allow-other-keys&rest _)
                (message "Got error: %S" error-thrown)))
   :complete (lambda (&rest _) (message "Finished!"))
   :status-code '((400 . (lambda (&rest _) (message "Got 400.")))
                  (418 . (lambda (&rest _) (message "Got 418.")))))

Flexible PARSER option::

  (request
   "https://github.com/tkf/emacs-request/commits/master.atom"
   ;; Parse XML in response body:
   :parser (lambda () (libxml-parse-xml-region (point) (point-max)))
   :success (function*
             (lambda (&key data &allow-other-keys)
               ;; Just don't look at this function....
               (let ((get (lambda (node &rest names)
                            (if names
                                (apply get
                                       (first (xml-get-children
                                               node (car names)))
                                       (cdr names))
                              (first (xml-node-children node))))))
                 (message "Latest commit: %s (by %s)"
                          (funcall get data 'entry 'title)
                          (funcall get data 'entry 'author 'name))))))

PUT JSON data::

  (request
   "http://httpbin.org/put"
   :type "PUT"
   :data (json-encode '(("key" . "value") ("key2" . "value2")))
   :headers '(("Content-Type" . "application/json"))
   :parser 'json-read
   :success (function*
             (lambda (&key data &allow-other-keys)
               (message "I sent: %S" (assoc-default 'json data)))))


Compatibility / backends
========================

Supported Emacs versions:

====================== ========================== =====================
 Emacs version          Does request.el work?      Tested on Travis CI
                                                   |build-status|
====================== ========================== =====================
 GNU Emacs 24.3-devel   yes (as of this writing)   yes
 GNU Emacs 24.2         yes                        yes
 GNU Emacs 24.1         yes                        no
 GNU Emacs 23.4         yes                        no
 GNU Emacs 23.3         yes                        yes
 GNU Emacs 23.1         yes (as of this writing)   no
 GNU Emacs < 23         ?                          no
====================== ========================== =====================


Supported backends:

========== ==================== ================ =========================
 Backends   Remarks              Multipart Form   Automatic Decompression
========== ==================== ================ =========================
 url.el     Included in Emacs
 curl       Reliable             ✔               ✔
========== ==================== ================ =========================


Monkey patches for url.el
=========================

Patches for following bugs are applied when request.el is loaded.
If the patch is not required for the Emacs version you are using, it
will not be applied.

- `#12374 - 24.1.50;
  Incorrect redirect in url-retrieve when URL contains port number -
  GNU bug report logs
  <http://debbugs.gnu.org/cgi/bugreport.cgi?bug=12374>`_

  (patch: `PATCH Fix bug 12374 treat port number when expanding URL
  <http://article.gmane.org/gmane.emacs.devel/155698>`_)

- `#11469 - 24.1.50; url-retrieve with PUT method fails every two
  times - GNU bug report logs
  <http://debbugs.gnu.org/cgi/bugreport.cgi?bug=11469>`_

  (patch: `PATCH Fix bug 11469 propagate url request vars properly
  <http://article.gmane.org/gmane.emacs.devel/155697>`_)


Related projects
================

`leathekd/grapnel · GitHub <https://github.com/leathekd/grapnel>`_:
  "HTTP request for Emacs lib built on curl with flexible callback dispatch"

`cinsk/emacs-curl · GitHub <https://github.com/cinsk/emacs-curl>`_:
  "CURL wrapper for Emacs"

`furl-el - Google Project Hosting <http://code.google.com/p/furl-el/>`_:
  "A wrapper for url.el that adds a nicer API and the ability to make
  multipart POST requests."


License
=======

Request.el is free software under GPL v3.
See COPYING file for details.


.. |build-status|
   image:: https://secure.travis-ci.org/tkf/emacs-request.png
           ?branch=master
   :target: http://travis-ci.org/tkf/emacs-request
   :alt: Build Status
