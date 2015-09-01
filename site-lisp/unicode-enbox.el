;;; unicode-enbox.el --- Surround a string with box-drawing characters
;;
;; Copyright (c) 2012 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/unicode-enbox
;; URL: http://raw.github.com/rolandwalker/unicode-enbox/master/unicode-enbox.el
;; Version: 0.1.3
;; Last-Updated: 14 Sep 2012
;; EmacsWiki: UnicodeEnbox
;; Package-Requires: ((string-utils "0.0.1") (ucs-utils "0.7.2") (persistent-soft "0.8.6") (pcache "0.2.3"))
;; Keywords: extensions, interface
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'unicode-enbox)
;;
;;     (insert "\n" (unicode-enbox "testing"))
;;
;; Explanation
;;
;; Unicode-enbox.el has no user-level interface; it is only useful
;; for programming in Emacs Lisp.
;;
;; This library provides two functions:
;;
;;     unicode-enbox
;;     unicode-enbox-debox
;;
;; which can be used to add/remove box-drawing characters around
;; a single- or multi-line string.
;;
;; To use unicode-enbox, place the unicode-enbox.el library somewhere
;; Emacs can find it, and add the following to your ~/.emacs file:
;;
;;     (require 'unicode-enbox)
;;
;; See Also
;;
;;     M-x customize-group RET unicode-enbox RET
;;
;; Notes
;;
;; For good monospaced box-drawing characters, it is recommended to
;; install the free DejaVu Sans Mono font and use unicode-fonts.el.
;; If unicode-fonts.el is too heavy for your needs, try adding the
;; following bit to your ~/.emacs file:
;;
;;     (set-fontset-font "fontset-default"
;;                       (cons (decode-char 'ucs #x2500)  (decode-char 'ucs #x257F))
;;                       '("DejaVu Sans Mono" . "iso10646-1"))
;;
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 24.3-devel     : yes, at the time of writing
;;     GNU Emacs version 24.1 & 24.2    : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.3 and lower : no
;;
;;     Requires string-utils.el, ucs-utils.el
;;
;; Bugs
;;
;; TODO
;;
;;     Interactive command that works on rectangles.
;;
;;     Logic in unicode-enbox is not clear, eg where it falls through
;;     to 'smart.
;;
;;     Detect lines of full dashes, replace with box chars and
;;     connectors, then would need more clever deboxing - or just
;;     store the original string in a property - done?
;;
;;     Detect acutal width of unicode characters in GUI - char-width
;;     does not return the right answer.
;;
;;     Generalize to comment boxes with multi-character drawing
;;     elements.
;;
;;; License
;;
;; Simplified BSD License:
;;
;; Redistribution and use in source and binary forms, with or
;; without modification, are permitted provided that the following
;; conditions are met:
;;
;;    1. Redistributions of source code must retain the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer.
;;
;;    2. Redistributions in binary form must reproduce the above
;;       copyright notice, this list of conditions and the following
;;       disclaimer in the documentation and/or other materials
;;       provided with the distribution.
;;
;; This software is provided by Roland Walker "AS IS" and any express
;; or implied warranties, including, but not limited to, the implied
;; warranties of merchantability and fitness for a particular
;; purpose are disclaimed.  In no event shall Roland Walker or
;; contributors be liable for any direct, indirect, incidental,
;; special, exemplary, or consequential damages (including, but not
;; limited to, procurement of substitute goods or services; loss of
;; use, data, or profits; or business interruption) however caused
;; and on any theory of liability, whether in contract, strict
;; liability, or tort (including negligence or otherwise) arising in
;; any way out of the use of this software, even if advised of the
;; possibility of such damage.
;;
;; The views and conclusions contained in the software and
;; documentation are those of the authors and should not be
;; interpreted as representing official policies, either expressed
;; or implied, of Roland Walker.
;;
;;; Code:
;;

;;; requires

;; for callf
(require 'cl)

(autoload 'string-utils-has-darkspace-p  "string-utils" "Test whether OBJ, when coerced to a string, has any non-whitespace characters.")
(autoload 'string-utils-pad-list         "string-utils" "Pad each member of STR-LIST to match the longest width.")

(autoload 'ucs-utils-char                "ucs-utils"    "Return the character corresponding to NAME, a UCS name.")
(autoload 'ucs-utils-string              "ucs-utils"    "Return a string corresponding to SEQUENCE of UCS names or characters.")

;;; variables

(defvar unicode-enbox-box-drawing-characters
  '(("Standard"
     (top-left-corner           . "Box Drawings Light Down and Right"        )
     (top-right-corner          . "Box Drawings Light Down and Left"         )
     (bottom-left-corner        . "Box Drawings Light Up and Right"          )
     (bottom-right-corner       . "Box Drawings Light Up and Left"           )
     (horizontal-line           . "Box Drawings Light Horizontal"            )
     (vertical-line             . "Box Drawings Light Vertical"              )
     (vertical-line-left-conx   . "Box Drawings Light Vertical and Left"     )
     (vertical-line-right-conx  . "Box Drawings Light Vertical and Right"    ))
    ("Rounded"
     (top-left-corner           . "Box Drawings Light Arc Down and Right"   )
     (top-right-corner          . "Box Drawings Light Arc Down and Left"    )
     (bottom-left-corner        . "Box Drawings Light Arc Up and Right"     )
     (bottom-right-corner       . "Box Drawings Light Arc Up and Left"      )
     (horizontal-line           . "Box Drawings Light Horizontal"           )
     (vertical-line             . "Box Drawings Light Vertical"             )
     (vertical-line-left-conx   . "Box Drawings Light Vertical and Left"    )
     (vertical-line-right-conx  . "Box Drawings Light Vertical and Right"   ))
    ("Heavy"
     (top-left-corner           . "Box Drawings Heavy Down and Right"       )
     (top-right-corner          . "Box Drawings Heavy Down and Left"        )
     (bottom-left-corner        . "Box Drawings Heavy Up and Right"         )
     (bottom-right-corner       . "Box Drawings Heavy Up and Left"          )
     (horizontal-line           . "Box Drawings Heavy Horizontal"           )
     (vertical-line             . "Box Drawings Heavy Vertical"             )
     (vertical-line-left-conx   . "Box Drawings Heavy Vertical and Left"    )
     (vertical-line-right-conx  . "Box Drawings Heavy Vertical and Right"   ))
    ("Double"
     (top-left-corner           . "Box Drawings Double Down and Right"      )
     (top-right-corner          . "Box Drawings Double Down and Left"       )
     (bottom-left-corner        . "Box Drawings Double Up and Right"        )
     (bottom-right-corner       . "Box Drawings Double Up and Left"         )
     (horizontal-line           . "Box Drawings Double Horizontal"          )
     (vertical-line             . "Box Drawings Double Vertical"            )
     (vertical-line-left-conx   . "Box Drawings Double Vertical and Left"   )
     (vertical-line-right-conx  . "Box Drawings Double Vertical and Right"  ))
    ("ASCII"
     (top-left-corner           . ?.)
     (top-right-corner          . ?.)
     (bottom-left-corner        . ?+)
     (bottom-right-corner       . ?+)
     (horizontal-line           . ?-)
     (vertical-line             . ?|)
     (vertical-line-left-conx   . ?|)
     (vertical-line-right-conx  . ?|))
    ("Spaces"
     (top-left-corner           . ?\s)
     (top-right-corner          . ?\s)
     (bottom-left-corner        . ?\s)
     (bottom-right-corner       . ?\s)
     (horizontal-line           . ?\s)
     (vertical-line             . ?\s)
     (vertical-line-left-conx   . ?\s)
     (vertical-line-right-conx  . ?\s)))
    "Alternative sets of box-drawing characters.")

;;; customizable variables

;;;###autoload
(defgroup unicode-enbox nil
  "Surround a string with box-drawing characters."
  :version "0.1.3"
  :link '(emacs-commentary-link "unicode-enbox")
  :prefix "unicode-enbox-"
  :group 'extensions)

(defcustom unicode-enbox-default-type "Standard"
  "Default box drawing characters to use for `unicode-enbox'."
  :type `(choice ,@(mapcar #'(lambda (x)
                               (list 'const (car x)))
                           unicode-enbox-box-drawing-characters))
  :group 'unicode-enbox)

;;; utility functions

;;;###autoload
(defun unicode-enbox-unicode-display-p ()
  "Return t if the current display supports unicode box characters."
  (ucs-utils-char "Box Drawings Light Down and Right" nil 'cdp))

;;; principal interface

;;;###autoload
(defun unicode-enbox-debox (str-val &optional force box-type)
  "Remove box drawing from the border of STR-VAL.

Unless optional FORCE is set, do not attempt to debox unless
`unicode-enbox' was previously run on STR-VAL.  This is detected
by means of the text property `unicode-enbox-type', or falls
back to `unicode-enbox-default-type'.

Optional BOX-TYPE overrides the `unicode-enbox-type' text property
or default type."
  (if (and (not force)
           (not (get-text-property 0 'unicode-enbox-type str-val)))
      str-val
    (callf or box-type (get-text-property 0 'unicode-enbox-type str-val) unicode-enbox-default-type)
    (destructuring-bind (top-left-corner
                         top-right-corner
                         bottom-left-corner
                         bottom-right-corner
                         horizontal-line
                         vertical-line
                         vertical-line-left-conx
                         vertical-line-right-conx)
        (mapcar #'(lambda (cell)
                    (ucs-utils-string (cdr cell) ?. 'cdp))
                (cdr (assoc-string box-type unicode-enbox-box-drawing-characters)))
      (let ((str-list (split-string str-val "\n")))
        (when (and str-list
                   (string-match-p (concat "\\`[" top-left-corner horizontal-line top-right-corner "]+\\'")
                                   (car str-list)))
          (pop str-list))
        (callf nreverse str-list)
        (when (and str-list
                   (string-match-p (concat "\\`[" bottom-left-corner horizontal-line bottom-right-corner "]+\\'")
                                   (car str-list)))
          (pop str-list))
        (callf nreverse str-list)
        (callf2 mapcar #'(lambda (str)
                           (replace-regexp-in-string
                            (concat "\\`[" vertical-line vertical-line-left-conx vertical-line-right-conx "]" ) "" str))
                str-list)
        (callf2 mapcar #'(lambda (str)
                           (replace-regexp-in-string
                            (concat "["    vertical-line vertical-line-left-conx vertical-line-right-conx "]\\'") "" str))
                str-list)
        (dolist (str str-list)
          (remove-text-properties 0 (length str) '(unicode-enbox-type nil) str))
        (mapconcat 'identity str-list "\n")))))

;;;###autoload
(defun unicode-enbox (str-val &optional unicode-only side-mode top-mode force box-type)
  "Return multi-line STR-VAL enclosed in a box.

Unicode line-drawing characters are used if possible.  When
optional UNICODE-ONLY is set, boxing is only performed when
Unicode line-drawing characters are available on the current
display.

Optional SIDE-MODE defaults to 'smart, but can be set to 'append
or 'overwrite to control whether side box characters overwrite
content or append/prepend to it.

Optional TOP-MODE defaults to 'smart, but can be set to 'append
or 'overwrite to control whether top/bottom box characters
overwrite content or append/prepend to it.

Unless optional FORCE is set, do not attempt to debox unless
`unicode-enbox' was previously run on STR-VAL.  This is detected
by means of the text property `unicode-enbox-type'.

Optional BOX-TYPE overrides the `unicode-enbox-default-type'
customizable variable, which defaults to \"Standard\".

The text property `unicode-enbox-type' will be set on the return
value to match BOX-TYPE."
  (if (and unicode-only
           (not (unicode-enbox-unicode-display-p)))
      str-val
    ;; else
    (when (or force
              (get-text-property 0 'unicode-enbox-type str-val))
      (callf unicode-enbox-debox str-val force))
    (callf or box-type unicode-enbox-default-type)
    (unless (unicode-enbox-unicode-display-p)
      (setq box-type "ASCII"))
    (callf or side-mode 'smart)
    (callf or top-mode 'smart)
    (assert (memq side-mode '(smart append overwrite)) nil "Bad SIDE-MODE value %s" side-mode)
    (assert (memq top-mode  '(smart append overwrite)) nil "Bad TOP-MODE value %s"  top-mode)
    (destructuring-bind (top-left-corner
                         top-right-corner
                         bottom-left-corner
                         bottom-right-corner
                         horizontal-line
                         vertical-line
                         vertical-line-left-conx
                         vertical-line-right-conx)
        (mapcar #'(lambda (cell)
                    (ucs-utils-char (cdr cell) ?. 'cdp))
                (cdr (assoc-string box-type unicode-enbox-box-drawing-characters)))

        (let* ((str-list (string-utils-pad-list (split-string str-val "\n")))
               (string-starts (mapconcat #'(lambda (str)
                                             (substring str 0 1))                            str-list ""))
               (string-ends   (mapconcat #'(lambda (str)
                                             (substring str (1- (length str)) (length str))) str-list ""))
               (string-top    (copy-seq (car str-list)))
               (string-bottom (copy-seq (car (last str-list)))))

          ;; left
          (if (or (eq side-mode 'append)
                  (< (length string-top) 2)
                  (and (eq side-mode 'smart)
                       (string-utils-has-darkspace-p string-starts)))
              ;; then prepend left side
              (callf2 mapcar #'(lambda (str)
                                 (concat (vector vertical-line) str)) str-list)
            ;; else overwrite left side
            (callf2 mapcar #'(lambda (str)
                               (setf (aref str 0) vertical-line) str) str-list))

          ;; right
          (if (or (eq side-mode 'append)
                  (< (length string-top) 2)
                  (and (eq side-mode 'smart)
                       (string-utils-has-darkspace-p string-ends)))
              ;; then append right side
              (callf2 mapcar #'(lambda (str)
                                 (concat str (vector vertical-line))) str-list)
            ;; else overwrite right side
            (callf2 mapcar #'(lambda (str)
                               (setf (aref str (1- (length str))) vertical-line) str) str-list))

          ;; delay measuring width until left and right are done
          (let ((top-assembly     (concat (vector top-left-corner)          (make-vector (- (length (car str-list)) 2) horizontal-line) (vector top-right-corner)))
                (bottom-assembly  (concat (vector bottom-left-corner)       (make-vector (- (length (car str-list)) 2) horizontal-line) (vector bottom-right-corner)))
                (divider-assembly (concat (vector vertical-line-right-conx) (make-vector (- (length (car str-list)) 2) horizontal-line) (vector vertical-line-left-conx))))

            ;; top
            (if (or (eq top-mode 'append)
                    (< (length str-list) 2)
                    (and (eq top-mode 'smart)
                         (string-utils-has-darkspace-p string-top)))
                ;; then prepend top side
                (push top-assembly str-list)
              ;; else overwrite top side
              (setf (car str-list) top-assembly))

            ;; bottom
            (if (or (eq top-mode 'append)
                    (< (length str-list) 2)
                    (and (eq top-mode 'smart)
                         (string-utils-has-darkspace-p string-bottom)))
                ;; then append bottom side
                (callf append str-list (list bottom-assembly))
              ;; else overwrite bottom side
              (setf (car (last str-list)) bottom-assembly))

            ;; horizontal dividers
            (callf2 mapcar #'(lambda (str)
                               (if (string-match-p (concat "\\`"
                                                           (regexp-quote (string vertical-line))
                                                           "--[ \t-]*"
                                                           (regexp-quote (string vertical-line))
                                                           "\\'") str)
                                   divider-assembly
                                 str))
                    str-list))

          ;; glue together and propertize the return value
          (propertize (mapconcat 'identity str-list "\n") 'unicode-enbox-type box-type)))))

(provide 'unicode-enbox)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;
;; LocalWords:  UnicodeEnbox ARGS alist utils enbox deboxing debox
;; LocalWords:  callf
;;

;;; unicode-enbox.el ends here
