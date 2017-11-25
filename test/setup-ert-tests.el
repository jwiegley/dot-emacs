;;; setup-ert-tests.el --- Provide needed forms -*- lexical-binding: t; -*-

;; Copyright (C) 2014-2017  Andreas Röhler

;; Author: Andreas Röhler <andreas.roehler@online.de>
;; Keywords: lisp

;; This program is free software; you can redistribute it and/or modify
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

;;; Code:

(defvar py-debug-p nil
  "Avoid error")

;; (setq py-debug-p t)

(defvar py-kugel-text
"class kugel(object):
    zeit = time.strftime('%Y%m%d--%H-%M-%S')
    def pylauf(self):
        \"\"\"Eine Doku fuer pylauf\"\"\"
        ausgabe = [\" \",\" \",\" \",\" \",\" \",\" \",\" \",\" \", \" \"]
        if treffer in gruen:
            # print \"0, Gruen\"
        elif treffer in schwarz:
            # print \"%i, Schwarz\" % (treffer)
            ausgabe[1] = treffer
        else:
            # print \"%i, manque\" % (treffer)
            ausgabe[7] = treffer
")

(setq py-kugel-text "class kugel(object):
    zeit = time.strftime('%Y%m%d--%H-%M-%S')
    def pylauf(self):
        \"\"\"Eine Doku fuer pylauf\"\"\"
        ausgabe = [\" \",\" \",\" \",\" \",\" \",\" \",\" \",\" \", \" \"]
        if treffer in gruen:
            # print \"0, Gruen\"
        elif treffer in schwarz:
            # print \"%i, Schwarz\" % (treffer)
            ausgabe[1] = treffer
        else:
            # print \"%i, manque\" % (treffer)
            ausgabe[7] = treffer
")

(defvar py-forward-text "
# {{
class bar:
    def foo ():
        try:
            if foo:
                for a in b:
                    print('%(language)s has %(number)03d quote types.' %
       {'language': \"Python\", \"number\": 2})

            elif bar:
                for a in b:
                    pass
            else:
                for a in b:
                    pass
# }}
        except:
            block2
")

(defvar py-up-text "
def foo():
    if True:
        def bar():
            pass
    elif False:
        def baz():
            pass
    else:
        try:
            1 == 1
        except True:
            def foo1():
                if True:
                    def bar1():
                        pass
                elif False:
                    def baz1():
                        pass
                else:
                    try:
                        1 == 1
                    except True:
                        pass
                    else True:
                        pass
                    finally:
                        pass
        else True:
            pass
        finally:
            pass
")

(defmacro py-test-with-temp-buffer-point-min (contents &rest body)
  "Create temp buffer in `python-mode' inserting CONTENTS.
BODY is code to be executed within the temp buffer.  Point is
 at the beginning of buffer."
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (let (hs-minor-mode py--imenu-create-index-p)
       (insert ,contents)
       (python-mode)
       (goto-char (point-min))
       (when py-debug-p (switch-to-buffer (current-buffer))
	     (font-lock-fontify-buffer))
       ,@body)
     ;; (sit-for 0.1)
     ))

(defmacro py-test-with-temp-buffer (contents &rest body)
  "Create temp buffer in `python-mode' inserting CONTENTS.
BODY is code to be executed within the temp buffer.  Point is
 at the end of buffer."
  (declare (indent 1) (debug t))
  `(with-temp-buffer
     (let (hs-minor-mode py--imenu-create-index-p)
       (insert ,contents)
       (python-mode)
       ;; (when py-debug-p (switch-to-buffer (current-buffer))
       ;; 	     (font-lock-fontify-buffer))
       ,@body)
     ;; (sit-for 0.1)
     ))

(provide 'setup-ert-tests)
;; setup-ert-tests.el ends here
