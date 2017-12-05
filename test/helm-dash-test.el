;;; helm-dash-test.el --- Helm-dash tests
;; Copyright (C) 2013-2014  Raimon Grau
;; Copyright (C) 2013-2014  Toni Reina

;; Author: Raimon Grau <raimonster@gmail.com>
;;         Toni Reina  <areina0@gmail.com>
;; Version: 0.1
;; Package-Requires: ((helm "0.0.0"))
;; Keywords: docs

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
;;
;;; Commentary:

;;; Code:

;;;; helm-dash-maybe-narrow-docsets

(ert-deftest helm-dash-maybe-narrow-docsets-test/filtered ()
  "Should return a list with filtered connections."
  (let ((pattern "Go ")
        (helm-dash-docsets-path "/tmp/.docsets")
        (helm-dash-common-docsets '("Redis" "Go" "CSS" "C" "C++"))
        (helm-dash-connections
         '(("Redis" "/tmp/.docsets/Redis.docset/Contents/Resources/docSet.dsidx" "DASH")
           ("Go" "/tmp/.docsets/Go.docset/Contents/Resources/docSet.dsidx" "DASH")
           ("C" "/tmp/.docsets/C.docset/Contents/Resources/docSet.dsidx" "DASH")
           ("C++" "/tmp/.docsets/C++.docset/Contents/Resources/docSet.dsidx" "DASH")
           ("CSS" "/tmp/.docsets/CSS.docset/Contents/Resources/docSet.dsidx" "ZDASH"))))
    (should (equal (helm-dash-maybe-narrow-docsets pattern)
                   '(("Go" "/tmp/.docsets/Go.docset/Contents/Resources/docSet.dsidx" "DASH"))))

    (should (equal "C" (caar (helm-dash-maybe-narrow-docsets "C foo"))))
    (should (equal "C++" (caar (helm-dash-maybe-narrow-docsets "C++ foo"))))
    (should (equal "C" (caar (helm-dash-maybe-narrow-docsets "c foo"))))))

(ert-deftest helm-dash-maybe-narrow-docsets-test/not-filtered ()
  "Should return all current connections because the pattern doesn't match with any connection."
  (let ((pattern "FOOOO ")
	(helm-dash-docsets-path "/tmp/.docsets")
	(helm-dash-common-docsets '("Redis" "Go" "CSS"))
	(helm-dash-connections
	 '(("Redis" "/tmp/.docsets/Redis.docset/Contents/Resources/docSet.dsidx" "DASH")
	   ("Go" "/tmp/.docsets/Go.docset/Contents/Resources/docSet.dsidx" "DASH")
	   ("CSS" "/tmp/.docsets/CSS.docset/Contents/Resources/docSet.dsidx" "ZDASH"))))
    (should (equal (helm-dash-maybe-narrow-docsets pattern) helm-dash-connections))))


;;;; helm-dash-sub-docset-name-in-pattern

(ert-deftest helm-dash-sub-docset-name-in-pattern-test/with-docset-name ()
  ""
  (let ((pattern "Redis BLPOP")
	(docset "Redis"))
    (should (equal (helm-dash-sub-docset-name-in-pattern pattern docset) "BLPOP"))))

(ert-deftest helm-dash-sub-docset-name-in-pattern-test/without-docset-name ()
  ""
  (let ((pattern "BLPOP")
	(docset "Redis"))
    (should (equal (helm-dash-sub-docset-name-in-pattern pattern docset) pattern))))

(ert-deftest helm-dash-sub-docset-name-in-pattern-test/with-special-docset-name ()
  ""
  (let ((pattern "C++ printf")
	(docset "C++"))
    (should (equal (helm-dash-sub-docset-name-in-pattern pattern docset) "printf"))))

;;;; helm-dash-result-url

(ert-deftest helm-dash-result-url/checks-docset-types ()
  (should (string-match-p "Documents/three#anchor$"
                          (helm-dash-result-url "Python 3" "three" "anchor")))
  (should (string-match-p "Documents/three#anchor$"
                          (helm-dash-result-url "Css" "three#anchor" nil)))
  (should (string-match-p "Documents/three#anchor$"
                          (helm-dash-result-url "Redis" "three#anchor"))))

(ert-deftest helm-dash-result-url/remove-dash-entry-tag-from-url ()
  (should (string-match-p "Documents/three#anchor$"
                          (helm-dash-result-url "Python 3" "three<dash_entry_menuDescription=android.provider.ContactsContract.CommonDataKinds.Website>" "anchor"))))

;;;; helm-dash-docsets-path

(ert-deftest helm-dash-docsets-path-test/relative-path ()
  "Should return the absolute path."
  (let ((helm-dash-docsets-path "~/.emacs.d/helm-dash-docsets")
	(home-path (getenv "HOME")))
    (should (equal (helm-dash-docsets-path)
		   (format "%s/.emacs.d/helm-dash-docsets" home-path)))))

;;;; helm-dash-add-to-kill-ring

(ert-deftest helm-dash-add-to-kill-ring-test ()
  "Should add to kill ring a string with a call to `helm-dash-browse-url'"
  (let ((results '(Redis ("func" "Documents/blpop.html"))))
    (helm-dash-add-to-kill-ring results))
  (should (equal (current-kill 0 t)
		 "(helm-dash-browse-url '(Redis (\"func\" \"Documents/blpop.html\")))")))

;;;; helm-dash-official-docsets

(ert-deftest helm-dash-official-docsets-test ()
  "Should return a list of available docsets."
  (let ((docsets (helm-dash-official-docsets)))
    (should (member "Ruby" docsets))
    ;; ignored docset:
    (should-not (member "Man_Pages" docsets))))

;;;; helm-dash-activate-docset

(ert-deftest helm-dash-activate-docset ()
  (let ((helm-dash-common-docsets '("Redis" "Go" "CSS"))
	(helm-dash-connections
	 '(("Redis" "/tmp/.docsets/Redis.docset/Contents/Resources/docSet.dsidx" "DASH")
	   ("Go" "/tmp/.docsets/Go.docset/Contents/Resources/docSet.dsidx" "DASH")
	   ("CSS" "/tmp/.docsets/CSS.docset/Contents/Resources/docSet.dsidx" "ZDASH"))))
    (helm-dash-activate-docset "Clojure")
    (should (equal'("Clojure" "Redis" "Go" "CSS") helm-dash-common-docsets))
    (should (equal nil helm-dash-connections))))

;; helm-dash-buffer-local-docsets

(ert-deftest helm-dash-buffer-local-docsets-narrowing ()
  (let ((c-buffer nil)
        (helm-dash-connections
         '(("Go" "/tmp/.docsets/Go.docset/Contents/Resources/docSet.dsidx" "DASH")
           ("C" "/tmp/.docsets/C.docset/Contents/Resources/docSet.dsidx" "DASH")
           ("CSS" "/tmp/.docsets/CSS.docset/Contents/Resources/docSet.dsidx" "ZDASH"))))
    (with-temp-buffer
      (setq c-buffer (current-buffer))
      (setq-local helm-dash-docsets (list "C"))

      (with-temp-buffer
        (setq-local helm-dash-docsets (list "Go"))
        (should (equal (helm-dash-maybe-narrow-docsets "*")
                       '(("Go" "/tmp/.docsets/Go.docset/Contents/Resources/docSet.dsidx" "DASH"))))

        (with-current-buffer c-buffer
          (should (equal (helm-dash-maybe-narrow-docsets "*")
                         '(("C" "/tmp/.docsets/C.docset/Contents/Resources/docSet.dsidx" "DASH"))))
          )))))

;; helm-dash-sql-query

(ert-deftest helm-dash-sql-query/DASH-docset-type ()
  (should (equal "SELECT t.type, t.name, t.path FROM searchIndex t WHERE t.name like '%blpop%' ORDER BY LENGTH(t.name), LOWER(t.name) LIMIT 1000"
		 (helm-dash-sql-query "DASH" "blpop"))))

(ert-deftest helm-dash-sql-query/ZDASH-docset-type ()
  (should (equal "SELECT ty.ZTYPENAME, t.ZTOKENNAME, f.ZPATH, m.ZANCHOR FROM ZTOKEN t, ZTOKENTYPE ty, ZFILEPATH f, ZTOKENMETAINFORMATION m WHERE ty.Z_PK = t.ZTOKENTYPE AND f.Z_PK = m.ZFILE AND m.ZTOKEN = t.Z_PK AND t.ZTOKENNAME like '%blpop%' ORDER BY LENGTH(t.ZTOKENNAME), LOWER(t.ZTOKENNAME) LIMIT 1000"
		 (helm-dash-sql-query "ZDASH" "blpop"))))

(ert-deftest helm-dash-sql-query/UNKNOWN-docset-type ()
  (should (equal nil (helm-dash-sql-query "FOO" "blpop"))))

(provide 'helm-dash-test)

;;; helm-dash-test ends here
