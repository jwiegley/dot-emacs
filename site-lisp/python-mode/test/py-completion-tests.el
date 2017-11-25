;;; py-completion-tests.el --- Test completion for available Python shell

;; Author: Andreas Roehler <andreas.roehler@online.de>
;; Keywords: languages, convenience

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

;;; Commentary: Edit `py-test-pyshellname-list' before
;; running this test-builder or give a list of shells as
;; arguments

;;; Code:

(defun python-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env python
pri"))
    (py-bug-tests-intern 'python-complete-base arg teststring)))

(defun python-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun usr-bin-python-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/python
pri"))
    (py-bug-tests-intern 'usr-bin-python-complete-base arg teststring)))

(defun usr-bin-python-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun usr-bin-python2.7-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/python2.7
pri"))
    (py-bug-tests-intern 'usr-bin-python2.7-complete-base arg teststring)))

(defun usr-bin-python2.7-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun home-speck-arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /home/speck/arbeit/python/epdfree/epd_free-7.2-2-rh5-x86/bin/python2.7
pri"))
    (py-bug-tests-intern 'home-speck-arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-complete-base arg teststring)))

(defun home-speck-arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun usr-bin-python3-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/python3
pri"))
    (py-bug-tests-intern 'usr-bin-python3-complete-base arg teststring)))

(defun usr-bin-python3-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun usr-bin-python3.1-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/python3.1
pri"))
    (py-bug-tests-intern 'usr-bin-python3.1-complete-base arg teststring)))

(defun usr-bin-python3.1-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun ipython-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/env ipython
pri"))
    (py-bug-tests-intern 'ipython-complete-base arg teststring)))

(defun ipython-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun usr-bin-ipython-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /usr/bin/ipython
pri"))
    (py-bug-tests-intern 'usr-bin-ipython-complete-base arg teststring)))

(defun usr-bin-ipython-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))

(defun home-speck-arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-complete-test (&optional arg)
  (interactive "p")
  (let ((teststring "#! /home/speck/arbeit/python/epd_free-7.1-2-rh5-x86/bin/ipython
pri"))
    (py-bug-tests-intern 'home-speck-arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-complete-base arg teststring)))

(defun home-speck-arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-complete-base ()
  (save-excursion (completion-at-point))
  ;; (sit-for 0.1)
  (assert (looking-at "nt") nil "py-completion-at-point-test failed"))


(provide "py-completion-tests")
;;; py-completion-tests ends here

