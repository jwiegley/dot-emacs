;;; helm-company-test.el --- helm-company: tests

;; Copyright (C)  2014 Yasuyuki Oka <yasuyk@gmail.com>

;; Author: Yasuyuki Oka <yasuyk@gmail.com>

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

(require 'helm)

;;;; Helpers

(defun helm-company-test/helm-window-lib-p ()
  (window-live-p (get-buffer-window helm-buffer)))

;;;; helm-company

(ert-deftest helm-company-test/unavailable-with-read-only-mode ()
  (let ((company-minimum-prefix-length 10)
        (word "defu") ret)
    (with-temp-buffer
      (emacs-lisp-mode)
      (company-mode 1)
      (insert word)
      (read-only-mode 1)
      (goto-char (point-min))
      (re-search-forward word)
      (helm-company))
    (should-not (helm-company-test/helm-window-lib-p))))


(provide 'helm-company-test)

;; Local Variables:
;; coding: utf-8
;; End:

;;; helm-company-test.el ends here
