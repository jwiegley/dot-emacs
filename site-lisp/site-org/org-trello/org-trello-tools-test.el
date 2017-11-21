;;; org-trello-tools-test.el ---

;; Copyright (C) 2016-2017  Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>

;; Author: Antoine R. Dumont (@ardumont) <antoine.romain.dumont@gmail.com>
;; Keywords:

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

(require 'org-trello-tools)
(require 'ert)
(require 'el-mock)

(ert-deftest test-orgtrello-tests-ask-for-buffer-or-fallback-to-default ()
  (should (equal :default-buffer
                 (with-mock
                   (mock (region-active-p) => nil)
                   (mock (current-buffer) => :current)
                   (mock (buffer-name :current) => :default-buffer)
                   (orgtrello-tests-ask-for-buffer-or-fallback-to-default))))
  (should (equal :result-with-region
                 (with-mock
                   (mock (region-active-p) => t)
                   (mock (region-beginning) => :start)
                   (mock (region-end) => :end)
                   (mock (buffer-substring :start :end) => :result-with-region)
                   (orgtrello-tests-ask-for-buffer-or-fallback-to-default))))
  (should (equal :res
                 (with-mock
                   (mock (read-string "Buffer name: ") => :res)
                   (orgtrello-tests-ask-for-buffer-or-fallback-to-default :buffer)))))

(ert-deftest test-orgtrello-tests-ns-file-from-current-buffer ()
  (should (equal "./test/org-trello-proxy-test.el"
                 (orgtrello-tests-ns-file-from-current-buffer "org-trello-proxy.el")))
  (should (equal "./test/org-trello-buffer-test.el"
                 (orgtrello-tests-ns-file-from-current-buffer "org-trello-buffer.el")))
  (should (equal "./test/org-trello-test.el"
                 (orgtrello-tests-ns-file-from-current-buffer "org-trello.el"))))


(provide 'org-trello-tools-test)
;;; org-trello-tools-test.el ends here
