;;; lentic-cookie-test.el --- Tests

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

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

;;; Code:
(require 'lentic-cookie)
(require 'ert)
(require 'assess)

(ert-deftest lentic-cookie-test-uncommented-fixup ()
  (should
   (assess=
    (with-temp-buffer
      (insert
       "# #!/usr/bin/python
")
      (lentic-cookie--uncommented-fixup-first-line-1
       (current-buffer)
       (point-max)
       "## ")
      (buffer-substring-no-properties
       (point-min)
       (point-max)))
    "#!/usr/bin/python
")))


(ert-deftest lentic-cookie-test-commented-fixup ()
  (should
   (assess=
    (with-temp-buffer
      (insert
       "#!/usr/bin/python
")
      (lentic-cookie--commented-fixup-first-line-1
       (current-buffer)
       (point-max))
      (buffer-substring-no-properties
       (point-min)
       (point-max)))
    "# #!/usr/bin/python
")))

(ert-deftest lentic-cookie-test-commented-fixup-with-comments-in ()
  (should
   (assess=
    (with-temp-buffer
      (insert
       "-- #!/usr/bin/lua
")
      (lentic-cookie--commented-fixup-first-line-1
       (current-buffer)
       (point-max))
      (buffer-substring-no-properties
       (point-min)
       (point-max)))
    "# #!/usr/bin/lua
")))





;;; lentic-cookie-test.el ends here:
