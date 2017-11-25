;;; flycheck-haskell-test.el --- Flycheck Haskell: Test suite  -*- lexical-binding: t; -*-

;; Copyright (C) 2014, 2015  Sebastian Wiesner <swiesner@lunaryorn.com>

;; Author: Sebastian Wiesner <swiesner@lunaryorn.com>

;; This file is not part of GNU Emacs.

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

;; The test suite for Flycheck Haskell.

;;; Code:

(require 'flycheck-haskell)

(require 'let-alist)
(require 'cl-lib)
(require 'dash)
(require 'ert)


;;; Directories

(defconst flycheck-haskell-test-dir
  (file-name-directory (if load-in-progress load-file-name (buffer-file-name)))
  "Directory of the test suite.")

(defconst flycheck-haskell-test-cabal-file
  (expand-file-name "flycheck-haskell-test.cabal" flycheck-haskell-test-dir)
  "Cabal file for our test suite.")

(defconst flycheck-haskell-test-sandbox-file
  (expand-file-name "cabal.sandbox.config" flycheck-haskell-test-dir)
  "Sandbox configuration file for our test suite.")

(defconst flycheck-haskell-test-config-file
  (expand-file-name "cabal.config" flycheck-haskell-test-dir)
  "Cabal configuration file for our test suite.")


;;; Helpers

(defun flycheck-haskell-read-test-config ()
  "Read the Cabal configuration from the test file."
  (flycheck-haskell-read-cabal-configuration flycheck-haskell-test-cabal-file))

(defmacro flycheck-haskell-test-with-cache (&rest body)
  "Run BODY and clear the config cache afterwards."
  (declare (indent 0))
  `(unwind-protect (progn ,@body)
     (flycheck-haskell-clear-config-cache)))

(defmacro flycheck-haskell-test-with-fake-file (&rest body)
  "Run BODY with a fake file buffer."
  (declare (indent 0))
  `(with-temp-buffer
     (let* ((default-directory flycheck-haskell-test-dir)
            (buffer-file-name (expand-file-name "test.hs")))
       ,@body)))

(defun flycheck-haskell--concat-dirs (&rest dirs)
  "Combine multiple relative directory names into one.

Combine directory names in DIRS into one long directory name
using directory separator."
  (cl-reduce
   #'concat
   (seq-map #'file-name-as-directory dirs)
   :initial-value nil))


;;; Cabal support
(ert-deftest flycheck-haskell-read-cabal-configuration/has-all-extensions ()
  (let-alist (flycheck-haskell-read-test-config)
    (should-not (seq-difference .extensions '("OverloadedStrings"
                                              "YouDontKnowThisOne"
                                              "GeneralizedNewtypeDeriving")))))

(ert-deftest flycheck-haskell-read-cabal-configuration/has-all-languages ()
  (let-alist (flycheck-haskell-read-test-config)
    (should-not (seq-difference .languages '("Haskell98"
                                             "SpamLanguage"
                                             "Haskell2010")))))

(ert-deftest flycheck-haskell-read-cabal-configuration/source-dirs ()
  (let-alist (flycheck-haskell-read-test-config)
    (should-not (seq-difference
                 .source-directories
                 (seq-map (lambda (fn)
                            (file-name-as-directory
                             (expand-file-name fn flycheck-haskell-test-dir)))
                          '("lib/" "." "src/"))))))

(ert-deftest flycheck-haskell-read-cabal-configuration/build-dirs ()
  (let* ((builddirs '("build" "build/autogen"
                      "build/flycheck-haskell-unknown-stuff/flycheck-haskell-unknown-stuff-tmp"
                      "build/flycheck-haskell-test/flycheck-haskell-test-tmp")))
    (let-alist (flycheck-haskell-read-test-config)
      (dolist (dir builddirs)
        (let ((stack-re (format "\\.stack-work/.*/%s\\'" (regexp-quote dir)))
              (cabal-re (format "dist/%s\\'" (regexp-quote dir))))
          (should (seq-find (apply-partially #'string-match-p stack-re)
                            .build-directories))
          (should (seq-find (apply-partially #'string-match-p cabal-re)
                            .build-directories)))))))

(ert-deftest flycheck-haskell-read-cabal-configuration/cpp-options ()
  (let-alist (flycheck-haskell-read-test-config)
    (should (member "-DDEBUG=1" .other-options))))

(ert-deftest flycheck-haskell-read-cabal-configuration/ghc-options ()
  (let-alist (flycheck-haskell-read-test-config)
    (should (member "-Wall" .other-options))))

(ert-deftest flycheck-haskell-get-configuration/no-cache-entry ()
  (let* ((cabal-file flycheck-haskell-test-cabal-file))
    (cl-letf (((symbol-function 'flycheck-haskell-read-cabal-configuration)
               (lambda (_) 'dummy)))
      (flycheck-haskell-test-with-cache
        (should-not (flycheck-haskell-get-cached-configuration cabal-file))
        (should (eq (flycheck-haskell-get-configuration cabal-file) 'dummy))
        (should (eq (flycheck-haskell-get-cached-configuration cabal-file)
                    'dummy))))))

(ert-deftest flycheck-haskell-read-cabal-configuration/read-from-dir-that-has-prelude-module ()
  (let* ((test-dir (flycheck-haskell--concat-dirs flycheck-haskell-test-dir
                                                  "test-data"
                                                  "project-with-prelude-module"))
         (default-directory test-dir))
    (cl-assert (file-regular-p (expand-file-name "foo.cabal" test-dir)))
    (flycheck-haskell-read-cabal-configuration "foo.cabal")
    (let-alist (flycheck-haskell-read-cabal-configuration "foo.cabal")
      (should (equal .dependencies '("base")))
      (should (equal .extensions '("OverloadedStrings")))
      (should (equal .languages '("Haskell2010")))
      (should (equal .other-options nil))
      (should (equal .source-directories '("lib/"))))))


;;; Configuration caching
(ert-deftest flycheck-haskell-clear-config-cache ()
  (unwind-protect
      (progn
        (puthash "foo" "bar" flycheck-haskell-config-cache)
        (should (= (hash-table-count flycheck-haskell-config-cache) 1))
        (flycheck-haskell-clear-config-cache)
        (should (= (hash-table-count flycheck-haskell-config-cache) 0)))
    (clrhash flycheck-haskell-config-cache)))

(ert-deftest flycheck-haskell-get-cached-configuration/no-cache-entry ()
  (should-not (flycheck-haskell-get-cached-configuration
               flycheck-haskell-test-cabal-file)))

(ert-deftest flycheck-haskell-get-cached-configuration/cached-config ()
  (flycheck-haskell-test-with-cache
    (flycheck-haskell-read-and-cache-configuration
     flycheck-haskell-test-cabal-file)
    (should (= (hash-table-count flycheck-haskell-config-cache) 1))
    (let ((config (flycheck-haskell-get-cached-configuration
                   flycheck-haskell-test-cabal-file)))
      (should (equal config
                     (flycheck-haskell-read-cabal-configuration
                      flycheck-haskell-test-cabal-file))))))

(ert-deftest flycheck-haskell-get-cached-configuration/file-is-modified ()
  (flycheck-haskell-test-with-cache
    (flycheck-haskell-read-and-cache-configuration
     flycheck-haskell-test-cabal-file)
    (should (flycheck-haskell-get-cached-configuration
             flycheck-haskell-test-cabal-file))
    ;; Wait a second, to ensure that the current time advances
    (sleep-for 1)
    (set-file-times flycheck-haskell-test-cabal-file)
    (should-not (flycheck-haskell-get-cached-configuration
                 flycheck-haskell-test-cabal-file))
    (should (= (hash-table-count flycheck-haskell-config-cache) 0))))


(ert-deftest flycheck-haskell-get-configuration/has-cache-entry ()
  (let* ((cabal-file flycheck-haskell-test-cabal-file)
         (mtime (nth 6 (file-attributes cabal-file))))
    (cl-letf (((symbol-function 'flycheck-haskell-read-cabal-configuration)
               (lambda (_) 'dummy)))
      (flycheck-haskell-test-with-cache
        ;; Create a fake hash entry, which is guaranteed to be newer than the
        ;; actual file
        (puthash cabal-file (cons (time-add mtime (seconds-to-time 1))
                                  'cached-dummy)
                 flycheck-haskell-config-cache)
        (should (eq (flycheck-haskell-get-configuration cabal-file)
                    'cached-dummy))
        (flycheck-haskell-clear-config-cache)
        (should (eq (flycheck-haskell-get-configuration cabal-file)
                    'dummy))))))


;;; Cabal sandbox support
(ert-deftest flycheck-haskell-get-config-value/returns-value ()
  (with-temp-buffer
    (insert "spam: with eggs\n")
    (goto-char (point-min))
    (should (equal (flycheck-haskell-get-config-value 'spam)
                   '(spam . "with eggs")))))

(ert-deftest flycheck-haskell-get-config-value/no-text-properties ()
  (with-temp-buffer
    (insert "spam: with eggs\n")
    (goto-char (point-min))
    (add-text-properties 6 (line-end-position) '(face 'bold))
    (let ((value (cdr (flycheck-haskell-get-config-value 'spam))))
      (should-not (text-properties-at 0 value)))))

(ert-deftest flycheck-haskell-get-config-value/no-such-key ()
  (with-temp-buffer
    (insert "spam: with eggs\n")
    (goto-char (point-min))
    (should-not (flycheck-haskell-get-config-value 'foo))))

(ert-deftest flycheck-haskell-get-cabal-config ()
  (flycheck-haskell-test-with-fake-file
    (let ((config (flycheck-haskell-get-cabal-config)))
      (should (equal config '((with-compiler . "/foo/bar/ghc-7.10")))))))

(ert-deftest flycheck-haskell-get-sandbox-config ()
  (flycheck-haskell-test-with-fake-file
    (let ((config (flycheck-haskell-get-sandbox-config))
          (db "/foo/bar/.cabal-sandbox/foo-packages.conf.d"))
      (should (equal config `((package-db . ,db)))))))


;;; Buffer setup
(ert-deftest flycheck-haskell-process-configuration/language-extensions ()
  (with-temp-buffer                     ; To scope the variables
    (flycheck-haskell-process-configuration (flycheck-haskell-read-test-config))
    (should-not (seq-difference flycheck-ghc-language-extensions
                                '("OverloadedStrings"
                                  "YouDontKnowThisOne"
                                  "GeneralizedNewtypeDeriving"
                                  "Haskell98"
                                  "SpamLanguage"
                                  "Haskell2010")))
    (should (local-variable-p 'flycheck-ghc-language-extensions))))

(ert-deftest flycheck-haskell-process-configuration/search-path ()
  (let* ((config (flycheck-haskell-read-test-config))
         (sourcedirs (seq-map
                      (lambda (d)
                        (file-name-as-directory
                         (expand-file-name d flycheck-haskell-test-dir)))
                      '("lib/" "." "src/"))))
    (let-alist config
      (with-temp-buffer
        (flycheck-haskell-process-configuration config)
        (should (local-variable-p 'flycheck-ghc-search-path))
        (should (cl-subsetp sourcedirs flycheck-ghc-search-path :test #'equal))
        (should (cl-subsetp .build-directories flycheck-ghc-search-path
                            :test #'equal))))))

(ert-deftest flycheck-haskell-process-configuration/hides-all-packages ()
  (with-temp-buffer
    (flycheck-haskell-process-configuration (flycheck-haskell-read-test-config))
    (should (member "-hide-all-packages" flycheck-ghc-args))
    (should (local-variable-p 'flycheck-ghc-args))))

(ert-deftest flycheck-haskell-process-configuration/includes-dependenty-packages ()
  (with-temp-buffer
    (flycheck-haskell-process-configuration (flycheck-haskell-read-test-config))
    (should (member "-package=bytestring" flycheck-ghc-args))
    (should (member "-package=base" flycheck-ghc-args))
    (should (local-variable-p 'flycheck-ghc-args))))

(ert-deftest flycheck-haskell-configure/ghc-executable ()
  (flycheck-haskell-test-with-fake-file
    (flycheck-haskell-configure)
    (should (equal flycheck-haskell-ghc-executable "/foo/bar/ghc-7.10"))
    (should (local-variable-p 'flycheck-haskell-ghc-executable))))

(ert-deftest flycheck-haskell-configure/package-database ()
  (flycheck-haskell-test-with-fake-file
    (flycheck-haskell-configure)
    (should (equal flycheck-ghc-package-databases
                   '("/foo/bar/.cabal-sandbox/foo-packages.conf.d")))
    (should (local-variable-p 'flycheck-ghc-package-databases))
    (should (equal flycheck-ghc-no-user-package-database t))
    (should (local-variable-p 'flycheck-ghc-no-user-package-database))))

(provide 'flycheck-haskell-test)

;;; flycheck-haskell-test.el ends here
