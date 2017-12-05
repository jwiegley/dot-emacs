;;; package-lint-test.el --- package-lint test suite

;; Copyright (C) 2016-2017  Steve Purcell, Fanael Linithien

;; Author: Steve Purcell <steve@sanityinc.com>
;;         Fanael Linithien <fanael4@gmail.com>
;; URL: https://github.com/purcell/package-lint
;; Version: 0

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

;; This file contains the official package-lint testsuite.

;;; Code:
(require 'package-lint)
(require 'ert)

(defun package-lint-test--run (contents &optional header version footer provide commentary url)
  "Run `package-lint-buffer' on a temporary buffer with given CONTENTS.

HEADER, VERSION, FOOTER, PROVIDE, COMMENTARY, and URL can be
either strings or nil; when one is a string, the corresponding
package boilerplate part is replaced with the passed string, when
it's nil, the default is used."
  (with-temp-buffer
    (emacs-lisp-mode)
    (insert (or header ";;; test.el --- A test\n"))
    (insert (or version ";; Package-Version: 0\n"))
    (insert (or url ";; URL: https://package-lint.test/p?q#f\n"))
    (insert (or commentary ";;; Commentary:\n;; A test package, for testing.\n"))
    (insert contents)
    (insert "\n" (or provide "(provide 'test)\n"))
    (insert (or footer "\n\n;;; test.el ends here\n"))
    (let ((buffer-file-name "test.el"))
      (package-lint-buffer))))

(ert-deftest package-lint-test-reserved-keybindings ()
  (let ((reserved-message "This key sequence is reserved (see Key Binding Conventions in the Emacs Lisp manual)"))
    ;; C-c and a letter (either upper or lower case)
    (should (equal (package-lint-test--run "(kbd \"C-c n\")")
                   `((6 13 warning ,reserved-message))))
    (should (equal (package-lint-test--run "(local-set-key \"\\C-cF\" 'something)")
                   `((6 34 warning ,reserved-message))))
    (should-not (package-lint-test--run "(kbd \"C-d n\")"))
    (should (equal (package-lint-test--run "(kbd \"C-c x n\")")
                   `((6 15 warning ,reserved-message))))

    ;; [C-keyname] bindings should work fine
    (should-not (package-lint-test--run "(define-key map [C-return] 'something)"))

    ;; C-c followed by a control character or a digit
    (should-not (package-lint-test--run "(defcustom test-something (kbd \"C-c 1\"))"))
    (should-not (package-lint-test--run "(global-set-key \"\\C-c1\" 'something)"))

    ;; C-c followed by {, }, <, >, : or ;
    (should-not (package-lint-test--run "(defcustom test-something (kbd \"C-c <\"))"))
    (should-not (package-lint-test--run "(define-key map \"\\C-c<\" 'something)"))

    ;; Function keys <F5> through <F9> without modifier keys
    (should (equal (package-lint-test--run "(define-key map (kbd \"<f5>\") 'something)")
                   `((6 40 warning ,reserved-message))))
    (should (equal (package-lint-test--run "(global-set-key [f5] 'something)")
                   `((6 32 warning ,reserved-message))))
    (should-not (package-lint-test--run "(global-set-key [f4] 'something)"))
    (should-not (package-lint-test--run "(global-set-key (kbd \"C-c <tab>\") 'something)"))

    ;; C-c followed by any other ASCII punctuation or symbol character
    (should-not (package-lint-test--run "(defcustom test-something (kbd \"C-c .\"))"))
    (should-not (package-lint-test--run "(global-set-key \"\\C-c.\" 'something)"))

    ;; But C-c followed by another modifier sequence is allowed
    (should-not (package-lint-test--run "(global-set-key (kbd \"C-c C-x d\") 'something)"))

    ;; Don't bind C-h following any prefix character
    (should (equal (package-lint-test--run "(defcustom test-something (kbd \"C-x C-h\"))")
                   `((6 41 warning ,reserved-message))))
    (should-not (package-lint-test--run "(defcustom test-something (kbd \"C-h C-x\"))"))

    ;; Don't bind a key sequence ending in <C-g>
    (should (equal (package-lint-test--run "(defcustom test-something (kbd \"C-x C-g\"))")
                   `((6 41 warning ,reserved-message))))
    (should (equal (package-lint-test--run "(global-set-key \"\\C-c\\C-g\" 'something)")
                   `((6 38 warning ,reserved-message))))
    (should-not (package-lint-test--run "(global-set-key \"C-x g\" 'something)"))
    ;; But we allow C-g alone, which is acceptable for some special cases
    (should-not (package-lint-test--run "(defcustom test-something (kbd \"C-g\"))"))

    ;; Don't bind a key sequence ending in <ESC> except following another <ESC>
    (should (equal (package-lint-test--run "(defcustom test-something (kbd \"C-x <ESC>\")")
                   `((6 43 warning ,reserved-message))))
    (should-not (package-lint-test--run "(defcustom test-something (kbd \"C-x <ESC> <ESC>\"))"))))

(ert-deftest package-lint-test-error-autoloads-on-private-functions ()
  (should (equal '() (package-lint-test--run "(defun test--private-function ())")))
  (should
   (equal
    '((6 0 warning "Private functions generally should not be autoloaded."))
    (package-lint-test--run ";;;###autoload\n(defun test--private-function ())")))
  (should
   (equal
    '((6 0 warning "Private functions generally should not be autoloaded."))
    (package-lint-test--run ";;;###autoload\n(defmacro test--private-macro ())"))))

(ert-deftest package-lint-test-warn-literal-emacs-path ()
  (should
   (equal
    '((6 9 warning "Use variable `user-emacs-directory' or function `locate-user-emacs-file' instead of a literal path to the Emacs user directory or files."))
    (package-lint-test--run "\".emacs\.d\"")))
  (should
   (equal
    '((6 11 warning "Use variable `user-emacs-directory' or function `locate-user-emacs-file' instead of a literal path to the Emacs user directory or files."))
    (package-lint-test--run "\"~/.emacs\.d/foo\"")))
  (should (equal '() (package-lint-test--run "\"/foo/foo.emacs.dat\"")))
  (should (equal '() (package-lint-test--run ";; ~/\.emacs\.d/elpa")))
  (should (equal '() (package-lint-test--run "\"emacs dot dee\""))))

(ert-deftest package-lint-test-accept-standard-keywords ()
  ;; Test comma- and space-separated keywords, as both are commonly used.
  (should (equal '() (package-lint-test--run ";; Keywords: lisp convenience")))
  (should (equal '() (package-lint-test--run ";; Keywords: lisp, convenience"))))

(ert-deftest package-lint-test-warn-no-standard-keyword ()
  (should
   (equal
    '((6 1 warning "You should include standard keywords: see the variable `finder-known-keywords'."))
    (package-lint-test--run ";; Keywords: foo"))))

(ert-deftest package-lint-test-no-warning-if-at-least-one-standard-keyword ()
  (should
   (equal nil (package-lint-test--run ";; Keywords: lisp foo"))))

(ert-deftest package-lint-test-error-if-no-url ()
  (should
   (equal
    '((1 1 error "Package should have a Homepage or URL header."))
    (package-lint-test--run "" nil nil nil nil nil "")))
  (should
   (equal
    '((3 9 error "Package URLs should be a single HTTPS or HTTP URL."))
    (package-lint-test--run "" nil nil nil nil nil ";; URL: not a URL\n")))
  (should
   (equal
    '((3 9 error "Package URLs should be a single HTTPS or HTTP URL."))
    (package-lint-test--run "" nil nil nil nil nil
                            ";; URL: git://test/test.git\n"))))

(ert-deftest package-lint-test-accept-homepage ()
  (should (equal '() (package-lint-test--run "" nil nil nil nil nil
                                             ";; Homepage: https://package-lint.test/foo\n"))))

(ert-deftest package-lint-test-warn-invalid-version ()
  (should
   (member
    '(2 21 warning "\"invalid\" is not a valid version. MELPA will handle this, but other archives will not.")
    (package-lint-test--run "" nil ";; Package-Version: invalid\n"))))

(ert-deftest package-lint-test-warn-no-version ()
  (should
   (member
    '(1 1 warning "\"Version:\" or \"Package-Version:\" header is missing. MELPA will handle this, but other archives will not.")
    (package-lint-test--run ";; Package-Requires: ((example \"0\"))" nil ""))))

(ert-deftest package-lint-test-accept-valid-version ()
  (should (equal '() (package-lint-test--run "" nil ";; Package-Version: 1.2.3-cvs\n"))))

(ert-deftest package-lint-test-error-lexical-binding-not-at-end ()
  (should
   (equal
    '((1 1 error "`lexical-binding' must be set in the first line."))
    (package-lint-test--run
     ";; Local Variables:
;; lexical-binding: t
;; End:"))))

(ert-deftest package-lint-test-warn-lexical-binding-without-emacs-24-dep ()
  (should
   (equal
    '((1 28 warning "You should depend on (emacs \"24\") if you need lexical-binding."))
    (package-lint-test--run
     ""
     ";;; test.el --- A test -*- lexical-binding: t -*-\n"))))

(ert-deftest package-lint-test-accept-lexical-binding-with-emacs-24-dep ()
  (should
   (equal
    '()
    (package-lint-test--run
     ";; Package-Requires: ((emacs \"24\"))"
     ";;; test.el --- A test -*- lexical-binding: t -*-\n"))))

(ert-deftest package-lint-test-warn-empty-summary ()
  (should
   (equal
    '((1 1 warning "Package should have a non-empty summary."))
    (package-lint-test--run "" ";;; test.el ---\n"))))

(ert-deftest package-lint-test-warn-too-long-summary ()
  (should
   (equal
    '((1 1 warning "The package summary is too long. It should be at most 50 characters."))
    (package-lint-test--run
     ""
     ";;; test.el --- xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n"))))

(ert-deftest package-lint-test-warn-emacs-in-summary ()
  (should
   (equal
    '((1 1 warning "Including \"Emacs\" in the package description is usually redundant."))
    (package-lint-test--run "" ";;; test.el --- A package for Emacs\n"))))

(ert-deftest package-lint-test-accept-emacs-lisp-in-summary ()
  (should (equal '() (package-lint-test--run "" ";;; test.el --- Emacs Lisp test framework\n"))))

(ert-deftest package-lint-test-accept-.emacs-in-summary ()
  (should (equal '() (package-lint-test--run "" ";;; test.el --- Something for .emacs\n"))))

(ert-deftest package-lint-test-error-invalid-dependency ()
  (should
   (member
    '(6 1 error "Expected (package-name \"version-num\"), but found invalid.")
    (package-lint-test--run ";; Package-Requires: (invalid)")))
  (should
   (member
    '(6 24 error "\"invalid\" is not a valid version string: see `version-to-list'.")
    (package-lint-test--run ";; Package-Requires: ((package-lint \"invalid\"))"))))

(ert-deftest package-lint-test-error-emacs-23-dep ()
  (should
   (equal
    '((6 24 error "You can only depend on Emacs version 24 or greater: package.el for Emacs 23 does not support the \"emacs\" pseudopackage."))
    (package-lint-test--run ";; Package-Requires: ((emacs \"23\"))"))))

(ert-deftest package-lint-test-accept-emacs-24+-dep ()
  (should (equal '() (package-lint-test--run ";; Package-Requires: ((emacs \"24\"))")))
  (should (equal '() (package-lint-test--run ";; Package-Requires: ((emacs \"26.7\"))"))))

(ert-deftest package-lint-test-error-uninstallable-dep ()
  (should
   (equal
    '((6 24 error "Package example-nonexistent-package is not installable."))
    (package-lint-test--run ";; Package-Requires: ((example-nonexistent-package \"1\"))"))))

(ert-deftest package-lint-test-warn-snapshot-dep ()
  (should
   (equal
    '((6 24 warning "Use a non-snapshot version number for dependency on \"package-lint\" if possible."))
    (package-lint-test--run ";; Package-Requires: ((package-lint \"20160101.1234\"))"))))

(ert-deftest package-lint-test-warn-unversioned-dep ()
  (should
   (equal
    '((6 24 warning "Use a properly versioned dependency on \"package-lint\" if possible."))
    (package-lint-test--run ";; Package-Requires: ((package-lint \"0\"))"))))

(ert-deftest package-lint-test-error-cl-lib-1.0-dep ()
  (should
   (member
    '(6 24 error "Depend on the latest 0.x version of cl-lib rather than on version \"(1)\".
Alternatively, depend on (emacs \"24.3\") or greater, in which cl-lib is bundled.")
    (package-lint-test--run ";; Package-Requires: ((cl-lib \"1\"))"))))

(ert-deftest package-lint-test-accept-normal-deps ()
  (should (equal '() (package-lint-test--run
                      ";; Package-Requires: ((package-lint \"0.2\") (cl-lib \"0.5\"))"))))

(ert-deftest package-lint-test-error-new-functions ()
  (should
   (equal
    '((6 1 error "You should depend on (emacs \"25\") if you need `when-let'."))
    (package-lint-test--run
     "(when-let ((foo (bar))) (message \"ok\"))"))))

(ert-deftest package-lint-test-accept-new-functions-with-dep ()
  (should
   (equal
    '()
    (package-lint-test--run
     ";; Package-Requires: ((emacs \"25\"))
\(when-let ((foo (bar))) (message \"ok\"))"))))

(ert-deftest package-lint-test-accept-new-functions-with-fboundp ()
  (should
   (equal
    '()
    (package-lint-test--run
     "(if (fboundp 'when-let)
    (when-let blah)
  (bloop))"))))

(ert-deftest package-lint-test-error-nonstandard-symbol-separator ()
  (should
   (equal
    '((6 1 error "`test-thing/bar' contains a non-standard separator `/', use hyphens instead (see Elisp Coding Conventions).")
      (7 1 error "`test-thing:bar' contains a non-standard separator `:', use hyphens instead (see Elisp Coding Conventions)."))
    (package-lint-test--run
     "(defun test-thing/bar () t)\n(defun test-thing:bar () nil)")))
  ;; But accept /= when at the end.
  (should (equal '() (package-lint-test--run "(defun test-/= (a b) t)"))))

(ert-deftest package-lint-test-error-unprefixed-definitions ()
  (should
   (equal
    '((6 1 error "\"foo\" doesn't start with package's prefix \"test\"."))
    (package-lint-test--run "(defun foo ())")))
  (should
   (equal
    '((6 1 error "\"global-testfoo-mode\" doesn't start with package's prefix \"test\"."))
    (package-lint-test--run "(define-globalized-minor-mode global-testfoo-mode ignore ignore :require 'test)"))))

(ert-deftest package-lint-test-accept-prefixed-definitions ()
  (should (equal '() (package-lint-test--run
                      "(defun test-foo ())\n(defun test ())")))
  (should (equal '() (package-lint-test--run
                      "(define-globalized-minor-mode global-test-mode ignore ignore :require 'test)")))
  (should (equal '() (package-lint-test--run
                      "(define-globalized-minor-mode global-test-foo-mode ignore ignore :require 'test)"))))

(ert-deftest package-lint-test-accept-sane-prefixed-definitions ()
  (should (equal '() (package-lint-test--run
                      "(defun org-dblock-write:test ())"))))

(ert-deftest package-lint-test-error-new-libraries ()
  (should
   (equal
    '((6 10 error "You should depend on (emacs \"24.4\") if you need `nadvice'."))
    (package-lint-test--run "(require 'nadvice)"))))

(ert-deftest package-lint-test-accept-new-libraries-with-dep ()
  (should (equal '() (package-lint-test--run
                      ";; Package-Requires: ((emacs \"24.4\"))\n(require 'nadvice)"))))

(ert-deftest package-lint-test-accept-new-libraries-with-optional-require ()
  (should (equal '() (package-lint-test--run "(require 'nadvice nil t)"))))

(ert-deftest package-lint-test-looks-like-a-package-p-works ()
  (should
   (with-temp-buffer
     (insert ";; Package-Version: 0\n")
     (package-lint-looks-like-a-package-p)))
  (should
   (with-temp-buffer
     (insert ";; Package-Requires: ((foo \"1\"))\n")
     (package-lint-looks-like-a-package-p)))
  (should
   (with-temp-buffer
     (insert ";; Version: 0\n")
     (package-lint-looks-like-a-package-p)))
  (should-not (with-temp-buffer (package-lint-looks-like-a-package-p)))
  (should-not
   (with-temp-buffer
     (insert ";; Dummy-Header: dummy-value\n")
     (package-lint-looks-like-a-package-p))))

(ert-deftest package-lint-test-error-unmatched-first-and-last-lines ()
  (should
   (member
    '(1 1 error "package.el cannot parse this buffer: Search failed: \";;; test.el ends here\"")
    (package-lint-test--run "" nil nil "\n\n;;; Test.el ends here\n"))))

(ert-deftest package-lint-test-error-missing-provide-form ()
  (should
   (equal
    '((1 1 error "There is no (provide 'test) form."))
    (package-lint-test--run "" nil nil nil ""))))

(ert-deftest package-lint-test-error-mismatched-provide-form ()
  (should
   (equal
    '((1 1 error "There is no (provide 'test) form."))
    (package-lint-test--run "" nil nil nil "(provide 'blargh)"))))

(ert-deftest package-lint-test-error-no-commentary ()
  (should
   (equal
    '((1 1 error "Package should have a ;;; Commentary section."))
    (package-lint-test--run "" nil nil nil nil "\n"))))

(ert-deftest package-lint-test-error-empty-commentary ()
  (should
   (equal
    '((4 0 error "Package should have a non-empty ;;; Commentary section."))
    (package-lint-test--run "" nil nil nil nil ";;; Commentary:\n ;;   \n \n\n;;; Code:\n"))))

(ert-deftest package-lint-test-accept-unprefixed-defadvice ()
  (should (equal '() (package-lint-test--run "(defadvice foo (before ignore))")))
  ;; Test if the special case we use for `defadvice' doesn't get
  ;; confused by weird spacing.
  (should (equal '() (package-lint-test--run "   (  defadvice \t\n\n foo (before ignore))"))))

(ert-deftest package-lint-test-minor-mode-global-t ()
  (should
   (equal
    '((6 0 error "Global minor modes must `:require' their defining file (i.e. \":require 'test\"), to support the customization variable of the same name."))
    (package-lint-test--run "(define-minor-mode test-mode \"\" :global t)"))))

(ert-deftest package-lint-test-globalized-minor-mode ()
  ;; Check for missing :require.
  (should
   (equal
    '((6 0 error "Global minor modes must `:require' their defining file (i.e. \":require 'test\"), to support the customization variable of the same name."))
    (package-lint-test--run "(define-globalized-minor-mode test-mode ignore ignore)")))
  ;; Check for incorrect :require.
  (should
   (equal
    '((6 0 error "Global minor modes must `:require' their defining file (i.e. \":require 'test\"), to support the customization variable of the same name."))
    (package-lint-test--run "(define-globalized-minor-mode test-mode ignore ignore :require 'blargh)"))))

(ert-deftest package-lint-test-error-defgroup-name ()
  (should
   (equal
    '((6 0 error "Customization groups should not end in \"-mode\" unless that name would conflict with their parent group."))
    (package-lint-test--run "(defgroup test-mode nil \"\" :group 'programming)")))
  (should
   (equal
    '((6 0 error "Customization groups should not end in \"-mode\" unless that name would conflict with their parent group."))
    (package-lint-test--run "(defgroup test-mode nil \"\" :group 'testing)")))
  (should
   (equal
    '()
    (package-lint-test--run "(defgroup test-mode nil \"\" :group 'test)"))))

(ert-deftest package-lint-test-error-defgroup-no-parent ()
  (should
   (equal
    '((6 0 error "Customization groups should specify a parent via `:group'."))
    (package-lint-test--run "(defgroup test nil \"\")"))))

(provide 'package-lint-test)
;;; package-lint-test.el ends here
