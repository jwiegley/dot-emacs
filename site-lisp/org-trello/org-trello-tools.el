;;; org-trello-tools.el --- Load the namespaces of org-trello in a dev or test context

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

(defvar org-trello-home (or (getenv "ORGTRELLO_HOME") (expand-file-name "."))
  "Org-trello home.")

(defvar org-trello-tools--namespaces '() "Org-trello namespaces for development purposes.")
(setq org-trello-tools--namespaces '("org-trello-log.el"
                                     "org-trello-setup.el"
                                     "org-trello-action.el"
                                     "org-trello-api.el"
                                     "org-trello-backend.el"
                                     "org-trello-entity.el"
                                     "org-trello-cbx.el"
                                     "org-trello-date.el"
                                     "org-trello-buffer.el"
                                     "org-trello-controller.el"
                                     "org-trello-hash.el"
                                     "org-trello-data.el"
                                     "org-trello-input.el"
                                     "org-trello-proxy.el"
                                     "org-trello-query.el"
                                     "org-trello-utils.el"
                                     "org-trello-deferred.el"
                                     "org-trello.el"))

(defun org-trello-tools-load-namespaces ()
  "Load the org-trello namespaces."
  (interactive)
  (add-to-list 'load-path org-trello-home)
  ;; recompile code
  (mapc (lambda (it) (load-with-code-conversion (concat org-trello-home "/" it) it)) org-trello-tools--namespaces)
  (require 'org-trello)
  ;; reload bindings
  (require 'helm)
  (custom-set-variables
   '(org-trello-current-prefix-keybinding "C-c o")
   '(orgtrello-log-level orgtrello-log-info)
   '(org-trello-input-completion-mechanism 'helm))
  (orgtrello-log-msg orgtrello-log-info "Code loaded!"))

(defun org-trello-tools-remove-bindings ()
  "Remove bindings."
  (interactive)
  ;; Remove old bindings
  (mapc 'orgtrello-setup-remove-local-prefix-mode-keybinding '("C-c o"
                                                               "C-c a"
                                                               "C-c x"
                                                               "C-c z"))
  ;; install the default one
  (orgtrello-setup-install-local-prefix-mode-keybinding "C-c o"))

(defun org-trello-tools-find-unused-definitions ()
  "Find unused definitions."
  (interactive)
  (let ((filename "/tmp/org-trello-find-unused-definitions.el"))
    (with-temp-file filename
      (erase-buffer)
      (mapc (lambda (file)
              (insert-file-contents file)
              (goto-char (point-max))) org-trello-tools--namespaces)
      (emacs-lisp-mode)
      (write-file filename)
      (call-interactively 'emr-el-find-unused-definitions))))

(defconst orgtrello-tests-test-folder "./test"
  "Folder where tests files are defined.")

(defvar orgtrello-tools--tests-namespaces '() "Org-trello test namespaces for development purposes.")
(setq orgtrello-tools--tests-namespaces '("test/org-trello-tests-test.el"
                                          "test/org-trello-setup-test.el"
                                          "test/org-trello-action-test.el"
                                          "test/org-trello-api-test.el"
                                          "test/org-trello-backend-test.el"
                                          "test/org-trello-entity-test.el"
                                          "test/org-trello-entity-test.el"
                                          "test/org-trello-cbx-test.el"
                                          "test/org-trello-date-test.el"
                                          "test/org-trello-buffer-test.el"
                                          "test/org-trello-controller-test.el"
                                          "test/org-trello-data-test.el"
                                          "test/org-trello-hash-test.el"
                                          "test/org-trello-proxy-test.el"
                                          "test/org-trello-query-test.el"
                                          "test/org-trello-utils-test.el"))

(defun org-trello-tools-load-test-namespaces ()
  "Load the org-trello's test namespaces."
  (interactive)
  ;; Add test folder to the load path
  (add-to-list 'load-path (expand-file-name orgtrello-tests-test-folder))
  (mapc #'load-file orgtrello-tools--tests-namespaces)
  (require 'org-trello)
  (orgtrello-log-msg orgtrello-log-info "Tests loaded!"))

(defun org-trello-tools--execute-fn-on-buffer (fn buffer-file)
  "Execute the function FN on buffer-file.
FN is a parameter-less function that compute something from BUFFER-FILE.
The buffer-file is not modified and the position is not changed."
  (save-excursion
    (with-temp-buffer
      (insert-file buffer-file)
      (goto-char (point-min))
      (funcall fn))))

(defun org-trello-tools--number-of (regexp buffer-file)
  "Given a REGEXP, count all occurences on BUFFER-FILE."
  (org-trello-tools--execute-fn-on-buffer
   (lambda ()
     (let ((c 0))
       (while (re-search-forward regexp nil t)
         (setq c (1+ c)))
       c))
   buffer-file))

(defun org-trello-tools--ask-for-buffer-or-fallback-to-default (&optional ask-buffer)
  "Compute the desired buffer.
If region is active, use the region.
Otherwise, if ASK-BUFFER is set, ask for input.
Otherwise, fallback to the current buffer name."
  (if (region-active-p)
      (buffer-substring (region-beginning) (region-end))
    (if ask-buffer
        (read-string "Buffer name: ")
      (buffer-name (current-buffer)))))

(defun org-trello-tools--interactive-number-of (regexp &optional ask-buffer)
  "Given a REGEXP, compute a number of occurrences.
If region is active, will use the region highlight as buffer.
Otherwise, if ASK-BUFFER is not nil, will ask the user.
Otherwise, default to current buffer."
  (let ((buf (org-trello-tools--ask-for-buffer-or-fallback-to-default ask-buffer)))
    (-when-let (c (org-trello-tools--number-of regexp buf))
      (insert (int-to-string c)))))

(defun org-trello-tools-functions-in-buffer (buffer-file)
  "Compute `def-un', `def-macro', `def-subst', `def-alias' nb in BUFFER-FILE.
Order is the same as the buffer's definitions."
  (org-trello-tools--execute-fn-on-buffer
   (lambda ()
     (let ((functions))
       (while (re-search-forward "\\(defalias '\\|defmacro \\|defsubst \\|defun \\)\\([a-zA-z0-9-]*\\)" nil t)
         (push (match-string-no-properties 2) functions))
       (nreverse functions)))
   buffer-file))

(require 'f)

(defun org-trello-tools-ns-file-from-current-buffer (ns-filename)
  "Compute the test namespace file from NS-FILENAME."
  (let ((buff (concat (f-no-ext ns-filename) "-test")))
    (->> (directory-files orgtrello-tests-test-folder)
         (-filter (-partial 'string-match-p buff))
         car
         (list orgtrello-tests-test-folder)
         (s-join "/"))))

(require 'helm)
(require 'thingatpt)

(defun org-trello-tools-function-at-pt-covered-p ()
  "Determine if function in region or at point is tested.
The function's name is either in active region or the thing at point."
  (interactive)
  (let* ((actual-buffer-file (buffer-name (current-buffer)))
         (buffer-test-file (org-trello-tools-ns-file-from-current-buffer
                            actual-buffer-file))
         (fn-name (if (region-active-p)
                      (buffer-substring-no-properties (region-beginning)
                                                      (region-end))
                    (thing-at-point 'sexp))))
    (message
     (if (< 0 (org-trello-tools--number-of (format "\(ert-deftest test-%s" fn-name)
                                           buffer-test-file))
         (message "Tested!")
       (message "'%s' is not covered in %s!"
                fn-name
                buffer-test-file)))))

(defun org-trello-tools-function-coverage ()
  "Determine the functions not covered in the current namespace."
  (let* ((actual-buffer-file (buffer-name (current-buffer)))
         (buffer-test (org-trello-tools-ns-file-from-current-buffer actual-buffer-file))
         (fn-names (org-trello-tools-functions-in-buffer actual-buffer-file)))
    (->> fn-names
         (--map (list it (< 0 (org-trello-tools--number-of (format "\(ert-deftest test-%s" it) buffer-test))))
         (-filter (-compose 'not 'cadr))
         (-map 'car)))) ;; FIXME: -reduce...

(defun org-trello-tools-next-uncovered-function ()
  "Ask for the next uncovered function in current buffer."
  (interactive)
  (-if-let (uncovered-functions (org-trello-tools-function-coverage))
      (let ((fn-name (helm-comp-read "Next uncovered function: " uncovered-functions)))
        (-if-let (pos (save-excursion
                        (goto-char (point-min))
                        (search-forward-regexp (format "\\(defalias '\\|defun \\|defmacro \\|defsubst \\)%s" fn-name))))
            (goto-char pos)
          (message "Curiously enough, I did not find '%s'... Sorry about that."
                   fn-name)))
    (message "Congrats! Namespace seems fully covered!")))

(defun org-trello-tools-count-functions (&optional ask-buffer)
  "Count the number of `def-un' or `def-alias' or `def-macro' or `def-subst'.
If region is active, will use the region highlight as buffer.
Otherwise, if ASK-BUFFER is not nil, will ask the user.
Otherwise, default to current buffer."
  (interactive "P")
  (org-trello-tools--interactive-number-of
   "\\(\(defun\\|\(defsubst\\|\(defmacro\\|\(defalias\\).*"
   ask-buffer))

(defun org-trello-tools-count-number-tests (&optional ask-buffer)
  "Count the number of `ert-def-test'.
If region is active, will use the region highlight as buffer.
Otherwise, if ASK-BUFFER is not nil, will ask the user.
Otherwise, default to current buffer."
  (interactive "P")
  (org-trello-tools--interactive-number-of "\\(ert-deftest\\).*" ask-buffer))

(defun org-trello-tools-find-next-error ()
  "Find the next test error in overseer buffer."
  (interactive)
  (with-current-buffer "*overseer*"
    (goto-char (point-min))
    (if (search-forward "(ert-test-failed" nil 'noerror)
        (progn
          (switch-to-buffer "*overseer*" nil 'same-window)
          (search-forward "(ert-test-failed" nil 'noerror)
          (forward-line 10))
      (message "All is good!"))))

(fset 'org-trello-tools-org-raw-coverage
      (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([tab tab tab 201326624 201326624 backspace tab S-iso-lefttab S-iso-lefttab S-iso-lefttab 201326624 201326624 backspace tab S-iso-lefttab S-iso-lefttab 201326624 201326624 201326624 134217848 111 114 103 116 114 101 108 108 111 45 116 101 115 116 115 45 99 111 117 110 116 45 102 117 110 99 116 105 111 110 115 13 134217736 tab 25 46 48 9 201326624 201326624 201326624 134217848 111 114 103 116 114 101 108 108 111 45 116 101 115 116 115 45 99 111 117 110 116 45 110 117 109 98 101 114 45 116 101 115 116 115 13 134217736 9 25 46 48 9 3 42 21 3 42 9] 0 "%d")) arg)))

(add-hook 'emacs-lisp-mode-hook (lambda ()
                                  (define-key emacs-lisp-mode-map (kbd "C-c o d") 'org-trello-tools-load-namespaces)
                                  (define-key emacs-lisp-mode-map (kbd "C-c o D") 'org-trello-tools-find-next-error)
                                  (define-key emacs-lisp-mode-map (kbd "C-c o r") 'org-trello-tools-load-namespaces)
                                  (define-key emacs-lisp-mode-map (kbd "C-c o t") 'org-trello-tools-load-test-namespaces)
                                  (define-key emacs-lisp-mode-map (kbd "C-c o f") 'org-trello-tools-find-unused-definitions)
                                  (define-key emacs-lisp-mode-map (kbd "C-c o o") 'org-trello-tools-org-raw-coverage)))

(add-hook 'org-trello-mode-hook (lambda ()
                                  (define-key org-trello-mode-map (kbd "C-c o d") 'org-trello-tools-load-namespaces)
                                  (define-key org-trello-mode-map (kbd "C-c o D") 'org-trello-tools-find-next-error)
                                  (define-key org-trello-mode-map (kbd "C-c o r") 'org-trello-tools-load-namespaces)
                                  (define-key org-trello-mode-map (kbd "C-c o t") 'org-trello-tools-load-test-namespaces)
                                  (define-key org-trello-mode-map (kbd "C-c o f") 'org-trello-tools-find-unused-definitions)
                                  (define-key org-trello-mode-map (kbd "C-c o o") 'org-trello-tools-org-raw-coverage)))

(provide 'org-trello-tools)
;;; org-trello-tools.el ends here
