#!/usr/bin/env emacs --script

;; A fallback test runner for platforms where 'ert-runner' is broken

(let* ((current-dir (file-name-directory load-file-name))
       (git-gutter+-test-dir current-dir)
       (git-gutter+-root-dir (expand-file-name ".." current-dir)))

  (add-to-list 'load-path git-gutter+-root-dir)
  (load-file (concat git-gutter+-test-dir "git-gutter+-test.el")))

(ert-run-tests-batch-and-exit t)
