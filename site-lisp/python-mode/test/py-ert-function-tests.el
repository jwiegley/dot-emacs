;;; py-ert-function-tests.el --- functionp ert tests  -*- lexical-binding: t; -*-

;; Copyright (C) 2015  Andreas Röhler

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

;;

;;; Code:

(ert-deftest py-ert-virtualenv-filter-functionp-test ()
  (should (functionp 'virtualenv-filter)))

(ert-deftest py-ert-virtualenv-append-path-functionp-test ()
  (should (functionp 'virtualenv-append-path)))

(ert-deftest py-ert-virtualenv-add-to-path-functionp-test ()
  (should (functionp 'virtualenv-add-to-path)))

(ert-deftest py-ert-virtualenv-current-functionp-test ()
  (should (functionp 'virtualenv-current)))

(ert-deftest py-ert-virtualenv-deactivate-functionp-test ()
  (should (functionp 'virtualenv-deactivate)))

(ert-deftest py-ert-virtualenv-activate-functionp-test ()
  (should (functionp 'virtualenv-activate)))

(ert-deftest py-ert-virtualenv-p-functionp-test ()
  (should (functionp 'virtualenv-p)))

(ert-deftest py-ert-virtualenv-workon-complete-functionp-test ()
  (should (functionp 'virtualenv-workon-complete)))

(ert-deftest py-ert-virtualenv-workon-functionp-test ()
  (should (functionp 'virtualenv-workon)))

(ert-deftest py-ert--beginning-of-block-p-functionp-test ()
  (should (functionp 'py--beginning-of-block-p)))

(ert-deftest py-ert--beginning-of-clause-p-functionp-test ()
  (should (functionp 'py--beginning-of-clause-p)))

(ert-deftest py-ert--beginning-of-block-or-clause-p-functionp-test ()
  (should (functionp 'py--beginning-of-block-or-clause-p)))

(ert-deftest py-ert--beginning-of-def-p-functionp-test ()
  (should (functionp 'py--beginning-of-def-p)))

(ert-deftest py-ert--beginning-of-class-p-functionp-test ()
  (should (functionp 'py--beginning-of-class-p)))

(ert-deftest py-ert--beginning-of-def-or-class-p-functionp-test ()
  (should (functionp 'py--beginning-of-def-or-class-p)))

(ert-deftest py-ert--beginning-of-if-block-p-functionp-test ()
  (should (functionp 'py--beginning-of-if-block-p)))

(ert-deftest py-ert--beginning-of-try-block-p-functionp-test ()
  (should (functionp 'py--beginning-of-try-block-p)))

(ert-deftest py-ert--beginning-of-minor-block-p-functionp-test ()
  (should (functionp 'py--beginning-of-minor-block-p)))

(ert-deftest py-ert--beginning-of-for-block-p-functionp-test ()
  (should (functionp 'py--beginning-of-for-block-p)))

(ert-deftest py-ert--beginning-of-top-level-p-functionp-test ()
  (should (functionp 'py--beginning-of-top-level-p)))

(ert-deftest py-ert--beginning-of-statement-p-functionp-test ()
  (should (functionp 'py--beginning-of-statement-p)))

(ert-deftest py-ert--beginning-of-expression-p-functionp-test ()
  (should (functionp 'py--beginning-of-expression-p)))

(ert-deftest py-ert--beginning-of-partial-expression-p-functionp-test ()
  (should (functionp 'py--beginning-of-partial-expression-p)))

(ert-deftest py-ert--beginning-of-block-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-block-bol-p)))

(ert-deftest py-ert--beginning-of-clause-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-clause-bol-p)))

(ert-deftest py-ert--beginning-of-block-or-clause-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-block-or-clause-bol-p)))

(ert-deftest py-ert--beginning-of-def-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-def-bol-p)))

(ert-deftest py-ert--beginning-of-class-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-class-bol-p)))

(ert-deftest py-ert--beginning-of-def-or-class-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-def-or-class-bol-p)))

(ert-deftest py-ert--beginning-of-if-block-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-if-block-bol-p)))

(ert-deftest py-ert--beginning-of-try-block-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-try-block-bol-p)))

(ert-deftest py-ert--beginning-of-minor-block-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-minor-block-bol-p)))

(ert-deftest py-ert--beginning-of-for-block-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-for-block-bol-p)))

(ert-deftest py-ert--beginning-of-statement-bol-p-functionp-test ()
  (should (functionp 'py--beginning-of-statement-bol-p)))

(ert-deftest py-ert-up-statement-functionp-test ()
  (should (functionp 'py-up-statement)))

(ert-deftest py-ert-down-statement-functionp-test ()
  (should (functionp 'py-down-statement)))

(ert-deftest py-ert-up-base-functionp-test ()
  (should (functionp 'py-up-base)))

(ert-deftest py-ert-down-base-functionp-test ()
  (should (functionp 'py-down-base)))

(ert-deftest py-ert-up-block-functionp-test ()
  (should (functionp 'py-up-block)))

(ert-deftest py-ert-up-minor-block-functionp-test ()
  (should (functionp 'py-up-minor-block)))

(ert-deftest py-ert-up-def-functionp-test ()
  (should (functionp 'py-up-def)))

(ert-deftest py-ert-up-class-functionp-test ()
  (should (functionp 'py-up-class)))

(ert-deftest py-ert-up-def-or-class-functionp-test ()
  (should (functionp 'py-up-def-or-class)))

(ert-deftest py-ert-down-block-functionp-test ()
  (should (functionp 'py-down-block)))

(ert-deftest py-ert-down-minor-block-functionp-test ()
  (should (functionp 'py-down-minor-block)))

(ert-deftest py-ert-down-def-functionp-test ()
  (should (functionp 'py-down-def)))

(ert-deftest py-ert-down-class-functionp-test ()
  (should (functionp 'py-down-class)))

(ert-deftest py-ert-down-def-or-class-functionp-test ()
  (should (functionp 'py-down-def-or-class)))

(ert-deftest py-ert-up-block-bol-functionp-test ()
  (should (functionp 'py-up-block-bol)))

(ert-deftest py-ert-up-minor-block-bol-functionp-test ()
  (should (functionp 'py-up-minor-block-bol)))

(ert-deftest py-ert-up-def-bol-functionp-test ()
  (should (functionp 'py-up-def-bol)))

(ert-deftest py-ert-up-class-bol-functionp-test ()
  (should (functionp 'py-up-class-bol)))

(ert-deftest py-ert-up-def-or-class-bol-functionp-test ()
  (should (functionp 'py-up-def-or-class-bol)))

(ert-deftest py-ert-down-block-bol-functionp-test ()
  (should (functionp 'py-down-block-bol)))

(ert-deftest py-ert-down-minor-block-bol-functionp-test ()
  (should (functionp 'py-down-minor-block-bol)))

(ert-deftest py-ert-down-def-bol-functionp-test ()
  (should (functionp 'py-down-def-bol)))

(ert-deftest py-ert-down-class-bol-functionp-test ()
  (should (functionp 'py-down-class-bol)))

(ert-deftest py-ert-down-def-or-class-bol-functionp-test ()
  (should (functionp 'py-down-def-or-class-bol)))

(ert-deftest py-ert--end-of-statement-position-functionp-test ()
  (should (functionp 'py--end-of-statement-position)))

(ert-deftest py-ert--end-of-block-position-functionp-test ()
  (should (functionp 'py--end-of-block-position)))

(ert-deftest py-ert--end-of-clause-position-functionp-test ()
  (should (functionp 'py--end-of-clause-position)))

(ert-deftest py-ert--end-of-block-or-clause-position-functionp-test ()
  (should (functionp 'py--end-of-block-or-clause-position)))

(ert-deftest py-ert--end-of-def-position-functionp-test ()
  (should (functionp 'py--end-of-def-position)))

(ert-deftest py-ert--end-of-class-position-functionp-test ()
  (should (functionp 'py--end-of-class-position)))

(ert-deftest py-ert--end-of-def-or-class-position-functionp-test ()
  (should (functionp 'py--end-of-def-or-class-position)))

(ert-deftest py-ert--end-of-buffer-position-functionp-test ()
  (should (functionp 'py--end-of-buffer-position)))

(ert-deftest py-ert--end-of-expression-position-functionp-test ()
  (should (functionp 'py--end-of-expression-position)))

(ert-deftest py-ert--end-of-partial-expression-position-functionp-test ()
  (should (functionp 'py--end-of-partial-expression-position)))

(ert-deftest py-ert--end-of-minor-block-position-functionp-test ()
  (should (functionp 'py--end-of-minor-block-position)))

(ert-deftest py-ert--end-of-if-block-position-functionp-test ()
  (should (functionp 'py--end-of-if-block-position)))

(ert-deftest py-ert--end-of-try-block-position-functionp-test ()
  (should (functionp 'py--end-of-try-block-position)))

(ert-deftest py-ert--end-of-except-block-position-functionp-test ()
  (should (functionp 'py--end-of-except-block-position)))

(ert-deftest py-ert--end-of-top-level-position-functionp-test ()
  (should (functionp 'py--end-of-top-level-position)))

(ert-deftest py-ert--end-of-statement-position-bol-functionp-test ()
  (should (functionp 'py--end-of-statement-position-bol)))

(ert-deftest py-ert--end-of-block-position-bol-functionp-test ()
  (should (functionp 'py--end-of-block-position-bol)))

(ert-deftest py-ert--end-of-clause-position-bol-functionp-test ()
  (should (functionp 'py--end-of-clause-position-bol)))

(ert-deftest py-ert--end-of-block-or-clause-position-bol-functionp-test ()
  (should (functionp 'py--end-of-block-or-clause-position-bol)))

(ert-deftest py-ert--end-of-def-position-bol-functionp-test ()
  (should (functionp 'py--end-of-def-position-bol)))

(ert-deftest py-ert--end-of-class-position-bol-functionp-test ()
  (should (functionp 'py--end-of-class-position-bol)))

(ert-deftest py-ert--end-of-minor-block-position-bol-functionp-test ()
  (should (functionp 'py--end-of-minor-block-position-bol)))

(ert-deftest py-ert--end-of-if-block-position-bol-functionp-test ()
  (should (functionp 'py--end-of-if-block-position-bol)))

(ert-deftest py-ert--end-of-try-block-position-bol-functionp-test ()
  (should (functionp 'py--end-of-try-block-position-bol)))

(ert-deftest py-ert-kill-block-functionp-test ()
  (should (functionp 'py-kill-block)))

(ert-deftest py-ert-kill-clause-functionp-test ()
  (should (functionp 'py-kill-clause)))

(ert-deftest py-ert-kill-block-or-clause-functionp-test ()
  (should (functionp 'py-kill-block-or-clause)))

(ert-deftest py-ert-kill-def-functionp-test ()
  (should (functionp 'py-kill-def)))

(ert-deftest py-ert-kill-class-functionp-test ()
  (should (functionp 'py-kill-class)))

(ert-deftest py-ert-kill-def-or-class-functionp-test ()
  (should (functionp 'py-kill-def-or-class)))

(ert-deftest py-ert-kill-if-block-functionp-test ()
  (should (functionp 'py-kill-if-block)))

(ert-deftest py-ert-kill-try-block-functionp-test ()
  (should (functionp 'py-kill-try-block)))

(ert-deftest py-ert-kill-minor-block-functionp-test ()
  (should (functionp 'py-kill-minor-block)))

(ert-deftest py-ert-kill-for-block-functionp-test ()
  (should (functionp 'py-kill-for-block)))

(ert-deftest py-ert-kill-top-level-functionp-test ()
  (should (functionp 'py-kill-top-level)))

(ert-deftest py-ert-kill-statement-functionp-test ()
  (should (functionp 'py-kill-statement)))

(ert-deftest py-ert-kill-expression-functionp-test ()
  (should (functionp 'py-kill-expression)))

(ert-deftest py-ert-kill-partial-expression-functionp-test ()
  (should (functionp 'py-kill-partial-expression)))

(ert-deftest py-ert-backward-expression-functionp-test ()
  (should (functionp 'py-backward-expression)))

(ert-deftest py-ert-forward-expression-functionp-test ()
  (should (functionp 'py-forward-expression)))

(ert-deftest py-ert-beginning-of-partial-expression-functionp-test ()
  (should (functionp 'py-backward-partial-expression)))

(ert-deftest py-ert-forward-partial-expression-functionp-test ()
  (should (functionp 'py-forward-partial-expression)))

(ert-deftest py-ert-beginning-of-line-functionp-test ()
  (should (functionp 'py-beginning-of-line)))

(ert-deftest py-ert-end-of-line-functionp-test ()
  (should (functionp 'py-end-of-line)))

(ert-deftest py-ert-backward-statement-functionp-test ()
  (should (functionp 'py-backward-statement)))

(ert-deftest py-ert-beginning-of-statement-bol-functionp-test ()
  (should (functionp 'py-backward-statement-bol)))

(ert-deftest py-ert-end-of-statement-functionp-test ()
  (should (functionp 'py-forward-statement)))

(ert-deftest py-ert-end-of-statement-bol-functionp-test ()
  (should (functionp 'py-forward-statement-bol)))

(ert-deftest py-ert-backward-decorator-functionp-test ()
  (should (functionp 'py-backward-decorator)))

(ert-deftest py-ert-end-of-decorator-functionp-test ()
  (should (functionp 'py-forward-decorator)))

(ert-deftest py-ert-forward-line-functionp-test ()
  (should (functionp 'py-forward-line)))

(ert-deftest py-ert-go-to-backward-comment-functionp-test ()
  (should (functionp 'py-go-to-beginning-of-comment)))

(ert-deftest py-ert--go-to-keyword-functionp-test ()
  (should (functionp 'py--go-to-keyword)))

(ert-deftest py-ert--clause-lookup-keyword-functionp-test ()
  (should (functionp 'py--clause-lookup-keyword)))

(ert-deftest py-ert-leave-comment-or-string-backward-functionp-test ()
  (should (functionp 'py-leave-comment-or-string-backward)))

(ert-deftest py-ert-beginning-of-list-pps-functionp-test ()
  (should (functionp 'py-beginning-of-list-pps)))

(ert-deftest py-ert-forward-into-nomenclature-functionp-test ()
  (should (functionp 'py-forward-into-nomenclature)))

(ert-deftest py-ert-backward-into-nomenclature-functionp-test ()
  (should (functionp 'py-backward-into-nomenclature)))

(ert-deftest py-ert--travel-current-indent-functionp-test ()
  (should (functionp 'py--travel-current-indent)))

(ert-deftest py-ert-beginning-of-block-current-column-functionp-test ()
  (should (functionp 'py-beginning-of-block-current-column)))

(ert-deftest py-ert--end-of-block-p-functionp-test ()
  (should (functionp 'py--end-of-block-p)))

(ert-deftest py-ert--end-of-clause-p-functionp-test ()
  (should (functionp 'py--end-of-clause-p)))

(ert-deftest py-ert--end-of-block-or-clause-p-functionp-test ()
  (should (functionp 'py--end-of-block-or-clause-p)))

(ert-deftest py-ert--end-of-def-p-functionp-test ()
  (should (functionp 'py--end-of-def-p)))

(ert-deftest py-ert--end-of-class-p-functionp-test ()
  (should (functionp 'py--end-of-class-p)))

(ert-deftest py-ert--end-of-def-or-class-p-functionp-test ()
  (should (functionp 'py--end-of-def-or-class-p)))

(ert-deftest py-ert--end-of-if-block-p-functionp-test ()
  (should (functionp 'py--end-of-if-block-p)))

(ert-deftest py-ert--end-of-try-block-p-functionp-test ()
  (should (functionp 'py--end-of-try-block-p)))

(ert-deftest py-ert--end-of-minor-block-p-functionp-test ()
  (should (functionp 'py--end-of-minor-block-p)))

(ert-deftest py-ert--end-of-for-block-p-functionp-test ()
  (should (functionp 'py--end-of-for-block-p)))

(ert-deftest py-ert--end-of-top-level-p-functionp-test ()
  (should (functionp 'py--end-of-top-level-p)))

(ert-deftest py-ert--end-of-statement-p-functionp-test ()
  (should (functionp 'py--end-of-statement-p)))

(ert-deftest py-ert--end-of-expression-p-functionp-test ()
  (should (functionp 'py--end-of-expression-p)))

(ert-deftest py-ert--end-of-block-bol-p-functionp-test ()
  (should (functionp 'py--end-of-block-bol-p)))

(ert-deftest py-ert--end-of-clause-bol-p-functionp-test ()
  (should (functionp 'py--end-of-clause-bol-p)))

(ert-deftest py-ert--end-of-block-or-clause-bol-p-functionp-test ()
  (should (functionp 'py--end-of-block-or-clause-bol-p)))

(ert-deftest py-ert--end-of-def-bol-p-functionp-test ()
  (should (functionp 'py--end-of-def-bol-p)))

(ert-deftest py-ert--end-of-class-bol-p-functionp-test ()
  (should (functionp 'py--end-of-class-bol-p)))

(ert-deftest py-ert--end-of-def-or-class-bol-p-functionp-test ()
  (should (functionp 'py--end-of-def-or-class-bol-p)))

(ert-deftest py-ert--end-of-if-block-bol-p-functionp-test ()
  (should (functionp 'py--end-of-if-block-bol-p)))

(ert-deftest py-ert--end-of-try-block-bol-p-functionp-test ()
  (should (functionp 'py--end-of-try-block-bol-p)))

(ert-deftest py-ert--end-of-minor-block-bol-p-functionp-test ()
  (should (functionp 'py--end-of-minor-block-bol-p)))

(ert-deftest py-ert--end-of-for-block-bol-p-functionp-test ()
  (should (functionp 'py--end-of-for-block-bol-p)))

(ert-deftest py-ert--end-of-statement-bol-p-functionp-test ()
  (should (functionp 'py--end-of-statement-bol-p)))

(ert-deftest py-ert--fast-completion-get-completions-functionp-test ()
  (should (functionp 'py--fast-completion-get-completions)))

(ert-deftest py-ert--fast--do-completion-at-point-functionp-test ()
  (should (functionp 'py--fast--do-completion-at-point)))

(ert-deftest py-ert--fast-complete-base-functionp-test ()
  (should (functionp 'py--fast-complete-base)))

(ert-deftest py-ert-fast-complete-functionp-test ()
  (should (functionp 'py-fast-complete)))

(ert-deftest py-ert--all-shell-mode-setting-functionp-test ()
  (should (functionp 'py--all-shell-mode-setting)))

(ert-deftest py-ert-fast-process-functionp-test ()
  (should (functionp 'py-fast-process)))

(ert-deftest py-ert--filter-result-functionp-test ()
  (should (functionp 'py--filter-result)))

(ert-deftest py-ert--fast-send-string-no-output-functionp-test ()
  (should (functionp 'py--fast-send-string-no-output)))

(ert-deftest py-ert--fast-send-string-intern-functionp-test ()
  (should (functionp 'py--fast-send-string-intern)))

(ert-deftest py-ert--fast-send-string-functionp-test ()
  (should (functionp 'py--fast-send-string)))

(ert-deftest py-ert-fast-send-string-functionp-test ()
  (should (functionp 'py--fast-send-string)))

(ert-deftest py-ert-process-region-fast-functionp-test ()
  (should (functionp 'py-process-region-fast)))

(ert-deftest py-ert-execute-statement-fast-functionp-test ()
  (should (functionp 'py-execute-statement-fast)))

(ert-deftest py-ert-execute-block-fast-functionp-test ()
  (should (functionp 'py-execute-block-fast)))

(ert-deftest py-ert-execute-block-or-clause-fast-functionp-test ()
  (should (functionp 'py-execute-block-or-clause-fast)))

(ert-deftest py-ert-execute-def-fast-functionp-test ()
  (should (functionp 'py-execute-def-fast)))

(ert-deftest py-ert-execute-class-fast-functionp-test ()
  (should (functionp 'py-execute-class-fast)))

(ert-deftest py-ert-execute-def-or-class-fast-functionp-test ()
  (should (functionp 'py-execute-def-or-class-fast)))

(ert-deftest py-ert-execute-expression-fast-functionp-test ()
  (should (functionp 'py-execute-expression-fast)))

(ert-deftest py-ert-execute-partial-expression-fast-functionp-test ()
  (should (functionp 'py-execute-partial-expression-fast)))

(ert-deftest py-ert-execute-top-level-fast-functionp-test ()
  (should (functionp 'py-execute-top-level-fast)))

(ert-deftest py-ert-execute-clause-fast-functionp-test ()
  (should (functionp 'py-execute-clause-fast)))

(ert-deftest py-ert-restore-window-configuration-functionp-test ()
  (should (functionp 'py-restore-window-configuration)))

(ert-deftest py-ert-shell-execute-string-now-functionp-test ()
  (should (functionp 'py-shell-execute-string-now)))

(ert-deftest py-ert-switch-to-python-functionp-test ()
  (should (functionp 'py-switch-to-python)))

(ert-deftest py-ert-send-file-functionp-test ()
  (should (functionp 'py-send-file)))

(ert-deftest py-ert-toggle-force-local-shell-functionp-test ()
  (should (functionp 'toggle-force-local-shell)))

(ert-deftest py-ert-force-local-shell-on-functionp-test ()
  (should (functionp 'py-force-local-shell-on)))

(ert-deftest py-ert-force-local-shell-off-functionp-test ()
  (should (functionp 'py-force-local-shell-off)))

(ert-deftest py-ert-toggle-force-py-shell-name-p-functionp-test ()
  (should (functionp 'toggle-force-py-shell-name-p)))

(ert-deftest py-ert-force-py-shell-name-p-on-functionp-test ()
  (should (functionp 'force-py-shell-name-p-on)))

(ert-deftest py-ert-force-py-shell-name-p-off-functionp-test ()
  (should (functionp 'force-py-shell-name-p-off)))

(ert-deftest py-ert-toggle-split-windows-on-execute-functionp-test ()
  (should (functionp 'py-toggle-split-windows-on-execute)))

(ert-deftest py-ert-split-windows-on-execute-on-functionp-test ()
  (should (functionp 'py-split-windows-on-execute-on)))

(ert-deftest py-ert-split-windows-on-execute-off-functionp-test ()
  (should (functionp 'py-split-windows-on-execute-off)))

(ert-deftest py-ert-toggle-shell-switch-buffers-on-execute-functionp-test ()
  (should (functionp 'py-toggle-shell-switch-buffers-on-execute)))

(ert-deftest py-ert-shell-switch-buffers-on-execute-on-functionp-test ()
  (should (functionp 'py-shell-switch-buffers-on-execute-on)))

(ert-deftest py-ert-shell-switch-buffers-on-execute-off-functionp-test ()
  (should (functionp 'py-shell-switch-buffers-on-execute-off)))

(ert-deftest py-ert-guess-default-python-functionp-test ()
  (should (functionp 'py-guess-default-python)))

(ert-deftest py-ert-dirstack-hook-functionp-test ()
  (should (functionp 'py-dirstack-hook)))

(ert-deftest py-ert-shell-dedicated-functionp-test ()
  (should (functionp 'py-shell-dedicated)))

(ert-deftest py-ert-set-ipython-completion-command-string-functionp-test ()
  (should (functionp 'py-set-ipython-completion-command-string)))

(ert-deftest py-ert-ipython--module-completion-import-functionp-test ()
  (should (functionp 'py-ipython--module-completion-import)))

(ert-deftest py-ert--compose-buffer-name-initials-functionp-test ()
  (should (functionp 'py--compose-buffer-name-initials)))

(ert-deftest py-ert--remove-home-directory-from-list-functionp-test ()
  (should (functionp 'py--remove-home-directory-from-list)))

(ert-deftest py-ert--choose-buffer-name-functionp-test ()
  (should (functionp 'py--choose-buffer-name)))

(ert-deftest py-ert--jump-to-exception-intern-functionp-test ()
  (should (functionp 'py--jump-to-exception-intern)))

(ert-deftest py-ert--jump-to-exception-functionp-test ()
  (should (functionp 'py--jump-to-exception)))

(ert-deftest py-ert-toggle-split-window-function-functionp-test ()
  (should (functionp 'py-toggle-split-window-function)))

(ert-deftest py-ert--manage-windows-set-and-switch-functionp-test ()
  (should (functionp 'py--manage-windows-set-and-switch)))

(ert-deftest py-ert--alternative-split-windows-on-execute-function-functionp-test ()
  (should (functionp 'py--alternative-split-windows-on-execute-function)))

(ert-deftest py-ert--get-splittable-window-functionp-test ()
  (should (functionp 'py--get-splittable-window)))

(ert-deftest py-ert--manage-windows-split-functionp-test ()
  (should (functionp 'py--manage-windows-split)))

(ert-deftest py-ert--shell-manage-windows-functionp-test ()
  (should (functionp 'py--shell-manage-windows)))

(ert-deftest py-ert-kill-shell-unconditional-functionp-test ()
  (should (functionp 'py-kill-shell-unconditional)))

(ert-deftest py-ert-kill-default-shell-unconditional-functionp-test ()
  (should (functionp 'py-kill-default-shell-unconditional)))

(ert-deftest py-ert--report-executable-functionp-test ()
  (should (functionp 'py--report-executable)))

(ert-deftest py-ert--shell-make-comint-functionp-test ()
  (should (functionp 'py--shell-make-comint)))

(ert-deftest py-ert--guess-buffer-name-functionp-test ()
  (should (functionp 'py--guess-buffer-name)))

(ert-deftest py-ert--configured-shell-functionp-test ()
  (should (functionp 'py--configured-shell)))

(ert-deftest py-ert--grab-prompt-ps1-functionp-test ()
  (should (functionp 'py--grab-prompt-ps1)))

(ert-deftest py-ert--start-fast-process-functionp-test ()
  (should (functionp 'py--start-fast-process)))

(ert-deftest py-ert-shell-functionp-test ()
  (should (functionp 'py-shell)))

(ert-deftest py-ert-shell-get-process-functionp-test ()
  (should (functionp 'py-shell-get-process)))

(ert-deftest py-ert-switch-to-shell-functionp-test ()
  (should (functionp 'py-switch-to-shell)))

(ert-deftest py-ert-which-execute-file-command-functionp-test ()
  (should (functionp 'py-which-execute-file-command)))

(ert-deftest py-ert--store-result-maybe-functionp-test ()
  (should (functionp 'py--store-result-maybe)))

(ert-deftest py-ert--close-execution-functionp-test ()
  (should (functionp 'py--close-execution)))

(ert-deftest py-ert--execute-base-functionp-test ()
  (should (functionp 'py--execute-base)))

(ert-deftest py-ert--send-to-fast-process-functionp-test ()
  (should (functionp 'py--send-to-fast-process)))

(ert-deftest py-ert--execute-base-intern-functionp-test ()
  (should (functionp 'py--execute-base-intern)))

(ert-deftest py-ert--execute-buffer-finally-functionp-test ()
  (should (functionp 'py--execute-buffer-finally)))

(ert-deftest py-ert--fetch-error-functionp-test ()
  (should (functionp 'py--fetch-error)))

(ert-deftest py-ert--fetch-result-functionp-test ()
  (should (functionp 'py--fetch-result)))

(ert-deftest py-ert--postprocess-comint-functionp-test ()
  (should (functionp 'py--postprocess-comint)))

(ert-deftest py-ert--execute-ge24.3-functionp-test ()
  (should (functionp 'py--execute-ge24.3)))

(ert-deftest py-ert-delete-temporary-functionp-test ()
  (should (functionp 'py-delete-temporary)))

(ert-deftest py-ert-execute-python-mode-v5-functionp-test ()
  (should (functionp 'py-execute-python-mode-v5)))

(ert-deftest py-ert--insert-offset-lines-functionp-test ()
  (should (functionp 'py--insert-offset-lines)))

(ert-deftest py-ert--execute-file-base-functionp-test ()
  (should (functionp 'py--execute-file-base)))

(ert-deftest py-ert-execute-file-functionp-test ()
  (should (functionp 'py-execute-file)))

(ert-deftest py-ert--current-working-directory-functionp-test ()
  (should (functionp 'py--current-working-directory)))

(ert-deftest py-ert--update-execute-directory-intern-functionp-test ()
  (should (functionp 'py--update-execute-directory-intern)))

(ert-deftest py-ert--update-execute-directory-functionp-test ()
  (should (functionp 'py--update-execute-directory)))

(ert-deftest py-ert-execute-string-functionp-test ()
  (should (functionp 'py-execute-string)))

(ert-deftest py-ert-execute-string-dedicated-functionp-test ()
  (should (functionp 'py-execute-string-dedicated)))

(ert-deftest py-ert--insert-execute-directory-functionp-test ()
  (should (functionp 'py--insert-execute-directory)))

(ert-deftest py-ert--fix-if-name-main-permission-functionp-test ()
  (should (functionp 'py--fix-if-name-main-permission)))

(ert-deftest py-ert--fix-start-functionp-test ()
  (should (functionp 'py--fix-start)))

(ert-deftest py-ert-fetch-py-master-file-functionp-test ()
  (should (functionp 'py-fetch-py-master-file)))

(ert-deftest py-ert-execute-import-or-reload-functionp-test ()
  (should (functionp 'py-execute-import-or-reload)))

(ert-deftest py-ert--qualified-module-name-functionp-test ()
  (should (functionp 'py--qualified-module-name)))

(ert-deftest py-ert-execute-buffer-functionp-test ()
  (should (functionp 'py-execute-buffer)))

(ert-deftest py-ert-execute-buffer-dedicated-functionp-test ()
  (should (functionp 'py-execute-buffer-dedicated)))

(ert-deftest py-ert-execute-buffer-switch-functionp-test ()
  (should (functionp 'py-execute-buffer-switch)))

(ert-deftest py-ert-execute-buffer-no-switch-functionp-test ()
  (should (functionp 'py-execute-buffer-no-switch)))

(ert-deftest py-ert-execute-buffer-dedicated-switch-functionp-test ()
  (should (functionp 'py-execute-buffer-dedicated-switch)))

(ert-deftest py-ert-execute-region-python-functionp-test ()
  (should (functionp 'py-execute-region-python)))

(ert-deftest py-ert-execute-region-python-switch-functionp-test ()
  (should (functionp 'py-execute-region-python-switch)))

(ert-deftest py-ert-execute-region-python-no-switch-functionp-test ()
  (should (functionp 'py-execute-region-python-no-switch)))

(ert-deftest py-ert-execute-region-python2-functionp-test ()
  (should (functionp 'py-execute-region-python2)))

(ert-deftest py-ert-execute-region-python2-switch-functionp-test ()
  (should (functionp 'py-execute-region-python2-switch)))

(ert-deftest py-ert-execute-region-python2-no-switch-functionp-test ()
  (should (functionp 'py-execute-region-python2-no-switch)))

(ert-deftest py-ert-execute-region-python3-functionp-test ()
  (should (functionp 'py-execute-region-python3)))

(ert-deftest py-ert-execute-region-python3-switch-functionp-test ()
  (should (functionp 'py-execute-region-python3-switch)))

(ert-deftest py-ert-execute-region-python3-no-switch-functionp-test ()
  (should (functionp 'py-execute-region-python3-no-switch)))

(ert-deftest py-ert-execute-region-ipython-functionp-test ()
  (should (functionp 'py-execute-region-ipython)))

(ert-deftest py-ert-execute-region-ipython-switch-functionp-test ()
  (should (functionp 'py-execute-region-ipython-switch)))

(ert-deftest py-ert-execute-region-ipython-no-switch-functionp-test ()
  (should (functionp 'py-execute-region-ipython-no-switch)))

(ert-deftest py-ert-execute-region-jython-functionp-test ()
  (should (functionp 'py-execute-region-jython)))

(ert-deftest py-ert-execute-region-jython-switch-functionp-test ()
  (should (functionp 'py-execute-region-jython-switch)))

(ert-deftest py-ert-execute-region-jython-no-switch-functionp-test ()
  (should (functionp 'py-execute-region-jython-no-switch)))

(ert-deftest py-ert-execute-defun-functionp-test ()
  (should (functionp 'py-execute-defun)))

(ert-deftest py-ert-process-file-functionp-test ()
  (should (functionp 'py-process-file)))

(ert-deftest py-ert-execute-line-functionp-test ()
  (should (functionp 'py-execute-line)))

(ert-deftest py-ert-remove-overlays-at-point-functionp-test ()
  (should (functionp 'py-remove-overlays-at-point)))

(ert-deftest py-ert-mouseto-exception-functionp-test ()
  (should (functionp 'py-mouseto-exception)))

(ert-deftest py-ert-goto-exception-functionp-test ()
  (should (functionp 'py-goto-exception)))

(ert-deftest py-ert--find-next-exception-functionp-test ()
  (should (functionp 'py--find-next-exception)))

(ert-deftest py-ert-down-exception-functionp-test ()
  (should (functionp 'py-down-exception)))

(ert-deftest py-ert-up-exception-functionp-test ()
  (should (functionp 'py-up-exception)))

(ert-deftest py-ert--postprocess-intern-functionp-test ()
  (should (functionp 'py--postprocess-intern)))

(ert-deftest py-ert--find-next-exception-prepare-functionp-test ()
  (should (functionp 'py--find-next-exception-prepare)))

(ert-deftest py-ert-python-functionp-test ()
  (should (functionp 'python)))

(ert-deftest py-ert-ipython-functionp-test ()
  (should (functionp 'ipython)))

(ert-deftest py-ert-python2-functionp-test ()
  (should (functionp 'python2)))

(ert-deftest py-ert-jython-functionp-test ()
  (should (functionp 'jython)))

(ert-deftest py-ert-python3-functionp-test ()
  (should (functionp 'python3)))

(ert-deftest py-ert-python-dedicated-functionp-test ()
  (should (functionp 'python-dedicated)))

(ert-deftest py-ert-ipython-dedicated-functionp-test ()
  (should (functionp 'ipython-dedicated)))

(ert-deftest py-ert-python2-dedicated-functionp-test ()
  (should (functionp 'python2-dedicated)))

(ert-deftest py-ert-jython-dedicated-functionp-test ()
  (should (functionp 'jython-dedicated)))

(ert-deftest py-ert-python3-dedicated-functionp-test ()
  (should (functionp 'python3-dedicated)))

(ert-deftest py-ert-python-switch-functionp-test ()
  (should (functionp 'python-switch)))

(ert-deftest py-ert-ipython-switch-functionp-test ()
  (should (functionp 'ipython-switch)))

(ert-deftest py-ert-python2-switch-functionp-test ()
  (should (functionp 'python2-switch)))

(ert-deftest py-ert-jython-switch-functionp-test ()
  (should (functionp 'jython-switch)))

(ert-deftest py-ert-python3-switch-functionp-test ()
  (should (functionp 'python3-switch)))

(ert-deftest py-ert-python-no-switch-functionp-test ()
  (should (functionp 'python-no-switch)))

(ert-deftest py-ert-ipython-no-switch-functionp-test ()
  (should (functionp 'ipython-no-switch)))

(ert-deftest py-ert-python2-no-switch-functionp-test ()
  (should (functionp 'python2-no-switch)))

(ert-deftest py-ert-jython-no-switch-functionp-test ()
  (should (functionp 'jython-no-switch)))

(ert-deftest py-ert-python3-no-switch-functionp-test ()
  (should (functionp 'python3-no-switch)))

(ert-deftest py-ert-python-switch-dedicated-functionp-test ()
  (should (functionp 'python-switch-dedicated)))

(ert-deftest py-ert-ipython-switch-dedicated-functionp-test ()
  (should (functionp 'ipython-switch-dedicated)))

(ert-deftest py-ert-python2-switch-dedicated-functionp-test ()
  (should (functionp 'python2-switch-dedicated)))

(ert-deftest py-ert-jython-switch-dedicated-functionp-test ()
  (should (functionp 'jython-switch-dedicated)))

(ert-deftest py-ert-python3-switch-dedicated-functionp-test ()
  (should (functionp 'python3-switch-dedicated)))

(ert-deftest py-ert-hide-base-functionp-test ()
  (should (functionp 'py-hide-base)))

(ert-deftest py-ert-show-base-functionp-test ()
  (should (functionp 'py-show-base)))

(ert-deftest py-ert-hide-show-functionp-test ()
  (should (functionp 'py-hide-show)))

(ert-deftest py-ert-hide-region-functionp-test ()
  (should (functionp 'py-hide-region)))

(ert-deftest py-ert-show-region-functionp-test ()
  (should (functionp 'py-show-region)))

(ert-deftest py-ert-hide-statement-functionp-test ()
  (should (functionp 'py-hide-statement)))

(ert-deftest py-ert-show-statement-functionp-test ()
  (should (functionp 'py-show-statement)))

(ert-deftest py-ert-hide-block-functionp-test ()
  (should (functionp 'py-hide-block)))

(ert-deftest py-ert-show-block-functionp-test ()
  (should (functionp 'py-show-block)))

(ert-deftest py-ert-hide-clause-functionp-test ()
  (should (functionp 'py-hide-clause)))

(ert-deftest py-ert-show-clause-functionp-test ()
  (should (functionp 'py-show-clause)))

(ert-deftest py-ert-hide-block-or-clause-functionp-test ()
  (should (functionp 'py-hide-block-or-clause)))

(ert-deftest py-ert-show-block-or-clause-functionp-test ()
  (should (functionp 'py-show-block-or-clause)))

(ert-deftest py-ert-hide-def-functionp-test ()
  (should (functionp 'py-hide-def)))

(ert-deftest py-ert-show-def-functionp-test ()
  (should (functionp 'py-show-def)))

(ert-deftest py-ert-hide-class-functionp-test ()
  (should (functionp 'py-hide-class)))

(ert-deftest py-ert-show-class-functionp-test ()
  (should (functionp 'py-show-class)))

(ert-deftest py-ert-hide-expression-functionp-test ()
  (should (functionp 'py-hide-expression)))

(ert-deftest py-ert-show-expression-functionp-test ()
  (should (functionp 'py-show-expression)))

(ert-deftest py-ert-hide-partial-expression-functionp-test ()
  (should (functionp 'py-hide-partial-expression)))

(ert-deftest py-ert-show-partial-expression-functionp-test ()
  (should (functionp 'py-show-partial-expression)))

(ert-deftest py-ert-hide-line-functionp-test ()
  (should (functionp 'py-hide-line)))

(ert-deftest py-ert-show-line-functionp-test ()
  (should (functionp 'py-show-line)))

(ert-deftest py-ert-hide-top-level-functionp-test ()
  (should (functionp 'py-hide-top-level)))

(ert-deftest py-ert-show-top-level-functionp-test ()
  (should (functionp 'py-show-top-level)))

(ert-deftest py-ert-copy-statement-functionp-test ()
  (should (functionp 'py-copy-statement)))

(ert-deftest py-ert-copy-statement-bol-functionp-test ()
  (should (functionp 'py-copy-statement-bol)))

(ert-deftest py-ert-copy-top-level-functionp-test ()
  (should (functionp 'py-copy-top-level)))

(ert-deftest py-ert-copy-top-level-bol-functionp-test ()
  (should (functionp 'py-copy-top-level-bol)))

(ert-deftest py-ert-copy-block-functionp-test ()
  (should (functionp 'py-copy-block)))

(ert-deftest py-ert-copy-block-bol-functionp-test ()
  (should (functionp 'py-copy-block-bol)))

(ert-deftest py-ert-copy-clause-functionp-test ()
  (should (functionp 'py-copy-clause)))

(ert-deftest py-ert-copy-clause-bol-functionp-test ()
  (should (functionp 'py-copy-clause-bol)))

(ert-deftest py-ert-copy-block-or-clause-functionp-test ()
  (should (functionp 'py-copy-block-or-clause)))

(ert-deftest py-ert-copy-block-or-clause-bol-functionp-test ()
  (should (functionp 'py-copy-block-or-clause-bol)))

(ert-deftest py-ert-copy-def-functionp-test ()
  (should (functionp 'py-copy-def)))

(ert-deftest py-ert-copy-def-bol-functionp-test ()
  (should (functionp 'py-copy-def-bol)))

(ert-deftest py-ert-copy-class-functionp-test ()
  (should (functionp 'py-copy-class)))

(ert-deftest py-ert-copy-class-bol-functionp-test ()
  (should (functionp 'py-copy-class-bol)))

(ert-deftest py-ert-copy-def-or-class-functionp-test ()
  (should (functionp 'py-copy-def-or-class)))

(ert-deftest py-ert-copy-def-or-class-bol-functionp-test ()
  (should (functionp 'py-copy-def-or-class-bol)))

(ert-deftest py-ert-copy-expression-functionp-test ()
  (should (functionp 'py-copy-expression)))

(ert-deftest py-ert-copy-expression-bol-functionp-test ()
  (should (functionp 'py-copy-expression-bol)))

(ert-deftest py-ert-copy-partial-expression-functionp-test ()
  (should (functionp 'py-copy-partial-expression)))

(ert-deftest py-ert-copy-partial-expression-bol-functionp-test ()
  (should (functionp 'py-copy-partial-expression-bol)))

(ert-deftest py-ert-copy-minor-block-functionp-test ()
  (should (functionp 'py-copy-minor-block)))

(ert-deftest py-ert-copy-minor-block-bol-functionp-test ()
  (should (functionp 'py-copy-minor-block-bol)))

(ert-deftest py-ert-statement-functionp-test ()
  (should (functionp 'py-statement)))

(ert-deftest py-ert-top-level-functionp-test ()
  (should (functionp 'py-top-level)))

(ert-deftest py-ert-block-functionp-test ()
  (should (functionp 'py-block)))

(ert-deftest py-ert-clause-functionp-test ()
  (should (functionp 'py-clause)))

(ert-deftest py-ert-block-or-clause-functionp-test ()
  (should (functionp 'py-block-or-clause)))

(ert-deftest py-ert-def-functionp-test ()
  (should (functionp 'py-def)))

(ert-deftest py-ert-class-functionp-test ()
  (should (functionp 'py-class)))

(ert-deftest py-ert-def-or-class-functionp-test ()
  (should (functionp 'py-def-or-class)))

(ert-deftest py-ert-expression-functionp-test ()
  (should (functionp 'py-expression)))

(ert-deftest py-ert-partial-expression-functionp-test ()
  (should (functionp 'py-partial-expression)))

(ert-deftest py-ert-minor-block-functionp-test ()
  (should (functionp 'py-minor-block)))

(ert-deftest py-ert-output-buffer-filter-functionp-test ()
  (should (functionp 'py-output-buffer-filter)))

(ert-deftest py-ert-output-filter-functionp-test ()
  (should (functionp 'py-output-filter)))

(ert-deftest py-ert-send-string-functionp-test ()
  (should (functionp 'py-send-string)))

(ert-deftest py-ert-copy-statement-functionp-test ()
  (should (functionp 'py-copy-statement)))

(ert-deftest py-ert-copy-top-level-functionp-test ()
  (should (functionp 'py-copy-top-level)))

(ert-deftest py-ert-copy-block-functionp-test ()
  (should (functionp 'py-copy-block)))

(ert-deftest py-ert-copy-clause-functionp-test ()
  (should (functionp 'py-copy-clause)))

(ert-deftest py-ert-copy-block-or-clause-functionp-test ()
  (should (functionp 'py-copy-block-or-clause)))

(ert-deftest py-ert-copy-def-functionp-test ()
  (should (functionp 'py-copy-def)))

(ert-deftest py-ert-copy-class-functionp-test ()
  (should (functionp 'py-copy-class)))

(ert-deftest py-ert-copy-def-or-class-functionp-test ()
  (should (functionp 'py-copy-def-or-class)))

(ert-deftest py-ert-copy-expression-functionp-test ()
  (should (functionp 'py-copy-expression)))

(ert-deftest py-ert-copy-partial-expression-functionp-test ()
  (should (functionp 'py-copy-partial-expression)))

(ert-deftest py-ert-copy-minor-block-functionp-test ()
  (should (functionp 'py-copy-minor-block)))

(ert-deftest py-ert-delete-statement-functionp-test ()
  (should (functionp 'py-delete-statement)))

(ert-deftest py-ert-delete-top-level-functionp-test ()
  (should (functionp 'py-delete-top-level)))

(ert-deftest py-ert-delete-block-functionp-test ()
  (should (functionp 'py-delete-block)))

(ert-deftest py-ert-delete-clause-functionp-test ()
  (should (functionp 'py-delete-clause)))

(ert-deftest py-ert-delete-block-or-clause-functionp-test ()
  (should (functionp 'py-delete-block-or-clause)))

(ert-deftest py-ert-delete-def-functionp-test ()
  (should (functionp 'py-delete-def)))

(ert-deftest py-ert-delete-class-functionp-test ()
  (should (functionp 'py-delete-class)))

(ert-deftest py-ert-delete-def-or-class-functionp-test ()
  (should (functionp 'py-delete-def-or-class)))

(ert-deftest py-ert-delete-expression-functionp-test ()
  (should (functionp 'py-delete-expression)))

(ert-deftest py-ert-delete-partial-expression-functionp-test ()
  (should (functionp 'py-delete-partial-expression)))

(ert-deftest py-ert-delete-minor-block-functionp-test ()
  (should (functionp 'py-delete-minor-block)))

(ert-deftest py-ert--beginning-of-statement-position-functionp-test ()
  (should (functionp 'py--beginning-of-statement-position)))

(ert-deftest py-ert--beginning-of-block-position-functionp-test ()
  (should (functionp 'py--beginning-of-block-position)))

(ert-deftest py-ert--beginning-of-clause-position-functionp-test ()
  (should (functionp 'py--beginning-of-clause-position)))

(ert-deftest py-ert--beginning-of-block-or-clause-position-functionp-test ()
  (should (functionp 'py--beginning-of-block-or-clause-position)))

(ert-deftest py-ert--beginning-of-def-position-functionp-test ()
  (should (functionp 'py--beginning-of-def-position)))

(ert-deftest py-ert--beginning-of-class-position-functionp-test ()
  (should (functionp 'py--beginning-of-class-position)))

(ert-deftest py-ert--beginning-of-def-or-class-position-functionp-test ()
  (should (functionp 'py--beginning-of-def-or-class-position)))

(ert-deftest py-ert--beginning-of-expression-position-functionp-test ()
  (should (functionp 'py--beginning-of-expression-position)))

(ert-deftest py-ert--beginning-of-partial-expression-position-functionp-test ()
  (should (functionp 'py--beginning-of-partial-expression-position)))

(ert-deftest py-ert--beginning-of-minor-block-position-functionp-test ()
  (should (functionp 'py--beginning-of-minor-block-position)))

(ert-deftest py-ert--beginning-of-if-block-position-functionp-test ()
  (should (functionp 'py--beginning-of-if-block-position)))

(ert-deftest py-ert--beginning-of-try-block-position-functionp-test ()
  (should (functionp 'py--beginning-of-try-block-position)))

(ert-deftest py-ert--beginning-of-except-block-position-functionp-test ()
  (should (functionp 'py--beginning-of-except-block-position)))

(ert-deftest py-ert--beginning-of-statement-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-statement-position-bol)))

(ert-deftest py-ert--beginning-of-block-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-block-position-bol)))

(ert-deftest py-ert--beginning-of-clause-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-clause-position-bol)))

(ert-deftest py-ert--beginning-of-block-or-clause-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-block-or-clause-position-bol)))

(ert-deftest py-ert--beginning-of-def-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-def-position-bol)))

(ert-deftest py-ert--beginning-of-class-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-class-position-bol)))

(ert-deftest py-ert--beginning-of-def-or-class-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-def-or-class-position-bol)))

(ert-deftest py-ert--beginning-of-minor-block-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-minor-block-position-bol)))

(ert-deftest py-ert--beginning-of-if-block-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-if-block-position-bol)))

(ert-deftest py-ert--beginning-of-try-block-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-try-block-position-bol)))

(ert-deftest py-ert--beginning-of-except-block-position-bol-functionp-test ()
  (should (functionp 'py--beginning-of-except-block-position-bol)))

(ert-deftest py-ert-fill-string-django-functionp-test ()
  (should (functionp 'py-fill-string-django)))

(ert-deftest py-ert-fill-string-onetwo-functionp-test ()
  (should (functionp 'py-fill-string-onetwo)))

(ert-deftest py-ert-fill-string-pep-257-functionp-test ()
  (should (functionp 'py-fill-string-pep-257)))

(ert-deftest py-ert-fill-string-pep-257-nn-functionp-test ()
  (should (functionp 'py-fill-string-pep-257-nn)))

(ert-deftest py-ert-fill-string-symmetric-functionp-test ()
  (should (functionp 'py-fill-string-symmetric)))

(ert-deftest py-ert-set-nil-docstring-style-functionp-test ()
  (should (functionp 'py-set-nil-docstring-style)))

(ert-deftest py-ert-set-pep-257-nn-docstring-style-functionp-test ()
  (should (functionp 'py-set-pep-257-nn-docstring-style)))

(ert-deftest py-ert-set-pep-257-docstring-style-functionp-test ()
  (should (functionp 'py-set-pep-257-docstring-style)))

(ert-deftest py-ert-set-django-docstring-style-functionp-test ()
  (should (functionp 'py-set-django-docstring-style)))

(ert-deftest py-ert-set-symmetric-docstring-style-functionp-test ()
  (should (functionp 'py-set-symmetric-docstring-style)))

(ert-deftest py-ert-set-onetwo-docstring-style-functionp-test ()
  (should (functionp 'py-set-onetwo-docstring-style)))

(ert-deftest py-ert-fill-comment-functionp-test ()
  (should (functionp 'py-fill-comment)))

(ert-deftest py-ert-fill-labelled-string-functionp-test ()
  (should (functionp 'py-fill-labelled-string)))

(ert-deftest py-ert--in-or-behind-or-before-a-docstring-functionp-test ()
  (should (functionp 'py--in-or-behind-or-before-a-docstring)))

(ert-deftest py-ert--string-fence-delete-spaces-functionp-test ()
  (should (functionp 'py--string-fence-delete-spaces)))

(ert-deftest py-ert--fill-fix-end-functionp-test ()
  (should (functionp 'py--fill-fix-end)))

(ert-deftest py-ert--fill-docstring-base-functionp-test ()
  (should (functionp 'py--fill-docstring-base)))

(ert-deftest py-ert--fill-docstring-last-line-functionp-test ()
  (should (functionp 'py--fill-docstring-last-line)))

(ert-deftest py-ert--fill-docstring-first-line-functionp-test ()
  (should (functionp 'py--fill-docstring-first-line)))

(ert-deftest py-ert--fill-docstring-functionp-test ()
  (should (functionp 'py--fill-docstring)))

(ert-deftest py-ert-fill-string-functionp-test ()
  (should (functionp 'py-fill-string)))

(ert-deftest py-ert-fill-paragraph-functionp-test ()
  (should (functionp 'py-fill-paragraph)))

(ert-deftest py-ert-insert-default-shebang-functionp-test ()
  (should (functionp 'py-insert-default-shebang)))

(ert-deftest py-ert--top-level-form-p-functionp-test ()
  (should (functionp 'py--top-level-form-p)))

(ert-deftest py-ert-indent-line-outmost-functionp-test ()
  (should (functionp 'py-indent-line-outmost)))

(ert-deftest py-ert--indent-fix-region-intern-functionp-test ()
  (should (functionp 'py--indent-fix-region-intern)))

(ert-deftest py-ert--indent-line-intern-functionp-test ()
  (should (functionp 'py--indent-line-intern)))

(ert-deftest py-ert--indent-line-base-functionp-test ()
  (should (functionp 'py--indent-line-base)))

(ert-deftest py-ert--calculate-indent-backwards-functionp-test ()
  (should (functionp 'py--calculate-indent-backwards)))

(ert-deftest py-ert-indent-line-functionp-test ()
  (should (functionp 'py-indent-line)))

(ert-deftest py-ert--delete-trailing-whitespace-functionp-test ()
  (should (functionp 'py--delete-trailing-whitespace)))

(ert-deftest py-ert-newline-and-indent-functionp-test ()
  (should (functionp 'py-newline-and-indent)))

(ert-deftest py-ert-newline-and-dedent-functionp-test ()
  (should (functionp 'py-newline-and-dedent)))

(ert-deftest py-ert-toggle-indent-tabs-mode-functionp-test ()
  (should (functionp 'py-toggle-indent-tabs-mode)))

(ert-deftest py-ert-indent-tabs-mode-functionp-test ()
  (should (functionp 'py-indent-tabs-mode)))

(ert-deftest py-ert-indent-tabs-mode-on-functionp-test ()
  (should (functionp 'py-indent-tabs-mode-on)))

(ert-deftest py-ert-indent-tabs-mode-off-functionp-test ()
  (should (functionp 'py-indent-tabs-mode-off)))

(ert-deftest py-ert-guessed-sanity-check-functionp-test ()
  (should (functionp 'py-guessed-sanity-check)))

(ert-deftest py-ert--guess-indent-final-functionp-test ()
  (should (functionp 'py--guess-indent-final)))

(ert-deftest py-ert--guess-indent-forward-functionp-test ()
  (should (functionp 'py--guess-indent-forward)))

(ert-deftest py-ert--guess-indent-backward-functionp-test ()
  (should (functionp 'py--guess-indent-backward)))

(ert-deftest py-ert-guess-indent-offset-functionp-test ()
  (should (functionp 'py-guess-indent-offset)))

(ert-deftest py-ert--comment-indent-function-functionp-test ()
  (should (functionp 'py--comment-indent-function)))

(ert-deftest py-ert-backward-paragraph-functionp-test ()
  (should (functionp 'py-backward-paragraph)))

(ert-deftest py-ert-end-of-paragraph-functionp-test ()
  (should (functionp 'py-forward-paragraph)))

(ert-deftest py-ert-indent-and-forward-functionp-test ()
  (should (functionp 'py-indent-and-forward)))

(ert-deftest py-ert-indent-region-functionp-test ()
  (should (functionp 'py-indent-region)))

(ert-deftest py-ert--beginning-of-buffer-position-functionp-test ()
  (should (functionp 'py--beginning-of-buffer-position)))

(ert-deftest py-ert-backward-declarations-functionp-test ()
  (should (functionp 'py-backward-declarations)))

(ert-deftest py-ert-end-of-declarations-functionp-test ()
  (should (functionp 'py-forward-declarations)))

(ert-deftest py-ert-declarations-functionp-test ()
  (should (functionp 'py-declarations)))

(ert-deftest py-ert-kill-declarations-functionp-test ()
  (should (functionp 'py-kill-declarations)))

(ert-deftest py-ert-backward-statements-functionp-test ()
  (should (functionp 'py-backward-statements)))

(ert-deftest py-ert-end-of-statements-functionp-test ()
  (should (functionp 'py-forward-statements)))

(ert-deftest py-ert-statements-functionp-test ()
  (should (functionp 'py-statements)))

(ert-deftest py-ert-kill-statements-functionp-test ()
  (should (functionp 'py-kill-statements)))

(ert-deftest py-ert--join-words-wrapping-functionp-test ()
  (should (functionp 'py--join-words-wrapping)))

(ert-deftest py-ert-insert-super-functionp-test ()
  (should (functionp 'py-insert-super)))

(ert-deftest py-ert-comment-region-functionp-test ()
  (should (functionp 'py-comment-region)))

(ert-deftest py-ert-delete-comments-in-def-or-class-functionp-test ()
  (should (functionp 'py-delete-comments-in-def-or-class)))

(ert-deftest py-ert-delete-comments-in-class-functionp-test ()
  (should (functionp 'py-delete-comments-in-class)))

(ert-deftest py-ert-delete-comments-in-block-functionp-test ()
  (should (functionp 'py-delete-comments-in-block)))

(ert-deftest py-ert-delete-comments-in-region-functionp-test ()
  (should (functionp 'py-delete-comments-in-region)))

(ert-deftest py-ert--delete-comments-intern-functionp-test ()
  (should (functionp 'py--delete-comments-intern)))

(ert-deftest py-ert-update-gud-pdb-history-functionp-test ()
  (should (functionp 'py-update-gud-pdb-history)))

(ert-deftest py-ert--pdbtrack-overlay-arrow-functionp-test ()
  (should (functionp 'py--pdbtrack-overlay-arrow)))

(ert-deftest py-ert--pdbtrack-track-stack-file-functionp-test ()
  (should (functionp 'py--pdbtrack-track-stack-file)))

(ert-deftest py-ert--pdbtrack-map-filename-functionp-test ()
  (should (functionp 'py--pdbtrack-map-filename)))

(ert-deftest py-ert--pdbtrack-get-source-buffer-functionp-test ()
  (should (functionp 'py--pdbtrack-get-source-buffer)))

(ert-deftest py-ert--pdbtrack-grub-for-buffer-functionp-test ()
  (should (functionp 'py--pdbtrack-grub-for-buffer)))

(ert-deftest py-ert-pdbtrack-toggle-stack-tracking-functionp-test ()
  (should (functionp 'py-pdbtrack-toggle-stack-tracking)))

(ert-deftest py-ert-turn-on-pdbtrack-functionp-test ()
  (should (functionp 'turn-on-pdbtrack)))

(ert-deftest py-ert-turn-off-pdbtrack-functionp-test ()
  (should (functionp 'turn-off-pdbtrack)))

(ert-deftest py-ert-execute-statement-pdb-functionp-test ()
  (should (functionp 'py-execute-statement-pdb)))

(ert-deftest py-ert-execute-region-pdb-functionp-test ()
  (should (functionp 'py-execute-region-pdb)))

(ert-deftest py-ert-pdb-execute-statement-functionp-test ()
  (should (functionp 'py-pdb-execute-statement)))

(ert-deftest py-ert-pdb-help-functionp-test ()
  (should (functionp 'py-pdb-help)))

;; (ert-deftest py-ert-pdb-break-functionp-test ()
;;   (should (functionp 'py-pdb-break)))

(ert-deftest py-ert-end-of-block-functionp-test ()
  (should (functionp 'py-forward-block)))

(ert-deftest py-ert-end-of-block-bol-functionp-test ()
  (should (functionp 'py-forward-block-bol)))

(ert-deftest py-ert-end-of-clause-functionp-test ()
  (should (functionp 'py-forward-clause)))

(ert-deftest py-ert-end-of-clause-bol-functionp-test ()
  (should (functionp 'py-forward-clause-bol)))

(ert-deftest py-ert-end-of-block-or-clause-functionp-test ()
  (should (functionp 'py-forward-block-or-clause)))

(ert-deftest py-ert-end-of-block-or-clause-bol-functionp-test ()
  (should (functionp 'py-forward-block-or-clause-bol)))

(ert-deftest py-ert-end-of-def-functionp-test ()
  (should (functionp 'py-forward-def)))

(ert-deftest py-ert-end-of-def-bol-functionp-test ()
  (should (functionp 'py-forward-def-bol)))

(ert-deftest py-ert-end-of-class-functionp-test ()
  (should (functionp 'py-forward-class)))

(ert-deftest py-ert-end-of-class-bol-functionp-test ()
  (should (functionp 'py-forward-class-bol)))

(ert-deftest py-ert-end-of-def-or-class-functionp-test ()
  (should (functionp 'py-forward-def-or-class)))

(ert-deftest py-ert-end-of-def-or-class-bol-functionp-test ()
  (should (functionp 'py-forward-def-or-class-bol)))

(ert-deftest py-ert-end-of-if-block-functionp-test ()
  (should (functionp 'py-forward-if-block)))

(ert-deftest py-ert-end-of-if-block-bol-functionp-test ()
  (should (functionp 'py-forward-if-block-bol)))

(ert-deftest py-ert-end-of-try-block-functionp-test ()
  (should (functionp 'py-forward-try-block)))

(ert-deftest py-ert-end-of-try-block-bol-functionp-test ()
  (should (functionp 'py-forward-try-block-bol)))

(ert-deftest py-ert-end-of-minor-block-functionp-test ()
  (should (functionp 'py-forward-minor-block)))

(ert-deftest py-ert-end-of-minor-block-bol-functionp-test ()
  (should (functionp 'py-forward-minor-block-bol)))

(ert-deftest py-ert-end-of-for-block-functionp-test ()
  (should (functionp 'py-forward-for-block)))

(ert-deftest py-ert-end-of-for-block-bol-functionp-test ()
  (should (functionp 'py-forward-for-block-bol)))

(ert-deftest py-ert-end-of-except-block-functionp-test ()
  (should (functionp 'py-forward-except-block)))

(ert-deftest py-ert-end-of-except-block-bol-functionp-test ()
  (should (functionp 'py-forward-except-block-bol)))

(ert-deftest py-ert-execute-statement-functionp-test ()
  (should (functionp 'py-execute-statement)))

(ert-deftest py-ert-execute-block-functionp-test ()
  (should (functionp 'py-execute-block)))

(ert-deftest py-ert-execute-block-or-clause-functionp-test ()
  (should (functionp 'py-execute-block-or-clause)))

(ert-deftest py-ert-execute-def-functionp-test ()
  (should (functionp 'py-execute-def)))

(ert-deftest py-ert-execute-class-functionp-test ()
  (should (functionp 'py-execute-class)))

(ert-deftest py-ert-execute-def-or-class-functionp-test ()
  (should (functionp 'py-execute-def-or-class)))

(ert-deftest py-ert-execute-expression-functionp-test ()
  (should (functionp 'py-execute-expression)))

(ert-deftest py-ert-execute-partial-expression-functionp-test ()
  (should (functionp 'py-execute-partial-expression)))

(ert-deftest py-ert-execute-top-level-functionp-test ()
  (should (functionp 'py-execute-top-level)))

(ert-deftest py-ert-execute-clause-functionp-test ()
  (should (functionp 'py-execute-clause)))

(ert-deftest py-ert--end-of-buffer-position-functionp-test ()
  (should (functionp 'py--end-of-buffer-position)))

(ert-deftest py-ert-toggle-smart-indentation-functionp-test ()
  (should (functionp 'py-toggle-smart-indentation)))

(ert-deftest py-ert-smart-indentation-on-functionp-test ()
  (should (functionp 'py-smart-indentation-on)))

(ert-deftest py-ert-smart-indentation-off-functionp-test ()
  (should (functionp 'py-smart-indentation-off)))

(ert-deftest py-ert-toggle-sexp-function-functionp-test ()
  (should (functionp 'py-toggle-sexp-function)))

(ert-deftest py-ert-toggle-autopair-mode-functionp-test ()
  (should (functionp 'py-toggle-autopair-mode)))

(ert-deftest py-ert-autopair-mode-on-functionp-test ()
  (should (functionp 'py-autopair-mode-on)))

(ert-deftest py-ert-autopair-mode-off-functionp-test ()
  (should (functionp 'py-autopair-mode-off)))

(ert-deftest py-ert-toggle-py-smart-operator-mode-p-functionp-test ()
  (should (functionp 'toggle-py-smart-operator-mode-p)))

(ert-deftest py-ert-smart-operator-mode-p-on-functionp-test ()
  (should (functionp 'py-smart-operator-mode-p-on)))

(ert-deftest py-ert-smart-operator-mode-p-off-functionp-test ()
  (should (functionp 'py-smart-operator-mode-p-off)))

(ert-deftest py-ert-toggle-py-switch-buffers-on-execute-p-functionp-test ()
  (should (functionp 'toggle-py-switch-buffers-on-execute-p)))

(ert-deftest py-ert-switch-buffers-on-execute-p-on-functionp-test ()
  (should (functionp 'py-switch-buffers-on-execute-p-on)))

(ert-deftest py-ert-switch-buffers-on-execute-p-off-functionp-test ()
  (should (functionp 'py-switch-buffers-on-execute-p-off)))

(ert-deftest py-ert-toggle-py-split-window-on-execute-functionp-test ()
  (should (functionp 'toggle-py-split-window-on-execute)))

(ert-deftest py-ert-split-window-on-execute-on-functionp-test ()
  (should (functionp 'py-split-window-on-execute-on)))

(ert-deftest py-ert-split-window-on-execute-off-functionp-test ()
  (should (functionp 'py-split-window-on-execute-off)))

(ert-deftest py-ert-toggle-py-fontify-shell-buffer-p-functionp-test ()
  (should (functionp 'toggle-py-fontify-shell-buffer-p)))

(ert-deftest py-ert-fontify-shell-buffer-p-on-functionp-test ()
  (should (functionp 'py-fontify-shell-buffer-p-on)))

(ert-deftest py-ert-fontify-shell-buffer-p-off-functionp-test ()
  (should (functionp 'py-fontify-shell-buffer-p-off)))

(ert-deftest py-ert-toggle-python-mode-v5-behavior-p-functionp-test ()
  (should (functionp 'toggle-python-mode-v5-behavior-p)))

(ert-deftest py-ert-python-mode-v5-behavior-p-on-functionp-test ()
  (should (functionp 'python-mode-v5-behavior-p-on)))

(ert-deftest py-ert-python-mode-v5-behavior-p-off-functionp-test ()
  (should (functionp 'python-mode-v5-behavior-p-off)))

(ert-deftest py-ert-toggle-py-jump-on-exception-functionp-test ()
  (should (functionp 'toggle-py-jump-on-exception)))

(ert-deftest py-ert-jump-on-exception-on-functionp-test ()
  (should (functionp 'py-jump-on-exception-on)))

(ert-deftest py-ert-jump-on-exception-off-functionp-test ()
  (should (functionp 'py-jump-on-exception-off)))

(ert-deftest py-ert-toggle-py-use-current-dir-when-execute-p-functionp-test ()
  (should (functionp 'toggle-py-use-current-dir-when-execute-p)))

(ert-deftest py-ert-use-current-dir-when-execute-p-on-functionp-test ()
  (should (functionp 'py-use-current-dir-when-execute-p-on)))

(ert-deftest py-ert-use-current-dir-when-execute-p-off-functionp-test ()
  (should (functionp 'py-use-current-dir-when-execute-p-off)))

(ert-deftest py-ert-toggle-py-electric-comment-p-functionp-test ()
  (should (functionp 'toggle-py-electric-comment-p)))

(ert-deftest py-ert-electric-comment-p-on-functionp-test ()
  (should (functionp 'py-electric-comment-p-on)))

(ert-deftest py-ert-electric-comment-p-off-functionp-test ()
  (should (functionp 'py-electric-comment-p-off)))

(ert-deftest py-ert-toggle-py-underscore-word-syntax-p-functionp-test ()
  (should (functionp 'toggle-py-underscore-word-syntax-p)))

(ert-deftest py-ert-underscore-word-syntax-p-on-functionp-test ()
  (should (functionp 'py-underscore-word-syntax-p-on)))

(ert-deftest py-ert-underscore-word-syntax-p-off-functionp-test ()
  (should (functionp 'py-underscore-word-syntax-p-off)))

(ert-deftest py-ert-backward-block-functionp-test ()
  (should (functionp 'py-backward-block)))

(ert-deftest py-ert-backward-clause-functionp-test ()
  (should (functionp 'py-backward-clause)))

(ert-deftest py-ert-beginning-of-block-or-clause-functionp-test ()
  (should (functionp 'py-backward-block-or-clause)))

(ert-deftest py-ert-backward-def-functionp-test ()
  (should (functionp 'py-backward-def)))

(ert-deftest py-ert-backward-class-functionp-test ()
  (should (functionp 'py-backward-class)))

(ert-deftest py-ert-beginning-of-def-or-class-functionp-test ()
  (should (functionp 'py-backward-def-or-class)))

(ert-deftest py-ert-beginning-of-if-block-functionp-test ()
  (should (functionp 'py-backward-if-block)))

(ert-deftest py-ert-beginning-of-try-block-functionp-test ()
  (should (functionp 'py-backward-try-block)))

(ert-deftest py-ert-beginning-of-minor-block-functionp-test ()
  (should (functionp 'py-backward-minor-block)))

(ert-deftest py-ert-beginning-of-for-block-functionp-test ()
  (should (functionp 'py-backward-for-block)))

(ert-deftest py-ert-beginning-of-except-block-functionp-test ()
  (should (functionp 'py-backward-except-block)))

(ert-deftest py-ert-backward-block-bol-functionp-test ()
  (should (functionp 'py-backward-block-bol)))

(ert-deftest py-ert-backward-clause-bol-functionp-test ()
  (should (functionp 'py-backward-clause-bol)))

(ert-deftest py-ert-backward-block-or-clause-bol-functionp-test ()
  (should (functionp 'py-backward-block-or-clause-bol)))

(ert-deftest py-ert-backward-def-bol-functionp-test ()
  (should (functionp 'py-backward-def-bol)))

(ert-deftest py-ert-backward-class-bol-functionp-test ()
  (should (functionp 'py-backward-class-bol)))

(ert-deftest py-ert-backward-def-or-class-bol-functionp-test ()
  (should (functionp 'py-backward-def-or-class-bol)))

(ert-deftest py-ert-backward-if-block-bol-functionp-test ()
  (should (functionp 'py-backward-if-block-bol)))

(ert-deftest py-ert-backward-try-block-bol-functionp-test ()
  (should (functionp 'py-backward-try-block-bol)))

(ert-deftest py-ert-backward-minor-block-bol-functionp-test ()
  (should (functionp 'py-backward-minor-block-bol)))

(ert-deftest py-ert-backward-for-block-bol-functionp-test ()
  (should (functionp 'py-backward-for-block-bol)))

(ert-deftest py-ert-backward-except-block-bol-functionp-test ()
  (should (functionp 'py-backward-except-block-bol)))

(ert-deftest py-ert-comment-auto-fill-functionp-test ()
  (should (functionp 'py-comment-auto-fill)))

(ert-deftest py-ert-comment-auto-fill-on-functionp-test ()
  (should (functionp 'py-comment-auto-fill-on)))

(ert-deftest py-ert-comment-auto-fill-off-functionp-test ()
  (should (functionp 'py-comment-auto-fill-off)))

(ert-deftest py-ert-backward-elif-block-functionp-test ()
  (should (functionp 'py-backward-elif-block)))

(ert-deftest py-ert-backward-else-block-functionp-test ()
  (should (functionp 'py-backward-else-block)))

(ert-deftest py-ert-backward-elif-block-bol-functionp-test ()
  (should (functionp 'py-backward-elif-block-bol)))

(ert-deftest py-ert-backward-else-block-bol-functionp-test ()
  (should (functionp 'py-backward-else-block-bol)))

(ert-deftest py-ert-indent-forward-line-functionp-test ()
  (should (functionp 'py-indent-forward-line)))

(ert-deftest py-ert-dedent-forward-line-functionp-test ()
  (should (functionp 'py-dedent-forward-line)))

(ert-deftest py-ert-dedent-functionp-test ()
  (should (functionp 'py-dedent)))

(ert-deftest py-ert--close-intern-functionp-test ()
  (should (functionp 'py--close-intern)))

(ert-deftest py-ert-close-def-functionp-test ()
  (should (functionp 'py-close-def)))

(ert-deftest py-ert-close-class-functionp-test ()
  (should (functionp 'py-close-class)))

(ert-deftest py-ert-close-block-functionp-test ()
  (should (functionp 'py-close-block)))

(ert-deftest py-ert-class-at-point-functionp-test ()
  (should (functionp 'py-class-at-point)))

(ert-deftest py-ert-py-match-paren-mode-functionp-test ()
  (should (functionp 'py-match-paren-mode)))

(ert-deftest py-ert-py-match-paren-functionp-test ()
  (should (functionp 'py-match-paren)))

(ert-deftest py-ert-eva-functionp-test ()
  (should (functionp 'eva)))

(ert-deftest py-ert-pst-here-functionp-test ()
  (should (functionp 'pst-here)))

(ert-deftest py-ert-printform-insert-functionp-test ()
  (should (functionp 'py-printform-insert)))

(ert-deftest py-ert-line-to-printform-python2-functionp-test ()
  (should (functionp 'py-line-to-printform-python2)))

(ert-deftest py-ert-boolswitch-functionp-test ()
  (should (functionp 'py-boolswitch)))

(ert-deftest py-ert-end-of-elif-block-functionp-test ()
  (should (functionp 'py-forward-elif-block)))

(ert-deftest py-ert-end-of-elif-block-bol-functionp-test ()
  (should (functionp 'py-forward-elif-block-bol)))

(ert-deftest py-ert-end-of-else-block-functionp-test ()
  (should (functionp 'py-forward-else-block)))

(ert-deftest py-ert-end-of-else-block-bol-functionp-test ()
  (should (functionp 'py-forward-else-block-bol)))

(ert-deftest py-ert-mark-paragraph-functionp-test ()
  (should (functionp 'py-mark-paragraph)))

(ert-deftest py-ert-mark-block-functionp-test ()
  (should (functionp 'py-mark-block)))

(ert-deftest py-ert-mark-minor-block-functionp-test ()
  (should (functionp 'py-mark-minor-block)))

(ert-deftest py-ert-mark-clause-functionp-test ()
  (should (functionp 'py-mark-clause)))

(ert-deftest py-ert-mark-block-or-clause-functionp-test ()
  (should (functionp 'py-mark-block-or-clause)))

(ert-deftest py-ert-mark-def-functionp-test ()
  (should (functionp 'py-mark-def)))

(ert-deftest py-ert-mark-class-functionp-test ()
  (should (functionp 'py-mark-class)))

(ert-deftest py-ert-mark-def-or-class-functionp-test ()
  (should (functionp 'py-mark-def-or-class)))

(ert-deftest py-ert-mark-line-functionp-test ()
  (should (functionp 'py-mark-line)))

(ert-deftest py-ert-mark-statement-functionp-test ()
  (should (functionp 'py-mark-statement)))

(ert-deftest py-ert-mark-comment-functionp-test ()
  (should (functionp 'py-mark-comment)))

(ert-deftest py-ert-mark-top-level-functionp-test ()
  (should (functionp 'py-mark-top-level)))

(ert-deftest py-ert-mark-partial-expression-functionp-test ()
  (should (functionp 'py-mark-partial-expression)))

(ert-deftest py-ert-mark-expression-functionp-test ()
  (should (functionp 'py-mark-expression)))

(ert-deftest py-ert--kill-emacs-hook-functionp-test ()
  (should (functionp 'py--kill-emacs-hook)))

(ert-deftest py-ert-python-version-functionp-test ()
  (should (functionp 'py-python-version)))

(ert-deftest py-ert-version-functionp-test ()
  (should (functionp 'py-version)))

(ert-deftest py-ert-history-input-filter-functionp-test ()
  (should (functionp 'py-history-input-filter)))

(ert-deftest py-ert-load-file-functionp-test ()
  (should (functionp 'py-load-file)))

(ert-deftest py-ert-proc-functionp-test ()
  (should (functionp 'py-proc)))

(ert-deftest py-ert--shell-simple-send-functionp-test ()
  (should (functionp 'py--shell-simple-send)))

(ert-deftest py-ert-guess-pdb-path-functionp-test ()
  (should (functionp 'py-guess-pdb-path)))

(ert-deftest py-ert-switch-shell-functionp-test ()
  (should (functionp 'py-switch-shell)))

(ert-deftest py-ert-toggle-local-default-use-functionp-test ()
  (should (functionp 'py-toggle-local-default-use)))

(ert-deftest py-ert--input-filter-functionp-test ()
  (should (functionp 'py--input-filter)))

(ert-deftest py-ert--set-auto-fill-values-functionp-test ()
  (should (functionp 'py--set-auto-fill-values)))

(ert-deftest py-ert--run-auto-fill-timer-functionp-test ()
  (should (functionp 'py--run-auto-fill-timer)))

(ert-deftest py-ert-complete-auto-functionp-test ()
  (should (functionp 'py-complete-auto)))

(ert-deftest py-ert-set-command-args-functionp-test ()
  (should (functionp 'py-set-command-args)))

(ert-deftest py-ert---emacs-version-greater-23-functionp-test ()
  (should (functionp 'py---emacs-version-greater-23)))

(ert-deftest py-ert--empty-arglist-indent-functionp-test ()
  (should (functionp 'py--empty-arglist-indent)))

(ert-deftest py-ert-symbol-at-point-functionp-test ()
  (should (functionp 'py-symbol-at-point)))

(ert-deftest py-ert-kill-buffer-unconditional-functionp-test ()
  (should (functionp 'py-kill-buffer-unconditional)))

(ert-deftest py-ert--line-backward-maybe-functionp-test ()
  (should (functionp 'py--line-backward-maybe)))

(ert-deftest py-ert--after-empty-line-functionp-test ()
  (should (functionp 'py--after-empty-line)))

(ert-deftest py-ert-compute-indentation-functionp-test ()
  (should (functionp 'py-compute-indentation)))

(ert-deftest py-ert--fetch-previous-indent-functionp-test ()
  (should (functionp 'py--fetch-previous-indent)))

(ert-deftest py-ert-continuation-offset-functionp-test ()
  (should (functionp 'py-continuation-offset)))

(ert-deftest py-ert-indentation-of-statement-functionp-test ()
  (should (functionp 'py-indentation-of-statement)))

(ert-deftest py-ert-list-beginning-position-functionp-test ()
  (should (functionp 'py-list-beginning-position)))

(ert-deftest py-ert-end-of-list-position-functionp-test ()
  (should (functionp 'py-end-of-list-position)))

(ert-deftest py-ert--in-comment-p-functionp-test ()
  (should (functionp 'py--in-comment-p)))

(ert-deftest py-ert-in-triplequoted-string-p-functionp-test ()
  (should (functionp 'py-in-triplequoted-string-p)))

(ert-deftest py-ert-in-string-p-functionp-test ()
  (should (functionp 'py-in-string-p)))

(ert-deftest py-ert-in-statement-p-functionp-test ()
  (should (functionp 'py-in-statement-p)))

(ert-deftest py-ert-beginning-of-top-level-p-functionp-test ()
  (should (functionp 'py-backward-top-level-p)))

(ert-deftest py-ert--beginning-of-line-p-functionp-test ()
  (should (functionp 'py--beginning-of-line-p)))

(ert-deftest py-ert--beginning-of-buffer-p-functionp-test ()
  (should (functionp 'py--beginning-of-buffer-p)))

(ert-deftest py-ert--beginning-of-paragraph-p-functionp-test ()
  (should (functionp 'py--beginning-of-paragraph-p)))

(ert-deftest py-ert--end-of-line-p-functionp-test ()
  (should (functionp 'py--end-of-line-p)))

(ert-deftest py-ert--end-of-paragraph-p-functionp-test ()
  (should (functionp 'py--end-of-paragraph-p)))

(ert-deftest py-ert--statement-opens-block-p-functionp-test ()
  (should (functionp 'py--statement-opens-block-p)))

(ert-deftest py-ert--statement-opens-base-functionp-test ()
  (should (functionp 'py--statement-opens-base)))

(ert-deftest py-ert--statement-opens-clause-p-functionp-test ()
  (should (functionp 'py--statement-opens-clause-p)))

(ert-deftest py-ert--statement-opens-block-or-clause-p-functionp-test ()
  (should (functionp 'py--statement-opens-block-or-clause-p)))

(ert-deftest py-ert--statement-opens-class-p-functionp-test ()
  (should (functionp 'py--statement-opens-class-p)))

(ert-deftest py-ert--statement-opens-def-p-functionp-test ()
  (should (functionp 'py--statement-opens-def-p)))

(ert-deftest py-ert--statement-opens-def-or-class-p-functionp-test ()
  (should (functionp 'py--statement-opens-def-or-class-p)))

(ert-deftest py-ert--record-list-error-functionp-test ()
  (should (functionp 'py--record-list-error)))

(ert-deftest py-ert--message-error-functionp-test ()
  (should (functionp 'py--message-error)))

(ert-deftest py-ert--end-base-functionp-test ()
  (should (functionp 'py--end-base)))

(ert-deftest py-ert--look-downward-for-beginning-functionp-test ()
  (should (functionp 'py--look-downward-for-beginning)))

(ert-deftest py-ert-look-downward-for-clause-functionp-test ()
  (should (functionp 'py-look-downward-for-clause)))

(ert-deftest py-ert-current-defun-functionp-test ()
  (should (functionp 'py-current-defun)))

(ert-deftest py-ert-sort-imports-functionp-test ()
  (should (functionp 'py-sort-imports)))

(ert-deftest py-ert--in-literal-functionp-test ()
  (should (functionp 'py--in-literal)))

(ert-deftest py-ert-count-lines-functionp-test ()
  (should (functionp 'py-count-lines)))

(ert-deftest py-ert--point-functionp-test ()
  (should (functionp 'py--point)))

(ert-deftest py-ert-install-search-local-functionp-test ()
  (should (functionp 'py-install-search-local)))

(ert-deftest py-ert-install-local-shells-functionp-test ()
  (should (functionp 'py-install-local-shells)))

(ert-deftest py-ert--until-found-functionp-test ()
  (should (functionp 'py--until-found)))

(ert-deftest py-ert--delay-process-dependent-functionp-test ()
  (should (functionp 'py--delay-process-dependent)))

(ert-deftest py-ert--send-string-no-output-functionp-test ()
  (should (functionp 'py--send-string-no-output)))

(ert-deftest py-ert--send-string-return-output-functionp-test ()
  (should (functionp 'py--send-string-return-output)))

(ert-deftest py-ert-which-def-or-class-functionp-test ()
  (should (functionp 'py-which-def-or-class)))

(ert-deftest py-ert--beginning-of-form-intern-functionp-test ()
  (should (functionp 'py--beginning-of-form-intern)))

(ert-deftest py-ert--backward-prepare-functionp-test ()
  (should (functionp 'py--backward-prepare)))

(ert-deftest py-ert--fetch-first-python-buffer-functionp-test ()
  (should (functionp 'py--fetch-first-python-buffer)))

(ert-deftest py-ert-unload-python-el-functionp-test ()
  (should (functionp 'py-unload-python-el)))

(ert-deftest py-ert--skip-to-semicolon-backward-functionp-test ()
  (should (functionp 'py--skip-to-semicolon-backward)))

(ert-deftest py-ert--end-of-comment-intern-functionp-test ()
  (should (functionp 'py--end-of-comment-intern)))

(ert-deftest py-ert--skip-to-comment-or-semicolon-functionp-test ()
  (should (functionp 'py--skip-to-comment-or-semicolon)))

(ert-deftest py-ert-backward-top-level-functionp-test ()
  (should (functionp 'py-backward-top-level)))

(ert-deftest py-ert-end-of-top-level-functionp-test ()
  (should (functionp 'py-forward-top-level)))

(ert-deftest py-ert-end-of-top-level-bol-functionp-test ()
  (should (functionp 'py-forward-top-level-bol)))

(ert-deftest py-ert--beginning-of-line-form-functionp-test ()
  (should (functionp 'py--beginning-of-line-form)))

(ert-deftest py-ert--mark-base-functionp-test ()
  (should (functionp 'py--mark-base)))

(ert-deftest py-ert--mark-base-bol-functionp-test ()
  (should (functionp 'py--mark-base-bol)))

(ert-deftest py-ert-mark-base-functionp-test ()
  (should (functionp 'py-mark-base)))

(ert-deftest py-ert-beginning-functionp-test ()
  (should (functionp 'py-beginning)))

(ert-deftest py-ert-end-functionp-test ()
  (should (functionp 'py-end)))

(ert-deftest py-ert-beginning-of-buffer-functionp-test ()
  (should (functionp 'py-beginning-of-buffer)))

(ert-deftest py-ert-end-of-buffer-functionp-test ()
  (should (functionp 'py-end-of-buffer)))

(ert-deftest py-ert-backward-same-level-functionp-test ()
  (should (functionp 'py-backward-same-level)))

(ert-deftest py-ert--end-of-buffer-p-functionp-test ()
  (should (functionp 'py--end-of-buffer-p)))

(ert-deftest py-ert--beginning-of-paragraph-position-functionp-test ()
  (should (functionp 'py--beginning-of-paragraph-position)))

(ert-deftest py-ert--end-of-paragraph-position-functionp-test ()
  (should (functionp 'py--end-of-paragraph-position)))

(ert-deftest py-ert--beginning-of-comment-position-functionp-test ()
  (should (functionp 'py--beginning-of-comment-position)))

(ert-deftest py-ert--end-of-comment-position-functionp-test ()
  (should (functionp 'py--end-of-comment-position)))

(ert-deftest py-ert-info-lookup-symbol-functionp-test ()
  (should (functionp 'py-info-lookup-symbol)))

(ert-deftest py-ert-python-after-info-look-functionp-test ()
  (should (functionp 'python-after-info-look)))

(ert-deftest py-ert--warn-tmp-files-left-functionp-test ()
  (should (functionp 'py--warn-tmp-files-left)))

(ert-deftest py-ert-fetch-docu-functionp-test ()
  (should (functionp 'py-fetch-docu)))

(ert-deftest py-ert-info-current-defun-functionp-test ()
  (should (functionp 'py-info-current-defun)))

(ert-deftest py-ert-help-at-point-functionp-test ()
  (should (functionp 'py-help-at-point)))

(ert-deftest py-ert--dump-help-string-functionp-test ()
  (should (functionp 'py--dump-help-string)))

(ert-deftest py-ert-describe-mode-functionp-test ()
  (should (functionp 'py-describe-mode)))

(ert-deftest py-ert-find-definition-functionp-test ()
  (should (functionp 'py-find-definition)))

(ert-deftest py-ert-find-imports-functionp-test ()
  (should (functionp 'py-find-imports)))

(ert-deftest py-ert-update-imports-functionp-test ()
  (should (functionp 'py-update-imports)))

(ert-deftest py-ert-pep8-run-functionp-test ()
  (should (functionp 'py-pep8-run)))

(ert-deftest py-ert-pep8-help-functionp-test ()
  (should (functionp 'py-pep8-help)))

(ert-deftest py-ert-pylint-run-functionp-test ()
  (should (functionp 'py-pylint-run)))

(ert-deftest py-ert-pylint-help-functionp-test ()
  (should (functionp 'py-pylint-help)))

(ert-deftest py-ert-pylint-doku-functionp-test ()
  (should (functionp 'py-pylint-doku)))

(ert-deftest py-ert-pyflakes-run-functionp-test ()
  (should (functionp 'py-pyflakes-run)))

(ert-deftest py-ert-pyflakes-help-functionp-test ()
  (should (functionp 'py-pyflakes-help)))

(ert-deftest py-ert-pyflakespep8-run-functionp-test ()
  (should (functionp 'py-pyflakespep8-run)))

(ert-deftest py-ert-pyflakespep8-help-functionp-test ()
  (should (functionp 'py-pyflakespep8-help)))

(ert-deftest py-ert-pychecker-run-functionp-test ()
  (should (functionp 'py-pychecker-run)))

(ert-deftest py-ert-check-command-functionp-test ()
  (should (functionp 'py-check-command)))

(ert-deftest py-ert-flake8-run-functionp-test ()
  (should (functionp 'py-flake8-run)))

(ert-deftest py-ert-flake8-help-functionp-test ()
  (should (functionp 'py-flake8-help)))

(ert-deftest py-ert--string-strip-functionp-test ()
  (should (functionp 'py--string-strip)))

(ert-deftest py-ert-nesting-level-functionp-test ()
  (should (functionp 'py-nesting-level)))

(ert-deftest py-ert-ffap-module-path-functionp-test ()
  (should (functionp 'py-ffap-module-path)))

(ert-deftest py-ert-toggle-flymake-intern-functionp-test ()
  (should (functionp 'py-toggle-flymake-intern)))

(ert-deftest py-ert-pylint-flymake-mode-functionp-test ()
  (should (functionp 'pylint-flymake-mode)))

(ert-deftest py-ert-pyflakes-flymake-mode-functionp-test ()
  (should (functionp 'pyflakes-flymake-mode)))

(ert-deftest py-ert-pychecker-flymake-mode-functionp-test ()
  (should (functionp 'pychecker-flymake-mode)))

(ert-deftest py-ert-pep8-flymake-mode-functionp-test ()
  (should (functionp 'pep8-flymake-mode)))

(ert-deftest py-ert-pyflakespep8-flymake-mode-functionp-test ()
  (should (functionp 'pyflakespep8-flymake-mode)))

(ert-deftest py-ert-variables-state-functionp-test ()
  (should (functionp 'variables-state)))

(ert-deftest py-ert-variables-base-state-functionp-test ()
  (should (functionp 'variables-base-state)))

(ert-deftest py-ert-smart-operator-check-functionp-test ()
  (should (functionp 'py-smart-operator-check)))

(ert-deftest py-ert-autopair-check-functionp-test ()
  (should (functionp 'py-autopair-check)))

(ert-deftest py-ert--set-ffap-form-functionp-test ()
  (should (functionp 'py--set-ffap-form)))

(ert-deftest py-ert--quote-syntax-functionp-test ()
  (should (functionp 'py--quote-syntax)))

(ert-deftest py-ert--python-send-setup-code-intern-functionp-test ()
  (should (functionp 'py--python-send-setup-code-intern)))

(ert-deftest py-ert--python-send-completion-setup-code-functionp-test ()
  (should (functionp 'py--python-send-completion-setup-code)))

(ert-deftest py-ert--python-send-ffap-setup-code-functionp-test ()
  (should (functionp 'py--python-send-ffap-setup-code)))

(ert-deftest py-ert--python-send-eldoc-setup-code-functionp-test ()
  (should (functionp 'py--python-send-eldoc-setup-code)))

(ert-deftest py-ert--ipython-import-module-completion-functionp-test ()
  (should (functionp 'py--ipython-import-module-completion)))

(ert-deftest py-ert--docstring-p-functionp-test ()
  (should (functionp 'py--docstring-p)))

(ert-deftest py-ert--font-lock-syntactic-face-function-functionp-test ()
  (should (functionp 'py--font-lock-syntactic-face-function)))

(ert-deftest py-ert-choose-shell-by-shebang-functionp-test ()
  (should (functionp 'py-choose-shell-by-shebang)))

(ert-deftest py-ert--choose-shell-by-import-functionp-test ()
  (should (functionp 'py--choose-shell-by-import)))

(ert-deftest py-ert-choose-shell-by-path-functionp-test ()
  (should (functionp 'py-choose-shell-by-path)))

(ert-deftest py-ert-which-python-functionp-test ()
  (should (functionp 'py-which-python)))

(ert-deftest py-ert-python-current-environment-functionp-test ()
  (should (functionp 'py-python-current-environment)))

(ert-deftest py-ert--cleanup-process-name-functionp-test ()
  (should (functionp 'py--cleanup-process-name)))

(ert-deftest py-ert-choose-shell-functionp-test ()
  (should (functionp 'py-choose-shell)))

(ert-deftest py-ert--normalize-directory-functionp-test ()
  (should (functionp 'py--normalize-directory)))

(ert-deftest py-ert-install-directory-check-functionp-test ()
  (should (functionp 'py-install-directory-check)))

(ert-deftest py-ert-guess-py-install-directory-functionp-test ()
  (should (functionp 'py-guess-py-install-directory)))

(ert-deftest py-ert-load-pymacs-functionp-test ()
  (should (functionp 'py-load-pymacs)))

(ert-deftest py-ert-set-load-path-functionp-test ()
  (should (functionp 'py-set-load-path)))

(ert-deftest py-ert-separator-char-functionp-test ()
  (should (functionp 'py-separator-char)))

(ert-deftest py-ert-pps-emacs-version-functionp-test ()
  (should (functionp 'pps-emacs-version)))

(ert-deftest py-ert-in-string-or-comment-p-functionp-test ()
  (should (functionp 'py-in-string-or-comment-p)))

(ert-deftest py-ert-electric-colon-functionp-test ()
  (should (functionp 'py-electric-colon)))

(ert-deftest py-ert-electric-close-functionp-test ()
  (should (functionp 'py-electric-close)))

(ert-deftest py-ert-electric-comment-functionp-test ()
  (should (functionp 'py-electric-comment)))

(ert-deftest py-ert-empty-out-list-backward-functionp-test ()
  (should (functionp 'py-empty-out-list-backward)))

(ert-deftest py-ert-electric-backspace-functionp-test ()
  (should (functionp 'py-electric-backspace)))

(ert-deftest py-ert-electric-delete-functionp-test ()
  (should (functionp 'py-electric-delete)))

(ert-deftest py-ert-electric-yank-functionp-test ()
  (should (functionp 'py-electric-yank)))

(ert-deftest py-ert-backward-comment-functionp-test ()
  (should (functionp 'py-backward-comment)))

(ert-deftest py-ert-forward-comment-functionp-test ()
  (should (functionp 'py-forward-comment)))

(ert-deftest py-ert-beginning-of-comment-functionp-test ()
  (should (functionp 'py-beginning-of-comment)))

(ert-deftest py-ert--uncomment-intern-functionp-test ()
  (should (functionp 'py--uncomment-intern)))

(ert-deftest py-ert-uncomment-functionp-test ()
  (should (functionp 'py-uncomment)))

(ert-deftest py-ert-comment-block-functionp-test ()
  (should (functionp 'py-comment-block)))

(ert-deftest py-ert-comment-minor-block-functionp-test ()
  (should (functionp 'py-comment-minor-block)))

(ert-deftest py-ert-comment-top-level-functionp-test ()
  (should (functionp 'py-comment-top-level)))

(ert-deftest py-ert-comment-clause-functionp-test ()
  (should (functionp 'py-comment-clause)))

(ert-deftest py-ert-comment-block-or-clause-functionp-test ()
  (should (functionp 'py-comment-block-or-clause)))

(ert-deftest py-ert-comment-def-functionp-test ()
  (should (functionp 'py-comment-def)))

(ert-deftest py-ert-comment-class-functionp-test ()
  (should (functionp 'py-comment-class)))

(ert-deftest py-ert-comment-def-or-class-functionp-test ()
  (should (functionp 'py-comment-def-or-class)))

(ert-deftest py-ert-comment-statement-functionp-test ()
  (should (functionp 'py-comment-statement)))

(ert-deftest py-ert-delete-statement-functionp-test ()
  (should (functionp 'py-delete-statement)))

(ert-deftest py-ert-delete-top-level-functionp-test ()
  (should (functionp 'py-delete-top-level)))

(ert-deftest py-ert-delete-block-functionp-test ()
  (should (functionp 'py-delete-block)))

(ert-deftest py-ert-delete-block-or-clause-functionp-test ()
  (should (functionp 'py-delete-block-or-clause)))

(ert-deftest py-ert-delete-def-functionp-test ()
  (should (functionp 'py-delete-def)))

(ert-deftest py-ert-delete-class-functionp-test ()
  (should (functionp 'py-delete-class)))

(ert-deftest py-ert-delete-def-or-class-functionp-test ()
  (should (functionp 'py-delete-def-or-class)))

(ert-deftest py-ert-delete-expression-functionp-test ()
  (should (functionp 'py-delete-expression)))

(ert-deftest py-ert-delete-partial-expression-functionp-test ()
  (should (functionp 'py-delete-partial-expression)))

(ert-deftest py-ert-delete-minor-block-functionp-test ()
  (should (functionp 'py-delete-minor-block)))

(ert-deftest py-ert-switch-imenu-index-function-functionp-test ()
  (should (functionp 'py-switch-imenu-index-function)))

(ert-deftest py-ert--imenu-create-index-functionp-test ()
  (should (functionp 'py--imenu-create-index)))

(ert-deftest py-ert--imenu-create-index-engine-functionp-test ()
  (should (functionp 'py--imenu-create-index-engine)))

(ert-deftest py-ert--imenu-create-index-new-functionp-test ()
  (should (functionp 'py--imenu-create-index-new)))

(ert-deftest py-ert-execute-file-python-functionp-test ()
  (should (functionp 'py-execute-file-python)))

(ert-deftest py-ert-execute-file-python-switch-functionp-test ()
  (should (functionp 'py-execute-file-python-switch)))

(ert-deftest py-ert-execute-file-python-no-switch-functionp-test ()
  (should (functionp 'py-execute-file-python-no-switch)))

(ert-deftest py-ert-execute-file-python-dedicated-functionp-test ()
  (should (functionp 'py-execute-file-python-dedicated)))

(ert-deftest py-ert-execute-file-python-dedicated-switch-functionp-test ()
  (should (functionp 'py-execute-file-python-dedicated-switch)))

(ert-deftest py-ert-execute-file-ipython-functionp-test ()
  (should (functionp 'py-execute-file-ipython)))

(ert-deftest py-ert-execute-file-ipython-switch-functionp-test ()
  (should (functionp 'py-execute-file-ipython-switch)))

(ert-deftest py-ert-execute-file-ipython-no-switch-functionp-test ()
  (should (functionp 'py-execute-file-ipython-no-switch)))

(ert-deftest py-ert-execute-file-ipython-dedicated-functionp-test ()
  (should (functionp 'py-execute-file-ipython-dedicated)))

(ert-deftest py-ert-execute-file-ipython-dedicated-switch-functionp-test ()
  (should (functionp 'py-execute-file-ipython-dedicated-switch)))

(ert-deftest py-ert-execute-file-python3-functionp-test ()
  (should (functionp 'py-execute-file-python3)))

(ert-deftest py-ert-execute-file-python3-switch-functionp-test ()
  (should (functionp 'py-execute-file-python3-switch)))

(ert-deftest py-ert-execute-file-python3-no-switch-functionp-test ()
  (should (functionp 'py-execute-file-python3-no-switch)))

(ert-deftest py-ert-execute-file-python3-dedicated-functionp-test ()
  (should (functionp 'py-execute-file-python3-dedicated)))

(ert-deftest py-ert-execute-file-python3-dedicated-switch-functionp-test ()
  (should (functionp 'py-execute-file-python3-dedicated-switch)))

(ert-deftest py-ert-execute-file-python2-functionp-test ()
  (should (functionp 'py-execute-file-python2)))

(ert-deftest py-ert-execute-file-python2-switch-functionp-test ()
  (should (functionp 'py-execute-file-python2-switch)))

(ert-deftest py-ert-execute-file-python2-no-switch-functionp-test ()
  (should (functionp 'py-execute-file-python2-no-switch)))

(ert-deftest py-ert-execute-file-python2-dedicated-functionp-test ()
  (should (functionp 'py-execute-file-python2-dedicated)))

(ert-deftest py-ert-execute-file-python2-dedicated-switch-functionp-test ()
  (should (functionp 'py-execute-file-python2-dedicated-switch)))

(ert-deftest py-ert-execute-file-jython-functionp-test ()
  (should (functionp 'py-execute-file-jython)))

(ert-deftest py-ert-execute-file-jython-switch-functionp-test ()
  (should (functionp 'py-execute-file-jython-switch)))

(ert-deftest py-ert-execute-file-jython-no-switch-functionp-test ()
  (should (functionp 'py-execute-file-jython-no-switch)))

(ert-deftest py-ert-execute-file-jython-dedicated-functionp-test ()
  (should (functionp 'py-execute-file-jython-dedicated)))

(ert-deftest py-ert-execute-file-jython-dedicated-switch-functionp-test ()
  (should (functionp 'py-execute-file-jython-dedicated-switch)))

(ert-deftest py-ert--shell-completion-get-completions-functionp-test ()
  (should (functionp 'py--shell-completion-get-completions)))

(ert-deftest py-ert--after-change-function-functionp-test ()
  (should (functionp 'py--after-change-function)))

(ert-deftest py-ert--try-completion-intern-functionp-test ()
  (should (functionp 'py--try-completion-intern)))

(ert-deftest py-ert--try-completion-functionp-test ()
  (should (functionp 'py--try-completion)))

(ert-deftest py--shell-do-completion-at-point-functionp-test ()
  (should (functionp 'py--shell-do-completion-at-point)))

(ert-deftest py--shell-insert-completion-maybe-functionp-test ()
  (should (functionp 'py--shell-insert-completion-maybe)))

(ert-deftest py-ert--complete-base-functionp-test ()
  (should (functionp 'py--complete-base)))

(ert-deftest py-ert--complete-prepare-functionp-test ()
  (should (functionp 'py--complete-prepare)))

(ert-deftest py-ert-shell-complete-functionp-test ()
  (should (functionp 'py-shell-complete)))

(ert-deftest py-ert-indent-or-complete-functionp-test ()
  (should (functionp 'py-indent-or-complete)))

(ert-deftest py-ert-shift-left-functionp-test ()
  (should (functionp 'py-shift-left)))

(ert-deftest py-ert-shift-right-functionp-test ()
  (should (functionp 'py-shift-right)))

(ert-deftest py-ert--shift-intern-functionp-test ()
  (should (functionp 'py--shift-intern)))

(ert-deftest py-ert--shift-forms-base-functionp-test ()
  (should (functionp 'py--shift-forms-base)))

(ert-deftest py-ert-shift-paragraph-right-functionp-test ()
  (should (functionp 'py-shift-paragraph-right)))

(ert-deftest py-ert-shift-paragraph-left-functionp-test ()
  (should (functionp 'py-shift-paragraph-left)))

(ert-deftest py-ert-shift-block-right-functionp-test ()
  (should (functionp 'py-shift-block-right)))

(ert-deftest py-ert-shift-block-left-functionp-test ()
  (should (functionp 'py-shift-block-left)))

(ert-deftest py-ert-shift-minor-block-left-functionp-test ()
  (should (functionp 'py-shift-minor-block-left)))

(ert-deftest py-ert-shift-minor-block-right-functionp-test ()
  (should (functionp 'py-shift-minor-block-right)))

(ert-deftest py-ert-shift-clause-right-functionp-test ()
  (should (functionp 'py-shift-clause-right)))

(ert-deftest py-ert-shift-clause-left-functionp-test ()
  (should (functionp 'py-shift-clause-left)))

(ert-deftest py-ert-shift-block-or-clause-right-functionp-test ()
  (should (functionp 'py-shift-block-or-clause-right)))

(ert-deftest py-ert-shift-block-or-clause-left-functionp-test ()
  (should (functionp 'py-shift-block-or-clause-left)))

(ert-deftest py-ert-shift-def-right-functionp-test ()
  (should (functionp 'py-shift-def-right)))

(ert-deftest py-ert-shift-def-left-functionp-test ()
  (should (functionp 'py-shift-def-left)))

(ert-deftest py-ert-shift-class-right-functionp-test ()
  (should (functionp 'py-shift-class-right)))

(ert-deftest py-ert-shift-class-left-functionp-test ()
  (should (functionp 'py-shift-class-left)))

(ert-deftest py-ert-shift-def-or-class-right-functionp-test ()
  (should (functionp 'py-shift-def-or-class-right)))

(ert-deftest py-ert-shift-def-or-class-left-functionp-test ()
  (should (functionp 'py-shift-def-or-class-left)))

(ert-deftest py-ert-shift-statement-right-functionp-test ()
  (should (functionp 'py-shift-statement-right)))

(ert-deftest py-ert-shift-statement-left-functionp-test ()
  (should (functionp 'py-shift-statement-left)))

(ert-deftest py-ert-end-of-block-functionp-test ()
  (should (functionp 'py-forward-block)))

(ert-deftest py-ert-end-of-clause-functionp-test ()
  (should (functionp 'py-forward-clause)))

(ert-deftest py-ert-end-of-block-or-clause-functionp-test ()
  (should (functionp 'py-forward-block-or-clause)))

(ert-deftest py-ert-end-of-def-functionp-test ()
  (should (functionp 'py-forward-def)))

(ert-deftest py-ert-end-of-class-functionp-test ()
  (should (functionp 'py-forward-class)))

(provide 'py-ert-function-tests)
;;; py-ert-function-tests.el ends here
