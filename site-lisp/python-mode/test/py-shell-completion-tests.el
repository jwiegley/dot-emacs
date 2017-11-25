;;; py-shell-completion-tests.el --- Test completion for available Python shell

;; Author: Andreas Röhler <andreas.roehler@online.de>
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

(defun python-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    ;; (set-buffer (py-shell nil t "python" nil "/"))
    (with-temp-buffer (py-shell nil t "python")
    (sit-for 0.1 t) 
    (when (interactive-p) (switch-to-buffer (current-buffer)))
    ;; (goto-char (point-max))
    (sit-for 0.1 t)
    (goto-char (or (and (boundp 'comint-last-prompt)(cdr comint-last-prompt)) (point-max)))
    (sit-for 0.2 t)
    ;; (goto-char (point-max))
    (insert "pri")
    (py-shell-complete)
    (sit-for 0.2 t)
    (assert (member (char-before) (list ?\( ?t)) nil "python-shell-complete-test failed"))))

(defun python2.7-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (set-buffer (py-shell nil t "python2.7"))
    (when (interactive-p) (switch-to-buffer (current-buffer)))
    (sit-for 0.1)
    (goto-char (point-max))
    (insert "pri")
    (py-shell-complete)
    (forward-word -1)
    (assert (looking-at "print") nil "python2.7-shell-complete-test failed")
    (message "%s" "python2.7-shell-complete-test passed")))


(defun arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (set-buffer (py-shell nil t "~/arbeit/python/epdfree/epd_free-7.2-2-rh5-x86/bin/python2.7"))
    (sit-for 0.2 t)
    (goto-char (point-max))
    (insert "pri")
    (py-shell-complete)
    (sit-for 0.1)
    (forward-word -1)
    (assert (looking-at "print") nil "arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-shell-complete-test failed")
    (when py-verbose-p (message "%s" "arbeit-python-epdfree-epd_free-7.2-2-rh5-x86-bin-python2.7-shell-complete-test passed"))))

(defun python3-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (set-buffer (py-shell nil t "python3"))
    (when (interactive-p) (switch-to-buffer (current-buffer)))
    (goto-char (point-max))
    (insert "pri")
    (py-shell-complete)
    (forward-word -1)
    (sit-for 0.1)
    (assert (looking-at "print") nil "python3-shell-complete-test failed")
    (message "%s" "python3-shell-complete-test passed")))

(defun ipython-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (and (buffer-live-p (get-buffer "*Ipython*"))
	 (kill-buffer-unconditional "*Ipython*"))
    (set-buffer (py-shell nil t "ipython"))
    (switch-to-buffer (current-buffer))
    (sit-for 0.1)
    (goto-char (point-max))
    ;; (comint-send-input)
    (insert "pri")

    (py-shell-complete)
    (sit-for 0.1)
    (assert (looking-back "print") nil "ipython-shell-complete-test failed")
    (message "%s" "ipython-shell-complete-test passed")))


(defun ipython-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (set-buffer (py-shell nil t "/usr/bin/ipython"))
    (sit-for 0.1)
    (goto-char (point-max))
    (insert "pri")
    (py-shell-complete)
    (sit-for 1 t)
    (forward-word -1)
    (assert (looking-at "print") nil "ipython-shell-complete-test failed")
    (message "%s" "ipython-shell-complete-test passed")))


(defun arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-shell-complete-test ()
  (interactive)
  (let (py-switch-buffers-on-execute-p
        py-split-window-on-execute)
    (set-buffer (py-shell nil t "~/arbeit/python/epd_free-7.1-2-rh5-x86/bin/ipython"))
    (sit-for 0.1)
    (switch-to-buffer (current-buffer))
    (goto-char (point-max))
    (insert "pri")
    (py-shell-complete)
    (sit-for 1 t)
    (forward-word -1)
    (assert (looking-at "print") nil "arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-shell-complete-test failed")
    (message "%s" "arbeit-python-epd_free-7.1-2-rh5-x86-bin-ipython-shell-complete-test passed")))



(provide 'py-shell-completion-tests)
;;; py-shell-completion-tests ends here
