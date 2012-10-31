;;; copy-code --- Copies highlighted code to the pasteboard as RTF

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 08 Dec 2011
;; Version: 1.0
;; Keywords: code clipboard pasteboard
;; X-URL: https://github.com/jwiegley/copy-code

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Uses the tool "highlight", and the system utility "pbcopy" to copy the
;; selected region (or the current buffer) as RTF to the system pasteboard.
;;
;; I bind this to M-a-w, or Cmd-Option-W on my Mac.  It's great for getting
;; code from Emacs into Keynote as highlighted text with leading line numbers.
;;
;; The command `copy-code-as-rtf' also accepts prefix and numerical arguments:
;;
;;   C-u M-x copy-code-as-rtf        Don't use prefixed line numbers
;;   M-24 M-x copy-code-as-rtf       Use a font-size of 24pt
;;   M-- M-24 M-x copy-code-as-rtf   Use a font-size of 24pt, and no linnums

(defgroup copy-code nil
  "Copies highlighted code to the pasteboard as RTF"
  :group 'prog-mode)

;;;###autoload
(defun copy-code-as-rtf (&optional font-size)
  (interactive "P")
  (let* ((real-font-size
          (if (and font-size
                   (/= (prefix-numeric-value font-size) 4))
              (abs font-size)
            18))
         (common-options
          (format "--font Monaco --font-size %d %s -O rtf --style Breeze"
                  real-font-size
                  (if (and font-size
                           (or (= (prefix-numeric-value font-size) 4)
                               (< (prefix-numeric-value font-size) 0)))
                      "--linenumbers" "")))
         (temp-buffer (get-buffer-create " *code*")))
    (shell-command-on-region
     (if (region-active-p) (region-beginning) (point-min))
     (if (region-active-p) (region-end) (point-max))
     (format "highlight --syntax %s %s"
             (file-name-extension (buffer-file-name)) common-options)
     temp-buffer)
    (with-current-buffer temp-buffer
      (goto-char (point-max))
      (search-backward "\\par\\pard")
      (delete-region (match-beginning 0) (match-end 0))
      (shell-command-on-region (point-min) (point-max) "pbcopy")
      (kill-buffer (current-buffer)))
    (message "Copied %s to pasteboard as RTF with font-size of %d"
             (if (region-active-p) "region" "file")
             real-font-size)))

(provide 'copy-code)

;;; copy-code.el ends here
