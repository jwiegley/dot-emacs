;;; discover.el --- discover more of Emacs

;; Copyright (C) 2013 Mickey Petersen

;; Author: Mickey Petersen <mickey@fyeah.org>
;; Keywords:
;; Package-Requires: ((makey "0.2"))

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

(require 'makey)

(defconst discover-context-menus
  '(
    ;; Dired
    (dired
     (description "DIRectory EDitor")
     (actions
      ("Navigation"
       ("DEL" "unmark backward" dired-unmark-backward)
       ("RET" "find file" dired-find-file)
       ("SPC" "next line" dired-next-line)
       ("<" "prev dirline" dired-prev-dirline)
       (">" "next dirline" dired-next-dirline)
       ("^" "up directory" dired-up-directory)
       ("j" "goto file" dired-goto-file)
       ("i" "maybe insert subdir" dired-maybe-insert-subdir)
       ("n" "next line" dired-next-line)
       ("p" "previous line" dired-previous-line)
       ("v" "view file" dired-view-file)
       ("w" "copy filename as kill" dired-copy-filename-as-kill))

      ("Marked file"
       ("A" "search marked" dired-do-search)
       ("B" "byte compile marked" dired-do-byte-compile)
       ("C" "copy marked" dired-do-copy)
       ("D" "delete marked" dired-do-delete)
       ("F" "find marked files marked" dired-do-find-marked-files)
       ("G" "chgrp marked" dired-do-chgrp)
       ("H" "hardlink marked" dired-do-hardlink)
       ("L" "load marked" dired-do-load)
       ("M" "chmod marked" dired-do-chmod)
       ("O" "chown marked" dired-do-chown)
       ("P" "print marked" dired-do-print)
       ("Q" "query replace regexp marked" dired-do-query-replace-regexp)
       ("R" "rename marked" dired-do-rename)
       ("S" "symlink marked" dired-do-symlink)
       ("T" "touch marked" dired-do-touch)
       ("V" "run mail marked" dired-do-run-mail)
       ("X" "shell command marked" dired-do-shell-command)
       ("k" "kill lines marked" dired-do-kill-lines)
       ("l" "redisplay marked" dired-do-redisplay)
       ("Y" "relsymlink marked" dired-do-relsymlink)
       ("Z" "compress marked" dired-do-compress)
       ("!" "shell command marked" dired-do-shell-command)
       ("&" "async shell command marked" dired-do-async-shell-command))

      ("Misc"
       ("+" "create directory" dired-create-directory)
       ("." "clean directory" dired-clean-directory)
       ("#" "flag auto save files" dired-flag-auto-save-files)
       ("$" "hide subdir" dired-hide-subdir)
       ("=" "diff" dired-diff)
       ("C-o" "display file" dired-display-file)
       ("I" "info" dired-info)
       ("N" "man" dired-man)
       ("U" "unmark all marks" dired-unmark-all-marks)
       ("a" "find alternate file" dired-find-alternate-file)
       ("d" "flag file deletion" dired-flag-file-deletion)
       ("g" "revert buffer" revert-buffer)
       ("m" "mark" dired-mark)
       ("o" "find file other window" dired-find-file-other-window)
       ("s" "sort toggle or edit" dired-sort-toggle-or-edit)
       ("t" "toggle marks" dired-toggle-marks)
       ("u" "unmark" dired-unmark)
       ("x" "delete flagged" dired-do-flagged-delete)
       ("y" "show file type" dired-show-file-type)
       ("~" "flag backup files" dired-flag-backup-files)
       ) ;; prefix commands for further nesting
      ("More"
       ("%" "do by regexp ..." makey-key-mode-popup-dired-regexp)
       ("*" "mark ..." makey-key-mode-popup-dired-marking)
       ("M-s" "isearch ..." makey-key-mode-popup-dired-isearch-meta)))
     ;; this will also kill the `dired' window. On one hand, it makes
     ;; sense: we're just feeding the commands straight to to dired
     ;; and `q' will indeed quit the dired window. On the other hand,
     ;; sometimes you just want to close the context menu -- and
     ;; you'd naturally do that with q.

     ;; ("q" "quit window" quit-window)
     )

    ;; These three context menus should drive home how many layers of
    ;; key bindings dired has!
    (dired-isearch-meta
     (description "Isearch in files or over files in dired")
     (actions
      ("Isearch"
       ("<backspace>" "... back" makey-key-mode-popup-dired)
       ("f" "isearch for files ..." makey-key-mode-popup-dired-isearch-for-filenames)
       ("a" "isearch in files ..." makey-key-mode-popup-dired-isearch-in-filenames))
      ))

    (dired-isearch-for-filenames
     (description "Isearch for files in dired")
     (actions
      ("Isearch"
       ("<backspace>" "... back" makey-key-mode-popup-dired-isearch-meta)
       ("C-s" "isearch filenames" dired-isearch-filenames)
       ("C-M-s" "isearch filenames regexp" dired-isearch-filenames-regexp))))

    (dired-isearch-in-filenames
     (description "Isearch in marked files")
     (actions
      ("Isearch"
       ("<backspace>" "... back" makey-key-mode-popup-dired-isearch-meta)
       ("C-s" "isearch marked" dired-do-isearch)
       ("C-M-s" "isearch regexp marked" dired-do-isearch-regexp))))

    (dired-marking
     (description "Mark/unmark by file, regexp, extension, directory & more")
     (actions
      ("Mark"
       ("C-n" "next marked file" dired-next-marked-file)
       ("C-p" "prev marked file" dired-prev-marked-file)
       ("!" "unmark all marks" dired-unmark-all-marks)
       ("%" "mark files by regexp" dired-mark-files-regexp)
       ("(" "mark files by sexp" dired-mark-sexp)
       ("*" "mark executables" dired-mark-executables)
       ("." "mark extension" dired-mark-extension)
       ("/" "mark directories" dired-mark-directories)
       ("?" "unmark all files" dired-unmark-all-files)
       ("@" "mark symlinks" dired-mark-symlinks)
       ("O" "mark omitted" dired-mark-omitted)
       ("c" "change marks" dired-change-marks)
       ("m" "mark selected" dired-mark)
       ("s" "mark subdir files" dired-mark-subdir-files)
       ("t" "toggle marks" dired-toggle-marks)
       ("u" "unmark selected" dired-unmark)
       ("DEL" dired-unmark-backward))))
    (dired-regexp
     (description "Do by marked or flagged files matching a regexp")
     (actions
      ("Regexp"
       ("&" "flag garbage files" dired-flag-garbage-files)
       ("C" "copy regexp" dired-do-copy-regexp)
       ("H" "hardlink regexp" dired-do-hardlink-regexp)
       ("R" "rename regexp" dired-do-rename-regexp)
       ("S" "symlink regexp" dired-do-symlink-regexp)
       ("Y" "relsymlink regexp" dired-do-relsymlink-regexp)
       ("d" "flag files regexp" dired-flag-files-regexp)
       ("g" "mark files containing regexp" dired-mark-files-containing-regexp)
       ("l" "downcase" dired-downcase)
       ("m" "mark files regexp" dired-mark-files-regexp)
       ("r" "rename regexp" dired-do-rename-regexp)
       ("u" "upcase" dired-upcase))))
    ;; Rectangles - C-x r ...
    (rectangles
     (description "Rectangles, register and bookmarks")
     (actions
      ("Rectangle"
       ("M-w" "copy rectangle as kill" copy-rectangle-as-kill)
       ("N" "rectangle number lines" rectangle-number-lines)
       ("c" "clear rectangle" clear-rectangle)
       ("d" "delete rectangle" delete-rectangle)
       ("k" "kill rectangle" kill-rectangle)
       ("o" "open rectangle" open-rectangle)
       ("r" "copy rectangle to register" copy-rectangle-to-register)
       ("t" "string rectangle" string-rectangle)
       ("y" "yank rectangle" yank-rectangle))

      ("Bookmark"
       ("b" "bookmark jump" bookmark-jump)
       ("l" "bookmark bmenu list" bookmark-bmenu-list)
       ("m" "bookmark set" bookmark-set))

      ("Register"
       ("+" "increment register" increment-register)
       ("C-@" "point to register" point-to-register)
       ("C-SPC" "point to register" point-to-register)
       ("SPC" "point to register" point-to-register)
       ("f" "frame configuration to register" frame-configuration-to-register)
       ("g" "insert register" insert-register)
       ("i" "insert register" insert-register)
       ;; this is technically not bound to a key but it's just too darn
       ;; useful to leave unbound.
       ("A" "append to register" append-to-register)
       ("j" "jump to register" jump-to-register)
       ("n" "number to register" number-to-register)
       ("s" "copy to register" copy-to-register)
       ("w" "window configuration to register" window-configuration-to-register)
       ("x" "copy to register" copy-to-register))))
    (isearch
     (description "Isearch, occur and highlighting")
     (lisp-switches
      ("-cf" "Case should fold search" case-fold-search t nil))
     (lisp-arguments
      ("=l" "context lines to show (occur)"
       "list-matching-lines-default-context-lines"
       (lambda (dummy) (interactive) (read-number "Number of context lines to show: "))))
     (actions
      ("Isearch"
       ("_" "isearch forward symbol" isearch-forward-symbol)
       ("w" "isearch forward word" isearch-forward-word))
      ("Occur"
       ("o" "occur" occur))
      ("More"
       ("h" "highlighters ..." makey-key-mode-popup-isearch-highlight))))
    (isearch-highlight
     (actions
      ("Highlight"
       ("l" "highlight lines matching regexp" highlight-lines-matching-regexp)
       ("p" "highlight phrase" highlight-phrase)
       ("r" "highlight regexp" highlight-regexp)
       ("u" "unhighlight regexp" unhighlight-regexp))
      ("Store"
       ("f" "hi lock find patterns" hi-lock-find-patterns)
       ("w" "hi lock write interactive patterns" hi-lock-write-interactive-patterns))))))

(makey-initialize-key-groups discover-context-menus)

(defun discover-turn-on-in-dired ()
  (local-set-key (kbd "?") 'makey-key-mode-popup-dired))

(add-hook 'dired-mode-hook 'discover-turn-on-in-dired)

;;; Default Keybindings
(defvar discover-map
  (let ((m (make-sparse-keymap)))
    ;; this overrides rectangles. this is what we want
    (define-key m (kbd "C-x r") 'makey-key-mode-popup-rectangles)
    (define-key m (kbd "M-s") 'makey-key-mode-popup-isearch)
    m)
  "Keymap for `discover'.")

;;;###autoload
(define-minor-mode discover-mode
  "Helps you discover Emacs with interactive context menus.

Key bindings:
\\{discover-map}"
  :keymap discover-map
  :group 'discover)

;;;###autoload
(define-globalized-minor-mode global-discover-mode discover-mode
  discover-mode-turn-on)

(defun discover-mode-turn-on ()
  "Enable `discover-mode' if appropriate for this buffer."
  (unless (or (minibufferp) (eq 'makey-key-mode major-mode))
    (discover-mode 1)))

(provide 'discover)
;;; discover.el ends here
