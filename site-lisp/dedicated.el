;;; dedicated.el --- A very simple minor mode for dedicated buffers

;; Copyright (C) 2000 Eric Crampton <eric@atdesk.com>

;; Author: Eric Crampton <eric@atdesk.com>
;; Maintainer: Eric Crampton <eric@atdesk.com>
;; Version: 1.0.0
;; Keywords: dedicated, buffer

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.

;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;; MA 02111-1307, USA.

;;; Commentary:

;; This minor mode allows you to toggle a window's "dedicated" flag.
;; When a window is "dedicated", Emacs will not select files into that
;; window. This can be quite handy since many commands will use
;; another window to show results (e.g., compilation mode, starting
;; info, etc.) A dedicated window won't be used for such a purpose.
;;
;; Dedicated buffers will have "D" shown in the mode line.

;;; Code:

(defvar dedicated-mode nil
  "Mode variable for dedicated minor mode.")
(make-variable-buffer-local 'dedicated-mode)

(defun dedicated-mode (&optional arg)
  "Dedicated minor mode."
  (interactive "P")
  (setq dedicated-mode (not dedicated-mode))
  (set-window-dedicated-p (selected-window) dedicated-mode)
  (if (not (assq 'dedicated-mode minor-mode-alist))
      (setq minor-mode-alist
	    (cons '(dedicated-mode " D")
		  minor-mode-alist))))

(provide 'dedicated)
