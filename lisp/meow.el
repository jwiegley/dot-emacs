;;; meow --- Notification system for Emacs similar to Growl

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 24 Aug 2011
;; Version: 1.0
;; Keywords: notification emacs message
;; X-URL: https://github.com/jwiegley/meow

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

;; Meow is a Growl workalike for Emacs that uses a common notification
;; interface with multiple, selectable "styles", whose use can be fully
;; customized by the user.  They can even use multiple styles for a given
;; event.  It pretty much works just like Growl, so I'd recommend learning
;; about how that system functions if this doesn't make sense.
;;
;; As for builtin styles, they currently are:
;;
;;  - Growl itself (surprised?)
;;  - `message', with face showing severity
;;  - `message' followed by `ding'
;;  - `error'
;;  - Persistent text in the mode-line, in different faces according
;;    to severity, similar to how ERC's track feature works
;;  - Turning the fringe a different color, based on severity
;;
;; It's easy to create a new style, such as playing a sound, sending an
;; e-mail, logging a message to syslog, queueing text to a log file, etc.
;;
;; The interface for programmers is simple:
;;
;;   (meow SYMBOL SEVERITY MESSAGE &optional TITLE BUFFER DATA)
;;
;; SYMBOL is a symbol which identifies the message.  That, in conjunction with
;; the major mode, is used for looking up which style(s) are used to notify
;; the user.  SEVERITY is one of the following, along with its typically
;; associated color:
;;
;;   - `urgent'    (red)
;;   - `high'      (orange)
;;   - `moderate'  (yellow)
;;   - `normal'    (green)
;;   - `low'       (blue)
;;   - `trivial'   (purple)
;;
;; If no TITLE is given, it's assumed to be the buffer-name.  If BUFFER is
;; nil, it is taken to be the current buffer.  Knowing which buffer an alert
;; comes from allows the user the easily navigate through all the buffers
;; which had unviewed alerts.  This is again similar to erc-track.  DATA is an
;; opaque value which modules can pass through to their own styles.  If a
;; style chosen by the user does not support it, it is ignored.
;;
;; Furthermore, users can configure what happens if an alert occurs in a
;; buried buffer, a buffer that's visible in a window in any or the current
;; frame, or a buffer that's visible in the currently selected window.  This
;; is followed by a set of keybindings for cycling through unvisited alerts,
;; listing past alerts (with unvisited ones in bold), and popping back to the
;; frame/window configuration the user was at before they started cycling.

(defgroup meow nil
  "Notification system for Emacs similar to Growl"
  :group 'emacs)

(defcustom meow-alert-styles nil
  ""
  :type 'boolean
  :group 'meow)

(defmacro define-meow-style ())

(defun meow (severity message &title title buffer data))

(provide 'meow)

;;; meow.el ends here
