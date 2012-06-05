;;; w3m-type-ahead.el --- type ahead support for Emacs-w3m

;;; Copyright (C) 2003, 2004, 2005, 2006 Matthew P. Hodges

;; Author: Matthew P. Hodges <MPHodges@member.fsf.org>
;; Version: $Id: w3m-type-ahead.el,v 1.107 2006/09/03 12:45:42 mphodges-guest Exp $

;; w3m-type-ahead.el is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; w3m-type-ahead.el is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied warranty
;; of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;;; Commentary:
;; 
;; Type ahead support for Emacs-w3m.  This allows an isearch facility
;; that is limited to HREF anchors.  Switch the mode on for all
;; w3m-mode buffers with:
;;     (add-hook 'w3m-mode-hook 'w3m-type-ahead-mode)

(require 'w3m)

;;; Code:

(defconst w3m-type-ahead-version "2.4.0"
  "Version number of this package.")

(defgroup w3m-type-ahead nil
  "Type ahead support for Emacs-w3m."
  :group 'w3m
  :link '(url-link "http://mph-emacs-pkgs.alioth.debian.org/WthreemTypeAheadEl.html"))

;; Customizable variables

(defcustom w3m-type-ahead-hide-url nil
  "If non-nil, hide the URL in the echo area.
Do this by removing `w3m-print-this-url' from
`w3m-after-cursor-move-hook' during the incremental search.  If
equal to the symbol regexp-only, only hide the URL for regexp
searches."
  :group 'w3m-type-ahead
  :type '(choice
          (const :tag "Show URL for all searches" nil)
          (const :tag "Hide URL for all searches" t)
          (const :tag "Hide URL for regexp searches" regexp-only)))

;; Entry points

(defun w3m-type-ahead (&optional arg new-session)
  "Type-ahead search for `w3m-mode' buffers.
If ARG is the number 2 or the list of the number 16 (you may
produce this by typing `C-u' twice) or NEW-SESSION is non-nil,
make a copy of the current session in advance.  Otherwise, if ARG
is non-nil, it forces reloading the URL at point.  (See
`w3m-view-this-url'.)"
  (interactive (if (member current-prefix-arg '(2 (16)))
		   (list nil t)
		 (list current-prefix-arg nil)))
  (w3m-type-ahead-internal nil arg new-session))

(defun w3m-type-ahead-regexp (&optional arg new-session)
  "Type-ahead regexp search for `w3m-mode' buffers.
If ARG is the number 2 or the list of the number 16 (you may
produce this by typing `C-u' twice) or NEW-SESSION is non-nil,
make a copy of the current session in advance.  Otherwise, if ARG
is non-nil, it forces reloading the URL at point.  (See
`w3m-view-this-url'.)"
  (interactive (if (member current-prefix-arg '(2 (16)))
		   (list nil t)
		 (list current-prefix-arg nil)))
  (w3m-type-ahead-internal t arg new-session))

;; Internal functions

(defun w3m-type-ahead-internal (regexp-p arg new-session)
  "Internal `w3m-type-ahead' function.
If non-nil REGEXP-P, do regular expression search.  ARG and
NEW-SESSION are passed to `w3m-view-this-url', which see."
  (cond
   ((not (eq major-mode 'w3m-mode))
    (message "Can't type ahead in non-W3M buffer."))
   (w3m-current-process
    (message "Can't type ahead while W3M is retrieving."))
   ((not (next-single-property-change (point-min)
                                      'w3m-anchor-sequence))
    (message "Can't type ahead; no anchors found in buffer."))
   (t
    (let ((advise '(search-forward
		    search-backward
		    re-search-forward
		    re-search-backward))
	  success)
      (unwind-protect
          (progn
            (mapcar (lambda (f)
                      (ad-enable-advice f 'around 'w3m-type-ahead)
                      (ad-activate f))
                    advise)
            (let ((w3m-after-cursor-move-hook
                   (copy-alist w3m-after-cursor-move-hook)))
              (when (or (eq w3m-type-ahead-hide-url t)
                        (and regexp-p
                             (eq w3m-type-ahead-hide-url 'regexp-only)))
                (setq w3m-after-cursor-move-hook
                      (delq 'w3m-print-this-url w3m-after-cursor-move-hook)))
              (setq success (isearch-forward regexp-p nil))))
        (mapcar (lambda (f)
                  (ad-disable-advice f 'around 'w3m-type-ahead)
                  (ad-activate f))
                advise))
      ;; Visit link if successful
      (when (and success (equal last-command-char ?\r))
        ;; If we have adjacent anchors we may need to adjust point
        (when isearch-forward
          (let ((anchor-1 (get-text-property (point) 'w3m-anchor-sequence))
                (anchor-2 (get-text-property (1- (point)) 'w3m-anchor-sequence)))
            (and anchor-1
                 anchor-2
                 (/= anchor-1 anchor-2)
                 (goto-char (1- (point))))))
        (w3m-view-this-url arg new-session))))))

(defun w3m-type-ahead-next-anchor ()
  "Return `point' for the start of the next anchor.
If in an anchor, just return current value of point; if no next
anchor, return nil."
  (if (get-text-property (point) 'w3m-anchor-sequence)
      (point)
    (next-single-property-change (point) 'w3m-anchor-sequence)))

(defun w3m-type-ahead-previous-anchor ()
  "Return `point' after the end of the previous anchor.
If in an anchor, just return current value of point; if no
previous anchor, return nil."
  (if (get-text-property
       ;; avoid problem with a reversed search from (point-min)
       (if (bobp) (point) (1- (point)))
       'w3m-anchor-sequence)
      (point)
    (previous-single-property-change (point) 'w3m-anchor-sequence)))

(defun w3m-type-ahead-anchor-end ()
  "Return `point' after the end of the current anchor."
  (unless (get-text-property (point) 'w3m-anchor-sequence)
    (error "Not in w3m anchor"))
  (next-single-property-change (point) 'w3m-anchor-sequence))

(defun w3m-type-ahead-anchor-start ()
  "Return `point' for the start of the current anchor."
  (unless (get-text-property (1- (point)) 'w3m-anchor-sequence)
    (error "Not in w3m anchor"))
  (previous-single-property-change (point) 'w3m-anchor-sequence))

;; Advised functions

(defadvice search-forward (around w3m-type-ahead)
  "Limit search to w3m anchors."
  (if (not (eq major-mode 'w3m-mode))
      ad-do-it
    (let (res)
      (ad-with-originals 'search-forward
        (while (and (goto-char
                     (or (w3m-type-ahead-next-anchor) (point-max)))
                    (not (eobp))
                    (not (setq res (search-forward
                                    (ad-get-arg 0)
                                    (w3m-type-ahead-anchor-end)
                                    'move-to-bound)))))
        (setq ad-return-value res)))))

(defadvice search-backward (around w3m-type-ahead)
  "Limit search to w3m anchors."
  (if (not (eq major-mode 'w3m-mode))
      ad-do-it
    (let (res)
      (ad-with-originals 'search-backward
        (while (and (goto-char
                     (or (w3m-type-ahead-previous-anchor) (point-min)))
                    (not (bobp))
                    (not (setq res (search-backward
                                    (ad-get-arg 0)
                                    (w3m-type-ahead-anchor-start)
                                    'move-to-bound)))))
        (setq ad-return-value res)))))

(defadvice re-search-forward (around w3m-type-ahead)
  "Limit search to w3m anchors."
  ;; isearch-message-prefix is the only place in isearch where a
  ;; search command (re-search-forward) is called with a non-nil BOUND
  ;; optional argument.
  (if (not (eq major-mode 'w3m-mode))
      ad-do-it
    (save-restriction
      (narrow-to-region (point-min) (or (ad-get-arg 1) (point-max)))
      (let ((posn (point)) res)
        (ad-with-originals 're-search-forward
          (while (and (goto-char
                       (or (w3m-type-ahead-next-anchor) (point-max)))
                      (not (eobp))
                      (not (setq res (re-search-forward
                                      (ad-get-arg 0)
                                      (w3m-type-ahead-anchor-end)
                                      'move-to-bound))))))
        (setq ad-return-value res)))))

(defadvice re-search-backward (around w3m-type-ahead)
  "Limit search to w3m anchors."
  (if (not (eq major-mode 'w3m-mode))
      ad-do-it
    (let (res)
      (ad-with-originals 're-search-backward
        (while (and (goto-char
                     (or (w3m-type-ahead-previous-anchor) (point-min)))
                    (not (bobp))
                    (not (setq res (re-search-backward
                                    (ad-get-arg 0)
                                    (w3m-type-ahead-anchor-start)
                                    'move-to-bound)))))
        (setq ad-return-value res)))))

;; Minor mode setup

(defvar w3m-type-ahead-mode-map
  (let ((map (make-sparse-keymap)))
     (define-key map (kbd "/") 'w3m-type-ahead)
     (define-key map (kbd "M-/") 'w3m-type-ahead-regexp)
    map)
  "Keymap for W3M Type Ahead mode.")

;; define-minor-mode is not available in GNU Emacs 20.  In XEmacs 21
;; and GNU Emacs 21, easy-mmode-define-minor-mode is an alias for
;; define-minor-mode.

;;;###autoload
(easy-mmode-define-minor-mode w3m-type-ahead-mode
  "Toggle W3M Type Ahead mode.
With ARG, turn W3M Type Ahead mode on if and only if ARG is
positive.

\\{w3m-type-ahead-mode-map}"
  nil " wta" w3m-type-ahead-mode-map)

(provide 'w3m-type-ahead)

;;; w3m-type-ahead.el ends here
