;;; rfringe.el --- display the relative location of the region, in the fringe.
;;
;; Author     : Dino Chiesa <dpchiesa@hotmail.com>
;; Created    : April 2011
;; Version    : 1.0
;; Keywords   : fringe, bitmap
;; X-URL      : http://www.emacswiki.org/emacs/rfringe.el
;; Last-saved : <2011-April-05 11:20:26>

;; Copyright (C) 2011 Dino Chiesa
;;
;; This file is NOT part of GNU Emacs and is licensed differently.
;; rfringe.el is licensed under the Ms-PL.  See the full copy of that
;; license for more details. http://www.opensource.org/licenses/ms-pl
;;

;;; Commentary:
;;
;; This is a module to allow the use of the fringe to indicate locations
;; relative to the bounds of the buffer.  rfringe = "relative fringe".
;;
;; In emacs, displaying fringe indicators is done via text overlays. In
;; that way, bitmaps in the fringe are attached to the lines of text
;; shown in the buffer window.
;;
;; This works nicely when the fringe is used to indicate information
;; that is relevant to the adjacent line; for example, text overflow, or
;; something similar. But, there isn't a simple way for an application
;; or module to use the fringe to display buffer-relative information -
;; for example, the location of compiler error messages.
;;
;; In fact, using the fringe to communicate this kind of information -
;; buffer-relative positions - is probably more intuitive and is
;; certainly more useful for the user. For example, consider the
;; scrollbar. The position and size of the scrollbar indicates to the
;; user the position and size of the current window relative to the
;; entire buffer. This is information that cound not be easily or
;; appropriately conveyed within the visual text. The fringe is
;; perfectly suited for this purpose.
;;
;; Along those lines, a useful integration of fringe with flymake would
;; be to use fringe bitmaps visually indicate the position of all
;; flymake errors and warnings in the buffer, relative to the beginning
;; and end of the buffer. A quick glance at the fringe would give a
;; visual indication of the number of errors or warnings and their
;; approximate positions.
;;
;; Likewise, a diff mode might want to display fringe indicators for the
;; number and approximate relative position of differences.
;;
;; Doing this is not simple, because of the dependency of fringe bitmaps
;; on text overlays that I described above.  To use the fringe to
;; communicate information regarding buffer-relative positions requires
;; a transformation from "buffer position" to "window position".  And
;; this transformation must be re-computed each time a window scrolls or
;; changes size.
;;
;; This module addresses that need, and provides that transformation. It
;; allows you to set an indicator that is buffer-relative in the fringe;
;; the indicator automatically redisplays if the window changes size, or
;; scrolls.
;;
;; Examples:
;;
;; 1. In the simplest case, you can use rfringe to provide a visual
;;    indicator of the top of the region in the buffer, like so:
;;
;;       (rfringe-show-region)
;;
;;    To turn off the indicator, do this:
;;
;;       (rfringe-hide-region)
;;
;;
;; 2. You can also use rfringe to display a set of indicators,
;;    corresponding to a set of locations in the buffer. These might be
;;    the locations of compiler errors, or section beginnings, or
;;    whatever you like.
;;
;;       (setq posns '(79 1000 2000 3000 4000 5000 6000 9000 10000))
;;       (mapc 'rfringe-create-relative-indicator posns)
;;
;;    As you scroll through the buffer, the indicators in the fringe remain fixed.
;;
;;    To remove the indicators, do this:
;;
;;       (rfringe-remove-managed-indicators)
;;
;;    By default, rfringe defines advice to extend flymake to display
;;    indicators this way.  This is not the only intended use of rfringe.el,
;;    but it is a good example.
;;


(require 'fringe)

(defvar rfringe-region-indicator-ovly nil
  "the overlay used internally for the region; see `rfringe-show-region-indicator'.

Applications should not set this value directly. It is intended
for use internally by rfringe.el .
" )

(defvar rfringe-managed-indicators nil
  "a list holding the position and actual overlay for all
\"managed\" indicators. They are managed in the sense that they
automatically update their positions when the window changes
configuration or scrolls, and they can be deleted as a set via
`rfringe-remove-managed-indicators'.

Each element in this list is a cons cell, (POS . OVLY) where POS
is the character position and OVLY is the actual overlay.

Applications should not set this value directly. It is intended
for use internally by rfringe.el .
")


(make-variable-buffer-local 'rfringe-managed-indicators)
(make-variable-buffer-local 'rfringe-region-indicator-ovly)

;; rfringe displays only one kind of bitmap - a thin dash. Create it here.
(define-fringe-bitmap 'rfringe-thin-dash [255 0])

(defun rfringe--compute-position (lines start-pos)
  "computes a position that is LINES ahead of START-POS"
  (save-excursion
    (goto-char start-pos)
    (while (> lines 0)
      (forward-line 1)
      (decf lines))
    ;;(message "l(%d) sp(%d) =x(%d)" lines start-pos (point))
    (point)))


(defun rfringe-hide-region ()
  "Hide any bitmap currently displayed in the fringe indicating the region."
  (interactive)
  (if rfringe-region-indicator-ovly
      (progn
        (delete-overlay rfringe-region-indicator-ovly)
        (setq rfringe-region-indicator-ovly nil))))



(defun rfringe-update-region-indicator (&optional buf)
  "update any fringe indicator for the region, in the buffer BUF."
  (if (not buf)
      (setq buf (current-buffer)))
  (with-current-buffer buf
    (if rfringe-region-indicator-ovly
        (rfringe-show-region-indicator buf))))



(defun rfringe-insert-bitmap (bitmap pos &optional side face)
  "Insert a fringe bitmap at POS.

BITMAP is the name of a bitmap defined with `define-fringe-bitmap'.
SIDE defaults to 'left-fringe and can also be
'right-fringe.  FACE is used to determine the bitmap's color.

The function returns an overlay object.
It should be removed when no longer needed via `delete-overlay'.
"

  (let* ((display-string `(,(or side 'left-fringe) ,bitmap .
                           ,(when face (cons face nil))))
          (before-string (propertize "!" 'display display-string))
          (ov (make-overlay pos pos)))
    (overlay-put ov 'before-string before-string)
    (overlay-put ov 'fringe-helper t)
    ov))




(defun rfringe-create-relative-indicator (pos &optional dont-manage)
  "Display an indicator in the fringe in the current buffer, for
the position POS relative to the buffer size, via a simple bitmap
dash.

If optional DONT-MANAGE is nil, or not present, the overlay is
stored and remembered.  In this case, if the window changes size,
or scrolls, the bitmap will be automatically moved. It can also
be deleted with `rfringe-remove-managed-indicators'. Passing
DONT-MANAGE as t does not do this.

For example, for a buffer of length 10000, if you pas a POS of
5000, then this funciton will display a dash in the fringe,
halfway down, regardless of whether char position 5000 is
visible in the window.

"
  (let* ((top-of-window (window-start))
         (line-delta (scroll-bar-scale (cons pos (point-max)) (window-body-height)))
         (pos-of-indicator
          (rfringe--compute-position line-delta top-of-window))
         ov)
    ;;(message "tow(%d) ld(%d)" top-of-window line-delta)
    ;;(message "compute x=>x1: %d => %d" pos pos-of-indicator)
    (setq ov (rfringe-insert-bitmap
              'rfringe-thin-dash
              pos-of-indicator
              'right-fringe
              'font-lock-warning-face))
    (if (not dont-manage)
        ;; save the location, and the actual overlay object
        (push (cons pos ov) rfringe-managed-indicators))
    ov))




(defun rfringe-show-region-indicator (buf)
  "Display an indicator in the fringe of the position of the region
in the buffer BUF, via a bitmap dash.

For example, if the region is at the top of the buffer, then a
dash will appear at the top of the fringe, regardless of whether
any part of the region is in fact visible in the window."

  (with-current-buffer buf
    (rfringe-hide-region)
    (if (mark) ;; the mark is set
        (setq rfringe-region-indicator-ovly
              (rfringe-create-relative-indicator (min (point) (mark)) t)))))



(defun rfringe-remove-managed-indicators ()
  "Removes all rfringe-managed indicators for the current buffer."
  (if rfringe-managed-indicators
      (progn
        (mapc (lambda (pair)
                (delete-overlay (cdr pair)))
              rfringe-managed-indicators)
        (setq rfringe-managed-indicators nil))))



(defun rfringe-show-region ()
  "Display an indicator in the fringe, for the top of the region."
  (interactive)
  (rfringe-show-region-indicator (current-buffer)))



;; hooks

(defun rfringe--update-region-on-window-scroll (wnd new-start)
  "a sort-of-hook that gets called as each window is scrolled.
The window is given by WND and the new start position is given
by NEW-START.

See `window-scroll-functions' for more info.
"
  (if wnd
      (rfringe-update-region-indicator (window-buffer wnd))))



(defun rfringe--reset-region-indicator-on-window-config-change ()
  "a sort-of-hook that gets called as a window's
\"configuration\" changes. Configuration includes size, width (I
guess), and so on. If the user splits or unsplits the window,
then the configuration changes, and this hook gets called.

This one resets the region indicator, if it is visible.

See `window-configuration-change-hook' for more info.
"
  (if rfringe-region-indicator-ovly
      (rfringe-show-region)))




(defun rfringe--reset-visible-indicators ()
  "a sort-of-hook that gets called as a window's
\"configuration\" changes. Configuration includes size, width (I
guess), and so on. Also, if the user splits or unsplits the
window, then the configuration changes, and this hook gets
called.

This fn moves all managed indicators.

See`window-configuration-change-hook' for more info.
"
  (if rfringe-managed-indicators
      (progn
        ;;(message "rfringe resetting...")
        (let* ((top-of-window (window-start))
               (bdy-height (window-body-height))
               (mx (point-max))
               (move-one
                (lambda (pair)
                  (let* ((pos (car pair))
                         (ov (cdr pair))
                         (line-delta (scroll-bar-scale (cons pos mx) bdy-height))
                         (ipos (rfringe--compute-position line-delta top-of-window)))
                    ;; (message "move %s to %s"
                    ;;          (prin1-to-string ov)
                    ;;          (prin1-to-string ipos))
                    (move-overlay ov ipos ipos)))))
          (mapc move-one rfringe-managed-indicators)))))



(defun rfringe--update-managed-indicators-on-window-scroll (wnd new-start)
  "a sort-of-hook that gets called as each window is scrolled.
The window is given by WND and the new start position is given
by NEW-START.

See `window-scroll-functions' for more info.
"
  (if wnd
      (with-current-buffer (window-buffer wnd)
        (rfringe--reset-visible-indicators))))



;; hooks for managing the 'special' region indicator
(add-hook 'window-scroll-functions 'rfringe--update-region-on-window-scroll)
(add-hook 'window-configuration-change-hook
          'rfringe--reset-region-indicator-on-window-config-change)
(add-hook 'activate-mark-hook 'rfringe-update-region-indicator)


;; hooks for managing all managed indicators
(add-hook 'window-scroll-functions 'rfringe--update-managed-indicators-on-window-scroll)
(add-hook 'window-configuration-change-hook 'rfringe--reset-visible-indicators)


(defun rfringe--char-pos-for-line (line-no)
  (save-excursion
    (goto-line line-no)
    (point)))


;; extend flymake to show fringe indicators
(defadvice flymake-post-syntax-check (after
                                      rfringe-indicate-flymake-status
                                      activate compile)
  (rfringe-remove-managed-indicators)
  (let ((err-count (flymake-get-err-count flymake-err-info "e"))
        (warn-count (flymake-get-err-count flymake-err-info "w")))

    (if (or (/= 0 err-count) (/= 0 warn-count))
       (mapc (lambda (item)
               (message "rfringe: marking error at line %d" (car item))
               (rfringe-create-relative-indicator (rfringe--char-pos-for-line (car item))))
             flymake-err-info))))


(provide 'rfringe)

