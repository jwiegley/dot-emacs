;;; circe-color-nicks.el --- Color nicks in the channel

;; Copyright (C) 2012  Taylan Ulrich Bayırlı/Kammer

;; Author: Taylan Ulrich Bayırlı/Kammer <taylanbayirli@gmail.com>

;; This file is part of Circe.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301  USA

;;; Commentary:

;; This Circe module adds the ability to assign a color to each
;; nick in a channel.

;; Some ideas/code copied from rcirc-colors.el.

;; To use it, put the following into your .emacs:

;; (require 'circe-color-nicks)
;; (enable-circe-color-nicks)

;;; Code:

(require 'circe)
(require 'color)
(require 'cl-lib)

;;;###autoload
(defun enable-circe-color-nicks ()
  "Enable the Color Nicks module for Circe.
This module colors all encountered nicks in a cross-server fashion."
  (interactive)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'circe-channel-mode)
        (add-circe-color-nicks))))
  (add-hook 'circe-channel-mode-hook
            'add-circe-color-nicks))

(defun disable-circe-color-nicks ()
  "Disable the Color Nicks module for Circe.
See `enable-circe-color-nicks'."
  (interactive)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq major-mode 'circe-channel-mode)
        (remove-circe-color-nicks))))
  (remove-hook 'circe-channel-mode-hook
               'add-circe-color-nicks))

(defun add-circe-color-nicks ()
  "Add `circe-color-nicks' to `lui-pre-output-hook'."
  (add-hook 'lui-pre-output-hook 'circe-color-nicks))

(defun remove-circe-color-nicks ()
  "Remove `circe-color-nicks' from `lui-pre-output-hook'."
  (remove-hook 'lui-pre-output-hook 'circe-color-nicks))


(defgroup circe-color-nicks nil
  "Nicks colorization for Circe"
  :prefix "circe-color-nicks-"
  :group 'circe)

(defcustom circe-color-nicks-min-contrast-ratio 7
  "Minimum contrast ratio from background for generated colors;
recommended is 7:1, or at least 4.5:1 (7 stands for 7:1 here).
Lower value allows higher color spread, but could lead to less
readability."
  :group 'circe-color-nicks)

(defcustom circe-color-nicks-min-difference 17
  "Minimum difference from each other for generated colors."
  :group 'circe-color-nicks)

(defcustom circe-color-nicks-min-fg-difference 17
  "Minimum difference from foreground for generated colors."
  :group 'circe-color-nicks)

(defcustom circe-color-nicks-min-my-message-difference 0
  "Minimum difference from own nick color for generated colors."
  :group 'circe-color-nicks)

(defcustom circe-color-nicks-everywhere nil
  "Whether nicks should be colored in message bodies too."
  :type 'boolean
  :group 'circe-color-nicks)

(defcustom circe-color-nicks-message-blacklist nil
  "Blacklist for nicks that shall never be highlighted inside
  images."
  :type '(repeat string)
  :group 'circe-color-nicks)

(defcustom circe-color-nicks-pool-type 'adaptive
  "Type of the color nick pool.
Must be one of the following:

'adaptive: Generate colors based on the current theme.

List of strings: Pick colors from the specified list of hex codes
or color names (see `color-name-rgb-alist')."
  :type '(choice (const :tag "Adaptive" adaptive)
                 (repeat string))
  :group 'circe-color-nicks)


;;; See http://www.w3.org/TR/2013/NOTE-WCAG20-TECHS-20130905/G18

(defsubst circe-w3-contrast-c-to-l (c)
  (if (<= c 0.03928)
      (/ c 12.92)
    (expt (/ (+ c 0.055) 1.055) 2.4)))

(defsubst circe-w3-contrast-relative-luminance (rgb)
  (apply #'+
         (cl-mapcar (lambda (color coefficient)
                      (* coefficient
                         (circe-w3-contrast-c-to-l color)))
                    rgb
                    '(0.2126 0.7152 0.0722))))

(defsubst circe-w3-contrast-contrast-ratio (color1 color2)
  (let ((l1 (+ 0.05 (circe-w3-contrast-relative-luminance color1)))
        (l2 (+ 0.05 (circe-w3-contrast-relative-luminance color2))))
    (if (> l1 l2)
        (/ l1 l2)
        (/ l2 l1))))


(defun circe-color-alist ()
  "Return list of colors (name rgb lab) where rgb is 0 to 1."
  (let ((alist (if (display-graphic-p)
                   color-name-rgb-alist
                 (mapcar (lambda (c)
                           (cons (car c) (cddr c)))
                         (tty-color-alist))))
        (valmax (float (car (color-values "#ffffff")))))
    (mapcar (lambda (c)
              (let* ((name (car c))
                     (rgb (mapcar (lambda (v)
                                    (/ v valmax))
                                  (cdr c)))
                     (lab (apply #'color-srgb-to-lab rgb)))
                (list name rgb lab)))
            alist)))

(defun circe-color-canonicalize-format (color)
  "Turns COLOR into (name rgb lab) format.  Avoid calling this in
a loop, it's very slow on a tty!"
  (let* ((name color)
         (rgb (circe-color-name-to-rgb color))
         (lab (apply #'color-srgb-to-lab rgb)))
   (list name rgb lab)))

(defun circe-color-contrast-ratio (color1 color2)
  "Gives the contrast ratio between two colors."
  (circe-w3-contrast-contrast-ratio (nth 1 color1) (nth 1 color2)))

(defun circe-color-diff (color1 color2)
  "Gives the difference between two colors per CIEDE2000."
  (color-cie-de2000 (nth 2 color1) (nth 2 color2)))

(defun circe-color-name-to-rgb (color)
  "Like `color-name-to-rgb' but also handles \"unspecified-bg\"
and \"unspecified-fg\"."
  (cond ((equal color "unspecified-bg") '(0 0 0))
        ((equal color "unspecified-fg") '(1 1 1))
        (t (color-name-to-rgb color))))


(defun circe-nick-color-appropriate-p (color bg fg my-msg)
  "Tells whether COLOR is appropriate for being a nick color.
BG, FG, and MY-MSG are the background, foreground, and my-message
colors; these are expected as parameters instead of computed here
because computing them repeatedly is a heavy operation."
  (and (>= (circe-color-contrast-ratio color bg)
           circe-color-nicks-min-contrast-ratio)
       (>= (circe-color-diff color fg)
           circe-color-nicks-min-fg-difference)
       (>= (circe-color-diff color my-msg)
           circe-color-nicks-min-my-message-difference)))

(defun circe-nick-colors-delete-similar (colors)
  "Return list COLORS with pairs of colors filtered out that are
too similar per `circe-color-nicks-min-difference'.  COLORS may
be mutated."
  (cl-mapl (lambda (rest)
             (let ((color (car rest)))
               (setcdr rest (cl-delete-if
                             (lambda (c)
                               (< (circe-color-diff color c)
                                  circe-color-nicks-min-difference))
                             (cdr rest)))))
           colors)
  colors)

(defun circe-nick-color-generate-pool ()
  "Return a list of appropriate nick colors."
  (if (consp circe-color-nicks-pool-type)
      circe-color-nicks-pool-type
    (let ((bg (circe-color-canonicalize-format (face-background 'default)))
          (fg (circe-color-canonicalize-format (face-foreground 'default)))
          (my-msg (circe-color-canonicalize-format
                   (face-attribute
                    'circe-my-message-face :foreground nil 'default))))
      (mapcar #'car (circe-nick-colors-delete-similar
                     (cl-remove-if-not
                      (lambda (c)
                        (circe-nick-color-appropriate-p c bg fg my-msg))
                      (circe-color-alist)))))))

(defun circe-nick-color-pool-test ()
  "Display all appropriate nick colors in a temp buffer."
  (interactive)
  (switch-to-buffer (get-buffer-create "*Circe color test*"))
  (erase-buffer)
  (let ((pool (circe-nick-color-generate-pool)))
    (while pool
      (let ((pt (point)))
        (insert "The quick brown fox jumped over the lazy dog.\n")
        (put-text-property pt (point) 'face `(:foreground ,(pop pool)))))))

(defvar circe-nick-color-pool nil
  "Pool of yet unused nick colors.")

(defvar circe-nick-color-mapping (make-hash-table :test 'equal)
  "Hash-table from nicks to colors.")

(defun circe-nick-color-nick-list ()
  "Return list of all nicks that have a color assigned to them.
Own and blacklisted nicks are excluded."
  (let ((our-nick (circe-nick))
        (channel-nicks (circe-channel-nicks))
        nicks)
    (maphash
     (lambda (nick color)
       (when (and (member nick channel-nicks)
                  (not (string= our-nick nick))
                  (not (member nick circe-color-nicks-message-blacklist)))
         (push nick nicks)))
     circe-nick-color-mapping)
    nicks))

(defvar circe-nick-color-timestamps (make-hash-table :test 'equal)
  "Hash-table from colors to the timestamp of their last use.")

(defun circe-nick-color-for-nick (nick)
  "Return the color for NICK.  Assigns a color to NICK if one
wasn't assigned already."
  (let ((color (gethash nick circe-nick-color-mapping)))
    (when (not color)
      ;; NOTE use this as entry point for taking NICK into account for
      ;; picking the new color
      (setq color (circe-nick-color-pick))
      (puthash nick color circe-nick-color-mapping))
    (puthash color (float-time) circe-nick-color-timestamps)
    color))

(defun circe-nick-color-pick ()
  "Picks either a color from the pool of unused colors, or the
color that was used least recently (i.e. nicks that have it
assigned have been least recently active)."
  (if (zerop (hash-table-count circe-nick-color-mapping))
      (setq circe-nick-color-pool (circe-nick-color-generate-pool)))
  (or (pop circe-nick-color-pool)
      (circe-nick-color-pick-least-recent)))

(defun circe-nick-color-pick-least-recent ()
  "Pick the color that was used least recently.
See `circe-nick-color-pick', which is where this is used."
  (let ((least-recent-color nil)
        (oldest-time (float-time)))
    (maphash
     (lambda (color time)
       (if (< time oldest-time)
           (progn
             (setq least-recent-color color)
             (setq oldest-time time))))
     circe-nick-color-timestamps)
    (if least-recent-color
        least-recent-color
      ;; Someone must have messed with `circe-nick-color-mapping', recover by
      ;; re-filling the pool.
      (setq circe-nick-color-pool (circe-nick-color-generate-pool))
      (pop circe-nick-color-pool))))

(defun circe-color-nicks ()
  "Color nicks on this lui output line."
  (when (eq major-mode 'circe-channel-mode)
    (let ((nickstart (text-property-any (point-min) (point-max)
                                        'lui-format-argument 'nick)))
      (when nickstart
        (goto-char nickstart)
        (let ((nickend (next-single-property-change nickstart
                                                    'lui-format-argument))
              (nick (plist-get (plist-get (text-properties-at nickstart)
                                          'lui-keywords)
                               :nick)))
          (when (not (circe-server-my-nick-p nick))
            (let ((color (circe-nick-color-for-nick nick)))
              (add-face-text-property nickstart nickend
                                      `(:foreground ,color)))))))
    (when circe-color-nicks-everywhere
      (let ((body (text-property-any (point-min) (point-max)
                                     'lui-format-argument 'body)))
        (when body
          (with-syntax-table circe-nick-syntax-table
            (goto-char body)
            (let* ((nicks (circe-nick-color-nick-list))
                   (regex (regexp-opt nicks 'words)))
              (let (case-fold-search)
                (while (re-search-forward regex nil t)
                  (let* ((nick (match-string-no-properties 0))
                         (color (circe-nick-color-for-nick nick)))
                    (add-face-text-property (match-beginning 0) (match-end 0)
                                            `(:foreground ,color))))))))))))

(defun circe-nick-color-reset ()
  "Reset the nick color mapping (and some internal data).

This is useful if you switched between frames supporting
different color ranges and would like nicks to get new colors
appropriate to the new color range."
  (interactive)
  (setq circe-nick-color-pool (circe-nick-color-generate-pool))
  (setq circe-nick-color-mapping (make-hash-table :test 'equal))
  (setq circe-nick-color-timestamps (make-hash-table :test 'equal)))

(provide 'circe-color-nicks)
;;; circe-color-nicks.el ends here
