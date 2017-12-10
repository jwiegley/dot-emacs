;;; bm.el --- Visible bookmarks in buffer.

;; Copyright (C) 2000-2015  Jo Odland

;; Author: Jo Odland <jo.odland(at)gmail.com>
;; Keywords: bookmark, highlight, faces, persistent
;; URL: https://github.com/joodland/bm

;; Portions Copyright (C) 2002 by Ben Key
;; Updated by Ben Key <bkey1(at)tampabay.rr.com> on 2002-12-05
;; to add support for XEmacs


;; This file is *NOT* part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING. If not, write to the
;; Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


;;; Commentary:

;;; Description:
;;
;;   This package was created because I missed the bookmarks from M$
;;   Visual Studio. I find that they provide an easy way to navigate
;;   in a buffer.
;;
;;   bm.el provides visible, buffer local, bookmarks and the ability
;;   to jump forward and backward to the next bookmark.
;;
;;   Features:
;;    - Toggle bookmarks with `bm-toggle' and navigate forward and
;;      backward in buffer with `bm-next' and `bm-previous'.
;;
;;    - Different wrapping modes, see `bm-wrap-search' and
;;      `bm-wrap-immediately'. Use `bm-toggle-wrapping' to turn
;;      wrapping on/off. Wrapping is only available when
;;      `bm-cycle-all-buffers' is nil.
;;
;;    - Navigate between bookmarks only in current buffer or cycle
;;      through all buffers. Use `bm-cycle-all-buffers' to enable
;;      looking for bookmarks across all open buffers. When cycling
;;      through bookmarks in all open buffers, the search will always
;;      wrap around.
;;
;;    - Setting bookmarks based on a regexp, see `bm-bookmark-regexp'
;;      and `bm-bookmark-regexp-region'.
;;
;;    - Setting bookmark based on line number, see `bm-bookmark-line'.
;;
;;    - Goto line position or start of line, see `bm-goto-position'.
;;
;;    - Persistent bookmarks (see below). Use
;;      `bm-toggle-buffer-persistence' to enable/disable persistent
;;      bookmarks (buffer local).
;;
;;    - List bookmarks with annotations and context in a separate
;;      buffer, see `bm-show' (current buffer) and `bm-show-all' (all
;;      open buffers). See `bm-show-mode-map' for key bindings.
;;
;;    - Remove all bookmarks in current buffer with
;;      `bm-remove-all-current-buffer' and all bookmarks in all open
;;      buffers with `bm-remove-all-all-buffers'.
;;
;;    - Annotate bookmarks, see `bm-bookmark-annotate' and
;;      `bm-bookmark-show-annotation'. The annotation is displayed in
;;      the message area when navigating to a bookmark. Set the
;;      variable `bm-annotate-on-create' to t to be prompted for an
;;      annotation when bookmark is created.
;;
;;    - Different bookmark styles, fringe-only, line-only or both, see
;;      `bm-highlight-style'. It is possible to have fringe-markers on
;;      left or right side.
;;


;;; Known limitations:
;;
;;   This package is developed and tested on GNU Emacs 23.x. It should
;;   work on all GNU Emacs 21.x, GNU Emacs 22.x and also on XEmacs
;;   21.x with some limitations.
;;
;;   There are some incompatibilities with lazy-lock when using
;;   fill-paragraph. All bookmark below the paragraph being filled
;;   will be lost. This issue can be resolved using the
;;   `jit-lock-mode' introduced in GNU Emacs 21.1
;;
;;   Bookmarks will be extended when inserting text (before, inside or
;;   after) bookmark in XEmacs. This is due to the missing support for
;;   overlay hooks i XEmacs.


;;; Installation:
;;
;;   To use bm.el, put it in your load-path and add
;;   the following to your .emacs
;;
;;   (require 'bm)
;;
;; or
;;
;;   (autoload 'bm-toggle   "bm" "Toggle bookmark in current buffer." t)
;;   (autoload 'bm-next     "bm" "Goto bookmark."                     t)
;;   (autoload 'bm-previous "bm" "Goto previous bookmark."            t)
;;


;;; Configuration:
;;
;;   To make it easier to use, assign the commands to some keys.
;;
;;   M$ Visual Studio key setup.
;;     (global-set-key (kbd "<C-f2>") 'bm-toggle)
;;     (global-set-key (kbd "<f2>")   'bm-next)
;;     (global-set-key (kbd "<S-f2>") 'bm-previous)
;;
;;   Click on fringe to toggle bookmarks, and use mouse wheel to move
;;   between them.
;;     (global-set-key (kbd "<left-fringe> <mouse-5>") 'bm-next-mouse)
;;     (global-set-key (kbd "<left-fringe> <mouse-4>") 'bm-previous-mouse)
;;     (global-set-key (kbd "<left-fringe> <mouse-1>") 'bm-toggle-mouse)
;;
;;   If you would like the markers on the right fringe instead of the
;;   left, add the following to line:
;;
;;   (setq bm-marker 'bm-marker-right)
;;



;;; Persistence:
;;
;;   Bookmark persistence is achieved by storing bookmark data in a
;;   repository when a buffer is killed. The repository is saved to
;;   disk on exit. See `bm-repository-file'. The maximum size of the
;;   repository is controlled by `bm-repository-size'.
;;
;;   The buffer local variable `bm-buffer-persistence' decides if
;;   bookmarks in a buffer is persistent or not. Non-file buffers
;;   can't have persistent bookmarks, except for *info* and
;;   indirect buffers.
;;
;;   Bookmarks are non-persistent as default. To have bookmarks
;;   persistent as default add the following line to .emacs.
;;
;;   ;; make bookmarks persistent as default
;;   (setq-default bm-buffer-persistence t)

;;   Use the function `bm-toggle-buffer-persistence' to toggle
;;   bookmark persistence.
;;
;;   To have automagic bookmark persistence we need to add some
;;   functions to the following hooks. Insert the following code
;;   into your .emacs file:
;;
;;   If you are using desktop or other packages that restore buffers
;;   on start up, bookmarks will not be restored. When using
;;   `after-init-hook' to restore the repository, it will be restored
;;   *after* .emacs is finished. To load the repository when bm is
;;   loaded set the variable `bm-restore-repository-on-load' to t,
;;   *before* loading bm (and don't use the `after-init-hook').
;;
;;   ;; Make sure the repository is loaded as early as possible
;;   (setq bm-restore-repository-on-load t)
;;   (require 'bm)
;;
;;   ;; Loading the repository from file when on start up.
;;   (add-hook' after-init-hook 'bm-repository-load)
;;
;;   ;; Restoring bookmarks when on file find.
;;   (add-hook 'find-file-hooks 'bm-buffer-restore)
;;
;;   ;; Saving bookmark data on killing a buffer
;;   (add-hook 'kill-buffer-hook 'bm-buffer-save)
;;
;;   ;; Saving the repository to file when on exit.
;;   ;; kill-buffer-hook is not called when Emacs is killed, so we
;;   ;; must save all bookmarks first.
;;   (add-hook 'kill-emacs-hook '(lambda nil
;;                                   (bm-buffer-save-all)
;;                                   (bm-repository-save)))
;;
;;   ;; Update bookmark repository when saving the file.
;;   (add-hook 'after-save-hook 'bm-buffer-save)
;;
;;   ;; Restore bookmarks when buffer is reverted.
;;   (add-hook 'after-revert-hook 'bm-buffer-restore)
;;
;;
;;   The `after-save-hook' and `after-revert-hook' is not necessary to
;;   use to achieve persistence, but it makes the bookmark data in
;;   repository more in sync with the file state.
;;
;;   The `after-revert-hook' might cause trouble when using packages
;;   that automatically reverts the buffer (like vc after a check-in).
;;   This can easily be avoided if the package provides a hook that is
;;   called before the buffer is reverted (like `vc-before-checkin-hook').
;;   Then new bookmarks can be saved before the buffer is reverted.
;;
;;   ;; make sure bookmarks is saved before check-in (and revert-buffer)
;;   (add-hook 'vc-before-checkin-hook 'bm-buffer-save)



;;; Acknowledgements:
;;
;;  - The use of overlays for bookmarks was inspired by highline.el by
;;    Vinicius Jose Latorre <vinicius(at)cpqd.com.br>.
;;  - Thanks to Ben Key for XEmacs support.
;;  - Thanks to Peter Heslin for notifying me on the incompability
;;    with lazy-lock.
;;  - Thanks to Christoph Conrad for adding support for goto line
;;    position in bookmarks and simpler wrapping.
;;  - Thanks to Jan Rehders for adding support for different bookmark
;;  - styles.
;;  - Thanks to Dan McKinley <mcfunley(at)gmail.com> for inspiration
;;    to add support for listing bookmarks in all buffers,
;;    `bm-show-all'. (http://www.emacswiki.org/cgi-bin/wiki/bm-ext.el)
;;  - Thanks to Jonathan Kotta <jpkotta(at)gmail.com> for mouse
;;    support and fringe markers on left or right side.
;;  - Thanks to Juanma Barranquero <lekktu(at)gmail.com> for making
;;    `bm-show' an electric window, cleaning up the code, finding and
;;    fixing bugs and correcting spelling errors.
;;  - Thanks to jixiuf <jixiuf(at)gmail.com> for adding LIFO support
;;    to bookmark navigation. See `bm-in-lifo-order' for more
;;    information.



;;; Change log:
;; See version history at Github, https://github.com/joodland/bm



;;; Code:
;;

(eval-and-compile
  (require 'cl-lib)
  (require 'cl-macs)
  ;; avoid compile warning on unbound variable
  (require 'info)

  ;; xemacs needs overlay emulation package
  (unless (fboundp 'overlay-lists)
    (require 'overlay)))


(defconst bm-bookmark-repository-version 2
  "The repository version.")

(defgroup bm nil
  "Visible, buffer local bookmarks."
  :link '(emacs-library-link :tag "Source Lisp File" "bm.el")
  :group 'faces
  :group 'editing
  :prefix "bm-")

(defcustom bm-highlight-style 'bm-highlight-only-line
  "*Specify how bookmars are highlighted."
  :type '(choice (const bm-highlight-only-line)
                 (const bm-highlight-only-fringe)
                 (const bm-highlight-line-and-fringe))
  :group 'bm)

(defcustom bm-face 'bm-face
  "*Specify face used to highlight the current line."
  :type 'face
  :group 'bm)


(defcustom bm-persistent-face 'bm-persistent-face
  "*Specify face used to highlight the current line for persistent bookmarks."
  :type 'face
  :group 'bm)

(defcustom bm-priority 0
  "*Specify bm overlay priority.

Higher integer means higher priority, so bm overlay will have precedence
over overlays with lower priority.  *Don't* use a negative number."
  :type 'integer
  :group 'bm)


(defface bm-face
  '((((class grayscale)
      (background light)) (:background "DimGray"))
    (((class grayscale)
      (background dark))  (:background "LightGray"))
    (((class color)
      (background light)) (:foreground "White" :background "DarkOrange1"))
    (((class color)
      (background dark))  (:foreground "Black" :background "DarkOrange1")))
  "Face used to highlight current line."
  :group 'bm)


(defface bm-persistent-face
  '((((class grayscale)
      (background light)) (:background "DimGray"))
    (((class grayscale)
      (background dark))  (:background "LightGray"))
    (((class color)
      (background light)) (:foreground "White" :background "DarkBlue"))
    (((class color)
      (background dark))  (:foreground "White" :background "DarkBlue")))
  "Face used to highlight current line if bookmark is persistent."
  :group 'bm)


(defcustom bm-fringe-face 'bm-fringe-face
  "*Specify face used to highlight the fringe."
  :type 'face
  :group 'bm)

(defcustom bm-fringe-persistent-face 'bm-fringe-persistent-face
  "*Specify face used to highlight the fringe for persistent bookmarks."
  :type 'face
  :group 'bm)

(defface bm-fringe-face
  '((((class grayscale)
      (background light)) (:background "DimGray"))
    (((class grayscale)
      (background dark))  (:background "LightGray"))
    (((class color)
      (background light)) (:foreground "White" :background "DarkOrange1"))
    (((class color)
      (background dark))  (:foreground "Black" :background "DarkOrange1")))
  "Face used to highlight bookmarks in the fringe."
  :group 'bm)

(defface bm-fringe-persistent-face
  '((((class grayscale)
      (background light)) (:background "DimGray"))
    (((class grayscale)
      (background dark))  (:background "LightGray"))
    (((class color)
      (background light)) (:foreground "White" :background "DarkBlue"))
    (((class color)
      (background dark))  (:foreground "White" :background "DarkBlue")))
  "Face used to highlight bookmarks in the fringe if bookmark is persistent."
  :group 'bm)


(defcustom bm-annotate-on-create nil
  "*Specify if bookmarks must be annotated when created.

nil, don't ask for an annotation when creating a bookmark.
t, always ask for annotation when creating a bookmark."
  :type 'boolean
  :group 'bm)


(defcustom bm-wrap-search t
  "*Specify if bookmark search should wrap.

nil, don't wrap when there are no more bookmarks.
t, wrap."
  :type 'boolean
  :group 'bm)


(defcustom bm-wrap-immediately t
  "*Specify if a wrap should be announced or not.
Only has effect when `bm-wrap-search' is t.

nil, announce before wrapping.
t, don't announce."
  :type 'boolean
  :group 'bm)


(defcustom bm-cycle-all-buffers nil
  "*Specify if bookmark search is done across buffers.
This will ignore the `bm-wrap-search' setting.

nil, only search in current buffer.
t, search in all open buffers."
  :type 'boolean
  :group 'bm)

(defcustom bm-in-lifo-order nil
  "`bm-show' and `bm-show-all' list bookmarks in LIFO order,
`bm-next' and `bm-previous' goto bookmark in LIFO order,
 (that is, most recently set ones come first, oldest ones come last)"
  :type 'boolean
  :group 'bm)

(defcustom temporary-bookmark-p nil
  "when visit a bookmark using `bm-next' or `bm-previsour'  the bookmark
will be auto removed if this option is not nil."
  :type 'boolean
  :group 'bm)

(defcustom bm-recenter nil
  "*Specify if the buffer should be recentered after jumping to a bookmark."
  :type 'boolean
  :group 'bm)


(defcustom bm-goto-position t
  "*Specify the position, on line, to go to when jumping to a bookmark.

nil, goto start of line.
t, goto position on the line where the bookmark was set."
  :type 'boolean
  :group 'bm)


(defcustom bm-electric-show t
  "*If t, `bm-show' acts like an electric buffer."
  :type 'boolean
  :group 'bm)


(defcustom bm-repository-file (expand-file-name "~/.bm-repository")
  "*Filename to store persistent bookmarks across sessions.

nil, the repository will not be persistent."
  :type 'string
  :group 'bm)


(defcustom bm-repository-size 100
  "*Size of persistent repository. If nil then there if no limit."
  :type 'integer
  :group 'bm)


(defcustom bm-buffer-persistence nil
  "*Specify if bookmarks in a buffer should be persistent.
Buffer local variable.

nil, don't save bookmarks.
t, save bookmarks."
  :type 'boolean
  :group 'bm)
(make-variable-buffer-local 'bm-buffer-persistence)


(defcustom bm-show-annotations t
  "*Specify if annotations are shown by `bm-show' and
`bm-show-all'."
  :type 'boolean
  :group 'bm)


(defvar bm-restore-repository-on-load nil
  "Specify if repository should be restored when loading bm.

nil, don't restore repository on load.
t, restore repository when this file is loaded. This must be set
before bm is loaded.")

(defvar bm-repository nil
  "Alist with all persistent bookmark data.")

(defvar bm-regexp-history nil
  "Bookmark regexp history.")

(defvar bm-annotation-history nil
  "Bookmark annotation history.")

(defvar bm-bookmark-context-size 16
  "The size of context stored, before and after, for each bookmark.")

(defvar bm-wrapped nil
  "State variable to support wrapping.")
(make-variable-buffer-local 'bm-wrapped)

(defconst bm-show-buffer-name "*bm-bookmarks*"
  "The name of the buffer used to show bookmarks by `bm-show'.")

(defvar bm-marker 'bm-marker-left
  "Fringe marker side. Left of right.")

(defvar bm-current nil)

;; avoid errors on emacs running in a terminal
(when (fboundp 'define-fringe-bitmap)
  (define-fringe-bitmap 'bm-marker-left   [#x00 #x00 #xFC #xFE #x0F #xFE #xFC #x00])
  (define-fringe-bitmap 'bm-marker-right  [#x00 #x00 #x3F #x7F #xF0 #x7F #x3F #x00]))


(defun bm-customize nil
  "Customize bm group."
  (interactive)
  (customize-group 'bm))


(defun bm-bookmark-annotate (&optional bookmark annotation)
  "Annotate bookmark at point or the BOOKMARK specified as parameter.

If ANNOTATION is provided use this, and not prompt for input."
  (interactive)
  (if (null bookmark)
      (setq bookmark (bm-bookmark-at (point))))

  (if (bm-bookmarkp bookmark)
      (progn
        (if (null annotation)
            (setq annotation (read-from-minibuffer "Annotation: " nil nil nil 'bm-annotation-history)))
        (overlay-put bookmark 'annotation annotation))
    (if (called-interactively-p 'interactive) (message "No bookmark at point"))))


(defun bm-bookmark-show-annotation (&optional bookmark)
  "Show annotation for bookmark.
Either the bookmark at point or the BOOKMARK specified as parameter."
  (interactive)
  (if (null bookmark)
      (setq bookmark (bm-bookmark-at (point))))

  (if (bm-bookmarkp bookmark)
      (message (or (overlay-get bookmark 'annotation)
                   "No annotation for current bookmark."))
    (message "No bookmark at current line.")))

(defun bm-highlight-line ()
  "Test if line is highlighted."
  (or (equal bm-highlight-style 'bm-highlight-only-line)
      (equal bm-highlight-style 'bm-highlight-line-and-fringe)))

(defun bm-highlight-fringe ()
  "Test if fringe is highlighted."
  (or (equal bm-highlight-style 'bm-highlight-only-fringe)
      (equal bm-highlight-style 'bm-highlight-line-and-fringe)))

(defun bm-get-highlight-face nil
  "Get the correct face according to the value of `bm-buffer-presistence'."
  (if bm-buffer-persistence bm-persistent-face bm-face))

(defun bm-get-highlight-face-fringde nil
  "Get the correct fringde face according to the value of `bm-buffer-presistence'."
  (if bm-buffer-persistence bm-fringe-persistent-face bm-fringe-face))

(defun bm-get-fringe-marker nil
  "Get the fringde marker string."
  (let ((marker-string "*fringe-dummy*"))
    (put-text-property 0 (length marker-string) 'display
                       (list (if (eq bm-marker 'bm-marker-left)
                                 'left-fringe
                               'right-fringe)
                             bm-marker (bm-get-highlight-face-fringde))
                       marker-string)
    marker-string))


(defun bm-bookmark-add (&optional annotation time temporary-bookmark)
  "Add bookmark at current line.

If ANNOTATION is provided use this, and do not prompt for input.
Only used if `bm-annotate-on-create' is true.

TIME is useful when `bm-in-lifo-order' is not nil. 

if TEMPORARY-BOOKMARK not nil,the bookmark will be removed
when `bm-next' or `bm-previous' navigate to this bookmark."
  (let((bookmark (bm-bookmark-at (point))))
    (if bookmark
        (progn (setq bm-current bookmark)
               (overlay-put bookmark 'position (point-marker))
               (overlay-put bookmark 'time (or time (float-time))))
      (let ((bookmark (make-overlay (bm-start-position) (bm-end-position)))
            (hlface (if bm-buffer-persistence bm-persistent-face bm-face))
            (hlface-fringe (if bm-buffer-persistence bm-fringe-persistent-face bm-fringe-face)))
        ;; set market
        (overlay-put bookmark 'time (or time (float-time)))
        (overlay-put bookmark 'temporary-bookmark
                     (if temporary-bookmark t temporary-bookmark-p))
        (overlay-put bookmark 'position (point-marker))
        ;; select bookmark face
        (when (bm-highlight-line)
          (overlay-put bookmark 'face hlface))
        (overlay-put bookmark 'evaporate t)
        (overlay-put bookmark 'category 'bm)
        (when (bm-highlight-fringe)
          (overlay-put bookmark 'before-string (bm-get-fringe-marker)))
        (if (or bm-annotate-on-create annotation)
            (bm-bookmark-annotate bookmark annotation))
        (unless (featurep 'xemacs)
          ;; gnu emacs specific features
          (overlay-put bookmark 'priority bm-priority)
          (overlay-put bookmark 'modification-hooks '(bm-freeze))
          (overlay-put bookmark 'insert-in-front-hooks '(bm-freeze-in-front))
          (overlay-put bookmark 'insert-behind-hooks '(bm-freeze)))
        (setq bm-current bookmark)
        bookmark))))


(defun bm-bookmark-remove (&optional bookmark)
  "Remove bookmark at point or the BOOKMARK specified as parameter."
  (if (null bookmark)
      (setq bookmark (bm-bookmark-at (point))))

  (if (bm-bookmarkp bookmark)
      (delete-overlay bookmark)))


;;;###autoload
(defun bm-toggle nil
  "Toggle bookmark at point."
  (interactive)
  (let ((bookmark (bm-bookmark-at (point))))
    (if bookmark
        (bm-bookmark-remove bookmark)
      (bm-bookmark-add))))


;;;###autoload
(defun bm-toggle-mouse (ev)
  "Toggle a bookmark with a mouse click.
EV is the mouse event."
  (interactive "e")
  (save-excursion
    (mouse-set-point ev)
    (bm-toggle)))


(defun bm-count nil
  "Count the number of bookmarks in buffer."
  (let ((bookmarks (bm-lists t 'bm-bookmark-is-visible)))
    (+ (length (car bookmarks)) (length (cdr bookmarks)))))


(defun bm-start-position nil
  "Return the bookmark start position."
  (point-at-bol))


(defun bm-end-position nil
  "Return the bookmark end position."
  (min (point-max) (+ 1 (point-at-eol))))


(defun bm-freeze-in-front (overlay after begin end &optional len)
  "Prevent overlay from being extended to multiple lines.
When inserting in front of overlay move overlay forward.

OVERLAY the overlay being modified.
AFTER nil when called before, t when called after modification.
BEGIN the beginning of the text being modified.
END the end of the text being modified.
When called after, the length of the modification is passed as LEN.

See Overlay Properties in the Emacs manual for more information:
http://www.gnu.org/s/emacs/manual/html_node/elisp/Overlay-Properties.html"
  (if after
      (move-overlay overlay (bm-start-position) (bm-end-position))))


(defun bm-freeze (overlay after begin end &optional len)
  "Prevent OVERLAY from being extended to multiple lines.
When inserting inside or behind the overlay, keep the original start postion.

OVERLAY the overlay being modified.
AFTER nil when called before, t when called after modification.
BEGIN the beginning of the text being modified.
END the end of the text being modified.
When called after, the length of the modification is passed as LEN.

See Overlay Properties in the Emacs manual for more information:
http://www.gnu.org/s/emacs/manual/html_node/elisp/Overlay-Properties.html"
  (if after
      (let ((bm-start (overlay-start overlay)))
        (if bm-start
            (move-overlay overlay
                          bm-start
                          (save-excursion
                            (goto-char bm-start)
                            (bm-end-position)))))))


(defun bm-equal (first second)
  "Compare two bookmarks. Return t if FIRST is equal to SECOND."
  (if (and (bm-bookmarkp first) (bm-bookmarkp second))
      (= (overlay-start first) (overlay-start second))
    nil))


(defun bm-bookmarkp (bookmark)
  "Return the BOOKMARK if overlay is a bookmark."
  (if (and (overlayp bookmark)
           (overlay-buffer bookmark)
           (string= (overlay-get bookmark 'category) "bm"))
      bookmark
    nil))

(defun bm-bookmark-is-visible (bookmark)
  "Return the BOOKMARK if the BOOKMARK is in the visible part of the buffer."
  (if (and (bm-bookmarkp bookmark)
           (>= (overlay-start bookmark) (point-min))
           (<= (overlay-end bookmark) (point-max)))
      bookmark
    nil))


(defun bm-bookmark-at (point)
  "Get bookmark at POINT."
  (let ((overlays (overlays-at point))
        (bookmark nil))
    (while (and (not bookmark) overlays)
      (if (bm-bookmarkp (car overlays))
          (setq bookmark (car overlays))
        (setq overlays (cdr overlays))))
    bookmark))


(defun bm-lists (&optional direction predicate)
  "Return a pair of lists giving all the bookmarks of the current buffer.
The car has all the bookmarks before the overlay center;
the cdr has all the bookmarks after the overlay center.
A bookmark implementation of `overlay-lists'.

If optional argument DIRECTION is provided, only return bookmarks
in the specified direction.

If optional argument PREDICATE is provided, it is used as a
selection criteria for filtering the lists."
  (if (null predicate)
    (setq predicate 'bm-bookmarkp))
  
  (overlay-recenter (point))
  (cond ((equal 'forward direction)
         (cons nil (remq nil (mapcar predicate (cdr (overlay-lists))))))
        ((equal 'backward direction)
         (cons (remq nil (mapcar predicate (car (overlay-lists)))) nil))
        (t
         (cons (remq nil (mapcar predicate (car (overlay-lists))))
               (remq nil (mapcar predicate (cdr (overlay-lists))))))))

(defun bm-overlay-in-buffer()
  "overlays in current buffer"
  (let ((bookmarks (bm-lists)))
    (append
     ;; xemacs has the list sorted after buffer position, while
     ;; gnu emacs list is sorted relative to current position.
     (if (featurep 'xemacs)
         (car bookmarks)
       (reverse (car bookmarks)))
     (cdr bookmarks))))

(defun bm-overlay-all()
  "overlays in all buffer"
  (cl-mapcan (lambda (x) (if (listp x) x nil))
             (remq
              nil  (mapcar #'(lambda (buffer)
                               (with-current-buffer buffer
                                 (bm-overlay-in-buffer))
                               )(buffer-list)))))

(defun bm-overlays-lifo-order(&optional all reverse)
  (sort  (if all
             (bm-overlay-all)
           (bm-overlay-in-buffer))
         #'(lambda(o1 o2)
             (if reverse
                 (< (overlay-get o1 'time) (overlay-get o2 'time))
               (> (overlay-get o1 'time) (overlay-get o2 'time))))))


(defun bm-find-lifo-next(&optional reverse)
  (let ((sorted-bm-list (bm-overlays-lifo-order bm-cycle-all-buffers reverse))
        ret)
    (setq ret (cl-loop with next   for i in sorted-bm-list
                    until  (bm-equal  bm-current i) do (setq next i)
                    finally return next))
    (if ret ret
      (car (last (bm-overlays-lifo-order bm-cycle-all-buffers reverse))))))

;;;###autoload
(defun bm-lifo-previous()
  "Goto previous bookmark in LIFO order . (that is, most
recently set ones come first, oldest ones come last)"
  (interactive)
  (let ((sorted-bm-list (bm-overlays-lifo-order bm-cycle-all-buffers t))
        next)
    (cond ((null sorted-bm-list)
           (message "no next bookmark"))
          ((or (null bm-current) (not (member bm-current sorted-bm-list)))
           (switch-to-buffer (overlay-buffer (car sorted-bm-list)))
           (bm-goto (car sorted-bm-list))
           (setq bm-current  (car (last sorted-bm-list))))
          (t
           (switch-to-buffer (overlay-buffer bm-current))
           (bm-goto bm-current)
           (setq bm-current (bm-find-lifo-next t))))))

;;;###autoload
(defun bm-lifo-next()
  "Goto next bookmark in LIFO order .(that is, most
recently set ones come first, oldest ones come last)"
  (interactive)
  (let ((sorted-bm-list (bm-overlays-lifo-order bm-cycle-all-buffers))
        next)
    (cond ((null sorted-bm-list)
           (message "no next bookmark"))
          ((or (null bm-current) (not (member bm-current sorted-bm-list)))
           (switch-to-buffer (overlay-buffer (car sorted-bm-list)))
           (bm-goto (car sorted-bm-list))
           (setq bm-current  (car (last sorted-bm-list))))
          (t
           (switch-to-buffer (overlay-buffer bm-current))
           (bm-goto bm-current)
           (setq bm-current (bm-find-lifo-next))))))

;;;###autoload
(defun bm-next nil
  (interactive)
  (if bm-in-lifo-order
      (bm-lifo-next)
    (bm-common-next)))

;;;###autoload
(defun bm-common-next nil
  "Goto next bookmark."
  (interactive)
  (let ((bm-list-forward (cdr (bm-lists 'forward 'bm-bookmark-is-visible))))
    ;; remove bookmark at point
    (if (bm-equal (bm-bookmark-at (point)) (car bm-list-forward))
        (setq bm-list-forward (cdr bm-list-forward)))

    (if bm-list-forward
        (bm-goto (car bm-list-forward))
      (cond (bm-cycle-all-buffers (bm-first-in-next-buffer))
            (bm-wrap-search (bm-wrap-forward))
            (t (message "No next bookmark."))))))

(defun bm-wrap-forward nil
  "Goto next bookmark, wrapping."
  (if (= (bm-count) 0)
      (message "No next bookmark.")
    (if (or bm-wrapped bm-wrap-immediately)
        (progn
          (message "Wrapped.")
          (bm-first))
      (setq bm-wrapped t)       ; wrap on next goto
      (message "No next bookmark."))))


;;;###autoload
(defun bm-next-mouse (ev)
  "Go to the next bookmark with the scroll wheel.
EV is the mouse event."
  (interactive "e")
  (let ((old-selected-window (selected-window)))
    (select-window (posn-window (event-start ev)))
    (bm-next)
    (select-window old-selected-window)))

;;;###autoload
(defun bm-previous nil
  (interactive)
  (if bm-in-lifo-order
      (bm-lifo-previous)
    (bm-common-previous)))

;;;###autoload
(defun bm-common-previous nil
  "Goto previous bookmark."
  (interactive)
  (let ((bm-list-backward (car (bm-lists 'backward 'bm-bookmark-is-visible))))
    ;; remove bookmark at point
    (if (bm-equal (bm-bookmark-at (point)) (car bm-list-backward))
        (setq bm-list-backward (cdr bm-list-backward)))

    (if bm-list-backward
        (bm-goto (car bm-list-backward))

      (cond (bm-cycle-all-buffers (bm-last-in-previous-buffer))
            (bm-wrap-search (bm-wrap-backward))
            (t (message "No previous bookmark."))))))

(defun bm-wrap-backward nil
  "Goto previous bookmark, wrapping."
  (if (= (bm-count) 0)
      (message "No previous bookmark.")
    (if (or bm-wrapped bm-wrap-immediately)
        (progn
          (message "Wrapped.")
          (bm-last))
      (setq bm-wrapped t)       ; wrap on next goto
      (message "No previous bookmark."))))


;;;###autoload
(defun bm-previous-mouse (ev)
  "Go to the previous bookmark with the scroll wheel.
EV is the mouse event."
  (interactive "e")
  (let ((old-selected-window (selected-window)))
    (select-window (posn-window (event-start ev)))
    (bm-previous)
    (select-window old-selected-window)))


(defun bm-first-in-next-buffer nil
  "Goto first bookmark in next buffer."
  (interactive)
  (let ((current (current-buffer))
        (buffers
         (save-excursion
           (remq nil (mapcar #'(lambda (buffer)
                                 (set-buffer buffer)
                                 (if (> (bm-count) 0)
                                     buffer
                                   nil))
                             ;; drop current buffer from list
                             (cdr (buffer-list)))))))

    (if buffers
        (progn
          (switch-to-buffer (car buffers))
          (bury-buffer current)
          (message "Switched to '%s'" (car buffers))
          (bm-first))
      ;; no bookmarks found in other open buffers,
      ;; wrap in current buffer?
      (if bm-wrap-search
          (bm-wrap-forward)
        (message "No bookmarks found in other open buffers.")))))


(defun bm-last-in-previous-buffer nil
  "Goto last bookmark in previous buffer."
  (interactive)
  (let ((buffers
         (save-excursion
           (remq nil (mapcar #'(lambda (buffer)
                                 (set-buffer buffer)
                                 (if (> (bm-count) 0)
                                     buffer
                                   nil))
                             ;; drop current buffer from list
                             (reverse (cdr (buffer-list))))))))

    (if buffers
        (progn
          (switch-to-buffer (car buffers))
          (message "Switched to '%s'" (car buffers))
          (bm-last))
      ;; no bookmarks found in other open buffers,
      ;; wrap in current buffer?
      (if bm-wrap-search
          (bm-wrap-backward)
        (message "No bookmarks found in other open buffers.")))))


(defun bm-first nil
  "Goto first bookmark in buffer."
  (let ((bookmark (bm-bookmark-at (point-min))))
    (if bookmark
        ;; display correct behaviour even when standing on a bookmark
        (bm-goto bookmark)
      (goto-char (point-min))
      (bm-next))))


(defun bm-last nil
  "Goto last bookmark in buffer."
  (let ((bookmark (bm-bookmark-at (point-max))))
    (if bookmark
        ;; display correct behaviour even when standing on a bookmark
        (bm-goto bookmark)
      (goto-char (point-max))
      (bm-previous))))


(defun bm-remove-all-all-buffers nil
  "Delete all visible bookmarks in all open buffers."
  (interactive)
  (save-excursion
    (mapcar #'(lambda (buffer)
                (set-buffer buffer)
                (bm-remove-all-current-buffer))
            (buffer-list))))


(defun bm-remove-all-current-buffer nil
  "Delete all visible bookmarks in current buffer."
  (interactive)
  (let ((bookmarks (bm-lists t 'bm-bookmark-is-visible)))
    (mapc 'bm-bookmark-remove (append (car bookmarks) (cdr bookmarks)))))


(defun bm-toggle-wrapping nil
  "Toggle wrapping on/off, when searching for next/previous bookmark."
  (interactive)
  (setq bm-wrap-search (not bm-wrap-search))
  (if bm-wrap-search
      (message "Wrapping on.")
    (message "Wrapping off.")))


(defun bm-toggle-cycle-all-buffers nil
  "Toggle searching across all buffers."
  (interactive)
  (setq bm-cycle-all-buffers (not bm-cycle-all-buffers))
  (if bm-cycle-all-buffers
      (message "Cycle all buffers on")
    (message "Cycle all buffers off")))


(defun bm-goto (bookmark)
  "Goto specified BOOKMARK."
  (if (bm-bookmarkp bookmark)
      (progn
        (if bm-goto-position
            (goto-char (max
                        ;; sometimes marker-position is before start of overlay
                        ;; marker is not updated when overlay hooks are called.
                        (overlay-start bookmark)
                        (marker-position (overlay-get bookmark 'position))))
          (goto-char (overlay-start bookmark)))
        (setq bm-wrapped nil)           ; turn off wrapped state
        (if bm-recenter
            (recenter))
        (let ((annotation (overlay-get bookmark 'annotation)))
          (if annotation
              (message annotation)))
        (when  (overlay-get bookmark 'temporary-bookmark)
          (bm-bookmark-remove  bookmark)))
    (message "Bookmark not found.")))


(defun bm-bookmark-regexp nil
  "Set bookmark on lines that match regexp."
  (interactive)
  (bm-bookmark-regexp-region (point-min) (point-max)))


(defun bm-bookmark-regexp-region (beg end)
  "Set bookmark on lines that match regexp in region.
Region defined by BEG and END."
  (interactive "r")
  (let ((regexp (read-from-minibuffer
                 "regexp: " nil nil nil 'bm-regexp-history))
        (annotation nil)
        (count 0))
    (save-excursion
      (if bm-annotate-on-create
          (setq annotation (read-from-minibuffer
                            "Annotation: " nil nil nil 'bm-annotation-history)))

      (goto-char beg)
      (while (and (< (point) end)
                  (re-search-forward regexp end t))
        (bm-bookmark-add annotation)
        (setq count (1+ count))
        (forward-line 1)))
    (message "%d bookmark(s) created." count)))


(defun bm-bookmark-line (line)
  "Set a bookmark on the specified LINE."
  (interactive "nSet a bookmark on line: ")
  (let* ((here (point))
         (remaining (progn
                      (goto-char (point-min))
                      (forward-line (1- line)))))
    (if (zerop remaining)
        (bm-bookmark-add)
      (message "Unable to set bookmark at line %d. Only %d lines in the buffer." line (- line remaining 1))
      (goto-char here))))


(defun bm-show-quit-window nil
  "Quit the window displaying `bm-show-buffer-name'."
  (interactive)
  (quit-window nil (get-buffer-window bm-show-buffer-name)))


(defun bm-show-all nil
  "Show bookmarked lines in all buffers."
  (interactive)
  (apply #'bm-show-display-lines
         (bm-show-extract-bookmarks bm-in-lifo-order t)))

(defun bm-show nil
  "Show bookmarked lines in current buffer."
  (interactive)
  (apply #'bm-show-display-lines
         (bm-show-extract-bookmarks bm-in-lifo-order nil)))


(defconst bm-header-buffer-name "File"
  "Header used for the buffer name column in a `bm-show-all'
buffer.")

(defconst bm-header-line "Line"
  "Header used for the line number column in a `bm-show' or
`bm-show-all' buffer.")

(defconst bm-header-annotation "Annotation"
  "Header used for the annotation column in a `bm-show' or
`bm-show-all' buffer.")

(defconst bm-header-contents "Contents"
  "Header used for the bookmarked line contents in a `bm-show' or
`bm-show-all' buffer.")

(defconst bm-annotation-width 20
  "Number of columns used for the annotation column in `bm-show'
or `bm-show-all' results.")

(defun bm-find-file-line-max-width (bookmarks include-buffer-name)
  "Return the width needed to display buffer name and line number.
This is used by `bm-show' and `bm-show-all' to determine how wide
they should make the display of the buffer name and line number
in their buffer.  When INCLUDE-BUFFER-NAME is nil, as it is when
we're called by `bm-show', the buffer name is not taken into
account.  The smallest possible result from this function will be
the combination of the header text separated by a colon,
e.g. 9 for \"File:Line\"."
  (apply #'max
         ;; First consider the header line.
         (if include-buffer-name
                   (+ (length bm-header-buffer-name)
                      ;; +1 for the colon separator.
                      1
                      (length bm-header-line))
                 (length bm-header-line))
         ;; Now consider all the bookmarks.
         (mapcar (lambda (bm)
                   (with-current-buffer (overlay-buffer bm)
                     (let* ((line-number (count-lines (point-min)
                                                      (overlay-start bm)))
                            (line-width
                             (length (number-to-string line-number))))
                       (if include-buffer-name
                           ;; +1 for the colon separator.
                           (+ (length (buffer-name)) 1 line-width)
                         line-width))))
                 bookmarks)))

(defun bm-show-extract-bookmarks (&optional lifo-order all)
  "Return (HEADER BOOKMARK-LIST) for displaying a list of bookmarks.
Both are strings to be used in the bookmark lists provided to
users by the likes of `bm-show' and `bm-show-all'."
  ;; format-non-nil is just like format except it ignores any nil
  ;; arguments.  For example, (format-non-nil "%s %s" "foo" nil "bar")
  ;; yields "foo bar".  This is useful below where we conditionally
  ;; omit annotations.
  ;;
  ;; lstrip strips trailing white space from STR.  lstrip was stolen
  ;; from s.el and
  ;; http://ergoemacs.org/emacs/modernization_elisp_lib_problem.html.
  (cl-flet ((format-non-nil (format-string &rest args)
              (apply #'format format-string (delete nil args)))
            (lstrip (str)
              (if (string-match "\\`[ \t\n\r]+" str)
                  (replace-match "" t t str)
                str)))
    (let* ((bookmarks (if lifo-order
                          (bm-overlays-lifo-order all)
                        (if all (bm-overlay-all)
                          (bm-overlay-in-buffer))))
           (file-line-width (bm-find-file-line-max-width bookmarks all))
           (format-string (concat (format "%%-%ds" file-line-width)
                                  (when bm-show-annotations
                                    (format " %%-%ds" bm-annotation-width))
                                  " %s")))
      (list
       ;; The header
       (format-non-nil format-string
                       (if all
                           (format "%s:%s" bm-header-buffer-name
                                   bm-header-line)
                         bm-header-line)
                       (when bm-show-annotations
                         bm-header-annotation)
                       bm-header-contents)
       ;; The bookmark list
       (mapconcat
        #'(lambda (bm)
            (with-current-buffer (overlay-buffer bm)
              (let* ((line (lstrip (buffer-substring (overlay-start bm)
                                                     (overlay-end bm))))
                     ;; line numbers start on 1
                     (line-num (+ 1 (count-lines (point-min) (overlay-start bm)))) 
                     (string
                      (format-non-nil format-string
                                      (if all
                                          (format "%s:%d" (buffer-name)
                                                  line-num)
                                        line-num)
                                      (when bm-show-annotations
                                        (or (overlay-get bm 'annotation) ""))
                                      (if (string-match "\n$" line)
                                          line
                                        (concat line "\n")))))
                (put-text-property 0 (length string) 'bm-buffer (buffer-name)
                                   string)
                (put-text-property 0 (length string) 'bm-bookmark bm string)
                string)))
        bookmarks
        "")))))


(defun bm-show-display-lines (header lines)
  "Show bookmarked LINES to the `bm-show-buffer-name' buffer."
  (if (= (length lines) 0)
      (message "No bookmarks defined.")
    (with-output-to-temp-buffer bm-show-buffer-name
      (set-buffer standard-output)
      (insert lines)
      (bm-show-mode)
      ;; Can only set header-line-format after bm-show-mode has called
      ;; kill-all-local-variables.  This use of propertize allows the
      ;; header line to line up with the left fringe, thanks
      ;; http://www.emacswiki.org/emacs/HeaderLine!
      (setq header-line-format
            (concat (propertize " " 'display '((space :align-to 0))) header))
      (setq buffer-read-only t)
      (when bm-electric-show
        (pop-to-buffer (current-buffer))))))


(defun bm-show-goto-bookmark nil
  "Goto the bookmark on current line in the `bm-show-buffer-name' buffer."
  (interactive)
  (let ((buffer-name (get-text-property (point) 'bm-buffer))
        (bookmark (get-text-property (point) 'bm-bookmark)))
    (if (null buffer-name)
        (message "No bookmark at this line.")
      (pop-to-buffer (get-buffer buffer-name))
      (bm-goto bookmark)
      (when bm-electric-show (bm-show-quit-window)))))


(defun bm-show-bookmark nil
  "Show the bookmark on current line in the `bm-show-buffer-name' buffer."
  (interactive)
  (let ((buffer-name (get-text-property (point) 'bm-buffer))
        (bookmark (get-text-property (point) 'bm-bookmark)))
    (if (null buffer-name)
        (message "No bookmark at this line.")
      (let ((current-buffer (current-buffer)))
        (pop-to-buffer (get-buffer buffer-name))
        (bm-goto bookmark)
        (pop-to-buffer current-buffer)))))


(defvar bm-show-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") 'bm-show-goto-bookmark)
    (define-key map (kbd "SPC") 'bm-show-bookmark)
    (define-key map (kbd "M-n") 'bm-show-next)
    (define-key map (kbd "M-p") 'bm-show-prev)
    (define-key map "q"         'bm-show-quit-window)
    map)
  "Keymap for `bm-show-mode'.")


(defun bm-show-next (lines)
  "Goto next bookmark in `bm-show' buffer.
LINES the number of lines to move forward."
  (interactive "p")
  (forward-line lines)
  (bm-show-bookmark))


(defun bm-show-prev (lines)
  "Goto previous bookmark in `bm-show' buffer.
LINES the number of lines to move backwards."
  (interactive "p")
  (forward-line (- lines))
  (bm-show-bookmark))


(defun bm-show-mode nil
  "Major mode for `bm-show' buffers."
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'bm-show-mode)
  (setq mode-name "bm-bookmarks")
  (use-local-map bm-show-mode-map))


(defun bm-toggle-buffer-persistence nil
  "Toggle if a buffer has persistent bookmarks or not."
  (interactive)
  (if bm-buffer-persistence
      ;; turn off
      (progn
        (setq bm-buffer-persistence nil)
        (bm-repository-remove (bm-buffer-file-name)) ; remove from repository
        (bm-redraw-bookmarks)
        (message "Bookmarks in buffer are not persistent."))
    ;; turn on
    (if (and (not (file-directory-p bm-repository-file)) (file-writable-p bm-repository-file))
        (if (not (null (bm-buffer-file-name)))
            (progn
              (setq bm-buffer-persistence (not bm-buffer-persistence))
              (bm-buffer-save)			; add to repository
              (bm-redraw-bookmarks)
              (message "Bookmarks in buffer are persistent."))
          (message "Unable to set persistent mode on a non-file buffer."))
      (message "Repository file '%s' not writeable" bm-repository-file))))
    

(defun bm-redraw-bookmarks nil
  "Update color on bookmarks after persistent state has changed."
  (let ((bookmarks (bm-lists)))
    (mapc #'(lambda (bookmark)
              (when (bm-highlight-line)
                (overlay-put bookmark 'face (bm-get-highlight-face)))

              (when (bm-highlight-fringe)
                (overlay-put bookmark 'before-string (bm-get-fringe-marker))))
          (append (car bookmarks) (cdr bookmarks)))))


(defun bm-get-position-from-context (bookmark)
  "Get position of BOOKMARK based on context.
If we find the context before the old bookmark we use it,
otherwise we use the context after."
  (save-excursion
    (let ((point nil)
          (before (cdr (assoc 'before-context-string bookmark)))
          (after (cdr (assoc 'after-context-string bookmark))))

      ;; search forward for context
      (if (and after (search-forward after (point-max) t))
          (progn
            (goto-char (match-beginning 0))
            (setq point (point))))

      ;; search backward for context
      (if (and before (search-backward before (point-min) t))
          (progn
            (goto-char (match-end 0))
            (setq point (point))))
      point)))


(defun bm-buffer-restore nil
  "Restore bookmarks saved in the repository for the current buffer."
  (interactive)
  (let ((buffer-data (assoc (bm-buffer-file-name) bm-repository)))
    (if buffer-data
        (let ((version (cdr (assoc 'version buffer-data))))
          (cond ((= version 2)
                 (bm-buffer-restore-2 buffer-data))
                (t
                 (message "Unknown data format. Version %d" version))))
      (if (called-interactively-p 'interactive) (message "No bookmarks in repository.")))))


(defun bm-buffer-restore-all nil
  "Restore bookmarks in all buffers."
  (save-current-buffer
    (mapc #'(lambda (buffer)
              (set-buffer buffer)
              (bm-buffer-restore))
          (buffer-list))))


(defun bm-buffer-restore-2 (buffer-data)
  "Restore bookmarks from version 2 format.
BUFFER-DATA is the content of `bm-repository-file'."
  (let ((buffer-size-match (equal (point-max) (cdr (assoc 'size buffer-data))))
        (bookmarks (cdr (assoc 'bookmarks buffer-data)))
        (count 0))

    (setq bm-buffer-persistence t) ; enable persistence
    (save-excursion
      (while bookmarks
        (let ((pos (if buffer-size-match
                       (cdr (assoc 'position (car bookmarks)))
                     (bm-get-position-from-context (car bookmarks))))
              (time (assoc 'time buffer-data))
              (temporary-bookmark (assoc 'temporary-bookmark buffer-data))
              (annotation (cdr (assoc 'annotation (car bookmarks)))))

          ;; create bookmark if is inside buffer
          (when (and (<= (point-min) pos)
                     (<= pos (point-max)))
            (goto-char pos)
            (bm-bookmark-add annotation time temporary-bookmark)
            (setq count (1+ count)))
          (setq bookmarks (cdr bookmarks)))))

    (if buffer-size-match
        (message "%d bookmark(s) restored." count)
      (message "%d bookmark(s) restored based on context." count))))


(defun bm-buffer-save nil
  "Save all bookmarks to repository."
  (interactive)
  (if (bm-buffer-file-name)
      (if bm-buffer-persistence
          (save-restriction
            (widen)
            (let ((buffer-data
                   (list
                    (bm-buffer-file-name)
                    (cons 'version bm-bookmark-repository-version)
                    (cons 'size (point-max))
                    (cons 'timestamp (current-time))
                    (cons 'bookmarks
                          (let ((bookmarks (bm-lists)))
                            (mapcar
                             #'(lambda (bm)
                                 (let ((position (marker-position (overlay-get bm 'position))))
                                   (list
                                    (cons 'position position)
                                    (cons 'time (overlay-get bm 'time))
                                    (cons 'temporary-bookmark (overlay-get bm 'temporary-bookmark))
                                    (cons 'annotation (overlay-get bm 'annotation))
                                    (cons 'before-context-string
                                          (let ((context-start
                                                 (max (point-min) (- position bm-bookmark-context-size))))
                                            (buffer-substring-no-properties context-start position)))
                                    (cons 'after-context-string
                                          (let ((context-end
                                                 (min (+ position bm-bookmark-context-size) (point-max))))
                                            (buffer-substring-no-properties position context-end))))))
                             (append (car bookmarks) (cdr bookmarks))))))))

              ;; remove if exists
              (bm-repository-remove (car buffer-data))

              ;; add if there exists bookmarks
              (let ((count (length (cdr (assoc 'bookmarks buffer-data)))))
                (if (> count 0)
                    (bm-repository-add buffer-data))
                (if (called-interactively-p 'interactive)
                    (message "%d bookmark(s) saved to repository." count)))
              ))

        (if (called-interactively-p 'interactive)
            (message "No bookmarks saved. Buffer is not persistent.")))

    (if (called-interactively-p 'interactive)
        (message "Unable to save bookmarks in non-file buffers."))))


(defun bm-buffer-save-all nil
  "Save bookmarks in all buffers."
  (save-current-buffer
    (mapc #'(lambda (buffer)
              (set-buffer buffer)
              (bm-buffer-save))
          (buffer-list))))


(defun bm-repository-add (data)
  "Add DATA for a buffer to the repository."
  ;; appending to list, makes the list sorted by time
  (setq bm-repository (append bm-repository (list data)))

  ;; remove oldest element if repository is too large
  (while (and bm-repository-size
              (> (length bm-repository) bm-repository-size))
    (setq bm-repository (cdr bm-repository))))


(defun bm-repository-remove (key)
  "Remove data for a buffer from the repository identified by KEY."
  (let ((repository nil))
    (when (assoc key bm-repository)
      ;; remove all occurances
      (while bm-repository
        (if (not (equal key (car (car bm-repository))))
            (setq repository (append repository (list (car bm-repository)))))
        (setq bm-repository (cdr bm-repository)))
      (setq bm-repository repository))))


(defun bm-repository-load (&optional file)
  "Load the repository from the FILE specified or to `bm-repository-file'."
  (unless file
    (setq file bm-repository-file))
  (when file
    (condition-case nil
        (setq bm-repository (with-temp-buffer
                              (insert-file-contents file)
                              (goto-char (point-min))
                              (read (current-buffer))))
      (error (message "Cannot read repository at %s" file)))))


(defun bm-repository-save (&optional file)
  "Save the repository to the FILE specified or to `bm-repository-file'."
  (unless file
    (setq file bm-repository-file))
  (when file
    (condition-case nil
        (with-temp-file file
          (set-buffer-file-coding-system 'utf-8)
          (insert ";; bm.el -- persistent bookmarks. ")
          (insert "Do not edit this file.\n")
          (prin1 bm-repository (current-buffer))
          (insert "\n"))
      (error (message "Cannot save repository to %s" file)))))


(defun bm-repository-clear nil
  "Clear the repository."
  (interactive)
  (setq bm-repository nil))


(defun bm-load-and-restore nil
  "Load bookmarks from persistent repository and restore them."
  (interactive)
  (bm-repository-load)
  (bm-buffer-restore-all))


(defun bm-save nil
  "Save bookmarks to persistent repository."
  (interactive)
  (bm-buffer-save-all)
  (bm-repository-save))


(defun bm-buffer-file-name nil
  "Get a unique key for the repository, even for non-file buffers."
  (cond ((equal 'Info-mode major-mode)
         (concat "[info:" Info-current-file "]"))
        ((null (buffer-file-name))
         (concat "[tmp: " (buffer-name) "]"))
        ((not (null (buffer-base-buffer)))
         (concat "[indirect:" (buffer-name) ":" (buffer-file-name (buffer-base-buffer)) "]"))
        (t (buffer-file-name))))


;; restore repository on load
(if bm-restore-repository-on-load
    (bm-repository-load))


(provide 'bm)
;;; bm.el ends here
