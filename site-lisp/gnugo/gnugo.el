;;; gnugo.el --- play GNU Go in a buffer         -*- lexical-binding: t -*-

;; Copyright (C) 2014  Free Software Foundation, Inc.

;; Author: Thien-Thi Nguyen <ttn@gnu.org>
;; Maintainer: Thien-Thi Nguyen <ttn@gnu.org>
;; Version: 3.0.0
;; Package-Requires: ((ascii-art-to-unicode "1.5") (xpm "1.0.1") (cl-lib "0.5"))
;; Keywords: games, processes
;; URL: http://www.gnuvola.org/software/gnugo/

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

;; Playing
;; -------
;;
;; This file provides the command `gnugo' which allows you to play the game of
;; go against the external program "gnugo" (http://www.gnu.org/software/gnugo)
;; in a dedicated Emacs buffer, or to resume a game in progress.  NOTE: In
;; this file, to avoid confusion w/ elisp vars and funcs, we use the term "GNU
;; Go" to refer to the process object created by running the external program.
;;
;; At the start of a new game, you can pass additional command-line arguments
;; to GNU Go to specify level, board size, color, komi, handicap, etc.  By
;; default GNU Go plays at level 10, board size 19, color white, and zero for
;; both komi and handicap.
;;
;; To play a stone, move the cursor to the desired vertice and type `SPC' or
;; `RET'; to pass, `P' (note: uppercase); to quit, `q'; to undo one of your
;; moves (as well as a possibly intervening move by GNU Go), `u'.  To undo
;; back through an arbitrary stone that you played, place the cursor on a
;; stone and type `U' (note: uppercase).
;;
;; There are a great many other commands.  Other keybindings are described in
;; the `gnugo-board-mode' documentation, which you may view with the command
;; `describe-mode' (normally `C-h m') in that buffer.  The buffer name shows
;; the last move and who is currently to play.  Capture counts and other info
;; are shown on the mode line immediately following the major mode name.
;;
;; While GNU Go is pondering its next move, certain commands that rely on its
;; assistence will result in a "still waiting" error.  Do not be alarmed; that
;; is normal.  When it is your turn again you may retry the command.  In the
;; meantime, you can use Emacs for other tasks, or start an entirely new game
;; with `C-u M-x gnugo'.  (NOTE: A new game will slow down all games. :-)
;;
;; If GNU Go should crash during a game the mode line will show "no process".
;; Please report the event to the GNU Go maintainers so that they can improve
;; the program.
;;
;;
;; Meta-Playing (aka Customizing)
;; ------------------------------
;;
;; Customization is presently limited to
;;   vars:            `gnugo-program'
;;                    `gnugo-animation-string'
;;                    `gnugo-mode-line'
;;                    `gnugo-X-face' `gnugo-O-face' `gnugo-grid-face'
;;                    `gnugo-undo-reaction'
;;                    `gnugo-xpms' (see also gnugo-imgen.el)
;;   normal hooks:    `gnugo-board-mode-hook'
;;                    `gnugo-frolic-mode-hook'
;;                    `gnugo-start-game-hook'
;;                    `gnugo-post-move-hook'
;;   and the keymaps: `gnugo-board-mode-map'
;;                    `gnugo-frolic-mode-map'
;;
;;
;; Meta-Meta-Playing (aka Hacking)
;; -------------------------------
;;
;; <http://git.sv.gnu.org/cgit/emacs/elpa.git/tree/packages/gnugo/>

;;; Code:

(require 'cl-lib)                       ; use the source luke!
(require 'time-date)                    ; for `time-subtract'

;;;---------------------------------------------------------------------------
;;; Political arts

(defconst gnugo-version "3.0.0"
  "Version of gnugo.el currently loaded.
This follows a MAJOR.MINOR.PATCH scheme.")

;;;---------------------------------------------------------------------------
;;; Variables for the uninquisitive programmer

(defvar gnugo-program "gnugo"
  "Name of the GNU Go program (executable file).
\\[gnugo] validates this using `executable-find'.
This program must accept command line args:
 --mode gtp --quiet
For more information on GTP and GNU Go, please visit:
<http://www.gnu.org/software/gnugo>")

(defvar gnugo-board-mode-map
  ;; Re <http://lists.gnu.org/archive/html/emacs-devel/2014-04/msg00123.html>,
  ;; ideally we could ‘defvar’ here w/o value and also ‘defvar’ below
  ;; in "load-time actions" w/ value and docstring, to avoid this ugly
  ;; (from the forward references) block early in the file.  Unfortunately,
  ;; byte-compiling such a split formulation results in the initial ‘defvar’
  ;; being replaced by:
  ;;   (defvar VAR (make-sparse-keymap))
  ;; and the second ‘defvar’ is ignored on load.  At least, this is the case
  ;; for Emacs built from repo (trunk) 2014-05-27.  --ttn
  (let ((map (make-sparse-keymap)))
    (suppress-keymap map)
    (mapc (lambda (pair)
            (define-key map (car pair) (cdr pair)))
          '(("?"        . describe-mode)
            ("S"        . gnugo-request-suggestion)
            ("\C-m"     . gnugo-move)
            (" "        . gnugo-move)
            ("P"        . gnugo-pass)
            ("R"        . gnugo-resign)
            ("q"        . gnugo-quit)
            ("Q"        . gnugo-leave-me-alone)
            ("U"        . gnugo-fancy-undo)
            ("\M-u"     . gnugo-undo-one-move)
            ("u"        . gnugo-undo-two-moves)
            ("\C-?"     . gnugo-undo-two-moves)
            ("o"        . gnugo-oops)
            ("O"        . gnugo-okay)
            ("\C-l"     . gnugo-refresh)
            ("\M-_"     . gnugo-boss-is-near)
            ("_"        . gnugo-boss-is-near)
            ("h"        . gnugo-move-history)
            ("L"        . gnugo-frolic-in-the-leaves)
            ("\C-c\C-l" . gnugo-frolic-in-the-leaves)
            ("i"        . gnugo-image-display-mode)
            ("w"        . gnugo-worm-stones)
            ("W"        . gnugo-worm-data)
            ("d"        . gnugo-dragon-stones)
            ("D"        . gnugo-dragon-data)
            ("g"        . gnugo-grid-mode)
            ("!"        . gnugo-estimate-score)
            (":"        . gnugo-command)
            (";"        . gnugo-command)
            ("="        . gnugo-describe-position)
            ("s"        . gnugo-write-sgf-file)
            ("\C-x\C-s" . gnugo-write-sgf-file)
            ("\C-x\C-w" . gnugo-write-sgf-file)
            ("l"        . gnugo-read-sgf-file)
            ("F"        . gnugo-display-final-score)
            ("A"        . gnugo-switch-to-another)
            ("C"        . gnugo-comment)
            ("\C-c\C-a" . gnugo-assist-mode)
            ("\C-c\C-z" . gnugo-zombie-mode)
            ;; mouse
            ([(down-mouse-1)] . gnugo-mouse-move)
            ([(down-mouse-2)] . gnugo-mouse-move) ; mitigate accidents
            ([(down-mouse-3)] . gnugo-mouse-pass)
            ;; delving into the curiosities
            ("\C-c\C-p" . gnugo-describe-internal-properties)))
    map)
  "Keymap for GNUGO Board mode.")

(defvar gnugo-board-mode-hook nil
  "Hook run when entering GNUGO Board mode.")

(defvar gnugo-start-game-hook nil
  "Normal hook run immediately before the first move of the game.
To find out who is to move first, use `gnugo-current-player'.
See also `gnugo-board-mode'.")

(defvar gnugo-post-move-hook nil
  "Normal hook run after a move and before the board is refreshed.
Initially, when `run-hooks' is called, the current buffer is the GNUGO
Board buffer of the game.  Hook functions that switch buffers must take
care not to call (directly or indirectly through some other function)
`gnugo-put' or `gnugo-get' after the switch.")

(defvar gnugo-animation-string
  (let ((jam "*#") (blink " #") (spin "-\\|/") (yada "*-*!"))
    (concat jam jam jam jam jam
            ;; "SECRET MESSAGE HERE"
            blink blink blink blink blink blink blink blink
            ;; Playing go is like fighting ignorance: when you think you have
            ;; surrounded something by knowing it very well it often turns
            ;; out that in the time you spent deepening this understanding,
            ;; other areas of ignorance have surrounded you.
            spin spin spin spin spin spin spin spin spin
            ;; Playing go is not like fighting ignorance: what one person
            ;; knows many people may come to know; knowledge does not build
            ;; solely move by move.  Wisdom, on the other hand...
            yada yada yada))
  "String whose individual characters are used for animation.
Specifically, the commands `gnugo-worm-stones' and `gnugo-dragon-stones'
render the stones in their respective result groups as the first character
in the string, then the next, and so on.")

(defvar gnugo-mode-line "~b ~w :~m :~u"
  "A `mode-line-format'-compliant value for GNUGO Board mode.
If a single string, the following special escape sequences are
replaced with their associated information:
  ~b,~w  black,white captures (a number)
  ~p     current player (black or white)
  ~m     move number
  ~t     time waiting for the current move
  ~u     time taken for the Ultimate (most recent) move
The times are in seconds, or \"-\" if that information is not available.
For ~t, the value is a snapshot, use `gnugo-refresh' to update it.")

(defvar gnugo-X-face 'font-lock-string-face
  "Name of face to use for X (black) stones.")

(defvar gnugo-O-face 'font-lock-builtin-face
  "Name of face to use for O (white) stones.")

(defvar gnugo-grid-face 'default
  "Name of face to use for the grid (A B C ... 1 2 3 ...).")

(defvar gnugo-undo-reaction 'play!
  "What to do if undo (or oops) leaves GNU Go to play.
After `gnugo-undo-one-move', `gnugo-undo-two-moves' or `gnugo-oops',
when GNU Go is to play, this can be a symbol:
 play     -- make GNU Go play (unless in Zombie mode)
 play!    -- make GNU Go play unconditionally (traditional behavior)
 zombie   -- enable Zombie mode (`gnugo-zombie-mode')
 one-shot -- like `zombie' but valid only for the next move
Any other value, or (as a special case) for `gnugo-undo-one-move',
any value other than `zombie', is taken as `one-shot'.  Note that
making GNU Go play will probably result in the recently-liberated
board position becoming re-occupied.")

(defvar gnugo-xpms nil
  "List of 46 ((TYPE . LOCATION) . XPM-IMAGE) forms.
XPM-IMAGE is an image as returned by `create-image' with
inline data (i.e., property :data with string value).

TYPE is a symbol, one of:
 hoshi -- unoccupied position with dot
 empty -- unoccupied position sans dot
 bpmoku, bmoku -- black stone with and sans highlight point
 wpmoku, wmoku -- white stone with and sans highlight point

LOCATION is an integer encoding edge, corner, or center:
 1 2 3
 4 5 6
 7 8 9
For instance, 4 means \"left edge\", 9 means \"bottom right\".

There is only one location for hoshi: center.  The other five
types each have all possible locations.  So (+ 1 (* 9 5)) => 46.

The value can also be a function (satisfying `functionp') that
takes one arg, the size of the board, and returns the appropriate
list of forms.")

;;;---------------------------------------------------------------------------
;;; Variables for the inquisitive programmer

(defconst gnugo-font-lock-keywords
  '(("X" . gnugo-X-face)
    ("O" . gnugo-O-face))
  "Font lock keywords for `gnugo-board-mode'.")

(defvar gnugo-option-history nil)

(defvar gnugo-state nil)                ; hint: C-c C-p

(defvar gnugo-btw nil)

;;;---------------------------------------------------------------------------
;;; Support functions

(defsubst gnugo--mkht (&rest etc)
  (apply 'make-hash-table :test 'eq etc))

(defsubst gnugo--compare-strings (s1 beg1 s2 beg2)
  (compare-strings s1 beg1 nil s2 beg2 nil))

(defun gnugo-put (key value)
  "Associate move/game/board-specific property KEY with VALUE.

There are many properties, each named by a keyword, that record and control
how gnugo.el manages each game.  Each GNUGO Board buffer has its own set
of properties, stored in the hash table `gnugo-state'.  Here we document
some of the more stable properties.  You may wish to use them as part of
a `gnugo-post-move-hook' function, for example.  Be careful to preserve
the current buffer as `gnugo-state' is made into a buffer-local variable.
NOTE: In the following, \"see foo\" actually means \"see foo source or
you may never really understand to any degree of personal satisfaction\".

 :proc -- subprocess named \"gnugo\", \"gnugo<1>\" and so forth

 :diamond -- the part of the subprocess name after \"gnugo\", may be \"\"

 :game-over -- nil until game over at which time its value is set to
               the alist ((live GROUP ...) (dead GROUP ...))

 :sgf-collection -- after a `loadsgf' command, entire parse tree of file,
                    a simple list of one or more gametrees, updated in
                    conjunction w/ :sgf-gametree and :monkey

 :sgf-gametree -- one of the gametrees in :sgf-collection

 :monkey -- vector of two elements:
            MEM, a pointer to one of the branches in the gametree;
            BIDX, the index of the \"current branch\"

 :gnugo-color -- either \"black\" or \"white\"
 :user-color
 :last-mover

 :last-waiting  -- seconds and time value, respectively; see `gnugo-push-move'
 :waiting-start

 :black-captures -- these are strings since gnugo.el doesn't do anything
 :white-captures    w/ the information besides display it in the mode line;
                    gory details in functions `gnugo-propertize-board-buffer'
                    and `gnugo-merge-showboard-results' (almost more effort
                    than they are worth!)

 :display-using-images -- XPMs, to be precise; see functions `gnugo-yy',
                          `gnugo-toggle-image-display' and `gnugo-refresh',
                          as well as gnugo-xpms.el (available elsewhere)

 :all-yy -- list of 46 symbols used as the `category' text property
            (so that their plists, typically w/ property `display' or
            `do-not-display') are consulted by the Emacs display engine;
            46 = 9 places * (4 moku + 1 empty) + 1 hoshi; see functions
            `gnugo-toggle-image-display', `gnugo-yy' and `gnugo-yang'

 :paren-ov -- a pair (left and right) of overlays shuffled about to indicate
              the last move; only one is used when displaying using images

 :last-user-bpos -- board position; keep the hapless human happy

As things stabilize probably more info will be added to this docstring."
  (declare (indent 1))
  (puthash key value gnugo-state))

(defun gnugo-get (key)
  "Return the move/game/board-specific value for KEY.
See `gnugo-put'."
  (gethash key gnugo-state))

(defun gnugo--forget (&rest keys)
  (dolist (key keys)
    (remhash key gnugo-state)))

(defsubst gnugo--tree-mnum (tree)
  (aref tree 1))

(defsubst gnugo--tree-ends (tree)
  (aref tree 0))

(defsubst gnugo--set-tree-ends (tree ls)
  (aset tree 0 (apply 'vector ls))
  (gnugo--tree-ends tree))

(defun gnugo--root-node (&optional tree)
  (aref (or tree (gnugo-get :sgf-gametree))
        2))

(defun gnugo-describe-internal-properties ()
  "Pretty-print `gnugo-state' properties in another buffer.
Handle the big, slow-to-render, and/or uninteresting ones specially."
  (interactive)
  (let ((buf (current-buffer))
        (d (gnugo-get :diamond))
        (acc (cl-loop
              for key being the hash-keys of gnugo-state
              using (hash-values val)
              collect (cons key
                            (cl-case key
                              ((:xpms)
                               (format "hash: %X (%d images)"
                                       (sxhash val)
                                       (length val)))
                              (:sgf-collection
                               (length val))
                              (:sgf-gametree
                               (list (hash-table-count
                                      (gnugo--tree-mnum val))
                                     (gnugo--root-node val)
                                     (gnugo--tree-ends val)))
                              (:monkey
                               (let ((mem (aref val 0)))
                                 (list (aref val 1)
                                       (car mem))))
                              (t val))))))
    (switch-to-buffer (get-buffer-create
                       (format "%s*GNUGO Board Properties*"
                               d)))
    (erase-buffer)
    (emacs-lisp-mode)
    (setq truncate-lines t)
    (save-excursion
      (pp acc
          (current-buffer))
      (goto-char (point-min))
      (let ((rx (format "overlay from \\([0-9]+\\).+\n%s\\s-+"
                        (if (string= "" d)
                            ".+\n"
                          ""))))
        (while (re-search-forward rx nil t)
          (let ((pos (get-text-property (string-to-number (match-string 1))
                                        'gnugo-position buf)))
            (delete-region (+ 2 (match-beginning 0)) (point))
            (insert (format " %S" pos))))))
    (message "%d properties" (length acc))))

(defun gnugo-board-buffer-p (&optional buffer)
  "Return non-nil if BUFFER is a GNUGO Board buffer."
  (eq 'gnugo-board-mode
      (buffer-local-value
       'major-mode
       (or buffer (current-buffer)))))

(defun gnugo-board-user-play-ok-p (&optional buffer)
  "Return non-nil if BUFFER is a GNUGO Board buffer ready for a user move."
  (with-current-buffer (or buffer (current-buffer))
    (and gnugo-state (not (gnugo-get :waiting)))))

(defsubst gnugo--blackp (string)
  (string= "black" string))

(defun gnugo-other (color)
  (if (gnugo--blackp color) "white" "black"))

(defun gnugo-current-player ()
  "Return the current player, either \"black\" or \"white\"."
  (gnugo-other (gnugo-get :last-mover)))

(defsubst gnugo--prop<-color (color)
  (if (gnugo--blackp color) :B :W))

(defun gnugo-gate (&optional in-progress-p)
  (unless (gnugo-board-buffer-p)
    (user-error "Wrong buffer -- try M-x gnugo"))
  (unless (gnugo-get :proc)
    (user-error "No \"gnugo\" process!"))
  (cl-destructuring-bind (&optional color . suggestion)
      (gnugo-get :waiting)
    (when color
      (apply 'user-error
             "%s -- please wait for \"(%s to play)\""
             (if suggestion
                 (list "Still thinking"
                       color)
               (list "Not your turn yet"
                     (gnugo-other color))))))
  (when (and in-progress-p (gnugo-get :game-over))
    (user-error "Sorry, game over")))

(defun gnugo-sentinel (proc string)
  (let ((status (process-status proc)))
    (when (memq status '(exit signal))
      (let ((buf (process-buffer proc)))
        (when (buffer-live-p buf)
          (with-current-buffer buf
            (setq mode-line-process
                  (list " [%s ("
                        (propertize (car (split-string string))
                                    'face 'font-lock-warning-face)
                        ")]"))
            (when (eq proc (gnugo-get :proc))
              (gnugo--forget :proc))))))))

(defun gnugo--begin-exchange (proc filter line)
  (declare (indent 2))                  ; good time, for a rime
                                        ; nice style, for a wile...
  (set-process-filter proc filter)
  (process-send-string proc line)
  (process-send-string proc "\n"))

(defun gnugo--q (fmt &rest args)
  "Send formatted command \"FMT ARGS...\"; wait for / return response.
The response is a string whose first two characters indicate the
status of the command.  See also `gnugo-query'."
  (let ((slow (gnugo-get :waiting))
        (proc (gnugo-get :proc)))
    (when slow
      (user-error "Sorry, still waiting for %s to %s"
                  (car slow) (if (cdr slow)
                                 "receive a suggestion"
                               "play")))
    (process-put proc :incomplete t)
    (process-put proc :srs "")          ; synchronous return stash
    (gnugo--begin-exchange
        proc (lambda (proc string)
               (let ((full (concat (process-get proc :srs)
                                   string)))
                 (process-put proc :srs full)
                 (unless (numberp (gnugo--compare-strings
                                   full (max 0 (- (length full)
                                                  2))
                                   "\n\n" nil))
                   (process-put proc :incomplete nil))))
      (if (null args)
          fmt
        (apply #'format fmt args)))
    (while (process-get proc :incomplete)
      (accept-process-output proc 30))
    (prog1 (substring (process-get proc :srs) 0 -2)
      (process-put proc :srs ""))))

(defsubst gnugo--no-worries (string)
  (= ?= (aref string 0)))

(defun gnugo--q/ue (fmt &rest args)
  (let ((ans (apply 'gnugo--q fmt args)))
    (unless (gnugo--no-worries ans)
      (user-error "%s" ans))
    (substring ans 2)))

(defun gnugo-query (message-format &rest args)
  "Send GNU Go a command formatted with MESSAGE-FORMAT and ARGS.
Return a string that omits the first two characters (corresponding
to the status indicator in the Go Text Protocol).  Use this function
when you are sure the command cannot fail."
  (substring (apply 'gnugo--q message-format args)
             2))

(defun gnugo--nquery (cmd)
  (string-to-number (gnugo-query cmd)))

(defun gnugo-lsquery (message-format &rest args)
  (split-string (apply 'gnugo-query message-format args)))

(defsubst gnugo--count-query (fmt &rest args)
  (length (apply 'gnugo-lsquery fmt args)))

(defsubst gnugo--root-prop (prop &optional tree)
  (cdr (assq prop (gnugo--root-node tree))))

(defun gnugo--set-root-prop (prop value &optional tree)
  (let* ((root (gnugo--root-node tree))
         (cur (assq prop root)))
    (if cur
        (setcdr cur value)
      (push (cons prop value)
            (cdr (last root))))))

(defun gnugo-goto-pos (pos)
  "Move point to board position POS, a letter-number string."
  (goto-char (point-min))
  (forward-line (- (1+ (gnugo-get :SZ))
                   (string-to-number (substring pos 1))))
  (forward-char 1)
  (forward-char (+ (if (= 32 (following-char)) 1 2)
                   (* 2 (- (let ((letter (aref pos 0)))
                             (if (> ?I letter)
                                 letter
                               (1- letter)))
                           ?A)))))

(defun gnugo-f (id)
  (intern (if (symbolp id)
              (symbol-name id)
            id)
          (gnugo-get :obarray)))

(defun gnugo-yang (c)
  (cdr (assq c '((?+ . hoshi)
                 (?. . empty)
                 (?X . (bmoku . bpmoku))
                 (?O . (wmoku . wpmoku))))))

(defun gnugo-yy (yin yang &optional momentaryp)
  (gnugo-f (format "%d-%s"
                   yin (cond ((symbolp yang) yang)
                             (momentaryp (cdr yang))
                             (t (car yang))))))

(defun gnugo-toggle-image-display ()
  (unless (display-images-p)
    (user-error "Display does not support images, sorry"))
  (let ((fresh (if (functionp gnugo-xpms)
                   (funcall gnugo-xpms (gnugo-get :SZ))
                 gnugo-xpms)))
    (unless fresh
      (user-error "Sorry, `gnugo-xpms' unset"))
    (unless (eq fresh (gnugo-get :xpms))
      (gnugo-put :xpms fresh)
      (gnugo--forget :all-yy)))
  (let* ((new (not (gnugo-get :display-using-images)))
         (act (if new 'display 'do-not-display)))
    (mapc (lambda (yy)
            (setcar (symbol-plist yy) act))
          (or (gnugo-get :all-yy)
              (gnugo-put :all-yy
                (prog1 (mapcar (lambda (ent)
                                 (let* ((k (car ent))
                                        (yy (gnugo-yy (cdr k) (car k))))
                                   (setplist yy `(not-yet ,(cdr ent)))
                                   yy))
                               (gnugo-get :xpms))
                  (gnugo-put :imul
                    (image-size (get (gnugo-yy 5 (gnugo-yang ?+))
                                     'not-yet)))))))
    (setplist (gnugo-f 'ispc) (and new '(display (space :width 0))))
    (gnugo-put :highlight-last-move-spec
      (if new
          `(,(lambda (p)
               (get (gnugo-yy (get-text-property p 'gnugo-yin)
                              (get-text-property p 'gnugo-yang)
                              t)
                    'display))
            0 delete-overlay)
        (gnugo-get :default-highlight-last-move-spec)))
    ;; a kludge to be reworked another time perhaps by another gnugo.el lover
    (dolist (group (cdr (assq 'dead (gnugo-get :game-over))))
      (mapc 'delete-overlay (cdar group))
      (setcdr (car group) nil))
    (gnugo-put :mul (if new
                        (gnugo-get :imul)
                      '(1 . 1)))
    (gnugo-put :display-using-images new)))

(define-minor-mode gnugo-grid-mode
  "If enabled, display grid around the board."
  :variable
  ((not (memq :nogrid buffer-invisibility-spec))
   .
   (lambda (bool)
     (funcall (if bool
                  'remove-from-invisibility-spec
                'add-to-invisibility-spec)
              :nogrid)
     (save-excursion (gnugo-refresh)))))

(defun gnugo-propertize-board-buffer ()
  (erase-buffer)
  (insert (substring (gnugo--q "showboard") 3))
  (let* ((grid-props (list 'invisible :nogrid
                           'font-lock-face gnugo-grid-face))
         (%gpad (gnugo-f 'gpad))
         (%gspc (gnugo-f 'gspc))
         (%lpad (gnugo-f 'lpad))
         (%rpad (gnugo-f 'rpad))
         (ispc-props (list 'category (gnugo-f 'ispc) 'rear-nonsticky t))
         (size (gnugo-get :SZ))
         (size-string (number-to-string size)))
    (goto-char (point-min))
    (put-text-property (point) (1+ (point)) 'category (gnugo-f 'tpad))
    (skip-chars-forward " ")
    (put-text-property (1- (point)) (point) 'category %gpad)
    (put-text-property (point) (progn (end-of-line) (point)) 'category %gspc)
    (forward-char 1)
    (add-text-properties (1+ (point-min)) (1- (point)) grid-props)
    (while (looking-at "\\s-*\\([0-9]+\\)[ ]")
      (let* ((row (match-string-no-properties 1))
             (edge (match-end 0))
             (other-edge (+ edge (* 2 size) -1))
             (right-empty (+ other-edge (length row) 1))
             (top-p (string= size-string row))
             (bot-p (string= "1" row)))
        (let* ((nL (- edge 1 (length size-string)))
               (nR (- edge 1))
               (ov (make-overlay nL nR (current-buffer) t)))
          (add-text-properties nL nR grid-props)
          ;; We redundantly set `invisible' in the overlay to workaround
          ;; a display bug whereby text *following* the overlaid text is
          ;; displayed with the face of the overlaid text, but only when
          ;; that text is invisible (i.e., `:nogrid' in invisibility spec).
          ;; This has something to do w/ the bletcherous `before-string'.
          (overlay-put ov 'invisible :nogrid)
          (overlay-put ov 'category %lpad))
        (cl-do ((p edge (+ 2 p)) (ival 'even (if (eq 'even ival) 'odd 'even)))
            ((< other-edge p))
          (let* ((position (format "%c%s" (aref "ABCDEFGHJKLMNOPQRST"
                                                (truncate (- p edge) 2))
                                   row))
                 (yin (let ((A-p (= edge p))
                            (Z-p (= (1- other-edge) p)))
                        (cond ((and top-p A-p) 1)
                              ((and top-p Z-p) 3)
                              ((and bot-p A-p) 7)
                              ((and bot-p Z-p) 9)
                              (top-p 2)
                              (bot-p 8)
                              (A-p 4)
                              (Z-p 6)
                              (t 5))))
                 (yang (gnugo-yang (char-after p))))
            (add-text-properties p (1+ p)
                                 `(gnugo-position
                                   ,position
                                   gnugo-yin
                                   ,yin
                                   gnugo-yang
                                   ,yang
                                   category
                                   ,(gnugo-yy yin yang)
                                   front-sticky
                                   (gnugo-position gnugo-yin))))
          (unless (= (1- other-edge) p)
            (add-text-properties (1+ p) (+ 2 p) ispc-props)
            (put-text-property p (+ 2 p) 'intangible ival)))
        (add-text-properties (1+ other-edge) right-empty grid-props)
        (goto-char right-empty)
        (when (looking-at "\\s-+\\(WH\\|BL\\).*capt.* \\([0-9]+\\).*$")
          (let ((prop (if (string= "WH" (match-string 1))
                          :white-captures
                        :black-captures))
                (beg (match-beginning 2))
                (end (match-end 2)))
            (put-text-property beg end :gnugo-cf (cons (- end beg) prop))
            (gnugo-put prop (match-string-no-properties 2))))
        (end-of-line)
        (put-text-property right-empty (point) 'category %rpad)
        (forward-char 1)))
    (add-text-properties (1- (point)) (point-max) grid-props)
    (skip-chars-forward " ")
    (put-text-property (1- (point)) (point) 'category %gpad)
    (put-text-property (point) (progn (end-of-line) (point))
                       'category %gspc)))

(defun gnugo-merge-showboard-results ()
  (let ((aft (substring (gnugo--q "showboard") 3))
        (adj 1)                         ; string to buffer position adjustment

        (sync "[0-9]* stones$")
        ;; Note: `sync' used to start w/ "[0-9]+", but that is too
        ;; restrictive a condition that fails in the case of:
        ;;
        ;; (before)
        ;;   ... WHITE has captured 1 stones
        ;;                           ^
        ;; (after)
        ;;   ... WHITE has captured 14 stones
        ;;                           ^
        ;;
        ;; where the after count has more digits than the before count,
        ;; but shares the same leading digits.  In this case, the result
        ;; of `compare-strings' points to the SPC following the before
        ;; count (indicated by caret in this example).

        (bef (buffer-substring-no-properties (point-min) (point-max)))
        (bef-start 0) (bef-idx 0)
        (aft-start 0) (aft-idx 0)
        aft-sync-backtrack mis inc cut new very-strange

        (inhibit-read-only t))
    (while (numberp (setq mis (gnugo--compare-strings
                               bef bef-start
                               aft aft-start)))
      (setq aft-sync-backtrack nil
            inc (if (cl-minusp mis)
                    (- (+ 1 mis))
                  (- mis 1))
            bef-idx (+ bef-start inc)
            aft-idx (+ aft-start inc)
            bef-start (if (eq bef-idx (string-match sync bef bef-idx))
                          (match-end 0)
                        (1+ bef-idx))
            aft-start (if (and (eq aft-idx (string-match sync aft aft-idx))
                               (let ((peek (1- aft-idx)))
                                 (while (not (= 32 (aref aft peek)))
                                   (setq peek (1- peek)))
                                 (setq aft-sync-backtrack (1+ peek))))
                          (match-end 0)
                        (1+ aft-idx))
            cut (+ bef-idx adj
                   (if aft-sync-backtrack
                       (- aft-sync-backtrack aft-idx)
                     0)))
      (goto-char cut)
      (if aft-sync-backtrack
          (let* ((asb aft-sync-backtrack)
                 (l-p (get-text-property cut :gnugo-cf))
                 (old-len (car l-p))
                 (capprop (cdr l-p))
                 (keep (text-properties-at cut)))
            (setq new (substring aft asb (string-match " " aft asb)))
            (plist-put keep :gnugo-cf (cons (length new) capprop))
            (gnugo-put capprop new)
            (delete-char old-len)
            (insert (apply 'propertize new keep))
            (cl-incf adj (- (length new) old-len)))
        (setq new (aref aft aft-idx))
        (insert-and-inherit (char-to-string new))
        (let ((yin (get-text-property cut 'gnugo-yin))
              (yang (gnugo-yang new)))
          (add-text-properties cut (1+ cut)
                               `(gnugo-yang
                                 ,yang
                                 category
                                 ,(gnugo-yy yin yang))))
        (delete-char 1)
        ;; do this last to avoid complications w/ font lock
        ;; (this also means we cannot include `intangible' in `front-sticky')
        (when (setq very-strange (get-text-property (1+ cut) 'intangible))
          (put-text-property cut (1+ cut) 'intangible very-strange))))))

(defsubst gnugo--move-prop (node)
  (or (assq :B node)
      (assq :W node)))

(defun gnugo--as-pos-func ()
  (let ((size (gnugo-get :SZ)))
    ;; rv
    (lambda (cc)
      (if (string= "" cc)
          "PASS"
        (let ((col (aref cc 0)))
          (format "%c%d"
                  (+ ?A (- (if (> ?i col) col (1+ col)) ?a))
                  (- size (- (aref cc 1) ?a))))))))

(defsubst gnugo--resignp (string)
  (string= "resign" string))

(defsubst gnugo--passp (string)
  (string= "PASS" string))

(defun gnugo-move-history (&optional rsel color)
  "Determine and return the game's move history.
Optional arg RSEL controls side effects and return value.
If nil, display the history in the echo area as \"(N moves)\"
followed by the space-separated list of moves.  When called
interactively with a prefix arg (i.e., RSEL is (4)), display
similarly, but suffix with the mover (either \":B\" or \":W\").
RSEL may also be a symbol that selects what to return:
 car  -- the most-recent move
 cadr -- the next-to-most-recent move
 two  -- the last two moves as a list, oldest last
 bpos -- the last stone on the board placed by COLOR
For all other values of RSEL, do nothing and return nil."
  (interactive "P")
  (let* ((monkey (gnugo-get :monkey))
         (mem (aref monkey 0))
         (as-pos (gnugo--as-pos-func))
         acc node mprop move)
    (cl-flet*
        ((as-pos-maybe (x) (if (gnugo--resignp x)
                               x
                             (funcall as-pos x)))
         (remem () (setq node (pop mem)
                         mprop (gnugo--move-prop node)))
         (next (byp) (when (remem)
                       (setq move (as-pos-maybe (cdr mprop)))
                       (push (if byp
                                 (format "%s%s" move (car mprop))
                               move)
                             acc)))
         (nn () (next nil))
         (tell () (message "(%d moves) %s"
                           (length acc)
                           (mapconcat 'identity (nreverse acc) " ")))
         (finish (byp) (while mem (next byp)) (tell)))
      (pcase rsel
        (`(4) (finish t))
        (`nil (finish nil))
        (`car        (car (nn)))
        (`cadr  (nn) (car (nn)))
        (`two (nn) (nn) acc)
        (`bpos (cl-loop
                with prop = (gnugo--prop<-color color)
                while mem
                when (and (remem)
                          (eq prop (car mprop))
                          (setq move (cdr mprop))
                          ;; i.e., "normal CC" position
                          (= 2 (length move)))
                return (funcall as-pos move)))
        (_ nil)))))

(defun gnugo-boss-is-near ()
  "Do `bury-buffer' until the current one is not a GNU Board."
  (interactive)
  (while (gnugo-board-buffer-p)
    (bury-buffer)))

(defsubst gnugo--no-regrets (monkey ends)
  (eq (aref ends (aref monkey 1))
      (aref monkey 0)))

(defun gnugo--as-cc-func ()
  (let ((size (gnugo-get :SZ)))
    (lambda (pos)
      (let* ((col (aref pos 0))
             (one (+ ?a (- col (if (< ?H col) 1 0) ?A)))
             (two (+ ?a (- size (string-to-number
                                 (substring pos 1))))))
        (format "%c%c" one two)))))

(defun gnugo--decorate (node &rest plist)
  (cl-loop
   with tp = (last node)
   with fruit
   while plist
   do (setf
       fruit (list (cons                ; DWR: LtR OoE assumed.
                    (pop plist)
                    (pop plist)))
       (cdr tp) fruit
       tp       fruit)))

(defun gnugo-close-game (end-time resign)
  (gnugo-put :game-end-time end-time)
  (let ((now (or end-time (current-time))))
    (gnugo-put :scoring-seed (logior (ash (logand (car now) 255) 16)
                                     (cadr now))))
  (gnugo-put :game-over
    (if (or (eq t resign)
            (and (stringp resign)
                 (string-match "[BW][+][Rr]esign" resign)))
        (cl-flet
            ((ls (color) (mapcar
                          (lambda (x)
                            (cons (list color)
                                  (split-string x)))
                          (split-string
                           (gnugo-query "worm_stones %s" color)
                           "\n"))))
          (let ((live (append (ls "black") (ls "white"))))
            `((live ,@live)
              (dead))))
      (let ((dd (gnugo-query "dragon_data"))
            (start 0) mem color ent live dead)
        (while (string-match "\\(.+\\):\n[^ ]+[ ]+\\(black\\|white\\)\n"
                             dd start)
          (setq mem (match-string 1 dd)
                color (match-string 2 dd)
                start (match-end 0)
                ent (cons (list color)
                          (sort (gnugo-lsquery "dragon_stones %s" mem)
                                'string<)))
          (string-match "\nstatus[ ]+\\(\\(ALIVE\\)\\|[A-Z]+\\)\n"
                        dd start)
          (if (match-string 2 dd)
              (push ent live)
            (push ent dead))
          (setq start (match-end 0)))
        `((live ,@live)
          (dead ,@dead))))))

(defun gnugo--unclose-game ()
  (gnugo--forget :game-over             ; all those in -close-game
                 :scoring-seed
                 :game-end-time)
  (let* ((root (gnugo--root-node))
         (cur (assq :RE root)))
    (when cur
      (cl-assert (not (eq cur (car root))) nil
                 ":RE at head of root node: %S"
                 root)
      (delq cur root))))

(defun gnugo-push-move (who move)
  (let* ((simple (booleanp who))
         (ucolor (gnugo-get :user-color))
         (color (if simple
                    (if who
                        ucolor
                      (gnugo-get :gnugo-color))
                  who))
         (start (gnugo-get :waiting-start))
         (now (current-time))
         (resignp (gnugo--resignp move))
         (passp (gnugo--passp move))
         (head (gnugo-move-history 'car))
         (onep (and head (gnugo--passp head)))
         (donep (or resignp (and onep passp))))
    (unless resignp
      (gnugo--q/ue "play %s %s" color move))
    (unless passp
      (gnugo-merge-showboard-results))
    (gnugo-put :last-mover color)
    (when (if simple
              who
            (string= ucolor color))
      (gnugo-put :last-user-bpos (and (not passp) (not resignp) move)))
    ;; update :sgf-gametree and :monkey
    (let* ((property (gnugo--prop<-color color))
           (pair (cons property (cond (resignp move)
                                      (passp "")
                                      (t (funcall (gnugo--as-cc-func)
                                                  move)))))
           (fruit (list pair))
           (monkey (gnugo-get :monkey))
           (mem (aref monkey 0))
           (tip (car mem))
           (tree (gnugo-get :sgf-gametree))
           (ends (gnugo--tree-ends tree))
           (mnum (gnugo--tree-mnum tree))
           (count (length ends))
           (tip-move-num (gethash tip mnum))
           (bidx (aref monkey 1)))
      ;; Detect déjà-vu.  That is, when placing "A", avoid:
      ;;
      ;;   X---Y---A         new
      ;;        \
      ;;         --A---B     old
      ;;
      ;; (such "variations" do not actually vary!) in favor of:
      ;;
      ;;   X---Y---A         new
      ;;            \
      ;;             --B     old
      ;;
      ;; This linear search loses for multiple ‘old’ w/ "A",
      ;; a very unusual (but not invalid, sigh) situation.
      (cl-loop
       with (bx previous)
       for i
       ;; Start with latest / highest likelihood for hit.
       ;; (See "to the right" comment, below.)
       from (if (gnugo--no-regrets monkey ends)
                1
              0)
       below count
       if (setq bx (mod (+ bidx i) count)
                previous
                (cl-loop
                 with node
                 for m on (aref ends bx)
                 while (< tip-move-num
                          (gethash (setq node (car m))
                                   mnum))
                 if (eq mem (cdr m))
                 return (when (equal pair (assq property node))
                          m)
                 finally return nil))
       ;; yes => follow
       return
       (progn
         (unless (= bidx bx)
           (cl-rotatef (aref ends bidx)
                       (aref ends bx)))
         (setq mem previous))
       ;; no => construct
       finally do
       (progn
         (unless (gnugo--no-regrets monkey ends)
           (setq ends (gnugo--set-tree-ends
                       tree (let ((ls (append ends nil)))
                              ;; copy old to the right of new
                              (push mem (nthcdr bidx ls))
                              ls))))
         (puthash fruit (1+ (gethash tip mnum)) mnum)
         (push fruit mem)
         (aset ends bidx mem)))
      (setf (aref monkey 0) mem))
    (when start
      (gnugo-put :last-waiting (cadr (time-subtract now start))))
    (when donep
      (gnugo-close-game now resignp))
    (gnugo-put :waiting-start (and (not donep) now))
    donep))

(defun gnugo-venerate (yin yang)
  (let* ((fg-yy (gnugo-yy yin yang))
         (fg-disp (or (get fg-yy 'display)
                      (get fg-yy 'do-not-display)))
         (fg-props (cdr fg-disp))
         (fg-data (plist-get fg-props :data))
         (c-symbs (plist-get fg-props :color-symbols))
         (bg-yy (gnugo-yy yin (gnugo-yang ?.)))
         (bg-disp (or (get bg-yy 'display)
                      (get bg-yy 'do-not-display)))
         (bg-data (plist-get (cdr bg-disp) :data))
         (bop (lambda (s)
                (let* ((start 0)
                       (ncolors
                        (when (string-match "\\([0-9]+\\)\\s-+[0-9]+\"," s)
                          (setq start (match-end 0))
                          (string-to-number (match-string 1 s)))))
                  (while (and (not (cl-minusp ncolors))
                              (string-match ",\n" s start))
                    (setq start (match-end 0)
                          ncolors (1- ncolors)))
                  (string-match "\"" s start)
                  (match-end 0))))
         (new (copy-sequence fg-data))
         (lx (length fg-data))
         (sx (funcall bop fg-data))
         (sb (funcall bop bg-data))
         (color-key (aref new sx)))     ; blech, heuristic
    (while (< sx lx)
      (when (and (not (= color-key (aref new sx)))
                 (cl-plusp (random 4)))
        (aset new sx (aref bg-data sb)))
      (cl-incf sx)
      (cl-incf sb))
    (apply 'create-image new 'xpm t
           :ascent 'center (when c-symbs
                             (list :color-symbols
                                   c-symbs)))))

(defun gnugo-refresh (&optional nocache)
  "Update GNUGO Board buffer display.
While a game is in progress, parenthesize the last-played stone (no parens
for pass).  If the buffer is currently displayed in the selected window,
recenter the board (presuming there is extra space in the window).  Update
the mode line.  Lastly, move point to the last position played by the user,
if that move was not a pass.

Prefix arg NOCACHE requests complete reconstruction of the display, which may
be slow.  (This should normally be unnecessary; specify it only if the display
seems corrupted.)  NOCACHE is silently ignored when GNU Go is thinking about
its move."
  (interactive "P")
  (let* ((move (gnugo-move-history 'car))
         (game-over (gnugo-get :game-over))
         (inhibit-read-only t)
         window last)
    (when (and nocache (not (gnugo-get :waiting)))
      (gnugo-propertize-board-buffer))
    ;; last move
    (when move
      (cl-destructuring-bind (l-ov . r-ov) (gnugo-get :paren-ov)
        (if (member move '("PASS" "resign"))
            (mapc 'delete-overlay (list l-ov r-ov))
          (gnugo-goto-pos move)
          (let* ((p (point))
                 (hspec (gnugo-get :highlight-last-move-spec))
                 (display-value (nth 0 hspec))
                 (l-offset (nth 1 hspec))
                 (l-new-pos (+ p l-offset))
                 (r-action (nth 2 hspec)))
            (overlay-put l-ov 'display
                         (if (functionp display-value)
                             (funcall display-value p)
                           display-value))
            (move-overlay l-ov l-new-pos (1+ l-new-pos))
            (if r-action
                (funcall r-action r-ov)
              (move-overlay r-ov (+ l-new-pos 2) (+ l-new-pos 3)))))))
    ;; buffer name
    (rename-buffer (concat (gnugo-get :diamond)
                           (if game-over
                               (format "%s(game over)"
                                       (if (gnugo--resignp move)
                                           (concat move "ation ")
                                         ""))
                             (format "%s(%s to play)"
                                     (if move (concat move " ") "")
                                     (gnugo-current-player)))))
    ;; pall of death
    (when game-over
      (let ((live (cdr (assq 'live game-over)))
            (dead (cdr (assq 'dead game-over)))
            p pall)
        (unless (eq game-over (get-text-property 1 'game-over))
          (dolist (group (append live dead))
            (dolist (pos (cdr group))
              (gnugo-goto-pos pos)
              (setq p (point))
              (put-text-property p (1+ p) 'group group)))
          (put-text-property 1 2 'game-over game-over))
        (dolist (group live)
          (when (setq pall (cdar group))
            (mapc 'delete-overlay pall)
            (setcdr (car group) nil)))
        (dolist (group dead)
          (unless (cdar group)
            (let (ov pall c (color (caar group)))
              (setq c (if (gnugo--blackp color) "x" "o"))
              (dolist (pos (cdr group))
                (gnugo-goto-pos pos)
                (setq p (point) ov (make-overlay p (1+ p)))
                (overlay-put
                 ov 'display
                 (if (gnugo-get :display-using-images)
                     ;; respect the dead individually; it takes more time
                     ;; but that's not a problem (for them)
                     (gnugo-venerate (get-text-property p 'gnugo-yin)
                                     (gnugo-yang (aref (upcase c) 0)))
                   (propertize c 'face 'font-lock-warning-face)))
                (push ov pall))
              (setcdr (car group) pall))))))
    ;; window update
    (when (setq window (get-buffer-window (current-buffer)))
      (let* ((gridp (not (memq :nogrid buffer-invisibility-spec)))
             (size (gnugo-get :SZ))
             (under10p (< size 10))
             (mul (gnugo-get :mul))
             (h (- (truncate (- (window-height window)
                                (* size (cdr mul))
                                (if gridp 2 0))
                             2)
                   (if gridp 0 1)))
             (edges (window-edges window))
             (right-w-edge (nth 2 edges))
             (avail-width (- right-w-edge (nth 0 edges)))
             (wmul (car mul))
             (imagesp (symbol-plist (gnugo-f 'ispc)))
             (w (/ (- avail-width
                      (* size wmul)
                      (if imagesp
                          0
                        (1- size))
                      2                 ; between board and grid
                      (if gridp
                          (if under10p 2 4)
                        0))
                   2.0)))
        (dolist (pair `((tpad . ,(if (and h (cl-plusp h))
                                     `(display ,(make-string h 10))
                                   '(invisible :nogrid)))
                        (gpad . (display
                                 (space :align-to
                                        ,(+ w
                                            2.0
                                            (cond (imagesp (+ (* 0.5 wmul)
                                                              (if under10p
                                                                  -0.5
                                                                0.5)))
                                                  (under10p 0)
                                                  (t 1))))))
                        (gspc . ,(when imagesp
                                   `(display
                                     (space-width
                                      ,(-
                                        ;; DWR: image width alone => OBOE!
                                        ;;- wmul
                                        ;; NB: ‘(* wmul cw)’ is the same
                                        ;; as ‘(car (image-size ... t))’.
                                        (let ((cw (frame-char-width)))
                                          (/ (+ 1.0 (* wmul cw))
                                             cw))
                                        1.0)))))
                        (lpad . ,(let ((d `(display (space :align-to ,w))))
                                   ;; We distinguish between these cases to
                                   ;; workaround a display bug whereby the
                                   ;; `before-string' is omitted entirely (not
                                   ;; rendered) when interacting w/ the text
                                   ;; mode last-move left-paren for moves in
                                   ;; column A.
                                   (if gridp
                                       `(before-string
                                         ,(apply 'propertize " " d))
                                     d)))
                        (rpad . (display
                                 (space :align-to ,(1- avail-width))))))
          (setplist (gnugo-f (car pair)) (cdr pair)))))
    ;; mode line update
    (let ((cur (gnugo-get :mode-line)))
      (unless (equal cur gnugo-mode-line)
        (setq cur gnugo-mode-line)
        (gnugo-put :mode-line cur)
        (gnugo-put :mode-line-form
          (cond ((stringp cur)
                 (setq cur (copy-sequence cur))
                 (let (acc cut c)
                   (while (setq cut (string-match "~[bwpmtu]" cur))
                     (aset cur cut ?%)
                     (setq c (aref cur (cl-incf cut)))
                     (aset cur cut ?s)
                     (push
                      `(,(intern (format "squig-%c" c))
                        ,(cl-case c
                           (?b '(or (gnugo-get :black-captures) 0))
                           (?w '(or (gnugo-get :white-captures) 0))
                           (?p '(gnugo-current-player))
                           (?t '(let ((ws (gnugo-get :waiting-start)))
                                  (if ws
                                      (cadr (time-since ws))
                                    "-")))
                           (?u '(or (gnugo-get :last-waiting) "-"))
                           (?m '(let ((tree (gnugo-get :sgf-gametree))
                                      (monkey (gnugo-get :monkey)))
                                  (gethash (car (aref monkey 0))
                                           (gnugo--tree-mnum tree)
                                           ;; should be unnecessary
                                           "?")))))
                      acc))
                   `(let ,(delete-dups (copy-sequence acc))
                      (format ,cur ,@(reverse (mapcar 'car acc))))))
                (t cur))))
      (let ((form (gnugo-get :mode-line-form)))
        (setq mode-line-process
              (and form
                   ;; this dynamicism is nice but excessive in its wantonness
                   ;;- `(" [" (:eval ,form) "]")
                   ;; this dynamicism is ok because the user triggers it
                   (format " [%s]" (eval form)))))
      (force-mode-line-update))
    ;; last user move
    (when (setq last (gnugo-get :last-user-bpos))
      (gnugo-goto-pos last))))

(defun gnugo--turn-the-wheel (&optional now)
  (unless (gnugo-get :waiting)
    (let ((color (gnugo-current-player))
          (wheel (gnugo-get :wheel)))
      (setcar wheel
              (when (and (not (gnugo-get :game-over))
                         (member color (cdr wheel)))
                (run-at-time
                 (if now
                     nil
                   2) ;;; sec (frettoloso? dubioso!)
                 nil
                 (lambda (buf color wheel)
                   (setcar wheel nil)
                   (with-current-buffer buf
                     (gnugo-get-move color)))
                 (current-buffer)
                 color wheel))))))

(defun gnugo--finish-move (&optional now)
  (let ((buf (current-buffer)))
    (run-hooks 'gnugo-post-move-hook)
    (set-buffer buf))
  (gnugo-refresh)
  (gnugo--turn-the-wheel now))

;;;---------------------------------------------------------------------------
;;; Game play actions

(defun gnugo--rename-buffer-portion (&optional back)
  (let ((old "to play")
        (new "waiting for suggestion"))
    (when back
      (cl-rotatef old new))
    (let ((name (buffer-name)))
      (when (string-match old name)
        (rename-buffer (replace-match new t t name))))))

(defun gnugo--display-suggestion (color suggestion)
  (message "%sSuggestion for %s: %s"
           (gnugo-get :diamond)
           color suggestion))

(defun gnugo-get-move-insertion-filter (proc string)
  (with-current-buffer (process-buffer proc)
    (let* ((so-far (gnugo-get :get-move-string))
           (full   (gnugo-put :get-move-string (concat so-far string))))
      (when (string-match "^= \\(.+\\)\n\n" full)
        (setq full (match-string 1 full)) ; POS or "PASS"
        (cl-destructuring-bind (color . suggestion)
            (gnugo-get :waiting)
          (gnugo--forget :get-move-string
                         :waiting)
          (if suggestion
              (progn
                (gnugo--rename-buffer-portion t)
                (unless (or (gnugo--passp full)
                            (eq 'nowarp suggestion))
                  (gnugo-goto-pos full))
                (gnugo--display-suggestion color full))
            (gnugo-push-move color full)
            (gnugo--finish-move)))))))

(defun gnugo-get-move (color &optional suggestion)
  (gnugo-put :waiting (cons color suggestion))
  (gnugo--begin-exchange
      (gnugo-get :proc) 'gnugo-get-move-insertion-filter
    ;; We used to use ‘genmove’ here, but that forced asymmetry in
    ;; downstream handling, an impediment to GNU Go vs GNU Go fun.
    (concat "reg_genmove " color))
  (accept-process-output))

(defun gnugo-cleanup ()
  (when (gnugo-board-buffer-p)
    (unless (zerop (buffer-size))
      (message "Thank you for playing GNU Go."))
    (setq gnugo-state nil)))

(defun gnugo-position ()
  (or (get-text-property (point) 'gnugo-position)
      (user-error "Not a proper position point")))

(defun gnugo-request-suggestion (&optional nowarp)
  "Request a move suggestion from GNU Go.
After some time (during which you can do other stuff),
Emacs displays the suggestion in the echo area and warps the
cursor to the suggested position.  Prefix arg inhibits warp."
  (interactive "P")
  (gnugo-gate t)
  (gnugo--rename-buffer-portion)
  (gnugo-get-move (gnugo-current-player)
                  (if nowarp
                      'nowarp
                    t)))

(defun gnugo--karma (color)             ; => BOOL
  (when (member color (cdr (gnugo-get :wheel)))
    t))

(defsubst gnugo--:karma (role)
  (gnugo--karma (gnugo-get role)))

(defun gnugo--assist-state (&optional gate)
  (let ((bool (gnugo--:karma :user-color)))
    (if (and bool gate)
        (user-error "Sorry, Assist mode enabled")
      bool)))

(defun gnugo--user-play (pos-or-pass)
  (gnugo-gate t)
  ;; The "user" in this func's name used to signify both
  ;; who does the action and for whom the action is done.
  ;; Now, it signifies only the former.
  (let ((color (gnugo-current-player)))
    ;; Don't get confused by mixed signals.
    (when (gnugo--karma color)
      (if (equal color (gnugo-get :one-shot))
          (gnugo--forget :one-shot)
        (user-error "Sorry, you cannot play for %s at this time"
                    color)))
    (gnugo-push-move color pos-or-pass))
  (gnugo--finish-move t))

(defun gnugo-move ()
  "Make a move on the GNUGO Board buffer.
The position is computed from current point.
Signal error if done out-of-turn or if game-over.
To start a game try M-x gnugo."
  (interactive)
  (gnugo--user-play (gnugo-position)))

(defun gnugo-mouse-move (e)
  "Do `gnugo-move' at mouse location."
  (interactive "@e")
  (mouse-set-point e)
  (when (memq (following-char) '(?. ?+))
    (gnugo-move)))

(defun gnugo-pass ()
  "Make a pass on the GNUGO Board buffer.
Signal error if done out-of-turn or if game-over.
To start a game try M-x gnugo."
  (interactive)
  (gnugo--user-play "PASS"))

(defun gnugo-mouse-pass (e)
  "Do `gnugo-pass' at mouse location."
  (interactive "@e")
  (mouse-set-point e)
  (gnugo-pass))

(defun gnugo-resign ()
  (interactive)
  (gnugo-gate t)
  (if (not (y-or-n-p "Resign? "))
      (message "(not resigning)")
    (gnugo-push-move t "resign")
    (gnugo-refresh)))

(defun gnugo-animate-group (w/d)
  ;; W/D is a symbol, either ‘worm’ or ‘dragon’.
  (gnugo-gate)
  (let* ((pos (gnugo-position))
         (orig-b-m-p (buffer-modified-p))
         blurb stones)
    (unless (memq (following-char) '(?X ?O))
      (user-error "No stone at %s" pos))
    (setq blurb (message "Computing %s stones ..." w/d)
          stones (gnugo-lsquery "%s_stones %s" w/d pos))
    (message "%s %s in group." blurb (length stones))
    (setplist (gnugo-f 'anim) nil)
    (let* ((spec (if (gnugo-get :display-using-images)
                     (cl-loop
                      with yin  = (get-text-property (point) 'gnugo-yin)
                      with yang = (gnugo-yang (following-char))
                      with up   = (get (gnugo-yy yin yang t) 'display)
                      with dn   = (get (gnugo-yy yin yang) 'display)
                      for n below (length gnugo-animation-string)
                      collect (if (zerop (logand 1 n))
                                  dn up))
                   (split-string gnugo-animation-string "" t)))
           (cell (list spec))
           (ovs (save-excursion
                  (mapcar (lambda (pos)
                            (gnugo-goto-pos pos)
                            (let* ((p (point))
                                   (ov (make-overlay p (1+ p))))
                              (overlay-put ov 'category (gnugo-f 'anim))
                              (overlay-put ov 'priority most-positive-fixnum)
                              ov))
                          stones))))
      (setplist (gnugo-f 'anim) (cons 'display cell))
      (while (and (cdr spec)            ; let last linger lest levity lost
                  (sit-for 0.08675309)) ; jenny jenny i got your number...
        (setcar cell (setq spec (cdr spec)))
        ;; Force redisplay of overlays.
        (set-buffer-modified-p orig-b-m-p))
      (sit-for 5)
      (mapc 'delete-overlay ovs)
      t)))

(defun gnugo-display-group-data (command buffer-name)
  (gnugo-gate)
  (message "Computing %s ..." command)
  (let ((data (gnugo--q "%s %s" command (gnugo-position))))
    (switch-to-buffer buffer-name)
    (erase-buffer)
    (insert data))
  (message "Computing %s ... done." command))

(defun gnugo-worm-stones ()
  "In the GNUGO Board buffer, animate \"worm\" at current position.
Signal error if done out-of-turn or if game-over.
See variable `gnugo-animation-string' for customization."
  (interactive)
  (gnugo-animate-group 'worm))

(defun gnugo-worm-data ()
  "Display in another buffer data from \"worm\" at current position.
Signal error if done out-of-turn or if game-over."
  (interactive)
  (gnugo-display-group-data "worm_data" "*gnugo worm data*"))

(defun gnugo-dragon-stones ()
  "In the GNUGO Board buffer, animate \"dragon\" at current position.
Signal error if done out-of-turn or if game-over.
See variable `gnugo-animation-string' for customization."
  (interactive)
  (gnugo-animate-group 'dragon))

(defun gnugo-dragon-data ()
  "Display in another buffer data from \"dragon\" at current position.
Signal error if done out-of-turn or if game-over."
  (interactive)
  (gnugo-display-group-data "dragon_data" "*gnugo dragon data*"))

(defun gnugo-estimate-score ()
  "Display estimated score of a game of GNU Go.
Output includes number of stones on the board and number of stones
captured by each player, and the estimate of who has the advantage (and
by how many stones)."
  (interactive)
  (message "Est.score ...")
  (let ((black (gnugo--count-query "list_stones black"))
        (white (gnugo--count-query "list_stones white"))
        (black-captures (gnugo-query "captures black"))
        (white-captures (gnugo-query "captures white"))
        (est (gnugo-query "estimate_score")))
    ;; might as well update this
    (gnugo-put :black-captures black-captures)
    (gnugo-put :white-captures white-captures)
    (message "Est.score ... B %s %s | W %s %s | %s"
             black black-captures white white-captures est)))

(defun gnugo--ok-file (filename)
  (setq default-directory
        (file-name-directory
         (expand-file-name filename)))
  (set-buffer-modified-p nil))

(defun gnugo-write-sgf-file (filename)
  "Save the game history to FILENAME (even if unfinished).
If FILENAME already exists, Emacs confirms that you wish to overwrite it."
  (interactive "FWrite game as SGF file: ")
  (when (and (file-exists-p filename)
             (not (y-or-n-p "File exists. Continue? ")))
    (user-error "Not writing %s" filename))
  (when (buffer-modified-p)
    ;; take responsibility for our actions
    (gnugo--set-root-prop :AP (cons "gnugo.el" gnugo-version)))
  (gnugo/sgf-write-file (gnugo-get :sgf-collection) filename)
  (gnugo--ok-file filename))

(defun gnugo--dance-dance (karma)
  (cl-destructuring-bind (dance btw)
      (aref [(moshpit " Zombie")
             (classic nil)
             (reverse " Zombie Assist") ; "Assist Zombie"?  no thanks!  :-D
             (stilted " Assist")]
            (cl-flet
                ((try (n prop)
                      (if (member (gnugo-get prop)
                                  karma)
                          n
                        0)))
              (+ (try 2 :user-color)
                 (try 1 :gnugo-color))))
    (gnugo-put :dance dance)            ; pure cruft (for now)
    (setq gnugo-btw btw)))

(defun gnugo--who-is-who (wait play samep)
  (unless samep
    (let ((wheel (gnugo-get :wheel)))
      (when wheel
        (gnugo--dance-dance
         (setcdr wheel (mapcar 'gnugo-other
                               (cdr wheel)))))))
  (message "GNU Go %splays as %s, you as %s (%s)"
           (if samep "" "now ")
           wait play (if samep
                         "as before"
                       "NOTE: this is a switch!")))

(defsubst gnugo--nodep (x)
  (keywordp (caar x)))

(defun gnugo--SZ! (size)
  (gnugo-put :SZ size)
  (gnugo-put :center-position
    (funcall (gnugo--as-pos-func)
             (let ((c (+ -1 ?a (truncate (1+ size) 2))))
               (string c c)))))

(defun gnugo--plant-and-climb (collection &optional sel)
  (gnugo-put :sgf-collection collection)
  (let ((tree (nth (or sel 0) collection)))
    (gnugo-put :sgf-gametree tree)
    (gnugo-put :monkey (vector
                        ;; mem
                        (aref (gnugo--tree-ends tree) 0)
                        ;; bidx
                        0))
    tree))

(defun gnugo-read-sgf-file (filename)
  "Load the first game tree from FILENAME, a file in SGF format."
  (interactive "fSGF file to load: ")
  (when (file-directory-p filename)
    (user-error "Cannot load a directory (try a filename with extension .sgf)"))
  (let (play wait samep coll tree game-over)
    ;; problem: requiring GTP `loadsgf' complicates network subproc support;
    ;; todo: skip it altogether when confident about `gnugo/sgf-create'
    (setq play (gnugo--q/ue "loadsgf %s" (expand-file-name filename))
          wait (gnugo-other play)
          samep (string= (gnugo-get :user-color) play))
    (gnugo-put :last-mover wait)
    (unless samep
      (gnugo-put :gnugo-color wait)
      (gnugo-put :user-color play))
    (setq coll (gnugo/sgf-create filename)
          tree (gnugo--plant-and-climb
                coll (let ((n (length coll)))
                       ;; This is better:
                       ;; (if (= 1 n)
                       ;;     0
                       ;;   (let* ((q (format "Which game? (1-%d)" n))
                       ;;          (choice (1- (read-number q 1))))
                       ;;     (if (and (< -1 choice) (< choice n))
                       ;;         choice
                       ;;       (message "(Selecting the first game)")
                       ;;       0)))
                       ;; but this is what we use (for now) to accomodate
                       ;; (aka faithfully mimic) GTP `loadsgf' limitations:
                       (unless (= 1 n)
                         (message "(Selecting the first game)"))
                       0)))
    ;; This is deliberately undocumented for now.
    (gnugo--SZ! (gnugo--root-prop :SZ tree))
    (when (setq game-over (or (gnugo--root-prop :RE tree)
                              (when (equal '("PASS" "PASS")
                                           (gnugo-move-history 'two))
                                'two-passes)))
      (gnugo-close-game nil game-over))
    (gnugo-put :last-user-bpos
      (gnugo-move-history 'bpos (gnugo-get :user-color)))
    (gnugo-refresh t)
    (gnugo--ok-file filename)
    (gnugo--who-is-who wait play samep)))

(defun gnugo--mem-with-played-stone (pos &optional noerror)
  (let ((color (cl-case (following-char)
                 (?X :B)
                 (?O :W))))
    (if (not color)
        (unless noerror
          (user-error "No stone at %s" pos))
      (cl-loop
       with fruit = (cons color (funcall (gnugo--as-cc-func) pos))
       for mem on (aref (gnugo-get :monkey) 0)
       when (equal fruit (caar mem))
       return mem
       finally return nil))))

(defun gnugo--climb-towards-root (spec &optional reaction keep)
  (gnugo-gate)
  (gnugo--assist-state t)
  (let* ((user-color (gnugo-get :user-color))
         (monkey (gnugo-get :monkey))
         (tree (gnugo-get :sgf-gametree))
         (ends (gnugo--tree-ends tree))
         (remorseful (not (gnugo--no-regrets monkey ends)))
         (stop (if (numberp spec)
                   (nthcdr (if (zerop spec)
                               (if (string= (gnugo-get :last-mover)
                                            user-color)
                                   1
                                 2)
                             spec)
                           (aref monkey 0))
                 (cdr (gnugo--mem-with-played-stone
                       (if (stringp spec)
                           spec
                         (gnugo-position)))))))
    (when (gnugo-get :game-over)
      (gnugo--unclose-game))
    (while (and (not (eq stop (aref monkey 0)))
                (gnugo--no-worries (gnugo--q "undo")))
      (pop (aref monkey 0))
      (gnugo-put :last-mover (gnugo-current-player))
      (gnugo-merge-showboard-results)   ; all
      (gnugo-refresh)                   ; this
      (redisplay))                      ; eye candy
    (let* ((ulastp (string= (gnugo-get :last-mover) user-color))
           (ubpos (gnugo-move-history (if ulastp 'car 'cadr))))
      (gnugo-put :last-user-bpos (if (and ubpos (not (gnugo--passp ubpos)))
                                     ubpos
                                   (gnugo-get :center-position)))
      (gnugo-refresh t)
      (unless (or keep remorseful)
        (aset ends (aref monkey 1) (aref monkey 0)))
      (when ulastp
        (let ((g (gnugo-get :gnugo-color)))
          (cl-flet ((turn () (gnugo--turn-the-wheel t)))
            (cl-case (or reaction gnugo-undo-reaction)
              (play (turn))
              (play! (let ((wheel (gnugo-get :wheel)))
                       (cl-letf (((cdr wheel) (cons g (cdr wheel))))
                         (turn))))
              (zombie (gnugo-zombie-mode 1))
              (t (gnugo-put :one-shot g)))))))))

(defun gnugo-undo-one-move (&optional me-next)
  "Undo exactly one move (perhaps GNU Go's, perhaps yours).
Do not schedule a move by GNU Go even if it is GNU Go's turn to play.
Prefix arg ME-NEXT means to arrange for you to play
the color of the next move (and GNU Go the opposite).
This is useful after loading an SGF file whose last
move was done by the color you prefer to play:
 \\[gnugo-read-sgf-file] FILENAME RET
 C-u \\[gnugo-undo-one-move]

See also `gnugo-undo-two-moves'."
  (interactive "P")
  (gnugo-gate)
  (when me-next
    (let* ((play (gnugo-get :last-mover))
           (wait (gnugo-other play))
           (samep (string= play (gnugo-get :user-color))))
      (gnugo-put :user-color play)
      (gnugo-put :gnugo-color wait)
      (gnugo--who-is-who wait play samep)))
  (gnugo--climb-towards-root 1 (cl-case gnugo-undo-reaction
                                 (zombie gnugo-undo-reaction)
                                 (t 'one-shot))))

(defun gnugo-undo-two-moves ()
  "Undo a pair of moves (GNU Go's and yours).
However, if you are the last mover, undo only one move.
Regardless, after undoing, it is your turn to play again."
  (interactive)
  (gnugo--climb-towards-root 0))

(defun gnugo-oops (&optional position)
  "Like `gnugo-undo-two-moves', but keep the undone moves.
The kept moves become a sub-gametree (variation) when play resumes.
Prefix arg means, instead, undo repeatedly up to and including
the move which placed the stone at point, like `\\[gnugo-fancy-undo]'."
  (interactive "P")
  (gnugo--climb-towards-root (unless position
                               0)
                             nil t))

(defun gnugo-okay (&optional full)
  "Redo a pair of undone moves.
Prefix arg means to redo all the undone moves."
  (interactive "P")
  (gnugo-gate)
  (let* ((tree (gnugo-get :sgf-gametree))
         (ends (gnugo--tree-ends tree))
         (monkey (gnugo-get :monkey)))
    (if (gnugo--no-regrets monkey ends)
        (message "Oop ack!")
      (let* ((as-pos (gnugo--as-pos-func))
             (mnum (gnugo--tree-mnum tree))
             (mem (aref monkey 0))
             (bidx (aref monkey 1))
             (end (aref ends bidx))
             (ucolor (gnugo-get :user-color))
             (uprop (gnugo--prop<-color ucolor)))
        (cl-flet ((mvno (node) (gethash node mnum)))
          (cl-loop
           with ok = (if full
                         (mvno (car end))
                       (+ 2 (mvno (car mem))))
           with (node move todo)
           for ls on end
           do (progn
                (setq node (car ls)
                      move (gnugo--move-prop node))
                (when (and move (>= ok (mvno node)))
                  (let ((userp (eq uprop (car move))))
                    (push (list userp
                                (funcall as-pos (cdr move)))
                          todo))))
           until (eq mem (cdr ls))
           finally do
           (cl-loop
            for (userp pos) in todo
            do (progn
                 (gnugo-push-move userp pos)
                 (gnugo-refresh)
                 (redisplay)))))))))

(defun gnugo-display-final-score (&optional comment)
  "Display final score and other info in another buffer (when game over).
If the game is still ongoing, Emacs asks if you wish to stop play (by
making sure two \"pass\" moves are played consecutively, if necessary).
Also, add the `:RE' SGF property to the root node of the game tree.
Prefix arg COMMENT means to also attach the text (slightly compacted)
to the last move, as a comment."
  (interactive "P")
  (let ((game-over (gnugo-get :game-over)))
    (unless (or game-over
                (and (not (gnugo-get :waiting))
                     (y-or-n-p "Game still in play. Stop play now? ")))
      (user-error "Sorry, game still in play"))
    (unless game-over
      (cl-flet
          ((pass (userp)
                 (message "Playing PASS for %s ..."
                          (gnugo-get (if userp :user-color :gnugo-color)))
                 (sit-for 1)
                 (gnugo-push-move userp "PASS")))
        (unless (pass t)
          (pass nil)))
      (gnugo-refresh)
      (sit-for 3)))
  (let ((b=  "   Black = ")
        (w=  "   White = ")
        (res (when (gnugo--resignp (gnugo-move-history 'car))
               (gnugo-get :last-mover)))
        blurb result)
    (if res
        (setq blurb (list
                     (format "%s wins.\n"
                             (substring (if (= ?b (aref res 0)) w= b=)
                                        3 8))
                     "The game is over.\n"
                     (format "Resignation by %s.\n" res))
              result (concat (upcase (substring (gnugo-other res) 0 1))
                             "+Resign"))
      (message "Computing final score ...")
      (let* ((g-over (gnugo-get :game-over))
             (live   (cdr (assq 'live g-over)))
             (dead   (cdr (assq 'dead g-over)))
             (seed   (gnugo-get :scoring-seed))
             (terr-q (format "final_status_list %%s_territory %d" seed))
             (terr   "territory")
             (capt   "captures")
             (b-terr (gnugo--count-query terr-q "black"))
             (w-terr (gnugo--count-query terr-q "white"))
             (b-capt (string-to-number (gnugo-get :black-captures)))
             (w-capt (string-to-number (gnugo-get :white-captures)))
             (komi   (gnugo--root-prop :KM)))
        (setq blurb (list "The game is over.  Final score:\n")
              result (gnugo-query "final_score %d" seed))
        (cond ((string= "Chinese" (gnugo--root-prop :RU))
               (dolist (group live)
                 (cl-incf (if (gnugo--blackp (caar group))
                              b-terr
                            w-terr)
                          (length (cdr group))))
               (dolist (group dead)
                 (cl-incf (if (gnugo--blackp (caar group))
                              w-terr
                            b-terr)
                          (length (cdr group))))
               (push (format "%s%d %s = %3.1f\n" b= b-terr terr b-terr) blurb)
               (push (format "%s%d %s + %3.1f %s = %3.1f\n" w=
                             w-terr terr komi 'komi (+ w-terr komi))
                     blurb))
              (t
               (dolist (group dead)
                 (cl-incf (if (gnugo--blackp (caar group))
                              w-terr
                            b-terr)
                          (* 2 (length (cdr group)))))
               (push (format "%s%d %s + %s %s = %3.1f\n" b=
                             b-terr terr
                             b-capt capt
                             (+ b-terr b-capt))
                     blurb)
               (push (format "%s%d %s + %s %s + %3.1f %s = %3.1f\n" w=
                             w-terr terr
                             w-capt capt
                             komi 'komi
                             (+ w-terr w-capt komi))
                     blurb)))
        (push (if (string= "0" result)
                  "The game is a draw.\n"
                (format "%s wins by %s.\n"
                        (substring (if (= ?B (aref result 0)) b= w=) 3 8)
                        (substring result 2)))
              blurb)
        (message "Computing final score ... done")))
    ;; extra info
    (let ((beg (gnugo-get :game-start-time))
          (end (gnugo-get :game-end-time)))
      (when end
        (push "\n" blurb)
        (cl-flet
            ((yep (pretty moment)
                  (push (format-time-string
                         (concat pretty ": %F %T %z\n")
                         moment)
                        blurb)))
          (yep "Game start" beg)
          (yep "       end" end))))
    (setq blurb (apply 'concat (nreverse blurb)))
    (gnugo--set-root-prop :RE result)
    (when comment
      (let ((node (car (aref (gnugo-get :monkey) 0))))
        (gnugo--decorate
         (delq (assq :C node) node)
         :C
         (with-temp-buffer              ; lame
           (insert blurb)
           (when (search-backward "\n\nGame start:" nil t)
             (delete-region (point) (point-max)))
           (cl-flet ((rep (old new)
                          (goto-char (point-min))
                          (while (search-forward old nil t)
                            (replace-match new))))
             (rep "The game is over.  " "")
             (rep "territory" "T")
             (rep "captures"  "C")
             (rep "komi"      "K"))
           (buffer-string)))))
    (switch-to-buffer (format "%s*GNUGO Final Score*" (gnugo-get :diamond)))
    (erase-buffer)
    (insert blurb)))

(defun gnugo-quit ()
  "Kill the current buffer, assumed to be in GNUGO Board mode, maybe.
If the game is not over, ask for confirmation first."
  (interactive)
  (if (or (gnugo-get :game-over)
          (y-or-n-p "Quit? "))
      (kill-buffer nil)
    (message "(not quitting)")))

(defun gnugo-leave-me-alone ()
  "Kill the current buffer unconditionally."
  (interactive)
  (kill-buffer nil))

(defun gnugo-fancy-undo (count)
  "Rewind the game tree in various ways.
Prefix arg COUNT means to undo that many moves.
Otherwise, undo repeatedly up to and including the move
which placed the stone at point."
  (interactive "P")
  (gnugo--climb-towards-root
   (if (numberp count)
       count
     (car-safe count))))

(define-minor-mode gnugo-image-display-mode
  "If enabled, display the board using images.
See function `display-images-p' and variable `gnugo-xpms'."
  :variable
  ((gnugo-get :display-using-images)
   .
   (lambda (bool)
     (unless (eq bool (gnugo-get :display-using-images))
       (gnugo-toggle-image-display)
       (save-excursion (gnugo-refresh))))))

(defsubst gnugo--node-with-played-stone (pos &optional noerror)
  (car (gnugo--mem-with-played-stone pos noerror)))

(defun gnugo-describe-position ()
  "Display the board position under cursor in the echo area.
If there a stone at that position, also display its move number."
  (interactive)
  (let* ((pos (gnugo-position))         ; do first (can throw)
         (node (gnugo--node-with-played-stone pos t)))
    (message
     "%s%s" pos
     (or (when node
           (let* ((tree (gnugo-get :sgf-gametree))
                  (mnum (gnugo--tree-mnum tree))
                  (move-num (gethash node mnum)))
             (format " (move %d)" move-num)))
         ""))))

(defun gnugo-switch-to-another ()
  "Switch to another GNU Go game buffer (if any)."
  (interactive)
  (cl-loop
   for buf in (cdr (buffer-list))
   if (gnugo-board-buffer-p buf)
   return (progn
            (bury-buffer)
            (switch-to-buffer buf))
   finally do (message "(only one)")))

(defun gnugo-comment (node comment)
  "Add to NODE a COMMENT (string) property.
Called interactively, NODE is the one corresponding to the
stone at point, and any previous comment is inserted as the
initial-input (see `read-string').

If COMMENT is nil or the empty string, remove the property entirely."
  (interactive
   (let* ((pos (gnugo-position))
          (node (gnugo--node-with-played-stone pos)))
     (list node
           (read-string (format "Comment for %s: "
                                (gnugo-describe-position))
                        (cdr (assq :C node))))))
  (setq node (delq (assq :C node) node))
  (unless (zerop (length comment))
    (gnugo--decorate node :C comment)))

(defun gnugo--struggle (prop updn)
  (unless (eq updn (gnugo--:karma prop)) ; drudgery avoidance
    (let ((color (gnugo-get prop)))
      (if updn
          ;; enable
          (gnugo-gate)
        ;; disable
        (let ((waiting (gnugo-get :waiting)))
          (when (and waiting (string= color (car waiting)))
            (gnugo--rename-buffer-portion)
            (setcdr waiting
                    ;; heuristic: Warp only if it appears
                    ;; that the user is "following along".
                    (or (ignore-errors
                          (string= (gnugo-position)
                                   (gnugo-move-history 'bpos color)))
                        'nowarp))
            (gnugo--display-suggestion color "forthcoming")
            (sit-for 2))))
      (let* ((wheel (gnugo-get :wheel))
             (timer (car wheel))
             (karma (cdr wheel)))
        (when (timerp timer)
          (cancel-timer timer))
        (setcar wheel nil)
        (setcdr wheel (setq karma
                            ;; walk to the west, fly to the east,
                            ;; talk and then rest, cry and then feast.
                            ;;   99 beers down thirsty throats sloshed?
                            ;;   500 years under pink mountains squashed?
                            ;; balk with the best, child now re-creased!
                            (if updn
                                (push color karma)
                              (delete color karma))))
        (gnugo--dance-dance karma))
      (gnugo--turn-the-wheel t))))

(define-minor-mode gnugo-assist-mode
  "If enabled (\"Assist\" in mode line), GNU Go plays for you.
When disabling, if GNU Go has already started thinking of
a move to play for you, the thinking is not cancelled but instead
transformed into a move suggestion (see `gnugo-request-suggestion')."
  :variable
  ((gnugo--assist-state)
   .
   (lambda (bool)
     (gnugo--struggle :user-color bool))))

(define-minor-mode gnugo-zombie-mode
  "If enabled (\"Zombie\" in mode line), GNU Go lets you play for it.
When disabling, if GNU Go has already started thinking of
a move to play, the thinking is not cancelled but instead
transformed into a move suggestion (see `gnugo-request-suggestion')."
  :variable
  ((not (gnugo--:karma :gnugo-color))
   .
   (lambda (bool)
     (gnugo--struggle :gnugo-color (not bool)))))

;;;---------------------------------------------------------------------------
;;; Command properties and gnugo-command

;; GTP commands entered by the user are never issued directly to GNU Go;
;; instead, their behavior and output are controlled by the property
;; `:gnugo-gtp-command-spec' hung off of each (interned/symbolic) command.
;; The value of this property is a sub-plist, w/ sub-properties as follows:
;;
;; :full -- completely interpret the command string; the value is a
;;          func that takes the list of words derived from splitting the
;;          command string (minus the command) and handles everything.
;;
;; :output -- either a keyword specifying the preferred output method:
;;              :message -- show output in minibuffer
;;              :discard -- sometimes you just don't care;
;;            or a function that takes one arg, the output string, and
;;            handles it completely.   default is to switch to buffer
;;            "*gnugo command output*" if the output has a newline,
;;            otherwise use `message'.
;;
;; :post-thunk -- run after output processing (at the very end).

(defun gnugo-command (command)
  "Send the Go Text Protocol COMMAND (a string) to GNU Go.
Output and Emacs behavior depend on which command is given (some
commands are handled completely by Emacs w/o using the subprocess;
some commands have their output displayed in specially prepared
buffers or in the echo area; some commands are instrumented to do
gnugo.el-specific housekeeping).

For example, for the command \"help\", Emacs visits the
GTP command reference info page.

NOTE: At this time, GTP command handling specification is still
      incomplete.  Thus, some commands WILL confuse gnugo.el."
  (interactive "sCommand: ")
  (if (string= "" command)
      (message "(no command given)")
    (let* ((split (split-string command))
           (cmd (intern (car split)))
           (spec (get cmd :gnugo-gtp-command-spec))
           (full (plist-get spec :full)))
      (if full
          (funcall full (cdr split))
        (message "Doing %s ..." command)
        (let* ((ans (gnugo--q command))
               (where (plist-get spec :output)))
          (if (string-match "unknown.command" ans)
              (message "%s" ans)
            (cond ((functionp where) (funcall where ans))
                  ((eq :discard where) (message ""))
                  ((or (eq :message where)
                       (not (string-match "\n" ans)))
                   (message "%s" ans))
                  (t (switch-to-buffer "*gnugo command output*")
                     (erase-buffer)
                     (insert ans)
                     (message "Doing %s ... done." command)))
            (let ((thunk (plist-get spec :post-thunk)))
              (when thunk (funcall thunk)))))))))

;;;---------------------------------------------------------------------------
;;; Major mode for interacting with a GNUGO subprocess

(define-derived-mode gnugo-board-mode special-mode "GNUGO Board"
  "Major mode for playing GNU Go.
Entering this mode runs the normal hook `gnugo-board-mode-hook'.
In this mode, keys do not self insert."
  (buffer-disable-undo)                 ; todo: undo undo undoing
  (setq font-lock-defaults '(gnugo-font-lock-keywords t)
        truncate-lines t)
  (add-hook 'kill-buffer-hook 'gnugo-cleanup nil t)
  (set (make-local-variable 'gnugo-state)
       (gnugo--mkht :size (1- 42)))
  (set (make-local-variable 'gnugo-btw) nil)
  (add-to-list 'minor-mode-alist '(gnugo-btw gnugo-btw))
  (gnugo-put :highlight-last-move-spec
    (gnugo-put :default-highlight-last-move-spec '("(" -1 nil)))
  (gnugo-put :paren-ov (cons (make-overlay 1 1)
                             (let ((ov (make-overlay 1 1)))
                               (overlay-put ov 'display ")")
                               ov)))
  (gnugo-put :mul '(1 . 1))
  (gnugo-put :obarray (make-vector 31 nil))
  (add-to-invisibility-spec :nogrid))

;;;---------------------------------------------------------------------------
;;; Entry point

;;;###autoload
(defun gnugo (&optional new-game)
  "Run gnugo in a buffer, or resume a game in progress.
If there is already a game in progress you may resume it instead
of starting a new one.  Prefix arg means skip the game-in-progress
check and start a new game straight away.

Before starting, Emacs queries you for additional command-line
options (Emacs supplies \"--mode gtp --quiet\" automatically).

Note that specifying \"--infile FILENAME\" (or, \"-l FILENAME\")
silently clobbers certain other options, such as \"--color\".
For details, see info node `(gnugo) Invoking GNU Go'.

\\<gnugo-board-mode-map>
To play, use \\[gnugo-move] to place a stone or \\[gnugo-pass] to pass.
See `gnugo-board-mode' for a full list of commands."
  (interactive "P")
  (let* ((all (let (acc)
                (dolist (buf (buffer-list))
                  (when (gnugo-board-buffer-p buf)
                    (push (cons (buffer-name buf) buf) acc)))
                acc))
         (n (length all)))
    (if (and (not new-game)
             (cl-plusp n)
             (y-or-n-p (format "GNU Go game%s in progress, resume play? "
                               (if (= 1 n) "" "s"))))
        ;; resume
        (switch-to-buffer
         (cdr (if (= 1 n)
                  (car all)
                (let ((sel (completing-read "Which one? " all nil t)))
                  (if (string= "" sel)
                      (car all)
                    (assoc sel all))))))
      ;; sanity check
      (unless (executable-find gnugo-program)
        (user-error "Invalid `gnugo-program': %S" gnugo-program))
      ;; set up a new board
      (switch-to-buffer (generate-new-buffer "(Uninitialized GNUGO Board)"))
      (gnugo-board-mode)
      (let* ((filename nil)
             (user-color "black")
             (args (cl-loop
                    with ls = (split-string
                               ;; todo: grok ‘gnugo --help’; completion
                               (read-string
                                "GNU Go options: "
                                (car gnugo-option-history)
                                'gnugo-option-history))
                    with ok
                    while ls do
                    (let ((arg (pop ls)))
                      (cl-flet
                          ((ex (opt fn)
                               (if filename
                                   (warn "%s %s ignored" opt fn)
                                 (setq filename fn))))
                        (cond
                         ((string= "--color" arg)
                          (push arg ok)
                          (push
                           ;; Unfortunately, GTP does not provide
                           ;; a way to query the user color, so
                           ;; we must resort to this weirdness.
                           (setq user-color
                                 (pop ls))
                           ok))
                         ((string= "--infile" arg)
                          (ex "--infile" (pop ls)))
                         ((string-match "^-l" arg)
                          (ex "-l" (if (< 2 (length arg))
                                       (substring arg 2)
                                     (pop ls))))
                         (t (push arg ok)))))
                    finally return (nreverse ok)))
             (proc (apply 'start-process "gnugo"
                          (current-buffer)
                          gnugo-program
                          "--mode" "gtp" "--quiet"
                          args))
             root board-size handicap komi)
        (gnugo-put :user-color user-color)
        (gnugo-put :proc proc)
        (set-process-sentinel proc 'gnugo-sentinel)
        ;; Emacs is too protective sometimes, blech.
        (set-process-query-on-exit-flag proc nil)
        (gnugo-put :diamond (substring (process-name proc) 5))
        (gnugo-put :gnugo-color (gnugo-other user-color))
        (if filename
            (gnugo-read-sgf-file (expand-file-name filename))
          (cl-flet
              ((r! (&rest plist) (apply 'gnugo--decorate root plist)))
            (gnugo--SZ!
             (setq root (gnugo--root-node
                         (gnugo--plant-and-climb
                          (gnugo/sgf-create "(;FF[4]GM[1])" t)))
                   komi       (gnugo--nquery "get_komi")
                   handicap   (gnugo--nquery "get_handicap")
                   board-size (gnugo--nquery "query_boardsize")))
            ;; Work around a GNU Go 3.8 (and possibly earlier/later)
            ;; bug whereby GTP command ‘get_handicap’ fails to return
            ;; the N set by ‘--handicap N’ on the command line.
            (let ((actually (member "--handicap" args)))
              ;; Checking ‘(zerop handicap)’ first is not strictly
              ;; necessary; it represents a hope that some day GNU Go
              ;; will DTRT (or provide rationale for this weird behavior)
              ;; and become worthy of our trust.
              (when (and (zerop handicap) actually)
                (setq handicap (string-to-number (cadr actually)))))
            (r! :SZ board-size
                :DT (format-time-string "%F")
                :RU (if (member "--chinese-rules" args)
                        "Chinese"
                      "Japanese")
                :KM komi)
            (let ((ub (gnugo--blackp user-color)))
              (r! (if ub :PW :PB) (concat "GNU Go " (gnugo-query "version"))
                  (if ub :PB :PW) (user-full-name)))
            (unless (zerop handicap)
              (r! :HA handicap
                  :AB (mapcar (gnugo--as-cc-func)
                              (gnugo-lsquery "fixed_handicap %d"
                                             handicap)))))))
      (gnugo-put :waiting-start (current-time))
      (gnugo-refresh t)
      (gnugo-goto-pos (or (gnugo-get :last-user-bpos)
                          (gnugo-get :center-position)))
      ;; first move
      (gnugo-put :game-start-time (current-time))
      (let ((g (gnugo-get :gnugo-color))
            (n (or (gnugo--root-prop :HA) 0))
            (u (gnugo-get :user-color)))
        (unless (gnugo-get :last-mover)
          (gnugo-put :last-mover
            (if (or (and (gnugo--blackp u) (< 1 n))
                    (and (gnugo--blackp g) (< n 2)))
                u
              g)))
        (let ((karma (list g)))
          (gnugo-put :wheel (cons nil karma))
          (gnugo--dance-dance karma))
        (run-hooks 'gnugo-start-game-hook)
        (gnugo--turn-the-wheel)))))

;;;---------------------------------------------------------------------------
;;; Load-time actions

(unless (get 'help :gnugo-gtp-command-spec)
  (cl-flet*
      ((sget (x) (get x :gnugo-gtp-command-spec))
       (jam (cmd prop val) (put cmd :gnugo-gtp-command-spec
                                (plist-put (sget cmd) prop val)))
       (validpos (s &optional go)
                 (let ((pos (upcase s)))
                   (cl-loop
                    with size = (gnugo-get :SZ)
                    for c across (funcall (gnugo--as-cc-func)
                                          pos)
                    do (let ((norm (- c ?a)))
                         (unless (and (< -1 norm)
                                      (> size norm))
                           (user-error "Invalid position: %s"
                                       pos))))
                   (when go
                     (gnugo-goto-pos pos))
                   pos))
       (defgtp (x &rest props) (dolist (cmd (if (symbolp x) (list x) x))
                                 (let ((ls props))
                                   (while ls
                                     (jam cmd (car ls) (cadr ls))
                                     (setq ls (cddr ls)))))))
    (cl-macrolet ((deffull (who &body body)
                    (declare (indent 1))
                    `(defgtp ',who :full (lambda (sel)
                                           ,@body))))

      (deffull help
        (info "(gnugo)GTP command reference")
        (when sel (setq sel (intern (car sel))))
        (let (buffer-read-only pad cur spec output found)
          (cl-flet
              ((note (s) (insert pad "[NOTE: gnugo.el " s ".]\n")))
            (goto-char (point-min))
            (save-excursion
              (while (re-search-forward "^ *[*] \\([a-zA-Z_]+\\)\\(:.*\\)*\n"
                                        nil t)
                (unless pad
                  (setq pad (make-string (- (match-beginning 1)
                                            (match-beginning 0))
                                         32)))
                (when (plist-get
                       (setq spec
                             (get (setq cur (intern (match-string 1)))
                                  :gnugo-gtp-command-spec))
                       :full)
                  (note "handles this command completely"))
                (when (setq output (plist-get spec :output))
                  (if (functionp output)
                      (note "handles the output specially")
                    (cl-case output
                      (:discard (note "discards the output"))
                      (:message (note "displays the output in the echo area")))))
                (when (eq sel cur)
                  (setq found (make-marker))
                  (set-marker found (match-beginning 0))))))
          (cond (found (goto-char found) (set-marker found nil))
                ((not sel))
                (t (message "(no such command: %s)" sel)))))

      (deffull final_score
        ;; Explicit ignorance avoids byte-compiler warning.
        (ignore sel)
        (gnugo-display-final-score))

      (defgtp '(boardsize
                clear_board
                fixed_handicap)
        :output :discard
        :post-thunk (lambda ()
                      (gnugo--unclose-game)
                      (gnugo--forget :last-mover)
                      ;; ugh
                      (gnugo--SZ! (gnugo--nquery "query_boardsize"))
                      (gnugo-refresh t)))

      (deffull loadsgf
        (gnugo-read-sgf-file (car sel)))

      (deffull (undo gg-undo)
        (gnugo--climb-towards-root
         (let (n)
           (cond ((not sel) 1)
                 ((cl-plusp (setq n (string-to-number (car sel)))) n)
                 (t (validpos (car sel) t)))))))))

(provide 'gnugo)


;;;---------------------------------------------------------------------------
;;; The remainder of this file defines a simplified SGF-handling library.
;;; When/if it should start to attain generality, it should be split off into
;;; a separate file (probably named sgf.el) w/ funcs and vars renamed sans the
;;; "gnugo/" prefix.

(defconst gnugo/sgf-*r4-properties*
  '((AB "Add Black"       setup list stone)
    (AE "Add Empty"       game  list point)
    (AN "Annotation"      game  simpletext)
    (AP "Application"     root  (simpletext . simpletext))
    (AR "Arrow"           -     list (point . point))
    (AS "Who adds stones" -     simpletext) ; (LOA)
    (AW "Add White"       setup list stone)
    (B  "Black"           move  move)
    (BL "Black time left" move  real)
    (BM "Bad move"        move  double)
    (BR "Black rank"      game  simpletext)
    (BT "Black team"      game  simpletext)
    (C  "Comment"         -     text)
    (CA "Charset"         root  simpletext)
    (CP "Copyright"       game  simpletext)
    (CR "Circle"          -     list point)
    (DD "Dim points"      -     elist point) ; (inherit)
    (DM "Even position"   -     double)
    (DO "Doubtful"        move  none)
    (DT "Date"            game  simpletext)
    (EV "Event"           game  simpletext)
    (FF "Fileformat"      root  [number (1 . 4)])
    (FG "Figure"          -     (or none (number . simpletext)))
    (GB "Good for Black"  -     double)
    (GC "Game comment"    game  text)
    (GM "Game"            root  [number (1 . 20)])
    (GN "Game name"       game  simpletext)
    (GW "Good for White"  -     double)
    (HA "Handicap"        game  number) ; (Go)
    (HO "Hotspot"         -     double)
    (IP "Initial pos."    game  simpletext) ; (LOA)
    (IT "Interesting"     move  none)
    (IY "Invert Y-axis"   game  simpletext)          ; (LOA)
    (KM "Komi"            game  real)                ; (Go)
    (KO "Ko"              move  none)
    (LB "Label"           -     list (point . simpletext))
    (LN "Line"            -     list (point . point))
    (MA "Mark"            -     list point)
    (MN "set move number" move  number)
    (N  "Nodename"        -     simpletext)
    (OB "OtStones Black"  move  number)
    (ON "Opening"         game  text)
    (OT "Overtime"        game  simpletext)
    (OW "OtStones White"  move  number)
    (PB "Player Black"    game  simpletext)
    (PC "Place"           game  simpletext)
    (PL "Player to play"  setup color)
    (PM "Print move mode" -     number) ; (inherit)
    (PW "Player White"    game  simpletext)
    (RE "Result"          game  simpletext)
    (RO "Round"           game  simpletext)
    (RU "Rules"           game  simpletext)
    (SE "Markup"          -     point)  ; (LOA)
    (SL "Selected"        -     list point)
    (SO "Source"          game  simpletext)
    (SQ "Square"          -     list point)
    (ST "Style"           root  [number (0 . 3)])
    (SU "Setup type"      game  simpletext) ; (LOA)
    (SZ "Size"            root  (or number (number . number)))
    (TB "Territory Black" -     elist point) ; (Go)
    (TE "Tesuji"          move  double)
    (TM "Timelimit"       game  real)
    (TR "Triangle"        -     list point)
    (TW "Territory White" -     elist point) ; (Go)
    (UC "Unclear pos"     -     double)
    (US "User"            game  simpletext)
    (V  "Value"           -     real)
    (VW "View"            -     elist point) ; (inherit)
    (W  "White"           move  move)
    (WL "White time left" move  real)
    (WR "White rank"      game  simpletext)
    (WT "White team"      game  simpletext)
    (LT "Lose on time"    setup simpletext))
  ;; r4-specific notes
  ;; - changed: DT FG LB RE RU SZ
  ;; - added: AP AR AS DD IP IY LN OT PM SE SQ ST SU VW
  "List of SGF[4] properties, each of the form (PROP NAME CONTEXT SPEC...).")

(defun gnugo/sgf-create (file-or-data &optional data-p)
  "Return the SGF[4] collection parsed from FILE-OR-DATA.
FILE-OR-DATA is a file name or SGF[4] data.
Optional arg DATA-P non-nil means FILE-OR-DATA is
a string containing SGF[4] data.
A collection is a list of gametrees, each a vector of four elements:

 ENDS -- a vector of node lists, with shared tails
         (last element of all the lists is the root node)

 MNUM -- `eq' hash: node to move numbers; non-\"move\" nodes
         have a move number of the previous \"move\" node (or zero)

 ROOT -- the root node"
  ;; Arg names inspired by `create-image', despite -P being frowned upon.
  (let ((keywords (or (get 'gnugo/sgf-*r4-properties* :keywords)
                      (put 'gnugo/sgf-*r4-properties* :keywords
                           (mapcar (lambda (full)
                                     (cons (car full)
                                           (intern (format ":%s" (car full)))))
                                   gnugo/sgf-*r4-properties*))))
        (specs (or (get 'gnugo/sgf-*r4-properties* :specs)
                   (put 'gnugo/sgf-*r4-properties* :specs
                        (mapcar (lambda (full)
                                  (cons (car full) (cl-cdddr full)))
                                gnugo/sgf-*r4-properties*))))
        SZ)
    (cl-labels
        ((sw () (skip-chars-forward " \t\n"))
         (x (end preserve-whitespace)
            (let ((beg (point))
                  (endp (cl-case end
                          (:end (lambda (char) (= ?\] char)))
                          (:mid (lambda (char) (= ?\: char)))
                          (t (lambda (char) (or (= ?\: char)
                                                (= ?\] char))))))
                  c)
              (while (not (funcall endp (setq c (following-char))))
                (cond ((= ?\\ c)
                       (delete-char 1)
                       (if (eolp)
                           (kill-line 1)
                         (forward-char 1)))
                      ((unless preserve-whitespace
                         (looking-at "\\s-+"))
                       (delete-region (point) (match-end 0))
                       (insert " "))
                      (t (forward-char 1))))
              (buffer-substring-no-properties beg (point))))
         (one (type end) (let ((s (progn
                                    (forward-char 1)
                                    (x end (eq 'text type)))))
                           (cl-case type
                             ((stone point move)
                              ;; blech, begone bu"tt"-ugly blatherings
                              ;; (but bide brobdingnagian boards)...
                              (if (and (string= "tt" s)
                                       SZ
                                       (>= 19 SZ))
                                  ""
                                s))
                             ((simpletext color) s)
                             ((number real double) (string-to-number s))
                             ((text) s)
                             ((none) "")
                             (t (error "Unhandled type: %S" type)))))
         (val (spec) (cond ((symbolp spec)
                            (one spec :end))
                           ((vectorp spec)
                            ;; todo: check range here.
                            (one (aref spec 0) :end))
                           ((eq 'or (car spec))
                            (let ((v (one (cadr spec) t)))
                              (if (= ?\] (following-char))
                                  v
                                (forward-char 1)
                                ;; todo: this assumes `spec' has the form
                                ;;         (or foo (foo . bar))
                                ;; i.e., foo is not rescanned.  e.g., `SZ'.
                                ;; probably this assumption is consistent
                                ;; w/ the SGF authors' desire to make the
                                ;; parsing easy, but you never know...
                                (cons v (one (cl-cdaddr spec) :end)))))
                           (t (cons (one (car spec) :mid)
                                    (one (cdr spec) :end)))))
         (short (who) (when (eobp)
                        (error "Unexpected EOF while reading %s" who)))
         (atvalp () (= ?\[ (following-char)))
         (PROP () (let (name spec ltype)
                    (sw) (short 'property)
                    (when (looking-at "[A-Z]")
                      (setq name (read (current-buffer))
                            spec (cdr (assq name specs)))
                      (sw)
                      (cons
                       (cdr (assq name keywords))
                       (prog1 (if (= 1 (length spec))
                                  (val (car spec))
                                (unless (memq (setq ltype (car spec))
                                              '(elist list))
                                  (error "Bad spec: %S" spec))
                                (if (and (eq 'elist ltype) (sw)
                                         (not (atvalp)))
                                    nil
                                  (let ((type (cadr spec))
                                        mo ls)
                                    (while (and (sw) (atvalp)
                                                (setq mo (val type)))
                                      (push mo ls)
                                      (forward-char 1))
                                    (forward-char -1)
                                    (nreverse ls))))
                         (forward-char 1))))))
         (morep () (and (sw) (not (eobp))))
         (seek (c) (and (morep) (= c (following-char))))
         (seek-into (c) (when (seek c)
                          (forward-char 1)
                          t))
         (NODE () (when (seek-into ?\;)
                    (cl-loop
                     with prop
                     while (setq prop (PROP))
                     collect (progn
                               (when (eq :SZ (car prop))
                                 (setq SZ (cdr prop)))
                               prop))))
         (TREE (parent mnum)
               (let ((ls parent)
                     prev node)
                 (seek-into ?\()
                 (while (seek ?\;)
                   (setq prev (car ls)
                         node (NODE))
                   (puthash node (+ (if (gnugo--move-prop node)
                                        1
                                      0)
                                    (gethash prev mnum 0))
                            mnum)
                   (push node
                         ls))
                 (prog1
                     (if (not (seek ?\())
                         ;; singular
                         (list ls)
                       ;; multiple
                       (cl-loop
                        while (seek ?\()
                        append (TREE ls mnum)))
                   (seek-into ?\))))))
      (with-temp-buffer
        (if (not data-p)
            (insert-file-contents file-or-data)
          (insert file-or-data)
          (goto-char (point-min)))
        (cl-loop
         while (morep)
         collect (let* ((mnum (gnugo--mkht :weakness 'key))
                        (ends (TREE nil mnum))
                        (root (car (last (car ends)))))
                   (vector (apply 'vector ends)
                           mnum
                           root)))))))

(defun gnugo/sgf-write-file (collection filename)
  (let ((aft-newline-appreciated '(:AP :GN :PB :PW :HA :KM :RU :RE))
        (specs (mapcar (lambda (full)
                         (cons (intern (format ":%s" (car full)))
                               (cl-cdddr full)))
                       gnugo/sgf-*r4-properties*))
        p name v spec)
    (cl-labels
        ((esc (composed fmt arg)
              (mapconcat (lambda (c)
                           (cl-case c
                             ;; ‘?\[’ is not strictly required
                             ;; but neither is it forbidden.
                             ((?\[ ?\] ?\\) (format "\\%c" c))
                             (?: (concat (if composed "\\" "") ":"))
                             (t (string c))))
                         (string-to-list (format fmt arg))
                         ""))
         (>>one (v) (insert "[" (esc nil "%s" v) "]"))
         (>>two (v) (insert "["
                            (esc t "%s" (car v))
                            ":"
                            (esc t "%s" (cdr v))
                            "]"))
         (>>nl () (cond ((memq name aft-newline-appreciated)
                         (insert "\n"))
                        ((< 60 (current-column))
                         (save-excursion
                           (goto-char p)
                           (insert "\n")))))
         (>>prop (prop)
                 (setq p (point)
                       name (car prop)
                       v (cdr prop))
                 (insert (substring (symbol-name name) 1))
                 (cond ((not v))
                       ((and (consp v)
                             (setq spec (cdr (assq name specs)))
                             (memq (car spec)
                                   '(list elist)))
                        (>>nl)
                        (let ((>> (if (consp (cadr spec))
                                      #'>>two
                                    #'>>one)))
                          (dolist (little-v v)
                            (setq p (point))
                            (funcall >> little-v)
                            (>>nl))))
                       ((consp v)
                        (>>two v) (>>nl))
                       (t
                        (>>one v) (>>nl))))
         (>>node (node)
                 (cl-loop
                  initially (insert ";")
                  for prop in node
                  do (>>prop prop)))
         (>>tree (tree)
                 (unless (zerop (current-column))
                   (newline))
                 (insert "(")
                 (dolist (x tree)
                   (funcall (if (gnugo--nodep x)
                                #'>>node
                              #'>>tree)
                            x))
                 (insert ")")))
      (with-temp-buffer
        (dolist (tree collection)
          ;; write it out
          (let ((ht (gnugo--mkht))
                (leaves (append (gnugo--tree-ends tree) nil)))
            (cl-flet
                ((hang (stack)
                       (cl-loop
                        with rh         ; rectified history
                        with bp         ; branch point
                        for node in stack
                        until (setq bp (gethash node ht))
                        do (puthash node
                                    (push node rh) ; good for now: ½τ
                                    ht)
                        finally return
                        (if (not bp)
                            ;; first run: main line
                            rh
                          ;; subsequent runs: grafts (value discarded)
                          (setcdr bp (nconc
                                      ;; Maintain order of ‘leaves’.
                                      (let ((was (cdr bp)))
                                        (if (gnugo--nodep (car was))
                                            (list was)
                                          was))
                                      (list rh)))))))
              (setq tree (hang (pop leaves)))
              (mapc #'hang leaves)
              (>>tree tree))))
        (newline)
        (write-file filename)))))

;;; gnugo.el ends here
