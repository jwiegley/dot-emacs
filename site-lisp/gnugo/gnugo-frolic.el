;;; gnugo-frolic.el --- gametree in a buffer    -*- lexical-binding: t -*-

;; Copyright (C) 2014  Free Software Foundation, Inc.

;; Author: Thien-Thi Nguyen <ttn@gnu.org>
;; Maintainer: Thien-Thi Nguyen <ttn@gnu.org>

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

;;; Code:

(require 'cl-lib)
(require 'gnugo)
(require 'ascii-art-to-unicode)         ; for `aa2u'

(defvar gnugo-frolic-mode-map
  (let ((map (make-sparse-keymap)))
    (suppress-keymap map)
    (mapc (lambda (pair)
            (define-key map (car pair) (cdr pair)))
          '(("q"          . gnugo-frolic-quit)
            ("Q"          . gnugo-frolic-quit)
            ("\C-q"       . gnugo-frolic-quit)
            ("C"          . gnugo-frolic-quit) ; like ‘View-kill-and-leave’
            ("\C-b"       . gnugo-frolic-backward-branch)
            ("\C-f"       . gnugo-frolic-forward-branch)
            ("\C-p"       . gnugo-frolic-previous-move)
            ("\C-n"       . gnugo-frolic-next-move)
            ("t"          . gnugo-frolic-tip-move)
            ("j"          . gnugo-frolic-exchange-left)
            ("J"          . gnugo-frolic-rotate-left)
            ("k"          . gnugo-frolic-exchange-right)
            ("K"          . gnugo-frolic-rotate-right)
            ("\C-m"       . gnugo-frolic-set-as-main-line)
            ("\C-\M-p"    . gnugo-frolic-prune-branch)
            ("o"          . gnugo-frolic-return-to-origin)))
    map)
  "Keymap for GNUGO Frolic mode.")

(defvar gnugo-frolic-parent-buffer nil)
(defvar gnugo-frolic-origin nil)

(define-derived-mode gnugo-frolic-mode special-mode "GNUGO Frolic"
  "A special mode for manipulating a GNUGO gametree."
  (setq truncate-lines t)
  (buffer-disable-undo))

(defun gnugo-frolic-quit ()
  "Kill GNUGO Frolic buffer and switch to its parent buffer."
  (interactive)
  (let ((bye (current-buffer)))
    (switch-to-buffer (when (buffer-live-p gnugo-frolic-parent-buffer)
                        gnugo-frolic-parent-buffer))
    (kill-buffer bye)))

(defun gnugo-frolic-return-to-origin ()
  "Move point to the board's current position."
  (interactive)
  (if (not gnugo-frolic-origin)
      (message "No origin")
    (goto-char gnugo-frolic-origin)
    (recenter (- (count-lines (line-beginning-position)
                              (point-max))))))

;;;###autoload
(defun gnugo-frolic-in-the-leaves ()
  "Display the game tree in a *GNUGO Frolic* buffer.
This looks something like:

  1 B  --  E7    E7    E7    E7
  2 W  --  K10   K10   K10   K10
  3 B  --  E2    E2    E2    E2
  4 W  --  J3    J3    J3    J3
  5 B  --  A6    A6    A6    A6
  6 W  --  C9    C9    C9    C9
           │
           ├─────┬─────┐
           │     │     │
  7 B  --  H7   !B8    C8    C8
                       │
                       ├─────┐
                       │     │
  8 W  --  D9    D9    D9    E9
  9 B  --              H8    H8
 10 W  --              PASS  PASS
 11 B  --              H5    PASS
 12 W  --              PASS
 13 B  --             *PASS

with 0, 1, ... N (in this case N is 3) in the header line
to indicate the branches.  Branch 0 is the \"main line\".
Point (* in this example) indicates the current position,
\"!\" indicates comment properties (e.g., B8, branch 1),
and moves not actually on the game tree (e.g., E7, branch 3)
are dimmed.  Type \\[describe-mode] in that buffer for details."
  (interactive)
  (let* ((buf (get-buffer-create (concat (gnugo-get :diamond)
                                         "*GNUGO Frolic*")))
         (from (or gnugo-frolic-parent-buffer
                   (current-buffer)))
         ;; todo: use defface once we finally succumb to ‘customize’
         (dimmed-node-face (list :inherit 'default
                                 :foreground "gray50"))
         (tree (gnugo-get :sgf-gametree))
         (ends (copy-sequence (gnugo--tree-ends tree)))
         (mnum (gnugo--tree-mnum tree))
         (seen (gnugo--mkht))
         (soil (gnugo--mkht))
         (width (length ends))
         (lanes (number-sequence 0 (1- width)))
         (monkey (gnugo-get :monkey))
         (as-pos (gnugo--as-pos-func))
         (at (car (aref monkey 0)))
         (bidx (aref monkey 1))
         (valid (cl-map 'vector (lambda (end)
                                  (gethash (car end) mnum))
                        ends))
         (max-move-num (apply 'max (append valid nil)))
         (inhibit-read-only t)
         finish)
    (cl-flet
        ((on (node)
             (gethash node seen))
         (emph (s face)
               (propertize s 'face face))
         (fsi (properties fmt &rest args)
              (insert (apply 'propertize
                             (apply 'format fmt args)
                             properties))))
      ;; breathe in
      (cl-loop
       for bx below width
       do (cl-loop
           with fork
           for node in (aref ends bx)
           do (if (setq fork (on node))
                  (cl-flet
                      ((tip-p (bix)
                              ;; todo: ignore non-"move" nodes
                              (eq node (car (aref ends bix))))
                       (link (other)
                             (cl-pushnew other (gethash node soil))))
                    (unless (tip-p bx)
                      (unless (tip-p fork)
                        (link fork))
                      (link bx)))
                (puthash node bx seen))
           until fork))
      ;; breathe out
      (switch-to-buffer buf)
      (gnugo-frolic-mode)
      (erase-buffer)
      (setq header-line-format
            (let ((full (concat
                         (make-string 11 ?\s)
                         (mapconcat (lambda (n)
                                      (format "%-5s" n))
                                    lanes
                                    " "))))
              `((:eval
                 (funcall
                  ,(lambda ()
                     (cl-flet
                         ((sp (w) (propertize
                                   " " 'display
                                   `(space :width ,w))))
                       (concat
                        (when (eq 'left scroll-bar-mode)
                          (let ((w (or scroll-bar-width
                                       (frame-parameter
                                        nil 'scroll-bar-width)))
                                (cw (frame-char-width)))
                            (sp (if w
                                    (/ w cw)
                                  2))))
                        (let ((fc (fringe-columns 'left t)))
                          (unless (zerop fc)
                            (sp fc)))
                        (condition-case nil
                            (substring full (window-hscroll))
                          (error ""))))))))))
      (set (make-local-variable 'gnugo-frolic-parent-buffer) from)
      (set (make-local-variable 'gnugo-state)
           (buffer-local-value 'gnugo-state from))
      (cl-loop
       with props
       for n                            ; move number
       from max-move-num downto 1
       do (setq props (list 'n n))
       do
       (cl-loop
        with (move forks br)
        initially (progn
                    (goto-char (point-min))
                    (fsi props
                         "%3d %s  -- "
                         n (aref ["W" "B"] (logand 1 n))))
        for bx below width
        do (let* ((node (unless (< (aref valid bx) n)
                          ;; todo: ignore non-"move" nodes
                          (pop (aref ends bx))))
                  (zow `(bx ,bx ,@props))
                  (ok (when node
                        (= bx (on node))))
                  (comment (when ok
                             (cdr (assq :C node))))
                  (s (cond ((not node) "")
                           ((not (setq move (gnugo--move-prop node))) "-")
                           (t (funcall as-pos (cdr move))))))
             (when comment
               (push comment zow)
               (push 'help-echo zow))
             (when (and ok (setq br (gethash node soil)))
               (push (cons bx (sort br '<))
                     forks))
             (fsi zow
                  "%c%-5s"
                  (if comment ?! ?\s)
                  (cond ((and (eq at node)
                              (or ok (= bx bidx)))
                         (when (= bx bidx)
                           (setq finish (point-marker)))
                         (emph s (list :inherit 'default
                                       :foreground (frame-parameter
                                                    nil 'cursor-color))))
                        ((not ok)
                         (emph s dimmed-node-face))
                        (t s))))
        finally do
        (when (progn (fsi props "\n")
                     (setq forks (nreverse forks)))
          (let* ((margin (make-string 11 ?\s))
                 (heads (mapcar #'car forks))
                 (tails (mapcar #'cdr forks)))
            (cl-flet*
                ((spaced (lanes func)
                         (mapconcat func lanes "     "))
                 ;;  live to play               ~   ~              ()
                 ;;  play to learn             (+) (-)       . o O
                 ;;  learn to live  --ttn        .M.   _____U
                 (dashed (lanes func) ;;;       _____ ^^^^
                         (mapconcat func lanes "-----"))
                 (cnxn (lanes set)
                       (spaced lanes (lambda (bx)
                                       (if (memq bx set)
                                           "|"
                                         " "))))
                 (pad-unless (condition)
                             (if condition
                                 ""
                               "     "))
                 (edge (set)
                       (insert margin
                               (cnxn lanes set)
                               "\n")))
              (edge heads)
              (cl-loop
               with bef
               for ls on forks
               do (let* ((one (car ls))
                         (yes (append
                               ;; "aft" heads
                               (mapcar 'car (cdr ls))
                               ;; ‘bef’ tails
                               (apply 'append (mapcar 'cdr bef))))
                         (ord (sort one '<))
                         (beg (car ord))
                         (end (car (last ord))))
                    (cl-flet
                        ((also (b e) (cnxn (number-sequence b e)
                                           yes)))
                      (insert
                       margin
                       (also 0 (1- beg))
                       (pad-unless (zerop beg))
                       (dashed (number-sequence beg end)
                               (lambda (bx)
                                 (cond ((memq bx ord) "+")
                                       ((memq bx yes) "|")
                                       (t             "-"))))
                       (pad-unless (>= end width))
                       (also (1+ end) (1- width))
                       "\n"))
                    (push one bef)))
              (edge (apply 'append tails))
              (aa2u (line-beginning-position
                     (- (1+ (length forks))))
                    (point))))))))
    (when finish
      (set (make-local-variable 'gnugo-frolic-origin) finish)
      (gnugo-frolic-return-to-origin))))

(defun gnugo--awake (how)
  ;; Valid HOW elements:
  ;;   require-valid-branch
  ;;   (line . numeric)
  ;;   (line . move-string)
  ;;   (omit . [VAR...])
  ;; Invalid elements blissfully ignored.  :-D
  (let* ((tree (gnugo-get :sgf-gametree))
         (ends (gnugo--tree-ends tree))
         (width (length ends))
         (monkey (gnugo-get :monkey))
         (line (cl-case (cdr (assq 'line how))
                 (numeric
                  (count-lines (point-min) (line-beginning-position)))
                 (move-string
                  (save-excursion
                    (when (re-search-backward "^ *[0-9]+ [BW]" nil t)
                      (match-string 0))))
                 (t nil)))
         (col (current-column))
         (a (unless (> 10 col)
              (let ((try (/ (- col 10)
                            6)))
                (unless (<= width try)
                  try))))
         (rv (list a)))
    (when (memq 'require-valid-branch how)
      (unless a
        (user-error "No branch here")))
    (cl-loop
     with omit = (cdr (assq 'omit how))
     for (name . value) in `((line   . ,line)
                             (bidx   . ,(aref monkey 1))
                             (monkey . ,monkey)
                             (width  . ,width)
                             (ends   . ,ends)
                             (tree   . ,tree))
     do (unless (memq name omit)
          (push value rv)))
    rv))

(defmacro gnugo--awakened (how &rest body)
  (declare (indent 1))
  `(cl-destructuring-bind
       ,(cl-loop
         with omit = (cdr (assq 'omit how))
         with ls   = (list 'a)
         for name in '(line bidx monkey
                            width ends
                            tree)
         do (unless (memq name omit)
              (push name ls))
         finally return ls)
       (gnugo--awake ',how)
     ,@body))

(defsubst gnugo--move-to-bcol (bidx)
  (move-to-column (+ 10 (* 6 bidx))))

(defun gnugo--swiz (direction &optional blunt)
  (gnugo--awakened (require-valid-branch
                    (omit tree)
                    (line . numeric))
    (let* ((b (cond ((numberp blunt)
                     (unless (and (< -1 blunt)
                                  (< blunt width))
                       (user-error "No such branch: %s" blunt))
                     blunt)
                    (t (mod (+ direction a) width))))
           (flit (if blunt (lambda (n)
                             (cond ((= n a) b)
                                   ((= n b) a)
                                   (t n)))
                   (lambda (n)
                     (mod (+ direction n) width))))
           (was (copy-sequence ends))
           (new-bidx (funcall flit bidx)))
      (cl-loop
       for bx below width
       do (aset ends (funcall flit bx)
                (aref was bx)))
      (unless (= new-bidx bidx)
        (aset monkey 1 new-bidx))
      (gnugo-frolic-in-the-leaves)
      (goto-char (point-min))
      (forward-line line)
      (gnugo--move-to-bcol b))))

(defun gnugo-frolic-exchange-left ()
  "Exchange the current branch with the one to its left."
  (interactive)
  (gnugo--swiz -1 t))

(defun gnugo-frolic-rotate-left ()
  "Rotate all branches left."
  (interactive)
  (gnugo--swiz -1))

(defun gnugo-frolic-exchange-right ()
  "Exchange the current branch with the one to its right."
  (interactive)
  (gnugo--swiz 1 t))

(defun gnugo-frolic-rotate-right ()
  "Rotate all branches right."
  (interactive)
  (gnugo--swiz 1))

(defun gnugo-frolic-set-as-main-line ()
  "Make the current branch the main line."
  (interactive)
  (gnugo--swiz nil 0))

(defun gnugo-frolic-prune-branch ()
  "Remove the current branch from the gametree.
This fails if there is only one branch in the tree.
This fails if the monkey is on the current branch
\(a restriction that will probably be lifted Real Soon Now\)."
  (interactive)
  (gnugo--awakened (require-valid-branch
                    (line . move-string))
    ;; todo: define meaningful eviction semantics; remove restriction
    (when (= a bidx)
      (user-error "Cannot prune with monkey on branch"))
    (when (= 1 width)
      (user-error "Cannot prune last remaining branch"))
    (let ((new (append ends nil)))
      ;; Explicit ignorance avoids byte-compiler warning.
      (ignore (pop (nthcdr a new)))
      (gnugo--set-tree-ends tree new))
    (when (< a bidx)
      (aset monkey 1 (cl-decf bidx)))
    (gnugo-frolic-in-the-leaves)
    (when line
      (goto-char (point-min))
      (search-forward line)
      (gnugo--move-to-bcol (min a (- width 2))))))

(defun gnugo--sideways (backwards n)
  (gnugo--awakened ((omit tree ends monkey bidx line))
    (gnugo--move-to-bcol (mod (if backwards
                                  (- (or a width) n)
                                (+ (or a -1) n))
                              width))))

(defun gnugo-frolic-backward-branch (&optional n)
  "Move backward N (default 1) branches."
  (interactive "p")
  (gnugo--sideways t n))

(defun gnugo-frolic-forward-branch (&optional n)
  "Move forward N (default 1) branches."
  (interactive "p")
  (gnugo--sideways nil n))

(defun gnugo--vertical (n direction)
  (when (> 0 n)
    (setq n (- n)
          direction (- direction)))
  (gnugo--awakened ((line . numeric)
                    (omit tree ends width monkey bidx))
    (let ((stop (if (> 0 direction)
                    0
                  (max 0 (1- (count-lines (point-min)
                                          (point-max))))))
          (col (unless a
                 (current-column))))
      (cl-loop
       while (not (= line stop))
       do (cl-loop
           do (progn
                (forward-line direction)
                (cl-incf line direction))
           until (get-text-property (point) 'n))
       until (zerop (cl-decf n)))
      (if a
          (gnugo--move-to-bcol a)
        (move-to-column col)))))

(defun gnugo-frolic-previous-move (&optional n)
  "Move to the Nth (default 1) previous move."
  (interactive "p")
  (gnugo--vertical n -1))

(defun gnugo-frolic-next-move (&optional n)
  "Move to the Nth (default 1) next move."
  (interactive "p")
  (gnugo--vertical n 1))

(defun gnugo-frolic-tip-move ()
  "Move to the tip of the current branch."
  (interactive)
  (gnugo--awakened ((omit line bidx monkey width)
                    require-valid-branch)
    (goto-char (point-max))
    (let ((mnum (gnugo--tree-mnum tree))
          (node (car (aref ends a))))
      (re-search-backward (format "^%3d" (gethash node mnum)))
      (gnugo--move-to-bcol a))))

;;;---------------------------------------------------------------------------
;;; that's it

(provide 'gnugo-frolic)

;;; gnugo-frolic.el ends here
