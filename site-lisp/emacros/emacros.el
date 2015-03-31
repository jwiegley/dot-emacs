
;; This is EMACROS 5.0, an extension to GNU Emacs.
;; Copyright (C) 1993, 2007 Free Software Foundation, Inc.

;; EMACROS is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY.  No author or distributor
;; accepts responsibility to anyone for the consequences of using it
;; or for whether it serves any particular purpose or works at all,
;; unless he says so in writing.  Refer to the GNU Emacs General Public
;; License for full details.

;; Everyone is granted permission to copy, modify and redistribute
;; EMACROS, but only under the conditions described in the
;; GNU Emacs General Public License.   A copy of this license is
;; supposed to have been given to you along with GNU Emacs so you
;; can know your rights and responsibilities.  It should be in a
;; file named COPYING.  Among other things, the copyright notice
;; and this notice must be preserved on all copies.

;; The HTML documentation for the Emacros package can be found at
;;
;; http://thbecker.net/free_software_utilities/emacs_lisp/emacros/emacros.html
;;
;; Send bug reports, questions, and comments to: emacros@thbecker.net


(defvar emacros-minibuffer-local-map
  nil
  "Local keymap for reading a new name for a keyboard macro from minibuffer.
Used by emacros-read-macro-name1.")

(setq emacros-minibuffer-local-map (make-sparse-keymap))

(define-key emacros-minibuffer-local-map "\C-g" 'abort-recursive-edit)
(define-key emacros-minibuffer-local-map "\n" 'emacros-exit-macro-read1)
(define-key emacros-minibuffer-local-map "\r" 'emacros-exit-macro-read1)

(defvar emacros-global-dir
  "~/"
  "*Default directory for saving global kbd-macros.")

(defvar emacros-glob-loc
  ?l
  "Default for saving named kbd-macros. 
Value ?l means local, value ?g means global. 
This is a buffer-local variable.")

(make-variable-buffer-local 'emacros-glob-loc)

(defvar emacros-last-name
  nil
  "Name of most recently named, renamed, moved, or executed kbd-macro.
This is a buffer-local variable.")

(make-variable-buffer-local 'emacros-last-name)

(defvar emacros-last-saved
  nil
  "Name of macro that was most recently moved, or saved 
using function emacros-name-last-kbd-macro-add with no prefix argument.
This is a buffer-local variable.")

(make-variable-buffer-local 'emacros-last-saved)

(defvar emacros-ok 
  nil
  "List of lists of directories from which kbd-macro files have been loaded. 
Each list is headed by the name of the mode to which it pertains.")

(defvar emacros-default 
  nil
  "Used only as dynamically bound local variable. Defined globally in order
to surpress compiler warning about free variable being used.")

(defvar emacros-read-existing-macro-name-history-list
  nil
  "History list variable for reading the name of an existing macro")

(defvar find-file-hook nil)
(or (memq 'emacros-load-macros find-file-hook) 
    (setq find-file-hook (cons 'emacros-load-macros find-file-hook)))

; Make sure pre-22 versions continue to work.
(defvar find-file-hooks nil)
(or (memq 'emacros-load-macros find-file-hooks) 
    (setq find-file-hooks (cons 'emacros-load-macros find-file-hooks)))

(defun emacros-macrop (sym)
  "Returns t if NAME, a symbol, is the name of a keyboard macro,
nil otherwise."
  (and (null (integerp sym))
       (fboundp sym)
       (let ((sym-fu (symbol-function sym)))
         (or (vectorp sym-fu)
             (stringp sym-fu)))))

(defun emacros-processed-mode-name ()
  "If the current mode name contains no slash, returns the current mode name.
Otherwise, returns the initial substring of the current mode name up to but
not including the first slash."
  (let ((slash-pos-in-mode-name (string-match "/" mode-name)))
    (if slash-pos-in-mode-name
        (substring mode-name 0 slash-pos-in-mode-name)
      mode-name)))

(defun emacros-process-global-dir ()
  "Expands the pathname stored in emacros-global-dir and ensures that it ends
in exactly one slash."
  (setq emacros-global-dir (expand-file-name (concat emacros-global-dir "/"))))
  
(defun emacros-exit-macro-read1 ()
  "The equivalent of exit-minibuffer for reading a new macroname 
from minibuffer. Used by emacros-read-macro-name1."
  (interactive)
  (let* ((name (buffer-substring (minibuffer-prompt-end) (point-max)))
         (parse-list (append name nil)))
    (if (equal name "")
        (progn (ding)
               (insert "[Can't use empty string]")
               (goto-char (minibuffer-prompt-end))
               (sit-for 2)
               (delete-region (minibuffer-prompt-end) (point-max)))
      (catch 'illegal
        (while parse-list
          (let ((char (car parse-list)))
            (if (or
                 (and (>= char ?0) (<= char ?9))
                 (and (>= char ?A) (<= char ?Z))
                 (and (>= char ?a) (<= char ?z))
                 (memq char (list ?- ?_)))
                (setq parse-list (cdr parse-list))
              (goto-char (point-max))
              (let ((pos (point)))
                (ding)
                (if (= char ? )
                    (insert " [No blanks, please!]")
                  (insert " [Use letters, digits, \"-\", \"_\"]"))
                (goto-char pos)
                (sit-for 2)
                (delete-region (point) (point-max)))
              (throw 'illegal t))))
        (if (integerp (car (read-from-string name)))
            (and (goto-char (point-max))
                 (let ((pos (point)))
                   (ding)
                   (insert " [Can't use integer]")
                   (goto-char pos)
                   (sit-for 2)
                   (delete-region (point) (point-max))))
          (exit-minibuffer))))))
  
(defun emacros-exit-macro-read2 ()
  "Substitutes minibuffer-complete-and-exit 
when reading an existing macro or macroname. 
Used by emacros-read-macro-name2."
  (interactive)
  (if (or (not (= (minibuffer-prompt-end) (point-max))) emacros-default)
      (minibuffer-complete-and-exit)
    (ding)
    (goto-char (minibuffer-prompt-end))
    (insert "[No default]")
    (sit-for 2)
    (delete-region (minibuffer-prompt-end) (point-max))))

(defun emacros-read-macro-name1 (prompt &optional letgo)
  "Reads a new name for a macro from minibuffer,
prompting with PROMPT. Rejects existing function names 
with the exception of optional argument SYMBOL."
  (let* ((name (read-from-minibuffer prompt "" emacros-minibuffer-local-map))
         (symbol (car (read-from-string name)))
         (sym-fu))
    (if (and (fboundp symbol)
             (not (equal symbol letgo)))
        (progn (setq sym-fu (symbol-function symbol))
               (if (and
                    (not (vectorp sym-fu))
                    (not (stringp sym-fu)))
                   (error "Function %s is already defined and not a keyboard macro" symbol))))
    symbol))

(defun emacros-read-macro-name2 (prompt)
  "Reads an existing name of a kbd-macro, prompting with PROMPT.
PROMPT must be given without trailing colon and blank."
  (let ((emacros-default (emacros-macrop emacros-last-name))
        (inp))
    (unwind-protect
        (progn
          (substitute-key-definition 'minibuffer-complete-and-exit
                                     'emacros-exit-macro-read2
                                     minibuffer-local-must-match-map)
          (setq inp (completing-read
                     (format "%s%s: "
                             prompt
                             (if emacros-default
                                 (format " (default %s)" emacros-last-name)
                               ""))
                     obarray
                     'emacros-macrop
                     t
                     nil
                     'emacros-read-existing-macro-name-history-list
                     (if emacros-default
                         (format "%s" emacros-last-name)
                       ""))))
      (substitute-key-definition 'emacros-exit-macro-read2
                                 'minibuffer-complete-and-exit
                                 minibuffer-local-must-match-map))
    (car (read-from-string inp))))

(defun emacros-new-macro (nam mac)
  "Assigns to the symbol NAME the function definition STRING."
  (fset nam mac))

(defun emacros-name-last-kbd-macro-add (&optional arg)
  "Assigns a name to the last keyboard macro defined.
Accepts letters and digits as well as \"_\" and \"-\".
Requires at least one non-numerical character.
Prompts for a choice betwen local and global saving.
With ARG, the user is prompted  for the name of a file
to save to. Default is the last location that was saved 
or moved to in the current buffer."
  (interactive "P")
  (or last-kbd-macro
      (error "No kbd-macro defined"))
  (emacros-process-global-dir)
  (let ((symbol (emacros-read-macro-name1 "Name for last kbd-macro: "))
        (macro-file (concat (emacros-processed-mode-name) "-mac.el"))
        (filename)
        (gl)
        (buf)
        (overwrite-existing-macro-definition nil))
    (if (= emacros-glob-loc ?g)
        (setq filename (concat emacros-global-dir macro-file))
      (setq filename (concat default-directory macro-file)))
    (if arg (setq filename
                  (expand-file-name 
                   (read-file-name (concat "Write macro to file (default "
                                           filename "): ")
                                   default-directory filename)))
      (if (equal (expand-file-name default-directory) emacros-global-dir)
          (let ((cursor-in-echo-area t))
            (message
             "Local = global in this buffer. Press any key to continue: ")
            (read-char)
            (setq gl emacros-glob-loc))
        (let ((cursor-in-echo-area t))
          (message "Save as local or global macro? (l/g, default %s) "
                   (if (= emacros-glob-loc ?g) "global" "local"))
          (setq gl (read-char)) 
          (while (not (memq gl (list ?l ?g ?\r)))
            (ding)
            (message
             "Please answer l for local, g for global, or RET for %s: "
             (if (= emacros-glob-loc ?g) "global" "local"))
            (setq gl (read-char))))
        (and (= gl ?\r) (setq gl emacros-glob-loc))
        (if (= gl ?g)
            (setq filename (concat emacros-global-dir macro-file))
          (setq filename (concat default-directory macro-file)))))
    (if (and (setq buf (get-file-buffer filename))
             (buffer-modified-p buf))
        (if arg
            (or (ding)
                (y-or-n-p
                 (format 
                  "Buffer visiting file %s modified. Continue? (Will save!) "
                  filename))
                (error "Aborted"))
          (or (ding)
              (y-or-n-p
               (format "Buffer visiting %s macro file modified. Continue? (Will save!) " (if (= gl ?l) "local" "global")))
              (error "Aborted"))))
    (setq overwrite-existing-macro-definition (emacros-prompt-for-overwriting-macro-definition macro-file buf symbol gl arg filename))
    (let ((find-file-hook nil)
          (find-file-hooks nil) ; make sure that pre-22 versions continue to work
          (emacs-lisp-mode-hook nil)
          (after-save-hook nil)
          (kill-buffer-hook nil))
      (save-excursion
        (if buf (set-buffer buf)
          (find-file filename))
        (emacros-insert-kbd-macro symbol last-kbd-macro overwrite-existing-macro-definition)
        (save-buffer 0)
        (or buf (kill-buffer (buffer-name)))))
    (if arg
        (message "Wrote definition of %s to file %s" symbol filename)
      (message "Wrote definition of %s to %s file %s"
               symbol
               (if (= gl ?g) "global" "local")
               macro-file)
      (setq emacros-glob-loc gl))
    (fset symbol last-kbd-macro)
    (setq emacros-last-name symbol)
    (if arg (setq emacros-last-saved nil)
      (setq emacros-last-saved symbol))))

(defun emacros-rename-macro ()
  "Renames macro in macrofile(s) and in current session.
Prompts for an existing name of a keyboard macro and a new name 
to replace it. Default for the old name is the name of the most recently
named, inserted, or manipulated macro in the current buffer."
  (interactive)
  (or (emacros-there-are-keyboard-macros) (error "No named kbd-macros defined"))
  (emacros-process-global-dir)
  (let* ((old-name (emacros-read-macro-name2 "Replace macroname"))
         (new-name (emacros-read-macro-name1
                    (format "Replace macroname %s with: " old-name) old-name))
         (macro-file (concat (emacros-processed-mode-name) "-mac.el"))
         (filename)
         (local-macro-filename)
         (global-macro-filename)
         (buf)
         (old-name-found)
         (new-name-found)
         (skip-this-file nil)
         (renamed))
    (while (equal new-name old-name)
      (or (ding)
          (y-or-n-p
           (format "%s and %s are identical. Repeat choice for new name? "
                   old-name new-name))
          (error "Aborted"))
      (setq new-name
            (emacros-read-macro-name1
             (format "Replace macroname %s with: " old-name) old-name)))
    (setq local-macro-filename (concat default-directory macro-file))
    (setq global-macro-filename(concat emacros-global-dir macro-file))
    (setq filename local-macro-filename)
    (if (and (setq buf (get-file-buffer filename))
             (buffer-modified-p buf))
        (or
         (ding)
         (y-or-n-p "Buffer visiting local macro file modified. Continue? (May save!) ")
         (error "Aborted")))
    (while filename
      (let ((find-file-hook nil)
            (find-file-hooks nil) ; make sure that pre-22 versions continue to work
            (emacs-lisp-mode-hook nil)
            (after-save-hook nil)
            (kill-buffer-hook nil))
        (save-excursion
          (if (or buf (file-exists-p filename))
              (progn (if buf
                         (set-buffer buf)
                       (find-file filename))
                     (goto-char (point-min)) 
                     (if (search-forward
                          (format "(emacros-new-macro '%s " old-name) 
                          (point-max) t)
                         (setq old-name-found t))
                     (goto-char (point-min)) 
                     (if (search-forward
                          (format "(emacros-new-macro '%s " new-name) 
                          (point-max) t)
                         (setq new-name-found t))
                     (or buf (kill-buffer (buffer-name)))))))
      (if old-name-found
          (progn (if new-name-found
                     (progn (ding)
                            (if (y-or-n-p
                                 (format "Macro %s exists in %s macro file %s. Overwrite? "
                                         new-name
                                         (if (equal filename local-macro-filename) "local" "global")
                                         macro-file))
                                (emacros-remove-macro-definition-from-file new-name buf filename)
                              (setq skip-this-file t))))
                 (if (not skip-this-file)
                     (let ((find-file-hook nil)
                           (find-file-hooks nil) ; make sure that pre-22 versions continue to work
                           (emacs-lisp-mode-hook nil)
                           (after-save-hook nil)
                           (kill-buffer-hook nil))
                       (save-excursion
                         (if (or buf (file-exists-p filename))
                             (progn (if buf
                                        (set-buffer buf)
                                      (find-file filename))
                                    (goto-char (point-min)) 
                                    (if (search-forward
                                         (format "(emacros-new-macro '%s " old-name) 
                                         (point-max) t)
                                        (progn (let ((end (point)))
                                                 (beginning-of-line)
                                                 (delete-region (point) end)) 
                                               (insert (format "(emacros-new-macro '%s "
                                                               new-name))
                                               (if renamed
                                                   (setq renamed (concat renamed " and ")))
                                               (setq renamed (concat renamed 
                                                                     (if (equal filename local-macro-filename)
                                                                         "local"
                                                                       "global")))
                                               (save-buffer 0)))
                                    (or buf (kill-buffer (buffer-name))))))))))
      (if (equal filename global-macro-filename)
          (setq filename nil)
        (setq filename global-macro-filename)
        (setq old-name-found nil)
        (setq new-name-found nil)
        (setq skip-this-file nil)
        (if (and (setq buf (get-file-buffer filename))
                 (buffer-modified-p buf))
            (or
             (ding)
             (y-or-n-p
              (format 
               "Buffer visiting global macro file modified. Continue? (May save!) "))
             (error "Aborted")))))
    (or renamed
        (error
         "Macro named %s not found or skipped at user request in current local and global file %s: no action taken"
         old-name macro-file))
    (fset new-name (symbol-function old-name))
    (fmakunbound old-name)
    (setq emacros-last-name new-name)
    (and (equal old-name emacros-last-saved)
         (setq emacros-last-saved new-name))
    (message "Renamed macro named %s to %s in %s file %s" 
             old-name
             new-name
             renamed
             macro-file)))

(defun emacros-move-macro ()
  "Moves macro from local to global macro file or vice versa.
Prompts for the name of a keyboard macro and a choice between 
\"from local\" and \"from global\", then moves the definition of the 
macro from the current local macro file to the global one or
vice versa. Default is the name of the most recently saved, inserted,
or manipulated macro in the current buffer."
  (interactive)
  (or (emacros-there-are-keyboard-macros) (error "No named kbd-macros defined"))
  (emacros-process-global-dir)
  (if (equal (expand-file-name default-directory) emacros-global-dir)
      (error "Local = global in this buffer"))
  (let ((name (emacros-read-macro-name2 "Move macro named"))
        (macro-file (concat (emacros-processed-mode-name) "-mac.el"))
        (gl)
        (moved)
        (filename1)
        (filename2)
        (buf1)
        (buf2)
        (name-found-in-source nil)
        (name-found-in-target nil)
        (buffername))
    (let ((cursor-in-echo-area t))
      (message "Move FROM local or FROM global? (l/g%s) "
               (if (equal name emacros-last-saved)
                   (format ", default %s"
                           (if (= emacros-glob-loc ?g) "global" "local")) ""))
      (setq gl (read-char)) 
      (while (not (if (equal name emacros-last-saved)
                      (memq gl (list ?l ?g ?\r))
                    (memq gl (list ?l ?g))))
        (ding)
        (message
         "Please answer l for local, g for global%s: "
         (if (equal name emacros-last-saved)
             (format ", or RET for %s"
                     (if (= emacros-glob-loc ?g) "global" "local")) ""))
        (setq gl (read-char))))
    (and (= gl ?\r) (setq gl emacros-glob-loc))
    (if (= gl ?l)
        (progn (setq filename1 (concat default-directory macro-file))
               (setq filename2 (concat emacros-global-dir macro-file)))
      (setq filename1 (concat emacros-global-dir macro-file))
      (setq filename2 (concat default-directory macro-file)))
    (if (and (setq buf1 (get-file-buffer filename1))
             (buffer-modified-p buf1))
        (or
         (ding)
         (y-or-n-p
          (format 
           "Buffer visiting %s macro file modified. Continue? (May save!) "
           (if (= gl ?g) "global" "local")))
         (error "Aborted")))
    (if (and (setq buf2 (get-file-buffer filename2))
             (buffer-modified-p buf2))
        (or
         (ding)
         (y-or-n-p
          (format 
           "Buffer visiting %s macro file modified. Continue? (May save!) "
           (if (= gl ?g) "local" "global")))
         (error "Aborted")))
    (let ((find-file-hook nil)
          (find-file-hooks nil) ; make sure that pre-22 versions continue to work
          (emacs-lisp-mode-hook nil)
          (after-save-hook nil)
          (kill-buffer-hook nil))
      (save-excursion
        (if (or buf1 (file-exists-p filename1))
            (progn (if buf1
                       (set-buffer buf1)
                     (find-file filename1))
                   (goto-char (point-min)) 
                   (if (search-forward
                        (format "(emacros-new-macro '%s " name)
                        (point-max) t)
                       (setq name-found-in-source t))
                   (or buf1 (kill-buffer (buffer-name)))))
        (if (or buf2 (file-exists-p filename2))
            (progn (if buf2
                       (set-buffer buf2)
                     (find-file filename2))
                   (goto-char (point-min)) 
                   (if (search-forward
                        (format "(emacros-new-macro '%s " name)
                        (point-max) t)
                       (setq name-found-in-target t))
                   (or buf2 (kill-buffer (buffer-name)))))))
    (if (not name-found-in-source)
        (error "Macro named %s not found in %s file %s"
               name (if (= gl ?l) "local" "global") macro-file))
    (if name-found-in-target
        (progn (ding)
               (if (y-or-n-p
                    (format "Macro %s exists in %s macro file %s. Overwrite? "
                            name
                            (if (= gl ?l) "global" "local")
                            macro-file))
                   (emacros-remove-macro-definition-from-file name buf2 filename2)
                 (error "Aborted"))))
    (let ((find-file-hook nil)
          (find-file-hooks nil) ; make sure that pre-22 versions continue to work
          (emacs-lisp-mode-hook nil)
          (after-save-hook nil)
          (kill-buffer-hook nil))
      (setq moved nil)
      (save-excursion
        (if buf1 (set-buffer buf1)
          (find-file filename1))
        (setq buffername (buffer-name))
        (goto-char (point-min))
        (if (search-forward
             (format "(emacros-new-macro '%s " name) (point-max) t)
            (progn (setq moved t)
                   (beginning-of-line)
                   (let ((beg (point)))
                     (search-forward "\n(emacros-new-macro '"
                                     (point-max) 'move)
                     (beginning-of-line)
                     (let ((end (point)))
                       (save-excursion
                         (if buf2 (set-buffer buf2)
                           (find-file filename2))
                         (goto-char (point-max))
                         (insert-buffer-substring buffername beg end)
                         (save-buffer 0)
                         (or buf2 (kill-buffer (buffer-name))))
                       (delete-region beg end)))
                   (save-buffer 0)))
        (or buf1 (kill-buffer buffername))))
    (if (null moved)
        (error "Macro named %s not found in %s file %s"
               name (if (= gl ?l) "local" "global") macro-file)
      (setq emacros-last-name name)
      (setq emacros-last-saved name)
      (if (= gl ?l)
          (setq emacros-glob-loc ?g)
        (setq emacros-glob-loc ?l))
      (message "Moved macro named %s to %s file %s"
               name (if (= gl ?l) "global" "local") macro-file))))

(defun emacros-remove-macro ()
  "Removes macro from current session and from current macro files.
The macroname defaults to the name of the most recently saved, 
inserted, or manipulated macro in the current buffer."
  (interactive)
  (or (emacros-there-are-keyboard-macros) (error "No named kbd-macros defined"))
  (emacros-process-global-dir)
  (let ((name (emacros-read-macro-name2 "Remove macro named"))
        (macro-file (concat (emacros-processed-mode-name) "-mac.el"))
        (filename)
        (local-macro-filename)
        (global-macro-filename)
        (buf)
        (deleted))
    (setq local-macro-filename (concat default-directory macro-file))
    (setq global-macro-filename(concat emacros-global-dir macro-file))
    (setq filename local-macro-filename)
    (if (and (setq buf (get-file-buffer filename))
             (buffer-modified-p buf))
        (or
         (ding)
         (y-or-n-p "Buffer visiting local macro file modified. Continue? (May save!) ")
         (error "Aborted")))
    (while filename
      (let ((find-file-hook nil)
            (find-file-hooks nil) ; make sure that pre-22 versions continue to work
            (emacs-lisp-mode-hook nil)
            (after-save-hook nil)
            (kill-buffer-hook nil))
        (save-excursion
          (if (or buf (file-exists-p filename))
              (progn (if buf
                         (set-buffer buf)
                       (find-file filename))
                     (goto-char (point-min))
                     (if (search-forward
                          (format "(emacros-new-macro '%s " name)
                          (point-max) t)
                         (progn (beginning-of-line)
                                (let ((beg (point)))
                                  (search-forward "\n(emacros-new-macro '" 
                                                  (point-max) 'move)
                                  (beginning-of-line)
                                  (delete-region beg (point)))
                                (if deleted
                                    (setq deleted (concat deleted " and ")))
                                (setq deleted (concat deleted 
                                                      (if (equal filename local-macro-filename)
                                                          "local"
                                                        "global")))
                                (save-buffer 0)))
                     (or buf (kill-buffer (buffer-name)))))))
      (if (equal filename global-macro-filename)
          (setq filename nil)
        (setq filename global-macro-filename)
        (if (and (setq buf (get-file-buffer filename))
                 (buffer-modified-p buf))
            (or
             (ding)
             (y-or-n-p
              (format 
               "Buffer visiting global macro file modified. Continue? (May save!) "))
             (error "Aborted")))))
    (if (not deleted)
        (error
         "Macro named %s not found in current file(s) %s: no action taken"
         name macro-file))
    (fmakunbound name)
    (and (equal name emacros-last-saved)
         (setq emacros-last-saved nil))
    (and (equal name emacros-last-name)
         (setq emacros-last-name nil))
    (message "Removed macro named %s from %s file %s" 
             name
             deleted
             macro-file)))

(defun emacros-execute-named-macro ()
  "Prompts for the name of a macro and executes it. Does completion.
Default is the most recently saved, inserted, or manipulated macro
in the current buffer."
  (interactive)
  (or (emacros-there-are-keyboard-macros) (error "No named kbd-macros defined"))
  (let ((name (emacros-read-macro-name2 "Execute macro named")))
    (setq emacros-last-name name)
    (execute-kbd-macro name)))

(defun emacros-auto-execute-named-macro ()
  "Prompts for the name of a macro and executes when a match has been found. 
Accepts letters and digits as well as \"_\" and \"-\".
Backspace acts normally, C-g exits, RET does rudimentary completion.
Default is the most recently saved, inserted, or manipulated macro
in the current buffer."
  (interactive)
  (or (emacros-there-are-keyboard-macros) (error "No named kbd-macros defined"))
  (let ((prompt (format "Auto-execute macro named%s: "
                        (if (emacros-macrop emacros-last-name) 
                            (format " (default %s)" emacros-last-name) "")))
        (name "")
        (is-macro)
        (char)
        (symbol)
        (compl))
    (while (not is-macro)
      (message "%s%s" prompt name)
      (setq char (read-char))
      (if (and (not (or (= char ?\r) (= char ?-) (= char ?_)
                        (= char ?\C-?)))
               (or (< char ?0)
                   (and (> char ?9) (< char ?A))
                   (and (> char ?Z) (< char ?a))
                   (> char ?z)))
          (and (null (ding))
               (message "%s%s [Illegal character]" prompt name)
               (sit-for 2))      
        (if (= char ?\C-?)
        (if (equal name "") 
            (ding)
          (setq name (substring name 0 (- (length name) 1))))
        (if (= char ?\r)
            (if (equal name "") 
                (if (emacros-macrop emacros-last-name)
                    (progn (setq symbol emacros-last-name)
                           (setq is-macro t))
                  (ding)
                  (message "%s[No default]" prompt)
                  (sit-for 2))
              (if (null (setq compl
                              (try-completion name obarray 'emacros-macrop)))
                  (and (null (ding))
                       (message "%s%s [No match]" prompt name)
                       (sit-for 2))
                (if (equal compl name)
                    (and (null (ding))
                         (message "%s%s [Not yet unique]" prompt name)
                         (sit-for 2))
                  (setq name compl)
                  (setq symbol (car (read-from-string name)))
                  (setq is-macro (emacros-macrop symbol)))))
          (setq name (concat name (char-to-string char)))
          (setq symbol (car (read-from-string name)))
          (setq is-macro (emacros-macrop symbol))))))
    (setq emacros-last-name symbol)
    (execute-kbd-macro symbol)))

(defun emacros-load-macros ()
  "Tries to load files mode-mac.el 
\(where \"mode\" stands for the name of the current mode\) 
from current directory and from directory emacros-global-dir. 
If the mode name contains a forward slash, then only the
initial substring of the mode name up to but not including
the forward slash is used.

Does not consider files that have been loaded previously or 
created during present session."
  (interactive)
  (emacros-process-global-dir)
  (let ((processed-mode-name (emacros-processed-mode-name))) 
    (let ((macro-file (concat processed-mode-name "-mac.el"))
          (mac-ok)
          (nextmac)
          (filename))
      (catch 'found-mode
        (while emacros-ok
          (setq nextmac (car emacros-ok))
          (setq emacros-ok (cdr emacros-ok))
          (and (equal processed-mode-name (car nextmac)) (throw 'found-mode t))
          (setq mac-ok (cons nextmac mac-ok))
          (setq nextmac nil)))
      (setq filename (concat emacros-global-dir macro-file))
      (if (file-exists-p filename) 
          (progn (or nextmac (load-file filename)) 
                 (setq emacros-glob-loc ?g)))
      (if (equal emacros-global-dir (expand-file-name default-directory))
          (progn (setq emacros-glob-loc ?g)
                 (setq nextmac (cons processed-mode-name (cdr nextmac))))
        (let ((dirlist (cdr nextmac))
              (dirli)
              (nextdir))
          (catch 'found-dir
            (while dirlist
              (setq nextdir (car dirlist))
              (setq dirlist (cdr dirlist))
              (and (equal default-directory nextdir) (throw 'found-dir t))
              (setq dirli (cons nextdir dirli))
              (setq nextdir nil)))
          (setq filename (concat default-directory macro-file))
          (if (file-exists-p filename)
              (progn (or nextdir (load-file filename))
                     (setq emacros-glob-loc ?l)))
          (setq nextmac (cons processed-mode-name
                              (append (cons default-directory dirli) dirlist)))))
      (setq emacros-ok (append (cons nextmac mac-ok) emacros-ok)))))
  
(defun emacros-show-macros ()
  "Displays the kbd-macros that are currently defined."
  (interactive)
  (let* ((mlist (emacros-make-macro-list))
         (next-macro-name (car mlist))
         (next-macro-definition (if next-macro-name (symbol-function next-macro-name) nil)))
    (or next-macro-name (error "No named kbd-macros defined"))
    (with-output-to-temp-buffer "*Help*"
      (princ "Below are all currently defined keyboard macros.\n")
      (princ "Use emacros-show-macro-names to see just the macro names.\n\n")
      (while next-macro-name
        (setq next-macro-definition (symbol-function next-macro-name))
        (princ next-macro-name) 
        (princ "  ")
        (if (stringp next-macro-definition)
            (prin1 next-macro-definition)
          (let ((nextevent)
                (eventlist (append next-macro-definition nil))
                (in-char-sequence nil)
                (in-keyboard-event-sequence nil))
            (while eventlist 
              (setq nextevent (car eventlist))
              (setq eventlist (cdr eventlist))
              (if (integerp nextevent)
                  (progn
                    (if in-keyboard-event-sequence (princ " "))
                    (if (not in-char-sequence) (princ "\""))
                    (if (and (<= 0 nextevent)
                             (<= nextevent 255))
                        (princ (char-to-string nextevent))
                      (princ (char-to-string 127))) ;for the lack of better
                    (setq in-char-sequence t)
                    (setq in-keyboard-event-sequence nil))
                (if in-char-sequence (princ "\""))
                (if (or in-char-sequence in-keyboard-event-sequence) (princ " "))
                (princ "<") 
                (prin1 nextevent) 
                (princ ">")
                (setq in-char-sequence nil)
                (setq in-keyboard-event-sequence t)))
            (if in-char-sequence (princ "\""))))
        (terpri)
        (setq mlist (cdr mlist))
        (setq next-macro-name (car mlist)))
      (princ " ") ; Funny, RMS is such a stickler for newline at EOF, and
                  ; his own printstream drops newlines at the end unless you
                  ; follow them by something else.
    (print-help-return-message))))

(defun emacros-show-macro-names (arg)
  "Displays the names of the kbd-macros that are currently defined."
  (interactive "P")
  (let* ((mlist (emacros-make-macro-list))
         (current-macro-name (car mlist))
         (current-column 0)
         (padding-width 0))
    (or current-macro-name (error "No named kbd-macros defined"))
    (with-output-to-temp-buffer "*Help*"
      (princ "Below are the names of all currently defined macros.\n")
      (princ "Use emacros-show-macros to see the macro names with their definitions.\n\n")
      (while current-macro-name
        (if (not (eq current-column 0))
            (progn
              (setq padding-width (- 35 current-column))
              (if (< 0 padding-width)
                  (progn  (princ (make-string padding-width 32))
                          (setq current-column (+ current-column padding-width)))
                (terpri)
                (setq current-column 0))))
        (setq current-macro-name (prin1-to-string current-macro-name))
        (princ current-macro-name)
        (if (not arg)
            (setq current-column (+ current-column (length current-macro-name)))
          (terpri))
        (setq mlist (cdr mlist))
        (setq current-macro-name (car mlist)))
      (if (not arg)(terpri))
      (princ " ") ; Funny, RMS is such a stickler for newline at EOF, and
                  ; his nown printstream drops newlines at the end unless you
                  ; follow it by something else.
    (print-help-return-message))))

(defun emacros-refresh-macros ()
  "Erases all macros and then reloads for current buffer.
When called in a buffer, this function produces, as far as 
kbd-macros are concerned, the same situation as if emacs had
just been started and the current file read from disc."
  (interactive)
  (let* ((mlist (emacros-make-macro-list))
         (next (car mlist)))
    (while next
      (fmakunbound next)
      (setq mlist (cdr mlist))
      (setq next (car mlist))))
  (setq emacros-ok nil)
  (setq last-kbd-macro nil)
  (setq emacros-last-name nil)
  (setq emacros-last-saved nil)
  (emacros-load-macros)
  (message "Macros refreshed for current buffer"))

(defun emacros-prompt-for-overwriting-macro-definition (macro-file buf symbol gl custom-file filename)
  "Checks if a macro definition exists in a macro file and if so, prompts for overwriting."
   (if (and (not buf) (not (file-exists-p filename)))
       nil
     (let ((macro-name-exists-p nil))
       (let ((find-file-hook nil)
             (find-file-hooks nil) ; make sure that pre-22 versions continue to work
             (emacs-lisp-mode-hook nil)
             (after-save-hook nil)
             (kill-buffer-hook nil))
         (save-excursion
           (if buf (set-buffer buf)
             (find-file filename))
           (goto-char (point-min)) 
           (if (search-forward
                (format "(emacros-new-macro '%s " symbol)
                (point-max) t)
               (setq macro-name-exists-p t))
           (or buf (kill-buffer (buffer-name)))))
       (if (not macro-name-exists-p)
           nil
         (if custom-file
             (or (ding)
                 (y-or-n-p
                  (format 
                   "Macro %s exists in file %s. Overwrite? "
                   symbol
                   filename))
                 (error "Aborted."))
           (or (ding)
               (y-or-n-p
                (format "Macro %s exists in %s macro file %s. Overwrite? "
                        symbol
                        (if (= gl ?l) "local" "global")
                        macro-file))
               (error "Aborted.")))))))
   
(defun emacros-insert-kbd-macro (symbol kbd-macro overwrite-existing-macro-definition)
  "Inserts macro definition in current buffer, overwriting existing definition if requested."
  (if overwrite-existing-macro-definition
      (emacros-remove-macro-definition symbol))
  (goto-char (point-max))
  (if (not (bolp)) (insert "\n"))
  (insert "(emacros-new-macro '")
  (prin1 symbol (current-buffer))
  (insert " ")
  (prin1 kbd-macro (current-buffer))
  (insert (if (eobp) ")\n" ")")))

(defun emacros-remove-macro-definition-from-file (symbol buf filename)
  "Removes first definition of macro named symbol from filename."
  (if (and (not buf) (not (file-exists-p filename)))
      nil
    (let ((find-file-hook nil)
          (find-file-hooks nil) ; make sure that pre-22 versions continue to work
          (emacs-lisp-mode-hook nil)
          (after-save-hook nil)
          (kill-buffer-hook nil))
      (save-excursion
        (if buf (set-buffer buf)
          (find-file filename))
        (emacros-remove-macro-definition symbol)
        (save-buffer 0)
        (or buf (kill-buffer (buffer-name)))))))

(defun emacros-remove-macro-definition (symbol)
  "Removes definition of macro named symbol from current buffer."
  (goto-char (point-min))
  (if (search-forward
       (format "(emacros-new-macro '%s " symbol)
       (point-max) t)
      (progn
        (end-of-line)
        (let ((eol (point)))
          (beginning-of-line)
          (delete-region (point) eol))
        (if (not (eobp))
                 (delete-char 1)))))

(defun emacros-make-macro-list ()
  "Makes a list of all symbols whose function definition is not void and is a macro."
  (let (macro-list)
    (mapatoms (lambda (symbol) (if (emacros-macrop symbol) (setq macro-list (cons symbol macro-list)))))
    (sort
     macro-list
     '(lambda (sym1 sym2)
        (let* ((str1 (prin1-to-string sym1))
              (str2 (prin1-to-string sym2))
              (cmp (compare-strings str1 0 (length str1) str2 0 (length str2) t)))
          (and (integerp cmp) (< cmp 0)))))))

(defun emacros-there-are-keyboard-macros ()
  "Returns t if there is at least one keyboard macro currently defined."
  (catch 'macro-found
    (mapatoms (lambda (symbol) (if (emacros-macrop symbol) (throw 'macro-found t))))
    nil))
