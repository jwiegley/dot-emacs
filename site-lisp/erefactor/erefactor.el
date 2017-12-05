;;; erefactor.el --- Emacs-Lisp refactoring utilities

;; Author: Masahiro Hayashi <mhayashi1120@gmail.com>
;; Keywords: extensions, tools, maint
;; URL: https://github.com/mhayashi1120/Emacs-erefactor
;; Emacs: GNU Emacs 24 or later
;; Package-Requires: ((cl-lib "0.3"))
;; Version: 0.7.1

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Simple refactoring, linting utilities for Emacs-Lisp.

;; ## Install:

;; Put this file into load-path'ed directory,
;; and byte compile its if desired.
;; And put the following expression into your ~/.emacs.
;;
;;     (eval-after-load 'lisp-mode
;;       '(progn
;;          (require 'erefactor)
;;          (define-key emacs-lisp-mode-map "\C-c\C-v" erefactor-map)))
;;
;; And set these variables correctly.
;;  `erefactor-lint-path-alist`, `erefactor-lint-by-emacsen`

;; Put the following in your .emacs, if you desire highlighting local variable.
;;
;;     (add-hook 'emacs-lisp-mode-hook 'erefactor-lazy-highlight-turn-on)
;;     (add-hook 'lisp-interaction-mode-hook 'erefactor-lazy-highlight-turn-on)

;; ## Usage:

;; `C-c C-v l` : elint current buffer in clean environment.
;; `C-c C-v L` : elint current buffer by multiple emacs binaries.
;;             See `erefactor-lint-emacsen`
;; `C-c C-v r` : Rename symbol in current buffer.
;;             Resolve `let` binding as long as i can.
;; `C-c C-v R` : Rename symbol in requiring modules and current buffer.
;; `C-c C-v h` : Highlight current symbol in this buffer
;;             and suppress `erefacthr-highlight-mode`.
;; `C-c C-v d` : Dehighlight all by above command.
;; `C-c C-v c` : Switch prefix bunch of symbols.
;;             ex: '(hoge-var hoge-func) -> '(foo-var foo-func)
;; `C-c C-v ?` : Display flymake elint warnings/errors

;; * To show compilation warnings when evaluate `defun` form.
;;
;;     M-x erefactor-check-eval-mode

;;; TODO:
;; * Change only same case if symbol. But docstring is not.
;;
;; * `.' is not a separator of lisp symbol.
;;   rename `region` symbol and `REGION.` in docstring
;;   don't use re-search while idiom,
;;   gather symbols in code, string, comment each context.
;;     (defun hoge (region)
;;       "REGION is REGION."
;;       region)
;;
;;  don't forget about `quoted` symbol.

;; * macroexpand misunderstand local variable
;;
;;     (defmacro hogemacro (&rest form)
;;       `(progn
;;          ,@form
;;          (let (a))))
;; =>
;;     (hogemacro a) <= `a' is not bounded in this context.
;;
;; * Separate elint and flymake to other elisp file.
;;
;; * flymake not works emacs-22

;; * Slowing down the Emacs when too many macroexpand in highlight-symbol-mode

;;; Code:

(require 'cl-lib)

(eval-when-compile
  (require 'easy-mmode))

;; externals
(defvar load-path)
(defvar shell-command-switch)
(defvar shell-file-name)
(defvar load-history)
(defvar idle-update-delay) ;; after Emacs 22
(defvar this-command)
(defvar timer-idle-list)
(defvar current-prefix-arg)
(defvar unread-command-events)
(defvar buffer-file-coding-system)

(defgroup erefactor nil
  "Emacs Lisp Refactoring utilities"
  :group 'lisp
  :prefix "erefactor-")

;;;
;;; Basic utilities
;;;

(defun erefactor-macrop (symbol)
  (and
   (symbolp symbol)
   (fboundp symbol)
   (eq (car-safe (indirect-function symbol)) 'macro)))

(defun erefactor-ref (key list)
  (cdr (assoc key list)))

(defun erefactor-emacs-version (command &optional major-only)
  (with-temp-buffer
    (call-process command nil (current-buffer) nil "-version")
    (let ((output (buffer-string)))
      (unless (string-match "Emacs *\\(\\([0-9]+\\)\\.[0-9]+\\.[0-9]+\\)" output)
        (error "Unable get version"))
      (if major-only
          (string-to-number (match-string 2 output))
        (match-string 1 output)))))

(defun erefactor-mapconcat (func list)
  (apply 'append (mapcar func list)))

(defun erefactor--union (list1 list2)
  (cl-loop for a in (append list1 list2)
           unless (member a res)
           collect a into res
           finally return res))

(defun erefactor--find (pred list)
  (cl-loop for a in list
           if (funcall pred a)
           return a))

(defmacro erefactor-interactive-p ()
  (cond
   ((= emacs-major-version 21)
    `(interactive-p))
   ((or (= emacs-major-version 22)
        (and (version<= emacs-version "23.2")
             (not (version= emacs-version "23.2"))))
    `(called-interactively-p))
   (t
    `(called-interactively-p 'any))))

(defun erefactor-create-regexp (symbol)
  "Create SYMBOL exclusive regexp."
  (format "\\_<\\(%s\\)\\_>" (regexp-quote symbol)))

(defun erefactor-create-prefixed-regexp (prefix)
  "Create matching to PREFIX exclusive regexp."
  (format "\\_<\\(\\(%s\\)\\(\\(?:\\s_\\|\\sw\\)*\\)\\)\\_>"
          (regexp-quote prefix)))

;;
;; Inner functions
;;

(defun erefactor--symbol-group-prefix (symbol)
  (let ((symbol-name (symbol-name symbol))
        most-prefix len p)
    (mapatoms
     (lambda (s)
       (when (and (setq p (get s 'custom-prefix))
                  (stringp p)
                  (string-match (concat "^" (regexp-quote p)) symbol-name)
                  (or (null len) (< len (match-end 0))))
         (setq len (match-end 0))
         (setq most-prefix p)))
     obarray)
    most-prefix))

(defun erefactor--guessed-using-files (symbol)
  (let (ret file)
    (let* ((prefix (erefactor--symbol-group-prefix symbol))
           (prefix-regexp (concat "^" (regexp-quote prefix))))
      (mapatoms
       (lambda (s)
         (when (and (string-match prefix-regexp (symbol-name s))
                    (setq file (symbol-file s)))
           ;; if byte compiled file
           (when (string-match "^\\(.*\\.el\\)c$" file)
             (setq file (match-string 1 file)))
           (add-to-list 'ret file)))
       obarray))
    (let ((files (append
                  (erefactor--symbol-using-sources 'defun symbol)
                  (erefactor--symbol-using-sources 'defvar symbol)
                  (erefactor--symbol-using-sources 'defface symbol))))
      (setq ret (erefactor--union files ret)))
    ret))

(defun erefactor--find-local-binding (name)
  (let* ((first (point))
         (symbol (intern name))
         (history (cons first nil))
         previous)
    (save-excursion
      (catch 'found
        (condition-case nil
            (while t
              (backward-up-list)
              (let* ((start (point-marker))
                     (form (read (current-buffer)))
                     (end (point-marker))
                     (special-bind (erefactor--special-binding
                                    symbol form history)))
                ;; detect looping
                ;; list start char by syntax-table
                (when (and previous (= (car previous) start))
                  (signal 'scan-error nil))
                (when special-bind
                  (throw 'found special-bind))
                (when (or
                       (erefactor--local-binding-p symbol form)
                       (erefactor--macroexpand-contains-p symbol form))
                  (throw 'found (cons start end)))
                (setq previous (cons start end))
                (setq history (cons previous history))))
          (scan-error nil))))))

(defun erefactor--special-binding (name form history)
  "NAME scope is not single sexp."
  (erefactor--local-fbinding name form history))

(defun erefactor--local-fbinding (name form history)
  (when (memq (car-safe form) '(flet macrolet labels))
    (save-excursion
      ;; ignore all error because `flet' case is special!!
      (condition-case nil
          (let ((region (cadr history))
                (first (car (last history))))
            (when (and (consp region)
                       (< (car region) first)
                       (> first (car region)))
              ;; at start definition of local function
              ;; (flet ((func (a b) (list a b))))
              ;;        ^^
              (goto-char (car region))
              (forward-char)
              (forward-sexp) ;; end of function name
              (let ((args (read (current-buffer))))
                (when (erefactor--lambda-binding-contains-p args name)
                  region))))
        (error nil)))))

(defun erefactor--local-binding-p (name form)
  (or
   ;; FIXME: difference between let and let*
   (and (memq (car-safe form) '(let let* lexical-let lexical-let*))
        (erefactor--let-binding-contains-p (cadr form) name))
   (and (memq (car-safe form) '(defun defmacro))
        (erefactor--lambda-binding-contains-p (cl-caddr form) name))
   (and (eq (car-safe form) 'lambda)
        (erefactor--lambda-binding-contains-p (cadr form) name))
   (and (eq (car-safe form) 'defadvice)
        (erefactor--defadvice-binding-contains-p (cl-caddr form) name))
   (and (eq (car-safe form) 'catch)
        (erefactor--catch-binding-contains-p (cdr form) name))
   (and (eq (car-safe form) 'condition-case)
        (erefactor--condition-case-contains-p (cdr form) name))
   (and (eq (car-safe form) 'eieio-defmethod)
        (erefactor--eieio-defmethod-contains-p (cl-caadr (cl-caddr form)) name))))

;; To avoid too many recursion.
;; Slow down the emacs if form contains a lot of macro. (ex: ert-deftest)
(defvar erefactor--macroexpand-depth 0)

;; This default value means to adequate the `loop' macro
(defvar erefactor--macroexpand-max-depth 3)

(defun erefactor--macroexpand-contains-p (name form)
  ;; `lambda' is macro expanded like (function (lambda () ...))
  (when (and (< erefactor--macroexpand-depth erefactor--macroexpand-max-depth)
             (not (memq (car-safe form) '(lambda)))
             (erefactor-macrop (car-safe form)))
    (condition-case nil
        (let ((erefactor--macroexpand-depth (1+ erefactor--macroexpand-depth))
              (expand-form (macroexpand form)))
          (catch 'found
            (when (erefactor--local-binding-p name expand-form)
              (throw 'found t))
            (when (erefactor--binding-exists-p name expand-form)
              (throw 'found t))
            nil))
      (error nil))))

(defun erefactor--binding-exists-p (name form)
  (catch 'found
    (dolist (f form)
      (when (or (erefactor--local-binding-p name f)
                (erefactor--macroexpand-contains-p name f))
        (throw 'found t))
      (when (and (listp f)
                 (erefactor--binding-exists-p name f))
        (throw 'found t)))))

(defun erefactor--condition-case-contains-p (form name)
  (let ((var (car-safe form)))
    ;; error binded variable and must be non-nil value
    (when (and (atom var) var)
      (eq var name))))

(defun erefactor--let-binding-contains-p (let-arg name)
  (or (memq name let-arg)
      (assq name let-arg)))

(defun erefactor--lambda-binding-contains-p (lambda-arg name)
  (and (not (memq name '(&optional &rest)))
       (memq name lambda-arg)))

(defun erefactor--eieio-defmethod-contains-p (method-arg name)
  (and (not (memq name '(&optional &rest)))
       (or (memq name method-arg)
           (assq name method-arg))))

(defun erefactor--defadvice-binding-contains-p (ad-args name)
  (let* ((rest (cddr ad-args))
         ;; consider optional position arg
         (args (cond
                ((consp (car rest))
                 (car rest))
                ((consp (cadr rest))
                 (cadr rest))
                (t nil))))
    (erefactor--lambda-binding-contains-p args name)))

(defun erefactor--catch-binding-contains-p (catch-arg name)
  "Consider (catch variable ...) like form."
  (and (listp (car catch-arg))
       (eq (caar catch-arg) 'quote)
       (symbolp (cl-cadar catch-arg))
       (eq (cl-cadar catch-arg) name)))

(defun erefactor-context-code-p (&optional point)
  (save-excursion
    (let ((parses (parse-partial-sexp (point-min) (or point (point)))))
      (and (not (nth 3 parses))
           (not (nth 4 parses))))))

(defun erefactor-context-string-p (&optional point)
  (save-excursion
    (let ((parses (parse-partial-sexp (point-min) (or point (point)))))
      (nth 3 parses))))

(defun erefactor-context-comment-p (&optional point)
  (save-excursion
    (let ((parses (parse-partial-sexp (point-min) (or point (point)))))
      (nth 4 parses))))

;; list only generally using
(defvar erefactor-def-alist
  '(
    ;; Variable cell
    (defvar defvar)
    (defcustom defvar)
    (defconst defvar)

    ;; Function cell
    (defun defun)
    (defmacro defun)
    (defun*  defun)
    (defmacro* defun)

    ;; Face
    (defface defface)

    ;; Misc
    (define-minor-mode defun defvar)
    ))

(defun erefactor--current-fnsym ()
  (save-excursion
    (let (ret)
      (condition-case nil
          (while (not (bobp))
            (let ((sym (thing-at-point 'symbol)))
              (backward-sexp)
              (when sym
                (push (intern sym) ret))
              (skip-syntax-backward " ")))
        (scan-error nil))
      ret)))

(defun erefactor--symbol-defined-alist (symbol)
  ;; FUNCS FACES VARS have file names.
  (let (funcs faces vars)
    (cl-loop for (file . entries) in load-history
             do (let (tmp)
                  (when (memq symbol entries)
                    (push file vars))
                  (when (and (setq tmp (rassq symbol entries))
                             (eq (car tmp) 'defface))
                    (push file faces))
                  (when (and (setq tmp (rassq symbol entries))
                             (eq (car tmp) 'defun))
                    (push file funcs))))
    `((defun . ,funcs)
      (defface . ,faces)
      (defvar . ,vars))))

(defun erefactor--add-load-name (file type symbol)
  ;; When duplicated definition exists, `load-history' simply have
  ;; duplicated values.
  (let ((hist (assoc file load-history)))
    (unless hist
      (error "%s is not loaded" file))
    (setcdr (last hist)
            (cond
             ((memq type '(defun defface))
              (list (cons type symbol)))
             ((eq type 'defvar)
              (list symbol))))))

(defun erefactor--change-load-name (old-symbol new-symbol type)
  (let ((defs (erefactor--find-load-history type old-symbol)))
    (dolist (def defs)
      (cond
       ((memq type '(defun defface))
        (setcdr def new-symbol))
       (t
        (setcar def new-symbol))))))

(defun erefactor--find-load-history (type symbol)
  (let* ((defs (erefactor--symbol-defined-alist symbol))
         (files (cdr (assq type defs)))
         (res '()))
    (dolist (file files)
      (let ((def (cdr (assoc file load-history))))
        (cond
         ((memq type '(defun defface))
          (let ((tmp (rassq symbol def)))
            (when (and tmp (car tmp) type)
              (setq res (cons tmp res)))))
         (t
          (let ((tmp (memq symbol def)))
            (when tmp
              (setq res (cons tmp res))))))))
    res))

(defun erefactor--symbol-package (type symbol)
  (let* ((defs (erefactor--symbol-defined-alist symbol))
         (files (cdr (assq type defs))))
    (catch 'done
      (dolist (file files)
        (let ((tmp (cdr (assq 'provide (cdr (assoc file load-history))))))
          (when tmp
            (throw 'done tmp)))))))

;; get a sources that is defined SYMBOL as TYPE
(defun erefactor--symbol-using-sources (type symbol)
  (let ((package (erefactor--symbol-package type symbol)))
    (cl-loop for defs in load-history
             when (cl-loop for def in (cdr defs)
                           when (and (listp def)
                                     (eq (car def) 'require)
                                     (eq package (cdr def)))
                           collect def)
             collect (car defs))))

(defun erefactor-after-rename-symbol (old-name new-name)
  (save-match-data
    (let ((fnsym (erefactor--current-fnsym))
          (old (intern old-name))
          (new (intern new-name)))
      ;; re-define definition.
      ;; if `defvar' or `defcustom' current value will be cleared.
      (condition-case err
          (eval-defun nil)
        (error
         (message "%s" err)
         (sit-for 0.1)))
      ;; after renaming is succeeded
      (when (eq (cadr fnsym) new)
        (let ((types (cdr (assq (car fnsym) erefactor-def-alist))))
          ;; try to change `load-history'
          (dolist (type types)
            (erefactor--change-load-name old new type)))))))

(defvar erefactor--read-symbol-history nil)
(defun erefactor-rename-symbol-read-args ()
  (let (current-name prompt new-name)
    (barf-if-buffer-read-only)
    (unless (setq current-name (thing-at-point 'symbol))
      (error "No symbol at point"))
    (setq prompt (format "%s -> New name: " current-name))
    (setq new-name
          (read-string
           prompt current-name
           'erefactor--read-symbol-history))
    (when (string= current-name new-name)
      (error "No difference"))
    (list current-name new-name)))

(defvar erefactor--read-prefix-history nil)
(defun erefactor-change-prefix-read-args ()
  (let (current-prefix prompt new-prefix)
    (barf-if-buffer-read-only)
    (setq current-prefix (thing-at-point 'symbol))
    (setq current-prefix
          (read-string
           "Changing prefix: " current-prefix
           'erefactor--read-prefix-history))
    (setq prompt (format "Changing prefix: %s -> New prefix: " current-prefix))
    (setq new-prefix
          (read-string
           prompt current-prefix 'erefactor--read-prefix-history))
    (when (string= current-prefix new-prefix)
      (error "No difference"))
    (list current-prefix new-prefix)))

(defvar erefactor--overlay nil)
(defvar erefactor--region-start nil)
(defvar erefactor--region-end nil)

(defun erefactor-dehighlight-in-interactive ()
  "Dehighlight text by `erefactor-re-highlight-in-interactive'."
  (when erefactor--overlay
    (delete-overlay erefactor--overlay))
  (erefactor-hl--dehighlight-all))

(defun erefactor-re-highlight-in-interactive (regexp beg fin)
  "Highlight REGEXP between BEG and FIN in region
`erefactor--region-start' to `erefactor--region-end'."
  ;; highlight replacing text
  (if (overlayp erefactor--overlay)
      (move-overlay erefactor--overlay beg fin (current-buffer))
    (setq erefactor--overlay (make-overlay beg fin))
    ;; higher than erefactor-highlight-face
    (overlay-put erefactor--overlay 'priority 100)
    (overlay-put erefactor--overlay 'face 'query-replace))
  ;; highlight scheduled replacing text.
  (erefactor-hl--update-region
   erefactor--region-start erefactor--region-end
   regexp t))

(defface erefactor-highlight-face
  '((t (:inherit match)))
  "Face for highlighting of matches."
  :group 'erefactor)

(defvar erefactor-highlight-face 'erefactor-highlight-face)
(defvar erefactor-hl--overlays nil)
(make-variable-buffer-local 'erefactor-hl--overlays)

(defvar erefactor-highlight-map nil)

(unless erefactor-highlight-map
  (let ((map (make-sparse-keymap)))

    (define-key map (kbd "M-<left>") 'erefactor-highlight-previous-symbol)
    (define-key map (kbd "M-<right>") 'erefactor-highlight-next-symbol)

    (setq erefactor-highlight-map map)))

(defun erefactor-hl--update-region (start end regexp &optional ignore-case check)
  "highlight START to END word that match to REGEXP.
CHECK is function that accept no arg and return boolean."
  (save-match-data
    (save-excursion
      (goto-char start)
      (let ((case-fold-search ignore-case))
        (setq erefactor-hl--overlays nil)
        (while (and (re-search-forward regexp nil t)
                    (< (point) end))
          (when (or (null check)
                    (save-match-data (funcall check)))
            (let ((ov (make-overlay (match-beginning 0) (match-end 0))))
              (overlay-put ov 'priority 1) ;; few value
              (overlay-put ov 'face erefactor-highlight-face)
              (overlay-put ov 'erefactor-overlay-p t)
              ;;FIXME not activated immediately if be in the timer.
              (overlay-put ov 'keymap erefactor-highlight-map)
              (setq erefactor-hl--overlays
                    (cons ov erefactor-hl--overlays)))))))))

(defun erefactor-hl--dehighlight-all ()
  (save-match-data
    (dolist (ov (overlays-in (point-min) (point-max)))
      (when (overlay-get ov 'erefactor-overlay-p)
        (delete-overlay ov))))
  (setq erefactor-hl--overlays nil))

(defmacro erefactor--with-file (file &rest form)
  (declare (indent 1))
  `(let ((win (selected-window))
         buffer opened)
     (if (setq buffer (get-file-buffer file))
         (setq opened t)
       (setq buffer (find-file-noselect file)))
     (unwind-protect
         (with-current-buffer buffer
           (save-window-excursion
             (set-window-buffer win buffer)
             (let (buffer-read-only)
               ,@form)))
       (unless opened
         (when (buffer-live-p buffer)
           (unless (buffer-modified-p buffer)
             (kill-buffer buffer)))))))

(defun erefactor--already-bounded (symbol start end)
  "SYMBOL is already bounded or not in region START END."
  (save-excursion
    (goto-char start)
    ;; search only symbol. (if possible...)
    (let (case-fold-search)
      (and (re-search-forward (erefactor-create-regexp symbol) nil t)
           (< (point) end)))))

(defun erefactor-rename-region (symbol new-symbol &optional region)
  "Rename SYMBOL to NEW-SYMBOL in REGION."
  (let ((start (if region (car region) (point-min)))
        (end (save-excursion
               (goto-char (if region (cdr region) (point-max)))
               (point-marker)))
        regexp)
    (when (or (not (erefactor--already-bounded new-symbol start end))
              (y-or-n-p (format "%s is already bound. Continue? " new-symbol)))
      (save-excursion
        (setq erefactor--region-start start)
        (setq erefactor--region-end end)
        (goto-char start)
        (setq regexp (erefactor-create-regexp symbol))
        ;; cannot use narrow-to-region because is unnatural while
        ;; interactive loop
        (while (and (re-search-forward regexp nil t)
                    (< (point) end))
          ;; to protect destroying match
          (let ((target (match-data)))
            (goto-char (match-end 1))
            (erefactor-re-highlight-in-interactive
             regexp (match-beginning 1) (match-end 1))
            (unwind-protect
                (when (y-or-n-p "Rename? ")
                  ;; restore match data (timer maybe destroy match-data)
                  (set-match-data target)
                  (replace-match new-symbol t nil nil 1)
                  (erefactor-after-rename-symbol symbol new-symbol))
              (erefactor-dehighlight-in-interactive))))))))

(defun erefactor-change-symbol-prefix (prefix new-prefix)
  "Switch symbol PREFIX to NEW-PREFIX in buffer."
  (save-excursion
    (setq erefactor--region-start (point-min))
    (setq erefactor--region-end (point-max))
    (goto-char (point-min))
    (let ((regexp (erefactor-create-prefixed-regexp prefix)))
      ;; cannot use narrow-to-region because is unnatural while
      ;; interactive loop
      (while (re-search-forward regexp nil t)
        (let ((target (match-data))
              (suffix (match-string 3)))
          (goto-char (match-end 1))
          (erefactor-re-highlight-in-interactive
           regexp (match-beginning 2) (match-end 2))
          (let* ((old-name (concat prefix suffix))
                 (new-name (concat new-prefix suffix)))
            (unwind-protect
                (when (y-or-n-p "Rename? ")
                  ;; restore match data (timer maybe destroy match-data)
                  (set-match-data target)
                  (replace-match new-prefix t nil nil 2)
                  (erefactor-after-rename-symbol old-name new-name))
              (erefactor-dehighlight-in-interactive))))))))

;;;
;;; lazy highlight local variable
;;;

(defvar ahs-face-check-include-overlay)

(defvar erefactor-lhl--timer nil)

(defvar erefactor-lhl--suspended nil)
(make-variable-buffer-local 'erefactor-lhl--suspended)

(defvar erefactor-highlight-mode)

(defun erefactor-hl--dehighlight-after-change (start end old-len)
  (ignore-errors
    (remove-hook 'after-change-functions 'erefactor-hl--dehighlight-after-change)
    (erefactor-dehighlight-all-symbol)))

(defun erefactor-lhl--stop ()
  (when erefactor-lhl--timer
    (unless (catch 'done
              (dolist (buf (buffer-list))
                (with-current-buffer buf
                  (when erefactor-highlight-mode
                    (throw 'done t)))))
      (cancel-timer erefactor-lhl--timer)
      (setq erefactor-lhl--timer nil))))

(defun erefactor-lhl--start ()
  (or
   (and erefactor-lhl--timer
        (memq erefactor-lhl--timer timer-idle-list))
   (setq erefactor-lhl--timer
         (run-with-idle-timer idle-update-delay t
                              'erefactor-lhl--highlight))))

(defun erefactor-lhl--dehihglight ()
  (erefactor-hl--dehighlight-all))

(defun erefactor-lhl--post-command ()
  (erefactor-lhl--dehihglight)
  (remove-hook 'post-command-hook 'erefactor-lhl--post-command))

(defun erefactor-lhl--highlight ()
  (save-match-data
    (with-local-quit
      (condition-case nil
          (cond
           ;; ignore when other command executing.
           ;; ex: erefactor-rename-symbol-*
           (this-command)
           ((not erefactor-highlight-mode))
           ;; t means suppress lazy highlight
           ((eq erefactor-lhl--suspended t))
           (t
            (save-match-data
              (erefactor-lhl--dehihglight)
              (let ((symbol (thing-at-point 'symbol)))
                (when symbol
                  (let ((region (erefactor--find-local-binding symbol)))
                    (when region
                      (erefactor-hl--update-region
                       (car region) (cdr region)
                       (erefactor-create-regexp symbol)
                       nil 'erefactor-context-code-p)
                      ;;FIXME keymap not updated
                      ;; (add-hook 'post-command-hook 'erefactor-lhl--post-command)
                      )))))))
        ;; completely ignore all errors
        (error nil)))))

(defun erefactor-hl--move-symbol (forward-p)
  (let* ((ovs (sort (copy-sequence erefactor-hl--overlays)
                    `(lambda (x y)
                       (,(if forward-p '< '>)
                        (overlay-start x)
                        (overlay-start y)))))
         (ov (erefactor--find (lambda (x) (overlay-get x 'erefactor-overlay-p))
                              (overlays-at (point))))
         (ov2 (cadr (memq ov ovs))))
    (when (or ov2 ovs)
      (let ((next (overlay-start (or ov2 (car ovs)))))
        (when next
          (goto-char next))))))

(define-minor-mode erefactor-highlight-mode
  "Toggle highlight mode on or off.
In highlight mode, the highlight the current symbol if recognize
as a local variable.
"
  :group 'erefactor
  (cond
   (erefactor-highlight-mode
    (erefactor-lhl--start)
    ;; FIXME suppress auto-highlight (auto-highlight-symbol.el)
    (set (make-local-variable 'ahs-face-check-include-overlay) t))
   (t
    (erefactor-lhl--stop)
    (erefactor-lhl--dehihglight)
    (kill-local-variable 'ahs-face-check-include-overlay))))

;;;###autoload
(defun erefactor-lazy-highlight-turn-on ()
  (erefactor-highlight-mode 1))

(defun erefactor-lazy-highlight-suspend ()
  (setq erefactor-lhl--suspended t))

(defun erefactor-lazy-highlight-resume ()
  (setq erefactor-lhl--suspended nil))

(defun erefactor-highlight-previous-symbol ()
  "Move to previous highlighting symbol."
  (interactive)
  (erefactor-hl--move-symbol nil))

(defun erefactor-highlight-next-symbol ()
  "Move to next highlighting symbol."
  (interactive)
  (erefactor-hl--move-symbol t))

;;;
;;; Simple check for evaluating function
;;;

(defvar erefactor-check--eval-alist
  '((eval-last-sexp after erefactor-check-eval-last-sexp)
    (eval-defun after erefactor-check-eval-defun)))

;; hack function ;-)
(defun erefactor-check--expand-closure (closure)
  (unless (eq (car-safe closure) 'closure)
    (error "Not a closure"))
  (let ((env (nth 1 closure))
        (vars (nth 2 closure))
        (body (nthcdr 3 closure)))
    (let ((let-vars nil)
          (def-vars nil))
      (mapc
       (lambda (v)
         (cond
          ((consp v)
           (push (list (car v) (cdr v)) let-vars))
          ((eq v t))
          ((symbolp v)
           (push v def-vars))
          (t (error "Not yet supported %s" v))))
       env)
      (append
       (mapcar (lambda (v) `(defvar ,v)) def-vars)
       `((let ,let-vars (defun dummy ,vars ,@body)))))))

(defun erefactor-check--closure-pseudo-source (closure)
  (let ((code (erefactor-check--expand-closure closure)))
    (with-output-to-string
      (dolist (c code)
        (pp c)))))

(defun erefactor-check--form (form)
  (cond
   ((memq (car-safe form) '(defun defun* defsubst))
    (let ((func (cadr form)))
      (when (and (symbolp func)
                 (functionp func))
        (erefactor-check--function func))))))

(defun erefactor-check--function (function)
  (let ((warns (erefactor-check--function-warnings function)))
    (when warns
      (let ((msg (mapconcat
                  (lambda (x)
                    (propertize x 'face font-lock-warning-face))
                  warns ", ")))
        (message "%s -> %s" (current-message) msg)
        (ding)))))

(defun erefactor-check--function-warnings (function)
  (let ((raw (symbol-function function)))
    (unwind-protect
        (let ((buf (get-buffer "*Compile-Log*"))
              end)
          (when buf
            (with-current-buffer buf
              (setq end (point-max))))
          ;; inhibit displaying *Compile-Log* window
          (save-window-excursion
            (let ((inhibit-redisplay t)
                  (byte-compile-warnings t)
                  (byte-compile-unresolved-functions))
              (cond
               ((eq (car-safe raw) 'closure)
                (let ((code (erefactor-check--closure-pseudo-source raw)))
                  (with-temp-buffer
                    (insert code)
                    (let ((lexical-binding t))
                      (byte-compile-from-buffer (current-buffer))))))
               (t
                (byte-compile function)))
              (byte-compile-warn-about-unresolved-functions)))
          (erefactor-check--gather-warnings end))
      ;; restore function body
      (fset function raw))))

(defun erefactor-check--gather-warnings (end)
  (let ((buf (get-buffer "*Compile-Log*"))
        res)
    (when buf
      (with-current-buffer buf
        (save-excursion
          (goto-char end)
          (while (re-search-forward "\\(?:Warning\\|Error\\): \\(.*\\)\\(?:\n +\\(.*\\)\\)?" nil t)
            (let ((line (concat (match-string 1) (match-string 2))))
              (setq res (cons line res))))))
      (nreverse res))))

;;;###autoload
(define-minor-mode erefactor-check-eval-mode
  "Display compiling warnings when \\[eval-last-sexp], \\[eval-defun]
"
  t nil nil
  (dolist (x erefactor-check--eval-alist)
    (let ((enabler
           (if erefactor-check-eval-mode
               'ad-enable-advice
             'ad-disable-advice)))
      (funcall enabler (nth 0 x) (nth 1 x) (nth 2 x))
      (funcall 'ad-activate (nth 0 x)))))

(defadvice eval-last-sexp
  (after erefactor-check-eval-last-sexp (edebug-it) activate)
  (when (erefactor-interactive-p)
    ;; call `preceding-sexp' same as `eval-last-sexp'
    (erefactor-check--form (preceding-sexp))))

(defadvice eval-defun
  (after erefactor-check-eval-defun (edebug-it) activate)
  (when (erefactor-interactive-p)
    (unless edebug-it
      ;; get FORM same as `eval-defun'
      (let ((form (save-excursion
                    (end-of-defun)
                    (beginning-of-defun)
                    (read (current-buffer)))))
        (erefactor-check--form form)))))

;;;
;;; Asynchronous Elint
;;;

(defcustom erefactor-lint-emacsen nil
  "*Emacs executables.

Examples:
\(setq erefactor-lint-emacsen
    '\(\"emacs-21\" \"emacs-22.1\" \"emacs-23.2\" \"emacs-current\"))
"
  :group 'erefactor
  :type '(list file))

(defcustom erefactor-lint-path-alist nil
  "*Associate list key is file name of Elisp.
value is `load-path' that required by key file if key file require some module.

Examples:
\(setq erefactor-lint-path-alist
   '\((\"/home/bob/.emacs.d/linting-file.el\"
       \"/home/bob/.emacs.d/misc\"))


\"/home/bob/.emacs.d/misc\" directory have some requiring module(s).
"
  :group 'erefactor
  :type '(list (list file)))

(defun erefactor-lint--running-p ()
  (let ((buffer (erefactor-lint--get-buffer)))
    (get-buffer-process buffer)))

(defun erefactor-lint--async (file commands)
  (let ((command (car commands))
        (rest (cdr commands)))
    (let ((proc (erefactor-lint--internal command file)))
      (set-process-sentinel
       proc
       `(lambda (p e)
          (when (eq (process-status p) 'exit)
            (with-current-buffer (process-buffer p)
              (erefactor-lint--append "\n\n")
              (erefactor-lint--exit-mode-line p))
            (when ',rest
              (erefactor-lint--async ,file ',rest))))))))

(defun erefactor-lint--exit-mode-line (process)
  (with-current-buffer (process-buffer process)
    (let* ((code (process-exit-status process))
           (msg  (format " (Exit [%d])" code)))
      (setq mode-line-process
            (propertize msg 'face
                        (if (= code 0)
                            'compilation-info 'compilation-error))))))

(defun erefactor-lint--internal (command file)
  (let* ((args (erefactor-lint--command-args command file))
         (buffer (erefactor-lint--get-buffer)))
    (display-buffer buffer)
    (with-current-buffer buffer
      (erefactor-lint--append (format "----- Linting by %s -----\n" command))
      (let ((proc (apply 'start-process "Async Elint" (current-buffer)
                         command args)))
        (set-process-sentinel proc (lambda (p e)))
        (setq mode-line-process
              (propertize " (Running)" 'face 'compilation-warning))
        proc))))

(defun erefactor-lint--initialize ()
  (with-current-buffer (erefactor-lint--get-buffer)
    (let ((inhibit-read-only t)
          buffer-read-only)
      (erase-buffer))))

(defun erefactor-lint--command-args (command file &optional temp-file)
  (let* ((path (erefactor-ref file erefactor-lint-path-alist))
         (version (erefactor-emacs-version command t))
         (sexp `(progn
                  (setq load-path (append load-path ',path))
                  (find-file ,(or temp-file file))
                  (goto-char (point-min))
                  (condition-case err
                      (let (sexp)
                        (while t
                          (setq sexp (read (current-buffer)))
                          (cond
                           ((memq (car-safe sexp) '(require))
                            (princ (format "Evaluating %s...\n" sexp))
                            (eval sexp))
                           ((eq (car-safe sexp) 'eval-when-compile)
                            (princ (format "Evaluating %s...\n" `(progn ,@(cdr-safe sexp))))
                            (eval `(progn ,@(cdr-safe sexp)))))))
                    (error nil))
                  ;;TODO trick
                  (macroexpand '(labels ()))
                  (elint-initialize)
                  (elint-current-buffer)
                  (with-current-buffer "*Elint*"
                    (princ (buffer-string)))))
         (eval-form (prin1-to-string sexp))
         (buffer (erefactor-lint--get-buffer))
         cmdline)
    (list "-batch" "-eval" eval-form)))

(defun erefactor-lint--get-buffer ()
  (get-buffer-create "*Async Elint*"))

(defun erefactor-lint--append (&rest strings)
  (let (buffer-read-only)
    (goto-char (point-max))
    (apply 'insert strings)))

;;;###autoload
(defun erefactor-lint ()
  "Execuet Elint in new Emacs process."
  (interactive)
  (erefactor-lint--initialize)
  (let ((command (expand-file-name (invocation-name) (invocation-directory)))
        (file (expand-file-name (buffer-file-name))))
    (let ((proc (erefactor-lint--internal command file)))
      (set-process-sentinel proc
                            (lambda (p e)
                              (when (eq (process-status p) 'exit)
                                (erefactor-lint--exit-mode-line p)))))))

;;;###autoload
(defun erefactor-lint-by-emacsen ()
  "Execuet Elint in new Emacs processes.
See variable `erefactor-lint-emacsen'."
  (interactive)
  (when (erefactor-lint--running-p)
    (error "Active process is running"))
  (unless erefactor-lint-emacsen
    (error "No command found."))
  (let ((file (expand-file-name (buffer-file-name))))
    (erefactor-lint--initialize)
    (erefactor-lint--async file erefactor-lint-emacsen)))

;;;
;;; flymake (experimental)
;;;

(require 'flymake nil t)

(defconst erefactor-flymake--allowed-file-name-masks
  '("\\.el$" erefactor-flymake--init erefactor-flymake--cleanup
    erefactor-flymake--get-real-file-name))

(defconst erefactor-flymake--error-line-patterns
  '("^\\([^:]+\\.el\\):\\([0-9]+\\):\\([0-9]+\\):[ ]*\\(.+\\)" 1 2 3 4))

(defvar erefactor-flymake-temp-file nil)
(defconst erefactor-flymake-error-buffer-name " *Erefactor errors* ")

(when (boundp 'flymake-allowed-file-name-masks)
  (add-to-list 'flymake-allowed-file-name-masks
               erefactor-flymake--allowed-file-name-masks))

(when (boundp 'flymake-err-line-patterns)
  (add-to-list 'flymake-err-line-patterns
               erefactor-flymake--error-line-patterns))

(defun erefactor-flymake--cleanup ()
  (flymake-safe-delete-file erefactor-flymake-temp-file)
  (setq flymake-last-change-time nil))

(defun erefactor-flymake--get-real-file-name (name)
  (or
   (cl-loop with temp-name = name
            for b in (buffer-list)
            when (let ((value (buffer-local-value 'erefactor-flymake-temp-file b)))
                   (and value
                        (string= temp-name (file-name-nondirectory value))))
            return (buffer-file-name b))
   (buffer-file-name)))

(defun erefactor-flymake--init ()
  (unless erefactor-flymake-temp-file
    (set (make-local-variable 'erefactor-flymake-temp-file)
         ;; match to `erefactor-flymake--error-line-patterns'
         (concat (make-temp-file "erefactor-") ".el")))
  (let ((file (buffer-file-name))
        (command (expand-file-name (invocation-name) (invocation-directory)))
        temp-file)
    (when (buffer-modified-p)
      (save-restriction
        (widen)
        (let ((coding-system-for-write buffer-file-coding-system))
          (write-region (point-min) (point-max) erefactor-flymake-temp-file nil 'no-msg)
          (setq temp-file erefactor-flymake-temp-file))))
    (list command
          (erefactor-lint--command-args command file temp-file))))

(defalias 'erefactor-flymake--have-errs-p 'erefactor-flymake--data)

(defun erefactor-flymake-display-errors ()
  (interactive)
  (if (not (erefactor-flymake--have-errs-p))
      (message "No errors or warnings")
    (let ((buf (get-buffer-create erefactor-flymake-error-buffer-name))
	  (title (erefactor-flymake--err-title))
	  (errs (erefactor-flymake--err-list)))
      (with-current-buffer buf
	(erase-buffer)
	(erefactor-flymake--insert-errors title errs))
      (save-window-excursion
        (display-buffer buf)
        (let ((event (read-event)))
          (setq unread-command-events (list event)))))))

(defun erefactor-flymake--insert-errors (title errs)
  (save-excursion
    (insert title "\n\n")
    (dolist (x errs)
      (insert x "\n"))))

(defun erefactor-flymake--err-get-title (x) (nth 0 x))
(defun erefactor-flymake--err-get-errs (x) (nth 1 x))

(defun erefactor-flymake--current-line-no ()
  ;; come from flymake 23.4
  (count-lines (point-min) (if (eobp) (point) (1+ (point)))))

(defun erefactor-flymake--data ()
  (let* ((line-no (erefactor-flymake--current-line-no))
         (info (nth 0 (flymake-find-err-info flymake-err-info line-no))))
    (flymake-make-err-menu-data line-no info)))

(defun erefactor-flymake--err-title ()
  (erefactor-flymake--err-get-title (erefactor-flymake--data)))

(defun erefactor-flymake--err-list ()
  (mapcar 'car (erefactor-flymake--err-get-errs (erefactor-flymake--data))))

;;;
;;; Main commands
;;;

(defun erefactor--rename-in-files (old-name new-name files)
  (dolist (file files)
    (erefactor--with-file file
      (erefactor-rename-region old-name new-name))))

;;;###autoload
(defun erefactor-rename-symbol-in-package (old-name new-name)
  "Rename symbol at point with queries.
This affect to current buffer and requiring modules.

Please remember, this function only works well if
the module have observance of `require'/`provide' system."
  (interactive
   (erefactor-rename-symbol-read-args))
  (let* ((symbol (intern-soft old-name))
         (guessed-files (erefactor--guessed-using-files symbol)))
    (when (buffer-file-name)
      (unless (member (buffer-file-name) guessed-files)
        (setq guessed-files (cons (buffer-file-name) guessed-files))))
    (erefactor--rename-in-files old-name new-name guessed-files)))

;;;###autoload
(defun erefactor-rename-symbol-in-buffer (old-name new-name)
  "Rename symbol at point resolving reference local variable
as long as i can with queries. This affect to current buffer."
  (interactive
   (erefactor-rename-symbol-read-args))
  (let ((region (erefactor--find-local-binding old-name)))
    (erefactor-rename-region old-name new-name region)))

;;;###autoload
(defun erefactor-change-prefix-in-buffer (old-prefix new-prefix)
  "Rename symbol prefix with queries.

OLD-PREFIX: `foo-' -> NEW-PREFIX: `baz-'
`foo-function1' -> `baz-function1'
`foo-variable1' -> `baz-variable1'"
  (interactive
   (erefactor-change-prefix-read-args))
  (erefactor-change-symbol-prefix old-prefix new-prefix))

;;;###autoload
(defun erefactor-add-current-defun ()
  "Add current defun form to `load-history'
This is usefull when creating new definition."
  (interactive)
  (unless (buffer-file-name)
    (error "Buffer is not associated any file"))
  (save-excursion
    (end-of-defun)
    (beginning-of-defun)
    (let* ((sexp (read (current-buffer)))
           (types (cdr (assq (car sexp) erefactor-def-alist)))
           (name (cadr sexp)))
      (dolist (type types)
        (let ((hist (erefactor--find-load-history type name)))
          ;; when not loaded in `load-history'
          (unless hist
            (erefactor--add-load-name
             (buffer-file-name) type name))))
      (message "%s" name))))

;;;###autoload
(defun erefactor-eval-current-defun (&optional edebug-it)
  "Evaluate current defun and add definition to `load-history'"
  (interactive "P")
  (eval-defun edebug-it)
  (when buffer-file-name
    (erefactor-add-current-defun)))

;;;###autoload
(defun erefactor-highlight-current-symbol ()
  "Highlight current symbol in this buffer.
Force to dehighlight \\[erefactor-dehighlight-all-symbol]"
  (interactive)
  (let ((symbol (thing-at-point 'symbol)))
    (erefactor-hl--dehighlight-all)
    (unless symbol
      (error "No symbol at point"))
    (erefactor-hl--update-region
     (point-min) (point-max) (erefactor-create-regexp symbol))
    (erefactor-lazy-highlight-suspend)
    (add-hook 'after-change-functions 'erefactor-hl--dehighlight-after-change)))

(defun erefactor-dehighlight-all-symbol ()
  "Dehighlight the all highlighted symbols in this buffer."
  (interactive)
  (erefactor-hl--dehighlight-all)
  (erefactor-lazy-highlight-resume))

;;;
;;; map
;;;

;;;###autoload
(defvar erefactor-map
  (let ((map (make-sparse-keymap)))

    (define-key map "L" 'erefactor-lint-by-emacsen)
    (define-key map "R" 'erefactor-rename-symbol-in-package)
    (define-key map "A" 'erefactor-add-current-defun)
    (define-key map "c" 'erefactor-change-prefix-in-buffer)
    (define-key map "d" 'erefactor-dehighlight-all-symbol)
    (define-key map "h" 'erefactor-highlight-current-symbol)
    (define-key map "l" 'erefactor-lint)
    (define-key map "r" 'erefactor-rename-symbol-in-buffer)
    (define-key map "x" 'erefactor-eval-current-defun)
    (define-key map "?" 'erefactor-flymake-display-errors)

    map))

;;
;; Compatibility for other elisp
;;

(eval-after-load 'auto-highlight-symbol
  `(progn
     (add-to-list 'ahs-inhibit-face-list 'erefactor-highlight-face)))

;;;###autoload(add-hook 'emacs-lisp-mode-hook 'erefactor-lazy-highlight-turn-on)
;;;###autoload(add-hook 'lisp-interaction-mode-hook 'erefactor-lazy-highlight-turn-on)

(provide 'erefactor)

;;; erefactor.el ends here
