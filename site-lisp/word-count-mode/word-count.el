;;;;; word-count.el - Counting word for Emacsen.
;;
;; AUTHOR:  Hiroyuki Komatsu <komatsu@taiyaki.org>
;; LICENCE: GPL2
;; $Id: word-count.el,v 1.3 2003/10/09 22:40:40 komatsu Exp $
;;
;; How to install:
;; 1). Download this file from the following URL.
;; <http://www.taiyaki.org/elisp/word-count/src/wourd-count.el>
;;
;; 2). Where this file is stored to ~/elisp/, please add the following lines to your ".emacs".
;; 
;; (setq load-path (cons (expand-file-name "~/elisp") load-path))
;; (autoload 'word-count-mode "word-count"
;;           "Minor mode to count words." t nil)
;; (global-set-key "\M-+" 'word-count-mode)
;;
;; How to use:
;; 1). M-+ (word-count-mode) toggles word-count mode.
;; 2). M-[space] (word-count-set-area) sets area for counting words.
;; 3). M-x word-count-set-region sets region or paragraph for counting words.
;; 4). M-x word-count-set-marker sets marker for counting words.


;; ----------------------------------------------------------------------
;; Mell
;; ----------------------------------------------------------------------

;; Checking Emacs or XEmacs. (APEL?)
(if (not (boundp 'running-xemacs))
    (defconst running-xemacs nil))

(defun mell-check-value (value)
  (and (boundp value)
       (symbol-value value)))

;; mell-region-active-p
(if running-xemacs
    (defun mell-region-active-p ()
      (region-active-p))
  (defun mell-region-active-p ()
    (mell-check-value 'mark-active))
  )

;; mell-transient-mode-p
(if running-xemacs
    (defun mell-transient-mode-p ()
      (mell-check-value 'zmacs-regions))
  (defun mell-transient-mode-p ()
    (mell-check-value 'transient-mark-mode))
  )

;; Define mell-transient-region-active-p
(defun mell-transient-region-active-p ()
  (and (mell-transient-mode-p)
       (mell-region-active-p)))

;; ------------------------------------------------------------

(defun mell-marker-set (marker &optional position buffer type)
  (or (markerp (eval marker))
      (set marker (make-marker)))
  (or position
      (setq position (point)))
  (set-marker (eval marker) position buffer)
  (set-marker-insertion-type (eval marker) type)
  )

(defun mell-defvar (symbol value &optional doc-string)
  (if (not (boundp symbol))
      (set symbol value))
  (if doc-string
      (put symbol 'variable-documentation doc-string))
  symbol)

(defun mell-defvar-locally (symbol initvalue &optional docstring)
  (mell-defvar symbol initvalue docstring)
  (make-variable-buffer-local symbol)
  symbol)

(defun mell-set-minor-mode (name modeline &optional key-map)
  (make-variable-buffer-local name)
  (setq minor-mode-alist
	(mell-alist-add minor-mode-alist (list name modeline)))
  (and key-map
       (setq minor-mode-map-alist
	     (mell-alist-add minor-mode-map-alist (cons name key-map)))
       )
  )

(defun mell-point-at-bop (&optional point)
  (save-excursion
    (goto-char (or point (point)))
    (backward-paragraph 1)
    (point)))

(defun mell-point-at-eop (&optional point)
  (save-excursion
    (goto-char (or point (point)))
    (forward-paragraph 1)
    (point)))

;; mell-alist ------------------------------------------------------------

(defun mell-alist-add! (alist new-cons)
  (if (null alist)
      (error "mell-alist-add! can not deal nil as an alist.")
    (let ((current-cons (assoc (car new-cons) alist)))
      (if current-cons
	  (setcdr current-cons (cdr new-cons))
	(if (car alist)
	    (nconc alist (list new-cons))
	  (setcar alist new-cons))
	)
      alist)))
  
(defun mell-alist-add (alist new-cons)
  (if (null alist)
      (list new-cons)
    (let ((return-alist (copy-alist alist)))
      (mell-alist-add! return-alist new-cons)
      return-alist)))
  
(defun mell-alist-delete (alist key)
  (if key
      (let (return-alist)
	(mapcar '(lambda (x)
		   (or (equal key (car x))
		       (setq return-alist (cons x return-alist))))
		alist)
	(if return-alist
	    (reverse return-alist)
	  (list nil)))
    alist)
  )

(defun mell-alist-get-value (key alist)
  "Return a value corresponded to KEY or 't' from ALIST."
  (if (consp alist)
      (let ((assoc-pair (assoc key alist)))
        (if assoc-pair
            (cdr assoc-pair)
          (cdr (assoc t alist))))
    alist))

;; mell-string ------------------------------------------------------------

(defun mell-string-split (string regexp)
  "Divide STRING from REGEXP."
  (let ((start 0) match-list splited-list)
    (while (string-match regexp string start)
      (setq match-list
	    (append match-list (list (match-beginning 0) (match-end 0))))
      (setq start (match-end 0))
      )
    (setq match-list (append '(0) match-list (list (length string))))
    (while match-list
      (setq splited-list 
	    (cons (substring string (nth 0 match-list) (nth 1 match-list))
		  splited-list))
      (setq match-list (nthcdr 2 match-list))
      )
    (reverse splited-list)))

(defun mell-string-replace (target-string from-regexp to-string)
  "Replace TARGET-STRING from FROM-REGEXP to TO-STRING."
  (if (string-match from-regexp target-string)
      (setq target-string
	    (mapconcat '(lambda (x) x)
		       (mell-string-split target-string from-regexp)
		       to-string))
    )
  target-string)

;; mell-match ------------------------------------------------------------

(defun mell-match-count-string (regexp string)
  (save-match-data
    (let ((i 0) (n 0))
      (while (and (string-match regexp string i) (< i (match-end 0)))
	(setq i (match-end 0))
	(setq n (1+ n)))
      n)))
  
(if running-xemacs
    (eval
     '(defun mell-match-count-region (regexp start end &optional buffer)
	(mell-match-count-string regexp (buffer-substring start end buffer))
	))
  (eval
   '(defun mell-match-count-region (regexp start end &optional buffer)
      (save-excursion
	(and buffer (set-buffer buffer))
	(mell-match-count-string regexp (buffer-substring start end))
	)))
  )

;; mell-sign ------------------------------------------------------------

(defun mell-color-find (color-name &optional alt-tty-color-num)
  (if window-system color-name
    (and (functionp 'find-tty-color)
	 (or (and color-name (find-tty-color color-name))
	     (nth alt-tty-color-num (tty-color-list))))
    ))

(defvar mell-sign-marker-overlay-alist (list nil))
(defun mell-sign-marker (marker &optional face)
  (let ((overlay (cdr (assoc marker mell-sign-marker-overlay-alist)))
	(start (min marker (1- (point-max)))) ;; for EOB
	(end (min (1+ marker) (point-max))))
    (if overlay
	(move-overlay overlay start end (marker-buffer marker))
      (setq overlay (make-overlay start end (marker-buffer marker)))
      (mell-alist-add! mell-sign-marker-overlay-alist (cons marker overlay))
      )
    (overlay-put overlay 'face (or face 'highlight))
    (overlay-put overlay 'evaporate t)
    (add-hook 'post-command-hook 'mell-sign-marker-redisplay t t)
    ))

(defun mell-sign-marker-off (marker)
  (let ((overlay (cdr (assoc marker mell-sign-marker-overlay-alist))))
    (if overlay
	(delete-overlay overlay))
    (setq mell-sign-marker-overlay-alist
	  (mell-alist-delete mell-sign-marker-overlay-alist marker))
    (remove-hook 'post-command-hook 'mell-sign-marker-redisplay t)
    ))

(defun mell-sign-marker-redisplay ()
  (mapcar 
   '(lambda (cons) (mell-sign-marker (car cons)))
   mell-sign-marker-overlay-alist))

(defvar mell-sign-region-overlay-alist (list nil))
(defun mell-sign-region (start end &optional buffer face)
  (or buffer (setq buffer (current-buffer)))
  (let* ((region (list start end buffer))
	 (overlay (cdr (assoc region mell-sign-region-overlay-alist))))
    (if overlay
	(move-overlay overlay start end buffer)
      (setq overlay (make-overlay start end buffer nil t))
      (mell-alist-add! mell-sign-region-overlay-alist (cons region overlay))
      )
    (overlay-put overlay 'face (or face 'highlight))
    (overlay-put overlay 'evaporate t)
    ))

(defun mell-sign-region-off (start end &optional buffer)
  (or buffer (setq buffer (current-buffer)))
  (let* ((region (list start end buffer))
	 (overlay (cdr (assoc region mell-sign-region-overlay-alist))))
    (if overlay
	(delete-overlay overlay))
    (setq mell-sign-region-overlay-alist
	  (mell-alist-delete mell-sign-region-overlay-alist region))
    ))


;; ----------------------------------------------------------------------
;; word-count-mode
;; ----------------------------------------------------------------------

(defcustom word-count-non-character-regexp "[\n\t ]"
  "Regexp what is not counted as characters.")
(defcustom word-count-word-regexp "[a-z0-9_-]+"
  "Regexp what is counted as words.")
(defcustom word-count-non-line-regexp "^[\t ]*\n\\|^[\t ]+$"
  "Regexp what is not counted as lines.")
(defcustom word-count-preremove-regexp-alist
  '((latex-mode . ("\\\\%" "%.*$")) (tex-mode . ("\\\\%" "%.*$"))
    (html-mode . ("<[^>]*>")) (sgml-mode . ("<[^>]*>"))
    (t . nil))
  "Regexp alist what is used by preremove operation.
These regexps are replaced to one space (ie '\\\\%' -> ' ', '%.*$' -> ' ').
A pair with 't' is a default.")
(defcustom word-count-modeline-string " WC:"
				  "String of modeline for word-count mode.")
(defcustom word-count-mode-hook nil
  "Function or functions called when word-count-mode is executed.")
(defcustom word-count-mode-init-hook nil
  "Function or functions called when word-count.el is loaded.")

(defcustom word-count-marker-foreground (mell-color-find "#D0D0D0" 7)
  "Color for word-count mode.")
(defcustom word-count-marker-background (mell-color-find "#5050A0" 3)
  "Color for word-count mode.")
(defcustom word-count-region-foreground (mell-color-find "#D0D0D0" 7)
  "Color for word-count mode.")
(defcustom word-count-region-background (mell-color-find "#5050A0" 3)
  "Color for word-count mode.")

(if (not (boundp 'word-count-marker-face))
    (progn
      (defcustom word-count-marker-face (make-face 'word-count-marker-face)
	"Face for word-count mode.")
      (set-face-foreground word-count-marker-face word-count-marker-foreground)
      (set-face-background word-count-marker-face word-count-marker-background)
      ))

(if (not (boundp 'word-count-region-face))
    (progn
      (defcustom word-count-region-face (make-face 'word-count-region-face)
	"Face for word-count mode.")
      (set-face-foreground word-count-region-face word-count-region-foreground)
      (set-face-background word-count-region-face word-count-region-background)
      ))

(global-set-key "\M-+" 'word-count-mode)
(defvar word-count-mode-map (make-sparse-keymap))
(define-key word-count-mode-map "\M- " 'word-count-set-area)


(defvar word-count-mode nil "*Non-nil means in an word-count mode.")
(mell-set-minor-mode 'word-count-mode 'word-count-modeline word-count-mode-map)

(mell-defvar-locally 'word-count-modeline " WC")
(mell-defvar-locally 'word-count-marker-beginning nil)
(mell-defvar-locally 'word-count-marker-end nil)

(defun word-count-mode (&optional arg)
  (interactive "P")
  (setq word-count-mode 
	(if (null arg) (not word-count-mode) (> (prefix-numeric-value arg) 0)))
  (if word-count-mode
      (word-count-mode-on)
    (word-count-mode-off))
  (run-hooks 'word-count-mode-hook)
  )

(defun word-count-mode-on ()
  (interactive)
  (setq word-count-mode t)
  (if (mell-transient-region-active-p)
      (word-count-set-region)
    (word-count-set-marker))
  (add-hook 'post-command-hook 'word-count-modeline-display t t)
  )

(defun word-count-mode-off ()
  (interactive)
  (setq word-count-mode nil)
  (remove-hook 'post-command-hook 'word-count-modeline-display t)
  (word-count-set-marker-off)
  (word-count-set-region-off)
  )

(defun word-count-set-area ()
  (interactive)
  (or word-count-mode
      (word-count-mode))
  (if (mell-transient-region-active-p)
      (word-count-set-region)
    (word-count-set-marker)
    ))

(defun word-count-set-marker ()
  (interactive)
  (or word-count-mode (word-count-mode))
  (word-count-set-region-off)
  (mell-marker-set 'word-count-marker-beginning)
  (mell-sign-marker word-count-marker-beginning word-count-marker-face)
  )

(defun word-count-set-marker-off ()
  (mell-sign-marker-off word-count-marker-beginning)
  )

(defun word-count-set-region ()
  (interactive)
  (or word-count-mode (word-count-mode))
  (word-count-set-marker-off)
  (if (mell-transient-region-active-p)
      (progn
	(mell-marker-set 'word-count-marker-beginning (min (mark) (point)))
	(mell-marker-set 'word-count-marker-end (max (mark) (point)) nil t)
	)
    (mell-marker-set 'word-count-marker-beginning (mell-point-at-bop))
    (mell-marker-set 'word-count-marker-end       (mell-point-at-eop) nil t)
    )
  (mell-sign-region word-count-marker-beginning word-count-marker-end nil
		    word-count-region-face)
  )

(defun word-count-set-region-off ()
  (mell-sign-region-off word-count-marker-beginning word-count-marker-end)
  (and (markerp word-count-marker-end)
       (set-marker word-count-marker-end nil))
  (setq word-count-marker-end nil)
  )

(defun word-count-modeline-display ()
  (setq word-count-modeline (word-count-modeline-create))
  (force-mode-line-update)
  )

(defun word-count-modeline-create ()
  (let ((beginning word-count-marker-beginning)
	(end (or word-count-marker-end (point))))
    (concat
     word-count-modeline-string
     (apply 'format "%d/%d/%d" (word-count-CWL-region beginning end))
     (if (mell-transient-region-active-p)
	 (apply 'format " (%d/%d/%d)" (word-count-CWL-region)))
     )))

(defun word-count-CWL-region (&optional start end)
  (word-count-CWL-string (word-count-buffer-substring start end)))

(defun word-count-CWL-string (string)
  (setq string (word-count-preremove-string string))
  (list
   (word-count-characters-string string t)
   (word-count-words-string      string t)
   (word-count-lines-string      string t)
   ))

(defun word-count-characters-region (&optional start end)
  (word-count-characters-string (word-count-buffer-substring start end)))

(defun word-count-words-region (&optional start end)
  (word-count-words-string (word-count-buffer-substring start end)))

(defun word-count-lines-region (&optional start end)
  (word-count-lines-string (word-count-buffer-substring start end)))

(defun word-count-buffer-substring (&optional start end)
  (or start (setq start (region-beginning)))
  (or end (setq end (region-end)))
  (buffer-substring start end))


(defun word-count-characters-string (string &optional nopreremove)
  (or nopreremove
      (setq string (word-count-preremove-string string)))
  (- (length string)
     (mell-match-count-string word-count-non-character-regexp string)
     ))

(defun word-count-words-string (string &optional nopreremove)
  (or nopreremove
      (setq string (word-count-preremove-string string)))
  (mell-match-count-string word-count-word-regexp string))

(defun word-count-lines-string (string &optional nopreremove)
  (or nopreremove
      (setq string (word-count-preremove-string string)))
  (- (1+ (mell-match-count-string
	  "\n" (substring string 0 (max 0 (1- (length string))))))
     (mell-match-count-string word-count-non-line-regexp string)
     ))


(defun word-count-preremove-string (string &optional patterns)
  (mapcar '(lambda (pattern)
	     (setq string (mell-string-replace string pattern " ")))
	  (or patterns
	      (mell-alist-get-value major-mode
				    word-count-preremove-regexp-alist)))
  string)

(run-hooks 'word-count-mode-init-hook)
(provide 'word-count)
;; ----------------------------------------------------------------------
