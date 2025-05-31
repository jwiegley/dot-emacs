;;;----------------------------------------------------------------
;; * OUTLINE MODE
;;;----------------------------------------------------------------
;; :PROPERTIES:
;; :CUSTOM_ID: outline-mode
;; :END:

(use-package outline
  :bind (:map outline-minor-mode-map
              ("TAB" . outline-cycle)
              ("<tab>" . outline-cycle)
              ("C-c C-n" . outline-next-visible-heading)
              ("C-c C-p" . outline-previous-visible-heading)
              ("C-c C-u" . outline-up-heading)
              ("C-c M-<up>" . outline-move-subtree-up)
              ("C-c M-<down>" . outline-move-subtree-down)
              ("C-c M-<left>" . outline-promote)
              ("C-c M-<right>" . outline-demote))
  :config
  (define-key outline-minor-mode-map (kbd "<backtab>")
              ;; (lambda () (interactive)
              ;;   (outline-back-to-heading)
              ;;   (outline-cycle))
              #'outline-cycle-all)

  (defun outline-next-line ()
    "Forward line, but mover over invisible line ends.
Essentially a much simplified version of `next-line'."
    (interactive)
    (beginning-of-line 2)
    (while (and (not (eobp))
                (get-char-property (1- (point)) 'invisible))
      (beginning-of-line 2)))

  (defvar outline-cycle-emulate-tab nil
    "Use tab to indent (when not on a heading) in outline-minor-mode")

  (defun outline-cycle-all (&optional arg)
    (interactive "p")
    (let ((level (save-match-data (funcall outline-level))))
      (if (eq last-command 'outline-cycle-all)
          (progn (outline-show-all)
                 (setq this-command 'outline-show-all))
        (save-excursion
          (outline-back-to-heading)
          (call-interactively #'outline-hide-sublevels)))))
  
  (defun outline-cycle () (interactive)
         (cond
          ((save-excursion (beginning-of-line 1)
                           (and (looking-at outline-regexp)
                                ;; (not (equal (save-match-data (funcall outline-level))
                                ;;             1000))
                                ))
           ;; At a heading: rotate between three different views
           (outline-back-to-heading)
           (let ((goal-column 0) beg eoh eol eos)
             ;; First, some boundaries
             (save-excursion
               (outline-back-to-heading)           (setq beg (point))
               (save-excursion (outline-next-line) (setq eol (point)))
               (outline-end-of-heading)            (setq eoh (point))
               (outline-end-of-subtree)            (setq eos (point)))
             ;; Find out what to do next and set `this-command'
             (cond
              ((= eos eoh)
               ;; Nothing is hidden behind this heading
               (message "EMPTY ENTRY"))
              ((>= eol eos)
               ;; Entire subtree is hidden in one line: open it
               (outline-show-entry)
               (outline-show-children)
               (message "CHILDREN")
               (setq this-command 'outline-cycle-children))
              ((eq last-command 'outline-cycle-children)
               ;; We just showed the children, now show everything.
               (outline-show-subtree)
               (message "SUBTREE"))
              (t
               ;; Default action: hide the subtree.
               (outline-hide-subtree)
               (message "FOLDED")))))

          ;; TAB emulation
          (outline-cycle-emulate-tab
           (call-interactively (key-binding (vector last-input-event)))
           ;; (indent-according-to-mode)
           )

          (t
           ;; Not at a headline: Do whatever this key would do otherwise.
           ;; (outline-back-to-heading)
           (let ((normal-binding (let ((outline-minor-mode nil))
                                   (key-binding (this-command-keys-vector)))))
             (if normal-binding
                 (progn
                   (setq this-command normal-binding)
                   (call-interactively normal-binding))
               (indent-according-to-mode)))))))

(use-package outline
  :when (version< "28.0" emacs-version)
  :defer
  :bind (:map outline-navigation-repeat-map
              ("TAB" . nil)
              ("<tab>" . nil)
              ("C-n" . nil)
              ("C-p" . nil)
              ("C-f" . nil)
              ("C-b" . nil)
              ("M-<left>" . outline-promote)
              ("M-<right>" . outline-demote)
              ("M-<up>" . outline-move-subtree-up)
              ("M-<down>" . outline-move-subtree-down))
  :config
  (dolist (sym '(outline-promote outline-demote outline-cycle
                 outline-move-subtree-up outline-move-subtree-down))
    (put sym 'repeat-map 'outline-navigation-repeat-map)))

;;;----------------------------------------------------------------
;; * HIDESHOW (built in)
;;;----------------------------------------------------------------
(use-package hideshow ; built-in
  :commands (hs-cycle
             hs-global-cycle)
  :bind (:map prog-mode-map
              ("C-<tab>" . hs-cycle)
              ("<backtab>" . hs-global-cycle)
              ("C-S-<iso-lefttab>" . hs-global-cycle))
  :config
  (setq hs-hide-comments-when-hiding-all nil
        ;; Nicer code-folding overlays (with fringe indicators)
        hs-set-up-overlay #'hideshow-set-up-overlay-fn)

  (defface hideshow-folded-face
    `((t (:inherit font-lock-comment-face :weight light)))
    "Face to hightlight `hideshow' overlays."
    :group 'hideshow)
  
  (defun hideshow-set-up-overlay-fn (ov)
    (when (eq 'code (overlay-get ov 'hs))
      (overlay-put
       ov 'display (propertize "  [...]  " 'face 'hideshow-folded-face))))
  
  (dolist (hs-command (list #'hs-cycle
                            #'hs-global-cycle))
    (advice-add hs-command :before
                (lambda (&optional end) "Advice to ensure `hs-minor-mode' is enabled"
                  (unless (bound-and-true-p hs-minor-mode)
                    (hs-minor-mode +1)))))

  (defun hs-cycle (&optional level)
    (interactive "p")
    (save-excursion
      (if (= level 1)
          (pcase last-command
            ('hs-cycle
             (hs-hide-level 1)
             (setq this-command 'hs-cycle-children))
            ('hs-cycle-children
             ;;TODO: Fix this case. `hs-show-block' needs to be called twice to
             ;;open all folds of the parent block.
             (hs-show-block)
             (hs-show-block)
             (setq this-command 'hs-cycle-subtree))
            ('hs-cycle-subtree
             (hs-hide-block))
            (_
             (if (not (hs-already-hidden-p))
                 (hs-hide-block)
               (hs-hide-level 1)
               (setq this-command 'hs-cycle-children))))
        (hs-hide-level level)
        (setq this-command 'hs-hide-level))))
  
  (defun hs-global-cycle ()
    (interactive)
    (pcase last-command
      ('hs-global-cycle
       (save-excursion (hs-show-all))
       (setq this-command 'hs-global-show))
      (_ (hs-hide-all))))  
  
  ;; extra folding support for more languages
  (unless (assq 't hs-special-modes-alist)
    (setq hs-special-modes-alist
          (append
           '((vimrc-mode "{{{" "}}}" "\"")
             ;; (yaml-mode "\\s-*\\_<\\(?:[^:]+\\)\\_>"
             ;;            ""
             ;;            "#"
             ;;            +fold-hideshow-forward-block-by-indent-fn nil)
             ;; (haml-mode "[#.%]" "\n" "/" +fold-hideshow-haml-forward-sexp-fn nil)
             ;; (ruby-mode "class\\|d\\(?:ef\\|o\\)\\|module\\|[[{]"
             ;;            "end\\|[]}]"
             ;;            "#\\|=begin"
             ;;            ruby-forward-sexp)
             ;; (enh-ruby-mode "class\\|d\\(?:ef\\|o\\)\\|module\\|[[{]"
             ;;                "end\\|[]}]"
             ;;                "#\\|=begin"
             ;;                enh-ruby-forward-sexp nil)
             (matlab-mode "^\s*if\\|switch\\|case\\|otherwise\\|while\\|^\s*for\\|try\\|catch\\|function"
                          "end"
                          "" (lambda (_arg) (matlab-forward-sexp)))
             (nxml-mode "<!--\\|<[^/>]*[^/]>"
                        "-->\\|</[^/>]*[^/]>"
                        "<!--" sgml-skip-tag-forward nil))
           hs-special-modes-alist
           '((t))))))

(provide 'setup-folds)
