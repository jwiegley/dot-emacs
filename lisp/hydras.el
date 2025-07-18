(defhydra hydra-rectangle
  (:body-pre (rectangle-mark-mode 1)
             :color pink
             :post (deactivate-mark))
  "
  ^_k_^     _d_elete    _s_tring
_h_   _l_   _o_k        _y_ank
  ^_j_^     _n_ew-copy  _r_eset
^^^^        _e_xchange  _u_ndo
^^^^        ^ ^         _p_aste
"
  ("h" rectangle-backward-char nil)
  ("l" rectangle-forward-char nil)
  ("k" rectangle-previous-line nil)
  ("j" rectangle-next-line nil)
  ("e" hydra-ex-point-mark nil)
  ("n" copy-rectangle-as-kill nil)
  ("d" delete-rectangle nil)
  ("r" (if (region-active-p)
           (deactivate-mark)
         (rectangle-mark-mode 1)) nil)
  ("y" yank-rectangle nil)
  ("u" undo nil)
  ("s" string-rectangle nil)
  ("p" kill-rectangle nil)
  ("o" nil nil))

;; (global-set-key (kbd "C-x SPC") 'hydra-rectangle/body)

(defhydra akirak/emacs-lisp-hydra
  (:hint nil)
  "
^^Eval             ^^Check            ^^Toggle
^^--------------   ^^---------------  ^^------------------------
_e_: eval-buffer   _l_: package-lint  _td_: debug-on-error [%s(if debug-on-error \"on\" \"off\")]
_me_: macroexpand

"
  ("e" eval-buffer :exit t)
  ("me" emacs-lisp-macroexpand :exit t)
  ("l" package-lint-current-buffer :exit t)
  ("td" toggle-debug-on-error))

;; Use this alias to run the hydra so that the hydra can become
;; context-sensitive in the future.
(defalias 'akirak/emacs-lisp-hydra 'akirak/emacs-lisp-hydra/body)

(bind-key "C-8"
          (defhydra hydra-unicode (:color blue)
            "Unicode"
            ("a" (insert "→") "arrow" :column "Symbols")
            ("o" (insert "°") "°")
            ("x" (insert "⨉") "cross")
            ("!" (insert "¬") "¬")
            ("+" (insert "±") "±")
            ("r" (insert "√") "√")
            ("^" (insert "∧") "∧")
            ("v" (insert "∨") "∨")
            ("\\" (insert "λ") "λ" :column "Letters")
            ("t" (insert "θ") "θ")
            ("p" (insert "φ") "φ")
            ("8" (insert "∞") "infinity")
            ("l" (insert "𝓁") "𝓁")
            ("R" (insert "ℝ") "ℝ")
            ("_i" (insert "ᵢ") "ᵢ")
            ("1" (insert "¹") "¹" :column "Numbers")
            ("2" (insert "²") "²")
            ("3" (insert "³") "³")
            (",0" (insert "₀") "₀")
            (",1" (insert "₁") "₁")
            (",2" (insert "₂") "₂")
            (",3" (insert "₃") "₃")
            ("c" (insert "∘") "∘" :column "Other")
            ("d" (insert "·") "·")
            ("/" (counsel-unicode-char) "search")
            ))

(defun mark-to-char-exclusive (arg char)
  "Mark up to but not including ARGth occurrence of CHAR."
  (interactive (list (prefix-numeric-value current-prefix-arg)
                     (read-char "Mark to char: " t)))
  (set-mark
   (save-excursion
     (move-to-char arg char)
     (backward-char)
     (point))))

(defun mark-to-char-inclusive (arg char)
  "Mark up to and including ARGth occurrence of CHAR."
  (interactive (list (prefix-numeric-value current-prefix-arg)
                     (read-char "Mark to char: " t)))
  (set-mark
   (save-excursion
     (move-to-char arg char)
     (point))))

(defhydra hydra-mark (:body-pre (set-mark-command nil) :color red)
  "
_w_, _,w_: word, symbol      _i'_, _a'_: string  _i)_, _a)_: pair
_t_, _f_: to char (exclude/include)   _0_, _$_: begin/end of line
_;_: comment   _u_: url    _e_: email      _>_: web-mode block or tag
_S_: sexp      _d_: defun  _p_: paragraph  _s_: sentence
_h_, _j_, _k_, _l_: move   _H-._: off
  "
  ("t" mark-to-char-exclusive)
  ("f" mark-to-char-inclusive)
  ("0" move-beginning-of-line)
  ("$" move-end-of-line)
  ("w" er/mark-word)
  (",w" er/mark-symbol)
  ("i'" er/mark-inside-quotes)
  ("a'" er/mark-outside-quotes)
  ("i)" er/mark-inside-pairs)
  ("a)" er/mark-outside-pairs)
  ("i]" er/mark-inside-pairs)
  ("a]" er/mark-outside-pairs)
  ("j" next-line)
  ("k" previous-line)
  ("h" left-char)
  ("l" right-char)
  (";" er/mark-comment)
  ("u" er/mark-url)
  ("e" er/mark-email)
  ("d" er/mark-defun)
  ("S" mark-sexp)
  ("s" mark-end-of-sentence)
  ("p" mark-paragraph)
  (">" web-mode-mark-and-expand)
  ("H-." deactivate-mark :exit t))

(defhydra hydra-projectile (:color teal
			           :columns 4)
  "Projectile"
  ("f"   projectile-find-file                "Find File")
  ("r"   projectile-recentf                  "Recent Files")
  ("z"   projectile-cache-current-file       "Cache Current File")
  ("x"   projectile-remove-known-project     "Remove Known Project")
  
  ("d"   projectile-find-dir                 "Find Directory")
  ("b"   projectile-switch-to-buffer         "Switch to Buffer")
  ("c"   projectile-invalidate-cache         "Clear Cache")
  ("X"   projectile-cleanup-known-projects   "Cleanup Known Projects")
  
  ("o"   projectile-multi-occur              "Multi Occur")
  ("s"   projectile-switch-project           "Switch Project")
  ("k"   projectile-kill-buffers             "Kill Buffers")
  ("q"   nil "Cancel" :color blue))

(defhydra hydra-global-org (:color blue)
  "Org"
  ("t" org-timer-start "Start Timer")
  ("s" org-timer-stop "Stop Timer")
  ;; This one requires you be in an orgmode doc, as it sets the timer for the header
  ("r" org-timer-set-timer "Set Timer")
  ;; output timer value to buffer
  ("p" org-timer "Print Timer")
  ;; used with (org-clock-persistence-insinuate) (setq org-clock-persist t)
  ("w" (org-clock-in '(4)) "Clock-In")
  ;; you might also want (setq org-log-note-clock-out t)
  ("o" org-clock-out "Clock-Out")
  ;; global visit the clocked task
  ("j" org-clock-goto "Clock Goto")
  ;; Don't forget to define the captures you want http://orgmode.org/manual/Capture.html
  ("c" org-capture "Capture")
  ("l" org-capture-goto-last-stored "Last Capture"))

(use-package helpful
  :ensure t
  :pretty-hydra
  ((:color teal :quit-key "q")
   ("Helpful"
    (("f" helpful-callable "callable")
     ("v" helpful-variable "variable")
     ("k" helpful-key "key")
     ("c" helpful-command "command")
     ("d" helpful-at-point "thing at point"))))
  :bind ("C-h" . helpful-hydra/body))

(pretty-hydra-define
  jp-toggles
  (:color amaranth :quit-key "q" :title jp-toggles--title)
  ("Basic"
   (("n" linum-mode "line number" :toggle t)
    ("w" whitespace-mode "whitespace" :toggle t)
    ("W" whitespace-cleanup-mode "whitespace cleanup" :toggle t)
    ("r" rainbow-mode "rainbow" :toggle t)
    ("L" page-break-lines-mode "page break lines" :toggle t))
   "Highlight"
   (("s" symbol-overlay-mode "symbol" :toggle t)
    ("l" hl-line-mode "line" :toggle t)
    ("x" highlight-sexp-mode "sexp" :toggle t)
    ("t" hl-todo-mode "todo" :toggle t))
   "UI"
   (("d" jp-themes-toggle-light-dark "dark theme" :toggle jp-current-theme-dark-p))
   "Coding"
   (("p" smartparens-mode "smartparens" :toggle t)
    ("P" smartparens-strict-mode "smartparens strict" :toggle t)
    ("S" show-smartparens-mode "show smartparens" :toggle t)
    ("f" flycheck-mode "flycheck" :toggle t))
   "Emacs"
   (("D" toggle-debug-on-error "debug on error" :toggle (default-value 'debug-on-error))
    ("X" toggle-debug-on-quit "debug on quit" :toggle (default-value 'debug-on-quit)))))

(defun jp-projects--title ()
  (let ((p (projectile-project-name)))
    (with-octicon "repo"
                  (if (s-blank-p p)
                      "Projects"
                    (s-concat "Projects (current: " p ")")))))

(pretty-hydra-define
  jp-projects
  (:color teal :quit-key "q" :title (jp-projects--title))
  ("Current Project"
   (("f" counsel-projectile "open file/buffer")
    ("b" counsel-projectile-switch-to-buffe "switch to buffer")
    ("d" counsel-projectile-find-dir "open directory")
    ("i" projectile-ibuffer "ibuffer")
    ("k" projectile-kill-buffers "kill buffers")
    ("I" projectile-invalidate-cache "invalidate cache"))
   "All Projects"
   (("p" jp-eyebrowse-switch-project "switch")
    ("r" jp-refresh-projectile-projects "refresh project list"))))

(defun dfeich/context-hydra-launcher ()
  "A launcher for hydras based on the current context."
  (interactive)
  (cl-case major-mode
    ('org-mode (let* ((elem (org-element-context))
                      (etype (car elem))
                      (type (org-element-property :type elem)))
                 (cl-case etype
                   (src-block (hydra-babel-helper/body))
                   (link (hydra-org-link-helper/body))
                   ((table-row table-cell) (hydra-org-table-helper/body) )
                   (t (message "No specific hydra for %s/%s" etype type)
                      (hydra-org-default/body))))
               )
    ('bibtex-mode (org-ref-bibtex-hydra/body))
    ('ibuffer-mode (hydra-ibuffer-main/body))
    (t (message "No hydra for this major mode: %s" major-mode))))

(global-set-key (kbd "<f9> <f9>") 'dfeich/context-hydra-launcher)

(major-mode-hydra-define
  emacs-lisp-mode nil
  ("Eval"
   (("b" eval-buffer "buffer")
    ("e" eval-defun "defun")
    ("r" eval-region "region"))
   "REPL"
   (("I" ielm "ielm"))
   "Test"
   (("t" ert "prompt")
    ("T" (ert t) "all")
    ("F" (ert :failed) "failed"))
   "Doc"
   (("d" describe-foo-at-point "thing-at-pt")
    ("f" describe-function "function")
    ("v" describe-variable "variable")
    ("i" info-lookup-symbol "info lookup"))))
