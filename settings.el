(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(Info-default-directory-list '("~/.emacs.d/lisp/org-mode/doc"))
 '(Info-fit-frame-flag nil)
 '(TeX-PDF-mode t)
 '(TeX-auto-save t)
 '(TeX-auto-untabify t)
 '(TeX-electric-escape t)
 '(TeX-engine 'xetex)
 '(TeX-expand-list
   '(("%p" TeX-printer-query)
     ("%q"
      (lambda nil
        (TeX-printer-query t)))
     ("%V"
      (lambda nil
        (TeX-source-correlate-start-server-maybe)
        (TeX-view-command-raw)))
     ("%vv"
      (lambda nil
        (TeX-source-correlate-start-server-maybe)
        (TeX-output-style-check TeX-output-view-style)))
     ("%v"
      (lambda nil
        (TeX-source-correlate-start-server-maybe)
        (TeX-style-check TeX-view-style)))
     ("%r"
      (lambda nil
        (TeX-style-check TeX-print-style)))
     ("%l"
      (lambda nil
        (TeX-style-check LaTeX-command-style)))
     ("%(PDF)"
      (lambda nil
        (if
            (and
             (eq TeX-engine 'default)
             (or TeX-PDF-mode TeX-DVI-via-PDFTeX))
            "pdf" "")))
     ("%(PDFout)"
      (lambda nil
        (cond
         ((and
           (eq TeX-engine 'xetex)
           (not TeX-PDF-mode))
          " -no-pdf")
         ((and
           (eq TeX-engine 'luatex)
           (not TeX-PDF-mode))
          " --output-format=dvi")
         ((and
           (eq TeX-engine 'default)
           (not TeX-PDF-mode)
           TeX-DVI-via-PDFTeX)
          " \"\\pdfoutput=0 \"")
         (t ""))))
     ("%(mode)"
      (lambda nil
        (if TeX-interactive-mode "" " -interaction=nonstopmode")))
     ("%(o?)"
      (lambda nil
        (if
            (eq TeX-engine 'omega)
            "o" "")))
     ("%(tex)"
      (lambda nil
        (eval
         (nth 2
              (assq TeX-engine
                    (TeX-engine-alist))))))
     ("%(latex)"
      (lambda nil
        (eval
         (nth 3
              (assq TeX-engine
                    (TeX-engine-alist))))))
     ("%(execopts)" ConTeXt-expand-options)
     ("%S" TeX-source-correlate-expand-options)
     ("%dS" TeX-source-specials-view-expand-options)
     ("%cS" TeX-source-specials-view-expand-client)
     ("%(outpage)"
      (lambda nil
        (if TeX-source-correlate-output-page-function
            (funcall TeX-source-correlate-output-page-function)
          "1")))
     ("%s" file nil t)
     ("%t" file t t)
     ("%`"
      (lambda nil
        (setq TeX-command-pos t TeX-command-text "")))
     (" \"\\"
      (lambda nil
        (if
            (eq TeX-command-pos t)
            (setq TeX-command-pos pos pos
                  (+ 3 pos))
          (setq pos
                (1+ pos)))))
     ("\""
      (lambda nil
        (if
            (numberp TeX-command-pos)
            (setq TeX-command-text
                  (concat TeX-command-text
                          (substring command TeX-command-pos
                                     (1+ pos)))
                  command
                  (concat
                   (substring command 0 TeX-command-pos)
                   (substring command
                              (1+ pos)))
                  pos TeX-command-pos TeX-command-pos t)
          (setq pos
                (1+ pos)))))
     ("%'"
      (lambda nil
        (prog1
            (if
                (stringp TeX-command-text)
                (progn
                  (setq pos
                        (+
                         (length TeX-command-text)
                         9)
                        TeX-command-pos
                        (and
                         (string-match " "
                                       (funcall file t t))
                         "\""))
                  (concat TeX-command-text " \"\\input\""))
              (setq TeX-command-pos nil)
              "")
          (setq TeX-command-text nil))))
     ("%n" TeX-current-line)
     ("%d" file "dvi" t)
     ("%f" file "ps" t)
     ("%o"
      (lambda nil
        (funcall file
                 (TeX-output-extension)
                 t)))
     ("%b" TeX-current-file-name-master-relative)
     ("%m" preview-create-subdirectory)
     ("%O"
      (lambda nil
        (expand-file-name
         (funcall file
                  (TeX-output-extension)
                  t))))))
 '(TeX-parse-self t)
 '(TeX-view-program-list
   '(("Skim"
      ("osascript" " ~/bin/skim-gotopage.script" " %O"
       (mode-io-correlate " %(outpage)")))))
 '(TeX-view-program-selection
   '(((output-dvi style-pstricks)
      "dvips and gv")
     (output-dvi "xdvi")
     (output-pdf "Skim")
     (output-html "xdg-open")))
 '(abbrev-file-name "~/.emacs.d/abbrevs.el")
 '(ac-auto-show-menu 1.0)
 '(ac-auto-start 3)
 '(ac-comphist-file "~/.emacs.d/data/ac-comphist.dat" t)
 '(ac-dwim nil)
 '(ac-ignore-case nil)
 '(ac-trigger-key "<tab>")
 '(ac-use-fuzzy nil)
 '(ace-isearch-function 'ace-jump-char-mode)
 '(ace-isearch-jump-delay 0.5)
 '(ace-isearch-submode 'ace-jump-char-mode)
 '(ace-isearch-use-jump nil)
 '(ad-redefinition-action 'accept)
 '(after-save-hook '(executable-make-buffer-file-executable-if-script-p))
 '(agda-input-tweak-all
   '(agda-input-compose
     (agda-input-prepend "\\")
     (agda-input-nonempty)))
 '(agda-input-user-translations
   '(("^" "^")
     ("nat" "⟹")
     ("next" "◯")
     ("always" "□")
     ("aly" "□")
     ("even" "◇")
     ("evn" "◇")
     ("for" "△")
     ("mer" "▽")
     ("iso" "≅")
     ("miso" "≃")
     ("diag" "∆")
     ("whl" "⊳")
     ("whr" "⊲")))
 '(agda2-backend "MAlonzo")
 '(agda2-include-dirs
   '("." "~/.nix-profile/share/agda-prelude" "~/.nix-profile/share/agda"))
 '(alert-default-style 'fringe)
 '(alert-notifier-command
   "~/Applications/terminal-notifier.app/Contents/MacOS/terminal-notifier")
 '(align-c++-modes '(csharp-mode c++-mode c-mode java-mode groovy-mode))
 '(align-to-tab-stop nil)
 '(allout-command-prefix ".")
 '(ansi-color-names-vector
   ["black" "red" "green" "brown" "blue" "magenta" "blue" "white"])
 '(appt-display-interval 30)
 '(appt-message-warning-time 60)
 '(auto-compression-mode t nil (jka-compr))
 '(auto-hscroll-mode 'current-line)
 '(auto-revert-use-notify nil)
 '(auto-save-file-name-transforms '(("\\`/[^/]*:.*" "/tmp" t)))
 '(auto-save-interval 64)
 '(auto-save-list-file-prefix "~/.emacs.d/data/auto-save-list/.saves-")
 '(auto-save-timeout 2)
 '(avy-case-fold-search t)
 '(avy-keys '(97 111 101 117 105 100 104 116 110 115))
 '(avy-timeout-seconds 0.3)
 '(aw-dispatch-when-more-than 6)
 '(aw-scope 'frame)
 '(backward-delete-char-untabify-method 'untabify)
 '(bbdb-default-country "")
 '(bbdb-file "~/doc/bbdb" t)
 '(bbdb-message-caching-enabled nil)
 '(bbdb-no-duplicates t)
 '(bbdb-offer-save 'savenoprompt)
 '(bbdb-silent-running t)
 '(bbdb-use-pop-up nil)
 '(bbdb-vcard-import-translation-table
   '(("CELL\\|CAR" . "Mobile")
     ("WORK" . "Work")
     ("HOME" . "Home")
     ("^$" . "Work")))
 '(bbdb/mail-auto-create-p nil)
 '(bc-bookmark-file "~/.emacs.d/data/breadcrumb" t)
 '(bind-key-segregation-regexp "\\`\\(\\(C-[chx.] \\|M-[gso] \\)\\([CM]-\\)?\\|.+-\\)")
 '(bm-buffer-persistence t)
 '(bm-cycle-all-buffers t)
 '(bm-highlight-style 'bm-highlight-only-fringe)
 '(bm-in-lifo-order t)
 '(bm-repository-file "/Users/johnw/.emacs.d/data/bm-repository")
 '(bmkp-bmenu-commands-file "~/.emacs.d/data/bmk-bmenu-commands.el")
 '(bmkp-bmenu-state-file "~/.emacs.d/data/bmk-bmenu-state.el")
 '(bmkp-crosshairs-flag nil)
 '(bmkp-last-as-first-bookmark-file "~/Documents/bookmarks")
 '(bookmark-default-file "~/doc/bookmarks")
 '(browse-url-browser-function 'browse-url-default-macosx-browser)
 '(byte-compile-verbose nil)
 '(c-default-style '((java-mode . "gnu") (awk-mode . "awk") (other . "gnu")))
 '(calendar-daylight-time-zone-name "PDT")
 '(calendar-latitude 38.5474883)
 '(calendar-longitude -121.5262693)
 '(calendar-mark-holidays-flag t)
 '(calendar-standard-time-zone-name "PST")
 '(calendar-time-zone -480)
 '(cargo-process--command-clippy "clippy")
 '(cc-other-file-alist
   '(("\\.hs\\'"
      (".hs-boot"))
     ("\\.cc\\'"
      (".hh" ".h"))
     ("\\.hh\\'"
      (".cc" ".C"))
     ("\\.c\\'"
      (".h"))
     ("\\.h\\'"
      (".c" ".cc" ".C" ".CC" ".cxx" ".cpp"))
     ("\\.C\\'"
      (".H" ".hh" ".h"))
     ("\\.H\\'"
      (".C" ".CC"))
     ("\\.CC\\'"
      (".HH" ".H" ".hh" ".h"))
     ("\\.HH\\'"
      (".CC"))
     ("\\.c\\+\\+\\'"
      (".h++" ".hh" ".h"))
     ("\\.h\\+\\+\\'"
      (".c++"))
     ("\\.cpp\\'"
      (".hpp" ".hh" ".h"))
     ("\\.hpp\\'"
      (".cpp"))
     ("\\.cxx\\'"
      (".hxx" ".hh" ".h"))
     ("\\.hxx\\'"
      (".cxx"))))
 '(clean-buffer-list-kill-never-buffer-names
   '("*scratch*" "*Messages*" "*server*" "*Group*" "*Org Agenda*" "todo.txt" "habits.txt" "Bahai.txt" "OSS.txt" "diary" "notes.txt" "&bitlbee"))
 '(clean-buffer-list-kill-never-regexps '("^ \\*Minibuf-.*\\*$" "^\\*Summary" "^\\*Article" "^#"))
 '(clean-buffer-list-kill-regexps '(".*"))
 '(column-number-mode t)
 '(company-coq-disabled-features
   '(hello prettify-symbols smart-subscripts dynamic-symbols-backend))
 '(company-coq-prettify-symbols-alist
   '(("|-" . 8866)
     ("True" . 8868)
     ("False" . 8869)
     ("->" . 8594)
     ("-->" . 10230)
     ("<-" . 8592)
     ("<--" . 10229)
     ("<->" . 8596)
     ("<-->" . 10231)
     ("==>" . 10233)
     ("<==" . 10232)
     ("++>" . 10239)
     ("<++" . 11059)
     ("fun" . 955)
     ("forall" . 8704)
     ("exists" . 8707)
     ("/\\" . 8743)
     ("\\/" . 8744)
     ("~" . 172)
     ("+-" . 177)
     ("<=" . 8804)
     (">=" . 8805)
     ("<>" . 8800)
     ("*" . 215)
     ("++" . 10746)
     ("nat" . 120029)
     ("Z" . 8484)
     ("N" . 8469)
     ("Q" . 8474)
     ("Real" . 8477)
     ("bool" . 120121)
     ("Prop" . 120031)))
 '(company-frontends
   '(company-pseudo-tooltip-unless-just-one-frontend company-echo-metadata-frontend company-preview-frontend))
 '(company-global-modes '(emacs-lisp-mode c-mode c++-mode))
 '(company-idle-delay nil)
 '(company-quickhelp-use-propertized-text t)
 '(company-show-numbers t)
 '(company-show-quick-access t)
 '(company-tooltip-align-annotations t)
 '(compilation-always-kill t)
 '(compilation-ask-about-save nil)
 '(compilation-context-lines 10)
 '(compilation-scroll-output 'first-error)
 '(compilation-search-path
   '(nil "~/src/gitlib" "~/src/gitlib/gitlib" "~/src/gitlib/gitlib-libgit2" "~/src/gitlib/gitlib-s3" "~/src/gitlib/gitlib-test" "~/src/gitlib/git-monitor" "~/src/c2hsc"))
 '(compilation-skip-threshold 2)
 '(compilation-window-height 100)
 '(completion-ignored-extensions
   '(".glob" ".vio" ".vo" ".vok" ".vos" ".v.d" ".o" "~" ".bin" ".lbin" ".so" ".a" ".ln" ".blg" ".bbl" ".elc" ".lof" ".glo" ".idx" ".lot" ".svn/" ".hg/" ".git/" ".bzr/" "CVS/" "_darcs/" "_MTN/" ".fmt" ".tfm" ".class" ".fas" ".lib" ".mem" ".x86f" ".sparcf" ".dfsl" ".pfsl" ".d64fsl" ".p64fsl" ".lx64fsl" ".lx32fsl" ".dx64fsl" ".dx32fsl" ".fx64fsl" ".fx32fsl" ".sx64fsl" ".sx32fsl" ".wx64fsl" ".wx32fsl" ".fasl" ".ufsl" ".fsl" ".dxl" ".lo" ".la" ".gmo" ".mo" ".toc" ".aux" ".cp" ".fn" ".ky" ".pg" ".tp" ".vr" ".cps" ".fns" ".kys" ".pgs" ".tps" ".vrs" ".pyc" ".pyo"))
 '(coq-compile-auto-save 'save-coq)
 '(coq-compile-before-require t)
 '(coq-compile-parallel-in-background t)
 '(coq-holes-minor-mode nil)
 '(coq-lookup-browse-pdf-function '(lambda (pdf page) (call-process "open" nil nil nil pdf)))
 '(coq-lookup-pdf "~/.local/share/coq/coq-8.15.2-reference-manual.pdf")
 '(coq-maths-menu-enable t)
 '(coq-one-command-per-line nil)
 '(coq-prefer-top-of-conclusion t)
 '(coq-prog-args '("-emacs"))
 '(counsel-describe-function-preselect 'ivy-function-called-at-point)
 '(counsel-find-file-ignore-regexp
   "\\(\\`\\.[^.]\\|\\(?:\\.\\(?:aux\\|b\\(?:bl\\|in\\|lg\\|zr/\\)\\|c\\(?:lass\\|ps?\\)\\|d\\(?:\\(?:64fs\\|fs\\|x\\(?:\\(?:32\\|64\\)fs\\)?\\)l\\)\\|elc\\|f\\(?:asl?\\|mt\\|ns?\\|\\(?:x\\(?:\\(?:32\\|64\\)f\\)\\)?sl\\)\\|g\\(?:it/\\|lob?\\|mo\\)\\|hg/\\|idx\\|kys?\\|l\\(?:bin\\|ib\\|o[ft]\\|x\\(?:\\(?:32\\|64\\)fsl\\)\\|[ano]\\)\\|m\\(?:em\\|o\\)\\|p\\(?:64fsl\\|fsl\\|gs?\\|y[co]\\)\\|s\\(?:o\\|parcf\\|vn/\\|x\\(?:\\(?:32\\|64\\)fsl\\)\\)\\|t\\(?:fm\\|oc\\|ps?\\)\\|ufsl\\|v\\(?:\\.d\\|rs\\|[or]\\|o[ks]\\)\\|wx\\(?:\\(?:32\\|64\\)fsl\\)\\|x86f\\|[ao]\\)\\|CVS/\\|_\\(?:\\(?:MTN\\|darcs\\)/\\)\\|~\\)\\'\\)" nil nil "Customized with use-package counsel")
 '(counsel-locate-cmd 'counsel-locate-cmd-default)
 '(counsel-projectile-remove-current-buffer t)
 '(counsel-projectile-remove-current-project t)
 '(current-language-environment "UTF-8")
 '(custom-buffer-done-function 'kill-buffer)
 '(custom-file "~/.emacs.d/settings.el")
 '(custom-raised-buttons nil)
 '(custom-safe-themes
   '("644e23f289dcd3548c3f054785c72cf1fd81fcee07875ac7fed311985a67a0dc" "c74e83f8aa4c78a121b52146eadb792c9facc5b1f02c917e3dbb454fca931223" "3c83b3676d796422704082049fc38b6966bcad960f896669dfc21a7a37a748fa" "b9e9ba5aeedcc5ba8be99f1cc9301f6679912910ff92fdf7980929c2fc83ab4d" "84d2f9eeb3f82d619ca4bfffe5f157282f4779732f48a5ac1484d94d5ff5b279" "a27c00821ccfd5a78b01e4f35dc056706dd9ede09a8b90c6955ae6a390eb1c1e" default))
 '(dabbrev-case-fold-search nil)
 '(dabbrev-case-replace nil)
 '(dafny-prover-args '("/compile:0" "/vcsCores:4"))
 '(dafny-prover-background-args
   '("/timeLimit:20" "/autoTriggers:1" "/printTooltips" "/vcsCores:4"))
 '(default-input-method "Agda")
 '(default-major-mode 'text-mode t)
 '(delete-old-versions t)
 '(diary-file "~/doc/diary")
 '(diff-mode-hook '(diff-delete-empty-files diff-make-unified smerge-mode))
 '(directory-abbrev-alist
   '(("\\`/tasks" . "/Users/johnw/doc/org")
     ("\\`/reader" . "/Users/johnw/Library/Mobile Documents/JFJWWP64QD~com~goodiware~GoodReader/Documents")))
 '(directory-free-space-args "-kh")
 '(dired-clean-up-buffers-too nil)
 '(dired-dwim-target t)
 '(dired-hide-details-hide-information-lines nil)
 '(dired-hide-details-hide-symlink-targets nil)
 '(dired-listing-switches "--group-directories-first -lah")
 '(dired-no-confirm
   '(byte-compile chgrp chmod chown copy hardlink symlink touch))
 '(dired-omit-mode nil t)
 '(dired-omit-size-limit 60000)
 '(dired-recursive-copies 'always)
 '(dired-recursive-deletes 'always)
 '(diredful-init-file "~/.emacs.d/data/diredful-conf.el" t)
 '(display-time-interval 60)
 '(display-time-mode t)
 '(display-time-use-mail-icon t)
 '(doc-view-resolution 300)
 '(docker-containers-shell-file-name "/bin/bash")
 '(docker-containers-show-all nil)
 '(dropbox-token-file "~/.config/dropbox/token")
 '(ebib-autogenerate-keys t)
 '(ediff-combination-pattern
   '("<<<<<<< A: HEAD" A "||||||| Ancestor" Ancestor "=======" B ">>>>>>> B: Incoming"))
 '(ediff-diff-options "-w")
 '(ediff-highlight-all-diffs nil)
 '(ediff-show-clashes-only t)
 '(ediff-window-setup-function 'ediff-setup-windows-plain)
 '(edit-server-new-frame nil)
 '(eglot-autoshutdown t)
 '(el-get-auto-update-cached-recipes nil)
 '(el-get-dir "~/.emacs.d/site-lisp/")
 '(el-get-generate-autoloads nil)
 '(eldoc-echo-area-use-multiline-p 3)
 '(electric-indent-mode nil)
 '(emms-player-vlc-command-name "/Applications/Misc/VLC.app/Contents/MacOS/VLC")
 '(enable-recursive-minibuffers t)
 '(erc-auto-query 'window-noselect)
 '(erc-autoaway-message "I'm away (after %i seconds of idle-time)")
 '(erc-autojoin-channels-alist
   '(("0.1" "#nixos" "#nix-darwin" "#hnix" "#haskell-overflow" "#haskell-ops" "#haskell-infrastructure" "#haskell" "#coq-blah" "#coq" "##categorytheory" "#use-package/Lobby" "#ledger" "#haskell-nix/Lobby" "#coq/coq" "#hs-to-coq" "#org-mode")
     ("libera" "#haskell" "#coq" "#ledger" "#haskell-ops" "#nix-darwin" "#haskell-infrastructure" "##categorytheory" "#nixos" "#org-mode")
     ("gitter" "#use-package/Lobby" "#haskell-nix/Lobby")))
 '(erc-button-alist
   '(("https://gist\\.github\\.com/\\(.*\\)" 0 t gist-fetch 1)
     ('nicknames 0 erc-button-buttonize-nicks erc-nick-popup 0)
     (erc-button-url-regexp 0 t browse-url 0)
     ("<URL: *\\([^<> ]+\\) *>" 0 t browse-url 1)
     ("[`]\\([a-zA-Z][-a-zA-Z_0-9]+\\)[']" 1 t erc-button-describe-symbol 1)
     ("\\bInfo:[\"]\\([^\"]+\\)[\"]" 0 t Info-goto-node 1)
     ("\\b\\(Ward\\|Wiki\\|WardsWiki\\|TheWiki\\):\\([A-Z][a-z]+\\([A-Z][a-z]+\\)+\\)" 0 t
      (lambda
        (page)
        (browse-url
         (concat "http://c2.com/cgi-bin/wiki?" page)))
      2)
     ("EmacsWiki:\\([A-Z][a-z]+\\([A-Z][a-z]+\\)+\\)" 0 t erc-browse-emacswiki 1)
     ("Lisp:\\([a-zA-Z.+-]+\\)" 0 t erc-browse-emacswiki-lisp 1)
     ("\\bGoogle:\\([^
]+\\)" 0 t
(lambda
  (keywords)
  (browse-url
   (format erc-button-google-url keywords)))
1)
     ("\\brfc[#: ]?\\([0-9]+\\)" 0 t
      (lambda
        (num)
        (browse-url
         (format erc-button-rfc-url num)))
      1)
     ("\\s-\\(@\\([0-9][0-9][0-9]\\)\\)" 1 t erc-button-beats-to-time 2)))
 '(erc-fill-function 'erc-fill-variable)
 '(erc-fill-static-center 12)
 '(erc-foolish-content
   '("MichaelSnoyman" "BrendanHay" "MichaelSloan" "ChrisDone" "travis-ci.*ekmett" "analystics.*ekmett" "rudybot:" "Ostergaard"))
 '(erc-format-nick-function 'erc-format-@nick)
 '(erc-generate-log-file-name-function 'erc-generate-log-file-name-short)
 '(erc-header-line-format nil)
 '(erc-hide-list '("JOIN" "NICK" "PART" "QUIT"))
 '(erc-ignore-list '("lensbot" "rudybot" "johnwilkins"))
 '(erc-ignore-reply-list '("JordiGH"))
 '(erc-keywords '("wiegley" "ledger" "eshell" "use-package"))
 '(erc-log-channels-directory "~/Messages/ERC")
 '(erc-log-write-after-send t)
 '(erc-lurker-hide-list '("JOIN" "NICK" "PART" "QUIT" "MODE"))
 '(erc-modules
   '(autojoin button completion dcc fill identd irccontrols list match menu move-to-prompt netsplit networks noncommands readonly replace ring services smiley stamp track truncate highlight-nicknames))
 '(erc-nick "johnw")
 '(erc-port 6667)
 '(erc-priority-people-regexp "\\`[^#].+")
 '(erc-prompt-for-nickserv-password nil)
 '(erc-rename-buffers t)
 '(erc-replace-alist '(("</?FONT>" . "")))
 '(erc-server "irc.libera.chat")
 '(erc-services-mode t)
 '(erc-text-matched-hook '(erc-hide-fools))
 '(erc-track-enable-keybindings t)
 '(erc-track-exclude '("#idris" "#agda" "#twitter_jwiegley"))
 '(erc-track-exclude-types '("JOIN" "KICK" "NICK" "PART" "QUIT" "MODE" "333" "353"))
 '(erc-track-faces-priority-list
   '(erc-error-face
     (erc-nick-default-face erc-current-nick-face)
     erc-current-nick-face erc-keyword-face
     (erc-nick-default-face erc-pal-face)
     erc-pal-face erc-nick-msg-face erc-direct-msg-face))
 '(erc-track-score-mode t)
 '(erc-track-showcount t)
 '(erc-user-full-name 'user-full-name)
 '(erc-yank-query-before-gisting nil)
 '(eshell-directory-change-hook
   '(sml/generate-buffer-identification direnv-update-environment) t)
 '(eshell-directory-name "~/.emacs.d/eshell/")
 '(eshell-hist-ignoredups t)
 '(eshell-history-size 50000)
 '(eshell-ls-dired-initial-args '("-h"))
 '(eshell-ls-exclude-regexp "~\\'")
 '(eshell-ls-initial-args "-h")
 '(eshell-modules-list
   '(eshell-alias eshell-basic eshell-cmpl eshell-dirs eshell-glob eshell-hist eshell-ls eshell-pred eshell-prompt eshell-rebind eshell-script eshell-smart eshell-term eshell-unix eshell-xtra))
 '(eshell-prompt-function
   (lambda nil
     (concat
      (abbreviate-file-name
       (eshell/pwd))
      (if
          (=
           (user-uid)
           0)
          " # " " $ "))))
 '(eshell-rebind-keys-alist
   '(([(control 97)]
      . eshell-bol)
     ([home]
      . eshell-bol)
     ([(control 100)]
      . eshell-delchar-or-maybe-eof)
     ([backspace]
      . eshell-delete-backward-char)
     ([delete]
      . eshell-delete-backward-char)))
 '(eshell-save-history-on-exit t)
 '(eshell-stringify-t nil)
 '(eshell-term-name "ansi")
 '(eshell-visual-commands '("vi" "top" "screen" "less" "lynx" "rlogin" "telnet"))
 '(eudc-inline-expansion-format '("%s <%s>" name email))
 '(eval-expr-print-function 'pp)
 '(eval-expr-print-length 100)
 '(eval-expr-print-level 20)
 '(eww-lnum-actions-link-alist
   '("----  Link   ----"
     (102 eww-lnum-visit "Visit")
     (101
      (lambda
        (info)
        (eww-lnum-visit info nil t))
      "Edit URL and visit")
     (70
      (lambda
        (info)
        (eww-lnum-visit info t))
      "Visit in new buffer")
     (69
      (lambda
        (info)
        (eww-lnum-visit info t t))
      "Edit URL and visit in new buffer")
     (98
      (lambda
        (info)
        (eww-lnum-visit info :background))
      "Open in background")
     (66
      (lambda
        (info)
        (eww-lnum-visit info :background t))
      "Edit URL and open in background")
     (100
      (lambda
        (info)
        (save-excursion
          (goto-char
           (cadr info))
          (eww-download)))
      "Download")
     (119
      (lambda
        (info)
        (let
            ((url
              (car info)))
          (kill-new url)
          (message url)))
      "Copy")
     (38
      (lambda
        (info)
        (eww-browse-with-external-browser
         (car info)))
      "Open in external browser")
     (68
      (lambda
        (info)
        (shell-command
         (concat "aria2c -d ~/Downloads -x5 '"
                 (car info)
                 "' &")
         "*Aria*"))
      "Download with Aria")))
 '(eww-search-prefix "https://startpage.com/do/m/mobilesearch?query=")
 '(explicit-shell-file-name "~/.emacs.d/runshell")
 '(eyebrowse-keymap-prefix "")
 '(eyebrowse-mode-line-separator " ")
 '(eyebrowse-new-workspace t)
 '(fill-column 78)
 '(find-ls-option '("-print0 | xargs -P4 -0 ls -ldN" . "-ldN"))
 '(find-ls-subdir-switches "-ldN")
 '(flx-ido-use-faces nil)
 '(flycheck-coq-executable "ct-coqtop")
 '(flycheck-display-errors-delay 0.0)
 '(flycheck-haskell-hpack-preference 'prefer-cabal)
 '(flycheck-standard-error-navigation nil)
 '(flymake-proc-compilation-prevents-syntax-check nil)
 '(flyspell-abbrev-p nil)
 '(flyspell-use-meta-tab nil)
 '(font-lock-support-mode 'jit-lock-mode)
 '(font-lock-verbose nil)
 '(forge-alist
   '(("github.com" "api.github.com" "github.com" forge-github-repository)
     ("gitlab.com" "gitlab.com/api/v4" "gitlab.com" forge-gitlab-repository)
     ("salsa.debian.org" "salsa.debian.org/api/v4" "salsa.debian.org" forge-gitlab-repository)
     ("framagit.org" "framagit.org/api/v4" "framagit.org" forge-gitlab-repository)
     ("gitlab.gnome.org" "gitlab.gnome.org/api/v4" "gitlab.gnome.org" forge-gitlab-repository)
     ("codeberg.org" "codeberg.org/api/v1" "codeberg.org" forge-gitea-repository)
     ("code.orgmode.org" "code.orgmode.org/api/v1" "code.orgmode.org" forge-gogs-repository)
     ("bitbucket.org" "api.bitbucket.org/2.0" "bitbucket.org" forge-bitbucket-repository)
     ("git.savannah.gnu.org" nil "git.savannah.gnu.org" forge-cgit**-repository)
     ("git.kernel.org" nil "git.kernel.org" forge-cgit-repository)
     ("repo.or.cz" nil "repo.or.cz" forge-repoorcz-repository)
     ("git.suckless.org" nil "git.suckless.org" forge-stagit-repository)
     ("git.sr.ht" nil "git.sr.ht" forge-srht-repository)))
 '(forge-database-file "~/.config/forge/database.sqlite")
 '(forge-owned-accounts '(("jwiegley")))
 '(frame-title-format
   '(:eval
     (concat
      (if buffer-file-name default-directory "%b")
      "    "
      (number-to-string
       (cdr
        (assq 'width
              (frame-parameters))))
      "x"
      (number-to-string
       (cdr
        (assq 'height
              (frame-parameters)))))) t)
 '(gdb-find-source-frame t)
 '(gdb-same-frame nil)
 '(ggtags-enable-navigation-keys nil)
 '(ggtags-oversize-limit 1048576)
 '(ggtags-use-sqlite3 t)
 '(git-commit-mode-hook '(turn-on-auto-fill flyspell-mode git-commit-save-message) t)
 '(github-review-fetch-top-level-and-review-comments t)
 '(glasses-separator "-")
 '(glasses-uncapitalize-p t)
 '(global-auto-complete-mode t)
 '(global-auto-revert-mode t)
 '(global-font-lock-mode t nil (font-lock))
 '(grep-command "egrep -nH -e ")
 '(grep-find-command
   "find . -name '*' -type f -print0 | xargs -0 -P8 egrep -nH ")
 '(grep-save-buffers t)
 '(guide-key/guide-key-sequence t)
 '(guide-key/idle-delay 1.5)
 '(guide-key/popup-window-position 'bottom)
 '(haskell-compile-cabal-build-command "cd %s && cabal new-build --ghc-option=-ferror-spans")
 '(haskell-hasktags-arguments '("-e"))
 '(haskell-hoogle-command nil)
 '(haskell-indent-spaces 4)
 '(haskell-indentation-ifte-offset 4)
 '(haskell-indentation-layout-offset 4)
 '(haskell-indentation-left-offset 2)
 '(haskell-indentation-starter-offset 4)
 '(haskell-indentation-where-post-offset 4)
 '(haskell-indentation-where-pre-offset 4)
 '(haskell-process-args-cabal-repl
   '("--ghc-option=-ferror-spans" "--repl-options=-Wno-missing-home-modules" "--repl-options=-ferror-spans"))
 '(haskell-process-load-or-reload-prompt t)
 '(haskell-tags-on-save t)
 '(helm-command-prefix-key nil)
 '(helm-dash-browser-func 'eww)
 '(helm-dash-docsets-path "/Users/johnw/Library/Application Support/Dash/DocSets/")
 '(helm-firefox-default-directory "~/Library/Application Support/Firefox/")
 '(helm-minibuffer-history-key nil)
 '(helm-recoll-options '("recollq" "-t" "-b"))
 '(hi2-ifte-offset 4)
 '(hi2-layout-offset 4)
 '(hi2-left-offset 4)
 '(hi2-show-indentations nil)
 '(hibtypes-github-default-user "jwiegley")
 '(hippie-expand-try-functions-list
   '(try-expand-dabbrev try-expand-dabbrev-all-buffers try-expand-dabbrev-from-kill try-complete-file-name-partially try-complete-file-name try-expand-all-abbrevs try-expand-list try-expand-line try-complete-lisp-symbol-partially try-complete-lisp-symbol))
 '(history-delete-duplicates t)
 '(history-length 200)
 '(hkey-init nil)
 '(holiday-bahai-holidays nil)
 '(hoogle-binary-path "hoogle")
 '(hpaste-announce 'always)
 '(hpaste-blank-title nil)
 '(hpaste-channel "#haskell")
 '(hpaste-default-lang "haskell")
 '(hpaste-default-nick "johnw")
 '(hpaste-lang 'always)
 '(ibuffer-default-display-maybe-show-predicates t)
 '(ibuffer-expert t)
 '(ibuffer-formats
   '((mark modified read-only " "
           (name 16 -1)
           " "
           (size 6 -1 :right)
           " "
           (mode 16 16)
           " " filename)
     (mark " "
           (name 16 -1)
           " " filename)))
 '(ibuffer-maybe-show-regexps nil)
 '(ibuffer-saved-filter-groups
   '(("default"
      ("Magit"
       (or
        (mode . magit-status-mode)
        (mode . magit-log-mode)
        (name . "\\*magit")
        (name . "magit-")
        (name . "git-monitor")))
      ("Coq"
       (or
        (mode . coq-mode)
        (name . "\\<coq\\>")
        (name . "_CoqProject")))
      ("Commands"
       (or
        (mode . shell-mode)
        (mode . eshell-mode)
        (mode . term-mode)
        (mode . compilation-mode)))
      ("Haskell"
       (or
        (mode . haskell-mode)
        (mode . haskell-cabal-mode)
        (mode . literate-haskell-mode)))
      ("Rust"
       (or
        (mode . rust-mode)
        (mode . cargo-mode)
        (name . "\\*Cargo")
        (name . "^\\*rls\\(::stderr\\)?\\*")
        (name . "eglot")))
      ("Nix"
       (mode . nix-mode))
      ("C++"
       (or
        (mode . c-mode)
        (mode . c++-mode)))
      ("Lisp"
       (mode . emacs-lisp-mode))
      ("Dired"
       (mode . dired-mode))
      ("Gnus"
       (or
        (mode . message-mode)
        (mode . mail-mode)
        (mode . gnus-group-mode)
        (mode . gnus-summary-mode)
        (mode . gnus-article-mode)
        (name . "^\\.newsrc-dribble")
        (name . "^\\*\\(sent\\|unsent\\|fetch\\)")
        (name . "^ \\*\\(nnimap\\|nntp\\|nnmail\\|gnus\\|server\\|mm\\*\\)")
        (name . "\\(Original Article\\|canonical address\\|extract address\\)")))
      ("Org"
       (or
        (name . "^\\*Calendar\\*$")
        (name . "^\\*Org Agenda")
        (name . "^ \\*Agenda")
        (name . "^diary$")
        (mode . org-mode)))
      ("Emacs"
       (or
        (name . "^\\*scratch\\*$")
        (name . "^\\*Messages\\*$")
        (name . "^\\*\\(Customize\\|Help\\)")
        (name . "\\*\\(Echo\\|Minibuf\\)"))))))
 '(ibuffer-show-empty-filter-groups nil)
 '(ibuffer-shrink-to-minimum-size t t)
 '(ibuffer-use-other-window t)
 '(icicle-Completions-text-scale-decrease 0)
 '(icicle-apropos-cycle-next-keys '([next] [(control 110)]))
 '(icicle-apropos-cycle-previous-keys '([prior] [(control 112)]))
 '(icicle-incremental-completion nil)
 '(icicle-max-candidates 100)
 '(ido-auto-merge-work-directories-length 0)
 '(ido-cannot-complete-command 'ido-exit-minibuffer)
 '(ido-decorations
   '("{" "}" "," ",..." "[" "]" " [No match]" " [Matched]" " [Not readable]" " [Too big]" " [Confirm]"))
 '(ido-enable-flex-matching t)
 '(ido-enable-last-directory-history nil)
 '(ido-enable-tramp-completion nil)
 '(ido-enter-matching-directory 'first)
 '(ido-ignore-files
   '("\\`CVS/" "\\`#" "\\`.#" "\\`\\.\\./" "\\`\\./" "\\`\\.DS_Store" "\\`\\.localized" "\\.sparsebundle/" "\\.dmg\\'"))
 '(ido-save-directory-list-file "~/.emacs.d/data/ido.last")
 '(ido-use-virtual-buffers t)
 '(ido-use-virtual-buffers-automatically t)
 '(idris-interpreter-flags '("-p" "effects"))
 '(image-dired-dir "~/.emacs.d/data/image-dired/")
 '(imagemagick-render-type 1)
 '(indent-tabs-mode nil)
 '(inhibit-startup-echo-area-message "johnw")
 '(inhibit-startup-screen t)
 '(initial-buffer-choice t)
 '(initial-major-mode 'fundamental-mode)
 '(initial-scratch-message "")
 '(initsplit-customizations-alist
   '(("\\`\\(gnus\\|nn\\|message\\|mail\\|mm-\\|smtp\\|send-mail\\|check-mail\\|spam\\|sc-\\)" "~/.emacs.d/gnus-settings.el" nil nil)
     ("\\`\\(jobhours-\\|org-\\|deft-\\|cfw:\\)" "~/.emacs.d/org-settings.el" nil nil)))
 '(ipa-file "~/doc/ipa")
 '(ipa-overlay-position "above")
 '(irfc-directory "~/Archives/Admin/RFC/")
 '(ispell-extra-args '("--sug-mode=fast" "--keyboard=dvorak"))
 '(ivy-dynamic-exhibit-delay-ms 200 nil nil "Customized with use-package ivy")
 '(ivy-extra-directories '("./"))
 '(ivy-height 10 nil nil "Customized with use-package ivy")
 '(ivy-ignore-buffers
   '("\\` " "\\`\\*git-monitor:" "\\`\\*magit-process:" "\\.elc$" "\\.CFUserTextEncoding" "\\`\\*Quail Completions\\*\\'" "\\`\\.newsrc-dribble\\'" "\\`\\.newsrc.eld\\'"))
 '(ivy-initial-inputs-alist nil nil nil "Customized with use-package ivy")
 '(ivy-magic-tilde nil nil nil "Customized with use-package ivy")
 '(ivy-re-builders-alist '((t . ivy--regex-ignore-order)) t nil "Customized with use-package ivy")
 '(ivy-rich-parse-remote-buffer nil)
 '(ivy-use-virtual-buffers t nil nil "Customized with use-package ivy")
 '(ivy-wrap t nil nil "Customized with use-package ivy")
 '(jist-enable-default-authorized t)
 '(jist-gist-directory "/Users/johnw/src/notes/gists")
 '(kill-do-not-save-duplicates t)
 '(kill-ring-max 500)
 '(kill-whole-line t)
 '(langtool-language-tool-jar "~/.nix-profile/share/languagetool-commandline.jar")
 '(large-file-warning-threshold nil)
 '(ledger-binary-path "ledger")
 '(ledger-file "/Volumes/Files/Accounts/ledger.dat")
 '(ledger-post-use-ido t)
 '(line-number-mode t)
 '(load-prefer-newer t)
 '(lsp-rust-features ["test"])
 '(mac-pass-command-to-system nil)
 '(mac-pass-control-to-system nil)
 '(mac-wheel-button-is-mouse-2 nil)
 '(magit-auto-revert-mode nil)
 '(magit-completing-read-function 'my-ivy-completing-read)
 '(magit-diff-options nil)
 '(magit-diff-refine-hunk t)
 '(magit-fetch-arguments nil)
 '(magit-git-executable "~/.nix-profile/bin/git")
 '(magit-highlight-trailing-whitespace nil)
 '(magit-highlight-whitespace nil)
 '(magit-log-section-commit-count 10)
 '(magit-pre-refresh-hook nil)
 '(magit-process-popup-time 15)
 '(magit-push-always-verify nil)
 '(magit-refresh-status-buffer nil)
 '(magit-section-initial-visibility-alist '((untracked . hide)))
 '(magit-stage-all-confirm nil)
 '(magit-unstage-all-confirm nil)
 '(magit-use-overlays nil)
 '(magithub-clone-default-directory "~/src")
 '(magithub-dir "/Users/johnw/.emacs.d/data/magithub")
 '(make-backup-file-name-function 'my-make-backup-file-name)
 '(malyon-stories-directory "~/doc/games")
 '(markdown-command "pandoc -f markdown_github+smart")
 '(markdown-command-needs-filename t)
 '(markdown-enable-math t)
 '(markdown-open-command "marked")
 '(math-additional-units
   '((GiB "1024 * MiB" "Giga Byte")
     (MiB "1024 * KiB" "Mega Byte")
     (KiB "1024 * B" "Kilo Byte")
     (B nil "Byte")
     (Gib "1024 * Mib" "Giga Bit")
     (Mib "1024 * Kib" "Mega Bit")
     (Kib "1024 * b" "Kilo Bit")
     (b "B / 8" "Bit")) t nil "Customized with use-package calc")
 '(mc/list-file "~/.emacs.d/data/mc-lists.el")
 '(mediawiki-site-alist
   '(("Wikipedia" "https://en.wikipedia.org/w/" "jwiegley" "" nil "Main Page")))
 '(menu-bar-mode nil)
 '(midnight-delay 18000)
 '(midnight-mode t)
 '(moccur-following-mode-toggle nil)
 '(modelinepos-column-limit 80)
 '(mudel-mode-hook '(mudel-add-scroll-to-bottom))
 '(mudel-output-filter-functions '(ansi-color-process-output))
 '(multi-term-program "screen")
 '(multi-term-program-switches "-DR")
 '(multi-term-scroll-show-maximum-output t)
 '(my-gnus-thread-sort-functions
   '(gnus-thread-sort-by-most-recent-date gnus-thread-sort-by-total-score))
 '(next-line-add-newlines nil)
 '(nix-buffer-directory-name "~/.emacs.d/data/nix-buffer" t)
 '(nix-indent-function 'nix-indent-line)
 '(nov-save-place-file "~/.emacs.d/data/nov-places")
 '(ns-alternate-modifier 'alt)
 '(ns-command-modifier 'meta)
 '(ns-function-modifier 'hyper)
 '(ns-right-alternate-modifier 'alt)
 '(nsm-settings-file "/Users/johnw/.emacs.d/data/network-security.data")
 '(nxml-sexp-element-flag t)
 '(nxml-slash-auto-complete-flag t)
 '(olivetti-hide-mode-line t)
 '(ovpn-mode-base-directory "~/.config/openvpn")
 '(pabbrev-idle-timer-verbose nil)
 '(package-archives
   '(("gnu" . "https://elpa.gnu.org/packages/")
     ("MELPA" . "https://melpa.org/packages/")
     ("Marmalade" . "https://marmalade-repo.org/packages/")))
 '(page-break-lines-modes
   '(emacs-lisp-mode compilation-mode outline-mode prog-mode haskell-mode))
 '(parens-require-spaces t)
 '(password-store-password-length 24)
 '(pcomplete-compare-entries-function 'file-newer-than-file-p)
 '(pdf-tools-handle-upgrades nil)
 '(persistent-scratch-autosave-interval 30)
 '(persistent-scratch-backup-directory "~/.cache/emacs/backups")
 '(persistent-scratch-file-name "~/.emacs.d/data/persistent-scratch" t)
 '(persistent-scratch-save-file "/Users/johnw/.emacs.d/data/persistent-scratch")
 '(phi-search-limit 100000)
 '(plantuml-default-exec-mode 'executable)
 '(plantuml-jar-path "~/.nix-profile/lib/plantuml.jar")
 '(powerline-default-separator 'arrow)
 '(powerline-image-apple-rgb t)
 '(pp^L-^L-string "                                            ")
 '(prettify-symbols-unprettify-at-point 'right-edge)
 '(projectile-cache-file "~/.emacs.d/data/projectile.cache")
 '(projectile-completion-system 'ivy)
 '(projectile-enable-caching t)
 '(projectile-file-exists-local-cache-expire 300)
 '(projectile-globally-ignored-directories
   '(".idea" ".ensime_cache" ".eunit" ".git" ".hg" ".fslckout" "_FOSSIL_" ".bzr" "_darcs" ".tox" ".svn" ".stack-work" "dist" "\\`/nix/.+" ".*/\\..*"))
 '(projectile-globally-ignored-files '("TAGS" "GPATH" "GRTAGS" "GTAGS" "ID"))
 '(projectile-ignored-project-function
   (lambda
     (path)
     (string-match "\\(:?\\`/\\(:?nix\\|tmp\\)\\|/\\.nix-profile\\)" path)))
 '(projectile-keymap-prefix "p")
 '(projectile-known-projects-file "~/.emacs.d/data/projectile-bookmarks.eld")
 '(projectile-other-file-alist
   '(("cpp" "h" "hpp" "ipp")
     ("ipp" "h" "hpp" "cpp")
     ("hpp" "h" "ipp" "cpp" "cc")
     ("cxx" "h" "hxx" "ixx")
     ("ixx" "h" "hxx" "cxx")
     ("hxx" "h" "ixx" "cxx")
     ("c" "h")
     ("m" "h")
     ("mm" "h")
     ("h" "c" "cc" "cpp" "ipp" "hpp" "cxx" "ixx" "hxx" "m" "mm")
     ("cc" "h" "hh" "hpp")
     ("hh" "cc")
     ("vert" "frag")
     ("frag" "vert")
     (nil "lock" "gpg")
     ("lock" "")
     ("gpg" "")
     ("mli" "ml")
     ("ml" "mli")
     ("hs-boot" "hs")
     ("hs" "hs-boot")
     ("nix" "exp")
     ("exp" "nix")))
 '(projectile-project-search-path '("~/src"))
 '(projectile-sort-order 'recentf)
 '(proof-auto-action-when-deactivating-scripting 'retract)
 '(proof-autosend-enable nil)
 '(proof-electric-terminator-enable t)
 '(proof-fast-process-buffer nil)
 '(proof-script-fly-past-comments t)
 '(proof-shell-fiddle-frames nil)
 '(proof-splash-enable nil)
 '(proof-sticky-errors t)
 '(proof-tidy-response t)
 '(ps-font-size '(8 . 10))
 '(ps-footer-font-size '(12 . 14))
 '(ps-header-font-size '(12 . 14))
 '(ps-header-title-font-size '(14 . 16))
 '(ps-line-number-font-size 10)
 '(ps-print-color-p nil)
 '(purpose-preferred-prompt 'vanilla)
 '(racer-cmd "racer")
 '(rdebug-many-windows nil)
 '(read-buffer-function 'ido-read-buffer)
 '(recentf-auto-cleanup 60)
 '(recentf-exclude
   '("~\\'" "\\`out\\'" "\\.log\\'" "^/[^/]*:" "\\.el\\.gz\\'"))
 '(recentf-max-saved-items 2000)
 '(recentf-save-file "~/.emacs.d/data/recentf")
 '(redisplay-dont-pause t t)
 '(reftex-plug-into-AUCTeX t)
 '(reftex-trust-label-prefix t)
 '(regex-tool-backend 'perl)
 '(rng-schema-locating-files
   '("schemas.xml" "~/src/schemas.xml" "~/.nix-profile/share/emacs/24.4/etc/schema/schemas.xml"))
 '(rtags-autostart-diagnostics t)
 '(rtags-completions-enabled t)
 '(rtags-display-result-backend 'ivy)
 '(runner-init-file "~/.emacs.d/data/runner-conf.el" t)
 '(rust-format-on-save t)
 '(rustic-format-trigger 'on-save)
 '(rustic-rustfmt-args "--edition 2021")
 '(safe-local-eval-forms
   '((add-hook 'write-file-hooks 'time-stamp)
     (add-hook 'write-file-functions 'time-stamp)
     (add-hook 'before-save-hook 'time-stamp nil t)
     (add-hook 'before-save-hook 'delete-trailing-whitespace nil t)
     (progn
       (let
           ((coq-root-directory
             (when buffer-file-name
               (locate-dominating-file buffer-file-name ".dir-locals.el")))
            (coq-project-find-file
             (and
              (boundp 'coq-project-find-file)
              coq-project-find-file)))
         (set
          (make-local-variable 'tags-file-name)
          (concat coq-root-directory "TAGS"))
         (setq camldebug-command-name
               (concat coq-root-directory "dev/ocamldebug-coq"))
         (unless coq-project-find-file
           (set
            (make-local-variable 'compile-command)
            (concat "make -C " coq-root-directory))
           (set
            (make-local-variable 'compilation-search-path)
            (cons coq-root-directory nil)))
         (when coq-project-find-file
           (setq default-directory coq-root-directory))))))
 '(safe-local-variable-values
   '((haskell-indent-spaces . 4)
     (haskell-indent-spaces . 2)
     (haskell-indentation-ifte-offset . 2)
     (haskell-indentation-layout-offset . 2)
     (haskell-indentation-left-offset . 2)
     (haskell-indentation-starter-offset . 2)
     (haskell-indentation-where-post-offset . 2)
     (haskell-indentation-where-pre-offset . 2)
     (after-save-hook check-parens quietly-read-abbrev-file)))
 '(sage-view-anti-aliasing-level 4)
 '(sage-view-margin '(20 . 20))
 '(sage-view-scale 2.0)
 '(same-window-buffer-names
   '("*eshell*" "*shell*" "*mail*" "*inferior-lisp*" "*ielm*" "*scheme*"))
 '(save-abbrevs 'silently)
 '(save-interprogram-paste-before-kill t)
 '(save-kill-file-name "~/.emacs.d/data/kill-ring-saved.el" t)
 '(save-place-file "~/.emacs.d/data/places")
 '(savehist-additional-variables
   '(tablist-named-filter file-name-history sr-history-registry kmacro-ring compile-history compile-command))
 '(savehist-autosave-interval 60)
 '(savehist-file "~/.emacs.d/data/history")
 '(savehist-ignored-variables '(load-history flyspell-auto-correct-ring kill-ring))
 '(savehist-mode t)
 '(scroll-bar-mode nil)
 '(semanticdb-default-save-directory "~/.emacs.d/data/semanticdb")
 '(sendmail-program "msmtp")
 '(sentence-end-double-space nil)
 '(shackle-default-rule '(:select t))
 '(shackle-rules
   '((compilation-mode :select nil :size 0.6)
     ("\\`\\*Messages" :select t :align t :size 0.6)
     ("\\` \\*Lusty-Matches\\*" :regexp t :noselect t)
     ("\\`\\*fetch" :regexp t :size 0.25 :noselect t :align bottom)
     ("\\`\\*Flycheck" :regexp t :size 0.2 :noselect t :align bottom)
     ("\\`\\*?magit-diff" :regexp t :align bottom :noselect t)
     ("\\`\\*makey" :regexp t :align bottom :noselect t)))
 '(shell-toggle-launch-shell 'shell)
 '(shm-auto-insert-bangs nil)
 '(shm-indent-spaces 4)
 '(shm-use-hdevtools t)
 '(shm-use-presentation-mode t)
 '(show-paren-delay 0)
 '(sky-color-clock-format "%-l:%M %p")
 '(slack-buffer-create-on-notify t)
 '(slack-completing-read-function 'ivy-completing-read)
 '(slack-prefer-current-team t)
 '(slack-request-timeout 30)
 '(slime-kill-without-query-p t)
 '(slime-repl-history-file "~/.emacs.d/data/slime-history.eld" t)
 '(slime-startup-animation nil)
 '(smex-history-length 20)
 '(smex-save-file "~/.emacs.d/data/smex-items")
 '(sp-highlight-pair-overlay nil)
 '(sql-sqlite-program "sqlite3")
 '(sr-attributes-display-mask '(nil nil t nil nil nil))
 '(sr-autoload-extensions nil)
 '(sr-confirm-kill-viewer nil)
 '(sr-kill-unused-buffers nil)
 '(sr-listing-switches "--time-style=locale --group-directories-first -alDhgG")
 '(sr-loop-use-popups nil)
 '(sr-popviewer-style 'single-frame)
 '(sr-show-file-attributes nil)
 '(sr-traditional-other-window t)
 '(sr-use-commander-keys nil)
 '(ssl-certificate-verification-policy 1)
 '(stock-quote-interval 60)
 '(svn-status-hide-unmodified t)
 '(swiper-stay-on-quit t)
 '(switch-to-buffer-preserve-window-point t)
 '(tab-always-indent 'complete)
 '(tags-add-tables t)
 '(tags-apropos-verbose t)
 '(tags-case-fold-search nil)
 '(tags-revert-without-query t)
 '(tail-max-size 25)
 '(tail-volatile nil)
 '(temp-buffer-resize-mode t nil (help))
 '(term-bind-key-alist
   '(("C-c C-c" . term-interrupt-subjob)
     ("C-b" . my-term-send-raw-at-prompt)
     ("C-f" . my-term-send-raw-at-prompt)
     ("C-a" . my-term-send-raw-at-prompt)
     ("C-e" . my-term-send-raw-at-prompt)
     ("C-p" . previous-line)
     ("C-n" . next-line)
     ("C-s" . isearch-forward)
     ("C-r" . isearch-backward)
     ("C-m" . term-send-raw)
     ("M-f" . term-send-forward-word)
     ("M-b" . term-send-backward-word)
     ("M->" . my-term-end-of-buffer)
     ("M-o" . term-send-backspace)
     ("M-p" . term-send-up)
     ("M-n" . term-send-down)
     ("M-d" . term-send-forward-kill-word)
     ("M-DEL" . term-send-backward-kill-word)
     ("M-r" . term-send-reverse-search-history)
     ("M-," . term-send-input)
     ("M-." . comint-dynamic-complete)
     ("C-y" . term-paste)))
 '(term-buffer-maximum-size 0)
 '(term-scroll-show-maximum-output t)
 '(text-mode-hook
   '(turn-on-auto-fill
     (lambda nil
       (ignore-errors
         (diminish 'auto-fill-function)))))
 '(tls-checktrust t)
 '(tls-program
   '("openssl s_client -connect %h:%p -no_ssl2 -ign_eof -CApath ~/.nix-profile/etc/ssl/certs -cert ~/Messages/me.pem"))
 '(tool-bar-mode nil)
 '(tramp-default-method "ssh")
 '(transient-history-file "~/.emacs.d/data/transient/history.el")
 '(transient-values-file "~/.emacs.d/data/transient/values.el")
 '(trash-directory "~/.Trash")
 '(undo-limit 800000)
 '(undo-tree-history-directory-alist '((".*" . "~/.cache/emacs/backups")))
 '(undo-tree-mode-lighter "")
 '(undo-tree-visualizer-timestamps t)
 '(unicode-fonts-block-font-mapping
   '(("Aegean Numbers"
      ("Noto Sans Symbols" "Aegean" "Symbola" "Quivira" "Code2001" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Ahom"
      ("AhomUnicode"))
     ("Alchemical Symbols"
      ("Noto Sans Symbols" "Symbola" "Quivira" "Everson Mono:weight=bold"))
     ("Alphabetic Presentation Forms"
      ("DejaVu Sans:width=condensed" "Arial Unicode MS" "Cardo" "Code2000" "Quivira" "Everson Mono:weight=bold" "FreeMono" "ALPHABETUM Unicode"))
     ("Anatolian Hieroglyphs"
      ("Anatolian"))
     ("Ancient Greek Musical Notation"
      ("Cardo" "Noto Sans Symbols" "Aegean" "New Athena Unicode" "Musica" "Symbola" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Ancient Greek Numbers"
      ("Noto Sans Symbols" "Apple Symbols" "New Athena Unicode" "Cardo" "Aegean" "Quivira" "Symbola" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Ancient Symbols"
      ("Noto Sans Symbols" "Analecta" "New Athena Unicode" "Cardo" "Aegean" "Quivira" "Symbola" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Arabic"
      ("Scheherazade New" "Courier New" "Simplified Arabic Fixed" "Simplified Arabic" "Amiri" "Aldhabi" "Adobe Arabic" "Urdu Typesetting" "Geeza Pro" "Baghdad" "Damascus" "Al Bayan" "Andalus" "Arabic Typesetting" "Traditional Arabic" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Arial Unicode MS" "Nadeem" "Microsoft Uighur" "Tahoma" "Microsoft Sans Serif" "MPH 2B Damase" "KufiStandardGK" "DecoType Naskh" "Koodak" "FreeMono" "Code2000"))
     ("Arabic Extended-A"
      ("Scheherazade New" "Amiri"))
     ("Arabic Mathematical Alphabetic Symbols"
      ("Scheherazade New" "Amiri"))
     ("Arabic Presentation Forms-A"
      ("Scheherazade New" "Geeza Pro" "Amiri" "Arial Unicode MS" "Microsoft Sans Serif" "Tahoma" "KufiStandardGK" "Andalus" "Arabic Typesetting" "Urdu Typesetting" "Adobe Arabic" "DecoType Naskh" "Al Bayan" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "MPH 2B Damase" "Code2000"))
     ("Arabic Presentation Forms-B"
      ("Scheherazade New" "DejaVu Sans Mono" "Geeza Pro" "Amiri" "Adobe Arabic" "Traditional Arabic" "Urdu Typesetting" "Arial Unicode MS" "Microsoft Sans Serif" "KufiStandardGK" "DejaVu Sans:width=condensed" "FreeMono" "DecoType Naskh" "Code2000"))
     ("Arabic Supplement"
      ("Scheherazade New" "Courier New" "Simplified Arabic Fixed" "Amiri" "Simplified Arabic" "Geeza Pro" "Damascus" "Andalus" "Arabic Typesetting" "Traditional Arabic" "Adobe Arabic" "Microsoft Uighur" "Tahoma" "Microsoft Sans Serif" "MPH 2B Damase"))
     ("Armenian"
      ("DejaVu Sans Mono" "Noto Sans Armenian" "Mshtakan" "Sylfaen" "DejaVu Sans:width=condensed" "Quivira" "MPH 2B Damase" "Code2000" "Arial Unicode MS" "Everson Mono:weight=bold" "FreeMono"))
     ("Arrows"
      ("DejaVu Sans Mono" "Apple Symbols" "Cambria Math" "Segoe UI Symbol" "DejaVu Sans:width=condensed" "Asana Math" "Arial Unicode MS" "BabelStone Modern" "Symbola" "Quivira" "Code2000" "Noto Sans Symbols" "Everson Mono:weight=bold" "FreeMono"))
     ("Avestan"
      ("Noto Sans Avestan" "Ahuramzda:weight=bold" "ALPHABETUM Unicode"))
     ("Balinese"
      ("Noto Sans Balinese:weight=bold" "Aksara Bali"))
     ("Bamum"
      ("Noto Sans Bamum"))
     ("Bamum Supplement"
      ("Noto Sans Bamum"))
     ("Batak"
      ("Batak-Unicode" "Noto Sans Batak"))
     ("Bengali"
      ("Bangla Sangam MN" "Noto Sans Bengali" "Noto Sans Bengali UI" "Nirmala UI" "Vrinda" "Mukti Narrow" "Akaash" "Arial Unicode MS" "Code2000" "ALPHABETUM Unicode"))
     ("Block Elements"
      ("DejaVu Sans Mono" "Noto Sans Symbols" "FreeMono" "DejaVu Sans:width=condensed" "Apple Symbols" "Segoe UI Symbol" "BabelStone Modern" "Symbola" "Quivira" "Code2000" "Everson Mono:weight=bold"))
     ("Bopomofo"
      ("Lantinghei TC" "MingLiU" "SimHei" "LiSong Pro" "FangSong" "SimSun" "DFKai-SB" "WenQuanYi Zen Hei Mono" "Microsoft JhengHei" "Microsoft JhengHei UI" "Microsoft YaHei" "Microsoft YaHei UI" "Lantinghei SC" "HAN NOM A" "Arial Unicode MS" "BabelStone Han" "Code2000" "ALPHABETUM Unicode"))
     ("Bopomofo Extended"
      ("MingLiU" "SimHei" "FangSong" "SimSun" "DFKai-SB" "Microsoft JhengHei" "Microsoft JhengHei UI" "Microsoft YaHei" "Microsoft YaHei UI" "BabelStone Han" "Code2000"))
     ("Box Drawing"
      ("DejaVu Sans Mono" "FreeMono" "DejaVu Sans" "Everson Mono" "Quivira" "Code2000" "Noto Sans Symbols" "Segoe UI Symbol" "Symbola"))
     ("Brahmi"
      ("Segoe UI Historic" "Noto Sans Brahmi" "Adinatha Tamil Brahmi" "ALPHABETUM Unicode"))
     ("Braille Patterns"
      ("Quivira" "Apple Braille" "DejaVu Sans:width=condensed" "Apple Symbols" "Segoe UI Symbol" "Symbola" "Noto Sans Symbols" "FreeMono" "Code2000" "Everson Mono:weight=bold"))
     ("Buginese"
      ("Noto Sans Buginese" "MPH 2B Damase" "Monlam Uni Sans Serif" "Code2000"))
     ("Buhid"
      ("Noto Sans Buhid" "Quivira" "Code2000"))
     ("Byzantine Musical Symbols"
      ("Noto Sans Symbols" "Musica" "Symbola" "FreeSerif"))
     ("CJK Compatibility"
      ("SimHei" "FangSong" "SimSun" "MingLiU" "Meiryo" "Microsoft JhengHei" "Microsoft JhengHei UI" "Lantinghei SC" "Lantinghei TC" "HAN NOM A" "Arial Unicode MS" "WenQuanYi Zen Hei Mono" "HanaMinA" "BabelStone Han" "Code2000"))
     ("CJK Compatibility Forms"
      ("WenQuanYi Zen Hei Mono" "Lantinghei SC" "SimHei" "FangSong" "SimSun" "LiSong Pro" "Baoli SC" "Microsoft YaHei" "Microsoft YaHei UI" "Lantinghei TC" "BabelStone Han" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "HAN NOM A" "Symbola" "Xingkai SC" "DFKai-SB" "Code2000"))
     ("CJK Compatibility Ideographs"
      ("SimHei" "FangSong" "SimSun" "Microsoft YaHei" "Microsoft YaHei UI" "WenQuanYi Zen Hei Mono" "BabelStone Han" "UnBatang" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "HAN NOM A" "Arial Unicode MS" "Lantinghei SC" "HanaMinA"))
     ("CJK Compatibility Ideographs Supplement"
      ("WenQuanYi Zen Hei Mono" "SimHei" "FangSong" "SimSun" "MingLiU" "HanaMinA" "Hiragino Kaku Gothic Pro" "Hiragino Maru Gothic Pro" "Hiragino Mincho Pro" "Microsoft JhengHei" "Microsoft JhengHei UI" "HAN NOM B" "LiSong Pro"))
     ("CJK Radicals Supplement"
      ("WenQuanYi Zen Hei Mono" "SimHei" "FangSong" "SimSun" "Microsoft YaHei" "Microsoft YaHei UI" "HanaMinA" "BabelStone Han" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "HAN NOM A" "DFKai-SB" "Apple Symbols" "Code2000"))
     ("CJK Strokes"
      ("WenQuanYi Zen Hei Mono" "HanaMinA" "BabelStone Han" "Code2000"))
     ("CJK Symbols and Punctuation"
      ("Lantinghei SC" "SimHei" "FangSong" "SimSun" "HanaMinA" "WenQuanYi Zen Hei Mono" "LiSong Pro" "STFangsong" "Microsoft YaHei" "Microsoft YaHei UI" "Lantinghei TC" "MingLiU" "HAN NOM A" "Arial Unicode MS" "PCMyungjo" "BabelStone Han" "Osaka:spacing=m" "Code2000"))
     ("CJK Unified Ideographs"
      ("WenQuanYi Zen Hei Mono" "Lantinghei SC" "Songti SC" "SimHei" "FangSong" "STFangsong" "SimSun" "LiSong Pro" "Baoli SC" "HanaMinA" "BabelStone Han" "Apple LiGothic" "Lantinghei TC" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "HAN NOM A" "DFKai-SB" "Arial Unicode MS" "Xingkai SC" "GB18030 Bitmap" "UnBatang"))
     ("CJK Unified Ideographs Extension A"
      ("SimHei" "FangSong" "STFangsong" "SimSun" "Songti SC" "Microsoft YaHei" "Microsoft YaHei UI" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "HanaMinA" "HAN NOM A" "Code2000" "DFKai-SB" "BabelStone Han" "GB18030 Bitmap"))
     ("CJK Unified Ideographs Extension B"
      ("SimHei" "FangSong" "SimSun" "LiSong Pro" "Microsoft YaHei" "Microsoft YaHei UI" "HanaMinB" "HAN NOM B" "Code2002" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "BabelStone Han" "DFKai-SB"))
     ("CJK Unified Ideographs Extension C"
      ("HanaMinB" "BabelStone Han" "HAN NOM B"))
     ("CJK Unified Ideographs Extension D"
      ("HanaMinB" "BabelStone Han"))
     ("CJK Unified Ideographs Extension E"
      ("HanaMinB" "BabelStone Han"))
     ("Carian"
      ("Segoe UI Historic" "Noto Sans Carian" "Aegean" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Chakma"
      ("Ribeng"))
     ("Cham"
      ("Noto Sans Cham" "Cham OI_Tangin" "Cham OI_Kulbleng" "Cham OI_Kul" "Code2000"))
     ("Cherokee"
      ("Aboriginal Sans" "Aboriginal Serif" "Plantagenet Cherokee" "Noto Sans Cherokee" "Gadugi" "MPH 2B Damase" "Quivira" "Everson Mono:weight=bold" "FreeMono" "Code2000"))
     ("Cherokee Supplement"
      ("Everson Mono:weight=bold"))
     ("Combining Diacritical Marks"
      ("Monaco" "Consolas" "Noto Sans" "Cambria Math" "Charis SIL" "Doulos SIL" "Courier New" "DejaVu Sans:width=condensed" "DejaVu Sans Mono" "Cardo" "Code2000" "Gentium Plus" "Junicode" "Tahoma" "Microsoft Sans Serif" "Arial" "Quivira" "Symbola" "Everson Mono" "FreeMono" "Arial Unicode MS" "ALPHABETUM Unicode"))
     ("Combining Diacritical Marks Extended"
      ("Monlam Uni Sans Serif"))
     ("Combining Diacritical Marks Supplement"
      ("Cardo" "FreeSerif" "Junicode" "Doulos SIL" "DejaVu Sans:width=condensed" "Noto Sans" "Segoe UI" "Code2000" "Everson Mono" "ALPHABETUM Unicode"))
     ("Combining Diacritical Marks for Symbols"
      ("Cambria Math" "Segoe UI Symbol" "Noto Sans Symbols" "Symbola" "Code2000" "Everson Mono" "Arial Unicode MS"))
     ("Combining Half Marks"
      ("Consolas" "DejaVu Sans:width=condensed" "Everson Mono:weight=bold" "Symbola"))
     ("Common Indic Number Forms"
      ("Noto Sans Kaithi" "Nirmala UI" "Siddhanta"))
     ("Control Pictures"
      ("Apple Symbols" "BabelStone Modern" "Noto Sans Symbols" "Segoe UI Symbol" "Arial Unicode MS" "Symbola" "Quivira" "FreeMono" "Code2000" "Everson Mono:weight=bold"))
     ("Coptic"
      ("Noto Sans Coptic" "Antinoou" "New Athena Unicode" "Segoe UI Historic" "Segoe UI Symbol" "Quivira" "Analecta" "Nilus" "Code2000" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Coptic Epact Numbers"
      ("Nilus" "Symbola"))
     ("Counting Rod Numerals"
      ("WenQuanYi Zen Hei Mono" "Noto Sans Symbols" "BabelStone Modern" "Symbola" "Quivira" "Apple Symbols" "Code2001"))
     ("Cuneiform"
      ("Segoe UI Historic" "Noto Sans Cuneiform" "Noto Sans Sumero-Akkadian Cuneiform" "Akkadian"))
     ("Cuneiform Numbers and Punctuation"
      ("Akkadian" "Segoe UI Historic" "Noto Sans Cuneiform" "Noto Sans Sumero-Akkadian Cuneiform"))
     ("Currency Symbols"
      ("Monaco" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Consolas" "Noto Sans Symbols" "Noto Sans" "Segoe UI" "Apple Symbols" "Symbola" "Quivira" "Everson Mono:weight=bold" "FreeMono"))
     ("Cypriot Syllabary"
      ("Segoe UI Historic" "Noto Sans Cypriot" "Aegean" "Code2001" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Cyrillic"
      ("Consolas" "Monaco" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Noto Sans" "Courier New" "Calibri" "Microsoft Sans Serif" "Code2000" "Arial Unicode MS" "Charis SIL" "Doulos SIL" "Symbola" "Quivira" "Everson Mono:weight=bold" "FreeMono" "Charcoal CY" "Geneva CY" "ALPHABETUM Unicode"))
     ("Cyrillic Extended-A"
      ("Quivira" "Everson Mono:weight=bold" "FreeSerif" "ALPHABETUM Unicode"))
     ("Cyrillic Extended-B"
      ("Quivira" "Code2000" "Everson Mono:weight=bold"))
     ("Cyrillic Supplement"
      ("Consolas" "Courier New" "Calibri" "Noto Sans" "DejaVu Sans:width=condensed" "Charis SIL" "Doulos SIL" "Symbola" "Quivira" "Code2000" "Everson Mono:weight=bold"))
     ("Deseret"
      ("Noto Sans Deseret" "Apple Symbols" "Segoe UI Symbol" "Analecta" "Code2001" "Everson Mono:weight=bold"))
     ("Devanagari"
      ("Annapurna SIL" "Noto Sans Devanagari" "Devanagari Sangam MN" "Devanagari MT" "Nirmala UI" "Mangal" "Samyak Devanagari" "Samyak" "Siddhanta" "Aparajita" "Code2000" "Arial Unicode MS" "ALPHABETUM Unicode"))
     ("Devanagari Extended"
      ("Annapurna SIL" "Siddhanta" "FreeSerif"))
     ("Dingbats"
      ("Apple Color Emoji" "DejaVu Sans Mono" "Segoe UI Symbol" "Zapf Dingbats" "DejaVu Sans:width=condensed" "Arial Unicode MS" "Code2000" "Noto Sans Symbols" "Symbola" "Quivira" "Everson Mono:weight=bold"))
     ("Domino Tiles"
      ("DejaVu Sans:width=condensed" "Symbola" "Quivira" "Segoe UI Symbol" "Noto Sans Symbols" "Code2001" "Everson Mono:weight=bold"))
     ("Early Dynastic Cuneiform"
      ("Akkadian"))
     ("Egyptian Hieroglyphs"
      ("Segoe UI Historic:weight=bold" "Noto Sans Egyptian Hieroglyphs:weight=bold" "Aegyptus:weight=bold" "Gardiner"))
     ("Elbasan"
      ("Albanian" "Everson Mono:weight=bold"))
     ("Emoticons"
      ("Apple Color Emoji" "Segoe UI Symbol" "Symbola" "Quivira"))
     ("Enclosed Alphanumeric Supplement"
      ("Segoe UI Symbol" "Noto Sans Symbols" "Symbola" "Quivira" "BabelStone Han" "BabelStone Modern"))
     ("Enclosed Alphanumerics"
      ("Noto Sans Symbols" "Segoe UI Symbol" "Junicode" "Arial Unicode MS" "Symbola" "Quivira" "Code2000" "BabelStone Han" "WenQuanYi Zen Hei Mono" "BabelStone Modern" "HAN NOM A" "Everson Mono:weight=bold"))
     ("Enclosed CJK Letters and Months"
      ("WenQuanYi Zen Hei Mono" "SimHei" "FangSong" "MingLiU" "Arial Unicode MS" "HanaMinA" "Meiryo" "BabelStone Han" "Quivira" "Code2000" "UnBatang" "HAN NOM A"))
     ("Enclosed Ideographic Supplement"
      ("Segoe UI Symbol" "Noto Sans Symbols" "HanaMinA" "BabelStone Han" "Symbola"))
     ("Ethiopic"
      ("Kefa" "Noto Sans Ethiopic" "Nyala" "Abyssinica SIL" "Ethiopia Jiret" "Ethiopic WashRa SemiBold" "Ethiopic Yebse" "Code2000"))
     ("Ethiopic Extended"
      ("Kefa" "Noto Sans Ethiopic" "Nyala" "Abyssinica SIL" "Code2000"))
     ("Ethiopic Extended-A"
      ("Kefa" "Noto Sans Ethiopic" "Abyssinica SIL"))
     ("Ethiopic Supplement"
      ("Kefa" "Noto Sans Ethiopic" "Nyala" "Abyssinica SIL" "Code2000"))
     ("General Punctuation"
      ("Monaco" "Apple Symbols" "Segoe UI Symbol" "Cambria Math" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Charis SIL" "Doulos SIL" "Antinoou" "Symbola" "Code2000" "Quivira" "Noto Sans" "Everson Mono:weight=bold" "FreeMono" "BabelStone Modern"))
     ("Geometric Shapes"
      ("DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Segoe UI Symbol" "Arial Unicode MS" "Symbola" "Noto Sans Symbols" "Quivira" "BabelStone Modern" "Everson Mono" "FreeMono" "Code2000"))
     ("Geometric Shapes Extended"
      ("Symbola" "Quivira"))
     ("Georgian"
      ("DejaVu Sans Mono" "Noto Sans Georgian" "Noto Serif Georgian" "DejaVu Sans:width=condensed" "Arial Unicode MS" "Code2000" "Quivira" "Sylfaen" "MPH 2B Damase" "Everson Mono:weight=bold"))
     ("Georgian Supplement"
      ("Noto Sans Georgian" "Noto Serif Georgian" "DejaVu Serif:width=condensed" "MPH 2B Damase" "Quivira" "Everson Mono:weight=bold"))
     ("Glagolitic"
      ("Noto Sans Glagolitic" "Segoe UI Historic" "Segoe UI Symbol" "MPH 2B Damase" "Quivira" "FreeSerif" "ALPHABETUM Unicode"))
     ("Gothic"
      ("Noto Sans Gothic" "Segoe UI Historic" "Segoe UI Symbol" "Analecta" "Junicode" "Sadagolthina" "MPH 2B Damase" "FreeSerif" "Code2001" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Greek Extended"
      ("Consolas" "DejaVu Sans Mono" "Courier New" "Antinoou" "Noto Sans" "DejaVu Sans:width=condensed" "Cardo" "Junicode" "New Athena Unicode" "Microsoft Sans Serif" "Gentium Plus Compact" "Gentium Plus" "Arial Unicode MS" "Arial" "Tahoma" "Aegean" "Code2000" "Quivira" "Everson Mono:weight=bold" "FreeMono" "ALPHABETUM Unicode"))
     ("Greek and Coptic"
      ("Consolas" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Antinoou" "Noto Sans" "Segoe UI Historic" "Segoe UI Symbol" "New Athena Unicode" "Calibri" "Microsoft Sans Serif" "Gentium Plus Compact" "Gentium Plus" "Lucida Console" "Arial Unicode MS" "Cardo" "Aegean" "Code2000" "Symbola" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode" "Noto Sans Coptic"))
     ("Gujarati"
      ("Nirmala UI" "Noto Sans Gujarati" "Noto Sans Gujarati UI" "Gujarati MT" "Shruti" "Samyak Gujarati" "Samyak" "Gujarati Sangam MN" "Code2000" "Arial Unicode MS"))
     ("Gurmukhi"
      ("Gurmukhi Sangam MN" "Gurmukhi MN" "Nirmala UI" "Noto Sans Gurmukhi" "Noto Sans Gurmukhi UI" "Raavi" "Code2000" "Arial Unicode MS" "AnmolUni"))
     ("Halfwidth and Fullwidth Forms"
      ("Meiryo" "Arial Unicode MS" "Microsoft JhengHei" "Microsoft JhengHei UI" "Microsoft YaHei" "Microsoft YaHei UI" "BabelStone Han" "Apple Symbols" "Quivira" "Code2000" "HAN NOM A"))
     ("Hangul Compatibility Jamo"
      ("PCMyungjo" "Malgun Gothic" "Gulim" "Dotum" "Batang" "Gungsuh" "AppleMyungjo" "UnBatang" "WenQuanYi Zen Hei Mono" "HAN NOM A" "Arial Unicode MS" "Code2000" "HeadLineA"))
     ("Hangul Jamo"
      ("UnBatang" "WenQuanYi Zen Hei Mono" "PCMyungjo" "Malgun Gothic" "Gulim" "Dotum" "Batang" "Gungsuh" "Arial Unicode MS" "Code2000"))
     ("Hangul Jamo Extended-A"
      ("Malgun Gothic" "HanaMinA" "UnBatang"))
     ("Hangul Jamo Extended-B"
      ("Malgun Gothic" "HanaMinA" "UnBatang"))
     ("Hangul Syllables"
      ("AppleGothic" "Malgun Gothic" "Gulim" "Dotum" "Batang" "Gungsuh" "UnBatang" "WenQuanYi Zen Hei Mono" "Arial Unicode MS" "Code2000"))
     ("Hanunoo"
      ("Noto Sans Hanunoo" "MPH 2B Damase" "Quivira" "FreeSerif"))
     ("Hebrew"
      ("Miriam Fixed" "Ezra SIL" "Ezra SIL SR" "Arial Hebrew" "Raanana" "New Peninim MT" "Aharoni" "David" "FrankRuehl" "Gisha" "Levenim MT" "Narkisim" "Rod" "Cardo" "Courier New" "Adobe Hebrew" "Code2000" "Aramaic Imperial Yeb" "Microsoft Sans Serif" "Tahoma" "Lucida Sans Unicode" "Arial Unicode MS" "Arial" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Hiragana"
      ("Osaka:spacing=m" "MS Gothic" "MS Mincho" "MingLiU" "Hiragino Kaku Gothic Pro" "Meiryo" "Arial Unicode MS" "HanaMinA" "BabelStone Han" "Microsoft JhengHei" "Microsoft YaHei" "Microsoft YaHei UI" "HAN NOM A" "Code2000" "ALPHABETUM Unicode"))
     ("IPA Extensions"
      ("Monaco" "Consolas" "DejaVu Sans Mono" "Courier New" "Noto Sans" "Arial Unicode MS" "Arial" "Tahoma" "Microsoft Sans Serif" "Aboriginal Sans" "Cardo" "Symbola" "Quivira" "Everson Mono:weight=bold" "FreeMono" "Code2000" "ALPHABETUM Unicode"))
     ("Ideographic Description Characters"
      ("SimHei" "FangSong" "SimSun" "Microsoft YaHei" "Microsoft YaHei UI" "BabelStone Han" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "AppleMyungjo" "HanaMinA" "HAN NOM A" "Quivira" "DFKai-SB" "Code2000"))
     ("Imperial Aramaic"
      ("Aramaic Imperial Yeb" "Quivira" "Segoe UI Historic" "Noto Sans Imperial Aramaic" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Inscriptional Pahlavi"
      ("ZH Mono" "Segoe UI Historic" "Noto Sans Inscriptional Pahlavi" "ALPHABETUM Unicode" "Ahuramzda:weight=bold"))
     ("Inscriptional Parthian"
      ("ZH Mono" "Segoe UI Historic" "Noto Sans Inscriptional Parthian" "ALPHABETUM Unicode"))
     ("Javanese"
      ("Noto Sans Javanese" "Tuladha Jejeg"))
     ("Kaithi"
      ("Noto Sans Kaithi"))
     ("Kana Supplement"
      ("Meiryo UI" "HanaMinA" "BabelStone Han"))
     ("Kanbun"
      ("SimHei" "FangSong" "SimSun" "Meiryo" "Arial Unicode MS" "WenQuanYi Zen Hei Mono" "HanaMinA" "BabelStone Han" "MingLiU" "Microsoft JhengHei" "Microsoft YaHei" "Microsoft YaHei UI" "HAN NOM A" "Code2000"))
     ("Kangxi Radicals"
      ("WenQuanYi Zen Hei Mono" "SimHei" "FangSong" "Meiryo" "SimSun" "Microsoft YaHei" "Microsoft YaHei UI" "BabelStone Han" "HanaMinA" "MingLiU" "Microsoft JhengHei" "Microsoft JhengHei UI" "HAN NOM A" "DFKai-SB" "AppleMyungjo" "Apple Symbols" "Code2000"))
     ("Kannada"
      ("Kannada Sangam MN" "Noto Sans Kannada" "Noto Sans Kannada UI" "Tunga" "Akshar Unicode" "Kedage" "Nirmala UI" "Kannada MN" "Arial Unicode MS" "Code2000"))
     ("Katakana"
      ("Osaka:spacing=m" "MS Gothic" "MingLiU" "Meiryo" "HanaMinA" "Arial Unicode MS" "BabelStone Han" "Microsoft JhengHei" "Microsoft YaHei" "Microsoft YaHei UI" "HAN NOM A" "Code2000" "ALPHABETUM Unicode"))
     ("Katakana Phonetic Extensions"
      ("MS Gothic" "MingLiU" "Meiryo" "HanaMinA" "Microsoft YaHei" "Microsoft YaHei UI" "BabelStone Han" "HAN NOM A" "Code2000"))
     ("Kayah Li"
      ("Noto Sans Kayah Li" "Code2000" "FreeMono"))
     ("Kharoshthi"
      ("Segoe UI Historic" "Noto Sans Kharoshthi" "MPH 2B Damase" "ALPHABETUM Unicode"))
     ("Khmer"
      ("Noto Sans Khmer" "Noto Sans Khmer UI" "Noto Serif Khmer" "Khmer Sangam MN" "DaunPenh" "Code2000" "MoolBoran" "Khmer Mondulkiri" "Khmer Busra"))
     ("Khmer Symbols"
      ("Noto Sans Khmer" "Noto Sans Khmer UI" "Noto Serif Khmer" "Khmer Sangam MN" "MoolBoran" "Khmer Mondulkiri" "Khmer Busra" "Code2000"))
     ("Khojki"
      ("KhojkiUnicodeOT"))
     ("Khudawadi"
      ("OldSindhi"))
     ("Lao"
      ("Noto Sans Lao" "Noto Sans Lao UI" "Noto Serif Lao" "Lao Sangam MN" "DokChampa" "DejaVu Sans Mono" "Arial Unicode MS" "Saysettha MX" "DejaVu Sans:width=condensed" "Code2000"))
     ("Latin Extended-C"
      ("DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Noto Sans" "Cambria Math" "Gentium Plus" "Charis SIL" "Doulos SIL" "Code2000" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Latin Extended-D"
      ("FreeMono" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Charis SIL" "Doulos SIL" "Junicode" "Cardo" "Quivira" "Code2000" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Latin Extended-E"
      ("Quivira" "Everson Mono:weight=bold" "HanaMinA"))
     ("Lepcha"
      ("Mingzat" "Noto Sans Lepcha"))
     ("Letterlike Symbols"
      ("Monaco" "Noto Sans Symbols" "Segoe UI Symbol" "Apple Symbols" "Cambria Math" "DejaVu Sans:width=condensed" "Arial Unicode MS" "Code2000" "Symbola" "Quivira" "HAN NOM A" "Everson Mono:weight=bold"))
     ("Limbu"
      ("Noto Sans Limbu" "Namdhinggo SIL" "MPH 2B Damase" "Code2000"))
     ("Linear A"
      ("Aegean"))
     ("Linear B Ideograms"
      ("Noto Sans Linear B" "Aegean" "Code2001" "Everson Mono:weight=bold" "ALPHABETUM Unicode" "MPH 2B Damase"))
     ("Linear B Syllabary"
      ("Noto Sans Linear B" "Aegean" "Code2001" "Everson Mono:weight=bold" "ALPHABETUM Unicode" "MPH 2B Damase" "Penuturesu"))
     ("Lisu"
      ("Lisu Unicode" "Miao Unicode" "Noto Sans Lisu" "Lisu Tzimu" "Quivira" "Everson Mono:weight=bold"))
     ("Lycian"
      ("Segoe UI Historic" "Noto Sans Lycian" "Aegean" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Lydian"
      ("Segoe UI Historic" "Noto Sans Lydian" "Aegean" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Mahjong Tiles"
      ("Segoe UI Symbol" "Symbola" "Noto Sans Symbols" "Quivira" "Everson Mono"))
     ("Malayalam"
      ("Malayalam Sangam MN" "Nirmala UI" "Kartika" "Code2000" "Akshar Unicode" "Samyak Malayalam" "Samyak" "Arial Unicode MS"))
     ("Mandaic"
      ("Noto Sans Mandaic"))
     ("Mathematical Alphanumeric Symbols"
      ("Cambria Math" "Noto Sans Symbols" "Asana Math" "Code2001" "Symbola" "Quivira" "Everson Mono:weight=bold"))
     ("Mathematical Operators"
      ("Monaco" "DejaVu Sans Mono" "Segoe UI Symbol" "Cambria Math" "DejaVu Sans:width=condensed" "Noto Sans Symbols" "Apple Symbols" "Asana Math" "Arial Unicode MS" "Code2000" "Symbola" "Quivira" "Everson Mono:weight=bold" "FreeMono"))
     ("Meetei Mayek"
      ("Noto Sans Meetei Mayek" "Eeyek Unicode" "Meetei Mayek"))
     ("Meetei Mayek Extensions"
      ("Noto Sans Meetei Mayek"))
     ("Meroitic Cursive"
      ("Nilus" "Segoe UI Historic" "Segoe UI Symbol"))
     ("Meroitic Hieroglyphs"
      ("Nilus"))
     ("Miao"
      ("Miao Unicode" "Albanian"))
     ("Miscellaneous Mathematical Symbols-A"
      ("Noto Sans Symbols" "Apple Symbols" "Segoe UI Symbol" "Asana Math" "Code2000" "Symbola" "Quivira" "Cambria Math" "Everson Mono:weight=bold"))
     ("Miscellaneous Mathematical Symbols-B"
      ("Noto Sans Symbols" "Segoe UI Symbol" "Apple Symbols" "Cambria Math" "Asana Math" "Code2000" "Symbola" "Quivira"))
     ("Miscellaneous Symbols"
      ("Noto Sans Symbols" "Segoe UI Symbol" "Apple Symbols" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Arial Unicode MS" "Symbola" "Quivira" "MS Reference Sans Serif" "Cardo" "Code2000" "Everson Mono:weight=bold"))
     ("Miscellaneous Symbols and Arrows"
      ("Symbola" "Quivira" "Asana Math" "Code2000" "Segoe UI Symbol" "Noto Sans Symbols"))
     ("Miscellaneous Symbols and Pictographs"
      ("Apple Color Emoji" "Segoe UI Symbol" "Symbola" "Quivira"))
     ("Miscellaneous Technical"
      ("Segoe UI Symbol" "Noto Sans Symbols" "Apple Symbols" "Cambria Math" "DejaVu Sans Mono" "Code2000" "Symbola" "Quivira" "Everson Mono:weight=bold"))
     ("Modi"
      ("MarathiCursiveG"))
     ("Modifier Tone Letters"
      ("Apple Symbols" "Noto Sans Symbols" "Gentium Plus" "Code2000" "Quivira" "Charis SIL" "Doulos SIL" "DejaVu Sans Mono"))
     ("Mongolian"
      ("STFangsong" "STHeiti" "STKaiti" "STSong" "Noto Sans Mongolian" "Mongolian Baiti" "Daicing Xiaokai" "Code2000"))
     ("Mro"
      ("Mro Unicode"))
     ("Musical Symbols"
      ("Noto Sans Symbols" "Musica" "FreeSerif" "Symbola" "Quivira"))
     ("Myanmar"
      ("Noto Sans Myanmar" "Noto Sans Myanmar UI" "Myanmar Text" "Myanmar Sangam MN" "Myanmar MN" "TharLon" "Yunghkio" "Myanmar3" "Masterpiece Uni Sans" "Padauk" "Code2000" "Tai Le Valentinium"))
     ("Myanmar Extended-A"
      ("Noto Sans Myanmar" "Noto Sans Myanmar UI" "Myanmar Text" "Padauk" "TharLon" "Yunghkio"))
     ("Myanmar Extended-B"
      ("TharLon" "Yunghkio"))
     ("NKo"
      ("Ebrima" "Conakry" "DejaVu Sans:width=condensed" "Noto Sans NKo" "Code2000"))
     ("Nabataean"
      ("Everson Mono:weight=bold"))
     ("New Tai Lue"
      ("Noto Sans New Tai Lue" "Microsoft New Tai Lue" "Dai Banna SIL Book" "Dai Banna SIL Book:style=Regular"))
     ("Number Forms"
      ("DejaVu Sans:width=condensed" "Asana Math" "Arial Unicode MS" "Junicode" "Symbola" "Quivira" "Charis SIL" "Doulos SIL" "Code2000" "Everson Mono:weight=bold" "FreeMono" "ALPHABETUM Unicode"))
     ("Ogham"
      ("Segoe UI Historic" "Segoe UI Symbol" "Noto Sans Ogham" "DejaVu Sans:width=condensed" "BabelStone Modern" "Code2000" "Aboriginal Serif" "Quivira" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Ol Chiki"
      ("Nirmala UI" "Noto Sans Ol Chiki" "Code2000"))
     ("Old Hungarian"
      ("OldHungarian"))
     ("Old Italic"
      ("Segoe UI Historic" "Segoe UI Symbol" "DejaVu Sans:width=condensed" "Cardo" "New Athena Unicode" "Aegean" "Noto Sans Old Italic" "Albanian" "Code2001" "Quivira" "Everson Mono:weight=bold" "FreeMono" "ALPHABETUM Unicode"))
     ("Old North Arabian"
      ("Marib"))
     ("Old Permic"
      ("Everson Mono:weight=bold"))
     ("Old Persian"
      ("Segoe UI Historic" "Noto Sans Old Persian" "MPH 2B Damase" "Aegean" "Code2001" "FreeSans" "ALPHABETUM Unicode"))
     ("Old South Arabian"
      ("Segoe UI Historic" "Noto Sans Old South Arabian" "Quivira" "Qataban" "Everson Mono:weight=bold"))
     ("Old Turkic"
      ("Noto Sans Old Turkic" "Segoe UI Historic" "Segoe UI Symbol" "Quivira" "Everson Mono:weight=bold"))
     ("Optical Character Recognition"
      ("Apple Symbols" "Segoe UI Symbol" "Noto Sans Symbols" "Arial Unicode MS" "Symbola" "Quivira" "FreeMono" "BabelStone Modern" "Code2000" "Everson Mono"))
     ("Oriya"
      ("Noto Sans Oriya" "Oriya Sangam MN" "Nirmala UI" "Kalinga" "Samyak Oriya" "Samyak" "Code2000" "Arial Unicode MS"))
     ("Ornamental Dingbats"
      ("Symbola"))
     ("Osmanya"
      ("Noto Sans Osmanya" "Ebrima" "Andagii" "MPH 2B Damase" "Code2001" "Everson Mono:weight=bold"))
     ("Phags-pa"
      ("BabelStone Phags-pa Book" "BabelStone Phags-pa Book:style=Regular" "Noto Sans Phags-pa" "Microsoft PhagsPa" "Code2000"))
     ("Phaistos Disc"
      ("Aegean" "Noto Sans Symbols" "Symbola" "Everson Mono:weight=bold" "Code2001" "ALPHABETUM Unicode"))
     ("Phoenician"
      ("Segoe UI Historic" "Noto Sans Phoenician" "Aegean" "Quivira" "Code2001" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Phonetic Extensions"
      ("Monaco" "Consolas" "Calibri" "Noto Sans" "Aboriginal Sans" "Charis SIL" "Doulos SIL" "Quivira" "Courier New" "DejaVu Sans:width=condensed" "Code2000" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Phonetic Extensions Supplement"
      ("Consolas" "Calibri" "Courier New" "Noto Sans" "Aboriginal Sans" "Charis SIL" "Doulos SIL" "Quivira" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Code2000" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Playing Cards"
      ("DejaVu Sans:width=condensed" "Symbola" "Noto Sans Symbols" "Segoe UI Symbol" "Quivira"))
     ("Rejang"
      ("Noto Sans Rejang" "Code2000" "Everson Mono:weight=bold"))
     ("Rumi Numeral Symbols"
      ("HanaMinA"))
     ("Runic"
      ("Noto Sans Runic" "Segoe UI Historic" "Segoe UI Symbol" "Aboriginal Serif" "Junicode" "FreeMono" "Quivira" "Code2000" "Cardo" "Everson Mono:weight=bold" "ALPHABETUM Unicode"))
     ("Samaritan"
      ("Noto Sans Samaritan" "Quivira" "Everson Mono:weight=bold"))
     ("Saurashtra"
      ("Noto Sans Saurashtra" "Code2000" "Sourashtra"))
     ("Sharada"
      ("Albanian"))
     ("Shavian"
      ("Segoe UI Historic" "Noto Sans Shavian" "Andagii" "MPH 2B Damase" "Apple Symbols" "Code2001" "Everson Mono:weight=bold"))
     ("Siddham"
      ("MuktamsiddhamG"))
     ("Sinhala"
      ("Noto Sans Sinhala" "Nirmala UI" "Iskoola Pota" "Akshar Unicode" "Sinhala Sangam MN"))
     ("Small Form Variants"
      ("Apple Symbols" "Arial Unicode MS" "WenQuanYi Zen Hei Mono" "Microsoft YaHei" "Microsoft YaHei UI" "Code2000"))
     ("Sora Sompeng"
      ("Nirmala UI"))
     ("Specials"
      ("BabelStone Modern" "Noto Sans Symbols" "Apple Symbols" "Arial Unicode MS" "Symbola" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Quivira" "FreeMono" "BabelStone Han"))
     ("Sundanese"
      ("Noto Sans Sundanese" "Sundanese Unicode"))
     ("Sundanese Supplement"
      ("Noto Sans Sundanese"))
     ("Superscripts and Subscripts"
      ("Consolas" "Monaco" "Apple Symbols" "Cambria Math" "DejaVu Sans Mono" "DejaVu Sans:width=condensed" "Segoe UI Symbol" "Asana Math" "Charis SIL" "Doulos SIL" "Symbola" "Quivira" "Everson Mono:weight=bold" "FreeMono"))
     ("Supplemental Arrows-A"
      ("Segoe UI Symbol" "Cambria Math" "DejaVu Sans:width=condensed" "Asana Math" "Quivira" "Symbola" "Apple Symbols" "Noto Sans Symbols" "Code2000" "Everson Mono:weight=bold" "FreeMono" "BabelStone Modern"))
     ("Supplemental Arrows-B"
      ("Cambria Math" "Segoe UI Symbol" "Apple Symbols" "Noto Sans Symbols" "Asana Math" "Quivira" "Symbola" "Code2000" "Everson Mono:weight=bold"))
     ("Supplemental Arrows-C"
      ("Symbola"))
     ("Supplemental Mathematical Operators"
      ("Cambria Math" "Segoe UI Symbol" "Noto Sans Symbols" "Apple Symbols" "Asana Math" "Code2000" "Symbola" "Quivira" "Everson Mono:weight=bold"))
     ("Supplemental Punctuation"
      ("DejaVu Sans Mono" "Segoe UI Symbol" "Noto Sans Symbols" "Antinoou" "New Athena Unicode" "Cardo" "Aegean" "Symbola" "Quivira" "Everson Mono:weight=bold" "Code2000" "ALPHABETUM Unicode"))
     ("Supplemental Symbols and Pictographs"
      ("Symbola"))
     ("Syloti Nagri"
      ("Noto Sans Syloti Nagri" "MPH 2B Damase"))
     ("Syriac"
      ("Segoe UI Historic" "Estrangelo Edessa" "Estrangelo Nisibin" "Code2000"))
     ("Tagalog"
      ("Quivira" "Noto Sans Tagalog"))
     ("Tagbanwa"
      ("Noto Sans Tagbanwa" "Quivira"))
     ("Tags"
      ("BabelStone Modern" "BabelStone Han"))
     ("Tai Le"
      ("Microsoft Tai Le" "TharLon" "Noto Sans Tai Le" "Yunghkio" "Tai Le Valentinium" "MPH 2B Damase" "FreeSerif"))
     ("Tai Tham"
      ("Noto Sans Tai Tham" "Lanna Alif" "Chiangsaen Alif" "Lanna Unicode UI" "Monlam Uni Sans Serif"))
     ("Tai Viet"
      ("Tai Heritage Pro" "Noto Sans Tai Viet"))
     ("Tai Xuan Jing Symbols"
      ("WenQuanYi Zen Hei Mono" "Apple Symbols" "Noto Sans Symbols" "Segoe UI Symbol" "BabelStone Han" "DejaVu Sans:width=condensed" "Symbola" "Quivira" "BabelStone Modern" "Code2001" "Everson Mono:weight=bold"))
     ("Takri"
      ("Albanian"))
     ("Tamil"
      ("Latha" "Noto Sans Tamil" "Noto Sans Tamil UI" "Nirmala UI" "Tamil MN" "Tamil Sangam MN" "InaiMathi" "Vijaya" "Maduram" "Akshar Unicode" "Samyak Tamil" "Samyak" "Code2000" "Arial Unicode MS"))
     ("Telugu"
      ("Noto Sans Telugu" "Noto Sans Telugu UI" "Telugu Sangam MN" "Vani" "Nirmala UI" "Gautami" "Akshar Unicode" "Code2000" "Arial Unicode MS"))
     ("Thaana"
      ("MV Boli" "Noto Sans Thaana" "MPH 2B Damase" "Code2000" "Everson Mono:weight=bold"))
     ("Thai"
      ("Thonburi" "DokChampa" "Noto Sans Thai" "Noto Sans Thai UI" "Noto Serif Thai" "Ayuthaya" "Silom" "Krungthep" "Sathu" "Angsana New" "AngsanaUPC" "Code2000" "Tahoma" "Arial Unicode MS" "Quivira" "Everson Mono:weight=bold"))
     ("Tibetan"
      ("Noto Sans Tibetan" "Kailasa" "Kokonor" "Tibetan Machine Uni" "Microsoft Himalaya" "Jomolhari" "Monlam Uni Sans Serif" "Arial Unicode MS"))
     ("Tifinagh"
      ("Noto Sans Tifinagh" "Ebrima" "DejaVu Sans:width=condensed" "Code2000" "Quivira" "Everson Mono:weight=bold"))
     ("Transport and Map Symbols"
      ("Apple Color Emoji" "Segoe UI Symbol" "Symbola"))
     ("Ugaritic"
      ("Segoe UI Historic" "Noto Sans Ugaritic" "Aegean" "Code2001" "Andagii" "Quivira" "Everson Mono:weight=bold" "FreeSans" "ALPHABETUM Unicode"))
     ("Unified Canadian Aboriginal Syllabics"
      ("Aboriginal Sans" "Aboriginal Serif" "Noto Sans Canadian Aboriginal" "Gadugi" "Euphemia UCAS" "Euphemia" "Code2000" "Quivira" "Everson Mono:weight=bold"))
     ("Unified Canadian Aboriginal Syllabics Extended"
      ("Aboriginal Sans" "Aboriginal Serif" "Noto Sans Canadian Aboriginal" "Gadugi" "Euphemia UCAS" "Euphemia" "Quivira" "Everson Mono:weight=bold"))
     ("Vai"
      ("Ebrima" "Noto Sans Vai" "Dukor" "Wakor" "Code2000" "Quivira"))
     ("Variation Selectors"
      ("BabelStone Modern" "BabelStone Han" "Code2000"))
     ("Variation Selectors Supplement"
      ("BabelStone Modern" "BabelStone Han"))
     ("Vedic Extensions"
      ("Siddhanta"))
     ("Vertical Forms"
      ("Microsoft YaHei" "Microsoft YaHei UI" "Symbola"))
     ("Yi Radicals"
      ("Noto Sans Yi" "Nuosu SIL" "Microsoft Yi Baiti" "STFangsong" "Code2000"))
     ("Yi Syllables"
      ("Noto Sans Yi" "Nuosu SIL" "Microsoft Yi Baiti" "STFangsong" "Code2000"))
     ("Yijing Hexagram Symbols"
      ("WenQuanYi Zen Hei Mono" "Noto Sans Symbols" "Segoe UI Symbol" "Apple Symbols" "DejaVu Sans:width=condensed" "BabelStone Han" "Symbola" "Quivira" "BabelStone Modern" "Code2000" "Everson Mono:weight=bold"))))
 '(unicode-fonts-skip-font-groups
   '(chinese-simplified chinese-traditional decorative low-quality-glyphs multicolor))
 '(uniquify-buffer-name-style 'post-forward-angle-brackets nil (uniquify))
 '(url-cache-directory "~/.emacs.d/data/url/cache")
 '(url-configuration-directory "~/.emacs.d/data/url/")
 '(url-irc-function 'url-irc-erc)
 '(use-package-enable-imenu-support t)
 '(user-full-name "John Wiegley")
 '(user-initials "jww")
 '(user-mail-address "johnw@newartisans.com")
 '(vc-command-messages t)
 '(vc-follow-symlinks t)
 '(vc-git-diff-switches '("-w" "-U3"))
 '(vc-handled-backends '(GIT SVN CVS Bzr Hg))
 '(vc-make-backup-files t)
 '(version-control t)
 '(visible-bell t)
 '(w3m-cookie-accept-bad-cookies 'ask)
 '(w3m-default-display-inline-images t)
 '(w3m-fill-column 100)
 '(w3m-use-cookies t)
 '(warning-minimum-log-level :error)
 '(wdired-use-dired-vertical-movement 'sometimes)
 '(weblogger-config-alist
   '(("newartisans" "http://www.newartisans.com/xmlrpc.php" "johnw" "" "5")))
 '(wg-mode-line-on nil)
 '(wg-morph-on nil)
 '(wg-prefix-key "")
 '(wg-query-for-save-on-emacs-exit nil)
 '(wg-query-for-save-on-workgroups-mode-exit nil)
 '(wgrep-auto-save-buffer t)
 '(wgrep-enable-key "")
 '(whitespace-auto-cleanup t t)
 '(whitespace-line-column 80)
 '(whitespace-rescan-timer-time nil t)
 '(whitespace-silent t t)
 '(whitespace-style '(face trailing lines-tail space-before-tab))
 '(window-divider-default-bottom-width 1)
 '(window-divider-default-places 'bottom-only)
 '(workgroups-mode nil)
 '(x-stretch-cursor t)
 '(x86-lookup-browse-pdf-function
   (lambda
     (pdf page)
     (org-pdfview-open
      (concat pdf "::" page))))
 '(x86-lookup-pdf "~/.local/share/x86/325462-sdm-vol-1-2abcd-3abcd.pdf")
 '(yaoddmuse-directory "~/.emacs.d/doc")
 '(yas-installed-snippets-dir "~/.emacs.d/site-lisp/yasnippet-snippets/snippets/" t)
 '(yas-prompt-functions '(yas-ido-prompt yas-completing-prompt yas-no-prompt))
 '(yas-snippet-dirs '("/Users/johnw/.emacs.d/snippets"))
 '(yas-triggers-in-field t)
 '(yas-wrap-around-region t)
 '(z3-solver-cmd "z3")
 '(zencoding-indentation 2)
 '(zencoding-preview-default nil)
 '(zoom-size 'size-callback))

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(company-coq-features/code-folding-bullet-face ((t (:weight bold))))
 '(coq-symbol-face ((t (:inherit default-face))))
 '(cursor ((t (:background "hotpink"))))
 '(diff-added ((((background dark)) (:foreground "#FFFF9B9BFFFF")) (t (:foreground "DarkGreen"))))
 '(diff-changed ((((background dark)) (:foreground "Yellow")) (t (:foreground "MediumBlue"))))
 '(diff-context ((((background dark)) (:foreground "White")) (t (:foreground "Black"))))
 '(diff-file-header ((((background dark)) (:foreground "Cyan" :background "Black")) (t (:foreground "Red" :background "White"))))
 '(diff-header ((((background dark)) (:foreground "Cyan")) (t (:foreground "Red"))))
 '(diff-index ((((background dark)) (:foreground "Magenta")) (t (:foreground "Green"))))
 '(diff-nonexistent ((((background dark)) (:foreground "#FFFFFFFF7474")) (t (:foreground "DarkBlue"))))
 '(diredp-dir-name ((t (:foreground "blue"))))
 '(diredp-file-name ((t nil)))
 '(diredp-file-suffix ((t (:foreground "lightgreen"))))
 '(ediff-current-diff-C ((t (:extend t :background "#222200"))))
 '(flymake-note ((t nil)))
 '(font-lock-comment-face ((t (:foreground "grey50" :slant italic))))
 '(font-lock-doc-face ((t (:foreground "cornflowerblue"))))
 '(highlight ((t (:background "blue4"))))
 '(markdown-header-face-1 ((t (:inherit markdown-header-face :height 2.0))))
 '(markdown-header-face-2 ((t (:inherit markdown-header-face :height 1.6))))
 '(markdown-header-face-3 ((t (:inherit markdown-header-face :height 1.4))))
 '(markdown-header-face-4 ((t (:inherit markdown-header-face :height 1.2))))
 '(markup-meta-face ((t (:stipple nil :foreground "gray60" :inverse-video nil :box nil :strike-through nil :overline nil :underline nil :slant normal :weight normal :width normal :foundry "unknown" :family "Monospace"))))
 '(markup-meta-hide-face ((t (:inherit markup-meta-face :foreground "gray50"))))
 '(markup-verbatim-face ((t (:foreground "orange"))))
 '(minibuffer-prompt ((t (:foreground "grey80"))))
 '(mode-line-inactive ((t (:background "grey95"))))
 '(nobreak-space ((t nil)))
 '(proof-eager-annotation-face ((t nil)))
 '(proof-locked-face ((t (:background "#180526"))))
 '(proof-omitted-proof-face ((t (:extend t :background "#23103c"))))
 '(proof-queue-face ((t (:background "#431807"))))
 '(proof-script-sticky-error-face ((t (:background "#50110e"))))
 '(proof-warning-face ((t (:background "orange4"))))
 '(variable-pitch ((t (:height 1.2 :family "Bookerly"))))
 '(whitespace-line ((t (:background "yellow"))))
 '(yas-field-highlight-face ((t (:background "#e4edfc")))))
