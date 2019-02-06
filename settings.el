(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(Info-fit-frame-flag nil)
 '(TeX-PDF-mode t)
 '(TeX-auto-save t)
 '(TeX-auto-untabify t)
 '(TeX-electric-escape t)
 '(TeX-engine (quote xetex))
 '(TeX-expand-list
   (quote
    (("%p" TeX-printer-query)
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
             (eq TeX-engine
                 (quote default))
             (or TeX-PDF-mode TeX-DVI-via-PDFTeX))
            "pdf" "")))
     ("%(PDFout)"
      (lambda nil
        (cond
         ((and
           (eq TeX-engine
               (quote xetex))
           (not TeX-PDF-mode))
          " -no-pdf")
         ((and
           (eq TeX-engine
               (quote luatex))
           (not TeX-PDF-mode))
          " --output-format=dvi")
         ((and
           (eq TeX-engine
               (quote default))
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
            (eq TeX-engine
                (quote omega))
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
                  t)))))))
 '(TeX-parse-self t)
 '(TeX-view-program-list
   (quote
    (("Skim"
      ("osascript" " ~/bin/skim-gotopage.script" " %O"
       (mode-io-correlate " %(outpage)"))))))
 '(TeX-view-program-selection
   (quote
    (((output-dvi style-pstricks)
      "dvips and gv")
     (output-dvi "xdvi")
     (output-pdf "Skim")
     (output-html "xdg-open"))))
 '(abbrev-file-name "~/.emacs.d/abbrevs.el")
 '(ac-auto-show-menu 1.0)
 '(ac-auto-start 3)
 '(ac-comphist-file "~/.emacs.d/data/ac-comphist.dat" t)
 '(ac-dwim nil)
 '(ac-ignore-case nil)
 '(ac-trigger-key "<tab>")
 '(ac-use-fuzzy nil)
 '(ace-isearch-submode (quote ace-jump-char-mode))
 '(ad-redefinition-action (quote accept))
 '(after-save-hook
   (quote
    (executable-make-buffer-file-executable-if-script-p)))
 '(agda-input-tweak-all
   (quote
    (agda-input-compose
     (agda-input-prepend "\\")
     (agda-input-nonempty))))
 '(agda-input-user-translations
   (quote
    (("^" "^")
     ("nat" "⟹")
     ("for" "△")
     ("mer" "▽")
     ("iso" "≅")
     ("miso" "≃")
     ("diag" "∆")
     ("whl" "⊳")
     ("whr" "⊲"))))
 '(agda2-include-dirs
   (quote
    ("." "~/.nix-profile/share/agda-prelude" "~/.nix-profile/share/agda")))
 '(alert-default-style (quote fringe))
 '(alert-notifier-command
   "~/Applications/terminal-notifier.app/Contents/MacOS/terminal-notifier")
 '(align-c++-modes (quote (csharp-mode c++-mode c-mode java-mode groovy-mode)))
 '(align-to-tab-stop nil)
 '(allout-command-prefix ".")
 '(ansi-color-names-vector
   ["black" "red" "green" "brown" "blue" "magenta" "blue" "white"])
 '(appt-display-interval 30)
 '(appt-message-warning-time 60)
 '(auto-compression-mode t nil (jka-compr))
 '(auto-hscroll-mode (quote current-line))
 '(auto-revert-use-notify nil)
 '(auto-save-file-name-transforms (quote (("\\`/[^/]*:.*" "/tmp" t))))
 '(auto-save-interval 64)
 '(auto-save-list-file-prefix "~/.emacs.d/data/auto-save-list/.saves-")
 '(auto-save-timeout 2)
 '(avy-case-fold-search t)
 '(avy-keys (quote (97 111 101 117 105 100 104 116 110 115)))
 '(avy-timeout-seconds 0.3)
 '(aw-dispatch-when-more-than 3)
 '(aw-scope (quote frame))
 '(backup-directory-alist
   (quote
    (("/Volumes/Files/" . "/Volumes/Files/.backups")
     ("\\(recentf\\|archive/sent\\)" . "/tmp")
     (".*" . "~/.cache/emacs/backups"))))
 '(backward-delete-char-untabify-method (quote untabify))
 '(bbdb-default-country "")
 '(bbdb-file "~/Documents/tasks/bbdb" t)
 '(bbdb-message-caching-enabled nil)
 '(bbdb-no-duplicates t)
 '(bbdb-offer-save (quote savenoprompt))
 '(bbdb-silent-running t)
 '(bbdb-use-pop-up nil)
 '(bbdb-vcard-import-translation-table
   (quote
    (("CELL\\|CAR" . "Mobile")
     ("WORK" . "Work")
     ("HOME" . "Home")
     ("^$" . "Work"))))
 '(bbdb/mail-auto-create-p nil)
 '(bc-bookmark-file "~/.emacs.d/data/breadcrumb" t)
 '(bind-key-segregation-regexp "\\`\\(\\(C-[chx.] \\|M-[gso] \\)\\([CM]-\\)?\\|.+-\\)")
 '(bm-buffer-persistence t)
 '(bm-cycle-all-buffers t)
 '(bm-highlight-style (quote bm-highlight-only-fringe))
 '(bm-in-lifo-order t)
 '(bm-repository-file "/Users/johnw/.emacs.d/data/bm-repository")
 '(bmkp-bmenu-commands-file "~/.emacs.d/data/bmk-bmenu-commands.el" t)
 '(bmkp-bmenu-state-file "~/.emacs.d/data/bmk-bmenu-state.el" t)
 '(bmkp-crosshairs-flag nil)
 '(bmkp-last-as-first-bookmark-file "~/Documents/tasks/bookmarks")
 '(bookmark-default-file "~/Documents/tasks/bookmarks")
 '(browse-url-browser-function
   (quote
    (("osx-ghc" . eww-browse-url)
     (".*" . browse-url-default-macosx-browser))))
 '(byte-compile-verbose nil)
 '(c-default-style
   (quote
    ((java-mode . "gnu")
     (awk-mode . "awk")
     (other . "gnu"))))
 '(calendar-daylight-time-zone-name "PDT")
 '(calendar-latitude 38.5474883)
 '(calendar-longitude -121.5262693)
 '(calendar-mark-holidays-flag t)
 '(calendar-standard-time-zone-name "PST")
 '(calendar-time-zone -480)
 '(canlock-password "8d2ee9a7e4658c4ff6d863f91a3dd5340b3918ec")
 '(cc-other-file-alist
   (quote
    (("\\.hs\\'"
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
      (".cxx")))))
 '(clean-buffer-list-kill-never-buffer-names
   (quote
    ("*scratch*" "*Messages*" "*server*" "*Group*" "*Org Agenda*" "todo.txt" "dfinity.txt" "habits.txt" "Bahai.txt" "OSS.txt" "diary" "notes.txt" "&bitlbee")))
 '(clean-buffer-list-kill-never-regexps
   (quote
    ("^ \\*Minibuf-.*\\*$" "^\\*Summary" "^\\*Article" "^#")))
 '(clean-buffer-list-kill-regexps (quote (".*")))
 '(column-number-mode t)
 '(company-coq-disabled-features
   (quote
    (hello prettify-symbols smart-subscripts dynamic-symbols-backend)))
 '(company-coq-prettify-symbols-alist
   (quote
    (("|-" . 8866)
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
     ("Prop" . 120031))))
 '(company-frontends
   (quote
    (company-pseudo-tooltip-unless-just-one-frontend company-echo-metadata-frontend company-preview-frontend)))
 '(company-global-modes (quote (emacs-lisp-mode c-mode c++-mode)))
 '(company-idle-delay nil)
 '(company-quickhelp-use-propertized-text t)
 '(company-show-numbers t)
 '(compilation-always-kill t)
 '(compilation-ask-about-save nil)
 '(compilation-context-lines 10)
 '(compilation-scroll-output (quote first-error))
 '(compilation-search-path
   (quote
    (nil "~/src/gitlib" "~/src/gitlib/gitlib" "~/src/gitlib/gitlib-libgit2" "~/src/gitlib/gitlib-s3" "~/src/gitlib/gitlib-test" "~/src/gitlib/git-monitor" "~/src/c2hsc")))
 '(compilation-skip-threshold 2)
 '(compilation-window-height 100)
 '(completion-ignored-extensions
   (quote
    (".glob" ".vo" ".v.d" ".o" "~" ".bin" ".lbin" ".so" ".a" ".ln" ".blg" ".bbl" ".elc" ".lof" ".glo" ".idx" ".lot" ".svn/" ".hg/" ".git/" ".bzr/" "CVS/" "_darcs/" "_MTN/" ".fmt" ".tfm" ".class" ".fas" ".lib" ".mem" ".x86f" ".sparcf" ".dfsl" ".pfsl" ".d64fsl" ".p64fsl" ".lx64fsl" ".lx32fsl" ".dx64fsl" ".dx32fsl" ".fx64fsl" ".fx32fsl" ".sx64fsl" ".sx32fsl" ".wx64fsl" ".wx32fsl" ".fasl" ".ufsl" ".fsl" ".dxl" ".lo" ".la" ".gmo" ".mo" ".toc" ".aux" ".cp" ".fn" ".ky" ".pg" ".tp" ".vr" ".cps" ".fns" ".kys" ".pgs" ".tps" ".vrs" ".pyc" ".pyo")))
 '(coq-compile-auto-save (quote save-coq))
 '(coq-compile-before-require t)
 '(coq-compile-parallel-in-background t)
 '(coq-holes-minor-mode nil)
 '(coq-lookup-browse-pdf-function
   (lambda
     (pdf page)
     (org-pdfview-open
      (concat pdf "::" page))))
 '(coq-lookup-pdf "~/.local/share/coq/coq-8.7.1-reference-manual.pdf")
 '(coq-maths-menu-enable t)
 '(coq-one-command-per-line nil)
 '(coq-prefer-top-of-conclusion t)
 '(coq-prog-args (quote ("-emacs")))
 '(counsel-describe-function-preselect (quote ivy-function-called-at-point))
 '(counsel-find-file-ignore-regexp
   "\\(\\`\\.[^.]\\|\\(?:\\.\\(?:aux\\|b\\(?:bl\\|in\\|lg\\|zr/\\)\\|c\\(?:lass\\|ps?\\)\\|d\\(?:\\(?:64fs\\|fs\\|x\\(?:\\(?:32\\|64\\)fs\\)?\\)l\\)\\|elc\\|f\\(?:asl?\\|mt\\|ns?\\|\\(?:x\\(?:\\(?:32\\|64\\)f\\)\\)?sl\\)\\|g\\(?:it/\\|lob?\\|mo\\)\\|hg/\\|idx\\|kys?\\|l\\(?:bin\\|ib\\|o[ft]\\|x\\(?:\\(?:32\\|64\\)fsl\\)\\|[ano]\\)\\|m\\(?:em\\|o\\)\\|p\\(?:64fsl\\|fsl\\|gs?\\|y[co]\\)\\|s\\(?:o\\|parcf\\|vn/\\|x\\(?:\\(?:32\\|64\\)fsl\\)\\)\\|t\\(?:fm\\|oc\\|ps?\\)\\|ufsl\\|v\\(?:\\.d\\|rs\\|[or]\\)\\|wx\\(?:\\(?:32\\|64\\)fsl\\)\\|x86f\\|[ao]\\)\\|CVS/\\|_\\(?:\\(?:MTN\\|darcs\\)/\\)\\|~\\)\\'\\)" nil nil "Customized with use-package counsel")
 '(counsel-locate-cmd (quote counsel-locate-cmd-default))
 '(counsel-projectile-remove-current-buffer t)
 '(counsel-projectile-remove-current-project t)
 '(current-language-environment "UTF-8")
 '(custom-buffer-done-function (quote kill-buffer))
 '(custom-file "~/.emacs.d/settings.el")
 '(custom-raised-buttons nil)
 '(custom-safe-themes
   (quote
    ("644e23f289dcd3548c3f054785c72cf1fd81fcee07875ac7fed311985a67a0dc" "c74e83f8aa4c78a121b52146eadb792c9facc5b1f02c917e3dbb454fca931223" "3c83b3676d796422704082049fc38b6966bcad960f896669dfc21a7a37a748fa" "b9e9ba5aeedcc5ba8be99f1cc9301f6679912910ff92fdf7980929c2fc83ab4d" "84d2f9eeb3f82d619ca4bfffe5f157282f4779732f48a5ac1484d94d5ff5b279" "a27c00821ccfd5a78b01e4f35dc056706dd9ede09a8b90c6955ae6a390eb1c1e" default)))
 '(dabbrev-case-fold-search nil)
 '(dabbrev-case-replace nil)
 '(default-major-mode (quote text-mode) t)
 '(delete-by-moving-to-trash t)
 '(delete-old-versions (quote none))
 '(diary-file "~/Documents/tasks/diary")
 '(diff-mode-hook
   (quote
    (diff-delete-empty-files diff-make-unified smerge-mode)))
 '(directory-free-space-args "-kh")
 '(dired-clean-up-buffers-too nil)
 '(dired-dwim-target t)
 '(dired-hide-details-hide-information-lines nil)
 '(dired-hide-details-hide-symlink-targets nil)
 '(dired-listing-switches "-lah")
 '(dired-no-confirm
   (quote
    (byte-compile chgrp chmod chown copy hardlink symlink touch)))
 '(dired-omit-files
   "^\\.?#\\|^\\.\\(DS_Store\\|localized\\|AppleDouble\\)$\\|^\\.\\.$")
 '(dired-omit-mode nil t)
 '(dired-recursive-copies (quote always))
 '(dired-recursive-deletes (quote always))
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
   (quote
    ("<<<<<<< A: HEAD" A "||||||| Ancestor" Ancestor "=======" B ">>>>>>> B: Incoming")))
 '(ediff-diff-options "-w")
 '(ediff-highlight-all-diffs nil)
 '(ediff-show-clashes-only t)
 '(ediff-window-setup-function (quote ediff-setup-windows-plain))
 '(edit-server-new-frame nil)
 '(el-get-auto-update-cached-recipes nil)
 '(el-get-dir "~/.emacs.d/site-lisp/")
 '(el-get-generate-autoloads nil)
 '(electric-indent-mode nil)
 '(elfeed-db-directory "~/.emacs.d/data/elfeed" t)
 '(elfeed-enclosure-default-dir "/Users/johnw/Downloads")
 '(elfeed-feeds
   (quote
    ("http://feeds.feedburner.com/schneier/excerpts" "https://www.reddit.com/new/.rss" "http://feeds.feedburner.com/codinghorror/" "http://blog.metatheorem.org/feed.xml" "http://www.tuaw.com/category/mac/rss.xml" "http://www.apple.com/main/rss/hotnews/hotnews.rss" "http://daringfireball.net/index.xml" "http://blog.higher-order.com/atom.xml" "http://www.haskellforall.com/feeds/posts/default?alt=rss" "http://comonad.com/reader/feed/" "http://byorgey.wordpress.com/feed/" "http://jaspervdj.be/rss.xml" "https://ghc.haskell.org/trac/ghc/blog?format=rss" "http://jeremykun.com/feed/" "https://feeds.feedburner.com/RomanCheplyaka" "http://tcsavage.org/atom.xml" "http://sequence.complete.org/node/feed" "http://www.serpentine.com/blog/feed/" "http://chris-taylor.github.io/atom.xml" "http://sigfpe.blogspot.com/feeds/posts/default" "http://blog.typlab.com/feed/" "http://intoverflow.wordpress.com/feed/" "https://elvishjerricco.github.io/feed.xml" "http://bartoszmilewski.wordpress.com/feed/" "http://lambda.jstolarek.com/feed/" "http://javran.github.io/atom.xml" "http://donsbot.wordpress.com/feed/" "http://dev.stephendiehl.com/fun/rss/atom.xml" "http://jelv.is/blog/atom.xml" "https://ocharles.org.uk/blog/posts.rss" "http://duplode.github.io/rss.xml" "http://themonadreader.wordpress.com/feed/" "http://learningagdaandats.wordpress.com/feed/" "http://paolocapriotti.com/atom.xml" "http://www.stephendiehl.com/feed.rss" "http://lambda-the-ultimate.org/rss.xml" "http://www.joachim-breitner.de/blog_feed.rss" "http://alpmestan.com/rss.xml" "http://blog.ezyang.com/feed/atom/" "http://lpuppet.banquise.net/atom.xml" "http://patternsinfp.wordpress.com/feed/" "http://blog.well-typed.com/feed/" "https://haskellexists.blogspot.com/feeds/posts/default" "http://feeds.bahai.org/bwns/rss" "http://www.bahairights.org/feed/" "http://iran.bahai.us/feed/" "https://stackoverflow.com/feeds/tag?tagnames=coq&sort=newest" "http://mukeshiiitm.wordpress.com/feed/" "http://poleiro.info/atom.xml" "http://pigworker.wordpress.com/feed/" "http://coq-blog.clarus.me/rss.xml" "http://osa1.net/rss.xml" "http://metatheorem.wordpress.com/feed/" "http://goodmath.scientopia.org/feed/" "http://existentialtype.wordpress.com/feed/" "https://golem.ph.utexas.edu/category/atom10.xml" "http://blog.jbapple.com/feeds/posts/default" "https://gmalecha.github.io/feed.xml" "http://mazzo.li/rss.xml" "http://www.carloangiuli.com/blog/feed/" "http://syntaxexclamation.wordpress.com/feed/" "http://feeds.feedburner.com/CoolTools" "http://motherboard.vice.com/rss?trk_source=motherboard" "http://feeds.arstechnica.com/arstechnica/gadgets")))
 '(emms-player-vlc-command-name "/Applications/Misc/VLC.app/Contents/MacOS/VLC")
 '(enable-recursive-minibuffers t)
 '(erc-auto-query (quote window-noselect))
 '(erc-autoaway-message "I'm away (after %i seconds of idle-time)")
 '(erc-autojoin-channels-alist
   (quote
    (("0.1" "#nixos" "#nix-darwin" "#hnix" "#haskell-overflow" "#haskell-ops" "#haskell-infrastructure" "#haskell" "#coq-blah" "#coq" "##categorytheory" "#use-package/Lobby" "#ledger" "#haskell-nix/Lobby" "#coq/coq" "#hs-to-coq" "#org-mode")
     ("freenode" "#haskell" "#coq" "#ledger" "#haskell-ops" "#nix-darwin" "#haskell-infrastructure" "##categorytheory" "#nixos" "#org-mode")
     ("gitter" "#use-package/Lobby" "#haskell-nix/Lobby"))))
 '(erc-button-alist
   (quote
    (("https://gist\\.github\\.com/\\(.*\\)" 0 t gist-fetch 1)
     ((quote nicknames)
      0 erc-button-buttonize-nicks erc-nick-popup 0)
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
     ("\\bGoogle:\\([^\n\f]+\\)" 0 t
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
     ("\\s-\\(@\\([0-9][0-9][0-9]\\)\\)" 1 t erc-button-beats-to-time 2))))
 '(erc-fill-function (quote erc-fill-variable))
 '(erc-fill-static-center 12)
 '(erc-foolish-content
   (quote
    ("MichaelSnoyman" "BrendanHay" "MichaelSloan" "ChrisDone" "travis-ci.*ekmett" "analystics.*ekmett" "rudybot:" "Ostergaard")))
 '(erc-format-nick-function (quote erc-format-@nick))
 '(erc-generate-log-file-name-function (quote erc-generate-log-file-name-short))
 '(erc-header-line-format nil)
 '(erc-hide-list (quote ("JOIN" "NICK" "PART" "QUIT")))
 '(erc-ignore-list (quote ("lensbot" "rudybot" "johnwilkins")))
 '(erc-ignore-reply-list (quote ("JordiGH")))
 '(erc-keywords (quote ("wiegley" "ledger" "eshell" "use-package")))
 '(erc-log-channels-directory "~/Messages/ERC")
 '(erc-log-write-after-send t)
 '(erc-lurker-hide-list (quote ("JOIN" "NICK" "PART" "QUIT" "MODE")))
 '(erc-modules
   (quote
    (autojoin button completion dcc fill identd irccontrols list match menu move-to-prompt netsplit networks noncommands readonly replace ring services smiley stamp track truncate highlight-nicknames)))
 '(erc-nick "johnw")
 '(erc-port 6667)
 '(erc-priority-people-regexp "\\`[^#].+")
 '(erc-prompt-for-nickserv-password nil)
 '(erc-rename-buffers t)
 '(erc-replace-alist (quote (("</?FONT>" . ""))))
 '(erc-server "irc.freenode.net")
 '(erc-services-mode t)
 '(erc-text-matched-hook (quote (erc-hide-fools my-erc-hook)))
 '(erc-track-enable-keybindings t)
 '(erc-track-exclude (quote ("#idris" "#agda" "#twitter_jwiegley")))
 '(erc-track-exclude-types
   (quote
    ("JOIN" "KICK" "NICK" "PART" "QUIT" "MODE" "333" "353")))
 '(erc-track-faces-priority-list
   (quote
    (erc-error-face
     (erc-nick-default-face erc-current-nick-face)
     erc-current-nick-face erc-keyword-face
     (erc-nick-default-face erc-pal-face)
     erc-pal-face erc-nick-msg-face erc-direct-msg-face)))
 '(erc-track-score-mode t)
 '(erc-track-showcount t)
 '(erc-user-full-name (quote user-full-name))
 '(erc-yank-query-before-gisting nil)
 '(eshell-directory-change-hook
   (quote
    (sml/generate-buffer-identification direnv-update-environment)))
 '(eshell-directory-name "~/.emacs.d/eshell/")
 '(eshell-hist-ignoredups t)
 '(eshell-history-size 50000)
 '(eshell-ls-dired-initial-args (quote ("-h")))
 '(eshell-ls-exclude-regexp "~\\'")
 '(eshell-ls-initial-args "-h")
 '(eshell-modules-list
   (quote
    (eshell-alias eshell-basic eshell-cmpl eshell-dirs eshell-glob eshell-hist eshell-ls eshell-pred eshell-prompt eshell-rebind eshell-script eshell-smart eshell-term eshell-unix eshell-xtra)))
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
   (quote
    (([(control 97)]
      . eshell-bol)
     ([home]
      . eshell-bol)
     ([(control 100)]
      . eshell-delchar-or-maybe-eof)
     ([backspace]
      . eshell-delete-backward-char)
     ([delete]
      . eshell-delete-backward-char))))
 '(eshell-save-history-on-exit t)
 '(eshell-stringify-t nil)
 '(eshell-term-name "ansi")
 '(eshell-visual-commands
   (quote
    ("vi" "top" "screen" "less" "lynx" "rlogin" "telnet")))
 '(eudc-inline-expansion-format (quote ("%s <%s>" name email)))
 '(eval-expr-print-function (quote pp))
 '(eval-expr-print-length 100)
 '(eval-expr-print-level 20)
 '(eww-lnum-actions-link-alist
   (quote
    ("----  Link   ----"
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
      "Download with Aria"))))
 '(eww-search-prefix "https://startpage.com/do/m/mobilesearch?query=")
 '(explicit-shell-file-name "~/.emacs.d/runshell")
 '(eyebrowse-keymap-prefix "")
 '(eyebrowse-mode-line-separator " ")
 '(eyebrowse-new-workspace t)
 '(fill-column 78)
 '(find-ls-option (quote ("-print0 | xargs -P4 -0 ls -ldN" . "-ldN")))
 '(find-ls-subdir-switches "-ldN")
 '(flx-ido-use-faces nil)
 '(flycheck-coq-executable "ct-coqtop")
 '(flycheck-display-errors-delay 0.0)
 '(flycheck-haskell-hpack-preference (quote prefer-cabal))
 '(flycheck-standard-error-navigation nil)
 '(flymake-compilation-prevents-syntax-check nil)
 '(flymake-proc-compilation-prevents-syntax-check nil)
 '(flyspell-abbrev-p nil)
 '(flyspell-use-meta-tab nil)
 '(font-lock-support-mode (quote jit-lock-mode))
 '(font-lock-verbose nil)
 '(forge-database-file "~/.config/forge/database.sqlite")
 '(frame-title-format
   (quote
    (:eval
     (concat
      (if buffer-file-name default-directory "%b")
      "    "
      (number-to-string
       (cdr
        (assq
         (quote width)
         (frame-parameters))))
      "x"
      (number-to-string
       (cdr
        (assq
         (quote height)
         (frame-parameters))))))) t)
 '(gdb-find-source-frame t)
 '(gdb-same-frame nil)
 '(ggtags-enable-navigation-keys nil)
 '(ggtags-oversize-limit 1048576)
 '(ggtags-use-sqlite3 t)
 '(git-commit-mode-hook
   (quote
    (turn-on-auto-fill flyspell-mode git-commit-save-message)) t)
 '(glasses-separator "-")
 '(glasses-uncapitalize-p t)
 '(global-auto-complete-mode t)
 '(global-auto-revert-mode t)
 '(global-font-lock-mode t nil (font-lock))
 '(global-undo-tree-mode t)
 '(grep-command "egrep -nH -e ")
 '(grep-find-command
   "find . -name '*' -type f -print0 | xargs -0 -P8 egrep -nH ")
 '(grep-save-buffers t)
 '(guide-key/guide-key-sequence t)
 '(guide-key/idle-delay 1.5)
 '(guide-key/popup-window-position (quote bottom))
 '(haskell-compile-cabal-build-command "cd %s && cabal new-build --ghc-option=-ferror-spans")
 '(haskell-hasktags-arguments (quote ("-e" "-x" "--ignore-close-implementation")))
 '(haskell-hoogle-command nil)
 '(haskell-indent-spaces 4)
 '(haskell-indentation-ifte-offset 4)
 '(haskell-indentation-layout-offset 4)
 '(haskell-indentation-left-offset 4)
 '(haskell-indentation-starter-offset 4)
 '(haskell-indentation-where-post-offset 4)
 '(haskell-indentation-where-pre-offset 4)
 '(haskell-process-load-or-reload-prompt t)
 '(helm-command-prefix-key nil)
 '(helm-dash-browser-func (quote eww))
 '(helm-dash-docsets-path "/Users/johnw/Library/Application Support/Dash/DocSets/")
 '(helm-firefox-default-directory "~/Library/Application Support/Firefox/")
 '(helm-minibuffer-history-key nil)
 '(helm-recoll-options (quote ("recollq" "-t" "-b")))
 '(hi2-ifte-offset 4)
 '(hi2-layout-offset 4)
 '(hi2-left-offset 4)
 '(hi2-show-indentations nil)
 '(hibtypes-github-default-user "jwiegley")
 '(hippie-expand-try-functions-list
   (quote
    (try-expand-dabbrev try-expand-dabbrev-all-buffers try-expand-dabbrev-from-kill try-complete-file-name-partially try-complete-file-name try-expand-all-abbrevs try-expand-list try-expand-line try-complete-lisp-symbol-partially try-complete-lisp-symbol)))
 '(history-delete-duplicates t)
 '(history-length 200)
 '(hkey-init nil)
 '(holiday-bahai-holidays nil)
 '(hoogle-binary-path "hoogle")
 '(hpaste-announce (quote always))
 '(hpaste-blank-title nil)
 '(hpaste-channel "#haskell")
 '(hpaste-default-lang "haskell")
 '(hpaste-default-nick "johnw")
 '(hpaste-lang (quote always))
 '(ibuffer-default-display-maybe-show-predicates t)
 '(ibuffer-expert t)
 '(ibuffer-formats
   (quote
    ((mark modified read-only " "
           (name 16 -1)
           " "
           (size 6 -1 :right)
           " "
           (mode 16 16)
           " " filename)
     (mark " "
           (name 16 -1)
           " " filename))))
 '(ibuffer-maybe-show-regexps nil)
 '(ibuffer-saved-filter-groups
   (quote
    (("default"
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
      ("Coq"
       (or
        (mode . coq-mode)
        (name . "^\\*\\(coq\\(-.*\\)?\\|goals\\|response\\)\\*")
        (name . "_CoqProject")))
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
      ("Magit"
       (or
        (mode . magit-status-mode)
        (mode . magit-log-mode)
        (name . "^\\*magit")
        (name . "git-monitor")))
      ("Emacs"
       (or
        (name . "^\\*scratch\\*$")
        (name . "^\\*Messages\\*$")
        (name . "^\\*\\(Customize\\|Help\\)")
        (name . "\\*\\(Echo\\|Minibuf\\)")))))))
 '(ibuffer-show-empty-filter-groups nil)
 '(ibuffer-shrink-to-minimum-size t t)
 '(ibuffer-use-other-window t)
 '(icicle-Completions-text-scale-decrease 0)
 '(icicle-apropos-cycle-next-keys (quote ([next] [(control 110)])))
 '(icicle-apropos-cycle-previous-keys (quote ([prior] [(control 112)])))
 '(icicle-incremental-completion nil)
 '(icicle-max-candidates 100)
 '(ido-auto-merge-work-directories-length 0)
 '(ido-cannot-complete-command (quote ido-exit-minibuffer))
 '(ido-decorations
   (quote
    ("{" "}" "," ",..." "[" "]" " [No match]" " [Matched]" " [Not readable]" " [Too big]" " [Confirm]")))
 '(ido-enable-flex-matching t)
 '(ido-enable-last-directory-history nil)
 '(ido-enable-tramp-completion nil)
 '(ido-enter-matching-directory (quote first))
 '(ido-ignore-files
   (quote
    ("\\`CVS/" "\\`#" "\\`.#" "\\`\\.\\./" "\\`\\./" "\\`\\.DS_Store" "\\`\\.localized" "\\.sparsebundle/" "\\.dmg\\'")))
 '(ido-save-directory-list-file "~/.emacs.d/data/ido.last")
 '(ido-use-virtual-buffers t)
 '(ido-use-virtual-buffers-automatically t)
 '(idris-interpreter-flags (quote ("-p" "effects")))
 '(image-dired-dir "~/.emacs.d/data/image-dired/" t)
 '(imagemagick-render-type 1)
 '(indent-tabs-mode nil)
 '(inhibit-startup-echo-area-message "johnw")
 '(inhibit-startup-screen t)
 '(initial-major-mode (quote fundamental-mode))
 '(initial-scratch-message "")
 '(initsplit-customizations-alist
   (quote
    (("\\`\\(gnus\\|nn\\|message\\|mail\\|mm-\\|smtp\\|send-mail\\|check-mail\\|spam\\|sc-\\)" "~/.emacs.d/gnus-settings.el" nil nil)
     ("\\`\\(org-\\|deft-\\|cfw:\\)" "~/.emacs.d/org-settings.el" nil nil))))
 '(ipa-file "~/Documents/ipa")
 '(ipa-overlay-position "above")
 '(irfc-directory "~/Archives/Admin/RFC/")
 '(ispell-extra-args (quote ("--sug-mode=fast" "--keyboard=dvorak")))
 '(ivy-dynamic-exhibit-delay-ms 200 nil nil "Customized with use-package ivy")
 '(ivy-extra-directories (quote ("./")))
 '(ivy-height 10 nil nil "Customized with use-package ivy")
 '(ivy-ignore-buffers
   (quote
    ("\\` " "\\`\\*git-monitor:" "\\`\\*magit-process:" "\\.elc$" "\\.CFUserTextEncoding" "\\`\\*Quail Completions\\*\\'" "\\`\\.newsrc-dribble\\'" "\\`\\.newsrc.eld\\'")))
 '(ivy-initial-inputs-alist nil t)
 '(ivy-magic-tilde nil nil nil "Customized with use-package ivy")
 '(ivy-re-builders-alist (quote ((t . ivy--regex-ignore-order))) t)
 '(ivy-rich-parse-remote-buffer nil)
 '(ivy-use-virtual-buffers t nil nil "Customized with use-package ivy")
 '(ivy-wrap t nil nil "Customized with use-package ivy")
 '(jiralib-url "https://dfinity.atlassian.net/")
 '(jist-enable-default-authorized t)
 '(jist-gist-directory "/Users/johnw/src/notes/gists")
 '(jobhours-files
   (quote
    ("~/Documents/tasks/dfinity.txt" "~/Documents/tasks/archive/dfinity.txt")))
 '(kill-do-not-save-duplicates t)
 '(kill-ring-max 500)
 '(kill-whole-line t)
 '(langtool-language-tool-jar "/run/current-system/sw/share/languagetool-commandline.jar")
 '(large-file-warning-threshold nil)
 '(ledger-binary-path "ledger")
 '(ledger-file "/Volumes/Files/Accounts/ledger.dat")
 '(ledger-post-use-ido t)
 '(line-number-mode t)
 '(load-prefer-newer t)
 '(lsp-enable-eldoc nil)
 '(lsp-haskell-process-args-hie (quote ("-l" "/tmp/hie.log")))
 '(lsp-highlight-symbol-at-point nil)
 '(lsp-inhibit-message t)
 '(lsp-ui-doc-enable nil)
 '(mac-pass-command-to-system nil)
 '(mac-pass-control-to-system nil)
 '(mac-wheel-button-is-mouse-2 nil)
 '(magit-auto-revert-mode nil)
 '(magit-completing-read-function (quote my-ivy-completing-read))
 '(magit-diff-options nil)
 '(magit-diff-refine-hunk t)
 '(magit-fetch-arguments nil)
 '(magit-highlight-trailing-whitespace nil)
 '(magit-highlight-whitespace nil)
 '(magit-log-section-commit-count 10)
 '(magit-pre-refresh-hook nil)
 '(magit-process-popup-time 15)
 '(magit-push-always-verify nil)
 '(magit-refresh-status-buffer nil)
 '(magit-stage-all-confirm nil)
 '(magit-unstage-all-confirm nil)
 '(magit-use-overlays nil)
 '(magithub-clone-default-directory "~/src")
 '(magithub-dir "/Users/johnw/.emacs.d/data/magithub")
 '(make-backup-file-name-function (quote my-make-backup-file-name))
 '(malyon-stories-directory "~/Documents/games")
 '(markdown-command "pandoc -f markdown_github+smart" t)
 '(markdown-command-needs-filename t)
 '(markdown-enable-math t)
 '(markdown-open-command "marked")
 '(math-additional-units
   (quote
    ((GiB "1024 * MiB" "Giga Byte")
     (MiB "1024 * KiB" "Mega Byte")
     (KiB "1024 * B" "Kilo Byte")
     (B nil "Byte")
     (Gib "1024 * Mib" "Giga Bit")
     (Mib "1024 * Kib" "Mega Bit")
     (Kib "1024 * b" "Kilo Bit")
     (b "B / 8" "Bit"))) t)
 '(mc/list-file "~/.emacs.d/data/mc-lists.el")
 '(mediawiki-site-alist
   (quote
    (("Wikipedia" "https://en.wikipedia.org/w/" "jwiegley" "" nil "Main Page"))))
 '(menu-bar-mode nil)
 '(midnight-delay 18000)
 '(midnight-mode t)
 '(moccur-following-mode-toggle nil)
 '(modelinepos-column-limit 80)
 '(mudel-mode-hook (quote (mudel-add-scroll-to-bottom)))
 '(mudel-output-filter-functions (quote (ansi-color-process-output)))
 '(multi-term-program "screen")
 '(multi-term-program-switches "-DR")
 '(multi-term-scroll-show-maximum-output t)
 '(my-gnus-thread-sort-functions
   (quote
    (gnus-thread-sort-by-most-recent-date gnus-thread-sort-by-total-score)))
 '(next-line-add-newlines nil)
 '(nix-buffer-directory-name "~/.emacs.d/data/nix-buffer" t)
 '(nix-indent-function (quote nix-indent-line))
 '(nov-save-place-file "~/.emacs.d/data/nov-places" t)
 '(ns-alternate-modifier (quote alt))
 '(ns-command-modifier (quote meta))
 '(ns-function-modifier (quote hyper))
 '(ns-right-alternate-modifier (quote alt))
 '(nsm-settings-file "/Users/johnw/.emacs.d/data/network-security.data")
 '(nxml-sexp-element-flag t)
 '(nxml-slash-auto-complete-flag t)
 '(olivetti-hide-mode-line t)
 '(ovpn-mode-base-directory "~/.config/openvpn")
 '(pabbrev-idle-timer-verbose nil)
 '(package-archives
   (quote
    (("gnu" . "https://elpa.gnu.org/packages/")
     ("MELPA" . "https://melpa.org/packages/")
     ("Marmalade" . "https://marmalade-repo.org/packages/"))))
 '(page-break-lines-modes
   (quote
    (emacs-lisp-mode compilation-mode outline-mode prog-mode haskell-mode)))
 '(parens-require-spaces t)
 '(password-store-password-length 24)
 '(pcomplete-compare-entries-function (quote file-newer-than-file-p))
 '(pdf-tools-handle-upgrades nil)
 '(persistent-scratch-autosave-interval 30)
 '(persistent-scratch-backup-directory "~/.cache/emacs/backups")
 '(persistent-scratch-file-name "~/.emacs.d/data/persistent-scratch" t)
 '(persistent-scratch-save-file "/Users/johnw/.emacs.d/data/persistent-scratch")
 '(phi-search-limit 100000)
 '(plantuml-jar-path "/run/current-system/sw/lib/plantuml.jar")
 '(powerline-default-separator (quote arrow))
 '(powerline-image-apple-rgb t)
 '(pp^L-^L-string "                                            ")
 '(projectile-cache-file "~/.emacs.d/data/projectile.cache")
 '(projectile-completion-system (quote ivy))
 '(projectile-enable-caching t)
 '(projectile-file-exists-local-cache-expire 300)
 '(projectile-globally-ignored-directories
   (quote
    (".idea" ".ensime_cache" ".eunit" ".git" ".hg" ".fslckout" "_FOSSIL_" ".bzr" "_darcs" ".tox" ".svn" ".stack-work" "dist" "\\`/nix/.+" ".*/\\..*")))
 '(projectile-globally-ignored-files (quote ("TAGS" "GPATH" "GRTAGS" "GTAGS" "ID")))
 '(projectile-ignored-project-function
   (lambda
     (path)
     (string-match "\\(:?\\`/\\(:?nix\\|tmp\\)\\|/\\.nix-profile\\)" path)))
 '(projectile-keymap-prefix "p")
 '(projectile-known-projects-file "~/.emacs.d/data/projectile-bookmarks.eld")
 '(projectile-other-file-alist
   (quote
    (("cpp" "h" "hpp" "ipp")
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
     ("exp" "nix"))))
 '(projectile-project-search-path (quote ("~/src")))
 '(projectile-sort-order (quote recentf))
 '(proof-auto-action-when-deactivating-scripting (quote retract))
 '(proof-autosend-enable nil)
 '(proof-electric-terminator-enable t)
 '(proof-fast-process-buffer nil)
 '(proof-script-fly-past-comments t)
 '(proof-shell-fiddle-frames nil)
 '(proof-splash-enable nil)
 '(proof-sticky-errors t)
 '(proof-tidy-response t)
 '(ps-font-size (quote (8 . 10)))
 '(ps-footer-font-size (quote (12 . 14)))
 '(ps-header-font-size (quote (12 . 14)))
 '(ps-header-title-font-size (quote (14 . 16)))
 '(ps-line-number-font-size 10)
 '(ps-print-color-p nil)
 '(purpose-preferred-prompt (quote vanilla))
 '(rdebug-many-windows nil)
 '(read-buffer-function (quote ido-read-buffer))
 '(recentf-auto-cleanup 60)
 '(recentf-exclude
   (quote
    ("~\\'" "\\`out\\'" "\\.log\\'" "^/[^/]*:" "\\.el\\.gz\\'")))
 '(recentf-max-saved-items 2000)
 '(recentf-save-file "~/.emacs.d/data/recentf")
 '(redisplay-dont-pause t t)
 '(reftex-plug-into-AUCTeX t)
 '(reftex-trust-label-prefix t)
 '(regex-tool-backend (quote perl))
 '(rng-schema-locating-files
   (quote
    ("schemas.xml" "~/src/schemas.xml" "~/.nix-profile/share/emacs/24.4/etc/schema/schemas.xml")))
 '(rtags-autostart-diagnostics t)
 '(rtags-completions-enabled t)
 '(rtags-display-result-backend (quote ivy))
 '(runner-init-file "~/.emacs.d/data/runner-conf.el" t)
 '(safe-local-eval-forms
   (quote
    ((add-hook
      (quote write-file-hooks)
      (quote time-stamp))
     (add-hook
      (quote write-file-functions)
      (quote time-stamp))
     (add-hook
      (quote before-save-hook)
      (quote time-stamp)
      nil t)
     (add-hook
      (quote before-save-hook)
      (quote delete-trailing-whitespace)
      nil t)
     (progn
       (let
           ((coq-root-directory
             (when buffer-file-name
               (locate-dominating-file buffer-file-name ".dir-locals.el")))
            (coq-project-find-file
             (and
              (boundp
               (quote coq-project-find-file))
              coq-project-find-file)))
         (set
          (make-local-variable
           (quote tags-file-name))
          (concat coq-root-directory "TAGS"))
         (setq camldebug-command-name
               (concat coq-root-directory "dev/ocamldebug-coq"))
         (unless coq-project-find-file
           (set
            (make-local-variable
             (quote compile-command))
            (concat "make -C " coq-root-directory))
           (set
            (make-local-variable
             (quote compilation-search-path))
            (cons coq-root-directory nil)))
         (when coq-project-find-file
           (setq default-directory coq-root-directory)))))))
 '(safe-local-variable-values
   (quote
    ((haskell-indent-spaces . 4)
     (haskell-indent-spaces . 2)
     (haskell-indentation-ifte-offset . 2)
     (haskell-indentation-layout-offset . 2)
     (haskell-indentation-left-offset . 2)
     (haskell-indentation-starter-offset . 2)
     (haskell-indentation-where-post-offset . 2)
     (haskell-indentation-where-pre-offset . 2)
     (after-save-hook check-parens quietly-read-abbrev-file))))
 '(sage-view-anti-aliasing-level 4)
 '(sage-view-margin (quote (20 . 20)))
 '(sage-view-scale 2.0)
 '(same-window-buffer-names
   (quote
    ("*eshell*" "*shell*" "*mail*" "*inferior-lisp*" "*ielm*" "*scheme*")))
 '(save-abbrevs (quote silently))
 '(save-interprogram-paste-before-kill t)
 '(save-kill-file-name "~/.emacs.d/data/kill-ring-saved.el" t)
 '(save-place-file "~/.emacs.d/data/places")
 '(savehist-additional-variables
   (quote
    (tablist-named-filter file-name-history sr-history-registry kmacro-ring compile-history)))
 '(savehist-autosave-interval 60)
 '(savehist-file "~/.emacs.d/data/history")
 '(savehist-ignored-variables (quote (load-history flyspell-auto-correct-ring kill-ring)))
 '(scroll-bar-mode nil)
 '(semanticdb-default-save-directory "~/.emacs.d/data/semanticdb" t)
 '(sendmail-program "msmtp")
 '(sentence-end-double-space nil)
 '(shackle-default-rule (quote (:select t)))
 '(shackle-rules
   (quote
    ((compilation-mode :select nil :size 0.6)
     ("\\`\\*Messages" :select t :align t :size 0.6)
     ("\\` \\*Lusty-Matches\\*" :regexp t :noselect t)
     ("\\`\\*fetch" :regexp t :size 0.25 :noselect t :align bottom)
     ("\\`\\*Flycheck" :regexp t :size 0.2 :noselect t :align bottom)
     ("\\`\\*?magit-diff" :regexp t :align bottom :noselect t)
     ("\\`\\*makey" :regexp t :align bottom :noselect t))))
 '(shell-toggle-launch-shell (quote shell))
 '(shm-auto-insert-bangs nil)
 '(shm-indent-spaces 4)
 '(shm-use-hdevtools t)
 '(shm-use-presentation-mode t)
 '(show-paren-delay 0)
 '(sky-color-clock-format "%-l:%M %p")
 '(slack-buffer-create-on-notify t)
 '(slack-completing-read-function (quote ivy-completing-read))
 '(slack-prefer-current-team t)
 '(slack-request-timeout 30)
 '(slime-kill-without-query-p t)
 '(slime-repl-history-file "~/.emacs.d/data/slime-history.eld" t)
 '(slime-startup-animation nil)
 '(smex-history-length 20)
 '(smex-save-file "~/.emacs.d/data/smex-items")
 '(sp-highlight-pair-overlay nil)
 '(sql-sqlite-program "sqlite3")
 '(sr-attributes-display-mask (quote (nil nil t nil nil nil)))
 '(sr-autoload-extensions nil)
 '(sr-confirm-kill-viewer nil)
 '(sr-kill-unused-buffers nil)
 '(sr-listing-switches "--time-style=locale --group-directories-first -alDhgG")
 '(sr-loop-use-popups nil)
 '(sr-popviewer-style (quote single-frame))
 '(sr-show-file-attributes nil)
 '(sr-traditional-other-window t)
 '(sr-use-commander-keys nil)
 '(ssl-certificate-verification-policy 1)
 '(svn-status-hide-unmodified t)
 '(swiper-stay-on-quit t)
 '(switch-to-buffer-preserve-window-point t)
 '(tab-always-indent (quote complete))
 '(tags-apropos-verbose t)
 '(tags-case-fold-search nil)
 '(tail-max-size 25)
 '(tail-volatile nil)
 '(temp-buffer-resize-mode t nil (help))
 '(term-bind-key-alist
   (quote
    (("C-c C-c" . term-interrupt-subjob)
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
     ("C-y" . term-paste))))
 '(term-buffer-maximum-size 0)
 '(term-scroll-show-maximum-output t)
 '(text-mode-hook
   (quote
    (turn-on-auto-fill
     (lambda nil
       (ignore-errors
         (diminish
          (quote auto-fill-function)))))))
 '(tls-checktrust t)
 '(tls-program
   (quote
    ("openssl s_client -connect %h:%p -no_ssl2 -ign_eof -CApath /etc/postfix/certs -cert ~/Messages/me.pem")))
 '(tool-bar-mode nil)
 '(tramp-default-method "ssh")
 '(trash-directory "~/.Trash")
 '(undo-limit 800000)
 '(undo-tree-history-directory-alist (quote ((".*" . "~/.cache/emacs/backups"))))
 '(undo-tree-mode-lighter "")
 '(undo-tree-visualizer-timestamps t)
 '(uniquify-buffer-name-style (quote post-forward-angle-brackets) nil (uniquify))
 '(url-cache-directory "~/.emacs.d/data/url/cache")
 '(url-configuration-directory "~/.emacs.d/data/url/")
 '(url-irc-function (quote url-irc-erc))
 '(use-package-enable-imenu-support t)
 '(user-full-name "John Wiegley")
 '(user-initials "jww")
 '(user-mail-address "johnw@newartisans.com")
 '(vc-command-messages t)
 '(vc-follow-symlinks t)
 '(vc-git-diff-switches (quote ("-w" "-U3")))
 '(vc-handled-backends (quote (GIT SVN CVS Bzr Hg)))
 '(vc-make-backup-files t)
 '(version-control t)
 '(visible-bell t)
 '(w3m-cookie-accept-bad-cookies (quote ask))
 '(w3m-default-display-inline-images t)
 '(w3m-fill-column 100)
 '(w3m-use-cookies t)
 '(warning-minimum-log-level :error)
 '(wdired-use-dired-vertical-movement (quote sometimes))
 '(weblogger-config-alist
   (quote
    (("newartisans" "http://www.newartisans.com/xmlrpc.php" "johnw" "" "5"))))
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
 '(whitespace-style (quote (face trailing lines-tail space-before-tab)))
 '(window-divider-default-bottom-width 1)
 '(window-divider-default-places (quote bottom-only))
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
 '(yas-prompt-functions
   (quote
    (yas-ido-prompt yas-completing-prompt yas-no-prompt)))
 '(yas-snippet-dirs (quote ("/Users/johnw/.emacs.d/snippets")))
 '(yas-triggers-in-field t)
 '(yas-wrap-around-region t)
 '(z3-solver-cmd "z3")
 '(zencoding-indentation 2)
 '(zencoding-preview-default nil)
 '(zoom-size (quote size-callback)))

(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(company-coq-features/code-folding-bullet-face ((t (:weight bold))))
 '(coq-symbol-face ((t (:inherit default-face))))
 '(cursor ((t (:background "#8D0CFF"))))
 '(diff-added ((((background dark)) (:foreground "#FFFF9B9BFFFF")) (t (:foreground "DarkGreen"))))
 '(diff-changed ((((background dark)) (:foreground "Yellow")) (t (:foreground "MediumBlue"))))
 '(diff-context ((((background dark)) (:foreground "White")) (t (:foreground "Black"))))
 '(diff-file-header ((((background dark)) (:foreground "Cyan" :background "Black")) (t (:foreground "Red" :background "White"))))
 '(diff-header ((((background dark)) (:foreground "Cyan")) (t (:foreground "Red"))))
 '(diff-index ((((background dark)) (:foreground "Magenta")) (t (:foreground "Green"))))
 '(diff-nonexistent ((((background dark)) (:foreground "#FFFFFFFF7474")) (t (:foreground "DarkBlue"))))
 '(font-lock-comment-face ((t (:foreground "grey50" :slant italic))))
 '(font-lock-doc-face ((t (:foreground "cornflowerblue"))))
 '(highlight ((t (:background "blue4"))))
 '(markdown-header-face-1 ((t (:inherit markdown-header-face :height 2.0))))
 '(markdown-header-face-2 ((t (:inherit markdown-header-face :height 1.6))))
 '(markdown-header-face-3 ((t (:inherit markdown-header-face :height 1.4))))
 '(markdown-header-face-4 ((t (:inherit markdown-header-face :height 1.2))))
 '(minibuffer-prompt ((t (:foreground "grey80"))))
 '(mode-line-inactive ((t (:background "grey95"))))
 '(proof-locked-face ((t (:background "#180526"))))
 '(proof-queue-face ((t (:background "#431807"))))
 '(proof-script-sticky-error-face ((t (:background "#50110e"))))
 '(proof-warning-face ((t (:background "orange4"))))
 '(variable-pitch ((t (:height 1.2 :family "Bookerly"))))
 '(whitespace-line ((t (:background "yellow"))))
 '(yas-field-highlight-face ((t (:background "#e4edfc")))))
