(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(check-mail-boxes (quote ("~/Messages/incoming/mail\\..*\\.spool")))
 '(check-mail-summary-function (quote check-mail-box-summary))
 '(gnus-activate-level 2)
 '(gnus-after-getting-new-news-hook
   (quote
    (gnus-group-list-groups gnus-group-save-newsrc gnus-display-time-event-handler)))
 '(gnus-agent-expire-all t)
 '(gnus-agent-expire-days 14)
 '(gnus-agent-go-online t)
 '(gnus-agent-mark-unread-after-downloaded nil)
 '(gnus-agent-synchronize-flags t)
 '(gnus-alias-allow-forward-as-reply t)
 '(gnus-alias-default-identity "NewArtisans")
 '(gnus-alias-identity-alist
   (quote
    ((#("Gnu" 0 1
        (idx 4))
      "" "\"John Wiegley\" <johnw@gnu.org>" "" nil "" "John Wiegley                  GPG fingerprint = 4710 CF98 AF9B 327B B80F\nhttp://newartisans.com                          60E1 46C4 BD1A 7AC1 4BA2")
     (#("Gmail" 0 1
        (idx 3))
      "" "\"John Wiegley\" <jwiegley@gmail.com>" "" nil "" "")
     (#("ATC" 0 1
        (idx 0))
      "" "\"ATC of Yolo Cluster\" <atcyolocluster@gmail.com>" ""
      (("BCC" . "sarv9mithaq@gmail.com, jwiegley@gmail.com"))
      "" "John Wiegley\nATC Secretary")
     (#("NewArtisans" 0 1
        (idx 5))
      "" "\"John Wiegley\" <johnw@newartisans.com>" "New Artisans LLC" nil "" "John Wiegley                  GPG fingerprint = 4710 CF98 AF9B 327B B80F\nhttp://newartisans.com                          60E1 46C4 BD1A 7AC1 4BA2")
     (#("DFINITY" 0 1
        (idx 2))
      "" "\"John Wiegley\" <john@dfinity.org>" "DFINITY LLC" nil "" "John Wiegley\nSr. Researcher & Engineer, DFINITY")
     (#("BAE" 0 1
        (idx 1))
      "" "\"John Wiegley\" <john.wiegley@baesystems.com>" "BAE Systems" nil "" "John Wiegley\nBAE Systems"))))
 '(gnus-alias-identity-rules
   (quote
    (("Ledger Mailing List"
      ("To" "ledger-cli@googlegroups\\.com" current)
      "Gmail")
     ("Emacs Mailing Lists"
      ("Cc" "\\(emacs\\|debbugs\\)" current)
      "Gnu")
     ("Emacs Mailing Lists"
      ("To" "\\(emacs\\|debbugs\\)" current)
      "Gnu")
     ("Emacs Newsgroups"
      ("Newsgroups" "emacs" current)
      "Gnu")
     ("Haskell Groups"
      ("Newsgroups" "\\(haskell\\|ghc\\|nix\\|coq\\|acl2\\|idris\\|agda\\|ssreflect\\|risc-v\\)" current)
      "NewArtisans")
     ("Haskell Mailing Lists"
      ("To" "\\(haskell\\|ghc\\|nix\\|coq\\|acl2\\|idris\\|agda\\|ssreflect\\|risc-v\\)" current)
      "NewArtisans")
     ("DFINITY"
      ("To" "\\(dfinity\\)" current)
      "DFINITY"))))
 '(gnus-alias-override-user-mail-address t)
 '(gnus-alias-unknown-identity-rule (quote error))
 '(gnus-always-read-dribble-file t)
 '(gnus-article-date-lapsed-new-header t)
 '(gnus-article-update-date-headers nil)
 '(gnus-asynchronous t)
 '(gnus-check-new-newsgroups nil)
 '(gnus-completing-read-function (quote gnus-ido-completing-read))
 '(gnus-default-adaptive-score-alist
   (quote
    ((gnus-saved-mark
      (subject 250)
      (from 50))
     (gnus-dormant-mark
      (subject 150)
      (from 50))
     (gnus-forwarded-mark
      (subject 100)
      (from 25))
     (gnus-replied-mark
      (subject 75)
      (from 15))
     (gnus-ticked-mark
      (subject 0)
      (from 0))
     (gnus-read-mark
      (subject 30)
      (from 5))
     (gnus-del-mark
      (subject 5)
      (from 0))
     (gnus-recent-mark
      (subject 0)
      (from 0))
     (gnus-killed-mark
      (subject -5)
      (from -5))
     (gnus-catchup-mark
      (subject -150)
      (from 0))
     (gnus-duplicate-mark
      (subject -150)
      (from 0))
     (gnus-expirable-mark
      (subject -250)
      (from 0))
     (gnus-spam-mark
      (subject -10)
      (from -150)))))
 '(gnus-default-article-saver (quote gnus-summary-save-in-mail))
 '(gnus-gcc-mark-as-read t)
 '(gnus-generate-tree-function (quote gnus-generate-horizontal-tree))
 '(gnus-group-default-list-level 2)
 '(gnus-group-line-format "%S%p%P%M%5y: %(%B%G%B%)\n")
 '(gnus-group-mode-hook (quote (gnus-topic-mode gnus-agent-mode hl-line-mode)))
 '(gnus-group-use-permanent-levels t)
 '(gnus-harvest-sender-alist (quote ((".*@gnu\\.org" . johnw@gnu\.org))))
 '(gnus-home-directory "~/Messages/Gnus/")
 '(gnus-ignored-from-addresses
   "\\(johnw\\|jwiegley\\)\\(-[^@]+\\)?@\\(gnu\\.org\\|\\(forumjobs\\|3dex\\|gmail\\|hotmail\\|newartisans\\|fpcomplete\\|boostpro\\)\\.com\\|public\\.gmane\\.org\\)")
 '(gnus-ignored-mime-types
   (quote
    ("application/x-pkcs7-signature" "application/ms-tnef" "text/x-vcard")))
 '(gnus-interactive-exit (quote quiet))
 '(gnus-large-newsgroup 4000)
 '(gnus-local-domain "newartisans.com")
 '(gnus-mailing-list-groups "\\`\\(list\\|wg21\\)\\.")
 '(gnus-mark-unpicked-articles-as-read t)
 '(gnus-message-archive-group (quote ((format-time-string "sent.%Y"))))
 '(gnus-message-replysign t)
 '(gnus-novice-user nil)
 '(gnus-parameters
   (quote
    (("brass\\.smedl"
      (list-identifier . "\\[brass-rings/smedl\\]"))
     ("^haskell$"
      (display . all))
     ("list\\.gnu\\.prog\\.discuss$"
      (list-identifier . "\\[gnu-prog-discuss\\]"))
     ("list\\.riscv\\.devel$"
      (to-address . "sw-dev@lists.riscv.org")
      (to-list . "sw-dev@lists.riscv.org")
      (list-identifier . "\\[\\(riscv-sw\\|sw-dev\\)\\]"))
     ("list\\.coq\\.fiat"
      (to-address . "fiat@lists.csail.mit.edu")
      (to-list . "fiat@lists.csail.mit.edu")
      (list-identifier . "\\[Fiat\\]"))
     ("list\\.gsoc\\.mentors$"
      (to-address . "google-summer-of-code-mentors-list@googlegroups.com")
      (to-list . "google-summer-of-code-mentors-list@googlegroups.com")
      (list-identifier . "\\[GSoC Mentors\\]"))
     ("list\\.haskell\\.ghc$"
      (to-address . "glasgow-haskell-users@haskell.org")
      (to-list . "glasgow-haskell-users@haskell.org")
      (list-identifier . "\\[Haskell\\]"))
     ("list\\.haskell\\.ghc-linker"
      (to-address . "ghc-linker@googlegroups.com")
      (to-list . "ghc-linker@googlegroups.com"))
     ("list\\.nix\\.devel"
      (to-address . "nix-dev@lists.science.uu.nl")
      (to-list . "nix-dev@lists.science.uu.nl")
      (list-identifier . "\\[Nix-dev\\]"))
     ("\\`gmane\\."
      (spam-process gnus-group-spam-exit-processor-report-gmane))
     ("list\\.github$"
      (total-expire . t)
      (expiry-wait . 14)
      (expiry-target . delete))
     ("mail\\.spam"
      (total-expire . t)
      (expiry-wait . 28)
      (expiry-target . delete)
      (ham-process-destination . "INBOX")
      (spam-contents gnus-group-spam-classification-spam)
      (spam-process
       ((spam spam-use-spamassassin)
        (ham spam-use-spamassassin))))
     ("list\\."
      (subscribed . t)
      (gcc-self . t))
     ("list\\.wg21\\.\\(.*\\)"
      (to-address . "c++std-\\1@accu.org")
      (to-list . "c++std-\\1@accu.org")
      (gcc-self . t)
      (gnus-list-identifiers "\\[c\\+\\+std-.+?\\]"))
     ("INBOX"
      (total-expire . t)
      (expiry-wait . 14)
      (expiry-target . "mail.archive")
      (spam-process-destination . "mail.spam")
      (spam-contents gnus-group-spam-classification-ham)
      (spam-process
       ((spam spam-use-spamassassin)
        (ham spam-use-spamassassin))))
     ("\\(mail\\.\\|INBOX\\)"
      (gnus-use-scoring nil))
     ("mail\\.archive"
      (gnus-summary-line-format "%«%U%R %uS %ur %»%(%*%-14,14f   %4u&size; %1«%B%s%»%)\n")
      (gnus-show-threads nil))
     ("list\\.ledger\\.devel"
      (to-address . "ledger-cli@googlegroups.com")
      (to-list . "ledger-cli@googlegroups.com")
      (gcc-self . t))
     ("list\\.bahai\\.tarjuman"
      (to-address . "tarjuman@bahai-library.com")
      (to-list . "tarjuman@bahai-library.com")
      (list-identifier . "\\[tj\\]"))
     ("list\\.emacs\\.devel$"
      (to-address . "emacs-devel@gnu.org")
      (to-list . "emacs-devel@gnu.org"))
     ("list\\.emacs\\.tangents$"
      (to-address . "emacs-tangents@gnu.org")
      (to-list . "emacs-tangents@gnu.org"))
     ("list\\.emacs\\.help$"
      (to-address . "help-gnu-emacs@gnu.org")
      (to-list . "help-gnu-emacs@gnu.org"))
     ("list\\.emacs\\.bugs$"
      (to-list . "bug-gnu-emacs@gnu.org"))
     ("list\\.emacs\\.bugs\\.tracker"
      (list-identifier . "\\[debbugs-tracker\\]"))
     ("list\\.emacs\\.diffs"
      (to-address . "emacs-diffs@gnu.org")
      (to-list . "emacs-diffs@gnu.org")
      (list-identifier . "\\[Emacs-diffs\\]"))
     ("list\\.emacs\\.elpa\\.diffs"
      (to-address . "emacs-elpa-diffs@gnu.org")
      (to-list . "emacs-elpa-diffs@gnu.org")
      (list-identifier . "\\[elpa\\]"))
     ("list\\.emacs\\.buildstatus"
      (to-address . "emacs-buildstatus@gnu.org")
      (to-list . "emacs-buildstatus@gnu.org"))
     ("list\\.emacs\\.sources"
      (to-address . "gnu-emacs-sources@gnu.org")
      (to-list . "gnu-emacs-sources@gnu.org"))
     ("list\\.emacs\\.orgmode"
      (to-address . "emacs-orgmode@gnu.org")
      (to-list . "emacs-orgmode@gnu.org")
      (list-identifier . "\\[O\\]"))
     ("list\\.boost\\.cppnow"
      (to-address . "boostcon-plan@googlegroups.com")
      (to-list . "boostcon-plan@googlegroups.com"))
     ("list\\.boost\\.ryppl"
      (list-identifier . "\\[ryppl-dev\\]")
      (to-address . "ryppl-dev@googlegroups.com")
      (to-list . "ryppl-dev@googlegroups.com"))
     ("list\\.boost\\.devel"
      (to-address . "boost@lists.boost.org")
      (to-list . "boost@lists.boost.org")
      (list-identifier . "\\[boost\\]"))
     ("list\\.boost\\.\\(users\\|announce\\)"
      (to-address . "boost-\\1@lists.boost.org")
      (to-list . "boost-\\1@lists.boost.org")
      (list-identifier . "\\\\[Boost-\\1\\\\]"))
     ("list\\.isocpp\\.\\(proposals\\|discussion\\)"
      (to-address . "std-\\1@isocpp.org")
      (to-list . "std-\\1@isocpp.org")
      (list-identifier . "\\\\[\\\\(lang\\\\|lib\\\\|std\\\\)-\\1\\\\]"))
     ("list\\.clang\\.devel"
      (to-address . "cfe-dev@cs.uiuc.edu")
      (to-list . "cfe-dev@cs.uiuc.edu")
      (list-identifier . "\\[\\(cfe-dev\\|LLVMdev\\)\\]"))
     ("list\\.llvm\\.devel"
      (to-address . "llvmdev@cs.uiuc.edu")
      (to-list . "llvmdev@cs.uiuc.edu")
      (list-identifier . "\\[\\(cfe-dev\\|LLVMdev\\)]"))
     ("list\\.nix\\.devel"
      (to-address . "nix-dev@lists.science.uu.nl")
      (to-list . "nix-dev@lists.science.uu.nl")
      (list-identifier . "\\[Nix-dev\\]"))
     ("list\\.haskell\\.pipes"
      (to-address . "haskell-pipes@googlegroups.com")
      (to-list . "haskell-pipes@googlegroups.com")
      (list-identifier . "\\[haskell-pipes\\]"))
     ("list\\.haskell\\.cafe"
      (to-address . "haskell-cafe@haskell.org")
      (to-list . "haskell-cafe@haskell.org")
      (list-identifier . "\\[Haskell\\(-cafe\\)?\\]"))
     ("list\\.haskell\\.libraries"
      (to-address . "libraries@haskell.org")
      (to-list . "libraries@haskell.org")
      (expiry-target . "archive.haskell.libraries"))
     ("list\\.haskell\\.prime"
      (to-address . "haskell-prime@haskell.org")
      (to-list . "haskell-prime@haskell.org")
      (list-identifier . "\\[haskell/rfcs\\]"))
     ("list\\.haskell\\.template-haskell"
      (to-address . "template-haskell@haskell.org")
      (to-list . "template-haskell@haskell.org"))
     ("list\\.haskell\\.beginners"
      (to-address . "beginners@haskell.org")
      (to-list . "beginners@haskell.org")
      (list-identifier . "\\[Haskell-beginners\\]"))
     ("list\\.haskell\\.infrastructure"
      (to-address . "haskell-infrastructure@community.galois.com")
      (to-list . "haskell-infrastructure@community.galois.com")
      (list-identifier . "\\[Haskell-infrastructure\\]"))
     ("list\\.haskell\\.community"
      (to-address . "haskell-community@haskell.org")
      (to-list . "haskell-community@haskell.org")
      (list-identifier . "\\[Haskell-\\(community\\|cafe\\)\\]"))
     ("list\\.haskell\\.announce"
      (to-address . "haskell@haskell.org")
      (to-list . "haskell@haskell.org")
      (list-identifier . "\\[Haskell\\]"))
     ("list\\.haskell\\.cabal"
      (to-address . "cabal-devel@haskell.org")
      (to-list . "cabal-devel@haskell.org")
      (list-identifier . "\\[Haskell\\]"))
     ("list\\.coq$"
      (to-address . "coq-club@inria.fr")
      (to-list . "coq-club@inria.fr")
      (list-identifier . "\\[Coq-Club\\]"))
     ("list\\.coq\\.devel$"
      (to-address . "coqdev@inria.fr")
      (to-list . "coqdev@inria.fr")
      (list-identifier . "\\[coqdev\\]"))
     ("list\\.agda\\.devel$"
      (to-address . "agda@lists.chalmers.se")
      (to-list . "agda@lists.chalmers.se")
      (list-identifier . "\\[Agda\\]"))
     ("list\\.idris\\.devel$"
      (to-address . "idris-lang@googlegroups.com")
      (to-list . "idris-lang@googlegroups.com")
      (list-identifier . "\\[Idris\\]"))
     ("list\\.safe\\.verify$"
      (to-address . "safe-verif@lists.crash-safe.org")
      (to-list . "safe-verif@lists.crash-safe.org")
      (list-identifier . "\\[Safe-verif\\]"))
     ("list\\.coq\\.ssreflect"
      (to-address . "ssreflect@msr-inria.inria.fr")
      (to-list . "ssreflect@msr-inria.inria.fr")
      (list-identifier . "\\[ssreflect\\]"))
     ("list\\.brass\\.proposal"
      (to-address . "brass-proposal@lists.brass-tacks.org")
      (to-list . "brass-proposal@lists.brass-tacks.org")
      (list-identifier . "\\[Brass-proposal\\]"))
     ("list\\.brass\\.commits"
      (to-address . "bae-brass-commits@googlegroups.com")
      (to-list . "bae-brass-commits@googlegroups.com")
      (list-identifier . "\\[bae-brass-commits\\]\\( \\[bae-brass/brass-proposal\\]\\)? [0-9a-f]+?:"))
     ("list\\.brass\\.rings$"
      (list-identifier . "\\[rings-all\\]")
      (to-address . "rings-all@googlegroups.com")
      (to-list . "rings-all@googlegroups.com"))
     ("list\\.brass\\.smedl$"
      (list-identifier . "\\[smedl\\]"))
     ("list\\.hott"
      (to-address . "hott-cafe@googlegroups.com")
      (to-list . "hott-cafe@googlegroups.com")
      (list-identifier . "\\[hott-cafe\\]"))
     ("list\\.acl2\\.help"
      (to-address . "acl2-help@utlists.utexas.edu")
      (to-list . "acl2-help@utlists.utexas.edu")))))
 '(gnus-permanently-visible-groups "INBOX")
 '(gnus-read-active-file nil)
 '(gnus-read-newsrc-file nil)
 '(gnus-refer-article-method
   (quote
    (current
     (nnir "nnimap:Local")
     (nntp "LocalNews"
           (nntp-address "localhost")
           (nntp-port-number 9119))
     (nntp "Gmane"
           (nntp-address "news.gmane.org"))
     (nntp "Eternal September"
           (nntp-address "news.eternal-september.org")
           (nntp-authinfo-user "jwiegley")))))
 '(gnus-registry-ignored-groups (quote (("nntp" t) ("^INBOX" t))))
 '(gnus-save-killed-list nil)
 '(gnus-save-newsrc-file nil)
 '(gnus-score-default-duration (quote p))
 '(gnus-score-expiry-days 30)
 '(gnus-score-interactive-default-score 10)
 '(gnus-select-group-hook (quote (gnus-group-set-timestamp)))
 '(gnus-select-method
   (quote
    (nnimap "Local"
            (nnimap-stream plain)
            (nnimap-address "127.0.0.1")
            (nnimap-server-port 9143))))
 '(gnus-sieve-file "~/Messages/dovecot.sieve")
 '(gnus-sieve-select-method "nnimap:Local")
 '(gnus-signature-separator (quote ("^-- $" "^-- *$" "^_____+$")))
 '(gnus-simplify-subject-functions (quote (gnus-simplify-subject-fuzzy)))
 '(gnus-split-methods
   (quote
    ((gnus-save-site-lisp-file)
     (gnus-article-archive-name)
     (gnus-article-nndoc-name))))
 '(gnus-started-hook
   (quote
    ((lambda nil
       (run-hooks
        (quote gnus-after-getting-new-news-hook))))))
 '(gnus-subscribe-newsgroup-method (quote gnus-subscribe-topics))
 '(gnus-sum-thread-tree-single-indent "  ")
 '(gnus-summary-expunge-below -100)
 '(gnus-summary-line-format "%«%3t %U%R %uS %ur %»%(%*%-14,14f   %1«%B%s%»%)\n")
 '(gnus-summary-mark-below -100)
 '(gnus-summary-pick-line-format "%U%R %uS %ur %(%*%-14,14f  %B%s%)\n")
 '(gnus-summary-prepared-hook (quote (gnus-summary-hide-all-threads)))
 '(gnus-summary-save-parts-default-mime ".*")
 '(gnus-suppress-duplicates t)
 '(gnus-suspend-gnus-hook (quote (gnus-group-save-newsrc)))
 '(gnus-thread-expunge-below -1000)
 '(gnus-thread-hide-subtree t)
 '(gnus-thread-ignore-subject nil)
 '(gnus-thread-score-function (quote max))
 '(gnus-thread-sort-functions (quote ((not gnus-thread-sort-by-number))))
 '(gnus-topic-display-empty-topics nil)
 '(gnus-topic-line-format "%i[ %A: %(%{%n%}%) ]%v\n")
 '(gnus-treat-date-lapsed (quote head))
 '(gnus-treat-hide-citation-maybe t)
 '(gnus-treat-strip-cr t)
 '(gnus-treat-strip-leading-blank-lines t)
 '(gnus-treat-strip-multiple-blank-lines t)
 '(gnus-treat-strip-trailing-blank-lines t)
 '(gnus-treat-unsplit-urls t)
 '(gnus-tree-minimize-window nil)
 '(gnus-uncacheable-groups "^nnml")
 '(gnus-use-adaptive-scoring (quote (line)))
 '(gnus-use-cache t)
 '(gnus-verbose 4)
 '(mail-envelope-from (quote header))
 '(mail-host-address "newartisans.com")
 '(mail-personal-alias-file "~/Documents/mailrc")
 '(mail-self-blind t)
 '(mail-setup-with-from nil)
 '(mail-source-delete-incoming t)
 '(mail-source-delete-old-incoming-confirm nil)
 '(mail-source-report-new-mail-interval 15)
 '(mail-sources (quote ((file :path "/var/mail/johnw"))))
 '(mail-specify-envelope-from t)
 '(mail-user-agent (quote gnus-user-agent))
 '(message-alternative-emails
   "\\(johnw?\\|jwiegley\\)@\\(\\(gmail\\|newartisans\\|fpcomplete\\|boostpro\\|yahoo\\|hotmail\\)\\.com\\|gnu\\.org\\)")
 '(message-directory "~/Messages/Gnus/Mail/")
 '(message-dont-reply-to-names
   "\\(jwiegley\\|johnw\\|john\\.wiegley\\)@\\(\\(gmail\\|newartisans\\|baesystems\\)\\.com\\|gnu\\.org\\)")
 '(message-fill-column 78)
 '(message-interactive t)
 '(message-mail-alias-type nil)
 '(message-mode-hook
   (quote
    (abbrev-mode footnote-mode turn-on-auto-fill turn-on-flyspell
                 (lambda nil
                   (set-fill-column 78))
                 turn-on-orgstruct++ turn-on-orgtbl)))
 '(message-send-mail-function (quote message-send-mail-with-sendmail))
 '(message-send-mail-partially-limit nil)
 '(message-sendmail-envelope-from (quote header))
 '(message-sendmail-extra-arguments
   (quote
    ("--read-envelope-from" "--file=/Users/johnw/.config/msmtp" "--account=fastmail")))
 '(message-sendmail-f-is-evil t)
 '(message-sent-hook (quote (my-gnus-score-followup)))
 '(message-setup-hook (quote (gnus-harvest-set-from message-check-recipients)))
 '(message-signature-separator "^-- *$")
 '(message-subscribed-address-functions (quote (gnus-find-subscribed-addresses)))
 '(message-x-completion-alist
   (quote
    (("\\([rR]esent-\\|[rR]eply-\\)?[tT]o:\\|[bB]?[cC][cC]:" . gnus-harvest-find-address)
     ((if
          (boundp
           (quote message-newgroups-header-regexp))
          message-newgroups-header-regexp message-newsgroups-header-regexp)
      . message-expand-group))))
 '(mm-attachment-override-types
   (quote
    ("text/x-vcard" "application/pkcs7-mime" "application/x-pkcs7-mime" "application/pkcs7-signature" "application/x-pkcs7-signature" "image/.*")))
 '(mm-decrypt-option (quote always))
 '(mm-discouraged-alternatives (quote ("application/msword" "text/richtext")))
 '(mm-inline-text-html-with-images t)
 '(mm-text-html-renderer (quote gnus-w3m))
 '(mm-verify-option (quote always))
 '(mm-w3m-safe-url-regexp nil)
 '(nnir-imap-default-search-key "imap")
 '(nnmail-crosspost nil)
 '(nnmail-expiry-wait 30)
 '(nnmail-extra-headers (quote (To Cc Newsgroups)))
 '(nnmail-scan-directory-mail-source-once t)
 '(sc-citation-leader "")
 '(sc-confirm-always-p nil)
 '(sc-default-attribution "")
 '(sc-default-cite-frame
   (quote
    ((begin
      (progn
        (sc-fill-if-different)
        (setq sc-tmp-nested-regexp
              (sc-cite-regexp "")
              sc-tmp-nonnested-regexp
              (sc-cite-regexp)
              sc-tmp-dumb-regexp
              (concat "\\("
                      (sc-cite-regexp "")
                      "\\)"
                      (sc-cite-regexp sc-citation-nonnested-root-regexp)))))
     ("^[       ]*$"
      (if sc-cite-blank-lines-p
          (sc-cite-line)
        (sc-fill-if-different "")))
     ((and
       (looking-at "^-- ?$")
       (not
        (save-excursion
          (goto-char
           (match-end 0))
          (re-search-forward "^-- ?$" nil t))))
      (sc-fill-if-different ""))
     (sc-reference-tag-string
      (if
          (string= sc-reference-tag-string "")
          (list
           (quote continue))
        nil))
     (sc-tmp-dumb-regexp
      (sc-cite-coerce-dumb-citer))
     (sc-tmp-nested-regexp
      (sc-add-citation-level))
     (sc-tmp-nonnested-regexp
      (sc-cite-coerce-cited-line))
     (sc-nested-citation-p
      (sc-add-citation-level))
     (t
      (sc-cite-line))
     (end
      (sc-fill-if-different "")))))
 '(sc-preferred-attribution-list (quote ("initials")))
 '(sc-use-only-preference-p t)
 '(send-mail-function (quote sendmail-send-it))
 '(smtpmail-default-smtp-server "smtp.gmail.com")
 '(smtpmail-queue-dir "~/Messages/Gnus/Mail/queue/")
 '(smtpmail-smtp-server "smtp.fastmail.com")
 '(smtpmail-smtp-service 587)
 '(smtpmail-smtp-user "johnw@newartisans.com")
 '(smtpmail-starttls-credentials
   (quote
    (("mail.johnwiegley.com" 587 nil nil)
     ("smtp.fastmail.com" 587 nil nil)
     ("smtp.gmail.com" 587 nil nil))))
 '(smtpmail-stream-type (quote ssl))
 '(spam-assassin-program "/opt/local/bin/spamc-5.12")
 '(spam-report-gmane-use-article-number nil)
 '(spam-sa-learn-program "/opt/local/bin/sa-learn-5.12")
 '(spam-use-regex-headers t)
 '(spam-use-spamassassin t))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(gnus-summary-normal-ticked ((t (:foreground "pink4"))))
 '(message-cited-text ((((class color)) (:foreground "Blue"))))
 '(message-header-cc ((((class color)) (:bold t :foreground "green2"))))
 '(message-header-name ((((class color)) (:bold nil :foreground "Blue"))))
 '(message-header-other ((((class color)) (:foreground "Firebrick"))))
 '(message-header-xheader ((((class color)) (:foreground "Blue"))))
 '(message-mml ((((class color)) (:foreground "DarkGreen"))))
 '(message-separator ((((class color)) (:foreground "Tan")))))
