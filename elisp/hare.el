;; hare.el --- Top level of HaRe package, loads all subparts

;; Note: based on
;; https://github.com/RefactoringTools/wrangler/blob/master/elisp/wrangler.el.src

;; Put the following code to your "~/.emacs".
;;
;; (add-to-list 'load-path
;;     "~/.cabal/share/HaRe-0.7.0.0/elisp")
;; (require 'hare)
;;
;; (autoload 'hare-init "hare" nil t)
;; (add-hook 'haskell-mode-hook (lambda () (hare-init)))
;;   Note: hare-init in addition to your normal haskell-mode hooks


;; Prerequisites

;; (require 'vc-hooks)
;; (require 'wrangler-clearcase-hooks)
;; (require 'vc)
;; (require 'erlang)
;; (require 'distel)
(require 'read-char-spec)

(if (eq (substring emacs-version 0 4) "22.2")
    (require 'ediff-init1)
  (require 'ediff-init))

(defgroup hare nil
  "HaRe options.")

(defcustom hare-search-paths (cons (expand-file-name ".") nil )
        "List of directories to search for .hs and .lhs files to refactor."
        :type '(repeat directory)
        :group 'hare)

(defcustom ghc-hare-command "ghc-hare"
     "The command name of \"ghc-hare\""
     :type 'string
     :group 'hare)

;; (defcustom version-control-system 'none
;;   "* FOR CASESTUDY USE ONLY.* Version control system used for storing casestudy results."
;;   :type '(choice
;;        (const none)
;;        (const ClearCase)
;;        (const Git)
;;        (const SVN))
;;   :group 'wrangler)

;; (defcustom dirs-to-monitor nil
;;   "*FOR CASESTUDY USE ONLY.* List of directories to be monitored by Wrangler to log refactoring activities."
;;   :type '(repeat directory)
;;   :group 'wrangler)


;; (defcustom refactor-log-file ""
;;   "*FOR CASESTUDY WITH ClearCase ONLY.* Path and name of the refactoring log file."
;;   :type '(file :must-match t)
;;   :group 'wrangler)


;; (defcustom refac-monitor-repository-path ""
;;   "*FOR CASESTUDY WITH Git/SVN ONLY.* Path to the Wrangler monitor reposiotry"
;;   :type 'directory
;;   :group 'wrangler)

;; (defcustom log-source-code nil
;;   "*FOR CASESTUDY USE ONLY* 'off' means to log the refactoring commands; 'on' means
;;   to log both refactoring commands and source code."
;;   :type 'boolean
;;   :group 'wrangler)

(defun hare-customize ()
  "Customization of group `hare' for the Haskell Refactorer."
  (interactive)
  (customize-group 'hare))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This initialization section based on ghc-mod one

(defvar hare-initialized nil)

;;;###autoload
(defun hare-init ()
  (unless hare-initialized
    (define-key haskell-mode-map "\C-c\C-rdm"  'hare-refactor-demote)
    (define-key haskell-mode-map "\C-c\C-rdd"  'hare-refactor-dupdef)
    (define-key haskell-mode-map "\C-c\C-ric"  'hare-refactor-iftocase)
    (define-key haskell-mode-map "\C-c\C-rlo"  'hare-refactor-lift-one)
    (define-key haskell-mode-map "\C-c\C-rlt"  'hare-refactor-lifttotop)
    (define-key haskell-mode-map "\C-c\C-rr"   'hare-refactor-rename)
    (define-key haskell-mode-map "\C-c\C-rsh"  'hare-refactor-show)
    (hare-init-menu)
    (setq hare-initialized t)))

(provide 'hare)

(defun hare-init-menu()
  ;; Creating a new menu pane in the menu bar to the right of “Tools” menu
  (define-key-after
    haskell-mode-map
    [menu-bar mymenu]
    (cons "Refactorer" (make-sparse-keymap "HaRe"))
    'tools )

  ;; Creating a menu item, under the menu by the id “[menu-bar mymenu]”
  (define-key haskell-mode-map [menu-bar mymenu dm] '("Demote Definition"    . hare-refactor-demote))
  (define-key haskell-mode-map [menu-bar mymenu dd] '("Duplicate Definition" . hare-refactor-dupdef))
  (define-key haskell-mode-map [menu-bar mymenu ic] '("Convert if to case"   . hare-refactor-iftocase))
  (define-key haskell-mode-map [menu-bar mymenu lo] '("Lift one level"       . hare-refactor-lift-one))
  (define-key haskell-mode-map [menu-bar mymenu lt] '("Lift to top level"    . hare-refactor-lifttotop))
  (define-key haskell-mode-map [menu-bar mymenu r ] '("Rename"               . hare-refactor-rename))
  (define-key haskell-mode-map [menu-bar mymenu sh ] '("Show"                 . hare-refactor-show))
)

(defun hare-init-interactive ()
  (interactive)
  (hare-init)
  (hare-init-menu)
  )

(defconst erlang-xemacs-p (string-match "Lucid\\|XEmacs" emacs-version)
  "Non-nil when running under XEmacs or Lucid Emacs.")


(defun hare-menu-remove()
  (interactive)
;; code to remove the whole menu panel
;; (global-unset-key [menu-bar mymenu])
  (global-unset-key [menu-bar mymenu])
  (local-unset-key [menu-bar mymenu])
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; (require 'erl)
;; (require 'erl-service)

;; Compatibility with XEmacs
(unless (fboundp 'define-minor-mode)
  (defalias 'define-minor-mode 'easy-mmode-define-minor-mode))

(setq kill-buffer-query-functions
      (remove 'process-kill-buffer-query-function
              kill-buffer-query-functions))


(defvar modified-files nil)
(defvar files-to-write nil)
(defvar files-to-rename nil)
(defvar refactoring-committed nil)
(defvar unopened-files nil)
(defvar ediff-ignore-similar-regions t)
(defvar refactor-mode nil)
(defvar has-warning 'false)
(defvar refac-result nil)
;; (defvar my_gen_refac_menu_items nil)
;; (defvar my_gen_composite_refac_menu_items nil)
(defvar hare_ext (expand-file-name (concat (getenv "HOME") "/.hare/elisp/hare_ext.el")))

;; (setq modified-files nil)
;; (setq files-to-write nil)
;; (setq files-to-rename nil)
;; (setq refactoring-committed nil)
;; (setq unopened-files nil)
;; (setq ediff-ignore-similar-regions t)
;; (setq refactor-mode nil)
;; (setq has-warning 'false)
;; (setq refac-result nil)
;; (setq my_gen_refac_menu_items nil)
;; (setq my_gen_composite_refac_menu_items nil)
;; (setq hare_ext (expand-file-name (concat (getenv "HOME") "/.hare/elisp/hare_ext.el")))


(defun hare-ediff(file1 file2)
  "run ediff on file1 and file2"
  (setq refactor-mode t)
  (ediff file1 file2)
)

(add-hook 'ediff-quit-hook 'my-ediff-qh)

(defun my-ediff-qh()
  "Function to be called when ediff quits."
  (if (equal refactor-mode t)
      (if (equal modified-files nil)
          (commit-or-abort)
        (if (y-or-n-p "Do you want to preview changes made to other files?")
            (progn
              (defvar file-to-diff)
              (setq file-to-diff (car modified-files))
              (setq modified-files (cdr modified-files))
              (if (get-file-buffer-1 file-to-diff)
                  nil
                (setq unopened-files (cons file-to-diff unopened-files))
                )
              (hare-ediff file-to-diff (concat (file-name-sans-extension file-to-diff) 
                                                ".refactored"
                                                (file-name-extension file-to-diff t) )))
          (progn
            (setq modified-files nil)
            (commit-or-abort))))
    nil))


;; (defun is-a-monitored-file(file)
;;   "check if a file is monitored by Hare for refactoring activities."
;;   (setq monitored nil)
;;   (setq dirs dirs-to-monitor)
;;   (setq file1 (if (featurep 'xemacs)
;;                (replace-in-string file "/" "\\\\")
;;              file))
;;   (while (and (not monitored) (not (equal dirs nil)))
;;     (if (string-match (regexp-quote (file-name-as-directory (car dirs))) file1)
;;      (setq monitored 'true)
;;       (setq dirs (cdr dirs))
;;       ))
;;   (if monitored
;;       (car dirs)
;;     nil))

;; (defun log-search-result(curfilename logmsg)
;;   (let ((dir (is-a-monitored-file curfilename)))
;;     (if (equal nil dir)
;;         nil
;;       (cond
;;        ((equal version-control-system 'ClearCase)
;;         (add-logmsg-to-logfile-clearcase logmsg))
;;        ((or (equal version-control-system 'Git)
;;             (equal version-control-system 'SVN))
;;         (write-to-refac-logfile dir logmsg "Clone Detection"))
;;        (t nil)
;;        ))))

;; (defun add-logmsg-to-logfile-clearcase(logmsg)
;;   "Add logmsg to the refactor log file which is stored in a clearase repository." 
;;   (run-hook-with-args 'before-commit-functions (list refactor-log-file) nil)
;;   (run-hook-with-args 'after-commit-functions refactor-log-file logmsg)
;; )

(defun prepare-to-commit()
  ";make sure the files are writeable when cleaecase is used as the repository."
  (run-hook-with-args 'before-commit-functions files-to-write files-to-rename)
  (setq files-to-write nil)
  (setq files-to-rename nil)
  )

(defun commit()
  "commit the refactoring result."
  ;; (if (equal version-control-system 'ClearCase)
  ;;     (prepare-to-commit)
  ;;   nil
  ;;   )
  (do-commit)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The next two functions courtesy of the ghc-mod elisp.

(defun ghc-read-lisp (func)
  (with-temp-buffer
    (funcall func)
    (goto-char (point-min))
    (condition-case nil
        (read (current-buffer))
      (error ()))))

(defun ghc-read-lisp-list (func n)
  (with-temp-buffer
    (funcall func)
    (goto-char (point-min))
    (condition-case nil
        (let ((m (set-marker (make-marker) 1 (current-buffer)))
              ret)
          (dotimes (i n (nreverse ret))
            (ghc-add ret (read m))))
      (error ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Executing command
;;;

(defun ghc-boot (n)
  (if (not (executable-find ghc-hare-command))
      (message "%s not found" ghc-hare-command)
    (ghc-read-lisp-list
     (lambda ()
       (message "Initializing...")
       (call-process ghc-hare-command nil t nil "-l" "boot")
       (message "Initializing...done"))
    n)
  ))

(defun get-hare-version ()
  (interactive)
  (if (not (executable-find ghc-hare-command))
      (message "%s not found" ghc-hare-command)
    (message "HaRe version:%s"
    (ghc-read-lisp
     (lambda ()
       (message "Initializing...")
       (call-process ghc-hare-command nil t nil "--version")
       (message "Initializing...done"))
     ))
  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun do-commit()
  "commit the refactoring result."
  ;; (erl-spawn
  ;;   (erl-send-rpc wrangler-erl-node 'wrangler_preview_server 'commit (list))
    ;; (erl-receive ()
    ;;     ((['rex ['badrpc rsn]]
    ;;       (message "Commit failed: badrpc, %s" rsn))
    ;;      (['rex ['error rsn]]
    ;;       (message "Commit failed: error, %s" rsn))
    ;;      (['rex ['ok files logmsg]]
    ;;      (condition-case nil
    ;;           (update-repository files logmsg)
    ;;        (error (message-box "The refactor monitor of Wrangler is not working properly!"))
    ;;        )
    (let ((files (list)))
          (message "files-to-write=%s" (prin1-to-string files-to-write))
          (dolist (uf files-to-write)
            (progn
              (message "uf=%s" (prin1-to-string uf))
              (setq files (cons
                           (list uf uf
                           (concat (file-name-sans-extension uf)
                                   ".refactored"
                                   (file-name-extension uf t) ))
                           files))))
          (message "files=%s" (prin1-to-string files))
          (delete-swp-file-and-buffers files)
          (setq refactoring-committed t)
          (dolist (uf unopened-files)
            (kill-buffer (get-file-buffer-1 uf)))
          (setq unopened-files nil)
          (setq refactor-mode nil)
          (if (equal has-warning 'true)
              (progn
                (message "Refactoring succeeded, but please read the warning message in the *erl-output* buffer.")
                (setq has-warning 'false))
            nil
            )
          )
)

;; Original
;; (defun do-commit()
;;   "commit the refactoring result."
;;   (erl-spawn
;;     (erl-send-rpc wrangler-erl-node 'wrangler_preview_server 'commit (list))
;;     (erl-receive ()
;;      ((['rex ['badrpc rsn]]
;;        (message "Commit failed: badrpc, %s" rsn))
;;       (['rex ['error rsn]]
;;        (message "Commit failed: error, %s" rsn))
;;       (['rex ['ok files logmsg]]
;;       (condition-case nil
;;            (update-repository files logmsg)
;;         (error (message-box "The refactor monitor of Wrangler is not working properly!"))
;;         )
;;        (delete-swp-file-and-buffers files)
;;        (setq refactoring-committed t)
;;        (dolist (uf unopened-files)
;;          (kill-buffer (get-file-buffer-1 uf)))
;;        (setq unopened-files nil)
;;        (setq refactor-mode nil)
;;        (if (equal has-warning 'true)
;;            (progn
;;              (message "Refactoring succeeded, but please read the warning message in the *erl-output* buffer.")
;;              (setq has-warning 'false))
;;          nil
;;          ))))))

(defun current-time-suffix()
  "Generate a time stamp suffix in ISO 8601 format for backed up
   files, including a leading '.'"
  (format-time-string ".%Y-%m-%dT%T%z")
)

(defun delete-swp-file-and-buffers (files)
 "delete those .refactored file and buffers generated by the refactorer. NOTE:also renames the files"
 (dolist (f files)
   (let (old-file-name new-file-name swp-file-name)
     (setq old-file-name (elt f 0))
     (setq new-file-name (elt f 1))
     (setq swp-file-name (elt f 2))

     ;; At this stage there are no file renaming operations, so we
     ;; simply need to replace old-file-name with swp-file-name
     (rename-file old-file-name (concat old-file-name (current-time-suffix)))
     (rename-file swp-file-name old-file-name)

     (let ((swp-buff (get-file-buffer-1 swp-file-name)))
       (if swp-buff (kill-buffer swp-buff)
         nil))
     ;(delete-file  swp-file-name)
     (let ((buffer (get-file-buffer-1 old-file-name)))
       (if buffer
           (if (equal old-file-name new-file-name)
               (with-current-buffer buffer (revert-buffer nil t t))
             (with-current-buffer buffer
               (set-visited-file-name new-file-name)
               ;;(delete-file old-file-name)
               (revert-buffer nil t t)))
         nil)))))

(defun abort-changes()
  "abort the refactoring results"
  (error "not implemented")
  ;; (erl-spawn
  ;;   (erl-send-rpc wrangler-erl-node 'wrangler_preview_server 'abort (list))
  ;;   (erl-receive ()
  ;;       ((['rex ['badrpc rsn]]
  ;;         (setq refactor-mode nil)
  ;;         (message "Aborting refactoring failed: %S" rsn))
  ;;        (['rex ['error rsn]]
  ;;         (setq refactor-mode nil)
  ;;         (message "Aborting refactoring failed: %s" rsn))
  ;;        (['rex ['ok files]]
  ;;         (dolist (f files)
  ;;           (progn
  ;;             (let ((buff (get-file-buffer-1 f)))
  ;;               (if buff (kill-buffer (get-file-buffer-1 f))
  ;;                 nil))
  ;;             (delete-file f)))
  ;;         (dolist (uf unopened-files)
  ;;           (kill-buffer (get-file-buffer-1 uf)))
  ;;         (setq unopened-files nil)
  ;;         (setq refactor-mode nil)
  ;;         (message "Refactoring aborted."))))))
)

(defun commit-or-abort()
  "commit or abort the refactoring result."
  (if (y-or-n-p "Do you want to perform the changes?")
      (commit)
    (progn
      ;; files is returned by the wrangler backend in the orig.
      ;; Seems to be the list of modified files
      ;; (dolist (f files)
      ;;   (progn
      ;;     (let ((buff (get-file-buffer-1 f)))
      ;;       (if buff (kill-buffer (get-file-buffer-1 f))
      ;;         nil))
      ;;     (delete-file f)))
      (dolist (uf unopened-files)
        (kill-buffer (get-file-buffer-1 uf)))
      (setq unopened-files nil)
      (setq refactor-mode nil)
      (message "Refactoring aborted."))))



;; (defun commit-or-abort()
;;   "commit or abort the refactoring result."
;;   (if (y-or-n-p "Do you want to perform the changes?")
;;       (commit)
;;      (erl-spawn
;;       (erl-send-rpc wrangler-erl-node 'wrangler_preview_server 'abort (list))
;;       (erl-receive ()
;;           ((['rex ['badrpc rsn]]
;;             (setq refactor-mode nil)
;;             (message "Aborting refactoring failed: %S" rsn))
;;            (['rex ['error rsn]]
;;             (setq refactor-mode nil)
;;             (message "Aborting refactoring failed: %s" rsn))
;;            (['rex ['ok files]]
;;             (dolist (f files)
;;               (progn
;;                 (let ((buff (get-file-buffer-1 f)))
;;                   (if buff (kill-buffer (get-file-buffer-1 f))
;;                     nil))
;;                 (delete-file f)))
;;             (dolist (uf unopened-files)
;;               (kill-buffer (get-file-buffer-1 uf)))
;;             (setq unopened-files nil)
;;             (setq refactor-mode nil)
;;             (message "Refactoring aborted.")))))))



(defvar refactor-menu-items
  `(
    ;; ("Rename Variable Name" erl-refactor-rename-var)
    ;; ("Rename Function Name" erl-refactor-rename-fun)
    ;; ("Rename Module Name" erl-refactor-rename-mod)
    ;; ("Generalise Function Definition" erl-refactor-generalisation)
    ("Move Function to Another Module" hare-refactor-move-fun)
    ;; ("Function Extraction" erl-refactor-fun-extraction)
    ;; ("Introduce New Variable"  erl-refactor-new-variable)
    ;; ("Inline Variable" erl-refactor-inline-variable)
    ;; ("Fold Expression Against Function" erl-refactor-fold-expression)
    ;; ("Tuple Function Arguments" erl-refactor-tuple-funpar)
    ;; ("Unfold Function Application" erl-refactor-unfold-fun)
    nil
    ("Introduce a Macro" erl-refactor-new-macro)
    ("Fold Against Macro Definition" erl-refactor-fold-against-macro)
    nil
    ;; ("Refactorings for QuickCheck"
    ;;  (
    ;;   ("Introduce ?LET" erl-refactor-introduce-let)
    ;;   ("Merge ?LETs"    erl-refactor-merge-let)
    ;;   ("Merge ?FORALLs"   erl-refactor-merge-forall)
    ;;   ("eqc_statem State Data to Record" erl-refactor-eqc-statem-to-record)
    ;;   ("eqc_fsm State Data to Record" erl-refactor-eqc-fsm-to-record)
    ;;   ("Test Cases to Property"  erl-refactor-test-cases-to-property)
    ;;   ("Refactor Bug PreCond"  erl-refactor-bug-precond)
    ;;   ))
    nil
    ;; ("Process Refactorings (Beta)"
    ;;  (
    ;;   ("Rename a Process" erl-refactor-rename-process)
    ;;   ("Add a Tag to Messages"  erl-refactor-add-a-tag)
    ;;   ("Register a Process"   erl-refactor-register-pid)
    ;;   ("From Function to Process" erl-refactor-fun-to-process)
    ;;   ))
    ;; ("Normalise Record Expression" erl-refactor-normalise-record-expr)
    ;; ("Partition Exported Functions"  erl-wrangler-code-inspector-partition-exports)
    ;; ("gen_fsm State Data to Record" erl-refactor-gen-fsm-to-record)
    ;; nil
    ;; ("gen_refac Refacs"  (gen_refac_menu_items))
    ;; ("gen_composite_refac Refacs" (gen_composite_refac_menu_items))
    ;; nil
    ;; ("My gen_refac Refacs" (my_gen_refac_menu_items))
    ;; ("My gen_composite_refac Refacs" (my_gen_composite_refac_menu_items))
    ;; nil
    ;; ("Apply Adhoc Refactoring"  apply-adhoc-refac)
    ;; ("Apply Composite Refactoring" apply-composite-refac)
    nil
    ("Add/Remove Menu Items"
     (
       ("Add To My gen_refac Refacs" add_to_my_gen_refac_menu_items)
       ("Add To My gen_composite_refac Refacs" add_to_my_gen_composite_refac_menu_items)
       nil
        ("Remove from My gen_refac Refacs" remove_from_my_gen_refac_menu_items)
        ("Remove from My gen_composite_refac Refacs" remove_from_my_gen_composite_refac_menu_items)
    ))))

(defvar inspector-menu-items
  '(("Instances of a Variable" erl-wrangler-code-inspector-var-instances)
    ("Calls to a Function" erl-wrangler-code-inspector-caller-funs)
    ("Dependencies of a Module" erl-wrangler-code-inspector-caller-called-mods)
    ("Nested If Expressions" erl-wrangler-code-inspector-nested-ifs)
    ("Nested Case Expressions" erl-wrangler-code-inspector-nested-cases)
    ("Nested Receive Expression" erl-wrangler-code-inspector-nested-receives)
    ("Long Functions" erl-wrangler-code-inspector-long-funs)
    ("Large Modules" erl-wrangler-code-inspector-large-mods)
    ;;("Component Extraction Suggestion" erl-wrangler-code-component-extraction)
    ("Show Non Tail Recursive Servers" erl-wrangler-code-inspector-non-tail-recursive-servers)
    ("Incomplete Receive Patterns" erl-wrangler-code-inspector-no-flush)
    nil
    ("Apply Adhoc Code Inspection" apply-my-code-inspection)
    ))

(defvar wrangler-menu-items
  `(("Refactor" ,refactor-menu-items)
    ("Inspector" ,inspector-menu-items)
    nil
    ("Undo" hare-refactor-undo)
    nil
    ("Similar Code Detection"
     (("Detect Similar Code in Current Buffer" erl-refactor-inc-sim-code-detection-in-buffer)
      ("Detect Similar Code in Dirs" erl-refactor-inc-sim-code-detection-in-dirs)
      ("Similar Expression Search in Current Buffer" erl-refactor-similar-expression-search)
      ("Similar Expression Search in Dirs" erl-refactor-similar-expression-search-in-dirs)
      ;;  ("Detect Similar Code in Current Buffer (Old)" erl-refactor-sim-code-detection-in-buffer)
      ;;  ("Detect Similar Code in Dirs (Old)" erl-refactor-sim-code-detection-in-dirs)
      ))
     nil
     ("Module Structure"
      (("Generate Function Callgraph" erl-wrangler-code-inspector-callgraph)
       ("Generate Module Graph" erl-wrangler-code-inspector-module-graph)
       ("Cyclic Module Dependency" erl-wrangler-code-inspector-cyclic-graph)
       ("Module Dependency via Only Internal Functions" erl-wrangler-code-inspector-improper-module-dependency)))
    nil
    ("API Migration"
     (("Generate API Migration Rules"  erl-refactor-generate-migration-rules)
      ("Apply API Migration to Current File" erl-refactor-apply-api-migration-file)
      ("Apply API Migration to Dirs" erl-refactor-apply-api-migration-dirs)
      nil
      ("From Regexp to Re"  erl-refactor-regexp-to-re)
      ))
    nil
    ("Skeletons"
     (("gen_refac Skeleton"  tempo-template-gen-refac)
      ("gen_composite_refac Skeleton" tempo-template-gen-composite-refac)
      ))
    nil
    ("Customize HaRe" hare-customize)
    nil
    ("Version" haskell-refactor-version)
    ))


(global-set-key (kbd "C-c C-r") 'toggle-haskell-refactorer)

;; (add-hook 'erl-nodedown-hook 'wrangler-nodedown)

;; (defun wrangler-nodedown(node)
;;   ( if (equal node wrangler-erl-node)
;;      (progn (hare-menu-remove)
;;             (message "Wrangler stopped.")
;;      )
;;    nil))

(defun toggle-haskell-refactorer ()
  (interactive)
  (if (get-buffer "*HaRe-Shell*")
      (call-interactively 'haskell-refactorer-off)
    (call-interactively 'haskell-refactorer-on)))

(defun start-hare-app()
   (interactive)
   (hare-menu-init)
   )
;; (defun start-hare-app()
;;   (interactive)
;;   (erl-spawn
;;     (erl-send-rpc wrangler-erl-node 'application 'start (list 'wrangler))
;;     (erl-receive()
;;         ((['rex 'ok]
;;           (hare-menu-init)
;;           (message "Wrangler started.")
;;           )
;;          (['rex ['error ['already_started app]]]
;;           (message "Wrangler failed to start: another Wrangler application is running.")
;;           )
;;          (['rex ['error rsn]]
;;           (message "Wrangler failed to start:%s" rsn)
;;         )))))

(defun haskell-refactorer-off()
  (interactive)
  (hare-menu-remove)
  (if (not (get-buffer "*HaRe-Shell*"))
      t

      t
    ;; (progn
    ;;   (erl-spawn
    ;;     (erl-send-rpc wrangler-erl-node 'application 'stop (list 'wrangler))
    ;;     (erl-receive()
    ;;         ((['rex 'ok]
    ;;           (kill-buffer "*HaRe-Shell*")
    ;;           (message "Wrangler stopped"))
    ;;          (['rex ['error rsn]]
    ;;           (kill-buffer "*HaRe-Shell*")
    ;;           (message "Wrangler stopped"))
    ;;          ))))
    ))


(defun haskell-refactorer-off-1()
  (interactive)
  (hare-menu-remove)
  (if (not (get-buffer "*HaRe-Shell*"))
      t
    (progn
      (kill-buffer "*HaRe-Shell*"))
    ;; (progn
    ;;   (erl-spawn
    ;;     (erl-send-rpc wrangler-erl-node 'application 'stop (list 'wrangler))
    ;;     (erl-receive()
    ;;         ((['rex 'ok]
    ;;           (kill-buffer "*HaRe-Shell*")
    ;;          )
    ;;          (['rex ['error rsn]]
    ;;           (kill-buffer "*HaRe-Shell*")
    ;;           )))))))
   ))


(defun haskell-refactorer-on()
  (interactive)
  (message "starting HaRe...")
  ;; (check-erl-cookie)
  (if   (get-buffer "*HaRe-Shell*")
      (haskell-refactorer-off-1)
    t)
  ;; (setq wrangler-erl-node-string (concat "wrangler" (number-to-string (random 1000)) "@localhost"))
  ;; (setq wrangler-erl-node (intern  wrangler-erl-node-string))
  ;; (sleep-for 1.0)
  (save-window-excursion
    (hare-shell))
  (sleep-for 1.0)
  ;; (erl-spawn
  ;;   (erl-send-rpc wrangler-erl-node 'code 'ensure_loaded (list 'distel))
  ;;   (erl-receive()
  ;;       ((['rex res]
  ;;         t))))
  ;; (sleep-for 1.0)
  (start-wrangler-app))


;; (defun hare-shell()
;;   "Start a shell for HaRe"
;;   (interactive)
;;   (call-interactively hare-shell-function))

;; (defun check-erl-cookie()
;;   "check if file .erlang.cookie exists."
;;   (let ((cookie-file  (expand-file-name (concat (getenv "HOME") "/.erlang.cookie"))))
;;     (if (file-exists-p  cookie-file)
;;         t
;;       (error "File %s does not exist; please create it first, then restart Wrangler." 
;;              cookie-file))))

;; (defvar hare-shell-function 'hare-shell
;;   "Command to execute start a new Haskell Refactorer shell"
;; )

;; (defvar hare-shell-type 'newshell
;;         "variable need to make HaRe start with Ubuntu"
;; )

;; (defun hare-shell()
;;   "Run a HaRe shell"
;;   (interactive)
;;   (require 'comint)
;;   ;; (setq opts (list "-name" wrangler-erl-node-string
;;   ;;                  "-pa" (expand-file-name (concat (getenv "HOME") "/.wrangler/ebin"))
;;   ;;                  "-setcookie" (erl-cookie)
;;   ;;                  "-newshell" "-env" "TERM" "vt100"))
;;   (setq opts (list ""))
;;   (setq hare-shell-buffer
;;         (apply 'make-comint
;;                "HaRe-Shell" "erl"
;;                nil opts))
;;   (setq hare-shell-process
;;         (get-buffer-process hare-shell-buffer))
;;   (switch-to-buffer hare-shell-buffer)
;;   (if (and (not (equal system-type 'windows-nt))
;;            (equal hare-shell-type 'newshell))
;;       (setq comint-process-echoes t)))

(defun haskell-refactor-version()
  (interactive)
  (message "HaRe version 0.7.0.0"))

(setq hare-version  "(hare-0.7.0.0) ")

(defun hare-menu-init()
  "Init HaRe menus."
  (interactive)
  ;; (define-key erlang-mode-map "\C-c\C-w_"  'hare-refactor-undo)
  ;; (define-key erlang-mode-map "\C-c\C-wb" 'erl-wrangler-code-inspector-var-instances)
  ;; (define-key erlang-mode-map "\C-c\C-we" 'remove-highlights)
  ;; (define-key erlang-mode-map "\C-c\C-wrv" 'erl-refactor-rename-var)
  ;; (define-key erlang-mode-map "\C-c\C-wrf"  'erl-refactor-rename-fun)
  ;; (define-key erlang-mode-map "\C-c\C-wrm"  'erl-refactor-rename-mod)
  ;; (define-key erlang-mode-map "\C-c\C-g"    'erl-refactor-generalisation)
  (define-key erlang-mode-map "\C-c\C-wm"   'hare-refactor-move-fun)
  ;; (define-key erlang-mode-map "\C-c\C-wnv"  'erl-refactor-new-variable)
  ;; (define-key erlang-mode-map "\C-c\C-wi"  'erl-refactor-inline-variable)
  ;; (define-key erlang-mode-map "\C-c\C-wnf"  'erl-refactor-fun-extraction)
  ;; (define-key erlang-mode-map "\C-c\C-wff"   'erl-refactor-fold-expression)
  ;; (define-key erlang-mode-map "\C-c\C-wt"  'erl-refactor-tuple-funpar)
  ;; (define-key erlang-mode-map "\C-c\C-wu"  'erl-refactor-unfold-fun)
  ;; (define-key erlang-mode-map "\C-c\C-wnm"  'erl-refactor-new-macro)
  ;; (define-key erlang-mode-map "\C-c\C-wfm"  'erl-refactor-fold-against-macro)
  ;; (define-key erlang-mode-map "\C-c\C-ws"  'erl-refactor-similar-expression-search)
  ;; (define-key erlang-mode-map "\C-c\C-wcb"  'erl-refactor-inc-sim-code-detection-in-buffer)
  ;; (define-key erlang-mode-map "\C-c\C-wcd"  'erl-refactor-inc-sim-code-detection-in-dirs)
  (erlang-menu-install "HaRe" wrangler-menu-items erlang-mode-map t)
  )

(if (file-exists-p hare_ext)
    (load  hare_ext)
    nil)

;; (defun hare-menu-remove()
;;   "Remove HaRe menus."
;;   (interactive)
;;   (define-key erlang-mode-map "\C-c\C-w\C-_"  nil)
;;   (define-key erlang-mode-map  "\C-c\C-w\C-b" nil)
;;   (define-key erlang-mode-map "\C-c\C-w\C-e"  nil)
;;   (cond (erlang-xemacs-p
;;          (erlang-menu-uninstall '("HaRe") wrangler-menu-items erlang-mode-map t))
;;         (t
;;          (erlang-menu-uninstall "HaRe" wrangler-menu-items erlang-mode-map t))
;;         ))

(defun erlang-menu-uninstall (name items keymap &optional popup)
  "UnInstall a menu in Emacs or XEmacs based on an abstract description."
  (cond (erlang-xemacs-p
         (delete-menu-item name))
        ((>= erlang-emacs-major-version 19)
         (define-key keymap (vector 'menu-bar (intern name))
           'undefined))
        (t nil)))

;; (defun hare-refactor-undo()
;;   "Undo the latest refactoring."
;;   (interactive)
;;   (let (buffer (current-buffer))
;;     (if (y-or-n-p "Undo a refactoring will also undo the editings done after the refactoring, undo anyway?")
;;         (progn
;;           ;; (if (equal version-control-system 'ClearCase)
;;           ;;     nil
;;           ;;     ;; (erl-spawn
;;           ;;     ;;   (erl-send-rpc wrangler-erl-node 'wrangler_undo_server 'files_to_change (list))
;;           ;;     ;;   (erl-receive (buffer)
;;           ;;     ;;       ((['rex ['badrpc rsn]]
;;           ;;     ;;         (message "Undo failed: %S" rsn))
;;           ;;     ;;        (['rex ['error rsn]]
;;           ;;     ;;         (message "Undo failed: %s" rsn))
;;           ;;     ;;        (['rex ['ok files-to-recover  filenames-to-recover]]
;;           ;;     ;;         (progn
;;           ;;     ;;           (setq files-to-write files-to-recover)
;;           ;;     ;;           (setq files-to-rename filenames-to-recover)
;;           ;;     ;;           (prepare-to-commit) )))))
;;           ;;   nil
;;           ;;   )
;;           ;; (erl-spawn
;;           ;;   (erl-send-rpc wrangler-erl-node 'wrangler_undo_server 'undo_emacs (list))
;;           ;;   (erl-receive (buffer)
;;           ;;       ((['rex ['badrpc rsn]]
;;           ;;         (message "Undo failed: %S" rsn))
;;           ;;        (['rex ['error rsn]]
;;           ;;         (message "Undo failed: %s" rsn))
;;           ;;        (['rex ['ok modified1 logmsg curfile]]
;;           ;;         (dolist (f modified1)
;;           ;;           (let ((oldfilename (car f))
;;           ;;                 (newfilename (car (cdr f)))
;;           ;;                 (buffer (get-file-buffer-1 (car (cdr f)))))
;;           ;;             (if buffer (if (not (equal oldfilename newfilename))
;;           ;;                            (with-current-buffer buffer
;;           ;;                              (progn (set-visited-file-name oldfilename)
;;           ;;                                     (revert-buffer nil t t)))
;;           ;;                          (with-current-buffer buffer (revert-buffer nil t t)))
;;           ;;               nil)))
;;           ;;         (let ((dir (is-a-monitored-file curfile)))
;;           ;;           (if (equal nil dir)
;;           ;;               nil
;;           ;;             (cond
;;           ;;              ((equal version-control-system 'ClearCase)
;;           ;;               (let* ((reason (read-string "Reason for undo: " nil nil "" nil))
;;           ;;                     (new-logmsg (concat "UNDO: " logmsg "Reason: " reason "\n")))
;;           ;;                 (add-logmsg-to-logfile-clearcase new-logmsg)))
;;           ;;              ((or (equal version-control-system 'Git)
;;           ;;                   (equal version-control-system 'SVN))
;;           ;;               (let ((reason (read-string "Reason for undo: " nil nil "" nil)))
;;           ;;                 (write-to-refac-logfile dir (concat "UNDO: " logmsg "Reason: " reason "\n") "UNDO"))
;;           ;;               )
;;           ;;              (t nil))
;;           ;;             (message "Undo succeeded")))))))
;;           )
;;       (message "Undo aborted."))
;;     )
;;   )


(defun preview-commit-cancel(current-file-name modified renamed)
  "preview, commit or cancel the refactoring result"
  (setq files-to-write modified)
  (setq files-to-rename renamed)
  (preview-commit-cancel-1 current-file-name modified)
  )


(defun preview-commit-cancel-1 (current-file-name modified)
  "preview, commit or cancel the refactoring result"
  (let ((answer (read-char-spec-1 "Do you want to preview(p)/commit(c)/cancel(n) the changes to be performed?(p/c/n):"
                  '((?p p "Answer p to preview the changes")
                    (?c c "Answer c to commit the changes without preview")
                    (?n n "Answer n to abort the changes")))))
    (cond ((equal answer 'p)
           (defvar first-file)
           (setq first-file (car modified))
           (setq modified-files (cdr modified))
           (hare-ediff first-file
                           (concat (file-name-sans-extension first-file)
                                   ".refactored"
                                   (file-name-extension first-file t))))
          ((equal answer 'c)
           (commit))
          ((equal answer 'n)
           (abort-changes)))))




(defun revert-all-buffers()
  "Refreshs all open buffers from their respective files"
      (interactive)
      (let* ((list (buffer-list))
             (buffer (car list)))
        (while buffer
          (if (string-match "\\*" (buffer-name buffer))
              (progn
                (setq list (cdr list))
                (setq buffer (car list)))
            (progn
              (set-buffer buffer)
              (if (file-exists-p (buffer-file-name buffer))
                  (revert-buffer t t t)
                nil)
              (setq list (cdr list))
              (setq buffer (car list)))))))


(defun current-buffer-saved(buffer)
  (let* ((n (buffer-name buffer)) (n1 (substring n 0 1)))
    (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p buffer))
        (if (y-or-n-p "The current buffer has been changed, and HaRe needs to save it before refactoring, continue?")
            (progn (save-buffer)
                   t)
          nil)
      t)))

(defun buffers-saved()
  (let (changed)
      (dolist (b (buffer-list) changed)
        (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
          (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
              (setq changed (cons (buffer-name b) changed)))))
      (if changed
          (if (y-or-n-p (format "There are modified buffers: %s, which HaRe needs to save before refactoring, continue?" changed))
              (progn
                (save-some-buffers t)
                t)
            nil)
        t)
      ))


(defun buffers-changed-warning()
  (let (changed)
    (dolist (b (buffer-list) changed)
      (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
            (setq changed (cons (buffer-name b) changed)))))
    (if changed
        (if (y-or-n-p (format "Undo a refactoring could also undo the editings done after the refactoring, undo anyway?"))
            t
          nil)
      t)
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-iftocase(start end)
  "Register a process with a user-provied name."
  (interactive (list ;; (read-string "process name: ")
                  (region-beginning)
                  (region-end)
                  ))
  (let ((current-file-name (buffer-file-name))
     (buffer (current-buffer))
     (start-line-no (line-no-pos start))
     (start-col-no  (current-column-pos start))
     (end-line-no   (line-no-pos end))
     (end-col-no    (current-column-pos end)))
    (if (buffers-saved)
        (hare-refactor-command current-file-name start-line-no start-col-no
                         `("iftocase" ,current-file-name
                         ,(number-to-string start-line-no) ,(number-to-string start-col-no)
                         ,(number-to-string end-line-no)   ,(number-to-string end-col-no)
                         )
                         hare-search-paths 'emacs tab-width)
      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-dupdef (name)
  "Duplicate a definition."
  (interactive (list (read-string "new definition name: ")))
  (let ((current-file-name (buffer-file-name))
        (line-no           (current-line-no))
        (column-no         (current-column-no))
        (buffer (current-buffer)))
    (if (buffers-saved)
        (hare-refactor-command current-file-name line-no column-no
                         `("dupdef" ,current-file-name ,name
                         ,(number-to-string line-no) ,(number-to-string column-no)
                         )
                         hare-search-paths 'emacs tab-width)
      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-lift-one ()
  "Lift a definition one level."
  (interactive)
  (let ((current-file-name (buffer-file-name))
        (line-no           (current-line-no))
        (column-no         (current-column-no))
        (buffer (current-buffer)))
    (if (buffers-saved)
        (hare-refactor-command current-file-name line-no column-no
                         `("liftOneLevel" ,current-file-name
                         ,(number-to-string line-no) ,(number-to-string column-no))
                         hare-search-paths 'emacs tab-width)

      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-lifttotop ()
  "Lift a definition to the top level."
  (interactive)
  (let ((current-file-name (buffer-file-name))
        (line-no           (current-line-no))
        (column-no         (current-column-no))
        (buffer (current-buffer)))
    (if (buffers-saved)
        (hare-refactor-command current-file-name line-no column-no
                         `("liftToTopLevel" ,current-file-name
                         ,(number-to-string line-no) ,(number-to-string column-no))
                         hare-search-paths 'emacs tab-width)

      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-demote ()
  "Move a declaration down one level"
  (interactive)
  (let ((current-file-name (buffer-file-name))
        (line-no           (current-line-no))
        (column-no         (current-column-no))
        (buffer (current-buffer)))
    (if (buffers-saved) ;; TODO: move this test into hare-refactor-command
        (hare-refactor-command current-file-name line-no column-no
                         `("demote" ,current-file-name
                         ,(number-to-string line-no) ,(number-to-string column-no))
                         hare-search-paths 'emacs tab-width)

      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-rename (name)
  "Rename an identifier."
  (interactive (list (read-string "new identifier name: ")))
  (let ((current-file-name (buffer-file-name))
        (line-no           (current-line-no))
        (column-no         (current-column-no))
        (buffer (current-buffer)))
    (if (buffers-saved)
        (hare-refactor-command current-file-name line-no column-no
                         `("rename" ,current-file-name ,name
                         ,(number-to-string line-no) ,(number-to-string column-no)
                         )
                         hare-search-paths 'emacs tab-width)
      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-show ()
  "Show ghc-hare config."
  (interactive)
  ;(interactive (list (read-string "new identifier name: ")))
  (let ((current-file-name (buffer-file-name))
        (line-no           (current-line-no))
        (column-no         (current-column-no))
        (buffer (current-buffer)))
    (if (buffers-saved)
        (hare-refactor-command current-file-name line-no column-no
                         `("show"
                         )
                         hare-search-paths 'emacs tab-width)
      (message "Refactoring aborted."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hare-refactor-command (current-file-name line-no column-no params search-paths editor tab-width)
  "Send a refactoring command to the ghc-hare executable and process the reply"
  (let (composite-refac-p name msg result)
  (setq composite-refac-p (equal editor 'composite_emacs))

  (let ((res
        (ghc-read-lisp
         (lambda ()
           (message "Running...")
           (apply 'call-process ghc-hare-command nil t nil
                         params)
           (message "Running...done"))
         )))
    (with-current-buffer (get-buffer-create "*HaRe*") (insert (format "%s\n"  (prin1-to-string res))))
    (message "Res=%s" res)
    (process-result current-file-name res line-no column-no composite-refac-p)
   )
  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun process-result(current-file-name result line-no column-no composite-refac-p)
  "process the result return by refactoring"
  (let (rsn modified renamed warning name_change)
  (if composite-refac-p
      (cond ((equal (elt result 0) 'badrpc)
             (setq rsn (elt result 1))
             (message "Refactoring failed: %S" rsn)
             (apply-refac-cmds current-file-name (list 'error rsn)))
            ((equal (elt result 0) 'error)
             (setq rsn (elt result 1))
             (message-box "Refactoring failed: %S" rsn)
             (apply-refac-cmds current-file-name (list 'error rsn)))
            ((equal (elt result 0) 'ok)
             (setq modified (elt result 1))
             (setq renamed (if (> (length result) 3)
                               (elt result 2)
                             nil))
             (setq warning (if (> (length result) 3)
                               (elt result 3)
                             (if (> (length result) 2)
                                 (elt result 2)
                               nil)))
             (if warning
                 (setq has-warning warning)
               nil)
             ;;(update-buffers modified)
             (revert-all-buffers)
             (apply-refac-cmds current-file-name (list 'ok modified)))
            ((and (sequencep (elt result 0)) (equal (elt (elt result 0) 0) 'ok))
             (setq modified (elt (elt result 0) 1))
             (setq name_change (elt result 1))
             (message "Refactoring succeeded %s" modified)
             ;;(update-buffers modified)
             (message "current: %s" current-file-name)
             (revert-all-buffers)
             (apply-refac-cmds current-file-name (list (list 'ok modified) name_change)))
            (t
             (revert-all-buffers)
             (message "Unexpected result: %s" result))
            )
    (cond ((equal (elt result 0) 'ok)
           (setq modified (if (> (length result) 1)
                              (elt result 1)
                            nil))
           (setq renamed (if (> (length result) 3)
                               (elt result 2)
                             nil))
           (setq warning (if (> (length result) 3)
                               (elt result 3)
                             (if (> (length result) 2)
                                 (elt result 2)
                               nil)))
           (if warning
               (setq has-warning warning)
             nil)
           (if (equal modified nil)
               (message "Refactoring finished, and no file has been changed.")
             (preview-commit-cancel current-file-name modified renamed)
             (if (not (eq line-no 0))
               (with-current-buffer (get-file-buffer-1 current-file-name)
                 (goto-line line-no)
                 (goto-column column-no))
               nil)))
          ((equal (elt result 0) 'error)
           (setq rsn (elt result 1))
           (message "Refactoring failed: %S" rsn))
          ((equal (elt result 0) 'badrpc)
           (setq rsn (elt result 1))
           (message "Refactoring failed: %S" rsn))
          ((equal result ['abort])
           (message "Refactoring aborted."))))))



;; redefined get-file-buffer to handle the difference between
;; unix and windows filepath seperator.
(defun get-file-buffer (filename)
 (let ((buffer)
       (bs (buffer-list)))
        (while (and (not buffer) (not (equal bs nil)))
           (let ((b (car bs)))
             (if (and (buffer-file-name b)
                      (and (equal (file-name-nondirectory filename)
                                  (file-name-nondirectory (buffer-file-name b)))
                           (equal (file-name-directory filename)
                            (file-name-directory (buffer-file-name b)))))
                 (setq buffer 'true)
               (setq bs (cdr bs)))))
        (car bs)))


;; (defun get_instances_to_gen(instances buffer highlight-region-overlay)
;;   (setq instances-to-gen nil)
;;   (setq last-position 0)
;;   (while (not (equal instances nil))
;;     (setq new-inst (car instances))
;;     (setq line1 (elt (elt new-inst 0) 0))
;;     (setq col1  (elt (elt  new-inst 0) 1))
;;     (setq line2 (elt (elt new-inst 1) 0))
;;     (setq col2  (elt  (elt new-inst 1) 1))
;;     (if  (> (get-position line1 col1) last-position)
;;      (progn
;;        (highlight-region line1 col1 line2  col2 buffer)
;;        (if (yes-or-no-p "The expression selected occurs more than once in this function clause, would you like to replace the occurrence highlighted too?")
;;            (progn
;;              (setq instances-to-gen (cons new-inst instances-to-gen))
;;              (setq last-position (get-position line2 col2)))
;;          nil))
;;       nil)
;;     (setq instances (cdr instances)))
;;   (org-delete-overlay highlight-region-overlay)
;;   instances-to-gen)




(defun current-line-no ()
  "grmpff. does anyone understand count-lines?"
  (+ (if (equal 0 (current-column)) 1 0)
     (count-lines (point-min) (point)))
  )

(defun current-column-no ()
  "the column number of the cursor"
  (+ 1 (current-column)))


(defun line-no-pos (pos)
  "grmpff. why no parameter to current-column?"
  (save-excursion
    (goto-char pos)
    (+ (if (equal 0 (current-column)) 1 0)
       (count-lines (point-min) (point))))
  )

(defun current-column-pos (pos)
  "grmpff. why no parameter to current-column?"
  (save-excursion
    (goto-char pos) (+ 1 (current-column)))
  )


(defun get-position(line col)
  "get the position at lie (line, col)"
  (save-excursion
    (goto-line line)
    (move-to-column col)
    (- (point) 1)))


(defun goto-column(col)
  (if (> col 0)
      (move-to-column (- col 1))
    (move-to-column col)))


(defvar highlight-region-overlay
  ;; Dummy initialisation
  (cond (erlang-xemacs-p
         (make-extent 1 1))
        (t (make-overlay 1 1)))
  "Overlay for highlighting.")

(defface highlight-region-face
  '((t (:background "CornflowerBlue")))
    "Face used to highlight current line.")

(defface def-instance-face
   '((t (:background "Orange")))
    "Face used to highlight def instance.")

(defface use-instance-face
   '((t (:background "CornflowerBlue")))
    "Face used to highlight def instance.")


(defun highlight-region(line1 col1 line2 col2 buffer)
  "hightlight the specified region"
  (org-overlay-put highlight-region-overlay
               'face 'highlight-region-face)
  (org-move-overlay highlight-region-overlay (get-position line1 col1)
                    (get-position line2 (+ 1 col2)) buffer)
  (goto-line line2)
  (goto-column col2)
  )


(defun remove-highlights()
  "remove highligths in the buffer"
  (interactive)
  (dolist (ov (if (featurep 'xemacs)
                  (extent-list (current-buffer))
                (overlays-in  1 100000)))
    (if (equal ov highlight-region-overlay)
        nil
      (org-delete-overlay ov))))


(defun highlight-instances-with-same-face(filename regions)
  "highlight regions in the buffer with the same color"
  ; (setq buffer (find-file filename))
  (let (buffer (find-file filename))
  (with-current-buffer buffer
    (dolist (r regions)
      (highlight-use-instance r buffer)))))


(defun highlight-a-instance(region buffer)
   "highlight one region in the buffer"
   (let ((line1 (elt (elt region 0) 0))
          (col1 (elt (elt region 0) 1))
          (line2 (elt (elt region 1) 0))
          (col2 (elt (elt region 1) 1)))
     (goto-char (get-position line1 (- col1 1)))
     (highlight-region line1 col1 line2 col2 buffer)
       ))

(defun highlight-instances(regions defpos buffer)
  "highlight regions in the buffer"
  (dolist (r regions)
     (if (member (elt r 0) defpos)
         (highlight-def-instance r buffer)
       (highlight-use-instance r buffer))))


(defun highlight-instances-1(regions selected buffer)
  "highlight regions in the buffer"
  (dolist (r regions)
    (if (equal r selected)
        (highlight-def-instance (elt r 1) buffer)
      (highlight-use-instance (elt r 1) buffer))))

(defun highlight-def-instance(region buffer)
   "highlight one region in the buffer"
   (let ((line1 (elt (elt region 0) 0))
          (col1 (elt (elt region 0) 1))
          (line2 (elt (elt region 1) 0))
          (col2 (elt (elt region 1) 1)))
     (highlight-region-with-face line1 col1 line2 col2 buffer 'def-instance-face)))


(defun highlight-use-instance(region buffer)
   "highlight one region in the buffer"
   (let ((line1 (elt (elt region 0) 0))
          (col1 (elt (elt region 0) 1))
          (line2 (elt (elt region 1) 0))
          (col2 (elt (elt region 1) 1)))
     (highlight-region-with-face line1 col1 line2 col2 buffer 'use-instance-face)))





(defun highlight-region-with-face(line1 col1 line2 col2 buffer face)
  "hightlight the specified region"
  (org-overlay-put (org-make-overlay (get-position line1 col1) (get-position line2 (+ 1 col2)))
                   'face face))


(defun org-make-overlay(beg end)
   ;; make a overlay
   (if (featurep 'xemacs)
       (make-extent beg end)
     (make-overlay beg end)))

(defun org-move-overlay (ovl beg end &optional buffer)
  (if (featurep 'xemacs)
      (set-extent-endpoints ovl beg end (or buffer (current-buffer)))
    (move-overlay ovl beg end buffer)))

(defun org-overlay-put (ovl prop value)
  (if (featurep 'xemacs)
      (set-extent-property  ovl prop value)
    (overlay-put ovl prop value)))

(defun org-delete-overlay (ovl)
  (if (featurep 'xemacs) (progn (detach-extent ovl) nil) (delete-overlay ovl)))




(defun get-file-buffer-1(f)
  (if (featurep 'xemacs)
      (progn
        (setq file-buffer nil)
        (setq buffers (buffer-list))
        (setq f1 (replace-in-string f "/" "\\\\"))
        (while (and (not file-buffer) (not (equal buffers nil)))
           (let ((filename (buffer-file-name (car buffers))))
             (if filename
                 (progn
                   (if (equal (downcase f1) (downcase filename))
                       (setq file-buffer (car buffers))
                     (setq buffers (cdr buffers)))
                   )
               (setq buffers (cdr buffers))
               )))
        file-buffer)
    (get-file-buffer f)))



(defun update-buffers(files)
  "update the buffers for files that have been changed"
  (dolist (f files)
    (let ((buffer (get-file-buffer-1 f)))
      (if buffer
          (with-current-buffer buffer (revert-buffer nil t t))
        nil))))

;; (defun get_user_inputs(args)
;;   "get the user input for parameters that need user input."
;;   (interactive)
;;   (setq new-args nil)
;;   (while (not (equal args nil))
;;     (let ((cur-arg (car args)))
;;       (if (sequencep cur-arg)
;;           (progn
;;             (if (equal (elt cur-arg 0) 'prompt)
;;                 (let ((prompt (elt cur-arg 1)))
;;                   (setq new-args (cons (read-string prompt) new-args)))
;;               (setq new-args (cons cur-arg new-args))
;;               ))
;;         (setq new-args (cons cur-arg new-args))
;;         ))
;;     (setq args (cdr args)))
;;   (reverse new-args)
;; )
 

;; (defun highlight_sels(args)
;;   "highlightget the selections."
;;   (interactive)
;;   (while (not (equal args nil))
;;     (let ((cur-arg (car args)))
;;       (if (sequencep cur-arg)
;;           (if(equal (elt cur-arg 0) 'range)
;;               (let ((file (elt (elt cur-arg 1) 0))
;;                     (ranges (elt (elt cur-arg 1) 1)))
;;                 (highlight-instances-with-same-face file ranges))
;;             nil)
;;         nil))
;;     (setq args (cdr args)))
;;   )



