;;; clipmon-test.el --- tests for clipmon.el
;;; Commentary:

; Just test the complicated things.

; Run standalone with
; $ emacs -batch -L . -l clipmon-test.el -f ert-run-tests-batch
;
; Running 2 tests (2014-12-27 01:01:14-0600)
;    passed  1/2  clipmon-test-all-transforms
;    passed  2/2  clipmon-test-no-transforms
; Ran 2 tests, 2 results as expected (2014-12-27 01:01:14-0600)
;
;
; or internally with (ert-run)
; or (ert-run-tests-interactively "regexp")


;;; Code:

(require 'ert)
(require 'clipmon)


(ert-deftest clipmon-test-no-transforms ()
  "Try with no transforms on text."

  (let ((clipmon-transform-trim nil)
        (clipmon-transform-remove nil)
        (clipmon-transform-prefix nil)
        (clipmon-transform-suffix nil)
        (clipmon-transform-function nil))

    (should (equal
             (clipmon--autoinsert-transform-text
               " Marbled murrelets use old-growth forest stands for nesting.[2][3] ")
               " Marbled murrelets use old-growth forest stands for nesting.[2][3] "))
    ))


(ert-deftest clipmon-test-all-transforms ()
  "Try all text transforms."

  (let ((clipmon-transform-trim t)
        (clipmon-transform-remove "stands \\|\\[[0-9]+\\]\\|\\[citation needed\\]")
        (clipmon-transform-prefix "<<")
        (clipmon-transform-suffix ">>")
        (clipmon-transform-function (lambda (s) (downcase s))))

    (should (equal
             (clipmon--autoinsert-transform-text
               " Marbled murrelets use old-growth forest stands for nesting.[2][3] ")
               "<<marbled murrelets use old-growth forest for nesting. >>"))
    ))


(ert-deftest clipmon-test-remove-regexp ()
  "Try the remove-regexp for Wikipedia references."

  (let ((clipmon-transform-trim nil)
        ; use the default remove-regexp
        (clipmon-transform-prefix nil)
        (clipmon-transform-suffix nil)
        (clipmon-transform-function nil))

    (should (equal
             (clipmon--autoinsert-transform-text
               " Marbled [1 2] murrelets[115] use [old-growth][99] stands [1984] for nesting.[2] ")
               " Marbled [1 2] murrelets use [old-growth] stands [1984] for nesting. "))
    ))


(ert-deftest clipmon-test-on-and-off ()
  "Try turning mode and autoinsert on and off."
  (let ((clipmon-autoinsert-sound nil))

    ; clipmon-mode
    ; off
    (clipmon-mode-stop)
    (should (null clipmon-mode))
    (clipmon-mode-stop)
    (should (null clipmon-mode))

    ; on
    (clipmon-mode-start)
    (should clipmon-mode)
    (clipmon-mode-start)
    (should clipmon-mode)

    ; off
    (clipmon-mode 'toggle)
    (should (null clipmon-mode))

    ; on
    (clipmon-mode 'toggle)
    (should clipmon-mode)

    ; off
    (clipmon-mode 0)
    (should (null clipmon-mode))


    ; autoinsert
    ; off
    (clipmon-autoinsert-stop)
    (should (null clipmon--autoinsert))
    (should (null clipmon-mode)) ; ie should still be off

    ; on
    (clipmon-autoinsert-toggle)
    (should clipmon--autoinsert)
    (should clipmon-mode) ; should automatically turn the mode on

    ; off
    (clipmon-autoinsert-toggle)
    (should (null clipmon--autoinsert))
    (should clipmon-mode) ; should stay on

    (clipmon-mode 0)
    (should (null clipmon-mode))
    ))


(ert-deftest clipmon-test-timeout ()
  "Let clock timeout."
  (let ((clipmon-timer-interval 0.1) ; secs
        (clipmon-autoinsert-timeout (/ 0.2 60.0)) ; 0.2 secs in mins
        (sleep-amount 0.4) ; secs
        (clipmon-autoinsert-sound nil))

    (clipmon-autoinsert-stop)
    (clipmon-autoinsert-start)
    (should clipmon--autoinsert)
    (should clipmon-mode) ; should turn this on also
    (sleep-for sleep-amount) ; wait for timeout
    (should (null clipmon--autoinsert))
    (should clipmon-mode) ; should still be on
    ))


; (defun get-tar-file (folder)
;   "Get the latest tar file from the folder."
;   (let* ((files (directory-files folder t "\\.tar$")) ; in sorted order
;          (tar-file (car (last files)))) ; latest tar
;     tar-file))
; ; (get-tar-file "../tar")
; ; (get-tar-file "./tar")



; (ert-deftest clipmon-test-install ()
;   "Test installing from latest tar file to a local elpa folder."
  
;   ;; We can make a new elpa folder, call it elpa-test, and install clipmon there,
;   ;; just to see that the install is working correctly. 
;   (let* ((folder-elpa-test (expand-file-name "elpa-test" "."))
;          (package-user-dir folder-elpa-test) ; temporarily bind this
;          (tar-file (get-tar-file "tar")))
    
;     ;; delete elpa-test folder to start new
;     (when (file-exists-p folder-elpa-test)
;       (message "deleting %s..." folder-elpa-test)
;       (delete-directory folder-elpa-test t))

;     ;; a typical setup
;     (global-set-key (kbd "C-0") 'clipmon-autoinsert-toggle)
;     (setq clipmon-interval 1) ; an old name
;     (setq clipmon-transform-clip nil) ; a new name
;     (add-to-list 'after-init-hook 'clipmon-mode-start) ; capture to kill ring
;     (add-to-list 'after-init-hook 'clipmon-persist) ; persist kill ring to disk
    
;     ;; Note: this file is run in batch mode, which inhibits packages from being initialized,
;     ;; so we must simulate it ourselves.
    
;     ;; install package from tar file - this also requires/loads the package.
;     ;; this is akin to what package-initialize does, after reading the init file,
;     ;; though package-initialize just loads the autoloads, not the whole file.
;     ;;> so, should add another test to check an existing installation.. somehow.
;     (package-install-file tar-file)

;     ; this hook would be run after package-initialize, so run it here
;     (run-hooks 'after-init-hook)
    
;     ;; make sure menu is there
;     (should (key-binding [menu-bar options clipmon-killring]))
    
;     ;; and settings
;     (should (boundp 'clipmon-timer-interval))
    
;     ;; see if files got there okay - .el, .wav
;     ;; (dired folder-elpa-test)
;     ;; (assert (member "clipmon.el" (directory-files latestclipmonfolder)))

;     ;; check renamings
;     (should (eq 1 clipmon-timer-interval))
;     (should (eq clipmon-timeout clipmon-autoinsert-timeout))

;     ;; turn on and off
;     (let ((clipmon-autoinsert-sound nil)) ; quiet
;       (clipmon-autoinsert-toggle)
;       (clipmon-mode 0)
;       (should (null clipmon--autoinsert))
;       (should (null clipmon-mode)))
    
;     ;; other things to check
;     ;; (find-library "clipmon")
;     ;; (describe-package "clipmon")
;     ;; (customize-group 'clipmon)
    
;     ))


;;; clipmon-test.el ends here
