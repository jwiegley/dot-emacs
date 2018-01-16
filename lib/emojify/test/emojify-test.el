;;; emojify-test.el --- Tests for emojify              -*- lexical-binding: t; -*-

;;; Commentary:
;;; Tests for emojify, major use case is to run from the command-line
;;; but can use can be interactively as well. Do M-x `eval-buffer' RET

;;; Code:

;; For interactive testing
(unless noninteractive
  (load (expand-file-name "test-helper.el") t))

;; Used for testing integration with programming modes
(require 'org)
(require 'org-agenda)
(require 'cc-mode)
(require 'bytecomp)

(ert-deftest emojify-tests-simple-ascii-emoji-test ()
  :tags '(ascii simple)
  (emojify-tests-with-emojified-static-buffer ":)"
    (emojify-tests-should-be-emojified (point-min))
    (should (equal (get-text-property (point-min) 'emojify-buffer) (current-buffer)))
    (should (equal (get-text-property (point-min) 'emojify-beginning) (point-min-marker)))
    (should (equal (get-text-property (point-min) 'emojify-end) (point-max-marker)))
    (should (equal (get-text-property (point-min) 'emojify-text)  ":)"))))

(ert-deftest emojify-tests-simple-github-emoji-test ()
  :tags '(github simple)
  (emojify-tests-with-emojified-static-buffer ":smile:"
    (emojify-tests-should-be-emojified (point-min))
    (should (equal (get-text-property (point) 'emojify-buffer) (current-buffer)))
    (should (equal (get-text-property (point-min) 'emojify-beginning) (point-min-marker)))
    (should (equal (get-text-property (point) 'emojify-end) (point-max-marker)))
    (should (equal (get-text-property (point) 'emojify-text)  ":smile:"))))

(ert-deftest emojify-tests-simple-unicode-emoji-test ()
  :tags '(unicode simple)
  (emojify-tests-with-emojified-static-buffer "😉"
    (emojify-tests-should-be-emojified (point-min))
    (should (equal (get-text-property (point) 'emojify-buffer) (current-buffer)))
    (should (equal (get-text-property (point-min) 'emojify-beginning) (point-min-marker)))
    (should (equal (get-text-property (point) 'emojify-end) (point-max-marker)))
    (should (equal (get-text-property (point) 'emojify-text)  "😉")))

  (emojify-tests-with-emojified-static-buffer "😉"
    ;; Emojis should be displayed by default in programming mode
    (emacs-lisp-mode)
    (emojify-tests-should-be-emojified (point-min))
    (should (equal (get-text-property (point) 'emojify-buffer) (current-buffer)))
    (should (equal (get-text-property (point-min) 'emojify-beginning) (point-min-marker)))
    (should (equal (get-text-property (point) 'emojify-end) (point-max-marker)))
    (should (equal (get-text-property (point) 'emojify-text)  "😉"))

    ;; Emojis should be displayed by default in non-programming mode
    (fundamental-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (point-min))

    ;; Emojis should not be displayed if code is not an element in emojify-program-contexts
    (setq emojify-program-contexts '())
    (emacs-lisp-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (point-min))))

(ert-deftest emojify-test-custom-emojis ()
  :tags '(core custom-images)
  (let ((emojify-user-emojis emojify-test-custom-emojis))
    (emojify-set-emoji-data)
    (emojify-tests-with-emojified-static-buffer ":neckbeard:
:troll:"
      (emojify-tests-should-be-emojified (point-min))
      (should (equal (get-text-property (point) 'emojify-buffer) (current-buffer)))
      (should (= (get-text-property (point-min) 'emojify-beginning) (point-min-marker)))
      (should (= (get-text-property (point) 'emojify-end) (line-end-position 1)))
      (should (equal (get-text-property (point) 'emojify-text)  ":neckbeard:"))

      (emojify-tests-should-be-emojified (line-beginning-position 2))
      (should (equal (get-text-property (line-beginning-position 2) 'emojify-buffer) (current-buffer)))
      (should (= (get-text-property (line-beginning-position 2) 'emojify-beginning) (line-beginning-position 2)))
      (should (= (get-text-property (line-beginning-position 2) 'emojify-end) (point-max-marker)))
      (should (equal (get-text-property (line-beginning-position 2) 'emojify-text)  ":troll:")))))

(ert-deftest emojify-tests-mixed-emoji-test ()
  :tags '(core mixed)
  (let ((emojify-user-emojis emojify-test-custom-emojis))
    (emojify-set-emoji-data)
    (emojify-tests-with-emojified-static-buffer "😉\n:D\nD:\n:smile:\n:neckbeard:"
      (emojify-tests-should-be-emojified (point-min))
      (emojify-tests-should-be-emojified (line-beginning-position 2))
      (emojify-tests-should-be-emojified (line-beginning-position 3))
      (emojify-tests-should-be-emojified (line-beginning-position 4))
      (emojify-tests-should-be-emojified (line-beginning-position 5)))))

(ert-deftest emojify-tests-emoji-uncovering ()
  :tags '(behaviour point-motion)
  (emojify-tests-with-emojified-buffer " :)"
    (setq emojify-point-entered-behaviour 'uncover)
    (execute-kbd-macro (kbd "C-f") 2)
    (emojify-tests-should-be-uncovered (point))))

(ert-deftest emojify-tests-emoji-echoing ()
  :tags '(behaviour point-motion)
  (emojify-tests-with-emojified-buffer " :)"
    (with-mock
      ;; Since emojify checks that there is no message being displayed
      ;; before echoing the emoji, we need to stub out current-message
      ;; too otherwise emojify does not echo the message since messages
      ;; from other tests are being displayed
      (stub current-message => nil)
      (mock (message ":)"))
      (setq emojify-point-entered-behaviour 'echo)
      (execute-kbd-macro (kbd "C-f"))
      (emojify-tests-should-be-emojified (point)))))

(ert-deftest emojify-tests-custom-point-entered-function ()
  :tags '(behaviour point-motion)
  (emojify-tests-with-emojified-buffer " :)"
    (setq emojify-point-entered-behaviour (lambda (buffer emoji-text emoji-start emoji-end)
                                            (should (equal buffer (current-buffer)))
                                            (should (equal emoji-text ":)"))
                                            (should (equal emoji-start (1+ (point-min))))
                                            (should (equal emoji-start (point-max)))))
    (goto-char (1+ (point-min)))
    (emojify-tests-should-be-emojified (point))))

(ert-deftest emojify-tests-emojify-setting-styles ()
  :tags '(styles github ascii)
  (emojify-tests-with-emojified-static-buffer ":) 😄 :smile: return"
    (let ((ascii-emoji-pos (point-min))
          (unicode-emoji-pos (+ (point-min) (length ":) ")))
          (github-emoji-pos (+ (point-min) (length ":) 😄 ")))
          (prettify-emoji-pos (+ (point-min) (length ":) 😄 :smile: "))))

      (setq emojify-composed-text-p t)
      (setq prettify-symbols-alist
            '(("return" . ?↪)))

      (setq emojify-composed-text-p t)

      (when (fboundp 'prettify-symbols-mode)
        (prettify-symbols-mode +1)
        ;; On Emacs 25.1 fontification does not happen automatically
        (when (fboundp 'font-lock-ensure) (font-lock-ensure)))

      (emojify-set-emoji-styles '(ascii))
      (emojify-tests-should-be-emojified ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prettify-emoji-pos)
      (emojify-tests-should-not-be-emojified github-emoji-pos)

      (emojify-set-emoji-styles '(unicode))
      (emojify-tests-should-not-be-emojified ascii-emoji-pos)
      (emojify-tests-should-be-emojified unicode-emoji-pos)
      (when (fboundp 'prettify-symbols-mode)
        (emojify-tests-should-be-emojified prettify-emoji-pos))
      (emojify-tests-should-not-be-emojified github-emoji-pos)

      (emojify-set-emoji-styles '(github))
      (emojify-tests-should-not-be-emojified ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prettify-emoji-pos)
      (emojify-tests-should-be-emojified github-emoji-pos)

      (emojify-set-emoji-styles '(ascii unicode github))
      (emojify-tests-should-be-emojified ascii-emoji-pos)
      (emojify-tests-should-be-emojified unicode-emoji-pos)
      (when (fboundp 'prettify-symbols-mode)
        (emojify-tests-should-be-emojified prettify-emoji-pos))
      (emojify-tests-should-be-emojified github-emoji-pos)

      (emojify-set-emoji-styles nil)
      (emojify-tests-should-not-be-emojified ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prettify-emoji-pos)
      (emojify-tests-should-not-be-emojified github-emoji-pos))))

(ert-deftest emojify-tests-program-contexts ()
  :tags '(core prog contextual)
  (emojify-tests-with-emojified-static-buffer ";; :) :smile:\n\":smile:\"\n8) 💜 :smile:"
    (let* ((comment-ascii-emoji-pos (+ 3 (point-min)))
           (comment-github-emoji-pos (+ comment-ascii-emoji-pos (length ":) ")))
           (string-github-emoji-pos (1+ (line-beginning-position 2)))
           (prog-ascii-emoji-pos (line-beginning-position 3))
           (prog-unicode-emoji-pos (+ 3 prog-ascii-emoji-pos))
           (prog-github-emoji-pos (+ 2 prog-unicode-emoji-pos)))
      (emacs-lisp-mode)
      (setq emojify-program-contexts '(comments string code))
      (emojify-redisplay-emojis-in-region)
      (emojify-tests-should-be-emojified comment-ascii-emoji-pos)
      (emojify-tests-should-be-emojified comment-github-emoji-pos)
      (emojify-tests-should-be-emojified string-github-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-ascii-emoji-pos)
      (emojify-tests-should-be-emojified prog-unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-github-emoji-pos)

      (setq emojify-program-contexts '(comments))
      (emojify-redisplay-emojis-in-region)
      (emojify-tests-should-be-emojified comment-ascii-emoji-pos)
      (emojify-tests-should-be-emojified comment-github-emoji-pos)
      (emojify-tests-should-not-be-emojified string-github-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-github-emoji-pos)

      (setq emojify-program-contexts '(string))
      (emojify-redisplay-emojis-in-region)
      (emojify-tests-should-not-be-emojified comment-ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified comment-github-emoji-pos)
      (emojify-tests-should-be-emojified string-github-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-github-emoji-pos)

      (setq emojify-program-contexts '(code))
      (emojify-redisplay-emojis-in-region)
      (emojify-tests-should-not-be-emojified comment-ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified comment-github-emoji-pos)
      (emojify-tests-should-not-be-emojified string-github-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-ascii-emoji-pos)
      (emojify-tests-should-be-emojified prog-unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-github-emoji-pos)

      (setq emojify-program-contexts '())
      (emojify-redisplay-emojis-in-region)
      (emojify-tests-should-not-be-emojified comment-ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified comment-github-emoji-pos)
      (emojify-tests-should-not-be-emojified string-github-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-ascii-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-unicode-emoji-pos)
      (emojify-tests-should-not-be-emojified prog-github-emoji-pos))))

(ert-deftest emojify-tests-ascii-emoji-contexts ()
  :tags '(core text contextual)
  ;; At start of comment
  (emojify-tests-with-emojified-static-buffer ";:)"
    (emacs-lisp-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (1+ (point-min))))

  ;; In comment after space
  (emojify-tests-with-emojified-static-buffer "; :)"
    (emacs-lisp-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (+ 2 (point-min))))

  ;; Inside a comment
  (emojify-tests-with-emojified-static-buffer "/**\n:)"
    (c-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (line-beginning-position 2)))

  ;; Immediately after a word
  (emojify-tests-with-emojified-static-buffer "A:)"
    (emojify-tests-should-not-be-emojified (1+ (point-min))))

  ;; Immediately before a word
  (emojify-tests-with-emojified-static-buffer ":)A"
    (emojify-tests-should-not-be-emojified (1+ (point-min))))

  ;; Immediately before a closing bracket
  (emojify-tests-with-emojified-static-buffer ":))"
    (emojify-tests-should-be-emojified (1+ (point-min))))

  ;; Immediately after a punctuation character
  (emojify-tests-with-emojified-static-buffer "!:)"
    (emojify-tests-should-not-be-emojified (1+ (point-min))))

  ;; Following a punctuation and a space
  (emojify-tests-with-emojified-static-buffer "! :)"
    (emojify-tests-should-be-emojified (+ 2 (point-min))))

  ;; Outside a comment
  (emojify-tests-with-emojified-static-buffer "/**/:)"
    (c-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (+ 4 (point-min))))

  ;; Surrounded by comments
  (emojify-tests-with-emojified-static-buffer "/*:)*/"
    (c-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (+ 2 (point-min)))))

(ert-deftest emojify-tests-multiple-emojis-in-sequence ()
  "See Github issue #6"
  :tags '(core contextual)
  (emojify-tests-with-emojified-static-buffer ":100::smile:
:100:a:smile:
🎆😃
🎆a😃
😉:wink:
:100:😃
:100:a😃"
    ;; Github emojis
    (emojify-tests-should-be-emojified (point-min))
    (emojify-tests-should-be-emojified (+ (point-min) 5))
    (emojify-tests-should-be-emojified (line-beginning-position 2))
    (emojify-tests-should-be-emojified (+ (line-beginning-position 2) 6))

    ;; Unicode emojis
    (emojify-tests-should-be-emojified (line-beginning-position 3))
    (emojify-tests-should-be-emojified (+ (line-beginning-position 3) 1))
    (emojify-tests-should-be-emojified (line-beginning-position 4))
    (emojify-tests-should-be-emojified (+ (line-beginning-position 4) 2))

    ;; Mixed emojis
    (emojify-tests-should-be-emojified (line-beginning-position 5))
    (emojify-tests-should-be-emojified (+ (line-beginning-position 5) 1))
    (emojify-tests-should-be-emojified (line-beginning-position 6))
    (emojify-tests-should-be-emojified (+ (line-beginning-position 6) 5))
    (emojify-tests-should-be-emojified (line-beginning-position 7))
    (emojify-tests-should-be-emojified (+ (line-beginning-position 7) 6))))

(ert-deftest emojify-tests-emojifying-lists ()
  :tags '(core contextual)
  (emojify-tests-with-emojified-static-buffer ":]"
    (emojify-tests-should-be-emojified (point-min)))

  (emojify-tests-with-emojified-static-buffer "[ :]"
    (emojify-tests-should-not-be-emojified (+ 3 (point-min))))

  (emojify-tests-with-emojified-static-buffer ";; 8)"
    (emojify-tests-should-be-emojified (+ 3 (point-min))))

  (emojify-tests-with-emojified-static-buffer ":(
:)"
    (fundamental-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (point-min))
    (emojify-tests-should-be-emojified (line-beginning-position 2)))

    (emojify-tests-with-emojified-static-buffer "(
:)"
    (fundamental-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (point-min))
    (emojify-tests-should-not-be-emojified (line-beginning-position 2)))

  (emojify-tests-with-emojified-static-buffer ";; (lambda () 8)"
    (emacs-lisp-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (+ 14 (point-min)))))

(ert-deftest emojify-tests-overlapping-emojis ()
  :tags '(core)
  (emojify-tests-with-emojified-static-buffer "👲🏽"
    (fundamental-mode)
    (let ((count 0))
      (emojify-do-for-emojis-in-region (point-min) (point-max)
        (cl-incf count))
      ;; Only one emoji should be displayed
      (should (= count 1))
      ;; The larger emoji should be preferred
      (should (string= (get-text-property (point-min) 'emojify-text)
                       "👲🏽")))))

(ert-deftest emojify-tests-emojifying-org-mode-buffers ()
  :tags '(org-mode contextual)
  (emojify-tests-with-emojified-static-buffer "* Test :books:\n:books:"
    (org-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (1- (line-end-position)))
    (emojify-tests-should-be-emojified (line-beginning-position 2)))

  (emojify-tests-with-emojified-static-buffer "8)"
    ;; org-mode in Emacs v24.3 failed in read only buffers
    ;; if first item was not a headline
    (with-mock (stub org-set-startup-visibility => nil)
               (org-mode))
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (point-min)))

  (emojify-tests-with-emojified-static-buffer "* 8)"
    (org-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (1- (point-max))))

  (emojify-tests-with-emojified-static-buffer "#+BEGIN_SRC emacs-lisp\n:)\n#+END_SRC"
    (org-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (line-beginning-position 2)))

  ;; TODO: This does not work yet
  ;; (emojify-tests-with-emojified-static-buffer "8) 8)"
  ;;   (org-mode)
  ;;   (emojify-redisplay-emojis-in-region)
  ;;   (emojify-tests-should-be-emojified (1- (point-max)))
  ;;   (emojify-tests-should-not-be-emojified (1+ (point-min))))

  ;; 8) should not emojified if it is a list item
  (emojify-tests-with-emojified-static-buffer "7) *)
8) 8)
9) :/"
    (org-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (line-beginning-position 2))
    (emojify-tests-should-be-emojified (1- (line-end-position 2))))

  ;; Emojis that are part of org-mode tags should not be emojified
  (emojify-tests-with-emojified-static-buffer "* Test :p\n* Test2 :p:"
    (org-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-be-emojified (1- (line-end-position)))
    (emojify-tests-should-not-be-emojified (- (line-end-position 2) 3)))

  (emojify-tests-with-emojified-static-buffer "* Test :books:\n:books:"
    (org-agenda-mode)
    (emojify-redisplay-emojis-in-region)
    (emojify-tests-should-not-be-emojified (1- (line-end-position)))
    (emojify-tests-should-be-emojified (line-beginning-position 2))))

(ert-deftest emojify-tests-uncover-on-isearch ()
  :tags '(isearch)
  (emojify-tests-with-emojified-buffer "Testing isearch\n:books:"
    (with-mock
      (setq emojify-reveal-on-isearch t)
      ;; We do not want to be bothered with isearch messages
      (stub message => nil)
      (emojify-tests-should-be-emojified (line-beginning-position 2))
      (isearch-mode +1)
      (execute-kbd-macro "boo")
      ;; Emoji should be uncovered when point enters it in isearch-mode
      (emojify-tests-should-be-uncovered (line-beginning-position))
      ;; Emoji should be restored on leaving the underlying text
      (execute-kbd-macro "")
      (emojify-tests-should-be-emojified (line-beginning-position 2))

      ;; Turn off revealing on isearch
      (setq emojify-reveal-on-isearch nil)
      ;; We do not want to be bothered with isearch messages
      (stub message => nil)
      (emojify-tests-should-be-emojified (line-beginning-position 2))
      (isearch-mode +1)
      (execute-kbd-macro "boo")
      ;; Emoji should be uncovered when point enters it in isearch-mode
      (emojify-tests-should-be-emojified (line-beginning-position)))))

(ert-deftest emojify-tests-electric-delete ()
  :tags '(electric-delete)
  (emojify-tests-with-emojified-buffer "Unicode emoji 😉\nGithub emoji :wink:\nAscii emoji ;)"
    (goto-char (line-end-position))
    (let ((final-line-end (get-text-property (1- (point)) 'emojify-beginning)))
      (execute-kbd-macro [backspace])
      (emojify-tests-should-not-be-emojified (line-end-position))
      (should (equal (copy-marker (line-end-position)) final-line-end))))

  (emojify-tests-with-emojified-buffer "Unicode emoji 😉\nGithub emoji :wink:\nAscii emoji ;)"
    (goto-char (line-end-position 2))
    (let ((final-line-end (get-text-property (1- (point)) 'emojify-beginning)))
      (execute-kbd-macro [backspace])
      (emojify-tests-should-not-be-emojified (line-end-position))
      (should (equal (copy-marker (line-end-position)) final-line-end))))

  (emojify-tests-with-emojified-buffer "Unicode emoji 😉\nGithub emoji :wink:\nAscii emoji ;)"
    (goto-char (line-end-position 3))
    (let ((final-line-end (get-text-property (1- (point)) 'emojify-beginning)))
      (execute-kbd-macro [backspace])
      (emojify-tests-should-not-be-emojified (line-end-position))
      (should (equal (copy-marker (line-end-position)) final-line-end))))

  (emojify-tests-with-emojified-buffer ";) 😉:wink:"
    (dotimes (n 4)
      (execute-kbd-macro (kbd "C-d"))
      (emojify-redisplay-emojis-in-region))
    (should (equal (point-min) (point-max))))

  (emojify-tests-with-emojified-buffer "😉:wink: ;)"
    (goto-char (point-max))
    (dotimes (_ 4)
      (execute-kbd-macro [backspace]))
    (should (equal (point-min) (point-max))))

  (emojify-tests-with-emojified-buffer "😉  :smile:"
    (goto-char (1+ (point-min)))
    (dotimes (_ 3)
      (execute-kbd-macro (kbd "C-d"))
      (emojify-redisplay-emojis-in-region))
    (should (equal (1+ (point-min)) (point-max))))

  (emojify-tests-with-emojified-buffer "😉:wink: ;)"
    "Integration with delsel mode"
    (with-mock
      (stub message => nil)
      (delete-selection-mode +1)
      (set-mark-command nil)
      (activate-mark)
      (goto-char (point-max))
      (exchange-point-and-mark)
      (let ((this-command 'emojify-delete-emoji-forward))
        (delete-selection-pre-hook))
      (should (equal (point-min) (point-max))))))

(ert-deftest emojify-tests-prettify-symbols ()
  :tags '(prettify-symbols)
  (when (fboundp 'prettify-symbols-mode)
    (emojify-tests-with-emojified-static-buffer "try:
    x = 1
except:
    raise(Exception)
lambdalambda
\"lambda\"
yield 3
return 4
"
      (setq emojify-composed-text-p t)
      (emojify-set-emoji-styles '(ascii unicode github))
      (python-mode)
      (setq-local prettify-symbols-alist
                  '(("return" . ?↪)
                    ("try" . ?😱)
                    ("except" . ?⛐)
                    ("raise" . ?💥)))
      (emojify-tests-should-not-be-emojified (point-min))
      (emojify-tests-should-not-be-emojified (line-beginning-position 3))
      (emojify-tests-should-not-be-emojified (+ (line-beginning-position 4) 5))
      (emojify-tests-should-not-be-emojified (line-beginning-position 5))
      (emojify-tests-should-not-be-emojified (line-beginning-position 6))
      (emojify-tests-should-not-be-emojified (line-beginning-position 7))
      (emojify-tests-should-not-be-emojified (line-beginning-position 8))
      (prettify-symbols-mode +1)
      ;; On Emacs 25.1 fontification does not happen automatically
      (when (fboundp 'font-lock-ensure)
        (font-lock-ensure)
        (emojify-redisplay-emojis-in-region))
      (emojify-tests-should-be-emojified (point-min))
      (should (equal (get-text-property (point-min) 'emojify-text) "😱"))
      (emojify-tests-should-not-be-emojified (line-beginning-position 3))
      (emojify-tests-should-be-emojified (+ (line-beginning-position 4) 5))
      (should (equal (get-text-property (+ (line-beginning-position 4) 5) 'emojify-text) "💥"))
      (emojify-tests-should-not-be-emojified (line-beginning-position 5))
      (emojify-tests-should-not-be-emojified (line-beginning-position 6))
      (emojify-tests-should-not-be-emojified (line-beginning-position 7))
      (emojify-tests-should-be-emojified (line-beginning-position 8))
      (should (equal (get-text-property (line-beginning-position 8) 'emojify-text) "↪"))
      (prettify-symbols-mode -1)
      ;; On Emacs 25.1 fontification does not happen automatically
      (when (fboundp 'font-lock-ensure)
        (font-lock-ensure)
        (emojify-redisplay-emojis-in-region))
      (emojify-tests-should-not-be-emojified (point-min))
      (emojify-tests-should-not-be-emojified (line-beginning-position 3))
      (emojify-tests-should-not-be-emojified (+ (line-beginning-position 4) 5))
      (emojify-tests-should-not-be-emojified (line-beginning-position 6))
      (emojify-tests-should-not-be-emojified (line-beginning-position 5))
      (emojify-tests-should-not-be-emojified (line-beginning-position 6))
      (emojify-tests-should-not-be-emojified (line-beginning-position 7)))))

(ert-deftest emojify-tests-prettify-symbols-with-custom-images ()
  :tags '(prettify-symbols)
  (when (fboundp 'prettify-symbols-mode)
    (let ((emojify-user-emojis emojify-test-custom-emojis))
      (emojify-set-emoji-data)
      (emojify-tests-with-emojified-static-buffer "try:
    lambda x: x
except:
    raise(Exception)

yield 3
return 4
"
        (setq emojify-composed-text-p t)
        (emojify-set-emoji-styles '(ascii unicode github))
        (python-mode)
        (setq-local prettify-symbols-alist
                    '(("return" . ?↪)
                      ("try" . ?😱)
                      ("except" . ?⛐)
                      ("lambda" . ?λ)
                      ("raise" . ?💥)))
        (emojify-tests-should-not-be-emojified (+ (line-beginning-position 2) 5))
        (prettify-symbols-mode +1)
        ;; On Emacs 25.1 fontification does not happen automatically
        (when (fboundp 'font-lock-ensure)
          (font-lock-ensure)
          (emojify-redisplay-emojis-in-region))
        (emojify-tests-should-be-emojified (point-min))
        (emojify-tests-should-be-emojified (+ (line-beginning-position 2) 5))
        (emojify-tests-should-not-be-emojified (line-beginning-position 3))
        (emojify-tests-should-be-emojified (+ (line-beginning-position 4) 5))
        (emojify-tests-should-not-be-emojified (line-beginning-position 6))
        (emojify-tests-should-be-emojified (line-beginning-position 7))))))

(ert-deftest emojify-tests-apropos ()
  :tags '(apropos)
  (emojify-apropos-emoji "squi")
  ;; Window with results should be visible
  (with-mock
    (stub message => nil)
    (should (get-buffer-window emojify-apropos-buffer-name))
    (let ((matches 0))

      (with-current-buffer emojify-apropos-buffer-name
        ;; Force a display of emojis
        (emojify-redisplay-emojis-in-region (point-min) (point-max))
        (emojify-do-for-emojis-in-region (point-min) (point-max)
          (goto-char emoji-start)
          (call-interactively #'emojify-apropos-copy-emoji)
          (should (string= (car kill-ring) (get-text-property (point) 'emojify-text)))
          (cl-incf matches)))

      (should (= matches 2)))

    ;; Test with custom emoji
    (let ((emojify-user-emojis emojify-test-custom-emojis)
          (matches 0))

      (emojify-set-emoji-data)
      (emojify-apropos-emoji "lambda")
      (should (get-buffer-window emojify-apropos-buffer-name))

      (with-current-buffer emojify-apropos-buffer-name
        (emojify-redisplay-emojis-in-region (point-min) (point-max))
        (emojify-do-for-emojis-in-region (point-min) (point-max)
          (goto-char emoji-start)
          (call-interactively #'emojify-apropos-copy-emoji)
          (should (string= (car kill-ring) (get-text-property (point) 'emojify-text)))
          (cl-incf matches)))

      (should (= matches 1)))))

(ert-deftest emojify-tests-no-byte-compilation-warnings ()
  :tags '(byte-compilation)
  (with-mock
    (stub message => nil)
    (stub byte-compile-dest-file => "/tmp/emojify.elc")
    (should (byte-compile-file (locate-library "emojify.el")))))

;; So that tests can be run simply by doing `eval-buffer'
(unless noninteractive
  (ert "^emojify-"))

(provide 'emojify-test)
;;; emojify-test.el ends here
