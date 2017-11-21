(require 'ert)
(require 'undercover)
(undercover "guide-key.el")

(require 'guide-key)
(eval-when-compile
  (require 'cl))

(defconst guide-key-test/global-keybindings
  '((1 . guide-key-test/global-keybinding1)
    (2 . guide-key-test/global-keybinding2)))

(defconst guide-key-test/prefix-key (kbd "s-S-C-M-x"))

(defmacro guide-key-test/deftest (name doc-string &rest body)
  (declare (indent 1)
           (doc-string 2))
  `(ert-deftest ,(intern (concat "guide-key-test/" (symbol-name name))) ()
     ,doc-string
     ;; setup
     (loop for (event . definition) in guide-key-test/global-keybindings
           do
           (global-set-key (vconcat guide-key-test/prefix-key (vector event)) definition))
     ;; test
     ,@body
     ;; teardown
     (loop for (event . definition) in guide-key-test/global-keybindings
           do
           (global-unset-key (vconcat guide-key-test/prefix-key (vector event))))
     ))

(guide-key-test/deftest setup-test
  "Assert that setup is done successfully."
  (should (same-keymap-p (keymap-canonicalize (key-binding guide-key-test/prefix-key))
                         (cons 'keymap guide-key-test/global-keybindings))))

(ert-deftest guide-key-test/get-highlight-face ()
  "Test of `guide-key/get-highlight-face'"
  (let ((guide-key/highlight-command-regexp
         '("rectangle"
           ("register" . font-lock-type-face)
           ("bookmark" . font-lock-warning-face)
           ("anonymous" . "hot pink") ; specify a color name
           ))
        (fixtures
         '(("Prefix Command" . guide-key/prefix-command-face)
           ("string-rectangle" . guide-key/highlight-command-face)
           ("jump-to-register" . font-lock-type-face)
           ("bookmark-jump" . font-lock-warning-face)
           ("copy-rectangle-to-register" . guide-key/highlight-command-face)
           ("anonymous-command" . (:foreground "hot pink")) ; anonymous face
           ("<NOTEXIST>" . nil)
           ))
        actual)
    (loop for (input . expected) in fixtures
          do
          (setq actual (guide-key/get-highlight-face input))
          (should (equal actual expected)))
    ))

(defun same-keymap-p (keymap1 keymap2)
  "Return if two KEYMAPs are the same.

This matcher ignores an order of alist (cdr of keymap)."
  (and (keymapp keymap1) (keymapp keymap2)
       (flet ((keymap-sorter (e1 e2) (< (car e1) (car e2))))
         (equal (sort (cdr keymap1) 'keymap-sorter)
                (sort (cdr keymap2) 'keymap-sorter)))))

