;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-

(load (concat (file-name-directory (or load-file-name (buffer-file-name)
                                       default-directory))
              "utils.el") nil 'nomessage 'nosuffix)

(defmacro should= (lhs rhs)
  `(should (equal ,lhs ,rhs)))

(describe "Test indent-new-comment-line"
  (it "works with -- ..."
    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("-- foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("-- foobar"
              "-- "))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("xyzzy -- foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("xyzzy -- foobar"
              "-- "))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("xyz<> xyzzy -- foobar"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("xyz"
              "xyzzy -- foobar")))


  (it "works with ---- ...."
    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("---- foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("---- foobar"
              "---- "))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("xyzzy ---- foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("xyzzy ---- foobar"
              "---- ")))

  (it "doesn't recognize \"--\" inside strings and comments"
    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("\"-- \" .. foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("\"-- \" .. foobar"
              ""))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("'-- ' .. foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("'-- ' .. foobar"
              ""))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("[[-- ]] .. foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("[[-- ]] .. foobar"
              ""))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("--[[-- ]] .. foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("--[[-- ]] .. foobar"
              ""))

    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("---[[-- ]] .. foobar <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("---[[-- ]] .. foobar"
              "---")))

  (it "works when the comment is empty"
    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("-- <>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("--"
              "--"))

    ;; Let's make sure that whitespace is optional.
    (expect (lua-buffer-strs
             (lua-insert-goto-<> '("--<>"))
             (execute-kbd-macro (kbd "M-j")))
            :to-equal
            '("--"
              "--"))))
