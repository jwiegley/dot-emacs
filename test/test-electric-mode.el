;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-

(load (concat (file-name-directory (or load-file-name (buffer-file-name)
                                       default-directory))
              "utils.el") nil 'nomessage 'nosuffix)

(require 'lua-mode)


(describe "Test electric mode"
  (it "works with curly braces"
    (with-lua-buffer
     (lua--setq-local blink-matching-paren nil)
     (make-local-variable 'electric-indent-mode)
     (electric-indent-mode 1)
     (execute-kbd-macro (kbd "return SPC foo SPC { M-j"))
     (execute-kbd-macro (kbd "'baz' M-j"))
     (expect (current-indentation) :to-be lua-indent-level)

     (execute-kbd-macro (kbd "}"))
     (expect (current-indentation) :to-be 0)))

  (it "works with parentheses"
    (with-lua-buffer
     (lua--setq-local blink-matching-paren nil)
     (make-local-variable 'electric-indent-mode)
     (electric-indent-mode 1)
     (execute-kbd-macro (kbd "return SPC foo SPC ( M-j"))
     (execute-kbd-macro (kbd "'baz' M-j"))
     (should (eq (current-indentation) lua-indent-level))

     (execute-kbd-macro (kbd ")"))
     (should (eq (current-indentation) 0))))

  (it "works with end"
    (with-lua-buffer
     (execute-kbd-macro (kbd "if SPC foo SPC then M-j"))
     (execute-kbd-macro (kbd "'baz' M-j"))
     (should (eq (current-indentation) lua-indent-level))

     (abbrev-mode 1)
     (execute-kbd-macro (kbd "end M-j"))
     (beginning-of-line 0)
     (should (eq (current-indentation) 0))))


  (it "works with else"
    (with-lua-buffer
     (execute-kbd-macro (kbd "if SPC foo SPC then M-j"))
     (execute-kbd-macro (kbd "'baz' M-j"))
     (should (eq (current-indentation) lua-indent-level))

     (abbrev-mode 1)
     (execute-kbd-macro (kbd "else M-j"))
     (beginning-of-line 0)
     (should (eq (current-indentation) 0))))


  (it "works with elseif"
    (with-lua-buffer
     (execute-kbd-macro (kbd "if SPC foo SPC then"))
     (newline-and-indent)
     (execute-kbd-macro (kbd "'baz'"))
     (newline-and-indent)
     (should (eq (current-indentation) lua-indent-level))

     (abbrev-mode 1)
     (execute-kbd-macro (kbd "elseif"))
     (newline-and-indent)
     (beginning-of-line 0)
     (should (eq (current-indentation) 0)))))


(when (fboundp 'electric-pair-mode)
  (describe "Electric pair mode"
    (it "skips parens when electric-pair-skip-self is t"
      (let ((old-mode (if electric-pair-mode 1 0)))
        (unwind-protect
            (with-lua-buffer
             (lua--setq-local blink-matching-paren nil)
             (lua--setq-local electric-pair-skip-self t)
             (lua--setq-local lua-electric-flag t)
             (electric-pair-mode 1)
             (execute-kbd-macro "(")
             (should (string= (buffer-string) "()"))
             (execute-kbd-macro ")")
             (should (string= (buffer-string) "()")))
          (electric-pair-mode old-mode))))))
