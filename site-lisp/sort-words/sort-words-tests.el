(load-file "sort-words.el")
(require 'ert)

(defun set-up-line (str keys start end)
  "STR populate the buffer with
   KEYS are commands to type
   START & END are points from which the content of the buffer should be returned"
  (with-temp-buffer
    (insert str)
    (save-window-excursion
      (set-window-buffer nil (current-buffer))
      (goto-char (point-min))
      (execute-kbd-macro (kbd keys)))
    (buffer-substring start end)))

(defconst buffer-content "zz bb aa 1\nfoo bar")

(ert-deftest sort-words-test ()
  "sort words test"
  (should (string= "1 aa bb zz"
                   (set-up-line buffer-content
                                "C-SPC C-e M-x sort-words"
                                1
                                11)))
  (should (string= "bar foo"
                   (set-up-line buffer-content
                                "C-n C-SPC C-e M-x sort-words"
                                12
                                19))))

(ert-deftest sort-words-on-multiple-lines ()
  "sort words on multiple lines, don't respect the newline"
  (should (string= "1 aa bar bb foo zz"
                   (set-up-line buffer-content
                                "C-SPC C-n C-e M-x sort-words"
                                1
                                19))))
