;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-
(load (concat (file-name-directory (or load-file-name (buffer-file-name)
                                       default-directory))
              "utils.el") nil 'nomessage 'nosuffix)


(defun expect-filled-as (strs etalon &optional look-at)
  (let ((result-str (lua-buffer-strs
                     (let ((fill-column 10))
                       (lua-insert-goto-<> strs)
                       (execute-kbd-macro (kbd "M-q"))
                       (when look-at
                         (expect (point) :to-precede look-at))))))
    (expect result-str :to-equal etalon)))



(describe "Test fill-paragraph"
  (it "fills single-line comment"
    (expect-filled-as '("<>-- foo bar baz qux")
                      '("-- foo bar"
                        "-- baz qux")
                      "-- foo bar"))
  (it "fills comment after code"
    (expect-filled-as '("<>foo -- bar baz")
                      '("foo -- bar"
                        "    -- baz")))
  (xit "fills multiline comment"
    ;; Right now it ends up with something like this:
    ;;
    ;; --[[ ab c
    ;; --d ]]
    (expect-filled-as '("<>--[[ ab c d ]]")
                      '("--[[ ab c"
                        "     d ]]")))
  (it "does not spill comments into code (issue #25)"
    (expect-filled-as '("<>"
                        "-- foo bar baz qux"
                        "foo_func()")
                      '(""
                        "-- foo bar"
                        "-- baz qux"
                        "foo_func()"))))


(describe "Test fill-paragraph preserves point position"
  (it "doesn't move point if nothing has changed"
    (expect-filled-as '("<>-- foo bar")
                      '("-- foo bar")
                      "-- foo bar")

    (expect-filled-as '("-- <>foo bar")
                      '("-- foo bar")
                      "foo bar")

    (expect-filled-as '("-- foo <>bar")
                      '("-- foo bar")
                      "bar"))

  (it "doesn't move point in refilled region"
    (expect-filled-as '("--<> foo bar baz qux")
                      '("-- foo bar"
                        "-- baz qux")
                      " foo bar\n")

    (expect-filled-as '("-- <>foo bar baz qux")
                      '("-- foo bar"
                        "-- baz qux")
                      "foo bar\n")

    (expect-filled-as '("-- <>   foo bar baz qux")
                      '("--    foo"
                        "--    bar"
                        "--    baz"
                        "--    qux")
                      "   foo\n")

    (expect-filled-as '("-- foo bar <>baz qux")
                      '("-- foo bar"
                        "-- baz qux")
                      "baz qux")
    (expect-filled-as '("-- foo bar<> baz qux")
                      '("-- foo bar"
                        "-- baz qux")
                      "\n-- baz qux")

    (expect-filled-as '("-- foo bar baz qux<>")
                      '("-- foo bar"
                        "-- baz qux")
                      "$")
    )

  (it "doesn't move point if nothing has changed (multi-line)"
    (expect-filled-as '("--[[ a <>b]]")
                      '("--[[ a b]]")
                      "b]]")

    (expect-filled-as '("--[[ a<>"
                        "     b"
                        "]]")
                      '("--[[ a"
                        "     b"
                        "]]")
                      "\n     b\n]]")

    )
  )
