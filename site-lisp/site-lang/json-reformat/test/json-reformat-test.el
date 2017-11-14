(ert-deftest json-reformat-test:indent ()
  ;; default 4
  (should (string= "" (json-reformat:indent 0)))
  (should (string= "    " (json-reformat:indent 1)))
  (should (string= "        " (json-reformat:indent 2)))

  ;; specify `json-reformat:indent-width'
  (let ((json-reformat:indent-width 3))
    (should (string= "" (json-reformat:indent 0)))
    (should (string= "   " (json-reformat:indent 1)))
    (should (string= "      " (json-reformat:indent 2))))
  )

(ert-deftest json-reformat-test:number-to-string ()
  (should (string= "1" (json-reformat:number-to-string 1)))
  (should (string= "100" (json-reformat:number-to-string 100)))
  (should (string= "-1" (json-reformat:number-to-string -1)))
  )

(ert-deftest json-reformat-test:symbol-to-string ()
  (should (string= "true" (json-reformat:symbol-to-string t)))
  (should (string= "false" (json-reformat:symbol-to-string :json-false)))
  (should (string= "foo" (json-reformat:symbol-to-string 'foo)))
  (should (string= ":bar" (json-reformat:symbol-to-string :bar)))
  )

(ert-deftest json-reformat-test:vector-to-string ()
  (should (string= "\
\[
    1,
    2,
    3
\]" (json-reformat:vector-to-string [1 2 3] 0)))

  (should (string= "\
\[
        \"foo\",
        \"bar\",
        3
    \]" (json-reformat:vector-to-string ["foo" "bar" 3] 1)))

  (should (string= "\
\[
    1,
    \[
        2,
        \[
            3,
            4
        \],
        5
    \],
    6,
    []
\]" (json-reformat:vector-to-string [1 [2 [3 4] 5] 6 []] 0)))
  )

(ert-deftest json-reformat-test:string-to-string ()
  (should (string= "\"foobar\"" (json-reformat:string-to-string "foobar")))
  (should (string= "\"fo\\\"o\\nbar\"" (json-reformat:string-to-string "fo\"o\nbar")))
  (should (string= "\"\\u2661\"" (json-reformat:string-to-string "\u2661")))

  (should (string= "\"^(amq\\\\.gen.*|amq\\\\.default)$\"" (json-reformat:string-to-string "^(amq\\.gen.*|amq\\.default)$")))
  )

(ert-deftest json-reformat-test:string-to-string-when-pretty ()
  (let ((json-reformat:pretty-string? t))
    (should (string= "\"foobar\"" (json-reformat:string-to-string "foobar")))
    (should (string= "\"fo\\\"o
bar\"" (json-reformat:string-to-string "fo\"o\nbar")))
    (should (string= "\"♡\"" (json-reformat:string-to-string "\u2661")))

    (should (string= "\"^(amq\\\\.gen.*|amq\\\\.default)$\"" (json-reformat:string-to-string "^(amq\\.gen.*|amq\\.default)$")))
    ))

(ert-deftest json-reformat-test:print-node ()
  (should (string= "null" (json-reformat:print-node nil 0)))
  )

(ert-deftest json-reformat-test:tree-to-string ()
  (let ((info (make-hash-table :test 'equal)))
    (puthash "male" t info)
    (should (string= "\
{
    \"info\": {
        \"male\": true
    },
    \"age\": 33,
    \"name\": \"John Smith\"
}" (json-reformat:tree-to-string
    `("info" ,info "age" 33 "name" "John Smith") 0)))
    ))

(ert-deftest json-reformat-test:json-reformat-region ()
  (should (string= "\
{
    \"name\": \"John Smith\",
    \"age\": 33,
    \"breakfast\": \[
        \"milk\",
        \"bread\",
        \"egg\"
    \]
}" (with-temp-buffer
     (insert "{\"name\": \"John Smith\", \"age\": 33, \"breakfast\":\[\"milk\", \"bread\", \"egg\"\]}")
     (json-reformat-region (point-min) (point-max))
     (buffer-string))))

  (should (string= "\
\[
    {
        \"foo\": \"bar\"
    },
    {
        \"foo\": \"baz\"
    }
\]" (with-temp-buffer
     (insert "[{ \"foo\" : \"bar\" }, { \"foo\" : \"baz\" }]")
     (json-reformat-region (point-min) (point-max))
     (buffer-string))))

  (should (string= "\
{
    \"foo\": {
    },
    \"bar\": null
}" (with-temp-buffer
     (insert "{\"foo\" : {}, \"bar\" : null}")
     (json-reformat-region (point-min) (point-max))
     (buffer-string)))))

(ert-deftest json-reformat-test:json-reformat-region-occur-error ()
  (let (message-string)
    (cl-letf (((symbol-function 'message) (lambda (&rest args) (setq message-string (apply 'format args)))))
      ;; missing camma after "milk"
      (with-temp-buffer
        (insert "{\"name\": \"John Smith\", \"age\": 33, \"breakfast\":\[\"milk\" \"bread\", \"egg\"\]}")
        (json-reformat-region (point-min) (point-max)))
      (should (string=
               "JSON parse error [Reason] Unknown JSON error: bleah [Position] In buffer, line 1 (char 55)"
               message-string))

      ;; The `foo' key don't start with '"'
      (with-temp-buffer
        (insert "\


[{ foo : \"bar\" }, { \"foo\" : \"baz\" }]") ;; At 3 (line)
        (json-reformat-region (point-min) (point-max)))
      (should (string=
               "JSON parse error [Reason] Bad string format: \"doesn't start with '\\\"'!\" [Position] In buffer, line 3 (char 6)"
               message-string))
      )))
