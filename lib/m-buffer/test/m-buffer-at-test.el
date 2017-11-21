(require 'm-buffer-at)

(ert-deftest m-buffer-at-eolp-1()
  (should
   (with-temp-buffer
     (insert "hello")
     (m-buffer-at-eolp (point-marker)))))

(ert-deftest m-buffer-at-eolp-2 ()
  (should
   (with-temp-buffer
     (insert "hello")
     (m-buffer-at-eolp
      (current-buffer)
      (point)))))

(ert-deftest m-buffer-at-eolp-3 ()
  (should-not
   (with-temp-buffer
     (insert "hello")
     (goto-char (point-min))
     (m-buffer-at-eolp (point-marker)))))

(ert-deftest m-buffer-at-eolp-4 ()
  (should-not
   (with-temp-buffer
     (insert "hello")
     (goto-char (point-min))
     (m-buffer-at-eolp
      (current-buffer)
      (point)))))

(ert-deftest m-buffer-string ()
  (should
   (string=
    "hello"
    (with-temp-buffer
      (insert "hello")
      (m-buffer-at-string (current-buffer))))))
