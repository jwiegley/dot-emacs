;;;
;;; persistent-soft.el tests -- basic
;;;
;;; Directory "test_output" should not yet exist when this test is run.
;;;
;;; todo - set pcache-directory location when load-file-name is not set,
;;;        restore to original value after testing

;;; requires and setup

(when load-file-name
  (setq pcache-directory (expand-file-name "test_output/" (file-name-directory load-file-name)))
  (setq package-enable-at-startup nil)
  (setq package-load-list '((pcache t)
                            (list-utils t)))
  (when (fboundp 'package-initialize)
    (package-initialize)))

(require 'list-utils)
(require 'persistent-soft)


;;; features

(ert-deftest persistent-soft-a:a-feature-01 nil
  (should (featurep 'pcache)))


;;; files and locations

(ert-deftest persistent-soft-a:b-files-01 nil
  "Any number of later tests could fail if the test_output directory already exists at this point."
  (should-not
   (file-exists-p pcache-directory)))

(ert-deftest persistent-soft-a:b-files-02 nil
  "Any number of later tests could fail if the ert-test-persistent-soft-location-1 data store exists at this point."
  (should
   (persistent-soft-location-destroy "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:b-files-03 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should
   (persistent-soft-location-destroy "ert-test-persistent-soft-location-2")))

(ert-deftest persistent-soft-a:b-files-04 nil
  "Any number of later tests could fail if the ert-test-persistent-soft-location-1 data store exists at this point."
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:b-files-05 nil
  "ert-test-persistent-soft-location-2 is never supposed to exist"
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-2")))


;;; nonexistent location

(ert-deftest persistent-soft-a:c-nonexistent-location-01 nil
  (should-not
   (persistent-soft-exists-p 'nonexistent-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:c-nonexistent-location-02 nil
  (should-not
   (persistent-soft-fetch 'nonexistent-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:c-nonexistent-location-03 nil
  (should-not
   (persistent-soft-location-readable "ert-test-persistent-soft-location-1")))


;;; nonexistent symbol

(ert-deftest persistent-soft-a:d-nonexistent-key-01 nil
  ;; ert-test-persistent-soft-location-1 is created here
  (should
   (persistent-soft-store 'actual-key t "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:d-nonexistent-key-02 nil
  (should
   (persistent-soft-location-readable "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:d-nonexistent-key-03 nil
  (should-not
   (persistent-soft-exists-p 'nonexistent-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:d-nonexistent-key-04 nil
  (should-not
   (persistent-soft-fetch 'nonexistent-key "ert-test-persistent-soft-location-1")))


;;; existing symbol

(ert-deftest persistent-soft-a:e-existing-key-01 nil
  (should
   (persistent-soft-exists-p 'actual-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:e-existing-key-02 nil
  (should
   (persistent-soft-exists-p 'actual-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:e-existing-key-03 nil
  (should
   (persistent-soft-fetch 'actual-key "ert-test-persistent-soft-location-1")))


;;; nonexistent location when another location does exist

(ert-deftest persistent-soft-a:f-nonexistent-location-01 nil
  (should-not
   (persistent-soft-exists-p 'actual-key "ert-test-persistent-soft-location-2")))

(ert-deftest persistent-soft-a:f-nonexistent-location-02 nil
  (should-not
   (persistent-soft-fetch 'actual-key "ert-test-persistent-soft-location-2")))


;;; data types

(ert-deftest persistent-soft-a:g-data-types-01 nil
  (let ((value "string"))
    (should
     (persistent-soft-store 'string-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'string-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'string-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-02 nil
  (let ((value "string with properties"))
    (callf propertize value :face 'bold)
    (should
     (persistent-soft-store 'string-with-properties-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'string-with-properties-key "ert-test-persistent-soft-location-1"))
    (should (equal-including-properties value
                   (persistent-soft-fetch 'string-with-properties-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-03 nil
  (let ((value '(1 2 "3")))
    (should
     (persistent-soft-store 'list-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-04 nil
  (let ((value '[1 2 "3"]))
    (should
     (persistent-soft-store 'vector-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'vector-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'vector-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-05 nil
  (let ((value (make-hash-table :test 'equal)))
    (dolist (num (number-sequence 1 1000))
      (puthash num (number-to-string num) value))
    (should
     (let ((persistent-soft-inhibit-sanity-checks t))
       ;; inhibiting sanity check keeps the stored hash from being copied,
       ;; allowing `equal' to work below
       (persistent-soft-store 'hash-key value "ert-test-persistent-soft-location-1")))
    (should
     (persistent-soft-exists-p 'hash-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'hash-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-06 nil
  (let ((value '(1 2 ("3" (4 nil) 7 (8 (8 (8 8))) '[9 9 9]))))
    (should
     (persistent-soft-store 'list-of-lists-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'list-of-lists-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'list-of-lists-key "ert-test-persistent-soft-location-1")))))

;; although the cyclic list is truncated on storage, including
;; this failed test at least assures that the data store is not
;; corrupted by the attempt
(ert-deftest persistent-soft-a:g-data-types-07 nil
  "Todo: correctly reconstitute cyclic lists"
  :expected-result :failed
  (let ((value '(a b c d e f g h)))
    (nconc value value)
    (should
     (persistent-soft-store 'cyclic-list-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'cyclic-list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'cyclic-list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-08 nil
  (let ((value '[1 2 [3 4 5] [6 [7 [8 9]]]]))
    (should
     (persistent-soft-store 'vector-of-vectors-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'vector-of-vectors-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'vector-of-vectors-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-09 nil
  (let ((value 3))
    (should
     (persistent-soft-store 'integer-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'integer-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'integer-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-10 nil
  (let ((value 3.14))
    (should
     (persistent-soft-store 'float-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'float-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'float-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-11 nil
  (let ((value 'symbol))
    (should
     (persistent-soft-store 'symbol-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'symbol-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'symbol-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-12 nil
  (let ((value (with-temp-buffer
                 (emacs-lisp-mode)
                 (syntax-table))))
    (should
     (persistent-soft-store 'char-table-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'char-table-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'char-table-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-13 nil
  (let ((value (make-bool-vector 10 nil)))
    (should
     (persistent-soft-store 'bool-vector-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'bool-vector-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'bool-vector-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-14 nil
  (let ((value #'(lambda () t)))
    (should
     (persistent-soft-store 'lambda-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'lambda-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'lambda-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-15 nil
  (let ((value (make-byte-code '(args) nil nil 0)))
    (should
     (persistent-soft-store 'byte-code-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'byte-code-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'byte-code-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-16 nil
  (let ((value (make-tconc)))
    (tconc-list value '(1 2 3))
    (tconc-list value '(4 5))
    (should
     (persistent-soft-store 'defstruct-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'defstruct-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'defstruct-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-17 nil
  (let ((value (make-sparse-keymap)))
    (define-key value (kbd "a") 'ignore)
    (should
     (persistent-soft-store 'keymap-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'keymap-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'keymap-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:g-data-types-18 nil
  (defclass tester-class nil
    ((uid)))
  (let ((value (tester-class "my_id")))
    (should
     (persistent-soft-store 'object-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'object-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'object-key "ert-test-persistent-soft-location-1")))))


;;; invalid data types

(ert-deftest persistent-soft-a:h-invalid-data-types-01 nil
  (let ((value (get-buffer "*scratch*")))
    (should
     (persistent-soft-store 'buffer-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'buffer-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'buffer-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-02 nil
  (let ((value (selected-window)))
    (should
     (persistent-soft-store 'window-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'window-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'window-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-03 nil
  (let ((value (selected-frame)))
    (should
     (persistent-soft-store 'frame-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'frame-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'frame-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-04 nil
  (let ((value (make-overlay 1 1)))
    (should
     (persistent-soft-store 'overlay-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'overlay-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'overlay-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-05 nil
  (let ((value (start-process "tester-sleeper" "*tester-sleeper*" "sleep" "10")))
    (should
     (persistent-soft-store 'process-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'process-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'process-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-06 nil
  (let ((value (make-marker)))
    (move-marker value 1)
    (should
     (persistent-soft-store 'marker-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'marker-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'marker-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-07 nil
  :tags '(:interactive)
  (let ((value (current-window-configuration)))
    (should
     (persistent-soft-store 'window-config-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'window-config-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'window-config-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-08 nil
  :tags '(:interactive)
  (let ((value (find-font (font-spec :name "Courier"))))
    (should
     (persistent-soft-store 'font-obj-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'font-obj-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'font-obj-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:h-invalid-data-types-09 nil
  :tags '(:interactive)
  (let ((value (current-frame-configuration)))
    (should
     (persistent-soft-store 'buffer-key value "ert-test-persistent-soft-location-1"))
    (should
     (persistent-soft-exists-p 'buffer-key "ert-test-persistent-soft-location-1"))
    (should (stringp
             (persistent-soft-fetch 'buffer-key "ert-test-persistent-soft-location-1")))))

;; todo this type is not serializable, but there isn't a test for it in persistent-soft
;;
;; (ert-deftest persistent-soft-a:h-invalid-data-types-10 nil
;;   (let ((value (selected-terminal)))
;;     (should
;;      (persistent-soft-store 'terminal-key value "ert-test-persistent-soft-location-1"))
;;     (should
;;      (persistent-soft-exists-p 'terminal-key "ert-test-persistent-soft-location-1"))
;;     (should (stringp
;;                    (persistent-soft-fetch 'terminal-key "ert-test-persistent-soft-location-1")))))


;;; expiration

(ert-deftest persistent-soft-a:i-expiration-01 nil
  (should
   (persistent-soft-store 'expiring-key t "ert-test-persistent-soft-location-1" 2)))

(ert-deftest persistent-soft-a:i-expiration-02 nil
  (should
   (persistent-soft-exists-p 'expiring-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:i-expiration-03 nil
  (should
   (persistent-soft-fetch 'expiring-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:i-expiration-04 nil
  (message "sleeping momentarily for expiration test...")
  (sleep-for 3)
  (should-not
   (persistent-soft-exists-p 'expiring-key "ert-test-persistent-soft-location-1")))

(ert-deftest persistent-soft-a:i-expiration-05 nil
  (should-not
   (persistent-soft-fetch 'expiring-key "ert-test-persistent-soft-location-1")))


;;; large data sets -- todo fetch these in further test modules

(ert-deftest persistent-soft-a:j-large-values-01 nil
  "Long list without sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 100000 200000))))
    (should
     (let ((persistent-soft-inhibit-sanity-checks t))
       (persistent-soft-store 'long-list-key value "ert-test-persistent-soft-location-1")))
    (should
     (persistent-soft-exists-p 'long-list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'long-list-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:j-large-values-02 nil
  "Long list with sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 100000 200000))))
    (should
     (let ((persistent-soft-inhibit-sanity-checks nil))
       (persistent-soft-store 'long-list-sanitized-key value "ert-test-persistent-soft-location-1")))
    (should
     (persistent-soft-exists-p 'long-list-sanitized-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'long-list-sanitized-key "ert-test-persistent-soft-location-1")))))

(ert-deftest persistent-soft-a:j-large-values-03 nil
  "Deep list without sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 1 10))))
    (dotimes (i 10)
      (push value value))
    (should
     (let ((persistent-soft-inhibit-sanity-checks t))
       (persistent-soft-store 'deep-list-key value "ert-test-persistent-soft-location-1")))
    (should
     (persistent-soft-exists-p 'deep-list-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'deep-list-key "ert-test-persistent-soft-location-1")))))

;; todo sanitization not efficient enough, this takes forever if the list is 20 deep
(ert-deftest persistent-soft-a:j-large-values-04 nil
  "Deep list with sanity check"
  (let ((value (mapcar 'number-to-string (number-sequence 1 10))))
    (dotimes (i 10)
      (push value value))
    (should
     (let ((persistent-soft-inhibit-sanity-checks nil))
       (persistent-soft-store 'deep-list-sanitized-key value "ert-test-persistent-soft-location-1")))
    (should
     (persistent-soft-exists-p 'deep-list-sanitized-key "ert-test-persistent-soft-location-1"))
    (should (equal value
                   (persistent-soft-fetch 'deep-list-sanitized-key "ert-test-persistent-soft-location-1")))))


;;; sanitize - todo complex function should have more tests

(ert-deftest persistent-soft-a:k-sanitize-01 nil
  (let ((value '(1 2 3)))
    (should (equal value
                   (persistent-soft--sanitize-data value)))))

(ert-deftest persistent-soft-a:k-sanitize-02 nil
  (let ((value '[1 2 3]))
    (should (equal value
                   (persistent-soft--sanitize-data value)))))

(ert-deftest persistent-soft-a:k-sanitize-03 nil
  (let ((value '(1 2 (3 4 nil) nil)))
    (should (equal value
                   (persistent-soft--sanitize-data value)))))

(ert-deftest persistent-soft-a:k-sanitize-04 nil
  (let ((value '[1 2 [] [4 5 6] nil [nil]]))
    (should (equal value
                   (persistent-soft--sanitize-data value)))))

(ert-deftest persistent-soft-a:k-sanitize-05 nil
  (let ((value '[1 2 [] [4 5 6] (7 8 (9 10)) nil [nil]]))
    (should (equal value
                   (persistent-soft--sanitize-data value)))))

(ert-deftest persistent-soft-a:k-sanitize-06 nil
  (with-current-buffer "*scratch*"
    (let ((value `[1 2 [] [4 5 6] (7 ,(current-buffer) (9 10)) nil [nil]]))
      (should (equal '[1 2 [] [4 5 6] (7 "*scratch*" (9 10)) nil [nil]]
                     (persistent-soft--sanitize-data value))))))

(ert-deftest persistent-soft-a:k-sanitize-07 nil
  (with-current-buffer "*scratch*"
    (let ((value (make-hash-table)))
      (puthash 1 (current-buffer) value)
      (should (equal "*scratch*"
                     (gethash 1 (persistent-soft--sanitize-data value)))))))


;;; flush

(ert-deftest persistent-soft-a:z-flush-01 nil
  (should
   (persistent-soft-flush "ert-test-persistent-soft-location-1")))


;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions)
;; End:
;;

;;; persistent-soft-a-test.el ends here
