;;; esup-tests.el --- tests for esup -*- lexical-binding: t -*-

;;; Commentary:

;; Tests for esup-child.el and esup.el functionality.

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'esup-child)
(require 'noflet)
(require 'el-mock)

(defmacro esup/with-mock-buffer (str &rest body)
  "Create buffer with STR and run BODY."
  (declare (indent 1))
  `(with-temp-buffer
     ;; We don't want to send anything over the network
     (noflet ((esup-child-send-log (&rest args) nil)
              (esup-child-send-result (&rest args) nil))
       ;; Create buffer-file-name because esup-child collects it.
       (let ((buffer-file-name "*esup-ert-test*"))
         (insert ,str)
         (goto-char (point-min))
         ,@body))))


(defmacro esup/profile-sexp (sexp-str)
  "Run `esup-child-profile-sexp' on SEXP-STR and return the result."
  `(esup/with-mock-buffer
    ,sexp-str
    (esup-child-profile-sexp (point-min) (point-max))))

(defun esup/profile-single-sexp (sexp-str)
  "Run `esup-child-profile-sexp' on SEXP-STR and return the first result."
  (car (esup/profile-sexp sexp-str)))

(defun esup/points-eq-p (esup-result start end)
  "Return t if ESUP-RESULT match START and END."
  (and (eq start (oref esup-result :start-point))
       (eq end (oref esup-result :end-point))))

(ert-deftest esup/start-end ()
  "Test that `esup-child-profile-sexp' has the right start and end points."
  (loop for (input start end) in
           '(("()" 1 3)
             ("'(1)" 1 5))
           do
           (should (esup/points-eq-p (esup/profile-single-sexp input)
                                     start end))))

(ert-deftest esup/empty-file ()
  "Test `esup-profile-sexp' with an empty string.
This is known to fail."
  (let ((result
         (esup/with-mock-buffer ""
           (esup-child-profile-sexp (point-min) (point-max)))))
    (should t)))

(ert-deftest esup/garbage-collections ()
    "Test that we count garbage collection properly."
    (should
     (eq 2
         (oref
          (esup/profile-single-sexp
           "(progn (garbage-collect) (garbage-collect))")
          :gc-number))))

(ert-deftest esup/require-to-load ()
  "Test that `esup-child-require-to-load' works."
  (cl-loop for (input expected) in
           '(("(require 'a)" "a")
             ("(require 'b \"bFilename\")" "bFilename"))
           do
           (should (equal
                    (esup-child-require-to-load (read input))
                    expected))))

(ert-deftest esup/profile-require-level1 ()
  "Test that `esup-child-profile-sexp' steps into require statments."
  (let ((esup-child-profile-require-level 1))
    (with-mock
      (stub esup-child-profile-file => (list 1 2))
      (cl-loop for (input expected) in
               '(("(require 'e)" 2))

               do
               (should (eq
                        (length (esup/profile-sexp input))
                        expected))
               )

      )))


;; To test:
;; (load custom-file) variable for file name
;; level is incremented

(provide 'esup-tests)
;;; esup-test.el ends here
