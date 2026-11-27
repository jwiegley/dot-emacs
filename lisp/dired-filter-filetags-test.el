;;; dired-filter-filetags-test.el --- Tests for tag filtering -*- lexical-binding: t; -*-

(require 'ert)
(add-to-list 'load-path
             (expand-file-name "dired-filetags" (file-name-directory (or load-file-name buffer-file-name))))
(require 'dired-filter-filetags)

(defmacro dired-filter-filetags-test--with-directory (&rest body)
  "Run BODY in a Dired buffer containing tagged and untagged files."
  (declare (indent 0) (debug t))
  `(let* ((dir (make-temp-file "dired-filter-filetags-" t))
          (dired-filter-stack nil)
          (dired-filter-verbose nil)
          buffer)
     (unwind-protect
         (progn
           (dolist (name '("one -- work urgent.txt" "two -- work.txt"
                           "three -- urgent.txt" "four.txt" "five -- working.txt"))
             (write-region "" nil (expand-file-name name dir) nil 'silent))
           (setq buffer (dired-noselect dir))
           (with-current-buffer buffer ,@body))
       (when (buffer-live-p buffer) (kill-buffer buffer))
       (delete-directory dir t))))

(defun dired-filter-filetags-test--present-p (name)
  "Return non-nil when NAME appears in the Dired listing."
  (save-excursion (dired-goto-file (expand-file-name name default-directory))))

(ert-deftest dired-filter-filetags-additive-and-negation ()
  (dired-filter-filetags-test--with-directory
    (should (eq (lookup-key dired-filter-map "t") 'dired-filter-by-filetags))
    (dired-filter-by-filetags "work")
    (should (dired-filter-filetags-test--present-p "one -- work urgent.txt"))
    (should (dired-filter-filetags-test--present-p "two -- work.txt"))
    (should-not (dired-filter-filetags-test--present-p "five -- working.txt"))
    (dired-filter-by-filetags "urgent")
    (should (dired-filter-filetags-test--present-p "one -- work urgent.txt"))
    (should-not (dired-filter-filetags-test--present-p "two -- work.txt"))
    (dired-filter-negate)
    (should-not (dired-filter-filetags-test--present-p "one -- work urgent.txt"))
    (should (dired-filter-filetags-test--present-p "two -- work.txt"))
    (should-not (dired-filter-filetags-test--present-p "four.txt"))
    (dired-filter-pop 1)
    (should (dired-filter-filetags-test--present-p "one -- work urgent.txt"))))

(ert-deftest dired-filter-filetags-or ()
  (dired-filter-filetags-test--with-directory
    (dired-filter-by-filetags "work")
    (dired-filter-by-filetags "urgent")
    (dired-filter-or)
    (should (dired-filter-filetags-test--present-p "two -- work.txt"))
    (should (dired-filter-filetags-test--present-p "three -- urgent.txt"))
    (should-not (dired-filter-filetags-test--present-p "four.txt"))))

(provide 'dired-filter-filetags-test)
;;; dired-filter-filetags-test.el ends here
