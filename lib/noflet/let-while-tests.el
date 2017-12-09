;;; let-while-tests.el -- tests for the let-while macro


(defun let-while-test ()
  (catch :io
    (let ((lines '("line 1" "line 2")))
      (noflet ((get-line ()
                 (or
                  (pop lines)
                  (throw :io :eof))))
        (let-while (line (get-line))
          (message "the line is: %s" line))))))


;;; let-while-tests.el ends here
