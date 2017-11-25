;;; elisp-refs-bench.el --- measure elisp-refs.el performance

;;; Code:

(require 'elisp-refs)
(require 'dash)
(require 'shut-up)

(defmacro elisp-refs--print-time (form)
  "Evaluate FORM, and print the time taken."
  `(progn
     (message "Timing %s" ',form)
     (-let [(total-time gc-runs gc-time)
            (shut-up (benchmark-run 1 ,form))]
       (message "Elapsed time: %fs (%fs in %d GCs)"
                total-time
                gc-time
                gc-runs))))

;; TODO: benchmark elisp-refs-variable (and add a smoke test)
;; TODO: make this more representative by loading more elisp files
;; before searching. Running this in a GUI is also conspicuously
;; slower, which bench.sh doesn't reflect.
(defun elisp-refs-bench ()
  "Measure runtime of searching."
  (interactive)
  (elisp-refs--report-loc)
  ;; Measure a fairly uncommon function.
  (elisp-refs--print-time (elisp-refs-function 'mod))
  ;; Measure a common macro
  (elisp-refs--print-time (elisp-refs-macro 'when))
  ;; Compare with searching for the same symbol without walking
  (elisp-refs--print-time (elisp-refs-symbol 'when))
  ;; Synthetic test of a large number of results.
  (message "Formatting 10,000 results")
  (let ((forms (-repeat 10000 (list '(ignored) 1 64)))
        (buf (generate-new-buffer " *dummy-elisp-refs-buf*")))
    (with-current-buffer buf
      (insert "(defun foo (bar) (if bar nil (with-current-buffer bar))) ;; blah")
      (setq-local elisp-refs--path "/tmp/foo.el"))
    (elisp-refs--print-time
     (elisp-refs--show-results 'foo "foo bar" (list (cons forms buf))
                               20 nil))
    (kill-buffer buf)))

(defun elisp-refs--report-loc ()
  "Report the total number of lines of code searched."
  (interactive)
  (let* ((loaded-paths (elisp-refs--loaded-paths))
         (loaded-src-bufs (shut-up (-map #'elisp-refs--contents-buffer loaded-paths)))
         (total-lines (-sum (--map (with-current-buffer it
                                     (line-number-at-pos (point-max)))
                                   loaded-src-bufs))))
    ;; Clean up temporary buffers.
    (--each loaded-src-bufs (kill-buffer it))
    (message "Total LOC: %s" (elisp-refs--format-int total-lines))))

(provide 'elisp-refs-bench)
;;; elisp-refs-bench.el ends here
