;;; benchstat.el --- proper benchmarking made simple

;; Author: Iskander Sharipov <quasilyte@gmail.com>
;; URL: https://github.com/Quasilyte/benchstat.el
;; Version: 1.0.1
;; Keywords: lisp

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be included in all
;; copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

;;; Commentary:

;; This package makes proper benchmark results analysis far easier by
;; leveraging benchstat utility.
;;
;; One can use this package instead of `benchmark-run-compiled'
;; and get the benefits of correct (statistically significant),
;; easy-to-read profile stats.
;;
;; In orded to use this, you need benchstat binary:
;; https://godoc.org/golang.org/x/perf/cmd/benchstat
;;
;; For detailed documentation, please visit `benchstat.el'
;; github repository.

;;; Code:

;; Skip to `Public:' section if you want to inspect package public API.
(eval-when-compile
  (defmacro benchstat--warn (msg &rest args)
    `(display-warning 'benchstat
                      (apply #'format-message (list ,msg ,@args))
                      :warning))
  ;; `profile' type is not meant to be used outside of this package,
  ;; so define it as compile-time private macro.
  (defmacro benchstat--make-profile (key filename) `(list ,key ,filename))
  (defmacro benchstat--profile-key (profile) `(nth 0 ,profile))
  (defmacro benchstat--profile-filename (profile) `(nth 1 ,profile))
  )

;; Public:

(defgroup benchstat nil
  "Emacs Lisp benchmarking with benchstat."
  :group 'lisp)

(defcustom benchstat-program "benchstat"
  "Command that is used to invoke `benchstat' program."
  :group 'benchstat)

(defcustom benchstat-buffer "*benchstat*"
  "The name of temporary output buffer for benchstat compare functions."
  :group 'benchstat)

(defvar benchstat-run-count 10
  "Default run count for benchstat/run functions.
The value lower than 5 is unrecommended.
The value higher than 10 can be good, but most of the time it's redundant.")

(defvar benchstat--profiles
  (list (benchstat--make-profile
         :old
         (expand-file-name "benchstat-old" temporary-file-directory))
        (benchstat--make-profile
         :new
         (expand-file-name "benchstat-new" temporary-file-directory)))
  "Associative list of known profiles.")

(defun benchstat-push-profile (key filename)
  "Make profile with KEY point to FILENAME.
The recommendation is to use keywords as profile key.
Pushing same KEY will overwrite old value.

FILENAME should be a full file name (path + base name).
It can be a relative path (i.e. just \"file name\"), but
do so only if you know what you are doing.

Please note that non-temp files are not going to be removed automatically."
  (unless (symbolp key)
    (benchstat--warn "Profile KEY should be a symbol; preferably a keyword (got %S)"
                     (type-of key)))
  (unless (file-writable-p filename)
    (error "FILENAME `%s' is not writeable" filename))
  (push (benchstat--make-profile key filename)
        benchstat--profiles))

(defun benchstat-compare (&optional old new delta-test)
  "Compare OLD and NEW profiles by using the DELTA-TEST method.
By default:
  - OLD = `:old'
  - NEW = `:new'
  - DELTA-TEST = \"utest\" (Mann-Whitney U-test)

The alternative DELTA-TEST is \"ttest\" (two-sample Welch)."
  (interactive)
  (let ((old (benchstat--profile (or old :old)))
        (new (benchstat--profile (or new :new)))
        (delta-test (or delta-test "utest"))
        (legend nil))
    (unless (and (eq :old (benchstat--profile-key old))
                 (eq :new (benchstat--profile-key new)))
      (setq legend (format "/* old=%S new=%S */"
                           old new)))
    (with-output-to-temp-buffer benchstat-buffer
      (with-current-buffer benchstat-buffer
        (when legend
          (insert legend "\n\n"))
        (insert
         (shell-command-to-string
          (format "%s -delta-test=%s %s %s"
                  benchstat-program
                  delta-test
                  (benchstat--profile-filename old)
                  (benchstat--profile-filename new))))))))

(defun benchstat-reset (key)
  "Clear KEY profile data file."
  (with-temp-file (benchstat--profile-filename (benchstat--profile key))
    (insert "")))

(defmacro benchstat-run (KEY REPETITIONS &rest FORMS)
  "Using KEY profile, run REPETITIONS timed evaluations of FORMS.
Internally, uses `benchmark-run-compiled' to collect profile data.

Overwrites profile data file.
Use `benchstat-run-more' if you want to append instead."
  (declare (indent 2))
  (let ((filename (benchstat--profile-filename (benchstat--profile KEY))))
    `(with-temp-file ,filename
       (insert (benchstat--run ,REPETITIONS ,@FORMS)))))

(defmacro benchstat-run-more (KEY REPETITIONS &rest FORMS)
  "Like (benchstat-run KEY REPETITIONS FORMS), but does not overwrite profile data file."
  (declare (indent 2))
  (let ((filename (benchstat--profile-filename (benchstat--profile KEY))))
    `(with-temp-buffer
       (insert "\n")
       (insert (benchstat--run ,REPETITIONS ,@FORMS))
       (append-to-file nil nil ,filename))))

;; Private:

(defun benchstat--profile (key)
  "Lookup profile using KEY.  Signals error on failure."
  (or (assq key benchstat--profiles)
      (error "Profile with KEY=`%S' not found" key)))

(defmacro benchstat--run-once (REPETITIONS &rest FORMS)
  "Return benchstat-compatible line for REPETITIONS execution of FORMS.
Benchmarking is done via `benchmark-run-compiled'."
  (when (symbolp REPETITIONS)
    (setq REPETITIONS (symbol-value REPETITIONS)))
  (unless (natnump REPETITIONS)
    (error "REPETITIONS is expected to be a positive number (got %S)"
           REPETITIONS))
  `(benchstat--format ,REPETITIONS
                      (benchmark-run-compiled ,REPETITIONS ,@FORMS)))

(defmacro benchstat--run (REPETITIONS &rest FORMS)
  "Run (benchstat--run-once REPETITIONS FORMS) `benchstat-run-count' times.
Return all lines that were collected during that."
  `(let ((run-count benchstat-run-count)
         lines)
     (dotimes (i run-count)
       (with-temp-message (format "benchstat: run %d/%d" i run-count)
         (push (benchstat--run-once ,REPETITIONS ,@FORMS)
               lines)))
     (mapconcat #'identity lines "\n")))

(defun benchstat--format (n stats)
  "Convert `(benchmark-run N ...)' result, STATS, to benchstat format."
  (let* ((time-s (nth 0 stats))
         (gc-runs (nth 1 stats))
         ;; Pedantically speaking, multiplier should be 10
         ;; times higher, but it will lead to less
         ;; pleasant results.
         ;; We are interested in relative
         ;; differences between `old' and `new', not in
         ;; the absolute values of `time-ns'.
         ;; Who measures Emacs Lisp execution in nanoseconds, anyway?
         (time-ns (* 100000000.0 time-s)))
    (if (> time-s 0)
        (format "BenchmarkEmacs %d %d ns/op %d allocs/op"
                n time-ns gc-runs)
      (benchstat--warn "Negative execution time: %fs (%dns)"
                       time-s
                       time-ns)
      "")))

(provide 'benchstat)

;;; benchstat.el ends here
