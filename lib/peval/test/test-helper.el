;;; test-helper.el --- Helper for tests              -*- lexical-binding: t; -*-

;; Copyright (C) 2017 Wilfred Hughes

;; Author: Wilfred Hughes <me@wilfred.me.uk>

;;; Code:

(require 'ert)
(require 'f)

(let ((peval-dir (f-parent (f-dirname (f-this-file)))))
  (add-to-list 'load-path peval-dir))

(require 'undercover)
(undercover "peval.el"
	    (:exclude "*-test.el")
	    (:report-file "/tmp/undercover-report.json"))
