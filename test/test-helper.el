;;; test-helper.el --- Helpers for smart-jump-test.el -*- lexical-binding: t -*-
;; Copyright (C) 2017 James Nguyen

;; Author: James Nguyen <james@jojojames.com>
;; Maintainer: James Nguyen <james@jojojames.com>
;; Created: 19 November 2017

;;; Commentary:

;; Utilities for running smart-jump tests.

;;; Code:

(require 'ert)

;; FIXME: Adding `f' as a dependency just for this line.
(require 'f)
(let ((smart-jump-dir (f-parent (f-dirname (f-this-file)))))
  (add-to-list 'load-path smart-jump-dir))
(require 'smart-jump)

;;; test-helper.el ends here
