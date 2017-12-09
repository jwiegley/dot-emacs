;;; test-helper.el --- Helpers for difflib.el-test.el

(let ((difflib-dir (f-parent (f-dirname (f-this-file)))))
  (add-to-list 'load-path difflib-dir))

;;; test-helper.el ends here
