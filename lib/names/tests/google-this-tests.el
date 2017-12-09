
(byte-compile-file "google-this.el")
(require 'noflet)
(require 'google-this)

;; (ert-deftest google-this-insert-lucky-string-should-replace-region ()
;;   (with-temp-buffer
;;     (insert "prefix ")
;;     (save-excursion (insert " suffix"))
;;     (let ((left (point))
;;           (old-last-url google-this--last-url)
;;           right)      
;;       (insert "imdb raiders")
;;       (setq right (point))
;;       (noflet ((region-active-p () t)
;;                (region-beginning () left)
;;                (region-end () right)
;;                (read-string (_ s) s)
;;                (kill-region (l r)
;;                             (delete-region l r))
;;                ;; Make this run synchronously, no need for manual search
;;                (google-this--do-lucky-search (_ func)
;;                                              (funcall func "http://www.imdb.com/title/tt0082971/")))
;;               (call-interactively 'google-this-lucky-and-insert-url)
;;               (setq google-this--last-url old-last-url)
;;               (should (equal "prefix http://www.imdb.com/title/tt0082971/ suffix"
;;                              (buffer-substring-no-properties (point-min) (point-max))))))))

(defvar gtt--test-string "This is a test")
(defvar gtt--base-url (google-this-url))
(defun gtt--format-and-hexify (term)
  (format gtt--base-url (url-hexify-string term)))

;;; Google string tests
(defvar gtt--url-result (gtt--format-and-hexify gtt--test-string))
(defvar gtt--url-result-quoted (gtt--format-and-hexify (concat "\"" gtt--test-string "\"")))
(ert-deftest google-this-string-test ()
  (let ((google-this-wrap-in-quotes nil))
    (noflet ((browse-url (url) url))
      (should (equal (google-this-string nil gtt--test-string t) gtt--url-result))
      (should (equal (google-this-string t gtt--test-string t)  gtt--url-result-quoted)))))
(ert-deftest google-this-string-inverted-test ()
  (let ((google-this-wrap-in-quotes t))
    (noflet ((browse-url (url) url))
      (should (equal (google-this-string nil gtt--test-string t) gtt--url-result-quoted))
      (should (equal (google-this-string t gtt--test-string t) gtt--url-result)))))

;;; google-this-search tests
(ert-deftest google-this-search-test ()
  (let ((google-this-wrap-in-quotes nil))
    (noflet ((browse-url (url) url)
              (google-this-pick-term (_) gtt--test-string))
      (should (equal 
                (google-this-search nil "foo *%s& url Tester") 
                (format "foo *%s& url Tester" (url-hexify-string gtt--test-string)))))))

;;; Other google-this-something tests
(ert-deftest google-this-buffer-test ()
  (let ((google-this-wrap-in-quotes nil)
        left right)
    (with-temp-buffer
      (insert "This is a ")
      (setq left (point))
      (insert "test\nI am doing")
      (save-excursion (insert " right\nnow"))
      (setq right (point))
      (noflet ((region-active-p () t)
               (region-beginning () left)
               (region-end () right)
               (browse-url (url) url)
               (read-string (_ def) def))
        (should (equal (google-this-region nil) (gtt--format-and-hexify "test\nI am doing")))
        (should (equal (google-this-line nil) (gtt--format-and-hexify "I am doing right")))
        (should (equal (google-this-word nil) (gtt--format-and-hexify "doing")))
        (should (equal (google-this-symbol nil) (gtt--format-and-hexify "doing")))))))

;;; Local Variables:
;;; lisp-indent-function:common-lisp-indent-function
;;; End:
