(require 'ert-x)

(defvar foo-mode-keywords
  `((,(concat "\\b"
              (regexp-opt '("foo" "bar") t)
              "\\b")
     . font-lock-keyword-face)))

(define-derived-mode foo1-mode fundamental-mode ""
  (setq font-lock-defaults '(foo-mode-keywords t t)))

(ert-deftest mmm-font-lock-without-font-lock-syntax-table ()
  (ert-with-test-buffer nil
    (let (mmm-mode-ext-classes-alist
          mmm-parse-when-idle)
      (insert "foo // foo_bar")
      (fundamental-mode)
      (mmm-mode-on)
      (mmm-ify-by-regexp 'foo1-mode "// " 0 "\\'" 0 nil)
      (font-lock-fontify-region (point-min) (point-max))
      (beginning-of-buffer)
      (should-not (get-text-property (point) 'face))
      (search-forward "fo" nil nil 2)
      (should (eq (get-text-property (point) 'face) font-lock-keyword-face))
      (search-forward "ba")
      (should (eq (get-text-property (point) 'face) font-lock-keyword-face)))))

(define-derived-mode foo2-mode fundamental-mode ""
  (setq font-lock-defaults '(foo-mode-keywords t t ((?_ . "w")))))

(ert-deftest mmm-font-lock-with-font-lock-syntax-table ()
  (ert-with-test-buffer nil
    (let (mmm-mode-ext-classes-alist
          mmm-parse-when-idle)
      (insert "foo // foo_bar")
      (fundamental-mode)
      (mmm-mode-on)
      (mmm-ify-by-regexp 'foo2-mode "// " 0 "\\'" 0 nil)
      (font-lock-fontify-region (point-min) (point-max))
      (should-not (next-single-property-change (point-min) 'face)))))

(define-derived-mode foo3-mode fundamental-mode ""
  (setq font-lock-defaults '(foo-mode-keywords nil t ((?_ . "w")))))

(ert-deftest mmm-syntax-propertize-function-preserves-current-syntax-table ()
  (ert-with-test-buffer nil
    (let (mmm-mode-ext-classes-alist
          mmm-parse-when-idle)
      (insert "foo_and_bar\n\nfoo")
      (foo3-mode)
      (mmm-mode-on)
      (syntax-ppss-flush-cache (point-min))
      ;; It locally changes `syntax-table' to `font-lock-syntax-table'
      ;; and calls `syntax-ppss' inside that before fontifying.
      (font-lock-fontify-region (point-min) (point-max))
      (let ((pt (next-single-property-change (point-min) 'face)))
        (should pt)
        (goto-char pt)
        (should (looking-at "foo\\'"))))))

(ert-deftest mmm-fontify-region-list-ignores-outside-for-syntactic-ff-tion ()
  (ert-with-test-buffer nil
    (let (mmm-mode-ext-classes-alist
          mmm-parse-when-idle)
      (insert "unpaired '!\n")
      (insert "js>>\n")
      (insert "var woo = js;\n")
      (foo1-mode)
      (mmm-mode-on)
      (syntax-ppss-flush-cache (point-min))
      (mmm-ify-by-regexp 'js-mode "js>>\n" 0 "\\'" 0 nil)
      (font-lock-fontify-region (point-min) (point-max))
      (search-backward "var")
      (should (eq 'font-lock-keyword-face
                  (get-text-property (point) 'face))))))

(ert-deftest mmm-fontify-region-list-carries-string-after-subregion ()
  (ert-with-test-buffer nil
    (let (mmm-mode-ext-classes-alist
          mmm-parse-when-idle)
      (insert "<p class=\"foo <% 1 + 2 %> bar tee\"</p>")
      (html-mode)
      (mmm-mode-on)
      (syntax-ppss-flush-cache (point-min))
      (mmm-ify-by-regexp 'js-mode "<%" 0 "%>" 0 nil)
      (font-lock-fontify-region (point-min) (point-max))
      (search-backward "1")
      (should (null (get-text-property (point) 'face)))
      (search-forward "bar")
      (should (eq 'font-lock-string-face
                  (get-text-property (point) 'face))))))
