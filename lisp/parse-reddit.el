(defun create-org-files-from-csv (csv-file)
  "Process CSV-FILE to generate .org files named after the \"date\" field with \"body\" content."
  (interactive "fCSV file: ")
  (let* ((data (with-temp-buffer
                 (insert-file-contents csv-file)
                 (buffer-string)))
         (rows (parse-csv-string-rows data ?\, ?\" ?\n))
         (headers (pop rows)))
    (let ((date-index (cl-position "date" headers :test 'string=))
          (body-index (cl-position "body" headers :test 'string=)))
      (dolist (row rows)
        (let* ((date (nth date-index row))
               (filename (format "%s.org" date))
               (content (nth body-index row)))
          (message (format "filename %s" filename))
          ;; (with-temp-file filename
          ;;   (insert content))
          )))))

;; Example usage:
;; (create-org-files-from-csv "/path/to/your/file.csv")
