(gptel-make-tool
 :function (lambda (x y)
             (format "The value of x and y multiplied is: %s" (* x y)))
 :name "multiply_numbers"
 :description "Multiply two numbers together"
 :args (list '(:name "x"
	             :type "integer"
	             :description "The first number to be multiplied")
             '(:name "y"
	             :type "integer"
	             :description "The second number to be multiplied"))
 :category "math"
 :confirm t)

(gptel-make-tool
 :function (lambda (path filename content)
             (let ((full-path (expand-file-name filename path)))
               (with-temp-buffer
                 (insert content)
                 (write-file full-path))
               (format "Created file %s in %s" filename path)))
 :name "create_file"
 :description "Create a new file with the specified content"
 :args (list '(:name "path"
	             :type "string"
	             :description "The directory where to create the file")
             '(:name "filename"
	             :type "string"
	             :description "The name of the file to create")
             '(:name "content"
	             :type "string"
	             :description "The content to write to the file"))
 :category "filesystem")

(provide 'gptel-tools)
