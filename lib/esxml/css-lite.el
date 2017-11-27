;; -*- lexical-binding: t -*-

;;; main interface

(defvar *css-stream* nil)

(defvar *indent-css* nil
  "Indicates if the properties of a selector should be indented or not.

There are three possible values:

* nil - The default value, and indicates that no indentation should be
  applied

* the symbol 'tab - Indicates that the properties should be indented
  using the Tab character

* an integer greater than 0 - Indicates how many Space characters
  should be used to indent the properties")

(defmacro css (&rest rules)
  `(mapconcat (lambda (x) (format "%s" x))
              ',(mapcan #'process-css-rule rules)
              ""))

(defun inline-css (&rest properties)
  (mapconcat (lambda (x) (format "%s" x))
             (process-css-properties properties t :newlines nil)
             ""))

(defun css-id-name (symbol)
  (cl-format nil "#~(~a~)" symbol))

(defmacro make-css-var (var-name var-val)
  `(progn 
     (setq ,var-name ,var-val)
     (setf (get ',var-name 'css-var) t)))

(defmacro make-css-func (func-name &rest forms)
  `(progn
     (defun ,func-name ,@forms)
     (setf (get ',func-name 'css-func) t)))

(make-css-func comment (comment-string) (list (concat "/*" comment-string) "*/"))


;;; implementation

(defun selector-to-string (selector)
  (condition-case nil
      (if (listp selector)
          (destructuring-bind (specifier element)
              selector
            (ecase specifier
              (:hover (format "%s:hover" (selector-to-string element)))
              (:id (css-id-name element))))
        (cond ((and (symbolp selector) (not (symbol-package selector))) (css-id-name selector))
              ((eql :and selector) ",")
              (t (to-string selector))))
    (t (error (format "%s isn't a valid CSS selector." selector)))))

(defun css-selectors-to-string (selectors)
  (reduce (lambda (s1 s2)
            (concat s1 " " s2))
          (mapcar #'selector-to-string selectors)))

(defvar +newline+ "\n")


(defun css-func-p (val)
  (if (symbolp val)
      (get val 'css-func)
    nil))


(defun css-var-p (val)
  (if (symbolp val)
      (get val 'css-var)
    nil))

(defun string-cut (str n)
  (or (ignore-errors (substring str 0 n)) str))

(defun css-comment-p (val)
  "Return T if `val' is the start of a CSS comment, otherwise return NIL."
  (string= (string-cut val 2) "/*"))

(defun expand-tree (tree)
  (let ((result '()))
    (labels ((scan (item)
                   (if (listp item)
                       (if (css-func-p (car item))
                           ;; this calls the function
                           (scan (eval `(,(car item) ,@(cdr item)))) 
                         (mapcar #'scan item))
                     (if (css-var-p item)
                         (scan (symbol-value item))
                       (push item result)))))
      (scan tree))
    (nreverse result)))


(defun* process-css-properties (properties eval-vals &key (newlines t))
  (loop for (name val) on
        (expand-tree properties)
        by #'cddr appending
        (list 
         (if newlines +newline+ "")
         (concat 
          ;; Indent the property as specified in the variable `*indent-css*'
          (cond ((null *indent-css*) "")
                ((equal *indent-css* 'tab)
                 (string ?\t))
                ((plusp *indent-css*)
                 (make-string *indent-css* ?\s))
                ;; XXX: If the value of `*indent-css*' is invalid, this
                ;; `cond' does the same thing as if `*indent-css*' had the
                ;; value `nil'. Should it raise an error?
                )
          (to-string name)
          ;; Only add the ':' character if this isn't a comment
          (unless (css-comment-p name)
            ":"))
         (if eval-vals (to-string val) 
           (to-string val))
         ;; The ';' character should only be added if this isn't a
         ;; comment
         (if (css-comment-p name)
             ""
           ";"))))

(defun* process-css-rule (rule &key (parent-selectors nil))
  (let ((selectors (if parent-selectors
                       (concatenate 'list parent-selectors (car rule))
                     (car rule)))
        (properties (cadr rule))
        (children-rules (cddr rule)))
    (append (list +newline+ (css-selectors-to-string selectors) " {")
            (process-css-properties properties nil)
            (list +newline+ "}" +newline+)
            (mapcan (lambda (child-rules) 
                      (process-css-rule child-rules :parent-selectors selectors))
                    children-rules))))

(defun to-string (x)
  (cond ((stringp x) x)
        ((keywordp x) (downcase (substring (symbol-name x) 1)))
        ((symbolp x) (downcase (symbol-name x)))
        ((listp x) (mapconcat (lambda (val)
                                (if (stringp val)
                                    (format "'%s'" val)
                                  (to-string val)))
                              x ", "))
	(t (princ-to-string x))))

(not
 (and
  (member
   nil
   (list
    (string=
     (css (("#foo") (:height "50px")))
     "
#foo {
height:50px;
}
")

    ;; defining a css-variable manually


    ;; using that css-variable
    (string=
     (progn
       (setq my-css-var '(:margin "50px 30px"))
       (setf (get 'my-css-var 'css-var) t)

       (css (("#foo") (:height "50px" my-css-var))))
     "
#foo {
height:50px;
margin:50px 30px;
}
")

    ;; now defining a css-variable with the make-css-var macro


    ;;using that variable
    (string=
     (progn
       (make-css-var my-favorite-border-var '(:border "1px solid red"))
       
       (css (("#foo") (:height "50px" my-css-var my-favorite-border-var))))
     "
#foo {
height:50px;
margin:50px 30px;
border:1px solid red;
}
")


    ;; now with cascading
    (string=
     (css (("#foo") (:length "50px" my-css-var my-favorite-border-var)  
           (("li") (:width "50px" :float "left"  my-css-var my-favorite-border-var))))
     "
#foo {
length:50px;
margin:50px 30px;
border:1px solid red;
}

#foo li {
width:50px;
float:left;
margin:50px 30px;
border:1px solid red;
}
")

    ;;now with functions

    (string=
     (progn
       (make-css-func foo-func2 (avar) (list avar avar))
       (css (("#foo") ((foo-func2 "should-be-repeated")
                       :height "50px" my-css-var my-favorite-border-var)
             (("li") (:width "50px" :float "left"  my-css-var my-favorite-border-var)))))
     "
#foo {
should-be-repeated:should-be-repeated;
height:50px;
margin:50px 30px;
border:1px solid red;
}

#foo li {
width:50px;
float:left;
margin:50px 30px;
border:1px solid red;
}
")
    ;; now with comments
    
    (string=
     (css (("#foo") ((comment "a comment" )
                     (foo-func2 "should-be-repeated")
                     :height "50px" my-css-var my-favorite-border-var)
           (("li") (:width "50px" my-css-var my-favorite-border-var))))
     
     "
#foo {
/*a comment*/
should-be-repeated:should-be-repeated;
height:50px;
margin:50px 30px;
border:1px solid red;
}

#foo li {
width:50px;
margin:50px 30px;
border:1px solid red;
}
")

    ;; To change the indentation of the properties, use the variable *indent-css*

    ;; Use tabs to indent

    (string=
     (progn
       (setf *indent-css* 'tab)
       (css (("#foo") ((comment "a comment")
                       (foo-func2 "should-be-repeated")
                       :height "50px" my-css-var my-favorite-border-var)
             (("li") (:width "50px" my-css-var my-favorite-border-var)))))

     "
#foo {
	/*a comment*/
	should-be-repeated:should-be-repeated;
	height:50px;
	margin:50px 30px;
	border:1px solid red;
}

#foo li {
	width:50px;
	margin:50px 30px;
	border:1px solid red;
}
")

    ;; Use a number of spaces

    (string=
     (progn
       (setf *indent-css* 2)
       (css (("#foo") ((comment "a comment" )
                       (foo-func2 "should-be-repeated")
                       :height "50px" my-css-var my-favorite-border-var)
             (("li") (:width "50px" my-css-var my-favorite-border-var)))))

     "
#foo {
  /*a comment*/
  should-be-repeated:should-be-repeated;
  height:50px;
  margin:50px 30px;
  border:1px solid red;
}

#foo li {
  width:50px;
  margin:50px 30px;
  border:1px solid red;
}
")

    ;; To get the default behaviour (no indentation), set the value of *indent-css* to nil.
    
    (string=
     (progn
       (setf *indent-css* nil)
       (css (("#foo") ((comment "a comment")
                       (foo-func2 "should-be-repeated")
                       :height "50px" my-css-var my-favorite-border-var)
             (("li") (:width "50px" my-css-var my-favorite-border-var)))))

     "
#foo {
/*a comment*/
should-be-repeated:should-be-repeated;
height:50px;
margin:50px 30px;
border:1px solid red;
}

#foo li {
width:50px;
margin:50px 30px;
border:1px solid red;
}
")
    ))
  t))
