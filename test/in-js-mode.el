(require 'test-helper)

(defun setting-js-mode ()
  (require 'js)
  (js-mode)
  (setq javascript-indent-tabs-mode nil)
  (setq javascript-indent-level 4))

(defun insert-newline-once-in-js-mode ()
  (setting-js-mode)
  (smart-newline))

(defun insert-newline-twice-in-js-mode ()
  (setting-js-mode)
  (smart-newline)
  (smart-newline))

(defun insert-newline-triple-in-js-mode ()
  (setting-js-mode)
  (smart-newline)
  (smart-newline)
  (smart-newline))

(ert-deftest test-js-mode-01 ()
  "insert newline at end of line in js-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
        xxxx;
    });
|};
"
            :exercise 'insert-newline-twice-in-js-mode)
   :expect (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
        xxxx;
    });

    |
};
")))

(ert-deftest test-js-mode-02 ()
  "insert newline at end of line in js-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
    |});
};
"
            :exercise 'insert-newline-once-in-js-mode)
   :expect (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
        |
    });
};
")))

(ert-deftest test-js-mode-02 ()
  "insert newline at end of line in js-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
    |});
};
"
            :exercise 'insert-newline-once-in-js-mode)
   :expect (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
        |
    });
};
")))

(ert-deftest test-js-mode-03 ()
  "insert newline at end of line in js-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){
        |
    });
};
"
            :exercise 'insert-newline-once-in-js-mode)
   :expect (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){

        |
    });
};
")))

(ert-deftest test-js-mode-04 ()
  "insert newline at end of line in js-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){

        |
    });
};
"
            :exercise 'insert-newline-once-in-js-mode)
   :expect (cursor-test/setup
            :init "
var foo = function () {
    bar(function (){

        |

    });
};
")))
