(require 'test-helper)

(defun insert-newline-once-in-ruby-mode ()
  (require 'ruby-mode)
  (ruby-mode)
  (smart-newline))

(defun insert-newline-twice-in-ruby-mode ()
  (require 'ruby-mode)
  (ruby-mode)
  (smart-newline)
  (smart-newline))

(defun insert-newline-triple-in-ruby-mode ()
  (require 'ruby-mode)
  (ruby-mode)
  (smart-newline)
  (smart-newline)
  (smart-newline))

(ert-deftest test-ruby-mode-01 ()
  "insert newline at end of line in ruby-mode."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo|
end
"
            :exercise 'insert-newline-once-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
  |
end
")))

(ert-deftest test-ruby-mode-02 ()
  "insert newline at beginning of line which has chars already."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
|end
"
            :exercise 'insert-newline-once-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
  |
end
")))

(ert-deftest test-ruby-mode-03 ()
  "insert newline at middle of line which has chars around cursor already."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
object =| FooBarBazFog.new
"
            :exercise 'insert-newline-once-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
object =
  |FooBarBazFog.new
")))

(ert-deftest test-ruby-mode-04 ()
  "insert newline"
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
end

|
def bar
end
"
            :exercise 'insert-newline-once-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
end

|

def bar
end
")))

(ert-deftest test-ruby-mode-06 ()
  "insert newline at above the not empty line."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
end

|
def bar
end
"
            :exercise 'insert-newline-once-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
end

|

def bar
end
")))

(ert-deftest test-ruby-mode-05 ()
  "insert newline at above the not empty line."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
end
|
def bar
end
"
            :exercise 'insert-newline-once-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
end
|

def bar
end
")))

(ert-deftest test-ruby-mode-06 ()
  "insert newline at above the not empty line."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
end
|
def bar
end
"
            :exercise 'insert-newline-twice-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
end

|

def bar
end
")))

(ert-deftest test-ruby-mode-07 ()
  "insert newline at above the not empty line."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
end
|
def bar
end
"
            :exercise 'insert-newline-twice-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
end

|

def bar
end
")))

(ert-deftest test-ruby-mode-08 ()
  "insert newline at above the not empty line."
  (cursor-test/equal
   :type 'pos
   :actual (cursor-test/setup
            :init "
def foo
end|
def bar
end
"
            :exercise 'insert-newline-triple-in-ruby-mode)
   :expect (cursor-test/setup
            :init "
def foo
end

|

def bar
end
")))
