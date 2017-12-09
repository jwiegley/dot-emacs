smart-newline.el
================

[![Build Status](https://travis-ci.org/ainame/smart-newline.el.png?branch=master)](https://travis-ci.org/ainame/smart-newline.el)

The `smart-newline.el` provide a stress-less newline command for programmer.
This extension's usage is VERY SIMPLE. Because, you have to ONLY press `RET` key.

## INSTALL

write in your ~/.emacs.d/init.el

```lisp
(setq el-get-sources '(
        (:name smart-newline
               :type github
               :website "https://github.com/ainame/smart-newline.el"
               :pkgname "ainame/smart-newline.el")
        )
)
```

after `M-x el-get-list-packages`

## CONFIGURATION

write in your ~/.emacs.d/init.el

* by minor-mode

`smart-newline` command bind to `RET` and `C-m`.

```lisp
(smart-newline-mode 1)
```

or

```lisp
(add-hook 'ruby-mode-hook ;; or any major-mode-hooks
  (lambda ()
  (smart-newline-mode 1)))
```

* by only using any key-bind

```lisp
(define-key global-map (kbd "C-j") 'smart-newline) ;; or any key as you like
```

## BEHAVIORS

List up smart-newline behaviors.

In this section, I use following words.

* newline   - Emacs's default command at `RET` or `C-m`
* open-line - Emacs's default command at `C-o`
* indent    - `indent-according-to-mode` command and almost Emacs's default command at `TAB` or `C-i`

And in these sample figures, `|`  representation editor's cursor.

In this description, display in ruby-mode patterns for example.You can see some patterns in other major-mode in [test cases](https://github.com/ainame/smart-newline.el/tree/master/test) .
### pattern 1

```ruby
def foo|  RET  def foo
end        ->    |
               end
```

`newline and indent` when the cursor exists at end of line.

* default Emacs: `C-j` / `RET` -> `TAB`
* smart-newline: `RET`

### pattern 2

```ruby
 def foo   RET  def foo
|end        ->    |
                end
```

`open-line and indent` at begininng of line which has chars.

* default Emacs: `C-o` -> `TAB`
* smart-newline: `RET`

### pattern 3

```ruby
object = |VeryVeryVeryLongSomeClassName.create_object

 | RET
 V

object =
  |VeryVeryVeryLongSomeClassName.create_object
```

`newline and indent` like `C-j`

* default Emacs: `C-j` / `RET` -> `TAB`
* smart-newline: `RET`

### pattern 4

```ruby
def foo         def foo          def foo
end       RET   end       RET    end
|         --->  |         --->
def bar                          |
end             def bar
                end              def bar
                                 end
```

You can insert balanced blank line around start point by only `RET`.
At the end, you will write new a method in smooth.

* default Emacs: `RET` -> `RET` -> `C-p` / `RET` -> `C-o`
* smart-newline: `RET` -> `RET`

### pattern 5

```ruby
def foo         def foo
end             end
          RET
|         --->  |
def bar
end             def bar
                end
```

* default Emacs: `C-o`
* smart-newline: `RET`

### pattern 6

```ruby
 def foo         def foo        def foo        def foo
 end       RET   end      RET   end      RET   end
|def bar   --->  |        --->  |        --->
 end             def bar                       |
                 end            def bar
                                end            def bar
                                               end
```

* default Emacs: `C-o` -> `C-o` -> `RET`
* smart-newline: `RET` -> `RET` -> `RET`

### pattern 7

```ruby
def foo         def foo        def foo        def foo
end|      RET   end      RET   end      RET   end
def bar   --->  |        --->           --->
end             def bar        |              |
                end            def bar
                               end            def bar
                                              end
```

* default Emacs: `RET` -> `RET` -> `C-o`
* smart-newline: `RET` -> `RET` -> `RET`
