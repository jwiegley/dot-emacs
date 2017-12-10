# multi-compile
Multi target interface to compile.

## Screenshot

![multi-target](https://cloud.githubusercontent.com/assets/1151286/10209424/de607546-67e3-11e5-8cb0-f50d390e823b.png)

## Installation

You can install `multi-compile.el` from [MELPA](https://melpa.org/) with `package.el`

```
 M-x package-install RET multi-compile RET
```

Or drop `multi-compile.el` and [`dash.el`](https://github.com/magnars/dash.el) into your load path.

## Common settings format:
```lisp
(setq multi-compile-alist '(
    (Trigger1 . (("menu item 1" . "command 1")
                ("menu item 2" . "command 2")
                ("menu item 3" . "command 3")))

    (Trigger2 . (("menu item 4" "command 4" (expression returns a directory for the compilation))
                 ("menu item 5" "command 5" (expression returns a directory for the compilation))))
...
    ))
```

### Triggers:

- Can be major-mode:

Example adds 3 a menu item for rust-mode:
```lisp
(setq multi-compile-alist '(
    (rust-mode . (("rust-debug" . "cargo run")
                  ("rust-release" . "cargo run --release")
                  ("rust-test" . "cargo test")))
    ...
    ))
```

- Can be file/buffer name pattern:

Adds menu item "print-filename" for filename ends "txt":
```lisp
(setq multi-compile-alist '(
    ("\\.txt\\'" . (("print-filename" . "echo %file-name")))
    ...
    ))
```
menu item "print-hello" for scratch buffer:
```lisp
(setq multi-compile-alist '(
    ("*scratch*" . (("print-hello" . "echo 'hello'")))
    ...
    ))
```
adds "item-for-all" for any file or buffer:
```lisp
(setq multi-compile-alist '(
    ("\\.*" . (("item-for-all" . "echo 'I am item for all'")))
    ...
    ))
```

- Can by expression returns t or nil:

adds "item-for-home" for any file in "/home/" directory:
```lisp
(defun string/starts-with (string prefix)
    "Return t if STRING starts with prefix."
    (and (stringp string) (string-match (rx-to-string `(: bos ,prefix) t) string)))

(setq multi-compile-alist '(
    ((string/starts-with buffer-file-name "/home/") . (("item-for-home" . "echo %file-name")))
    ...
    ))
```
### Commands:
String with command for "compile" package.
In a compilation commands, you can use the templates:

- "%path" - "/tmp/prj/file.rs" (full path)
- "%dir" - "/tmp/prj/"
- "%file-name" - "file.rs"
- "%file-sans" - "file"
- "%file-ext" - "rs"
- "%make-dir" - (Look up the directory hierarchy from current file for a directory containing "Makefile") - "/tmp/"

### Compilation directory:
Default compilation directory is a system variable default-directory.
If you want to change it, add an expression that returns the correct directory.

For example, add a menu to compile go project under git:
```lisp
(setq multi-compile-alist '(
    (go-mode . (("go-build" "go build -v"
                 (locate-dominating-file buffer-file-name ".git"))
                ("go-build-and-run" "go build -v && echo 'build finish' && eval ./${PWD##*/}"
                 (multi-compile-locate-file-dir ".git"))))
    ...
    ))
```
Where:

  - "${PWD##*/}" returns current directory name.
  - (locate-dominating-file buffer-file-name ".git") - look up the directory hierarchy from current file for a directory containing directory ".git"
  - (multi-compile-locate-file-dir ".git") this is equivalent to (locate-dominating-file buffer-file-name ".git")

## Usage

- M-x multi-compile-run

## Links

[In Russian](http://reangdblog.blogspot.com/2015/10/emacs-multi-compile.html)

[In Russian (Part 2)](http://reangdblog.blogspot.com/2016/02/emacs-multi-compile.html)
