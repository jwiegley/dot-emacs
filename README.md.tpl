# f.el [![Build Status](https://api.travis-ci.org/rejeep/f.el.png?branch=master)](http://travis-ci.org/rejeep/f.el) [![Coverage Status](https://img.shields.io/coveralls/rejeep/f.el.svg)](https://coveralls.io/r/rejeep/f.el)

Much inspired by [@magnars](https://github.com/magnars)'s excellent
[s.el](https://github.com/magnars/s.el) and
[dash.el](https://github.com/magnars/dash.el),
[f.el](https://github.com/rejeep/f.el) is a modern API for working
with files and directories in Emacs.

## Installation

It's available on [Melpa](https://melpa.org/):

    M-x package-install f

Or you can just dump `f.el` in your load path somewhere.

## API

### Paths

* [f-join](#f-join-rest-args) `(&rest args)`
* [f-split](#f-split-path) `(path)`
* [f-expand](#f-expand-path-optional-dir) `(path &optional dir)`
* [f-filename](#f-filename-path) `(path)`
* [f-dirname](#f-dirname-path) `(path)`
* [f-common-parent](#f-common-parent-paths) `(paths)`
* [f-ext](#f-ext-path) `(path)`
* [f-no-ext](#f-no-ext-path) `(path)`
* [f-swap-ext](#f-swap-ext) `(path ext)`
* [f-base](#f-base-path) `(path)`
* [f-relative](#f-relative-path-optional-dir) `(path &optional dir)`
* [f-short](#f-short-path) `(path)`
* [f-long](#f-long-path) `(path)`
* [f-canonical](#f-canonical-path) `(path)`
* [f-slash](#f-slash-path) `(path)`
* [f-full](#f-full-path) `(path)`
* [f-uniquify](#f-uniquify-paths) `(paths)`
* [f-uniquify-alist](#f-uniquify-alist-paths) `(paths)`

### I/O

* [f-read-bytes](#f-read-bytes-path) `(path)`
* [f-write-bytes](#f-write-bytes-data-path) `(data path)`
* [f-read-text](#f-read-text-path-optional-coding) `(path &optional coding)`
* [f-write-text](#f-write-text-text-coding-path)`(text coding path)`
* [f-append-text](#f-append-text-text-coding-path)`(text coding path)`
* [f-append-bytes](#f-append-data-path)`(text coding path)`

### Destructive

* [f-mkdir](#f-mkdir-rest-dirs) `(&rest dirs)`
* [f-delete](#f-delete-path-optional-force) `(path &optional force)`
* [f-symlink](#f-symlink-source-path) `(source path)`
* [f-move](#f-move-from-to) `(from to)`
* [f-copy](#f-copy-from-to) `(from to)`
* [f-copy-contenst](#f-copy-contents-from-to) `(from to)`
* [f-touch](#f-touch-path) `(path)`

### Predicates

* [f-exists?](#f-exists-path) `(path)`
* [f-directory?](#f-directory-path) `(path)`
* [f-file?](#f-file-path) `(path)`
* [f-symlink?](#f-symlink-path) `(path)`
* [f-readable?](#f-readable-path) `(path)`
* [f-writable?](#f-writable-path) `(path)`
* [f-executable?](#f-executable-path) `(path)`
* [f-absolute?](#f-absolute-path) `(path)`
* [f-relative?](#f-relative-path) `(path)`
* [f-root?](#f-root-path) `(path)`
* [f-ext?](#f-ext-path-ext) `(path ext)`
* [f-same?](#f-same-path-a-path-b) `(path-a path-b)`
* [f-parent-of?](#f-parent-of-path-a-path-b) `(path-a path-b)`
* [f-child-of?](#f-child-of-path-a-path-b) `(path-a path-b)`
* [f-ancestor-of?](#f-ancestor-of-path-a-path-b) `(path-a path-b)`
* [f-descendant-of?](#f-descendant-of-path-a-path-b) `(path-a path-b)`
* [f-hidden?](#f-hidden-path) `(path)`
* [f-empty?](#f-empty-path) `(path)`

### Stats

* [f-size](#f-size-path) `(path)`
* [f-depth](#f-depth-path) `(path)`

### Misc

* [f-this-file](#f-this-file-) `()`
* [f-path-separator](#f-path-separator-) `()`
* [f-glob](#f-glob-pattern-optional-path) `(pattern &optional path)`
* [f-entries](#f-entries-path-optional-fn-recursive) `(path &optional fn recursive)`
* [f-directories](#f-directories-path-optional-fn-recursive) `(path &optional fn recursive)`
* [f-files](#f-files-path-optional-fn-recursive) `(path &optional fn recursive)`
* [f-root](#f-root-) `()`
* [f-traverse-upwards](#f-traverse-upwards-fn-optional-path) `(fn &optional path)`
* [f-with-sandbox](#f-with-sandbox-path-or-paths-rest-body) `(path-or-paths &rest body)`

## Documentation and examples

### f-join `(&rest args)`

{{f-join}}

```lisp
(f-join "path") ;; => "path"
(f-join "path" "to") ;; => "path/to"
(f-join "/" "path" "to" "heaven") ;; => "/path/to/heaven"
```

### f-split `(path)`

{{f-split}}

```lisp
(f-split "path") ;; => '("path")
(f-split "path/to") ;; => '("path" "to")
(f-split "/path/to/heaven") ;; => '("/" "path" "to" "heaven")
```

### f-expand `(path &optional dir)`

{{f-expand}}

```lisp
(f-expand "name") ;; => "/default/directory/name"
(f-expand "name" "other/directory") ;; => "other/directory/name"
```

### f-filename `(path)`

{{f-filename}}

```lisp
(f-filename "path/to/file.ext") ;; => "file.ext"
(f-filename "path/to/directory") ;; => "directory"
```

### f-dirname `(path)`

{{f-dirname}}

Alias: `f-parent`

```lisp
(f-dirname "path/to/file.ext") ;; => "path/to"
(f-dirname "path/to/directory") ;; => "path/to"
(f-dirname "/") ;; => nil
```

### f-common-parent `(paths)`

{{f-common-parent}}

```lisp
(f-common-parent '("foo/bar/baz" "foo/bar/qux" "foo/bar/mux")) ;; => "foo/bar/"
(f-common-parent '("/foo/bar/baz" "/foo/bar/qux" "/foo/bax/mux")) ;; => "/foo/"
(f-common-parent '("foo/bar/baz" "quack/bar/qux" "lack/bar/mux")) ;; => ""
```

### f-ext `(path)`

{{f-ext}}

```lisp
(f-ext "path/to/file.ext") ;; => "ext"
(f-ext "path/to/directory") ;; => nil
```

### f-no-ext `(path)`

{{f-no-ext}}

```lisp
(f-no-ext "path/to/file.ext") ;; => "path/to/file"
(f-no-ext "path/to/directory") ;; => "path/to/directory"
```

### f-swap-ext `(path ext)`

{{f-swap-ext}}

```lisp
(f-swap-ext "path/to/file.ext" "org") ;; => "path/to/file.org"
(f-swap-ext "path/to/file.ext" "") ;; => error
```

### f-base `(path)`

{{f-base}}

```lisp
(f-base "path/to/file.ext") ;; => "file"
(f-base "path/to/directory") ;; => nil
```

### f-relative `(path &optional dir)`

{{f-relative}}

```lisp
(f-relative "/some/path/relative/to/my/file.txt" "/some/path/") ;; => relative/to/my/file.txt
(f-relative "/default/directory/my/file.txt") ;; => my/file.txt
```

### f-short `(path)`

{{f-short}}

Alias: `f-abbrev`

```lisp
(f-short "/Users/foo/Code/bar") ;; => ~/Code/bar
(f-short "/path/to/Code/bar") ;; => /path/to/Code/bar
```

### f-long `(path)`

{{f-long}}

```lisp
(f-long "~/Code/bar") ;; => /Users/foo/Code/bar
(f-long "/path/to/Code/bar") ;; => /path/to/Code/bar
```

### f-canonical `(path)`

{{f-canonical}}

```lisp
(f-canonical "/path/to/real/file") ;; => /path/to/real/file
(f-canonical "/link/to/file") ;; => /path/to/real/file
```

### f-slash `(path)`

{{f-slash}}

```lisp
(f-slash "/path/to/file") ;; => /path/to/file
(f-slash "/path/to/dir") ;; => /path/to/dir/
(f-slash "/path/to/dir/") ;; => /path/to/dir/
```

### f-full `(path)`

{{f-full}}

```lisp
(f-full "~/path/to/file") ;; => /home/path/to/file
(f-full "~/path/to/dir") ;; => /home/path/to/dir/
(f-full "~/path/to/dir/") ;; => /home/path/to/dir/
```

### f-uniquify `(paths)`

{{f-uniquify}}

```lisp
(f-uniquify '("/foo/bar" "/foo/baz" "/foo/quux")) ;; => '("bar" "baz" "quux")
(f-uniquify '("/foo/bar" "/www/bar" "/foo/quux")) ;; => '("foo/bar" "www/bar" "quux")
(f-uniquify '("/foo/bar" "/www/bar" "/www/bar/quux")) ;; => '("foo/bar" "www/bar" "quux")
(f-uniquify '("/foo/bar" "/foo/baz" "/home/www/bar" "/home/www/baz" "/var/foo" "/opt/foo/www/baz")) ;; => '("foo/bar" "www/bar" "foo/baz" "home/www/baz" "foo/www/baz" "foo")
```

### f-uniquify-alist `(paths)`

{{f-uniquify-alist}}

```lisp
(f-uniquify-alist '("/foo/bar" "/foo/baz" "/foo/quux")) ;; => '(("/foo/bar" . "bar") ("/foo/baz" . "baz") ("/foo/quux" . "quux"))
(f-uniquify-alist '("/foo/bar" "/www/bar" "/foo/quux")) ;; => '(("/foo/bar" . "foo/bar") ("/www/bar" . "www/bar") ("/foo/quux" . "quux"))
(f-uniquify-alist '("/foo/bar" "/www/bar" "/www/bar/quux")) ;; => '(("/foo/bar" . "foo/bar") ("/www/bar" . "www/bar") ("/www/bar/quux" . "quux"))
(f-uniquify-alist '("/foo/bar" "/foo/baz" "/home/www/bar" "/home/www/baz" "/var/foo" "/opt/foo/www/baz")) ;; => '(("/foo/bar" . "foo/bar") ("/home/www/bar" . "www/bar") ("/foo/baz" . "foo/baz") ("/home/www/baz" . "home/www/baz") ("/opt/foo/www/baz" . "foo/www/baz") ("/var/foo" . "foo"))
```

### f-read-bytes `(path)`

{{f-read-bytes}}

```lisp
(f-read-bytes "path/to/binary/data")
```

### f-write-bytes `(data path)`

{{f-write-bytes}}

```lisp
(f-write-bytes (unibyte-string 72 101 108 108 111 32 119 111 114 108 100) "path/to/binary/data")
```

### f-read-text `(path &optional coding)`

{{f-read-text}}

Alias: `f-read`

```lisp
(f-read-text "path/to/file.txt" 'utf-8)
(f-read "path/to/file.txt" 'utf-8)
```

### f-write-text `(text coding path)`

{{f-write-text}}

Alias: `f-write`

```lisp
(f-write-text "Hello world" 'utf-8 "path/to/file.txt")
(f-write "Hello world" 'utf-8 "path/to/file.txt")
```

### f-append-text `(text coding path)`

{{f-append-text}}

Alias: `f-append`

```lisp
(f-append-text "Hello world" 'utf-8 "path/to/file.txt")
(f-append "Hello world" 'utf-8 "path/to/file.txt")
```

### f-append-bytes `(data path)`

{{f-append-bytes}}

```lisp
(f-append-bytes "path/to/file" (unibyte-string 72 101 108 108 111 32 119 111 114 108 100))
```

### f-mkdir `(&rest dirs)`

{{f-mkdir}}

```lisp
(f-mkdir "dir") ;; => /default/directory/dir
(f-mkdir "other" "dir") ;; => /default/directory/other/dir
```

### f-delete `(path &optional force)`

{{f-delete}}

```lisp
(f-delete "dir")
(f-delete "other/dir" t)
(f-delete "path/to/file.txt")
```

### f-symlink `(source path)`

{{f-symlink}}

```lisp
(f-symlink "path/to/source" "path/to/link")
```

### f-move `(from to)`

{{f-move}}

```lisp
(f-move "path/to/file.txt" "new-file.txt")
(f-move "path/to/file.txt" "other/path")
```

### f-copy `(from to)`

{{f-copy}}

```lisp
(f-copy "path/to/file.txt" "new-file.txt")
(f-copy "path/to/dir" "other/dir")
```

### f-copy-contents `(from to)`

{{f-copy-contents}}

```lisp
(f-copy-contents "path/to/dir" "path/to/other/dir")
```

### f-touch `(path)`

{{f-touch}}

```lisp
(f-touch "path/to/existing/file.txt")
(f-touch "path/to/non/existing/file.txt")
```

### f-exists? `(path)`

{{f-exists?}}

```lisp
(f-exists? "path/to/file.txt")
(f-exists? "path/to/dir")
```

### f-directory? `(path)`

{{f-directory?}}

Aliases: `f-directory-p f-dir? f-dir-p`

```lisp
(f-directory? "path/to/file.txt") ;; => nil
(f-directory? "path/to/dir") ;; => t
```

### f-file? `(path)`

{{f-file?}}

Alias: `f-file-p`

```lisp
(f-file? "path/to/file.txt") ;; => t
(f-file? "path/to/dir") ;; => nil
```

### f-symlink? `(path)`

{{f-symlink?}}

Alias: `f-symlink-p`

```lisp
(f-symlink? "path/to/file.txt") ;; => nil
(f-symlink? "path/to/dir") ;; => nil
(f-symlink? "path/to/link") ;; => t
```

### f-readable? `(path)`

{{f-readable?}}

Alias: `f-readable-p`

```lisp
(f-readable? "path/to/file.txt")
(f-readable? "path/to/dir")
```

### f-writable? `(path)`

{{f-writable?}}

Alias: `f-writable-p`

```lisp
(f-writable? "path/to/file.txt")
(f-writable? "path/to/dir")
```

### f-executable? `(path)`

{{f-executable?}}

Alias: `f-executable-p`

```lisp
(f-executable? "path/to/file.txt")
(f-executable? "path/to/dir")
```

### f-absolute? `(path)`

{{f-absolute?}}

Alias: `f-absolute-p`

```lisp
(f-absolute? "path/to/dir") ;; => nil
(f-absolute? "/full/path/to/dir") ;; => t
```

### f-relative? `(path)`

{{f-relative?}}

Alias: `f-relative-p`

```lisp
(f-relative? "path/to/dir") ;; => t
(f-relative? "/full/path/to/dir") ;; => nil
```

### f-root? `(path)`

{{f-root?}}

Alias: `f-root-p`

```lisp
(f-root? "/") ;; => t
(f-root? "/not/root") ;; => nil
```

### f-ext? `(path ext)`

{{f-ext?}}

Alias: `f-ext-p`

```lisp
(f-ext? "path/to/file.el" "el") ;; => t
(f-ext? "path/to/file.el" "txt") ;; => nil
(f-ext? "path/to/file.el") ;; => t
(f-ext? "path/to/file") ;; => nil
```

### f-same? `(path-a path-b)`

{{f-same?}}

Aliases: `f-same-p f-equal? f-equal-p`

```lisp
(f-same? "foo.txt" "foo.txt") ;; => t
(f-same? "/path/to/foo.txt" "/path/to/bar.txt") ;; => nil
```

### f-parent-of? `(path-a path-b)`

{{f-parent-of?}}

Alias: `f-parent-of-p`

```lisp
(f-parent-of? "/path/to" "/path/to/dir") ;; => t
(f-parent-of? "/path/to/dir" "/path/to") ;; => nil
(f-parent-of? "/path/to" "/path/to") ;; => nil
```

### f-child-of? `(path-a path-b)`

{{f-child-of?}}

Alias: `f-child-of-p`

```lisp
(f-child-of? "/path/to" "/path/to/dir") ;; => nil
(f-child-of? "/path/to/dir" "/path/to") ;; => t
(f-child-of? "/path/to" "/path/to") ;; => nil
```

### f-ancestor-of? `(path-a path-b)`

{{f-ancestor-of?}}

Alias: `f-ancestor-of-p`

```lisp
(f-ancestor-of? "/path/to" "/path/to/dir") ;; => t
(f-ancestor-of? "/path" "/path/to/dir") ;; => t
(f-ancestor-of? "/path/to/dir" "/path/to") ;; => nil
(f-ancestor-of? "/path/to" "/path/to") ;; => nil
```

### f-descendant-of? `(path-a path-b)`

{{f-descendant-of?}}

Alias: `f-descendant-of-p`

```lisp
(f-descendant-of? "/path/to/dir" "/path/to") ;; => t
(f-descendant-of? "/path/to/dir" "/path") ;; => t
(f-descendant-of? "/path/to" "/path/to/dir") ;; => nil
(f-descendant-of? "/path/to" "/path/to") ;; => nil
```

### f-hidden? `(path)`

{{f-hidden?}}

```lisp
(f-hidden? "/path/to/foo") ;; => nil
(f-hidden? "/path/to/.foo") ;; => t
```

Alias: `f-hidden-p`

### f-empty? `(path)`

{{f-empty?}}

```lisp
(f-empty? "/path/to/empty-file") ;; => t
(f-empty? "/path/to/file-with-contents") ;; => nil
(f-empty? "/path/to/empty-dir/") ;; => t
(f-empty? "/path/to/dir-with-contents/") ;; => nil
```

Alias: `f-empty-p`

### f-size `(path)`

{{f-size}}

```lisp
(f-size "path/to/file.txt")
(f-size "path/to/dir")
```

### f-depth `(path)`

{{f-depth}}

```lisp
(f-depth "/") ;; 0
(f-depth "/var/") ;; 1
(f-depth "/usr/local/bin") ;; 3
```

### f-this-file `()`

{{f-this-file}}

```lisp
(f-this-file) ;; => /path/to/this/file
```

### f-path-separator `()`

{{f-path-separator}}

```lisp
(f-path-separator) ;; => /
```

### f-glob `(pattern &optional path)`

{{f-glob}}

See: `file-expand-wildcards`

```lisp
(f-glob "path/to/*.el")
(f-glob "*.el" "path/to")
```

### f-entries `(path &optional fn recursive)`

{{f-entries}}

```lisp
(f-entries "path/to/dir")
(f-entries "path/to/dir" (lambda (file) (s-matches? "test" file)))
(f-entries "path/to/dir" nil t)
(f--entries "path/to/dir" (s-matches? "test" it))
```

### f-directories `(path &optional fn recursive)`

{{f-directories}}

```lisp
(f-directories "path/to/dir")
(f-directories "path/to/dir" (lambda (dir) (equal (f-filename dir) "test")))
(f-directories "path/to/dir" nil t)
(f--directories "path/to/dir" (equal (f-filename it) "test"))
```

### f-files `(path &optional fn recursive)`

{{f-files}}

```lisp
(f-files "path/to/dir")
(f-files "path/to/dir" (lambda (file) (equal (f-ext file) "el")))
(f-files "path/to/dir" nil t)
(f--files "path/to/dir" (equal (f-ext it) "el"))
```

### f-root `()`

{{f-root}}

```lisp
(f-root) ;; => "/"
```

### f-traverse-upwards `(fn &optional path)`

{{f-traverse-upwards}}

```lisp
(f-traverse-upwards
 (lambda (path)
   (f-exists? (f-expand ".git" path)))
 start-path)

(f--traverse-upwards (f-exists? (f-expand ".git" it)) start-path) ;; same as above
```

### f-with-sandbox `(path-or-paths &rest body)`

{{f-with-sandbox}}

```lisp
(f-with-sandbox foo-path
  (f-touch (f-expand "foo" foo-path)))
(f-with-sandbox (list foo-path bar-path)
  (f-touch (f-expand "foo" foo-path))
  (f-touch (f-expand "bar" bar-path)))
(f-with-sandbox foo-path
  (f-touch (f-expand "bar" bar-path))) ;; "Destructive operation outside sandbox"
```

## Example

Here's an example of a function that finds the Git project root.

### Using standard Emacs builtin functions

```lisp
(defun find-git-root (&optional dir)
  (unless dir (setq dir (expand-file-name (file-name-directory (buffer-file-name)))))
  (let ((parent (expand-file-name ".." dir)))
    (unless (equal parent dir)
      (if (file-exists-p (expand-file-name ".git" dir))
          dir
        (find-git-root parent)))))
```

### Using `f.el`

```lisp
(defun find-git-root (&optional dir)
  (interactive)
  (unless dir (setq dir (f-dirname (buffer-file-name))))
  (let ((parent (f-parent dir)))
    (unless (f-root? parent)
      (if (f-exists? (f-expand ".git" dir))
          dir
        (find-git-root parent)))))
```

Now, try writing it even simpler yourself. Hint, check out `f-traverse-upwards`.

## Contribution

Be sure to!

Install [Cask](https://github.com/rejeep/cask.el) if you haven't
already.

Run the unit tests with:

    $ make test

Do not change `README.md` directly. If you want to change the README
or if you change any function comments, update the README with:

    $ make docs
