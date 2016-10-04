# Auto-YASnippet

This is a hybrid of
[keyboard macros](http://www.gnu.org/software/emacs/manual/html_node/emacs/Basic-Keyboard-Macro.html)
and [yasnippet](http://code.google.com/p/yasnippet/).  You create the
snippet on the go, usually to be used just in the one place.  It's
fast, because you're not leaving the current buffer, and all you do is
enter the code you'd enter anyway, just placing `~` where you'd like
yasnippet fields and mirrors to be.

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-generate-toc again -->
**Table of Contents**

- [Auto-YASnippet](#auto-yasnippet)
- [Installation instructions](#installation-instructions)
- [Usage](#usage)
    - [A basic example](#a-basic-example)
    - [Inline text](#inline-text)
    - [Multiple placeholders](#multiple-placeholders)
    - [JavaScript - `aya-one-line`:](#javascript---aya-one-line)
    - [Generating comments](#generating-comments)
- [Functions](#functions)
    - [aya-create](#aya-create)
    - [aya-expand](#aya-expand)
    - [aya-open-line](#aya-open-line)
    - [aya-persist-snippet](#aya-persist-snippet)

<!-- markdown-toc end -->

# Installation instructions

It's easiest/recommended to install from [MELPA](http://melpa.org/).
Here's a minimal MELPA configuration for your `~/.emacs`:

```cl
(package-initialize)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
```

Afterwards, <kbd>M-x package-install RET auto-yasnippet RET</kbd> (you might
want to <kbd>M-x package-refresh-contents RET</kbd> beforehand if
you haven't done so recently).

You will also want to setup the key bindings. Here's what I recommend:

```cl
(global-set-key (kbd "H-w") #'aya-create)
(global-set-key (kbd "H-y") #'aya-expand)
```

I also like to bind this, instead of using <kbd>TAB</kbd> to expand yasnippets:

```cl
(global-set-key (kbd "C-o") #'aya-open-line)
```

# Usage

## A basic example

Suppose we want to write:

```js
count_of_red = get_total("red");
count_of_blue = get_total("blue");
count_of_green = get_total("green");
```

We write a template, using ~ to represent variables that we want to
replace:

```
count_of_~red = get_total("~red");
```

Call `aya-create` with point on this line, and the template is
converted to a value we want:

```
count_of_red = get_total("red");
```

Then call `aya-expand` and you can 'paste' additional instances of
the template. Yasnippet is active, so you can tab between
placeholders as usual.

```
count_of_red = get_total("red");
count_of_ = get_total("");
```

## Inline text

`~` replaces the symbol after it. If you want to replace arbitrary
text, use Emacs-style backticks:

```
`red'_total = get_total("`red'_values");
```

## Multiple placeholders

You can replace multiple values in a template, just like normal
yasnippet.

In this example, our template has multiple lines, so we need to
select the relevant lines before calling `aya-create`.

```
~FooType get~Foo() {
    // Get the ~foo attribute on this.
    return this.~foo;
}
```

We only fill in three placeholders in this example (the fourth is
the same as the third).

## JavaScript - `aya-one-line`:

`aya-one-line` works as a combination of `aya-create` and `aya-expand`
for one-line snippets. It's invoked by `aya-create` in case
there's no `aya-marker` (default `~`) on the line, but there's
`aya-marker-one-line` (default `$`). Or you can invoke it on its own.

```js
field$ = document.getElementById("");
```

call `aya-create` and the rest is as before:

```js
field1 = document.getElementById("field1");
field2 = document.getElementById("field2");
field3 = document.getElementById("field3");
fieldFinal = document.getElementById("fieldFinal");
```

## Generating comments

Here's a yasnippet that makes use of `aya-tab-position`. You need to call
`aya-open-line` if you want to use it.


    # -*- mode: snippet -*-
    # name: short comment
    # key: sc
    # --
    //———$1${1:$(make-string (- 47 aya-tab-position (length yas-text)) ?—)}$0

Comments generated with this will always end in same column position,
no matter from which indentation level they were invoked from.

# Functions

## aya-create

Removes "~" from current line or region (if mark is active)
yielding valid code.
The created snippet is recorded into `aya-current`.

## aya-expand

Expands whatever is currently in `aya-current`

## aya-open-line

Generic expansion function. It will either expand or move
to the next field depending on the context.

## aya-persist-snippet

Save the current auto-snippet to a user snippets folder (this defaults to
`~/.emacs.d/snippets/`.)  The current `major-mode` name will be used
to determine the snippets sub-directory to store the snippet.  For
example when working in `js2-mode` the snippet will be saved to (by
default) `~/.emacs.d/snippets/js2-mode/`.

You will be prompted for the snippet **name**. The appropriate file will be opened but not saved,
with the point on the `key: ` parameter of the snippet. If you wish to proceed, fill in the key,
save the buffer and call <kbd>C-c C-l</kbd> (`yas-load-snippet-buffer`). Otherwise, simply kill the
buffer - there will be no side effects.

You can customize `aya-persist-snippets-dir` to use a different folder
for storing auto-snippets.

You will need to run `yas/reload-all` before using the new snippet
with its **key** trigger.
