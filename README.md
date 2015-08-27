Parsebib
=======

(c) 2014 Joost Kremers

`Parsebib` is an Elisp library for reading `.bib` files. It provides functions for going through a `.bib` file and reading the entries one by one. There are separate functions for reading `@Preamble`, `@String` and `@Comment` items.

To get started reading a `.bib` file, use the function `parsebib-find-next-item`, which finds the first BibTeX item following point, where an item is either an entry, or a `@Preamble`, `@String`, or `@Comment`. This function moves point to the item and returns the item’s name as a string without the `@` (i.e., either the entry type, or `"preamble"`, `"string"`, or `"comment"`). The functions `parsebib-read-preamble`, `parsebib-read-string`, `parsebib-read-comment`, and `parsebib-read-entry` all do as their names suggest. They start reading at the beginning of the line that point is on and thus can be used after `parsebib-find-next-item`. Note that `parsebib-read-entry` takes the entry type (as returned by `parsebib-find-next-entry`) as argument. All these functions take an optional position argument (either a number or a marker), from which to start searching, which defaults to point.

The reading functions return the contents of the item they read: `parsebib-read-preamble` and `parsebib-read-comment` return the text as a string. `parsebib-read-string` returns a cons cell of the form `(<abbrev> . <string>)`, and `parsebib-read-entry` returns the entry as an alist of `(<field> . <value>)` pairs. The alist contains an element with the key `=type=`, which holds the entry type, and an element with the key `=key=`, which holds the entry key. All functions move point to the end of the entry.

The reading functions return `nil` if they do not find the element they should be reading at the line point is on. Point is nonetheless moved, however. Similarly, `parsebib-find-next-item` returns `nil` if it finds no next entry, leaving point at the end of the buffer. Additionally, it will signal an error of type `parsebib-entry-type-error` if it finds something that it deems to be an invalid item name. What is considered to be a valid name is determined by the regexp `parsebib-bibtex-identifier`, which is set to `"[^^\"@\\&$#%',={}() \t\n\f]*"`, meaning that any string not containing whitespace or any of the characters `^"@\&$#%',={}()` is considered a valid identifier.

There is one additional function: `parsebib-find-bibtex-dialect`. This function looks for a local variable block in a `@Comment` and checks if the variable `bibtex-dialect` is set. If it is, it returns the value that is set (as a symbol). The value should be one of the elements in `bibtex-dialect-list`, i.e., by default one of `(BibTeX biblatex)`.
