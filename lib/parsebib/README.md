Parsebib
=======

(c) 2014-2017 Joost Kremers

`Parsebib` is an Elisp library for reading `.bib` files. It provides two different APIs, a higher-level one that reads all items in one go, and a lower-level one that reads one item at a time. Supported items are `@Preamble`, `@String` and `@Comment` items, and obviously actual bibliographic entries.

Both APIs parse the current buffer. If you wish to combine multiple `.bib` files, you need to parse each separately.


Resolving `@string` abbreviations and cross-references
------------------------------------------------------

Parsebib can resolve `@string` abbrevs and cross-references while reading the contents of a `.bib` file. When `@string` abbrevs are resolved, abbreviations in field values (or `@string` definitions) are replaced with their expansion. In addition, the braces or double quotes around field values are removed, and multiple spaces and newlines in sequence are reduced to a single space. In essence, the field values are modified in such a way that they are suitable for display, but they no longer reliably represent the contents of the `.bib` file. When `@string` abbrevs are not resolved, no modifications are applied to the field values, so that the parsing results reflect the contents of the `.bib` file accurately.

Cross-references can also be resolved. This means that if an entry that has a `crossref` field, fields in the cross-referenced entry that are not already part of the cross-referencing entry are added to it. Both BibTeX's (rather simplistic) inheritance rule and BibLaTeX's more sophisticated inheritance schema are supported. It is also possible to specify a custom inheritance schema. Note that resolving cross-references can be done independently from resolving `@string` abbrevs, but the former generally won't make sense without the latter.

Resolving `@string` abbrevs can be done with both the higher-level and the lower-level API. Resolving cross-references can only be done with the higher-level API. This is mainly because cross-referenced entries appear *after* cross-referencing entries in the `.bib` file, so that when an entry with a `crossref` field is read, its cross-referenced entry is not known yet, while `@string` definitions appear in the `.bib` file before they are used. It is possible, however, to resolve cross-references after all entries have been read.


Higher-level API
----------------

The higher-level API consists of functions that read and return all items of a specific type in the current buffer. They do not move point.


### `parsebib-collect-entries (&optional hash strings inheritance)` ###

Collect all entries in the current buffer and return them as a hash table, where the keys correspond to the BibTeX keys and the values are alists consisting of `(<field> . <value>)` pairs of the relevant entries. In this alist, the BibTeX key and the entry type are stored under `=key=` and `=type=`, respectively.

The variable `hash` can be used to pass a hash table in which the entries are stored. This can be used to combine multiple `.bib` files into a single hash table, or to update an existing hash table by rereading its `.bib` file.

If the variable `strings` is present, `@string` abbreviations are expanded. `strings` should be a hash table of `@string` definitions as returned by `parsebib-collect-strings`.

If the variable `inheritance` is present, cross-references among entries are resolved. It can be `t`, in which case the file-local or global value of `bibtex-dialect` is used to determine which inheritance schema is used. It can also be one of the symbols `BibTeX` or `biblatex`, or it can be a custom inheritance schema.


### `parsebib-collect-strings (&optional hash expand-strings)` ###

Collect all `@string` definitions in the current buffer and return them as a hash table. The variable `hash` can be used to provide a hash table to store the definitions in. If it is `nil`, a new hash table is created.

The argument `expand-strings` is a boolean value. If non-nil, any abbreviations found in the string definitions are expanded against the `@string` definitions appearing earlier in the `.bib` file and against `@string` definitions in `hash`, if provided.


### `parsebib-collect-preambles` ###

Collect all `@preamble` definitions in the current buffer and return them as a list.


### `parsebib-collect-comments` ###

Collect all `@comments` in the current buffer and return them as a list.


### `parsebib-find-bibtex-dialect` ###

Find and return the BibTeX dialect for the current buffer. The BibTeX dialect is either `BibTeX` or `biblatex` and can be defined in a local-variable block at the end of the file.


### `parsebib-parse-buffer (&optional entries strings expand-strings inheritance)` ###

Collect all BibTeX data in the current buffer. Return a five-element list:

    (<entries> <strings> <preambles> <comments> <BibTeX dialect>)

The `<entries>` and `<strings>` are hash tables, `<preambles>` and `<comments>` are lists, `<BibTeX dialect>` is a symbol (either `BibTeX` or `biblatex`) or `nil`.

If the arguments `entries` and `strings` are present, they should be hash tables with `equal` as the `:test` function. They are then used to store the entries and strings, respectively.

The argument `expand-strings` functions as the same-name argument in `parsebib-collect-strings`, and `inheritance` functions as the same-name argument in `parsebib-collect-entries`.

Note that `parsebib-parse-buffer` only makes one pass through the buffer. It is therefore a bit faster than calling all the `parsebib-collect-*` functions above in a row, since that would require making four passes through the buffer.


### `parsebib-expand-xrefs (entries inheritance)` ###

Expand cross-references in `entries` according to inheritance schema `inheritance`. `entries` should be a hash table as returned by `parsebib-collect-entries`. Each entry with a `crossref` field is expanded as described above. The results are stored in the hash table `entries` again, the return value of this function is always `nil`.


Lower-level API
---------------

The lower-level API consists of functions that do the actual reading of a BibTeX item. Unlike the higher-level API, the functions here are dependent on the position of `point`. They are meant to be used in a `while` loop in which `parsebib-find-next-item` is used to move `point` to the next item and then use one of the `parsebib-read-*` functions to read the contents of the item.

All functions here take an optional position argument, which is the position in the buffer from which they should start reading. The default value is `(point)`.


### `parsebib-find-next-item (&optional pos)` ###

Find the first BibTeX item following `pos`, where an item is either a BibTeX entry, or a `@Preamble`, `@String`, or `@Comment`. This function returns the item's type as a string, i.e., either `"preamble"`, `"string"`, or `"comment"`, or the entry type. Note that the `@` is *not* part of the returned string. This function moves point into the correct position to start reading the actual contents of the item, which is done by one of the following functions.


### `parsebib-read-string (&optional pos strings)` ###
### `parsebib-read-entry (type &optional pos strings)` ###
### `parsebib-read-preamble (&optional pos)` ###
### `parsebib-read-comment (&optional pos)` ###

These functions do what their names suggest: read one single item of the type specified. Each takes the `pos` argument just mentioned. In addition, `parsebib-read-string` and `parsebiib-read-entry` take an extra argument, a hash table of `@string` definitions. When provided, abbreviations in the `@string` definitions or in field values are expanded. Note that `parsebib-read-entry` takes the entry type (as returned by `parsebib-find-next-entry`) as argument.

The reading functions return the contents of the item they read: `parsebib-read-preamble` and `parsebib-read-comment` return the text as a string. `parsebib-read-string` returns a cons cell of the form `(<abbrev> . <string>)`, and `parsebib-read-entry` returns the entry as an alist of `(<field> . <value>)` pairs. One of these pairs contains the entry type `=type=`, and one contains the entry key. These have the keys `"=key="` and `"=type="`, respectively.

Note that all `parsebib-read*` functions move point to the end of the entry.

The reading functions return `nil` if they do not find the element they should be reading at the line point is on. Point is nonetheless moved, however. Similarly, `parsebib-find-next-item` returns `nil` if it finds no next entry, leaving point at the end of the buffer. Additionally, it will signal an error of type `parsebib-entry-type-error` if it finds something that it deems to be an invalid item name. What is considered to be a valid name is determined by the regexp `parsebib-bibtex-identifier`, which is set to `"[^^\"@\\&$#%',={}() \t\n\f]*"`, meaning that any string not containing whitespace or any of the characters `^"@\&$#%',={}()` is considered a valid identifier.
