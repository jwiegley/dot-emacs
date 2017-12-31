Ace-mc - Add Multiple Cursors with Ace Jump
===========================================

Ace-mc makes it really easy to add *and remove* multiple cursors using
ace jump mode.

# Screenshots
<img src="https://jmm.io/ace-mc/add-example.gif" alt="Adding cursors with ace-mc">

<img src="https://jmm.io/ace-mc/delete-example.gif" alt="Deleting cursors with ace-mc">

<img src="https://jmm.io/ace-mc/region-example.gif" alt="Using the region with ace-mc">

# Installation

Ace-mc is available through [MELPA](https://melpa.org/), so installing it is as easy as:

	M-x package-install RET ace-mc RET

# Usage

Ace-mc comes with two commands:
* `ace-mc-add-multiple-cursors`
* `ace-mc-add-single-cursor`.

Both do pretty much the same thing.

I have `ace-jump-mode` bound to <kbd>C-0</kbd>, so I bind
`ace-mc-add-multiple-cursors` to <kbd>C-)</kbd> and
`ace-mc-add-single-cursor` to <kbd>C-M-)</kbd>. The setup would be like
this:

```elisp
(global-set-key (kbd "C-)") 'ace-mc-add-multiple-cursors)
(global-set-key (kbd "C-M-)") 'ace-mc-add-single-cursor)
```

`ace-mc-add-multiple-cursors` prompts for a "Query Char" for the first
character of a word, much in the same way that Ace Jump does. In fact,
`ace-mc-add-multiple-cursors` takes similar prefix arguments that
`ace-jump-mode` does. So if you pass one <kbd>C-u</kbd> prefix to it, it'll
activate `ace-jump-char-mode`, and with <kbd>C-u</kbd> <kbd>C-u</kbd> it'll activate
`ace-jump-line-mode`.

Once you enter a query char, you'll be prompted for locations to add
`multiple-cursor-mode` cursors. If a cursor is already at the
location, it'll be removed. You'll be continually prompted for more
locations to add or remove cursors until you exit out of it by pressing
<kbd>Enter</kbd> or <kbd>Esc</kbd> or anything really that's not
alphabetic.

When you have an active region, no "query char" is prompted
for. Instead, you just get a list of locations that match the text in
your region.

`ace-mc-add-single-cursor` does the same thing as
`ace-mc-add-multiple-cursors`, just without looping.
