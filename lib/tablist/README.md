# Tablist

This package adds marks and filters to `tabulated-list-mode`. It also
puts a dired face on tabulated list buffers.

It can be used by deriving from `tablist-mode`, or with more limited features
by enabling `tablist-minor-mode` inside a `tabulated-list-mode` buffer.

# Tablist minor mode

| command                  | keymap             |
|--------------------------|--------------------|
| tablist-mark-forward     | <kbd>m</kbd>       |
| tablist-unmark-backward  | <kbd>DEL</kbd>     |
| tablist-do-kill-lines    | <kbd>k</kbd>       |
| tablist-unmark-all-marks | <kbd>U</kbd>       |
| tablist-unmark-forward   | <kbd>u</kbd>       |
| tablist-toggle-marks     | <kbd>t</kbd>       |
| tablist-sort             | <kbd>s</kbd>       |
| tablist-shrink-column    | <kbd><</kbd>       |
| tablist-enlarge-column   | <kbd>></kbd>       |
| tablist-quit             | <kbd>q</kbd>       |
| tablist-revert           | <kbd>G</kbd>       |
| tablist-export-csv       | <kbd>C-c C-e</kbd> |


## Marks

| command                    | keymap                           |
|----------------------------|----------------------------------|
| tablist-change-marks       | <kbd>* c</kbd>                   |
| tablist-unmark-all-marks   | <kbd>* !</kbd>                   |
| tablist-mark-items-regexp  | <kbd>* r</kbd> or <kbd>% m</kbd> |
| tablist-mark-items-numeric | <kbd>* n</kbd>                   |
| tablist-mark-forward       | <kbd>* m</kbd>                   |

## Filters

| command                           | keymap         |
|-----------------------------------|----------------|
| tablist-pop-filter                | <kbd>/ p</kbd> |
| tablist-push-regexp-filter        | <kbd>/ r</kbd> |
| tablist-push-equal-filter         | <kbd>/ =</kbd> |
| tablist-push-numeric-filter       | <kbd>/ n</kbd> |
| tablist-negate-filter             | <kbd>/ !</kbd> |
| tablist-toggle-first-filter-logic | <kbd>/ t</kbd> |
| tablist-display-filter            | <kbd>/ /</kbd> |
| tablist-suspend-filter            | <kbd>/ z</kbd> |
| tablist-push-named-filter         | <kbd>/ a</kbd> |
| tablist-name-current-filter       | <kbd>/ s</kbd> |
| tablist-delete-named-filter       | <kbd>/ D</kbd> |
| tablist-deconstruct-named-filter  | <kbd>/ d</kbd> |
| tablist-edit-filter               | <kbd>/ e</kbd> |
| tablist-clear-filter              | <kbd>/ C</kbd> |

# Tablist mode

Same bindings as `tablist-minor-mode`, plus the following:

| command                   | keymap         |
|---------------------------|----------------|
| tablist-flag-forward      | <kbd>d</kbd>   |
| tablist-find-entry        | <kbd>RET</kbd> |
| tablist-find-entry        | <kbd>f</kbd>   |
| tablist-do-delete         | <kbd>D</kbd>   |
| tablist-do-copy           | <kbd>C</kbd>   |
| tablist-do-rename         | <kbd>R</kbd>   |
| tablist-do-flagged-delete | <kbd>x</kbd>   |
