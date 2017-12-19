# smart-region
Smart region guess what you want to select by one command.
If you call this command multiple times at the same position, it expands selected region (it calls ```er/expand-region```).
Else, if you move from the mark and call this command, it select the region rectangular (it call ```rectangle-mark-mode```).
Else, if you move from the mark and call this command at same column as mark, it add cursor to each line (it call ```mc/edit-lines```).

This basic concept is from [sense-region](https://gist.github.com/tnoda/1776988).