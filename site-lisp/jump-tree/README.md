# Jump tree #

jump-tree is an undo-tree like jumping implementation, so that we can jump back and forth in a tree way like undo-tree. It's inspired by and a combination of undo-tree and jumplist.

![demo](https://github.com/yangwen0228/jump-tree/blob/master/jump-tree.gif)

## Installation
You can install from [melpa](https://melpa.org/#/jump-tree) ,or

You can install manually from github:

`git clone https://github.com/yangwen0228/jump-tree.git`

Then add this to your init:

`(require 'jump-tree)`

## Usage
Just call `M-x global-jump-tree-mode` and then use `M-,` to jump previous, `M-.` to jump next and `C-x j` to view the jump tree visualizer.

Support several kinds of skipping methods. The priority is higher than that of recording:
1. skip command in `jump-tree-pos-list-skip-commands`.
2. skip when buffer in `jump-tree-pos-list-skip-buffers`.
3. skip the commands whose prefix is "jump-tree".

Support several kinds of recording methods. The priorities are:
1. record when command in `jump-tree-pos-list-record-commands`.
2. record when offset exceeding threshold.
3. record when switch-buffer.

The default `jump-tree-pos-list-skip-commands` value is as follows:
```
'(self-insert-command)
```

The default `jump-tree-pos-list-skip-buffers` value is as follows(this may be changed to use regexp in the future.):
```
'(*Messages*)'
```

The record of the jump node is decided by the `jump-tree-pos-list-record-commands` variable. The default value is as follows:
```
'(beginning-of-buffer
  end-of-buffer backward-up-list
  beginning-of-defun end-of-defun
  unimacs-move-beginning-of-line unimacs-move-end-of-line
  unimacs-move-beginning-of-window unimacs-move-end-of-window
  helm-swoop helm-imenu helm-find-files helm-multi-files
  helm-projectile-switch-project helm-projectile-find-file
  helm-gtags-find-pattern helm-gtags-find-tag-adapter
  helm-gtags-find-rtag-adapter helm-ag-select-directory
  find-function find-variable
  mark-defun mark-whole-buffer
  avy-goto-char avy-goto-char-2
  ensime-edit-definition
  ensime-edit-definition-with-fallback
  isearch-forward)
```

We can support the record the position, when the movement or offset is exceeding the threshold. The default threshold points `jump-tree-pos-list-offset-threshold` is:
```
200
```

Besides, we support to record the position when switch to another buffer or file. Whether this feature is enabled is determined by `jump-tree-pos-list-switch-buffer`. The default value is enabled:
```
t
```

## Thanks to
Toby Cubitt's [undo-tree](http://www.dr-qubit.org/undo-tree/undo-tree.el)

ganmacs's [jumplist](https://github.com/ganmacs/jumplist)

## Todo
- [ ] When the records' buffers get closed, the position markers become invalid, now just ignore the positions. Clear the records? Or use a file to save the last point states, and restore the states?
- [x] Support jump to prev/next buffers directly.
- [ ] Support jump only in current buffer.
- [ ] Rebuild a tree contains only buffers' last position in visualizer, jump to prev/next buffers directly.
- [ ] Rebuild a tree contains positions only in current buffer in visualizer, jump only in current buffer.
- [x] Last position is sometimes not reachable.

