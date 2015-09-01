## Transpose Mark

A small libary that lets you transpose data by leaving an Emacs mark on the line you want to transpose.

## Installation

This package can be installed through [melpa](http://melpa.milkbox.net/):

    M-x package-install transpose-mark

## Usage

### Transpose Mark Line

Transpose a marked line (leave a mark by e.g. searching for something) with the current line:

`M-x transpose-mark`
or
`M-x transpose-mark-line`

![transpose-mark](https://raw.githubusercontent.com/attichacker/transpose-mark/master/images/transpose-mark.gif)

### Transpose Mark Region

Select a region to be transposed, run command, afterwards select another region and run command again.

`M-x transpose-mark`
or
`M-x transpose-mark-region`

![transpose-region](https://raw.githubusercontent.com/attichacker/transpose-mark/master/images/transpose-region.gif)


### Transpose Mark Region Start / End Func

When a region has been selection for transposition you can afterwards expand / contract it.

`M-x tmr-end--forward-word`

`M-x tmr-end--forward-char`

`M-x tmr-end--backward-word`

`M-x tmr-end--backward-char`

![transpose-region](https://raw.githubusercontent.com/attichacker/transpose-mark/master/images/transpose-region-expand-end.gif)


`M-x tmr-start--forward-word`

`M-x tmr-start--forward-char`

`M-x tmr-start--backward-word`

`M-x tmr-start--backward-char`

![transpose-region](https://raw.githubusercontent.com/attichacker/transpose-mark/master/images/transpose-region-expand-start.gif)


### Creating your own expanding functions

You can create your own expanding functions using

`transpose-mark-region-start-func`

or

`transpose-mark-region-end-func`


This is how tmr-end--forward-char is defined:

    (defun tmr-end--forward-char ()
      "Run transpose-mark-region-end-func with forward-char."
      (interactive)
      (transpose-mark-region-end-func 'forward-char))


### Functions
* `transpose-mark`
* `transpose-mark-line`
* `transpose-mark-region`
* `transpose-mark-region-abort`
* `transpose-mark-region-start-func`
* `transpose-mark-region-end-func`

### Overlay manipulation functions
* `tmr-start--forward-word`
* `tmr-start--backward-word`
* `tmr-start--forward-char`
* `tmr-start--backward-char`
* `tmr-end--forward-word`
* `tmr-end--backward-word`
* `tmr-end--forward-char`
* `tmr-end--backward-char`


### Faces
* `transpose-mark-region-set-face`


### Useful info

If you're using Hydra mode you can define a Hydra map to expand / contract
the overlay region, e.q.:

    (defhydra transpose-mark-end (my-key-map "t")
      "Move transpose-mark-region-end."
      ("f" tmr-end--forward-char "forward-char")
      ("b" tmr-end--backward-char "backward-char")
      ("M-f" tmr-end--forward-word "forward-word")
      ("M-b" tmr-end--backward-word "backward-word")
      ("q" hydra-keyboard-quit "quit" :color blue))
    
    (defhydra transpose-mark-start (my-key-map "r")
      "Move transpose-mark-region-start."
      ("f" tmr-start--forward-char "forward-char")
      ("b" tmr-start--backward-char "backward-char")
      ("M-f" tmr-start--forward-word "forward-word")
      ("M-b" tmr-start--backward-word "backward-word")
      ("q" hydra-keyboard-quit "quit" :color blue))

