#json-snatcher.el

Say you're looking through a large JSON file, and see a value that you want to extract programmatically. This Emacs extension will allow you to snatch the path to this value.

Available on MELPA at http://melpa.milkbox.net/#/json-snatcher .
## Installation

First include the package
```lisp
(require 'json-snatcher)
```

Then add the following lines to your .emacs file, which sets a hotkey when editing JSON files in either js or js2 mode
   ```lisp
   (defun js-mode-bindings ()
   "Sets a hotkey for using the json-snatcher plugin"
   	 (when (string-match  "\\.json$" (buffer-name))
	       (local-set-key (kbd "C-c C-g") 'jsons-print-path)))
   (add-hook 'js-mode-hook 'js-mode-bindings)
   (add-hook 'js2-mode-hook 'js-mode-bindings)
   ```
## Demo
   Here's an example of the plugin at work

   ![Lights, Camera, Action!](https://github.com/Sterlingg/json-snatcher/raw/master/Demo/demo.gif)

