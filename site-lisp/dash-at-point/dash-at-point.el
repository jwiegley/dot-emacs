;;; dash-at-point.el --- Search the word at point with Dash

;; Copyright (C) 2013 Shinji Tanaka
;; Author:  Shinji Tanaka <shinji.tanaka@gmail.com>
;; Created: 17 Feb 2013
;; Version: 0.0.5
;; URL: https://github.com/stanaka/dash-at-point
;;
;; This file is NOT part of GNU Emacs.
;;
;; Permission is hereby granted, free of charge, to any person obtaining a copy of
;; this software and associated documentation files (the "Software"), to deal in
;; the Software without restriction, including without limitation the rights to
;; use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
;; of the Software, and to permit persons to whom the Software is furnished to do
;; so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be included in all
;; copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.
;;
;;; Commentary:
;;
;; Dash ( http://kapeli.com/ ) is an API Documentation Browser and
;; Code Snippet Manager.  dash-at-point make it easy to search the word
;; at point with Dash.
;;
;; Add the following to your .emacs:
;;
;;   (add-to-list 'load-path "/path/to/dash-at-point")
;;   (autoload 'dash-at-point "dash-at-point"
;;             "Search the word at point with Dash." t nil)
;;   (global-set-key "\C-cd" 'dash-at-point)
;;
;; Run `dash-at-point' to search the word at point, then Dash is
;; launched and search the word. To edit the search term first,
;; use C-u to set the prefix argument for `dash-at-point'.
;;
;; Dash queries can be narrowed down with a docset prefix.  You can
;; customize the relations between docsets and major modes.
;;
;;   (add-to-list 'dash-at-point-mode-alist '(perl-mode . "perl"))
;;
;; Additionally, the buffer-local variable `dash-at-point-docset' can
;; be set in a specific mode hook (or file/directory local variables)
;; to programmatically override the guessed docset.  For example:
;;
;;   (add-hook 'rinari-minor-mode-hook
;;             (lambda () (setq dash-at-point-docset "rails")))

;;; Code:

;;;###autoload
(defgroup dash-at-point nil
  "Searching in Dash for text at point."
  :prefix "dash-at-point-"
  :group 'external)

;;;###autoload
(defcustom dash-at-point-legacy-mode nil
  "Non-nil means use the legacy mode ('dash://') to invoke Dash.
Nil means use the modern mode ('dash-plugin://').
(This mode may remove in the future.)"
  :type 'boolean
  :group 'dash-at-point)

;;;###autoload
(defcustom dash-at-point-mode-alist
  '((actionscript-mode . "actionscript")
    (arduino-mode . "arduino")
    (c++-mode . "cpp,net,boost,qt,cvcpp,cocos2dx,c,manpages")
    (c-mode . "c,glib,gl2,gl3,gl4,manpages")
    (caml-mode . "ocaml")
    (clojure-mode . "clojure")
    (coffee-mode . "coffee")
    (common-lisp-mode . "lisp")
    (cperl-mode . "perl")
    (css-mode . "css,bootstrap,foundation,less,awesome,cordova,phonegap")
    (dart-mode . "dartlang,polymerdart,angulardart")
    (elixir-mode . "elixir")
    (emacs-lisp-mode . "elisp")
    (enh-ruby-mode . "ruby")
    (erlang-mode . "erlang")
    (gfm-mode . "markdown")
    (go-mode . "go,godoc")
    (groovy-mode . "groovy")
    (haml-mode . "haml")
    (haskell-mode . "haskell")
    (html-mode . "html,svg,css,bootstrap,foundation,awesome,javascript,jquery,jqueryui,jquerym,angularjs,backbone,marionette,meteor,moo,prototype,ember,lodash,underscore,sencha,extjs,knockout,zepto,cordova,phonegap,yui")
    (jade-mode . "jade")
    (java-mode . "java,javafx,grails,groovy,playjava,spring,cvj,processing,javadoc")
    (js2-mode . "javascript,backbone,angularjs")
    (js3-mode . "nodejs")
    (latex-mode . "latex")
    (less-css-mode . "less")
    (lua-mode . "lua,corona")
    (markdown-mode . "markdown")
    (nginx-mode . "nginx")
    (objc-mode . "cpp,iphoneos,macosx,appledoc,cocoapods,cocos2dx,cocos2d,cocos3d,kobold2d,sparrow,c,manpages")
    (perl-mode . "perl,manpages")
    (php-mode . "php,wordpress,drupal,zend,laravel,yii,joomla,ee,codeigniter,cakephp,phpunit,symfony,typo3,twig,smarty,phpp,html,mysql,sqlite,mongodb,psql,redis")
    (processing-mode . "processing")
    (puppet-mode . "puppet")
    (python-mode . "python3,django,twisted,sphinx,flask,tornado,sqlalchemy,numpy,scipy,saltcvp")
    (ruby-mode . "ruby,rubygems,rails")
    (rust-mode . "rust")
    (sass-mode . "sass,compass,bourbon,neat,css")
    (scala-mode . "scala,akka,playscala,scaladoc")
    (stylus-mode . "stylus")
    (tcl-mode . "tcl")
    (tuareg-mode . "ocaml")
    (twig-mode . "twig")
    (vim-mode . "vim")
    (yaml-mode . "chef,ansible"))
  "Alist which maps major modes to Dash docset tags.
Each entry is of the form (MAJOR-MODE . DOCSET-TAG) where
MAJOR-MODE is a symbol and DOCSET-TAG is corresponding tags
for one or more docsets in Dash."
  :type '(repeat (cons (symbol :tag "Major mode name")
                       (string :tag "Docset tags")))
  :group 'dash-at-point)

;;;###autoload
(defcustom dash-at-point-mode-alist-legacy
  '((actionscript-mode . "actionscript")
    (arduino-mode . "arduino")
    (c++-mode . "cpp")
    (c-mode . "c")
    (caml-mode . "ocaml")
    (clojure-mode . "clojure")
    (coffee-mode . "coffee")
    (common-lisp-mode . "lisp")
    (cperl-mode . "perl")
    (css-mode . "css")
    (elixir-mode . "elixir")
    (emacs-lisp-mode . "elisp")
    (enh-ruby-mode . "ruby")
    (erlang-mode . "erlang")
    (gfm-mode . "markdown")
    (go-mode . "go")
    (groovy-mode . "groovy")
    (haml-mode . "haml")
    (haskell-mode . "haskell")
    (html-mode . "html")
    (jade-mode . "jade")
    (java-mode . "java")
    (js2-mode . "javascript")
    (js3-mode . "nodejs")
    (latex-mode . "latex")
    (less-css-mode . "less")
    (lua-mode . "lua")
    (markdown-mode . "markdown")
    (nginx-mode . "nginx")
    (objc-mode . "iphoneos")
    (perl-mode . "perl")
    (php-mode . "php")
    (processing-mode . "processing")
    (puppet-mode . "puppet")
    (python-mode . "python3")
    (ruby-mode . "ruby")
    (rust-mode . "rust")
    (sass-mode . "sass")
    (scala-mode . "scala")
    (stylus-mode . "stylus")
    (tcl-mode . "tcl")
    (tuareg-mode . "ocaml")
    (twig-mode . "twig")
    (vim-mode . "vim")
    (yaml-mode . "chef"))
  "Alist which maps major modes to Dash docset tags.
Each entry is of the form (MAJOR-MODE . DOCSET-TAG) where
MAJOR-MODE is a symbol and DOCSET-TAG is a corresponding tag
for one or more docsets in Dash."
  :type '(repeat (cons (symbol :tag "Major mode name")
                       (string :tag "Docset tag")))
  :group 'dash-at-point)

;;;###autoload
(defvar dash-at-point-docsets (mapcar #'cdr dash-at-point-mode-alist)
  "Variable used to store all known Dash docsets. The default value
is a collection of all the values from `dash-at-point-mode-alist'.

Setting or appending this variable can be used to add completion
options to `dash-at-point-with-docset'.")

;;;###autoload
(defvar dash-at-point-docset nil
  "Variable used to specify the docset for the current buffer.
Users can set this to override the default guess made using
`dash-at-point-mode-alist', allowing the docset to be determined
programatically.

For example, Ruby on Rails programmers might add an \"allruby\"
tag to the Rails, Ruby and Rubygems docsets in Dash, and then add
code to `rinari-minor-mode-hook' or `ruby-on-rails-mode-hook'
which sets this variable to \"allruby\" so that Dash will search
the combined docset.")
(make-variable-buffer-local 'dash-at-point-docset)

(defun dash-at-point-guess-docset ()
  "Guess which docset suit to the current major mode."
  (cdr (assoc major-mode
	      (if dash-at-point-legacy-mode
		  dash-at-point-mode-alist-legacy
		  dash-at-point-mode-alist))))

(defun dash-at-point-run-search (search-string &optional docset)
  "Directly execute search for SEARCH-STRING in Dash."
  (start-process "Dash" nil "open"
		 (if dash-at-point-legacy-mode
		     (concat "dash://"
			     (when docset
			       (concat docset ":"))
			     search-string)
		   (concat "dash-plugin://"
			   (when docset
			     (concat "keys=" docset "&"))
			   "query=" (url-hexify-string search-string)))))

;;;###autoload
(defun dash-at-point (&optional edit-search)
  "Search for the word at point in Dash.
If the optional prefix argument EDIT-SEARCH is specified,
the user will be prompted to edit the search string first."
  (interactive "P")
  (let* ((thing (thing-at-point 'symbol))
	 (docset (or dash-at-point-docset (dash-at-point-guess-docset))))
    (dash-at-point-run-search
     (if (or edit-search (null thing))
         (read-string "Dash search: " thing)
       thing)
     docset)))

;;;###autoload
(defun dash-at-point-with-docset (&optional edit-search)
  "Search for the word at point in Dash with a chosen docset.
The docset options are suggested from the variable
`dash-at-point-docsets'.

If the optional prefix argument EDIT-SEARCH is specified,
the user will be prompted to edit the search string after
choosing the docset."
  (interactive "P")
  (let* ((thing (thing-at-point 'symbol))
         (docset (completing-read "Dash docset: " dash-at-point-docsets
				  nil nil nil 'minibuffer-history (dash-at-point-guess-docset)))
         (search (if (or edit-search (null thing))
                     (read-from-minibuffer (concat "Dash search (" docset "): "))
                   thing)))
    (dash-at-point-run-search search docset)))

(provide 'dash-at-point)

;;; dash-at-point.el ends here
