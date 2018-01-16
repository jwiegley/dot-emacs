;;; w3m-search.el --- functions convenient to access web search engines

;; Copyright (C) 2001--2012, 2017 TSUCHIYA Masatoshi <tsuchiya@namazu.org>

;; Authors: Keisuke Nishida    <kxn30@po.cwru.edu>,
;;          Shun-ichi GOTO     <gotoh@taiyo.co.jp>,
;;          TSUCHIYA Masatoshi <tsuchiya@namazu.org>,
;;          Romain FRANCOISE   <romain@orebokech.com>
;; Keywords: w3m, WWW, hypermedia

;; This file is a part of emacs-w3m.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; This module contains the `w3m-search' command and some utilities
;; to improve your cyberlife.  For more detail about emacs-w3m, see:
;;
;;    http://emacs-w3m.namazu.org/

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'w3m)

(defcustom w3m-search-engine-alist
  (let* ((ja (equal "Japanese" w3m-language))
	 (utf-8 (or (and (boundp 'mule-version)
			 (not (string< (symbol-value 'mule-version) "6.0")))
		    (featurep 'un-define)
		    (fboundp 'utf-translate-cjk-mode)
		    (and (not ja) (w3m-find-coding-system 'utf-8)))))
    `(,@(if ja
	    '(("yahoo"
	       "https://search.yahoo.co.jp/bin/search?p=%s"
	       euc-japan)
	      ("yahoo-en"
	       "https://search.yahoo.com/bin/search?p=%s"))
	  '(("yahoo"
	     "https://search.yahoo.com/bin/search?p=%s")
	    ("yahoo-ja"
	     "https://search.yahoo.co.jp/bin/search?p=%s"
	     euc-japan)))
      ("alc" "https://eow.alc.co.jp/%s/UTF-8/" utf-8)
      ,@(cond
	 ((and ja utf-8)
	  '(("blog"
	     "https://blogsearch.google.com/blogsearch?q=%s&hl=ja&lr=lang_ja&oe=utf-8&ie=utf-8"
	     utf-8)
	    ("blog-en"
	     "https://blogsearch.google.com/blogsearch?q=%s&hl=en&oe=utf-8&ie=utf-8"
	     utf-8)))
	 (ja
	  '(("blog"
	     "https://blogsearch.google.com/blogsearch?q=%s&hl=ja&lr=lang_ja&ie=Shift_JIS&oe=Shift_JIS"
	     shift_jis)
	    ("blog-en"
	     "https://blogsearch.google.com/blogsearch?q=%s&hl=en")))
	 (utf-8
	  '(("blog"
	     "https://blogsearch.google.com/blogsearch?q=%s&oe=utf-8&ie=utf-8"
	     utf-8)
	    ("blog-en"
	     "https://blogsearch.google.com/blogsearch?q=%s&hl=en&oe=utf-8&ie=utf-8"
	     utf-8)))
	 (t
	  '(("blog"
	     "https://blogsearch.google.com/blogsearch?q=%s")
	    ("blog-ja"
	     "https://blogsearch.google.com/blogsearch?q=%s&lr=lang_ja&ie=Shift_JIS&oe=Shift_JIS"
	     shift_jis))))
      ,@(cond
	 ((and ja utf-8)
	  '(("google"
	     "https://www.google.com/search?q=%s&hl=ja&lr=lang_ja&ie=utf-8&oe=utf-8"
	     utf-8)
	    ("google-en"
	     "https://www.google.com/search?q=%s&hl=en&ie=utf-8&oe=utf-8"
	     utf-8)))
	 (ja
	  '(("google"
	     "https://www.google.com/search?q=%s&hl=ja&lr=lang_ja&ie=Shift_JIS&oe=Shift_JIS"
	     shift_jis)
	    ("google-en"
	     "https://www.google.com/search?q=%s&hl=en")))
	 (utf-8
	  '(("google"
	     "https://www.google.com/search?q=%s&ie=utf-8&oe=utf-8"
	     utf-8)
	    ("google-en"
	     "https://www.google.com/search?q=%s&hl=en&ie=utf-8&oe=utf-8"
	     utf-8)))
	 (t
	  '(("google"
	     "https://www.google.com/search?q=%s")
	    ("google-ja"
	     "https://www.google.com/search?q=%s&hl=ja&lr=lang_ja&ie=Shift_JIS&oe=Shift_JIS"
	     shift_jis))))
      ,@(cond
	 ((and ja utf-8)
	  '(("google news"
	     "https://news.google.co.jp/news?q=%s&hl=ja&ie=utf-8&oe=utf-8"
	     utf-8)
	    ("google news-en"
	     "https://news.google.com/news?q=%s&hl=en")))
	 (ja
	  '(("google news"
	     "https://news.google.co.jp/news?q=%s&hl=ja&ie=Shift_JIS&oe=Shift_JIS"
	     shift_jis)
	    ("google news-en"
	     "https://news.google.com/news?q=%s&hl=en")))
	 (utf-8
	  '(("google news"
	     "https://news.google.com/news?q=%s&ie=utf-8&oe=utf-8"
	     utf-8)
	    ("google news-en"
	     "https://news.google.com/news?q=%s&hl=en&ie=utf-8&oe=utf-8")))
	 (t
	  '(("google news"
	     "https://news.google.com/news?q=%s")
	    ("google news-ja"
	     "https://news.google.co.jp/news?q=%s&hl=ja&ie=Shift_JIS&oe=Shift_JIS"
	     shift_jis))))
      ,@(if ja
	    '(("technorati"
	       "https://www.technorati.jp/search/search.html?query=%s&language=ja"
	       utf-8)
	      ("technorati-en"
	       "https://www.technorati.com/search/%s"
	       utf-8))
	  '(("technorati"
	     "https://www.technorati.com/search/%s"
	     utf-8)
	    ("technorati-ja"
	     "https://www.technorati.jp/search/search.html?query=%s&language=ja"
	     utf-8)))
      ("technorati-tag"
       "https://www.technorati.com/tag/%s"
       utf-8)
      ("goo-ja"
       "https://search.goo.ne.jp/web.jsp?MT=%s"
       euc-japan)
      ("excite-ja"
       "https://www.excite.co.jp/search.gw?target=combined&look=excite_jp\
&lang=jp&tsug=-1&csug=-1&search=%s"
       shift_jis)
      ("altavista"
       "https://altavista.com/sites/search/web?q=\"%s\"&kl=ja&search=Search")
      ("rpmfind"
       "https://rpmfind.net/linux/rpm2html/search.php?query=%s"
       nil)
      ("debian-pkg"
       "https://packages.debian.org/search\
?&searchon=names&suite=stable&section=all&arch=amd64&keywords=%s")
      ("debian-bts"
       "https://bugs.debian.org/cgi-bin/pkgreport.cgi?archive=yes&pkg=%s")
      ("freebsd-users-jp"
       "https://home.jp.FreeBSD.org/cgi-bin/namazu.cgi?key=\"%s\"&whence=0\
&max=50&format=long&sort=score&dbname=FreeBSD-users-jp"
       euc-japan)
      ("iij-archie"
       "https://www.iij.ad.jp/cgi-bin/archieplexform?query=%s\
&type=Case+Insensitive+Substring+Match&order=host&server=archie1.iij.ad.jp\
&hits=95&nice=Nice")
      ("waei"
       "https://dictionary.goo.ne.jp/search.php?MT=%s&kind=je"
       euc-japan)
      ("eiwa"
       "https://dictionary.goo.ne.jp/search.php?MT=%s&kind=ej")
      ("kokugo"
       "https://dictionary.goo.ne.jp/search.php?MT=%s&kind=jn"
       euc-japan)
      ("eiei"
       "https://www.dictionary.com/cgi-bin/dict.pl?term=%s&r=67")
      ,@(if ja
	    '(("amazon"
	       "https://www.amazon.co.jp/gp/search?\
__mk_ja_JP=%%83J%%83%%5E%%83J%%83i&url=search-alias%%3Daps&field-keywords=%s"
	       shift_jis)
	      ("amazon-en"
	       "https://www.amazon.com/exec/obidos/search-handle-form/\
250-7496892-7797857"
	       iso-8859-1
	       "url=index=blended&field-keywords=%s"))
	  '(("amazon"
	     "https://www.amazon.com/exec/obidos/search-handle-form/\
250-7496892-7797857"
	     iso-8859-1
	     "url=index=blended&field-keywords=%s")
	    ("amazon-ja"
	       "https://www.amazon.co.jp/gp/search?\
__mk_ja_JP=%%83J%%83%%5E%%83J%%83i&url=search-alias%%3Daps&field-keywords=%s"
	       shift_jis)))
      ("emacswiki" "https://www.emacswiki.org/cgi-bin/wiki?search=%s")
      ("en.wikipedia" "https://en.wikipedia.org/wiki/Special:Search?search=%s")
      ("de.wikipedia" "https://de.wikipedia.org/wiki/Spezial:Search?search=%s"
       utf-8)
      ("ja.wikipedia" "https://ja.wikipedia.org/wiki/Special:Search?search=%s"
       utf-8)
      ("msdn" "https://search.msdn.microsoft.com/search/default.aspx?query=%s")
      ("duckduckgo" "https://duckduckgo.com/?q=%s" utf-8)))
  "*An alist of search engines.
Each element looks like (ENGINE ACTION CODING POST-DATA)
ENGINE is a string, the name of the search engine.
ACTION is a string, the URL that performs a search.
ACTION must contain a \"%s\", which is substituted by a query string.
CODING is optional value which is coding system for query string.
POST-DATA is optional value which is a string for POST method search engine.
If CODING is omitted, it defaults to `w3m-default-coding-system'."
  :group 'w3m
  :type `(repeat
	  (group :indent 2
		 (string :format "Engine: %v\n")
		 (string :format "       Action: %v\n")
		 (coding-system :format "%t: %v\n")
		 (checklist :inline t
			    :entry-format ,(if (w3m-device-on-window-system-p)
					       "%b   %v"
					     "%b  %v")
			    (string :format "PostData: %v\n")))))

(defcustom w3m-search-default-engine "google"
  "*Name of the default search engine.
See also `w3m-search-engine-alist'."
  :group 'w3m
  :type 'string)

(defcustom w3m-search-word-at-point t
  "*Non-nil means that the word at point is used as an initial string.
If Transient Mark mode, this option is ignored and the region is used
as an initial string."
  :group 'w3m
  :type 'boolean)

(defvar w3m-search-engine-history nil
  "History variable used by `w3m-search' for prompting a search engine.")

(defvar w3m-search-thing-at-point-arg 'word
  "Argument for `thing-at-point' used in `w3m-search-read-query'")

(defun w3m-search-escape-query-string (str &optional coding)
  (mapconcat (lambda (s) (w3m-url-encode-string s coding))
	     (split-string str)
	     "+"))

(defun w3m-search-read-query (prompt prompt-with-default &optional history)
  "Read a query from the minibuffer, prompting with string PROMPT.
When a default value for the query is discovered, prompt with string
PROMPT-WITH-DEFAULT instead of string PROMPT."
  (let ((default
	  (if (w3m-region-active-p)
	      (buffer-substring (region-beginning) (region-end))
	    (unless (and (eq major-mode 'w3m-mode)
			 (listp (get-text-property (point-at-bol) 'face))
			 (memq 'w3m-header-line-location-title
			       (get-text-property (point-at-bol) 'face)))
	      (thing-at-point w3m-search-thing-at-point-arg))))
	initial)
    (when default
      (set-text-properties 0 (length default) nil default)
      (when (or w3m-search-word-at-point (w3m-region-active-p))
	(setq initial default
	      default nil))
      (when (w3m-region-active-p)
	(w3m-deactivate-region)))
    (read-string (if default
		     (format prompt-with-default default)
		   prompt)
		 initial history default)))

(defun w3m-search-read-variables (where)
  "Ask for a search engine and words to query and return them as a list.

WHERE is a string which should have the value \"current\" is the calling
function intends for the search results to be presented in the current
buffer, or \"new\" if in a new buffer."
  (when w3m-current-process
    (error "%s"
	   (substitute-command-keys "
Cannot run two w3m processes simultaneously \
\(Type `\\<w3m-mode-map>\\[w3m-process-stop]' to stop asynchronous process)")))
  (let* ((prompt-prefix (format "Search in %s buffer. " where))
	 (search-engine
	  (if current-prefix-arg
	      (let ((default (or (car w3m-search-engine-history)
				 w3m-search-default-engine))
		    (completion-ignore-case t))
		(completing-read (format "%sWhich engine? (default %s): "
					 prompt-prefix default)
				 w3m-search-engine-alist nil t nil
				 'w3m-search-engine-history default))
	    w3m-search-default-engine))
	 (query
	  (w3m-search-read-query
	   (format "%s %s search: " prompt-prefix search-engine)
	   (format "%s search (default %%s): " search-engine))))
    (list search-engine query)))

(defun w3m-search-do-search (w3m-goto-function search-engine query)
  "Call W3M-GOTO-FUNCTION with the URL for the search."
  (unless (string= query "")
    (let ((info (assoc search-engine w3m-search-engine-alist)))
      (if info
	  (let ((query-string (w3m-search-escape-query-string query
							      (caddr info)))
		(post-data (cadddr info)))
	    (w3m-history-store-position)
	    (funcall w3m-goto-function
		     (format (cadr info) query-string)
		     post-data
		     nil
		     (and post-data (format post-data query-string))))
	(error "Unknown search engine: %s" search-engine)))))

;;;###autoload
(defun w3m-search (search-engine query)
  "Search QUERY using SEARCH-ENGINE.

Search results will appear in the current buffer.

When called interactively with a prefix argument, you can choose one of
the search engines defined in `w3m-search-engine-alist'.  Otherwise use
`w3m-search-default-engine'.
If Transient Mark mode, use the region as an initial string of query
and deactivate the mark."
  (interactive (w3m-search-read-variables "current"))
  (w3m-search-do-search 'w3m-goto-url search-engine query))

;;;###autoload
(defun w3m-search-new-session (search-engine query)
  "Like `w3m-search', but do the search in a new buffer."
  (interactive (w3m-search-read-variables "new"))
  (w3m-search-do-search 'w3m-goto-url-new-session search-engine query))

;;;###autoload
(defun w3m-search-uri-replace (uri engine)
  "Generate query string for ENGINE from URI matched by last search."
  (let ((query (substring uri (match-end 0)))
	(info (assoc engine w3m-search-engine-alist)))
    (when info
      (format (cadr info)
	      (w3m-search-escape-query-string query (caddr info))))))

(provide 'w3m-search)

;;; w3m-search.el ends here
