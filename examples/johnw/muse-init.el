(require 'muse)
(require 'muse-mode)
(require 'muse-colors)
(require 'muse-project)
(require 'muse-book)

(require 'muse-html)
(require 'muse-latex)
(require 'muse-texinfo)

(require 'muse-journal)
(require 'muse-poem)
(require 'muse-message)

(require 'muse-http)

;;(require 'muse-arabic)
;;(require 'muse-cite)

(eval-after-load "whitespace"
  '(add-to-list 'whitespace-modes 'muse-mode))

(defun muse-maybe-convert-poem ()
  (if (string-match "/poems/" muse-publishing-current-file)
      (muse-poem-prepare-buffer)))

(defun muse-insert-reset-chapter ()
  (insert "\n\\setcounter{chapter}{1}\n"))

(defun muse-insert-all-poems-header ()
  (insert "\n\\renewcommand{\\poemtoc}{chapter}
\\settocdepth{chapter}\n"))

;; I use my own sectioning commands in conjunction with memoir.cls
(setcdr (assq 'chapter muse-latex-markup-strings)       "\\mychapter{")
(setcdr (assq 'section muse-latex-markup-strings)       "\\mysection{")
(setcdr (assq 'subsection muse-latex-markup-strings)    "\\mysubsection{")
(setcdr (assq 'subsubsection muse-latex-markup-strings) "\\mysubsubsection{")

;; Relocate the images directory
;(setcdr (assq 'image-with-desc muse-latex-markup-strings)
;	"\\includegraphics[width=\\textwidth]{../%s}")
(setcdr (assq 'image-with-desc muse-latex-markup-strings)
	"\\includegraphics[scale=0.6]{../%s}")
(setcdr (assq 'image-link muse-latex-markup-strings)
	"\\includegraphics[scale=0.6]{../%s}")
(setcdr (assq 'url-with-image muse-latex-markup-strings)
	"%% %s\n\\includegraphics[scale=0.6]{../%s}")

(muse-derive-style "site-html" "html"
		   :maintainer "jwiegley@hotmail.com"
		   :before 'muse-maybe-convert-poem
		   :after 'muse-my-html-finalize-buffer
		   :final 'muse-site-html-set-mode
		   :header "~/Documents/site/header.html"
		   :footer "~/Documents/site/footer.html")
(muse-derive-style "site-journal-html" "journal-html"
		   :maintainer "jwiegley@hotmail.com"
		   :before 'muse-my-journal-find-entries
		   :after 'muse-my-journal-insert-contents
		   :final 'muse-site-html-set-mode
		   :header "~/Documents/site/header.html"
		   :footer "~/Documents/site/footer.html")
(muse-derive-style "newartisans-html" "html"
		   :maintainer "johnw@newartisans.com"
		   :header "~/Sites/newartisans/header.html"
		   :footer "~/Sites/newartisans/footer.html")
(muse-derive-style "newartisans-journal-html" "journal-html"
		   :maintainer "johnw@newartisans.com"
		   :header "~/Sites/newartisans/header.html"
		   :footer "~/Sites/newartisans/footer.html")

(custom-set-variables
 '(muse-project-alist
   (quote
    (("website"				; my various writings
      (:book-part "Essays"
       :book-funcall muse-insert-reset-chapter
       "~/Documents/essays"
       :book-part "Stories"
       :book-funcall muse-insert-reset-chapter
       "~/Documents/stories"
       :book-part "Journal"
       :book-style "journal-book-pdf"
       :book-funcall muse-insert-reset-chapter
       "~/Documents/journal/early"
       "~/Documents/journal/summer2003"
       "~/Documents/journal/j2003"
       "~/Documents/journal/j2004"
       "~/Documents/journal/j2005"
       "~/Documents/journal/journal"
       "~/Documents/journal/pending"
       :book-part "Poems"
       :book-style "chapbook-pdf"
       :book-funcall muse-insert-all-poems-header
       :book-funcall muse-insert-reset-chapter
       :nochapters t  ; do automatically add chapters
       :book-chapter "Mystical"
       "~/Documents/poems/mystical"
       :book-chapter "Romance"
       "~/Documents/poems/romantic"
       :book-chapter "Nature"
       "~/Documents/poems/natural"
       :book-chapter "Melancholoy"
       "~/Documents/poems/melancholy"
       :book-chapter "Commentary"
       "~/Documents/poems/commentary"
       :book-end t
       "~/Documents/contents"
       "~/Documents/notes"
       :default "journal")

      (:base "site-html" :path "~/Sites/johnw"
       :include "/contents/recent")
      (:base "pdf" :path "~/Sites/johnw/pdf"
       :include "/\\(essays\\|stories\\)/")
      (:base "poem-pdf" :path "~/Sites/johnw/pdf"
       :include "/poems/")
      (:base "site-html" :path "~/Sites/johnw"
       :exclude "/journal/")
      (:base "journal-pdf" :path "~/Sites/johnw/pdf"
       :include "/journal/")
      (:base "site-journal-html" :path "~/Sites/johnw"
       :include "/journal/")
      (:base "journal-rdf" :path "~/Sites/johnw"
       :include "/journal/journal"
       :base-url "http://johnwiegley.com/")
      (:base "journal-rss" :path "~/Sites/johnw"
       :include "/journal/journal"
       :base-url "http://johnwiegley.com/")
      (:base "journal-rss" :path "~/Sites/johnw"
       :include "/journal/pending"
       :base-url "http://johnwiegley.com/"))
     ("thoughts"			; collected writings
      (:book-end t
       "~/Documents/thoughts/thoughts"
       :default "thoughts")
      (:base "journal-pdf" :path "~/Sites/johnw/pdf")
      (:base "site-journal-html" :path "~/Sites/johnw"))
     ("newartisans"			; my company
      ("~/Documents/newartisans"
       :default "index")
      (:base "newartisans-html" :path "~/Sites/newartisans"
       :exclude "/news")
      (:base "newartisans-journal-html" :path "~/Sites/newartisans"
       :include "/news"))
     ("planner"				; my company
      ("~/Private/plan"
       :default "TaskPool"
       :major-mode planner-mode)))))
 '(muse-mode-highlight-p t nil (muse-colors))
 '(muse-mode-auto-p t nil (muse-project))
 '(muse-latex-header "~/Documents/site/header.tex")
 '(muse-latex-footer "~/Documents/site/footer.tex")
 '(muse-book-latex-header "~/Documents/site/book-header.tex")
 '(muse-poem-latex-header "~/Documents/site/poem-header.tex")
 '(muse-poem-latex-footer "~/Documents/site/poem-footer.tex")
 '(muse-chapbook-latex-header "~/Documents/site/chapbook-header.tex")
 ;;'(muse-before-publish-hook (quote (muse-cite-munge-footnotes)))
 '(muse-mode-hook (quote (list footnote-mode turn-on-auto-fill flyspell-mode))))

(defun muse-publish-my-books (&optional force)
  (interactive "P")
  (muse-book-publish-project
   '("essays" ("~/Documents/essays"))
   "essays" "Collected Essays" "book-pdf" "~/Sites/johnw/pdf" force)
  (muse-book-publish-project
   '("stories" ("~/Documents/stories"))
   "stories" "Collected Stories" "book-pdf" "~/Sites/johnw/pdf" force)
  (muse-book-publish-project
   '("myjournal"
     ("~/Documents/journal/early"
      "~/Documents/journal/summer2003"
      "~/Documents/journal/j2003"
      "~/Documents/journal/j2004"
      "~/Documents/journal/j2005"
      "~/Documents/journal/journal"
      :book-end t
      "~/Documents/poems/mystical"
      "~/Documents/poems/romantic"
      "~/Documents/poems/natural"
      "~/Documents/poems/melancholy"
      "~/Documents/poems/commentary"))
   "myjournal" "Thought Journal" "journal-book-pdf" "~/Sites/johnw/pdf" force)
  (muse-book-publish-project
   '("poems"
     (:nochapters t  ; do automatically add chapters
      :book-chapter "Mystical"
      "~/Documents/poems/mystical"
      :book-chapter "Romance"
      "~/Documents/poems/romantic"
      :book-chapter "Nature"
      "~/Documents/poems/natural"
      :book-chapter "Melancholoy"
      "~/Documents/poems/melancholy"
      :book-chapter "Commentary"
      "~/Documents/poems/commentary"))
   "poems" "Collected Poems" "chapbook-pdf" "~/Sites/johnw/pdf" force)
  (muse-book-publish-project
   "website" "writings" "Collected Writings" "book-pdf"
   "~/Sites/johnw/pdf" force))

(defun modules-get-version-and-date (module)
  (let (version date)
    (with-temp-buffer
      (insert-file-contents-literally module nil 0 1000)
      (if (re-search-forward "Version:\\s-+\\(.*\\)" nil t)
	  (setq version (match-string 1))))
    (setq date (format-time-string "%Y-%m-%d"
				   (nth 5 (file-attributes module))))
    (concat (and muse-publishing-p "<span class=\"version\">")
	    (if version
		(format "%s (%s)" date version)
	      date)
	    (and muse-publishing-p "</span>"))))

(defun muse-blog-add-entry ()
  (interactive)
  (muse-project-find-file "journal" "website")
  (goto-char (point-min))
  (forward-line 3)
  (insert "* " (format-time-string "%Y%m%d: ")
	  (read-string "Journal entry title: ")
	  "\n\n\n\n")
  (forward-line -2))

(defun muse-my-html-insert-contents (&optional ignore)
  (let ((index 1)
	base contents l)
    (save-excursion
      (goto-char (point-min))
      (search-forward "Page published by Emacs Muse begins here" nil t)
      (catch 'done
	(while (re-search-forward "^<h\\([0-9]+\\)>\\(.+?\\)</h\\1>" nil t)
	  (unless (get-text-property (point) 'read-only)
	    (setq l (1- (string-to-number (match-string 1))))
	    (if (null base)
		(setq base l)
	      (if (< l base)
		  (throw 'done t)))
	    (when (<= l 1)
	      (setq contents (cons (cons l (muse-match-string-no-properties 2))
				   contents))
	      (goto-char (match-beginning 2))
	      (muse-html-insert-anchor (concat "sec" (int-to-string index)))
	      (setq index (1+ index)))))))
    (setq index 1 contents (reverse contents))
    (when (> (length contents) 0)
      (goto-char (point-min))
      (or (search-forward "<h2>Archives</h2>" nil t)
	  (search-forward "#include virtual=\"/sidebar.html\"" nil t))
      (beginning-of-line)
      (insert "<h2>Contents</h2>\n\n<ul>\n")
      (dolist (item contents)
	(insert "<li><a href=\"" (muse-publish-output-name)
		"#sec" (int-to-string index) "\">"
		(muse-publish-strip-tags (cdr item))
		"</a></li>\n")
	(setq index (1+ index)))
      (insert "</ul>\n"))))

(defun muse-my-html-finalize-buffer ()
  (when muse-publish-generate-contents
    (muse-my-html-insert-contents (cdr muse-publish-generate-contents))
    (setq muse-publish-generate-contents nil))
  (when (string= (muse-publish-output-name) "recent.html")
    (goto-char (point-min))
    (search-forward "Page published by Emacs Muse")
    (forward-line 1)
    (delete-region (point-min) (point))
    (search-forward "Page published by Emacs Muse")
    (beginning-of-line)
    (delete-region (point) (point-max))))

(defun muse-site-html-set-mode (file output-path final-target)
  (set-file-modes output-path ?\755))

(defvar muse-my-journal-entries nil)
(defvar muse-my-journal-nested t)

(defun muse-my-journal-find-entries ()
  (goto-char (point-min))
  (let ((heading-regexp (concat "^\\* " muse-journal-heading-regexp "$"))
	(inhibit-read-only t)
	entries)
    (while (re-search-forward heading-regexp nil t)
      (let ((begin (match-beginning 0))
	    (date (match-string 1))
	    (title (muse-match-string-no-properties 2))
	    enclosure qotd desc)
	(if title
	    (save-match-data
	      (if (string-match muse-explicit-link-regexp title)
		  (setq enclosure (match-string 1 title)
			title (match-string 2 title)))))
	(save-match-data
	  (when (and date
		     (string-match
		      (concat "\\([1-9][0-9][0-9][0-9]\\)[./]?"
			      "\\([0-1][0-9]\\)[./]?\\([0-3][0-9]\\)") date))
	    (setq date (encode-time 0 0 0
				    (string-to-number (match-string 3 date))
				    (string-to-number (match-string 2 date))
				    (string-to-number (match-string 1 date))
				    (current-time-zone)))))
	(while (string-match "\\*" title)
	  (setq title (replace-match "" nil nil title)))
	(unless muse-my-journal-nested
	  (let* ((path (muse-style-element :path))
		 (item-path
		  (concat (expand-file-name (format-time-string "%Y/%m")
					    path)
			  "/" (muse-journal-anchorize-title title)))
		 (end
		  (save-excursion
		    (if (re-search-forward heading-regexp nil t)
			(match-beginning 0)
		      (if (re-search-forward "^Footnotes:" nil t)
			  (match-beginning 0)
			(point-max)))))
		 (data (buffer-substring begin end))
		 (footnotes
		  (save-excursion
		    (if (re-search-forward "^Footnotes:" nil t)
			(buffer-substring (match-beginning 0) (point-max)))))
		 (project (muse-project)))
	    (save-excursion
	      (unless (file-directory-p (file-name-directory item-path))
		(make-directory  (file-name-directory item-path) t))
	      (find-file item-path)
	      (erase-buffer)
	      (insert "#title " title ?\n)
	      (insert "#date " (format-time-string "%B %e, %Y" date) ?\n)
	      (insert ?\n)
	      (setq begin (point))
	      (insert data)
	      (goto-char begin)
	      (forward-line 2)
	      (delete-region begin (point))
	      (goto-char (point-max))
	      (if footnotes
		  (insert ?\n footnotes))
	      (save-buffer)
	      (kill-buffer (current-buffer))
	      (let ((muse-my-journal-nested t)
		    (muse-current-project project))
		(muse-publish-file item-path "journal-pdf"
				   (file-name-directory item-path))
		(muse-publish-file item-path "site-journal-html"
				   (file-name-directory item-path)))
	      (delete-file item-path))))
	(set (make-local-variable 'muse-my-journal-entries)
	     (cons (cons title date)
		   muse-my-journal-entries))))))

(defun muse-my-journal-insert-contents ()
  (goto-char (point-min))
  (or (search-forward "<h2>Archives</h2>" nil t)
      (search-forward "#include virtual=\"/sidebar.html\"" nil t))
  (beginning-of-line)
  (if (string= "journal" (muse-page-name))
      (insert "<h2>Recent Entries</h2>\n\n<ul>\n")
    (insert "<h2>Contents</h2>\n\n<ul>\n"))
  (dolist (entry (nreverse muse-my-journal-entries))
    ;;(setq date (format-time-string "%m/%d" date))
    ;;(if (= ?0 (aref date 0))
    ;;	(setq date (substring date 1)))
    (insert (format "<li><a href=\"%s#%s\">%s</a></li>\n"
		    (muse-publish-output-name)
		    (muse-journal-anchorize-title (car entry))
		    (car entry))))
  (insert "</ul>\n\n")
  ;; jww (2005-04-17): a hack to rewrite MP3 titles
  (goto-char (point-min))
  (let ((inhibit-read-only t))
    (while (re-search-forward "<h2><a href=\"\\([^\"]+\\)\">\\(.+?\\)</a></h2>" nil t)
      (replace-match "<h2><a href=\"\\1\"><img src=\"images/speak.png\"></img></a>&nbsp;\\2</h2>"))))

;; (eval-when-compile
;;   (defvar muse-current-project))
;;
;; (defvar muse-ref-tag '("ref" nil t muse-ref-markup-tag))
;;
;; (defun muse-ref-markup-tag (beg end attrs)
;;   "This markup tag allows a poem to be included from another project page.
;; The form of usage is:
;;   <ref title=\"page.name[#subtitle]\">"
;;   (let ((page (cdr (assoc (cdr (assoc "title" attrs))
;;			  (muse-project-file-alist))))
;;	beg start end text)
;;     (if (null page)
;;	(insert "  *Reference to\n  unknown page \""
;;		(cdr (assoc "title" attrs)) "\".*\n")
;;       (setq beg (point))
;;       (let (title)
;;	(if (string-match "html" muse-publishing-current-style)
;;	    t
;;	  (insert
;;	   (with-temp-buffer
;;	     (insert-file-contents page)
;;	     (goto-char (point-min))
;;	     (forward-paragraph)
;;	     (forward-line)
;;	     (buffer-substring-no-properties (point) (point-max)))))))))
;;
;; (add-to-list 'muse-publish-markup-tags muse-ref-tag)

(when (and window-system (load "httpd" t))
  (require 'muse-http)
  ;;(add-hook 'after-init-hook 'httpd-start)
  (setq httpd-document-root (expand-file-name "~/Sites/johnw")))

;;(setq
;; muse-cite-titles
;; '(("Bahá'u'lláh"
;;    ("Kitáb-i-Íqán"
;;     "http://bahai-library.com/?file=bahaullah_kitab_iqan.html"
;;     "http://bahai-library.com/?file=bahaullah_kitab_iqan.html#%d"))
;;   ("`Abdu'l-Bahá"
;;    ("Promulgation of Universal Peace"
;;     "http://bahai-library.com/?file=abdulbaha_promulgation_universal_peace.html"
;;     "http://www.bahai-library.com/writings/abdulbaha/pup/pup.html#%d"))))

(provide 'muse-init)
