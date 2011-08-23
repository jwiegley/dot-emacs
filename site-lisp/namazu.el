;; -*- Mode: Emacs-Lisp -*-
;;
;; Mule 上で Namazu を利用した検索を行うための elisp です。
;;
;;  $Id: namazu.el,v 1.13 2000/02/24 06:48:33 kose Exp $

(defconst namazu-version "namazu.el 1.0.3")

;; Namazu による検索結果が指すドキュメント(類)が
;; ローカルディスク上にある場合にはそれを直接参照し、
;; ネットワーク上にある場合には brouse-url の機能を用いて
;; それを参照することができます。
;;
;; ローカルディスク上のドキュメント(類)が圧縮してある場合、
;; jka-compr の機能を用いてそれを展開しようとします。
;;
;; Namazu モードではローカルディスクにないファイルへの
;; アクセスについては brouse-url に一任しています。
;; そういったわけですので browse-url-browser-function に
;; 適切な設定をしておかないと、外部にあるリソースを
;; 参照することはできません。たとえばこんな設定をします:
;;
;;  (autoload 'namazu "namazu" nil t)
;;  (setq browse-url-browser-function 'browse-url-netscape)
;;
;; font-lock や hilit19 がロードしてあれば
;; 検索結果は(いくらか)華やかに表示されるでしょう。
;;
;; 用意する必要があるかも知れないもの:
;; 前述の通り browse-url が必要ですが、19.28 ベースの Mule には
;; これが含まれていないようです。同梱の "browse-url-for-emacs-19.28.el"
;; をお使い下さい。
;;
;; 検索方法:
;; 上記の設定を終えたら M-x namazu とタイプしてください。
;; すると検索のキー(条件式)を聞いてきますので namazu とか
;; ruby & perl といった検索キーを入力します。
;; 入力を終えると Namazu が起動され、
;; 検索結果を表示するバッファが作られます。
;; このバッファ内では以下のキー操作が定義されています。
;;
;;             前ページ    前項     次項    次ページ
;;   標準(1)      P         p        n         N
;;   標準(2)              [BkSp]  [Space]
;;   標準(3)              M-[Tab]  [Tab]
;;   vi 風        h         k        j         l
;;   カーソル   [left]     [up]    [down]   [right]
;;
;;   ページの先頭へ        <
;;   ページの末尾へ        >
;;   ドキュメントの参照    g または [Enter]
;;   条件を追加して再検索  r
;;   検索結果の消去        q
;;   namazu 終了           Q
;;   ヘルプ表示            ?
;;
;; また、mouse のまんなかのボタンを押すと、押した位置によって、
;; "ドキュメントの参照"、"前ページ"、 "次ページ" のどれかの動作を行な
;; います。
;;
;; デフォルト以外のインデックス(NMZ.*)を使用したい場合は、
;; C-u M-x namazu とタイプすることでインデックスの置いてあるディレクト
;; リを指定することも出来ます。また、個々のディレクトリに対して別名を
;; 定義することも可能です。設定例など詳しいことは namazu-dir-alist の
;; 説明を参照してください :-P。
;;
;; 最新版の入手について:
;; namazu.el の最新版は namazu に付属するものや、namazu ML などで
;; 入手可能です.
;;
;; 配布条件など:
;; これは まつもと ゆきひろ <matz@netlab.co.jp> さんが作成し、
;; 同氏と 馬場 肇 <baba@kusastro.kyoto-u.ac.jp> さん、
;; 高林 哲 <ccsatoru@vega.aichi-u.ac.jp> さん、
;; Toshiaki Tanaka <toshiaki@ksj1.kansai-sc.toshiba.co.jp>さん、
;; 奥西 藤和 <fuji0924@mbox.kyoto-inet.or.jp> さんのご協力の下で
;; やまだ あきら <akira@linux.or.jp> さんが改造を加えたものを、
;; 土屋 雅稔 <tsuchiya@pine.kuee.kyoto-u.ac.jp> さん、
;; 堀口恭太郎 <kyota@po.ntts.co.jp> さん達の叱咤激励により
;; Namazu Project が改造しているものです。
;; いかなる形での利用・再配布についても権利の類は一切主張しません。
;; 自由に扱ってもらって構いません。
;;
;; お約束:
;; これは何らかの保証を伴うものではありません。
;; 提供される機能を使った結果、利用者が直接的あるいは間接的に
;; 損害を被ったとしても、それは作者達の関知するところではありません。
;; あくまで at your own risk でご利用下さい。
;;

;; CUSTOM emulation derived from BBDB and APEL.
(eval-and-compile
  (condition-case ()
      (require 'custom)
    (error nil))
  (if (and (featurep 'custom) (fboundp 'custom-declare-variable))
      nil ;; We've got what we needed
    ;; We have the old custom-library, hack around it!
    (defmacro defgroup (&rest args)
      nil)
    (defmacro defcustom (var value doc &rest args) 
      (` (defvar (, var) (, value) (, doc))))
    (defmacro defface (var value doc &rest args)
      (` (make-face (, var))))
    (defmacro define-widget (&rest args)
      nil)))

(defgroup namazu nil
  "Namazu front-end for Emacs."
  :group 'external)

(defcustom namazu-command "namazu"
  "*Namazu の検索用プログラム名です。
通常は namazu などでしょうが、そうではない場合や
PATH が通っていない場合には適当なプログラム名を指定します。"
  :type 'string
  :group 'namazu)

(defcustom namazu-search-num 30
  "*Namazu の検索結果を一度に表示する件数です。"
  :type 'integer
  :group 'namazu)

(defcustom namazu-default-dir nil
  "*Namazu が参照するインデックスの置いてあるディレクトリ名です。
特に指定しなければデフォルトのインデックスを参照します。
複数のインデックスを指定する場合にはそれぞれを空白で区切ってください。"
  :type '(choice
	  (item :tag "Auto" :value nil)
	  (directory :tag "Default Index"))
  :group 'namazu)

(defcustom namazu-dir-alist nil
  "*インデックスが置いてあるディレクトリに
シンボリックな名前をつけるための alist です。
  '((\"Namazu\" . \"/usr/doc/namazu/index /var/lib/namazu/index\")
    (\"Ruby\" . \"/usr/doc/ruby/namazu\"))
などのように設定しておくと、個々のインデックスファイルのある
ディレクトリ名を指定する代わりに Namazu や Ruby といった
いわば別名を指定することができます。
複数のインデックスを指定する場合にはそれぞれを空白で区切ってください。"
  :type '(repeat (cons :format "%v"
		       (string :tag "Alias")
		       (string :tag "Index path")))
  :group 'namazu)

(defcustom namazu-always-query-index-directory nil
  "*nil 以外の値を設定すると、数値引数がないときに
インデックスファイルを指定でき、数値引数があるときに
デフォルトのインデックスを参照するようになります。
常にインデックスファイルを指定して検索を行いたい
場合などに便利かもしれません。"
  :type 'boolean
  :group 'namazu)

(defcustom namazu-auto-turn-page nil
  "*nil 以外の値を設定すると、自動的にページめくりをします。"
  :type 'boolean
  :group 'namazu)

(defcustom namazu-mode-hook nil
  "*Namazu モードを作成するタイミングで呼ばれる hook です。"
  :type 'hook
  :group 'namazu)

(defcustom namazu-display-hook nil
  "*Namazu の出力を表示するときに呼ばれる hook です。"
  :type 'hook
  :group 'namazu)

(defcustom namazu-url-regex "^\\(https?://\\|ftp://\\)"
  "*URL と見なすファイル名のパターンを設定します。"
  :type 'regexp
  :group 'namazu)

(defcustom namazu-view-function-alist
  '(("[^/]+\\.s?html?" . namazu-browse-url)
    ("/Mail\\|News/.*/[1-9][0-9]*$" . namazu-view-msg)
    ("man/man" . namazu-man)
    ;; ("/usr/local/info/\\|\\.info" . namazu-info) ;; 未作成
    ("." . namazu-view-file))
  "*ファイル名のパターンとそれに対応する閲覧関数を設定します。"
      :type '(repeat (cons :format "%v"
			   (regexp :tag "Filename Regexp")
			   (symbol :tag "Function Name")))
      :group 'namazu)

(defcustom namazu-view-other-window nil
  "*If non-nil, make an other window when namazu-view."
  :type 'boolean
  :group 'namazu)

(defcustom namazu-view-other-frame nil
  "*If non-nil, make an other frame when namazu-view."
  :type 'boolean
  :group 'namazu)

(defcustom namazu-msg-visible-field (list "subject" "from" "to" "newsgroups" "date")
  "*Visible header list for namazu-view-msg."
  :type '(repeat (string :tag "Header"))
  :group 'namazu)

(defcustom namazu-msg-highlight-function nil
  "*A function, view-msg highlight method.
e.g.
  namazu-msg-highlight-mew -- use Mew functions(require Mew 1.94 or later)."
  :type '(radio (function-item :tag "use Mew functions"
			       :format "%t\n"
			       namazu-msg-highlight-mew)
		(function :tag "Other"))
  :group 'namazu)

(defvar namazu-cs-write
  (if (memq system-type '(OS/2 emx windows-nt))
      (if (> emacs-major-version 19) 'sjis-dos '*sjis*dos)
    (if (> emacs-major-version 19) 'euc-jp '*euc-japan*))
  "*Coding system for namazu process (output).")

(defvar namazu-cs-read
  (if (> emacs-major-version 19) 'undecided '*autoconv*)
  "*Coding system for namazu process (input).")

(defvar namazu-config-file-path
  (list (getenv "NAMAZUCONFPATH")
	(getenv "NAMAZUCONF")		; obsolete?
	"./.namazurc"
	"~/.namazurc"
	"/usr/local/etc/namazu/namazurc"
	"/usr/local/namazu/lib/namazurc") ;obsolete?
  "*Search path for a Namazu configuration file.")

(defvar namazu-argument "-H"
  "*Namazu の検索用プログラムを起動する際に指定する引数です。")

;;
;; ここから先をいじって、素敵になったら教えてくださいね。
;;

(defvar namazu-fill-prefix "\t")
(defvar namazu-header-prefix "   ")
(defvar namazu-index-history '(""))
(defvar namazu-keyword-history '(""))
(defvar namazu-mode-map nil)
(defvar namazu-minibuffer-map nil)
(defvar namazu-minibuffer-field-map nil)
(defvar namazu-buffer "*namazu*")
(defvar namazu-last-dir nil
  "現在の検索で参照しているインデックスの在処")
(defvar namazu-current-page 0
  "閲覧中の検索結果のページ番号")
(defvar namazu-max-page 0
  "現在の検索結果の最大ページ番号")
(defvar namazu-output-title-pattern
  "^\\([0-9]+\\.\\) \\(.*\\) \\(([^)]*)\\)$"
  "検索結果の中のドキュメントのタイトルを示す行のパターン")
(defvar namazu-output-header-pattern
  (format "^%s\\([^:]+:.*\\)$" namazu-header-prefix)
  "検索結果の中の From、Date ヘッダを示すパターン")
(defvar namazu-output-url-pattern
  "^\\(\\(~?/\\|[a-z]+:\\)[^ ]+\\) \\(.*\\)$"
  "検索結果の中のドキュメントの在処(URL)を示す行のパターン")
(defvar namazu-output-current-list-pattern
  "^[^:]+: [0-9]+ - [0-9]+$"
  "検索結果の中のどの部分を閲覧中かを示す行のパターン")
(defvar namazu-output-pages-pattern
  "^[^:]+: \\(\\[[0-9]+\\]\\)*\\[\\([0-9]+\\)\\]$"
  "検索結果のページ数を示す行のパターン")
(defvar namazu-view-vismark nil)

(and (locate-library "browse-url") (require 'browse-url))
(and (locate-library "jka-compr") (require 'jka-compr))
(provide 'namazu)

(defun namazu (&optional page-num namazu-dir key)
  "namazu-command を起動して検索を行います。"
  (interactive
   (list
    0
    (if (or (and (not namazu-always-query-index-directory) current-prefix-arg)
	    (and namazu-always-query-index-directory (not current-prefix-arg)))
	(read-from-minibuffer "Namazu index directory: " nil
			      namazu-minibuffer-map nil 'namazu-index-history)
      nil)
    (read-from-minibuffer "Enter Keyword: " nil
			  namazu-minibuffer-field-map nil 'namazu-keyword-history)))
  (let ((buffer (get-buffer-create namazu-buffer))
	(dir (or namazu-dir
		 (progn
		   (or namazu-default-dir
		       (setq namazu-default-dir (namazu-get-default-index-dir)))
		   (expand-file-name namazu-default-dir))))
	(arg-list (if (listp namazu-argument)
		      namazu-argument (list namazu-argument))))
    (setq arg-list (append
		    arg-list
		    (list "-n" (int-to-string namazu-search-num)
			  "-w" (int-to-string (* page-num namazu-search-num))
			  key)))
    (if (and dir (not (string= dir "")) (string-match "[^ \t]" dir))
	(setq arg-list (append arg-list
			       (namazu-split-dir (namazu-expand-dir-alias dir)))))
    (set-buffer buffer)
    (setq buffer-read-only nil)
    (buffer-disable-undo (current-buffer))
    (erase-buffer)
    (message "Namazu running ...")
    (let ((default-process-coding-system (cons namazu-cs-read namazu-cs-write))
	  (process-input-coding-system namazu-cs-read)
	  (process-output-coding-system namazu-cs-write)
	  (coding-system-for-read namazu-cs-read)
	  (coding-system-for-write namazu-cs-write))
      (apply (function call-process) namazu-command nil t nil arg-list))
    (if (not (and buffer
		  (get-buffer buffer)
		  (buffer-name (get-buffer buffer))))
	(message "Namazu exits with no output")
      (pop-to-buffer buffer)
      (goto-char (point-min))
      (save-excursion
	(namazu-fill)
	(if (re-search-forward namazu-output-pages-pattern nil t)
	    (setq namazu-max-page
		  (+ -1 (string-to-int (buffer-substring
					(match-beginning 2) (match-end 2)))))
	  (setq namazu-max-page 0)))

      ;(goto-char (point-min))
      (setq namazu-current-page page-num)
      (setq namazu-last-dir dir)
      (namazu-mode)
      (setq buffer-read-only t)
      (run-hooks 'namazu-display-hook)
      (message "Namazu running ... done.") )))

(defun namazu-fill ()
  "namazu-command での検索結果を整形します。"
  (while (re-search-forward "^[0-9]+\. " nil t)
    (beginning-of-line 2)
    (let ((start-point (point)))
      (re-search-forward "^$" nil t)
      (forward-line -1)
      ;; there is URL or file name
      (if (looking-at namazu-output-url-pattern)
	  (forward-line -1))
      ;; there is description
      (if (> (point) start-point)
	  (save-excursion
	    (while (> (point) start-point)
	      (forward-line -1)
	      (insert namazu-header-prefix)
	      (beginning-of-line))
	  ))
      ;; there is description
      (let ((fill-column default-fill-column)
	    (fill-prefix namazu-fill-prefix)
	    (enable-kinsoku nil))
	(insert namazu-fill-prefix)
	(fill-region (point)
		     (save-excursion (forward-line 1) (point))))
      ;; 余分な空行をとっぱらうための努力
      (re-search-forward "^$" nil t)
      (while (looking-at "^$")
	(delete-char 1)
	(forward-line 1))
      )))

(defun namazu-re-search (&optional key)
  "現在の検索キーを変更した上で再検索します。"
  (interactive
   (list
    (save-excursion
      (read-from-minibuffer "Enter Keyword: "
			    (cons (car namazu-keyword-history) 1)
			    namazu-minibuffer-field-map
			    nil 'namazu-keyword-history))))
  (namazu 0 namazu-last-dir key))

(defun namazu-next-page ()
  "次のページの検索結果へ移動します。"
  (interactive)
  (if (< namazu-current-page namazu-max-page)
      (namazu (+ 1 namazu-current-page) namazu-last-dir (car namazu-keyword-history))
    t))

(defun namazu-prev-page ()
  "前のページの検索結果へ移動します。"
  (interactive)
  (if (> namazu-current-page 0)
      (namazu (+ -1 namazu-current-page) namazu-last-dir (car namazu-keyword-history))
    t))

(defun namazu-dir-complete ()
  "ディレクトリ名または namazu-dir-alist からの
文字列補完を行います。"
  (interactive)
  (let ((input (buffer-substring 1 (point)))
	(alist namazu-dir-alist)
	dir file files compl all sub-input mb)
    (if (string-match "\\(^\\|\\(\\\\\\\\\\)*[^\\\\] \\)\\(\\(\\(\\\\\\\\\\)*\\\\ \\|[^ ]\\)*/\\)?\\([^/]*\\)$" input)
	(progn
	  (setq mb (match-end 1))
	  (save-match-data
	    (setq sub-input
		  (namazu-unescape-dir
		   (substring input mb (match-end 6)))))
	  (save-match-data
	    (setq dir
		  (namazu-unescape-dir
		   (substring input mb (match-beginning 6)))))
	  (setq file (substring input (match-beginning 6) (match-end 6)))
	  ;; HOME からの相対パスの処理
	  (if (and (string= dir "")
		   (string-match  "^~" file))
	      (progn (setq dir file) (setq file "")))
	  ;; ディレクトリの場合の処理
	  (setq files (and (file-exists-p dir)
			   (file-directory-p dir)
			   (directory-files dir t "^[^.]")))
	  (while files
	    (if (file-directory-p (car files))
		(setq alist
		      (append alist
			      (list (cons (concat (car files) "/")
					  (car files))))))
	    (setq files (cdr files)))
	  ;; Completion-List の作成
	  (setq compl (or (try-completion sub-input alist)
			  (try-completion (expand-file-name sub-input) alist)))
	  (setq all (or (all-completions sub-input alist)
			(all-completions (expand-file-name sub-input) alist)))
	  (cond ((stringp compl)
		 (delete-region (+ mb 1) (point-max))
		 (insert (namazu-escape-dir compl))
		 (with-output-to-temp-buffer "*Completions*"
		   (display-completion-list all)))
		(compl
		 nil)
		(t
		 (beep)))
	  )
      (beep))))

(defun namazu-escape-dir (dir)
  "ディレクトリ中の \"\\\" と \" \" をエスケープします。"
  (let ((tmpdir1 dir) (tmpdir2 ""))
    (while (string-match "\\([ \\]\\)" tmpdir1)
      (setq tmpdir2
	    (concat tmpdir2
		    (substring tmpdir1 0 (match-beginning 0))
		    "\\" (substring tmpdir1
				    (match-beginning 1) (match-end 1))))
      (setq tmpdir1 (substring tmpdir1 (match-end 0))))
    (concat tmpdir2 tmpdir1)))

(defun namazu-unescape-dir (dir)
  "ディレクトリ中の \"\\\" と \" \" をエスケープします。"
  (let ((tmpdir1 dir) (tmpdir2 ""))
    (while (string-match "\\\\\\([ \\]\\)" tmpdir1)
      (setq tmpdir2
	    (concat tmpdir2
		    (substring tmpdir1 0 (match-beginning 0))
		    (substring tmpdir1
			       (match-beginning 1) (match-end 1))))
      (setq tmpdir1 (substring tmpdir1 (match-end 0))))
    (concat tmpdir2 tmpdir1)))

(defun namazu-split-dir (dirs)
  "インデックスディレクトリ文字列を分割し、\"~\" などを展開します。"
  (let ((tmpdir1 dirs) (dir-list (list))
	(nmz-expand-filename (function (lambda (f)
		(expand-file-name (namazu-unescape-dir 
		    (or (cdr (assoc f namazu-dir-alist)) f)))))))
    (while (string-match "\\([^\\\\]\\) " tmpdir1)
      (save-match-data
	(setq dir-list
	      (append dir-list
		      (list (funcall nmz-expand-filename
			      (substring tmpdir1 0 (match-end 1)))))))
      (setq tmpdir1 (substring tmpdir1 (match-end 0))))
    (if dirs
	(append dir-list (list (funcall nmz-expand-filename tmpdir1)))
      dir-list)))

(defun namazu-expand-dir-alias (dir)
  "インデックスディレクトリ文字列中のエイリアスを展開します。"
  (and dir namazu-dir-alist
       (let ((alist namazu-dir-alist))
	 (while alist
	   (while (string-match
		   (concat "\\(^\\| \\|\t\\)\\("
			   (regexp-quote (car (car alist)))
			   "\\)\\( \\|\t\\|$\\)") dir)
	     (setq dir (concat (substring dir 0 (match-beginning 2))
			       (cdr (car alist))
			       (substring dir (match-beginning 3)))))
	   (setq alist (cdr alist)))))
  dir)

(defun namazu-field-complete ()
  "+to:field の補完をします。"
  (interactive)
  (goto-char (point-max))
  (let ((p (point))
        (alist (namazu-make-field-completion-alist namazu-last-dir))
        (completion-buffer "*Completions*")
        word start result)
    (save-excursion
      (if (re-search-backward "\\+[^ \t]*" nil t)
	  (progn
	    (setq start (match-beginning 0))
	    (setq word (match-string 0))
	    (setq result (try-completion word alist)))))
    (cond
     ((eq result t)
      (ding))
     ((eq result nil)
      (ding))
     ((string= result word)
      (with-output-to-temp-buffer completion-buffer
        (display-completion-list
         (all-completions word alist))))
     (t
      (delete-region start p)
      (insert result)
      (if (eq t (try-completion result alist))
          ()
        (ding))))))

(defun namazu-make-field-completion-alist (namazu-dirs)
  "make \'+files:\' completion alist."
  (let (dir flist fields fname el
	 (dirs (namazu-split-dir 
		(or namazu-dirs namazu-default-dir
		    (setq namazu-default-dir (namazu-get-default-index-dir))))))
    (while (setq dir (car dirs))
      (if (file-exists-p dir)
	  (setq flist (append (directory-files dir) flist)))
      (setq dirs (cdr dirs)))
    (while (setq fname (car flist))
      (and (string-match "NMZ.field.\\([^.]+\\)\\'" fname)
	   (setq el (list (format "+%s:"
              (substring fname (match-beginning 1) (match-end 1)))))
	   (if (not (member el fields))
	       (setq fields (append (list el) fields))))
      (setq flist (cdr flist)))
    fields))

(defun namazu-search-config-file ()
  "Search namazu-config-file-path for a Namazu configuration file.
Return the abosolute file name of the configuration.  When the file is
not found, return nil "
  (let ((config-file-list namazu-config-file-path) config-file)
    (setq config-file-list (delq nil config-file-list))
    (if (catch 'found
	  (while config-file-list
	    (setq config-file (expand-file-name (car config-file-list)))
	    (and (file-exists-p config-file)
		 (throw 'found t))
	    (setq config-file-list (cdr config-file-list))))
	config-file
      nil)))

(defun namazu-read-config-file (file)
  "Read a namazu configuration file and return an alist of directive
and value(s) pairs.
FILE indicates the absolute file name of the configuration file. FILE
must exists."
  (let* (conf-alist
	 (buffer (get-file-buffer file))
	 (buffer-already-there-p buffer))
    (or buffer-already-there-p
	(setq buffer (find-file-noselect file)))
    (unwind-protect
	(save-excursion
	  (set-buffer buffer)
	  (goto-char (point-min))
	  (let (directive value1 value2)
	    (while (re-search-forward "\\(^[ \t]*\\(INDEX\\|BASE\\|\
LOGGING\\|LANG\\|SCORING\\)[ \t]+\\([^ \t\n#]+\\)\\)\\|\
\\(^[ \t]*\\(REPLACE\\)[ \t]+\\([^ \t\n#]+\\)[ \t]+\\([^ \t\n#]+\\)\\)" nil t)
	      (cond ((match-string 1)   ; only 1 value
		     (setq directive (match-string 2))
		     (setq value1 (match-string 3))
		     (setq conf-alist
			   (delete (assoc directive conf-alist) conf-alist))
		     (setq conf-alist
			   (cons (cons directive value1) conf-alist)))
		    ((match-string 4)	; 2 values
		     (setq directive (match-string 5))
		     (setq value1 (match-string 6))
		     (setq value2 (match-string 7))
		     (setq conf-alist
			   (delete (assoc directive conf-alist) conf-alist))
		     (setq conf-alist
			   (cons (list directive value1 value2)
				 conf-alist)))))))
      (if (not buffer-already-there-p)
	  (kill-buffer buffer)))
    conf-alist))

(defun namazu-get-default-index-dir ()
  "Get a Namazu default index directory from a Namazu configuration file.
Return \"/usr/local/namazu/index\" if the configuration file is not
found."
  (let (config-file conf-alist cell dir)
    (setq config-file (namazu-search-config-file))
    (if config-file
	(progn
	  (setq conf-alist (namazu-read-config-file config-file))
	  (setq cell (assoc "INDEX" conf-alist))
	  (and cell
	       (setq dir (cdr cell)))
	  dir)
      "/usr/local/namazu/index")))

(defun namazu-mode ()
  "Namazu の検索結果を閲覧するためのモードです。

binding          key
-------          ---
前のページ       P           / h / [left]
前の項目         p / [BkSp]  / k / [up]    / M-[Tab]
後の項目         n / [Space] / j / [down]  / [Tab]
後のページ       N           / l / [right]

ページの先頭へ   <
ページの末尾へ   >
文書を参照       g / [Enter]
再検索           r / f
検索結果消去     q
Namazu 終了      Q
ヘルプ表示       ?

mouse の真ん中のボタンを押すと、押した位置によって、\"文章を参照\"、
\"前のページ\"、\"後ろのページ\" のどれかの処理を実行します。
"
  (interactive)
  (save-excursion
    (if (eq major-mode 'namazu-mode)
	()
      (kill-all-local-variables)
      (use-local-map namazu-mode-map)
      (setq mode-name "Namazu")
      (setq major-mode 'namazu-mode)
      (run-hooks 'namazu-mode-hook))))

(defun namazu-jump-next ()
  "検索結果の次の項目へ移動します。"
  (interactive)
  (let ((pos (point)))
    (forward-line 1)
    (if (re-search-forward namazu-output-url-pattern nil t)
	(beginning-of-line)
      (goto-char pos)
      (if (and namazu-auto-turn-page
	       (< namazu-current-page namazu-max-page))
	  (progn
	    (namazu-next-page)
	    (namazu-jump-next))))))

(defun namazu-jump-prev ()
  "検索結果の一つ前の項目へ移動します。"
  (interactive)
  (if (re-search-backward namazu-output-url-pattern nil t)
      (if (save-excursion
	    (let ((ws (window-start)))
	      (if (re-search-backward "^$" nil t)
		  (and (>= ws (point))
		       (< 1 (count-lines ws (point))))
		nil)))
	  (recenter))
    (if (and namazu-auto-turn-page
	     (> namazu-current-page 0))
	(progn
	  (namazu-prev-page)
	  (end-of-buffer)
	  (namazu-jump-prev)))))

(defun namazu-view-at-mouse (event)
  "mouse を使ってブラウズしたりページを移動したりします。"
  (interactive "e")
  (set-buffer (event-buffer event))
  (goto-char (event-point event))
  (let ((pos (point))
	pos-title pos-url)
    (end-of-line)
    (and (re-search-backward namazu-output-title-pattern nil t)
	 (setq pos-title (point))
	 (goto-char pos)
	 (re-search-forward namazu-output-title-pattern nil t)
	 (re-search-backward namazu-output-url-pattern nil t)
	 (> (point) pos-title)
	 (setq pos-url (point))
	 (setq pos (point)))
    (goto-char pos)
    (beginning-of-line)
    (and (not pos-url)
	 (re-search-forward namazu-output-url-pattern nil t)
	 (setq pos-url (point)))
    (goto-char pos)
    (cond
     ((and pos-title pos-url)
      (namazu-view))
     ((and pos-url (> namazu-current-page 0))
      (namazu-prev-page))
     ((and pos-title (< namazu-current-page namazu-max-page))
      (namazu-next-page))
     (t (message "nothing to do.")))))

;; emacs 向けの定義
(eval-and-compile
  (or (fboundp 'event-buffer)
      (defun event-buffer (event)
	(window-buffer (posn-window (event-start event))))))

(eval-and-compile
  (or (fboundp 'event-point)
      (defun event-point (event)
	(posn-point (event-start event)))))

(eval-and-compile
  (or (fboundp 'match-string)
      (defun match-string (num &optional string)
	(if (match-beginning num)
	    (if string
		(substring string (match-beginning num) (match-end num))
	      (buffer-substring (match-beginning num) (match-end num)))))))

(defun namazu-view ()
  "ポイントが位置する項目をブラウズします。"
  (interactive)
  (beginning-of-line)
  (if (re-search-forward namazu-output-url-pattern nil t)
      (let ((url (buffer-substring (match-beginning 1) (match-end 1))))
        (beginning-of-line)
        (sit-for 0)
        (and (string-match "^/\\([a-zA-Z]\\)|\\(/.*\\)$" url)
	     ;; if DOS/Windows /c|...
	     (setq url
		   (concat (substring url (match-beginning 1) (match-end 1))
			   ":"
			   (substring url (match-beginning 2) (match-end 2)))))
	(if (string-match namazu-url-regex url)
	    (namazu-browse-url url)
	  (let ((ext '("" ".gz" ".Z" "bz2"))
		(fl namazu-view-function-alist)
		(file (expand-file-name url)) (name "") path done)
	    (and (string-match "\\(.*\\)\\(#.*\\)$" url)
		 (setq file (substring url (match-beginning 1) (match-end 1)))
		 (setq name (substring url (match-beginning 2) (match-end 2))))
	    (while (and (null done) ext)
	      (setq path (concat file (car ext)))
	      (and (file-exists-p path)
		   (setq done t)
		   (while fl
		     (if (string-match (car (car fl)) path)
			 (progn
			   (funcall (cdr (car fl)) (concat path name))
			   (setq fl nil)))
                     (setq fl (cdr fl))))
	      (setq ext (cdr ext))))))))

(defun namazu-view-file (&optional file)
  "View file function."
  (interactive "fView message: ")
  (if (and window-system namazu-view-other-frame)
      (view-file-other-frame file)
    (if namazu-view-other-window
	(view-file-other-window file)
      (view-file file)))
  ;; xxx
  (if (and (boundp 'view-mode-map) view-mode-map)
      (define-key view-mode-map "," 'namazu-view-top))
  (if (and (boundp 'view-minor-mode-map) view-minor-mode-map)
      (define-key view-minor-mode-map "," 'namazu-view-top))
  (make-local-variable 'namazu-view-vismark))

(defun namazu-view-msg (&optional file)
  "View message function."
  (namazu-view-file file)
  (let ((buffer-read-only nil)
	(vis-head "")
	hspos)
    (goto-char (point-min))
    (if (not (re-search-forward "^$" nil t))
	()
      (save-excursion
	(save-restriction
	  (narrow-to-region (point-min) (point))
	  (mapcar (function
		   (lambda (head)
		     (goto-char (point-min))
		     (if (not (re-search-forward (concat "^" head ":") nil t))
			 ()
		       (beginning-of-line)
		       (setq hspos (point))
		       (forward-line 1)
		       (while (looking-at "^[ \t]+")
			 (forward-line 1))
		       (setq vis-head
			     (concat vis-head (buffer-substring hspos (point))))
		       (delete-region hspos (point)))))
		  namazu-msg-visible-field)
	  (goto-char (point-max))
	  (setq namazu-view-vismark (point-marker))
	  (insert vis-head)
	  (condition-case err
	      (cond
	       ((fboundp 'mew-header-decode-region)
		(mew-header-decode-region 'text (point-min) (point-max) t))
	       ((fboundp 'eword-decode-region)
		(eword-decode-region (point-min) (point-max) t)))
	    (error nil))
	  (widen)))
      (goto-char namazu-view-vismark)
      (recenter 0)
      (if namazu-msg-highlight-function
	  (funcall namazu-msg-highlight-function))
      (set-visited-file-name nil)
      (set-buffer-modified-p nil))))

(defun namazu-view-top ()
  "goto namazu view top point."
  (interactive)
  (if (and (boundp 'namazu-view-vismark)
	   (markerp namazu-view-vismark))
      (goto-char namazu-view-vismark)
    (goto-char (point-min)))
  (recenter 0))

(defun namazu-browse-url (url)
  "browse-url を使って表示します。
使用する browser は browse-url-browser-function で指定します。"
  (interactive)
  (setq url (browse-url-file-url url))
  (if (fboundp 'browse-url)
      (browse-url url)
    (funcall browse-url-browser-function url)))

(defun namazu-man (file)
  "manual を表示します。"
  (interactive)
  (require 'man)
  (let ((manual-program "nroff -man -h"))
    (Man-getpage-in-background file)))

(defun namazu-exit ()
  "namazu を終了します。"
  (interactive)
  (if (and (get-buffer namazu-buffer)
	   (buffer-name (get-buffer namazu-buffer)))
      (kill-buffer namazu-buffer)))

(if namazu-mode-map
    nil
  (setq namazu-mode-map (make-keymap))
  (suppress-keymap namazu-mode-map)
  (define-key namazu-mode-map "P"     'namazu-prev-page)
  (define-key namazu-mode-map "p"     'namazu-jump-prev)
  (define-key namazu-mode-map "n"     'namazu-jump-next)
  (define-key namazu-mode-map "N"     'namazu-next-page)

  (define-key namazu-mode-map "\177"  'namazu-jump-prev)
  (define-key namazu-mode-map " "     'namazu-jump-next)

  (define-key namazu-mode-map "\M-\t" 'namazu-jump-prev)
  (define-key namazu-mode-map "\t"    'namazu-jump-next)

  (define-key namazu-mode-map "h"     'namazu-prev-page)
  (define-key namazu-mode-map "k"     'namazu-jump-prev)
  (define-key namazu-mode-map "j"     'namazu-jump-next)
  (define-key namazu-mode-map "l"     'namazu-next-page)

  (define-key namazu-mode-map [left]  'namazu-prev-page)
  (define-key namazu-mode-map [up]    'namazu-jump-prev)
  (define-key namazu-mode-map [down]  'namazu-jump-next)
  (define-key namazu-mode-map [right] 'namazu-next-page)

  (define-key namazu-mode-map "<"     'beginning-of-buffer)
  (define-key namazu-mode-map ">"     'end-of-buffer)
  (define-key namazu-mode-map "\r"    'namazu-view)
  (define-key namazu-mode-map "g"     'namazu-view)
  (define-key namazu-mode-map "r"     'namazu-re-search)
  (define-key namazu-mode-map "q"     'bury-buffer)
  (define-key namazu-mode-map "Q"     'namazu-exit)
  (define-key namazu-mode-map "?"     'describe-mode)

  (if (string-match "XEmacs" emacs-version)
      (define-key namazu-mode-map [(button2)] 'namazu-view-at-mouse)
    (define-key namazu-mode-map [mouse-2] 'namazu-view-at-mouse)))

(if namazu-minibuffer-map
    nil
  (let ((map (copy-keymap minibuffer-local-map)))
    (define-key map "\t" 'namazu-dir-complete)
    (setq namazu-minibuffer-map map)))

(if namazu-minibuffer-field-map
    nil
  (let ((map (copy-keymap minibuffer-local-map)))
    (define-key map "\t" 'namazu-field-complete)
    (setq namazu-minibuffer-field-map map)))

(cond
 ((featurep 'font-lock)
  (or (boundp 'font-lock-variable-name-face)
      (setq font-lock-variable-name-face font-lock-type-face))
  (or (boundp 'font-lock-reference-face)
      (setq font-lock-reference-face font-lock-function-name-face))
  (if (boundp 'font-lock-defaults)
      (progn
	(defvar namazu-font-lock-keywords
	  (list
	   (list namazu-output-title-pattern
		 '(1 font-lock-comment-face)
		 '(2 font-lock-keyword-face)
		 '(3 font-lock-reference-face))
	   (list namazu-output-header-pattern
		 1 'font-lock-variable-name-face)
	   (list namazu-output-url-pattern
		 '(1 (progn
		       (set-text-properties (match-beginning 1) (match-end 1)
					    '(mouse-face highlight))
		       font-lock-function-name-face))
		 '(3 font-lock-type-face))
	   (list namazu-output-current-list-pattern
		 0 'font-lock-comment-face)
	   (list namazu-output-pages-pattern 0 'font-lock-comment-face)))
	(add-hook
	 'namazu-display-hook
	 (lambda ()
	   (make-local-variable 'font-lock-defaults)
	   (setq font-lock-defaults
		 '((namazu-font-lock-keywords) t))
	   (font-lock-mode 1))))
    (defvar namazu-font-lock-keywords
      (list
       (list namazu-output-title-pattern 1 'font-lock-comment-face)
       (list namazu-output-title-pattern 2 'font-lock-keyword-face)
       (list namazu-output-title-pattern 3 'font-lock-reference-face)
       (list namazu-output-header-pattern 1 'font-lock-variable-name-face)
       (list namazu-output-url-pattern 1 'font-lock-function-name-face)
       (list namazu-output-url-pattern 3 'font-lock-type-face)
       (list namazu-output-current-list-pattern  0 'font-lock-comment-face)
       (list namazu-output-pages-pattern 0 'font-lock-comment-face))
      "Namazu での検索結果にお化粧をするための設定です. ")
    (add-hook 'namazu-display-hook
	      (lambda ()
		(setq font-lock-keywords namazu-font-lock-keywords)
		(font-lock-mode 1)))))
 ((featurep 'hilit19)
  (if (and (boundp 'hilit-background-mode)
	   (eq hilit-background-mode 'dark))
      (hilit-set-mode-patterns
       'namazu-mode
       (list
	(list namazu-output-title-pattern  1 'red-bold-underline)
	(list namazu-output-title-pattern  2 'yellow-bold)
	(list namazu-output-title-pattern  3 'grey80)
	(list namazu-output-header-pattern 1 'palegreen)
	(list namazu-output-url-pattern    1 'gold-underline)
	(list namazu-output-url-pattern    3 'grey80)))
    (hilit-set-mode-patterns
     'namazu-mode
     (list
      (list namazu-output-title-pattern  1 'red-bold-underline)
      (list namazu-output-title-pattern  2 'purple)
      (list namazu-output-title-pattern  3 'grey40)
      (list namazu-output-header-pattern 1 'DarkGoldenrod)
      (list namazu-output-url-pattern    1 'blue-bold-underline)
      (list namazu-output-url-pattern    3 'grey40))))
  (add-hook 'namazu-display-hook
	    'hilit-rehighlight-buffer-quietly)))

;; Message highlight functions. 
;; e.g. 
;; (setq namazu-msg-highlight-function 'namazu-msg-highlight-mew)

;;
;; for Mew freak.
(defun namazu-msg-highlight-mew ()
  "namazu message highlight use Mew functions (1.94 or later)."
  (save-excursion
    (condition-case err
	(progn
	  (if (not (and (boundp 'mew-version)
			mew-version))
	      (save-excursion
		(require 'mew)
		(mew-init)
		(if (get-buffer mew-buffer-hello)
		    (kill-buffer mew-buffer-hello))))
	  (goto-char (point-min))
	  (if (and (fboundp 'mew-highlight-header-region)
		   (re-search-forward "^$" nil t))
	      (progn
		(mew-highlight-header-region (point-min) (point))
		(put-text-property (point) (1+ (point)) 'read-only t))) ;; header-end
	  (cond
	   ((fboundp 'mew-cite-color)
	    (mew-cite-color))
	   ((fboundp 'mew-highlight-body)
	    (mew-highlight-body)))
	  (and (fboundp 'mew-highlight-url)
	       (mew-highlight-url)))
      (error nil))))

;; end here.
