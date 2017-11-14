;;; tex-jp.el --- Support for Japanese TeX.  -*- coding: iso-2022-jp-unix; -*-

;; Copyright (C) 1999, 2001-2008, 2012-2013, 2016-2017
;;   Free Software Foundation, Inc.

;; Author:     KOBAYASHI Shinji <koba@flab.fujitsu.co.jp>,
;;             Hidenobu Nabetani <nabe@debian.or.jp>
;; Maintainer: Masayuki Ataka <masayuki.ataka@gmail.com>
;;             Ikumi Keita <ikumikeita@jcom.home.ne.jp>
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file was written by KOBAYASHI Shinji <koba@flab.fujitsu.co.jp>
;; based on many patches developed by Japanese NetNews community.
;; Japanese message translation by MATUI Takao <mat@nuis.ac.jp>.

;;; Code:

(require 'latex)
(require 'tex-buf)

;;; Customization

(defgroup AUCTeX-jp nil
  "Japanese support in AUCTeX."
  :group 'AUCTeX)

(defcustom japanese-TeX-engine-default 'ptex
  "Default TeX engine for Japanese TeX."
  :group 'AUCTeX-jp
  :type '(choice (const :tag "pTeX" ptex)
		 (const :tag "jTeX" jtex)
		 (const :tag "upTeX" uptex)))

(defcustom japanese-TeX-use-kanji-opt-flag (not (eq system-type 'windows-nt))
  "Add kanji option to Japanese pTeX family if non-nil.
If `TeX-japanese-process-input-coding-system' or
`TeX-japanese-process-output-coding-system' are non-nil, the process coding
systems are determined by their values regardless of the kanji option."
  :group 'AUCTeX-jp
  :type 'boolean)

(setq TeX-engine-alist-builtin
      (append TeX-engine-alist-builtin
             '((ptex "pTeX" "ptex %(kanjiopt)" "platex %(kanjiopt)" "eptex")
               (jtex "jTeX" "jtex" "jlatex" nil)
               (uptex "upTeX" "euptex" "uplatex" "euptex"))))

;; 順調に行けば不要になる。
(defcustom japanese-TeX-command-list
  ;; Changed to double quotes for Windows afflicted people.  I don't
  ;; use the %(latex) and %(tex) shorthands here because I have not
  ;; clue whether Omega-related versions exist.  --dak
  '(("jTeX" "%(PDF)jtex %`%S%(PDFout)%(mode)%' %t"
     TeX-run-TeX nil (plain-tex-mode) :help "Run NTT jTeX")
    ("jLaTeX" "%(PDF)jlatex %`%S%(PDFout)%(mode)%' %t"
     TeX-run-TeX nil (latex-mode) :help "Run NTT jLaTeX")
    ("pTeX" "%(PDF)ptex %(kanjiopt)%`%S%(PDFout)%(mode)%' %t"
     TeX-run-TeX nil (plain-tex-mode) :help "Run ASCII pTeX")
    ("pLaTeX" "%(PDF)platex %(kanjiopt)%`%S%(PDFout)%(mode)%' %t"
     TeX-run-TeX nil (latex-mode) :help "Run ASCII pLaTeX")
    ("Mendex" "mendex %(mendexkopt)%s" TeX-run-command nil t :help "Create index file with mendex")
    ("jBibTeX" "jbibtex %s" TeX-run-BibTeX nil t :help "Run jBibTeX")
    ("pBibTeX" "pbibtex %(kanjiopt)%s" TeX-run-BibTeX nil t :help "Run pBibTeX"))
  "Additional list of commands, especially for Japanese.
For detail, see `TeX-command-list', to which this list is appended."
  :group 'AUCTeX-jp
  :type '(repeat (group :value ("" "" TeX-run-command nil t)
			(string :tag "Name")
			(string :tag "Command")
			(choice :tag "How"
				:value TeX-run-command
				(function-item TeX-run-command)
				(function-item TeX-run-format)
				(function-item TeX-run-TeX)
				(function-item TeX-run-interactive)
				(function-item TeX-run-BibTeX)
				(function-item TeX-run-compile)
				(function-item TeX-run-shell)
				(function-item TeX-run-discard)
				(function-item TeX-run-background)
				(function-item TeX-run-silent)
				(function-item TeX-run-discard-foreground)
				(function-item TeX-run-function)
				(function-item TeX-run-discard-or-function)
				(function :tag "Other"))
			(boolean :tag "Prompt")
			(choice :tag "Modes"
				(const :tag "All" t)
				(set (const :tag "Plain TeX" plain-tex-mode)
				     (const :tag "LaTeX" latex-mode)
				     (const :tag "DocTeX" doctex-mode)
				     (const :tag "ConTeXt" context-mode)
				     (const :tag "Texinfo" texinfo-mode)
				     (const :tag "AmSTeX" ams-tex-mode)))
			(repeat :tag "Menu elements" :inline t sexp))))

;; customize option の初期値や saved value そのものを改変しないように
;; するため、setcar の使用は避ける。
(setq TeX-command-list
      ;; `TeX-command-list' と同じ構造の新しい list を作る。
      ;; 各要素の list を l として、l そのものを使ったり、l を
      ;; 若干修正した list を作ったりして `mapcar' で集める。
      (mapcar
       (lambda (l)
	 (cond
	  ;; l の第1要素が "BibTeX" や "Index" だったら、l の第2要素
	  ;; だけを入れ替えた別の list を作る。
	  ((equal (car l) "BibTeX")
	   (append (list (car l) "%(bibtex) %s") (cddr l)))
	  ((equal (car l) "Index")
	   (append (list (car l) "%(makeindex) %s") (cddr l)))
	  ;; それ以外の場合は l そのものを使う。
	  (t
	   l)))
       TeX-command-list))

;; 順調に行けば不要になる。
(setq TeX-command-list
      (append japanese-TeX-command-list
	      '(("-" "" ignore nil t)) ;; separator for command menu
	      TeX-command-list))

;; Define before first use.
(defvar japanese-TeX-mode nil
  "Non-nil means the current buffer handles Japanese TeX/LaTeX.")
(make-variable-buffer-local 'japanese-TeX-mode)
(put 'japanese-TeX-mode 'permanent-local t)

(setq TeX-expand-list-builtin
      (append
       TeX-expand-list-builtin
       '(
        ;; -kanji オプションの文字列を作る。
        ("%(kanjiopt)" (lambda ()
                         (if (and
                              ;; non-mule な emacsen はそもそも日本語
                              ;; 文書を typeset することは考えなくても
                              ;; いいだろう、とは思うけど一応…。
                              (featurep 'mule)
                              japanese-TeX-use-kanji-opt-flag)
                             (let ((str (japanese-TeX-get-encoding-string)))
                               (if str (format " -kanji=%s " str) ""))
                           "")))
        ;; pbibtex, jbibtex, upbibtex, bibtex の中から適切なものを選択する。
        ("%(bibtex)" (lambda ()
                       (cond
                        ((eq TeX-engine 'ptex)
                         ;; pLaTeX 用日本語 BibTeX が pbibtex になった
                         ;; のは比較的最近なので、まだ jbibtex の人もそ
                         ;; れなりにいるだろう。
                         (if (executable-find "pbibtex")
                             "pbibtex %(kanjiopt)" "jbibtex"))
                        ((eq TeX-engine 'jtex) "jbibtex")
                        ((eq TeX-engine 'uptex) "upbibtex")
                        (t "bibtex"))))
        ;; mendex, upmendex, makeindex のうち適切なものを選択する。
        ("%(makeindex)" (lambda ()
                          (cond
			   ;; upmendex は XeLaTeX や LuaLaTeX でも
			   ;; 使える。see
			   ;; http://www.t-lab.opal.ne.jp/tex/README_upmendex.md
			   ;; FIXME: XeLaTeX や LuaLaTeX だけを使う
			   ;; 利用者の場合は、tex-jp は load されな
			   ;; いのでこの設定は意味がない。
                           ((and (memq TeX-engine '(uptex xetex luatex))
                                 (executable-find "upmendex"))
                            "upmendex %(dic)")
                           ((memq TeX-engine '(ptex uptex))
                            "mendex %(mendexkopt) %(dic)")
                           (t "makeindex"))))
        ;; mendex 用日本語コードオプション。
        ("%(mendexkopt)" (lambda ()
                           (if (and (featurep 'mule)
                                    japanese-TeX-use-kanji-opt-flag)
                               (let ((str (japanese-TeX-get-encoding-string)))
                                 ;; １文字目を大文字に。
                                 (if str (format " -%c " (upcase (aref str 0)))
                                   ""))
                             "")))
	;; (up)mendex 用辞書指定オプション。
	("%(dic)" (lambda ()
		    ;; master と同名で拡張子が .dic のファイルがあれば
		    ;; それを辞書名として -d オプションに与える。
		    ;; C-c C-r 等の場合 _region_.dic にすべきでは
		    ;; ないので、`TeX-master-file' を陽に呼ぶ。
		    (let ((dicname (TeX-master-file "dic" t)))
		      (if (file-exists-p
			   (expand-file-name dicname (TeX-master-directory)))
			  (let ((result (format "-d %s" dicname)))
			    ;; Advance past the file name in order to
			    ;; prevent expanding any substring of it.
			    (setq pos (+ pos (length result)))
			    result)
			""))))
        ;; pxdvi と %(o?)xdvi の適切な方を選択する。
        ("%(xdvi)" (lambda ()
                     ;; pxdvi は ptex, jtex 共用なので、
                     ;; japanese mode かどうかで判定すれば OK。
                     (if (and japanese-TeX-mode (executable-find "pxdvi"))
                         "pxdvi" "%(o?)xdvi"))))))

;;; Viewing (new implementation)

(setq TeX-view-predicate-list-builtin
      (append
       '((paper-a4
	  (let ((regex "\\`\\(?:a4j\\|a4paper\\|a4dutch\\|a4wide\\|sem-a4\\)\\'"))
	    (or (TeX-match-style regex)
		(and (fboundp 'LaTeX-match-class-option)
		     (LaTeX-match-class-option regex)))))
         (paper-a5
	  (let ((regex "\\`\\(?:a5j\\|a5paper\\|a5comb\\)\\'"))
	    (or (TeX-match-style regex)
		(and (fboundp 'LaTeX-match-class-option)
		     (LaTeX-match-class-option regex)))))
         ;; jarticle などだと b4paper, b5paper は JIS B 系列。
         ;; j-article などの方には a4j, b5j といったオプションはない。
         (paper-b5    ; ISO B5
          (and (fboundp 'LaTeX-match-class-option)
	       (LaTeX-match-class-option "\\`b5paper\\'")
               (not (TeX-match-style "\\`u?[jt]s?\\(?:article\\|report\\|book\\)\\'"))))
         (paper-b5jis ; JIS B5
	  (and (fboundp 'LaTeX-match-class-option)
	       (or (LaTeX-match-class-option "\\`b5j\\'")
		   (and (LaTeX-match-class-option "\\`b5paper\\'")
			(TeX-match-style "\\`u?[jt]s?\\(?:article\\|report\\|book\\)\\'")))))
         ;; article などには b4paper というオプションはない。
         ;; b4paper というオプションがあったら JIS B4 と見なす。
         (paper-b4jis
	  (and (fboundp 'LaTeX-match-class-option)
	       (LaTeX-match-class-option "\\`\\(?:b4j\\|b4paper\\)\\'"))))
       ;; jsclasses だと他にももっと判型のオプションがあるが、全部面倒
       ;; 見てるとキリがないので、これくらいでいいだろう。
       ;; jsarticle.el や jsbook.el で追加分の処理を仕込めばいいのかも知れない。
       TeX-view-predicate-list-builtin))

(unless (memq system-type '(windows-nt darwin))
  (let ((l (assoc "xdvi" TeX-view-program-list-builtin)))
    (when l
      (setcar (cadr l) "%(xdvi) -unique")
      (setcdr (cdr l) '("%(xdvi)"))))
  (setq TeX-view-program-list-builtin
	(append TeX-view-program-list-builtin
		'(("MuPDF" "mupdf %o" "mupdf")))))

;; これは tex.el に取り入れてもらうのは難しいか？
;; tex-jp.el が読み込まれるだけで、dvi viewer のデフォルトが dviout に
;; なってしまうのは抵抗が大きいかも。
(unless (get 'TeX-view-program-selection 'saved-value)
  (if (eq system-type 'windows-nt)
      (setq TeX-view-program-selection
	    (append
	     '((output-dvi "dviout"))
	     TeX-view-program-selection))))

(mapc (lambda (dir) (add-to-list 'TeX-macro-global dir t))
      (or (TeX-tree-expand
	   '("$SYSTEXMF" "$TEXMFLOCAL" "$TEXMFMAIN" "$TEXMFDIST")
	   "platex" '("/ptex/" "/pbibtex/bst/"))
	  '("/usr/share/texmf/ptex/" "/usr/share/texmf/pbibtex/bst/")))

(mapc (lambda (dir) (add-to-list 'TeX-macro-global dir t))
      (or (TeX-tree-expand
	   '("$SYSTEXMF" "$TEXMFLOCAL" "$TEXMFMAIN" "$TEXMFDIST")
	   "jlatex" '("/jtex/" "/jbibtex/bst/"))
	  '("/usr/share/texmf/jtex/" "/usr/share/texmf/jbibtex/bst/")))

(defcustom japanese-TeX-error-messages t
  "*If non-nil, explain TeX error messages in Japanese."
  :group 'AUCTeX-jp
  :type 'boolean)

(defcustom TeX-japanese-process-input-coding-system nil
  "If non-nil, used for encoding input to Japanese TeX process.
When nil, AUCTeX tries to choose suitable coding system.
See also a user custom option `TeX-japanese-process-output-coding-system'."
  :group 'AUCTeX-jp
  :type '(choice (const :tag "Default" nil) coding-system))

(defcustom TeX-japanese-process-output-coding-system nil
  "If non-nil, used for decoding output from Japanese TeX process.
When nil, AUCTeX tries to choose suitable coding system.
See also a user custom option `TeX-japanese-process-input-coding-system'."
  :group 'AUCTeX-jp
  :type '(choice (const :tag "Default" nil) coding-system))

;; 順調に行けば不要になる。
(defcustom japanese-TeX-command-default "pTeX"
  "*The default command for `TeX-command' in the japanese-TeX mode."
  :group 'AUCTeX-jp
  :type 'string)
  (make-variable-buffer-local 'japanese-TeX-command-default)

;; 順調に行けば不要になる。
(defcustom japanese-LaTeX-command-default "LaTeX"
  "*The default command for `TeX-command' in the japanese-LaTeX mode."
  :group 'AUCTeX-jp
  :type 'string)
  (make-variable-buffer-local 'japanese-LaTeX-command-default)

(defcustom japanese-LaTeX-default-style "jarticle"
  "*Default when creating new Japanese documents."
  :group 'AUCTeX-jp
  :type 'string)

(defcustom japanese-LaTeX-style-list
  '(("j-article")
    ("j-report")
    ("j-book")
    ("jslides")
    ("jarticle")
    ("jreport")
    ("jbook")
    ("tarticle")
    ("treport")
    ("tbook")
    ("jsarticle")
    ("jsbook")
    ;; for upLaTeX
    ("ujarticle") ("ujreport") ("ujbook")
    ("utarticle") ("utreport") ("utbook"))
  "*List of Japanese document classes."
  :group 'AUCTeX-jp
  :type '(repeat (group (string :format "%v"))))

(setq LaTeX-style-list
      (append japanese-LaTeX-style-list LaTeX-style-list))

;; text〜系の明朝体・ゴシック体指定コマンドは jLaTeX にはないようで、
;; (u)pLaTeX でしか使えないが、問題になることはないだろう。
(setq LaTeX-font-list
      (append '((?m "\\textmc{" "}" "\\mathmc{" "}")
                (?g "\\textgt{" "}" "\\mathgt{" "}"))
	      LaTeX-font-list))

;;; Coding system

(defun japanese-TeX-set-process-coding-system (process)
  "Set proper coding system for japanese TeX PROCESS."
  (with-current-buffer TeX-command-buffer
    (when japanese-TeX-mode
      ;; TeX-engine が ptex, jtex, uptex のいずれかである場合のみ考え
      ;; る。luatex-ja などの場合はそもそもただの latex-mode でよく、
      ;; わざわざ japanese-latex-mode にする必要がない。

      ;; FIXME: 以下の処理は tex engine を対象とする場合しか考えていない。
      ;; bibtex や mendex 等の補助ツールの場合は正しくない処理かもしれない。
      (let*
	  ;; -kanji オプションありの時の文字コード。
	  ((kanji (and japanese-TeX-use-kanji-opt-flag
		       (let ((str (japanese-TeX-get-encoding-string)))
			 (cond
			  ((equal str "euc") 'euc-jp)
			  ((equal str "jis") 'iso-2022-jp)
			  ((equal str "sjis") 'shift_jis)
			  ((equal str "utf8") 'utf-8)))))

	   ;; process からの出力の文字コード。
	   (dec (cond
		 ;; windows と mac の場合。
		 ((memq system-type '(windows-nt darwin))
		  (cond
		   ;; ptex なら mac は utf-8。
		   ;; windows で -kanji オプションありの時はその文字コード、
		   ;; なしの時は sjis。
		   ((eq TeX-engine 'ptex)
		    (cond ((eq system-type 'darwin)
			   'utf-8)
			  ((and japanese-TeX-use-kanji-opt-flag kanji)
			   kanji)
			  (t 'shift_jis)))
		   ;; jtex なら sjis に固定する。
		   ((eq TeX-engine 'jtex)
		    'shift_jis)
		   ;; uptex なら utf-8 に固定する。
		   (t
		    'utf-8)))
		 ;; unix の場合。
		 (t
		  ;; jtex なら euc に固定する。
		  (cond
		   ((eq TeX-engine 'jtex)
		    'euc-jp)
		   ;; それ以外は、uptex でも locale に従う。
		   ;; ただし、locale が日本語をサポートしない場合は
		   ;; euc に固定する。
		   (t
		    (let ((lcs
			   (cond
			    ((boundp 'locale-coding-system)
			     locale-coding-system)
			    ;; XEmacs doesn't have `locale-coding-system'.
			    ;; Instead xemacs 21.5 has
			    ;; `get-coding-system-from-locale' and
			    ;; `current-locale'.  They aren't available on
			    ;; xemacs 21.4.
			    ((and
			      (featurep 'xemacs)
			      (fboundp 'get-coding-system-from-locale))
			     (get-coding-system-from-locale
			      (if (fboundp 'current-locale)
				  (current-locale)
				;; I don't know XEmacs well, so incorporate
				;; the suggestion of
				;; http://lists.gnu.org/archive/html/auctex-devel/2017-02/msg00079.html
				;; as well.
				(or (getenv "LC_ALL")
				    (getenv "LC_CTYPE")
				    (getenv "LANG")
				    "")))))))
		      (if (and lcs (japanese-TeX-coding-ejsu lcs))
			  lcs 'euc-jp)))))))

	   ;; process に与える入力の文字コード。
	   (enc (cond
		 ;; ptex で -kanji オプションありなら、その文字コード。
		 ;; なしなら utf-8 か sjis。
		 ((eq TeX-engine 'ptex)
		  (if (and japanese-TeX-use-kanji-opt-flag kanji)
		      kanji
		    (if (eq system-type 'windows-nt)
			'shift_jis 'utf-8)))
		 ;; jtex なら euc か sjis に固定する。
		 ((eq TeX-engine 'jtex)
		  (if (memq system-type '(windows-nt darwin))
		      'shift_jis 'euc-jp))
		 ;; uptex なら utf-8 に固定する。
		 (t
		  'utf-8))))

	;; 改行コードを指定。
	(setq dec (coding-system-change-eol-conversion
		   dec
		   (if (eq system-type 'windows-nt) 'dos 'unix))
	      enc (coding-system-change-eol-conversion
		   enc
		   (if (eq system-type 'windows-nt) 'dos 'unix)))

	;; Customize 値があればそれを優先。
	(set-process-coding-system
	 process
	 (or TeX-japanese-process-output-coding-system dec)
	 (or TeX-japanese-process-input-coding-system enc))))))

(defun japanese-TeX-coding-ejsu (coding-system)
  "Convert japanese CODING-SYSTEM to mnemonic string.
euc-jp:    \"euc\"
jis:       \"jis\"
shift_jis: \"sjis\"
utf-8:     \"utf8\"
Return nil otherwise."
  (let ((base (coding-system-base coding-system)))
    (if (featurep 'xemacs)
	(setq base (coding-system-name base)))
    (cdr (assq base
              '((japanese-iso-8bit . "euc")
                (euc-jp . "euc") ; for xemacs
                (iso-2022-jp . "jis")
                (japanese-shift-jis . "sjis")
                (shift_jis . "sjis") ; for xemacs
                (utf-8 . "utf8")
                (mule-utf-8 . "utf8") ; for emacs 21, 22
                ;; utf-8-auto や utf-8-emacs を入れる必要はあるのか？

                ;; xemacs 21.5 with mule には、jisx0213 の charset は
                ;; あるがそれ用の coding system はない。
                (euc-jis-2004 . "euc")
                (iso-2022-jp-2004 . "jis")
                (japanese-shift-jis-2004 . "sjis")

                (japanese-cp932 . "sjis")
                (eucjp-ms . "euc")
                (windows-932 . "sjis") ; for xemacs 21.5 with mule
		)))))

(defun japanese-TeX-get-encoding-string ()
  "Return coding option string for Japanese pTeX family.
For inappropriate encoding, nil instead."
  (or (japanese-TeX-coding-ejsu buffer-file-coding-system)

      ;; 複数ファイルに分割した文書の場合、emacs で開いたファイルが日本
      ;; 語を１字も含まないことがある。このため、そのファイルの
      ;; buffer-file-coding-system は日本語コードが不定に留まって
      ;; しまう可能性がある。そのような場合、master file の
      ;; buffer-file-coding-system を使う。
      (if (stringp TeX-master) ; 自分が子ファイルのとき
         (let ((buf (get-file-buffer (TeX-master-file t))))
           (if buf
               (japanese-TeX-coding-ejsu
                (with-current-buffer buf buffer-file-coding-system)))))

      ;; それでも決められない場合は buffer-file-coding-system の
      ;; default 値を使う。
      (japanese-TeX-coding-ejsu
       (default-value 'buffer-file-coding-system))))

;;; Japanese TeX modes

;;;###autoload
(defun japanese-plain-tex-mode ()
  "Major mode in AUCTeX for editing Japanese plain TeX files.
Set `japanese-TeX-mode' to t, and enter `TeX-plain-tex-mode'."
  (interactive)
  (setq japanese-TeX-mode t)
  (TeX-plain-tex-mode))

(defun japanese-plain-tex-mode-initialization ()
  "Japanese plain-TeX specific initializations."
  (when japanese-TeX-mode
;    (setq TeX-command-default japanese-TeX-command-default)
    (TeX-engine-set japanese-TeX-engine-default)

    ;; For the intent of the following lines, see the comments below
    ;; in `japanese-latex-mode-initialization'.
    (when enable-local-variables
      (setq major-mode 'japanese-plain-tex-mode)
      (add-hook 'hack-local-variables-hook 'japanese-TeX-reset-mode-name
		nil t))))

(add-hook 'plain-TeX-mode-hook 'japanese-plain-tex-mode-initialization)

;;;###autoload
(defun japanese-latex-mode ()
  "Major mode in AUCTeX for editing Japanese LaTeX files.
Set `japanese-TeX-mode' to t, and enter `TeX-latex-mode'."
  (interactive)
  (setq japanese-TeX-mode t)
  (TeX-latex-mode))

(defun japanese-latex-mode-initialization ()
  "Japanese LaTeX specific initializations."
  (when japanese-TeX-mode
;    (setq TeX-command-default japanese-LaTeX-command-default)
    (TeX-engine-set
     (cond
      ((TeX-match-style "\\`u[jt]\\(article\\|report\\|book\\)\\'")
       'uptex)
      ((TeX-match-style "\\`[jt]s?\\(article\\|report\\|book\\)\\'")
       (if (LaTeX-match-class-option "\\`uplatex\\'")
	   'uptex 'ptex))
      ((TeX-match-style "\\`j-\\(article\\|report\\|book\\)\\'")
       'jtex)
      (t japanese-TeX-engine-default)))
    (setq LaTeX-default-style japanese-LaTeX-default-style)
;    (setq TeX-command-BibTeX
;        (if (and (eq TeX-engine 'ptex) (executable-find "pbibtex"))
;            "pBibTeX" "jBibTeX"))

    (when (and (fboundp 'font-latex-add-keywords)
	       (eq TeX-install-font-lock 'font-latex-setup))
      ;; jLaTeX にはないコマンドだが、それはもう気にしなくていいだろう。
      (font-latex-add-keywords '(("textgt" "{") ("mathgt" "{"))
			       'bold-command)
      (font-latex-add-keywords '("gtfamily")
			       'bold-declaration))

    ;; The value of `major-mode' should be `latex-mode', not
    ;; `japanese-latex-mode', because the name `latex-mode' is hard
    ;; coded in several places of AUCTeX like "(eq major-mode
    ;; 'latex-mode)", "(memq major-mode '(doctex-mode latex-mode)" and
    ;; so on.  By such piece of codes, `japanese-latex-mode' should
    ;; simply be regarded as `latex-mode'.  So we'd like to leave
    ;; `major-mode' as `latex-mode' here, but doing so confuses
    ;; `hack-local-variables' in two ways.
    ;; (1) It is tricked into considering that the major mode is not
    ;;     yet initialized and calls `japanese-latex-mode' again.
    ;; (2) It does not read the directory local variables prepared for
    ;;     `japanese-latex-mode'.
    ;; Thus we temporarily set `major-mode' to `japanese-latex-mode'
    ;; here and plan to reset it to `latex-mode' after
    ;; `hack-local-variables' is done.
    (when enable-local-variables
      (setq major-mode 'japanese-latex-mode)
      (add-hook 'hack-local-variables-hook 'japanese-TeX-reset-mode-name
		nil t))))

(add-hook 'LaTeX-mode-hook 'japanese-latex-mode-initialization)

;; This function is useful only within `hack-local-variables-hook'.
(defun japanese-TeX-reset-mode-name ()
  (cond ((eq major-mode 'japanese-latex-mode)
	 (setq major-mode 'latex-mode))
	((eq major-mode 'japanese-plain-tex-mode)
	 (setq major-mode 'plain-tex-mode)))
  (remove-hook 'hack-local-variables-hook 'japanese-TeX-reset-mode-name t))

;; Make `hack-dir-local-variables' to regard `latex-mode' as parent
;; of `japanese-latex-mode', and `plain-tex-mode' as parent of
;; `japanese-plain-tex-mode'.
(put 'japanese-plain-tex-mode 'derived-mode-parent 'plain-tex-mode)
(put 'japanese-latex-mode 'derived-mode-parent 'latex-mode)

;;; Support for various self-insert-command

(fset 'japanese-TeX-self-insert-command
      (cond ((fboundp 'can-n-egg-self-insert-command)
	     #'can-n-egg-self-insert-command)
	    ((fboundp 'egg-self-insert-command)
	     #'egg-self-insert-command)
	    ((fboundp 'canna-self-insert-command)
	     #'canna-self-insert-command)
	    (t
	     #'self-insert-command)))

(defun TeX-insert-punctuation ()
  "Insert point or comma, cleaning up preceding space."
  (interactive)
  (expand-abbrev)
  (if (TeX-looking-at-backward "\\\\/\\(}+\\)" 50)
      (replace-match "\\1" t))
  (call-interactively 'japanese-TeX-self-insert-command))

;;; Error Messages

(if japanese-TeX-error-messages
(setq TeX-error-description-list
  '(("\\(?:Package Preview Error\\|Preview\\):.*" .
"`preview'へ`auctex'オプションを直接与えるのは避けてください．
プレビューの実行時以外でこのエラーが出た場合，余りにこみいったことを
しすぎか，でなければAUCTeXがひどい失敗をしています．")

    ("Bad \\\\line or \\\\vector argument.*" .
"線の傾きを指定する，\\lineまたは\\vectorの最初の引数が不正です．")

    ("Bad math environment delimiter.*" .
"数式モード中で数式モード開始コマンド\\[または\\(，または，数式モード外で
数式モード終了コマンド\\]または\\)をTeXが見つけました．この問題は，数式モー
ドのデリミタがマッチしていなかったり，括弧のバランスがとれていなかったりす
るために生じます．")

    ("Bad use of \\\\\\\\.*" .
"\\\\コマンドがパラグラフ中にありました．この使いかたは無意味です．
このエラーメッセージは\\\\がcentering環境やflushing環境で使われた
時，あるいはcentering/flushing宣言が有効なところで使われた時に生じます．")

    ("\\\\begin{[^ ]*} ended by \\\\end{[^ ]*}." .
"対応する\\begin命令のない\\end命令をLaTeXが見つけました．\\end命令の環
境名を間違えたか，余分な\\begin命令があるか，\\end命令をわすれたかのいず
れかでしょう．")

    ("Can be used only in preamble." .
"プリアンブルでしか使えない\\documentclass・\\nofiles・\\includeonly
\\makeindex・\\makeglossaryのうちのいずれかが\\begin{document}よりも
後で使われているのをLaTeXが検出しました．このエラーは\\begin{document}
が余分にあった時にも生じます．")

    ("Command name [^ ]* already used.*" .
"すでに定義されている命令名または環境名に対して\\newcommand・
\\newenvironment・\\newlength・\\newsavebox・\\newtheoremのうちのいず
れかを実行しようとしています(ある環境を定義すると同じ名前の命令が自動
的に定義されるので，既に存在する環境と同名の命令は定義できません)．新
しい名前を考えるか，\\newcommandか\\newenvironmentの場合なら対応する
\\renew...命令を使わなければなりません．")

    ("Counter too large." .
"1. 文字で順序付けされたもの，たぶん番号付けされたリスト環境のラベルが，
26よりも大きい番号を受け取りました．非常に長いリストを使っているか，
カウンタを再設定してしまったかのいずれかでしょう．

2. 脚注が文字または脚注記号で順序づけされていますが，文字または記号を
使い切ってしまいました．おそらく\\thanks命令の使いすぎです．")


    ("Environment [^ ]* undefined." .
"定義されていない環境に対する\\begin命令をLaTeXが見つけました．おそらく
環境名を間違えたのでしょう．")

    ("Float(s) lost." .
"parboxのなかにfigure環境・table環境または\\marginpar命令がありました
\(なお，parboxはminipage環境か\\parbox命令によって作られるか，脚注や図
などに対してLaTeXが生成するものです\)．これは出力時のエラーなので，原因
となっている環境あるいは命令は，LaTeXが問題を発見した場所よりもだいぶ
ん前にある可能性があります．出力されていない図・表・傍注などがいくつか
あるかもしれませんが，それらが原因であるとは限りません．")

    ("Illegal character in array arg." .
"array環境またはtabular環境の引数，または\\multicolumn命令の第2引数
の中に不正な文字がありました．")

    ("Missing \\\\begin{document}." .
"\\begin{document}命令より前にLaTeXが出力を行なってしまいました．
\\begin{document}命令を忘れたか，プリアンブルに何か間違いがあるのでしょう．
打ち間違いによる文字や，宣言の誤りによる可能性もあります．例えば，引数を
囲む括弧を抜かしたとか，命令名の\\を忘れた場合などです．")

    ("Missing p-arg in array arg.*" .
"array環境・tabular環境の引数，あるいは\\multicolumn命令の第2引数の中に，
括弧に囲まれた表現のついていないpがありました．")

    ("Missing @-exp in array arg." .
"array環境・tabular環境の引数，あるいは\\multicolumn命令の第2引数の中に，
@表現のついていない@がありました．")

    ("No such counter." .
"\\setcounter命令または\\addtocounter命令で，存在しないカウンタが指定され
ました．おそらくただのタイプミスでしょう．ただし，エラーがauxファイルの中
で生じた場合は，\\newcounter命令をプリアンブルの外で使ったのだと思われます．")

    ("Not in outer par mode." .
"figure環境・table環境あるいは\\marginpar命令が数式モードまたはparboxの中
で使われました．")

    ("\\\\pushtabs and \\\\poptabs don't match." .
"\\pushtabsと対応しない\\poptabsがみつかったか，または，対応する\\poptabs
をもたない\\pushtabsがあるのに\\end{tabbing}が現れてしまいました．")

    ("Something's wrong--perhaps a missing \\\\item." .
"リスト環境の中に\\item命令がないのが最もありそうなケースです．
thebibliography環境で引数を忘れた場合にも生じます．")

    ("Tab overflow." .
"\\=が，LaTeXで許されるタブストップの最大数を超えています．")

    ("There's no line here to end." .
"\\newline命令または\\\\命令がパラグラフ間にあります．この使いかたは
無意味です．もし空行をあけたいのでしたら，\\vspaceを使ってください．")

    ("This may be a LaTeX bug." .
"まったくわけがわからなくなってしまいました．たぶんこれ以前に検出された
エラーのせいだと思われます．しかし，LaTeX自体のバグである可能性もあります．
もしこのエラーが入力ファイルに対する最初のエラーであり，何も間違いが見つ
からない場合は，そのファイルを保存して，ローカルガイドに書かれている責任
者に連絡してください．")

    ("Too deeply nested." .
"リスト環境の入れ子が深すぎます．何段階の入れ子が許されるかは使っている
コンピュータに依存しますが，少なくとも4段階までは許されています(普通は
それで十分でしょう)．")

    ("Too many unprocessed floats." .
"このエラーは1ページ中の\\marginpar命令が多すぎるために生じる場合もあ
りますが，もっとありそうなのは，限界を超えて図や表を保存しようとした場
合です．長い文書を組版していくとき，LaTeXは図や表を個々に保存し，ペー
ジの分割を行なう時にそれらを挿入します．このエラーは，ページへの分割が
行なわれる前に，あまりにも多くのfigure環境やtable環境が見つかった場合
に生じます．この問題は環境のうちのいくつかを文書の終わりの方に移動すれ
ば解決できます．また，このエラーは``logjam''によって生じることもありま
す．``logjam''とは，LaTeXが出現順序通りにしか図表を出力できないせいで，
図表の出力が1ヶ所でもつまるとその後ろの図表が軒並みすべてつっかえてしま
うことをいいます．このジャムの原因は，大きすぎて1ページないしはオプショ
ン引数で指定された位置に収まらないような図や表である可能性があります．こ
れは，引数にpオプションが指定されていないと起きやすくなります．")

    ("Undefined tab position." .
"\\>・\\+・\\-または\\<命令で，存在しないタブ位置，すなわち\\=命令で定
義されていないタブ位置を指定しようとしています．")

    ("\\\\< in mid line." .
"\\<命令がtabbing環境の行の途中に現れました．この命令は行の先頭になければ
なりません．")

    ("Double subscript." .
"数式中の1つの列に2つの下付き文字がついています．例えばx_{2}_{3}のように．
このような表現は無意味です．")

    ("Double superscript." .
"数式中の1つの列に2つの上付き文字がついています．例えばx^{2}^{3}のように．
このような表現は無意味です．")

    ("Extra alignment tab has been changed to \\\\cr." .
"array環境またはtabular環境の1列中にある項目が多すぎます．言い換えると，
列の終わりまでにある&の数が多すぎます．おそらく前の列の最後に\\\\をつけ
るのを忘れたのでしょう．")

    ("Extra \\}, or forgotten \\$." .
"括弧または数式モードのデリミタが正しく対応していません．おそらく{・\\[・
\\(あるいは$のうちのいずれかを書き忘れたのでしょう．")

    ("Font [^ ]* not loaded: Not enough room left." .
"この文書は限界よりも多くのフォントを使っています．もし文書の部分ごとに
別々のフォントが使われているのなら，分割して処理すれば問題は解決されます．")

    ("I can't find file `.*'." .
"必要なファイルが見つかりませんでした．もし見つからないファイルの拡張子
がtexの場合，あなたが指定したファイル，すなわちメインファイルまたは
\\input命令・\\include命令で挿入されるファイルが見つからないのです．
拡張子がstyであれば，存在しない文書スタイルまたはスタイルオプションを
指定しようとしています．")

    ("Illegal parameter number in definition of .*" .
"これはおそらく，\\newcommand・\\renewcommand・\\newenvironmentまたは
\\renewenvironment命令のなかで#が正しく使われなかったために生じたエラー
です．\\#命令として使われる場合を除けば，#という文字は，例えば2番目の
引数を指定する#2のように，引数パラメータとしてしか使えません．また，
このエラーは，上にあげた4つのコマンドがお互いに入れ子になっている場合
や，\\newenvironment命令・\\renewenvironment命令で#2のようなパラメータ
が最後の引数の中で使われている場合にも生じます．")

    ("Illegal unit of measure ([^ ]* inserted)." .
"もし
      ! Missing number, treated as zero.
というエラーが起きた直後であれば，このエラーの原因もそれと同じです．
そうでない場合は，LaTeXが引数としてlengthを期待しているのにnumberが
現れたことを意味しています．このエラーの最もありがちな原因は長さ0を
表わす0inのような表現の代わりに0とかいてしまうことにあります．ただし，
命令の引数を書き忘れた場合にもこのエラーが生じることがあります．")

    ("Misplaced alignment tab character \\&." .
"arrayまたはtabular環境での項目区切りにのみ使われるべき文字&が普通の文
の中にありました．たぶん\\&と入力したかったのでしょう．")

    ("Missing control sequence inserted." .
"このエラーは，おそらく命令名でないものを\\newcommand・\\renewcommand・
\\newlengthまたは\\newsaveboxの第1引数として使ったために生じたのでしょう．")

    ("Missing number, treated as zero." .
"このエラーはたいてい，引数としてnumberまたはlengthを必要としている命令に
対して引数が与えられなかったために生じます．引数を書き忘れたのか，テキスト
の中の大括弧([])がオプション引数の指定と間違えられてしまったかのどちらかで
しょう．また，数を生成する\\valueのような命令やlength命令の前に\\protectを
置いた場合にもこのエラーは生じます．")

    ("Missing [{}] inserted." .
"TeXは既にわけがわからなくなっています．エラーメッセージによって示されて
いる場所はたぶん入力に間違いがあったところよりも後ろになってしまっている
でしょう．")

    ("Missing \\$ inserted." .
"おそらく，数式モード中でしか使えない命令をTeXが数式モード外で検出した
のだと思われます．特に記述されていない限り，LaTeX Book(Lamport著,訳書
はアスキー出版)の3.3節にある添字・分数・数学記号などのコマンドはすべて
数式モードでしか使えないのだということに注意してください．たとえ命令が
数式環境の中にあったとしても，boxを生成する命令の引数を処理しはじめた
時点では，TeXはまだ数式モードに入っていないのです．また，このエラーは，
数式モード中でTeXが空行を検出した場合にも生じます．")

    ("Not a letter." .
"\\hyphenation命令の引数の中になにか正しくないものがあります．")

    ("Paragraph ended before [^ ]* was complete." .
"命令の引数の中に不正な空行が入ってしまっています．おそらく引数の終わり
に閉じ括弧をつけるのを忘れたのでしょう．")

    ("\\\\[^ ]*font [^ ]* is undefined .*" .
"このエラーはあまり一般的でないフォントが数式モードで使われた時に生じ
ます．例えば，脚注の中の数式で\\sc命令が使われると，footnotesizeの
small capsフォントが呼びだされることになります．この問題は\\load命令を
使えば解決できます．")

    ("Font .* not found." .
"未知のfamily/series/shape/sizeの組み合わせのフォントが指定されました．
このエラーが起きるケースは2つ考えられます．
   1) \\sizeマクロで使えないサイズを選択しようとした．
   2) そうでなければ，管理者のところに行って，フォント選択テーブルが
      腐っていると文句をつけてやりましょう!")

    ("TeX capacity exceeded, sorry .*" .
"TeXがメモリを使いきってしまい，実行を中断しました．しかし，慌てないで
ください．このエラーが生じた原因は，たぶん，TeXにあなたの文書を処理で
きるだけの能力がないからではありません．TeXにメモリを使いきらせた原因
は，おそらく入力したファイルの前の方で生じたエラーです．あなたが本当に
TeXの容量を超えたことをしようとしたのかどうか，そしてその場合どうすれ
ばいいのかを判断する方法を以下に説明します．もし問題が入力ファイル中の
エラーにある場合は，個々のエラーを解決していく方法をとるのがよいでしょ
う．LaTeXが短いファイルでメモリを使いきることはめったにありませんから，
エラーの起きた位置より前に処理したページが数ページしかなければ，まず間
違いなく入力ファイルに問題があるはずです．

エラーメッセージの最後に，TeXが使いきってしまったメモリの種類が示され
ています．それらのうち一般的なものについて，考えられる原因を以下に挙げ
ます．

buffer size
===========
章節・\\caption・\\addcontentslineあるいは\\addtocontents命令の引数と
して与えたテキストが長すぎる場合に生じることがあります．このエラーは
たいてい\\end{document}を処理している時に生じますが，\\tableofcontents・
\\listoffiguresあるいは\\listoftables命令を実行している場合にも起きる
ことがあります．この問題を解決するには，もっと短いテキストをオプション
引数として与えてください．目次や図表一覧を作成しても，見出しが長すぎる
と読みにくくなるはずです．

exception dictionary
====================
TeXが持っている領域以上にハイフネーション情報を与えようとしています．
あまり使わない単語の\\hyphenation命令を取り除いて，代わりに\\-命令を使っ
てください．

hash size
=========
命令名の定義または相互参照ラベルの定義が多すぎます．

input stack size
================
このエラーはおそらく命令定義中の誤りによるものです．例えば，次の命令は
再帰的定義となっており，自分自身を使って\\gnuを定義しています．

	  \\newcommand{\\gnu}{a \\gnu} % これはだめ

この\\gnu命令を見つけるとTeXは\\gnuが何をうみだすのかを決定しようとし
てその末尾をいつまでも追いつづけ，やがて``input stack''を使いきってし
まいます．

main memory size
================
これは，TeXが短いファイルを処理している時に使いきる可能性のあるメモリ
のひとつです．main memoryを使いきるのは次の3つの場合のいずれかです．
\(1\)非常に長く複雑な命令を数多く定義した．(2)indexまたはglossaryを作っ
ているとき，1ページ中にあまりにも多くの\\indexまたは\\glossary命令があ
る．(3)生成のための情報をTeXが保持しきれないような，あまりにも複雑なペー
ジを生成しようとした．最初の2つの問題の解決方法は明らかです．命令定義
の数あるいは\\index・\\glossary命令の数を減らすことです．3番目の問題は
ちょっと厄介です．これは，大きなtabbing・tabular・array・picture環境の
せいで生じることがあります．出力位置が決定されるのを待っている図や表で
TeXのメモリがいっぱいになっているのかもしれません．本当にTeXの容量を超
えてしまったのかどうか調べるためには，エラーの起こった場所の直前に
\\clearpage命令を入れてもう一度コンパイルを実行してみてください．もし
それでもメモリが足りなくなるようなら，なんらかの手段を講じる必要があり
ます．TeXがページを切断するかどうか決定するためには段落全体を処理しな
ければならないということを思いだしてください．段落の途中に\\newpage命
令を入れれば，段落の残りを処理する前に今のページをTeXに出力させること
で余裕ができるかもしれません(\\pagebreak命令ではだめです)．もし図や表
が溜まっていることが問題なのならば，図表をもっと後ろの方に移動するとか，
あるいはもっと前の時点で出力されるようにすれば回避できます．もしまだ文
書を作成している途中なら，とりあえず\\clearpage命令を入れておいて，最
終版を作る時までこの問題は棚上げしておきましょう．入力ファイルが変わる
と問題が解消される場合もあるのです．

pool size
=========
相互参照の\\labelが多すぎるか，命令の定義が多すぎるかのどちらかです．
正確にいえば，定義したラベル名および命令名に使った文字数が多すぎるとい
うことです．ですから，もっと短い名前を使えばこの問題は解決します．ただ
し，このエラーは，\\setcounterなどのカウンタ命令や\\newenvironment・
\\newtheorem命令の引数の終わりを示す右括弧を忘れた場合にも生じます．

save size
=========
このエラーは，宣言の有効範囲や命令・環境があまりにも深く入れ子になって
いる場合に生じます．たとえば，\\multiput命令の引数にpicture環境があり，
そのなかに\\footnotesize宣言があり，その宣言の有効範囲に\\multiput命令
があって，その引数に... というような場合です．")

    ("Text line contains an invalid character." .
"入力中に不正な文字が含まれています．ファイル作成の誤りによってテキスト
エディタがこの文字を挿入してしまったのでしょう．実際に何が起きたのかは
エディタによります．入力ファイルを調べてみて，指摘された文字が見つから
ない場合にはローカルガイドを見てください．")

    ("Undefined control sequence."   .
"TeXが未定義の命令名を発見しました．おそらく入力の誤りでしょう．もしこ
のエラーがLaTeX命令の処理中に生じた場合は，その命令は間違った位置に置か
れています．例えば，リスト環境の中でないのに\\item命令が使われた場合など
です．また，\\documentclass命令がない場合にもこのエラーが生じます．")

    ("Use of [^ ]* doesn't match its definition." .
"おそらく描画のための命令だと思われますが，引数の使いかたが間違ってい
ます．間違っているのが\\@array命令の場合は，array環境かtabular環境での
@表現の引数になにか誤りがあるのでしょう．fragileな命令が\\protectされて
いないのかもしれません．")

    ("You can't use `macro parameter character \\#' in [^ ]* mode." .
"特殊文字#が普通のテキストの中に現れました．おそらく\\#と書きたかった
のでしょう．")

    ("Overfull \\\\hbox .*" .
"行分割のための適切な場所が見つからなかったので，1行に収まるべき分量以上
の出力が行なわれてしまいました．")

    ("Overfull \\\\vbox .*" .
"ページ分割のための適切な場所が見つからなかったので，1ページに収まるべき
分量以上の出力が行なわれてしまいました．")

    ("Underfull \\\\hbox .*" .
"余分な垂直スペースがないかどうか出力を確かめてください．もしあれば，そ
れは\\\\命令または\\newline命令に関係する問題のために生じたものです．例
えば2つの\\\\命令が続いている場合などです．この警告はsloppypar環境や
\\sloppy宣言の使用，あるいは\\linebreak命令の挿入などによる場合もあります．")

    ("Underfull \\\\vbox .*" .
"ページを分割するための適切な場所が見つけられず，十分なテキストのない
ページができてしまいました．")

;; New list items should be placed here
;;
;; ("err-regexp" . "context")
;;
;; the err-regexp item should match anything

    (".*" . "ごめんなさい．該当するヘルプメッセージがありません．"))))

(provide 'tex-jp)

;;; tex-jp.el ends here
