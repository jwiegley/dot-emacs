;;; ascii.el --- ASCII code display.

;; Copyright (C) 1999, 2000, 2001, 2006, 2007, 2008, 2009, 2010, 2011
;; Vinicius Jose Latorre

;; Author:	Vinicius Jose Latorre <viniciusjl@ig.com.br>
;; Maintainer:	Vinicius Jose Latorre <viniciusjl@ig.com.br>
;; Time-stamp:	<2011/01/12 00:58:17 vinicius>
;; Keywords:	data, ascii
;; Version:	3.1
;; X-URL:	http://www.emacswiki.org/cgi-bin/wiki/ViniciusJoseLatorre

;; This file is *NOT* (yet?) part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.

;; This program is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.

;; You should have received a copy of the GNU General Public License along with
;; GNU Emacs; see the file COPYING.  If not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.

;;; Commentary:

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Introduction
;; ------------
;;
;; This package provides a way to display ASCII code on a window, that is,
;; display in another window an ASCII table highlighting the current character
;; code.
;;
;; Well, maybe the name "ascii" is not a good name for this package, as this
;; package also displays non-ASCII code, that is, character code which is
;; greater than 255.  It also displays characters codified in HTML (&Aacute;),
;; quoted (=20), escaped (\xFF) and Emacs Lisp character (?\^A).
;;
;; To use ascii, insert in your ~/.emacs:
;;
;;    (require 'ascii)
;;
;; Or:
;;
;;    (autoload 'ascii-on        "ascii" "Turn on ASCII code display."   t)
;;    (autoload 'ascii-off       "ascii" "Turn off ASCII code display."  t)
;;    (autoload 'ascii-display   "ascii" "Toggle ASCII code display."    t)
;;    (autoload 'ascii-customize "ascii" "Customize ASCII code display." t)
;;
;; For good performance, be sure to byte-compile ascii.el, e.g.
;;
;;    M-x byte-compile-file <give the path to ascii.el when prompted>
;;
;; This will generate ascii.elc, which will be loaded instead of ascii.el.
;;
;; It runs on GNU Emacs 20.4.1, 21, 22 and 23.
;;
;;
;; Using ascii
;; -----------
;;
;; To activate ascii, type:
;;
;;    M-x ascii-on RET
;;
;; Or:
;;
;;    C-u 1 M-x ascii-display RET
;;
;; To deactivate ascii, type:
;;
;;    M-x ascii-off RET
;;
;; Or:
;;
;;    C-u 0 M-x ascii-display RET
;;
;; To toggle ascii, type:
;;
;;    M-x ascii-display RET
;;
;; To customize ascii, type:
;;
;;    M-x ascii-customize RET
;;
;; You can also bind `ascii-display', `ascii-on', `ascii-off' and
;; `ascii-customize' to some key, like:
;;
;;    (global-set-key "\C-c\C-a" 'ascii-on)
;;    (global-set-key "\C-c\C-e" 'ascii-off)
;;    (global-set-key "\C-c\C-t" 'ascii-display)
;;    (global-set-key "\C-c\C-c" 'ascii-customize)
;;
;; If you're using `mule' package, a good usage example is to activate `ascii'
;; on emacs/etc/HELLO file.
;;
;;
;; Hooks
;; -----
;;
;; ascii has the following hook variable:
;;
;; `ascii-hook'
;;    It is evaluated once when ascii is turned on.
;;
;;
;; Options
;; -------
;;
;; Below it's shown a brief description of ascii options, please, see the
;; options declaration in the code for a long documentation.
;;
;; `ascii-code'				Specify list of character code to
;;					display.
;;
;; `ascii-show-nonascii'		Non-nil means converts to unibyte and
;;					display the ascii code.
;;
;; `ascii-show-nonascii-message'	Non-nil means show a message when
;;					character is above 255.
;;
;; `ascii-window-size'			Specify initial ASCII window size.
;;
;; `ascii-display-code'			Specify list of character range to be
;;					displayed.
;;
;; `ascii-keep-window'			Non-nil means to keep ASCII window
;;					active.
;;
;; `ascii-table-separator'		Specify string used to separate ASCII
;;					table columns.
;;
;; `ascii-ascii-face'			Specify symbol face used to highlight
;;					ascii code.
;;
;; `ascii-non-ascii-face'		Specify symbol face used to highlight
;;					non-ascii code.
;;
;; To set the above options you may:
;;
;; a) insert the code in your ~/.emacs, like:
;;
;;	 (setq ascii-window-size 6)
;;
;;    This way always keep your default settings when you enter a new Emacs
;;    session.
;;
;; b) or use `set-variable' in your Emacs session, like:
;;
;;	 M-x set-variable RET ascii-window-size RET 6 RET
;;
;;    This way keep your settings only during the current Emacs session.
;;
;; c) or use customization, for example:
;;	 click on menu-bar *Help* option,
;;	 then click on *Customize*,
;;	 then click on *Browse Customization Groups*,
;;	 expand *Data* group,
;;	 expand *Ascii* group
;;	 and then customize ascii options.
;;    Through this way, you may choose if the settings are kept or not when
;;    you leave out the current Emacs session.
;;
;; d) or see the option value:
;;
;;	 C-h v ascii-window-size RET
;;
;;    and click the *customize* hypertext button.
;;    Through this way, you may choose if the settings are kept or not when
;;    you leave out the current Emacs session.
;;
;; e) or invoke:
;;
;;	 M-x ascii-customize RET
;;
;;    and then customize ascii options.
;;    Through this way, you may choose if the settings are kept or not when
;;    you leave out the current Emacs session.
;;
;;
;; Acknowledgments
;; ---------------
;;
;; Thanks to Steven W. Orr <steveo@syslang.net> for patch to Emacs 23.
;;
;; Thanks to Roman Belenov <roman@nstl.nnov.ru> for suggestion on dynamic ascii
;; table evaluation (depending on character encoding).
;;
;; Thanks to Alex Schroeder <asc@bsiag.com> for suggestion on customization.
;;
;;
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; code:


;; XEmacs needs overlay emulation package.
(eval-and-compile
  (and (let (case-fold-search)
	 (string-match "XEmacs\\|Lucid\\|Epoch" emacs-version))
       (not (require 'overlay))
       (error "`ascii' requires `overlay' package.")))


;; GNU Emacs 20, 21 and 22 compatibility
(or (fboundp 'characterp)
    (defalias 'characterp 'char-valid-p))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; User Variables:


;;; Interface to the command system


(defgroup ascii nil
  "ASCII code display"
  :link '(emacs-library-link :tag "Source Lisp File" "ascii.el")
  :prefix "ascii-"
  :group 'data)


(defcustom ascii-code '(quoted html backslash elisp)
  "*Specify list of character code to display.

If list is nil, display only ASCII code.

If list is non-nil, valid element values are:

   quoted	display quoted and ASCII code.
		Quoted code is specified by `=HH' where H is a hexadecimal
		character or by `=' followed by newline.  This character coding
		is used on MIME.  For example:
		=FF  =1f  =20  =

   html		display HTML and ASCII code.
		HTML code is specified by `&CODE;', for example:
		&aacute;  &Aacute;  &#192;

   backslash	display backslash and ASCII code.
		Backslash code is specified by `\\CODE' like in C, for example:
		\\177  \\xFF  \\x1f  \\t  \\Z  \\\\

   elisp	display Emacs Lisp and ASCII code.
		Emacs Lisp code is specified by `?CODE', see how Emacs Lisp
		specify a character.  For example:
		??  ?a  ?A  ?\\^A  ?\\C-A
		?\\177  ?\\xFF  ?\\x1f  ?\\t  ?\\Z  ?\\\\

Any other value is ignored."
  :type '(repeat :tag "ASCII Code List"
		 (choice :menu-tag "ASCII Code"
			 :tag "ASCII Code"
			 (const :tag "Quoted" quoted)
			 (const :tag "HTML" html)
			 (const :tag "Backslash" backslash)
			 (const :tag "Elisp" elisp)))
  :group 'ascii)


(defcustom ascii-show-nonascii t
  "*Non-nil means converts to unibyte and display the ascii code."
  :type 'boolean
  :group 'ascii)


(defcustom ascii-show-nonascii-message t
  "*Non-nil means show a message when character is above 255."
  :type 'boolean
  :group 'ascii)


(defcustom ascii-window-size 6
  "*Specify initial ASCII window size."
  :type 'integer
  :group 'ascii)


(defcustom ascii-display-code '((?\000 . ?\377))
  "*Specify list of character range to be displayed.

Each element has the following form:

   (LOWER . UPPER)

LOWER and UPPER are the minimum and maximum character code, respectively.
A character is displayed if:
   LOWER <= character <= UPPER
   and 0 <= LOWER <= 255
   and 0 <= UPPER <= 255"
  :type '(repeat :tag "Range List"
		 (cons :tag "Range"
		       (integer :tag "From")
		       (integer :tag "To")))
  :group 'ascii)


(defcustom ascii-keep-window t
  "*Non-nil means to keep ASCII window active."
  :type 'boolean
  :group 'ascii)


(defcustom ascii-table-separator "|"
  "*Specify string used to separate ASCII table columns."
  :type 'string
  :group 'ascii)


(defcustom ascii-ascii-face 'ascii-ascii-face
  "*Specify symbol face used to highlight ascii code."
  :type 'face
  :group 'ascii)


;; secondary-selection face
(defface ascii-ascii-face
  '((((type tty) (class color))
     (:background "cyan" :foreground "black"))
    (((class color) (background light))
     (:background "paleturquoise"))
    (((class color) (background dark))
     (:background "SkyBlue4"))
    (t (:inverse-video t)))
  "Face used to highlight ascii code.")


(defcustom ascii-non-ascii-face 'ascii-non-ascii-face
  "*Specify symbol face used to highlight non-ascii code."
  :type 'face
  :group 'ascii)


;; highlight face
(defface ascii-non-ascii-face
  '((((type tty) (class color))
     (:background "green"))
    (((class color) (background light))
     (:background "darkseagreen2"))
    (((class color) (background dark))
     (:background "darkolivegreen"))
    (t (:inverse-video t)))
  "Face used to highlight non-ascii code.")

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization


;;;###autoload
(defun ascii-customize ()
  "Customize ASCII options."
  (interactive)
  (customize-group 'ascii))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; User commands


(defconst ascii-buffer-name " *ASCII*")


(defvar ascii-overlay         nil)
(defvar ascii-reference-count 0)


(defvar ascii-display nil)
(make-variable-buffer-local 'ascii-display)


;;;###autoload
(defun ascii-display (&optional arg)
  "Toggle ASCII code display.

If ARG is null, toggle ASCII code display.
If ARG is a number and is greater than zero, turn on display; otherwise, turn
off display.
If ARG is anything else, turn on display."
  (interactive "P")
  (if (if arg
	  (> (prefix-numeric-value arg) 0)
	(not ascii-display))
      (ascii-on)
    (ascii-off)))


;;;###autoload
(defun ascii-on ()
  "Turn on ASCII code display."
  (interactive)
  (unless ascii-display
    (setq ascii-display         t
	  ascii-reference-count (1+ ascii-reference-count))
    ;; local hooks
    (add-hook 'post-command-hook 'ascii-post-command nil t)
    (add-hook 'kill-buffer-hook 'ascii-off nil t)
    ;; own hook
    (run-hooks 'ascii-hook)
    (ascii-post-command)))


;;;###autoload
(defun ascii-off ()
  "Turn off ASCII code display."
  (interactive)
  (when ascii-display
    (setq ascii-display         nil
	  ascii-reference-count (1- ascii-reference-count))
    (remove-hook 'post-command-hook 'ascii-post-command t)
    (remove-hook 'kill-buffer-hook 'ascii-off t)
    (if (> ascii-reference-count 0)
	;; at least one buffer with ascii activated
	(or ascii-keep-window
	    (ascii-hide-table))
      ;; *no* buffer with ascii activated
      (and ascii-overlay
	   (delete-overlay ascii-overlay))
      (let ((buffer (get-buffer ascii-buffer-name)))
	(and buffer
	     (save-excursion
	       (delete-windows-on buffer)
	       (kill-buffer buffer)))))))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal variables


(defconst ascii-table
  (concat
   ;; (0 <= x <= 127)
   " OCT DEC HX               |-  OCT DEC HX    |-  OCT DEC HX    \
|-  OCT DEC HX\n"
   (let ((str "")
	 (c   -1)
	 (cod [
	       "C-@ NUL ^@   "		; 0
	       "C-a SOH ^A   "		; 1
	       "C-b STX ^B   "		; 2
	       "C-c ETX ^C   "		; 3
	       "C-d EOT ^D   "		; 4
	       "C-e ENQ ^E   "		; 5
	       "C-f ACK ^F   "		; 6
	       "C-g BEL ^G \\a"		; 7
	       "C-h BS  ^H \\b"		; 8
	       "TAB HT  ^I \\t"		; 9
	       "C-j LF  ^J \\n"		; 10
	       "C-k VT  ^K \\v"		; 11
	       "C-l FF  ^L \\f"		; 12
	       "RET CR  ^M \\r"		; 13
	       "C-n SO  ^N   "		; 14
	       "C-o SI  ^O   "		; 15
	       "C-p DLE ^P   "		; 16
	       "C-q DC1 ^Q   "		; 17
	       "C-r DC2 ^R   "		; 18
	       "C-s DC3 ^S   "		; 19
	       "C-t DC4 ^T   "		; 20
	       "C-u NAK ^U   "		; 21
	       "C-v SYN ^V   "		; 22
	       "C-w ETB ^W   "		; 23
	       "C-x CAN ^X   "		; 24
	       "C-y EM  ^Y   "		; 25
	       "C-z SUB ^Z   "		; 26
	       "ESC ESC ^[ \\e"		; 27
	       "C-\\ FS  ^\\   "	; 28
	       "C-] GS  ^]   "		; 29
	       "C-^ RS  ^^   "		; 30
	       "C-_ US  ^_   "		; 31
	       ])
	 c32 c64 c96)
     (while (< c 31)
       (setq c   (1+ c)
	     c32 (+ c 32)
	     c64 (+ c 64)
	     c96 (+ c 96)
	     str (concat
		  str
		  (format "\\%03o %03d %02x  %s|| \\%03o %03d %02x %s|| \
\\%03o %03d %02x  %c || \\%03o %03d %02x %s\n"
			  c   c   c (aref cod c)
			  c32 c32 c32
			  (if (= c32 ?\x20) "SPC"    (format " %c "c32))
			  c64 c64 c64 c64
			  c96 c96 c96
			  (if (= c96 ?\x7F) "DEL ^?" (format " %c" c96))))))
     str)

   ;; (128 <= x <= 255)
   "\n OCT DEC HX               |-  OCT DEC HX    |-  OCT DEC HX    \
|-  OCT DEC HX\n"
   (let ((str "")
	 (c   127)
	 c32 c64 c96)
     (while (< c 159)
       (setq c   (1+ c)
	     c32 (+ c 32)
	     c64 (+ c 64)
	     c96 (+ c 96)
	     str (concat
		  str
		  (format "\\%03o %03d %02x  \\%03o         || \
\\%03o %03d %02x  %c || \\%03o %03d %02x  %c || \\%03o %03d %02x  %c\n"
			  c   c   c   c
			  c32 c32 c32 c32
			  c64 c64 c64 c64
			  c96 c96 c96 c96))))
     str))
  "ASCII table.")


(defconst ascii-position
  (vector
   ;; 0             1             2             3
   [2  0  23 0]  [3  0  23 0]  [4  0  23 0]  [5  0  23 0]
   ;; 4             5             6             7
   [6  0  23 0]  [7  0  23 0]  [8  0  23 0]  [9  0  26 0]
   ;; 8             9             10            11
   [10 0  26 0]  [11 0  26 0]  [12 0  26 0]  [13 0  26 0]
   ;; 12            13            14            15
   [14 0  26 0]  [15 0  26 0]  [16 0  23 0]  [17 0  23 0]
   ;; 16            17            18            19
   [18 0  23 0]  [19 0  23 0]  [20 0  23 0]  [21 0  23 0]
   ;; 20            21            22            23
   [22 0  23 0]  [23 0  23 0]  [24 0  23 0]  [25 0  23 0]
   ;; 24            25            26            27
   [26 0  23 0]  [27 0  23 0]  [28 0  23 0]  [29 0  26 0]
   ;; 28            29            30            31
   [30 0  23 0]  [31 0  23 0]  [32 0  23 0]  [33 0  23 0]
   ;; 32            33            34            35
   [2  28 43 1]  [3  28 42 1]  [4  28 42 1]  [5  28 42 1]
   ;; 36            37            38            39
   [6  28 42 1]  [7  28 42 1]  [8  28 42 1]  [9  28 42 1]
   ;; 40            41            42            43
   [10 28 42 1]  [11 28 42 1]  [12 28 42 1]  [13 28 42 1]
   ;; 44            45            46            47
   [14 28 42 1]  [15 28 42 1]  [16 28 42 1]  [17 28 42 1]
   ;; 48            49            50            51
   [18 28 42 1]  [19 28 42 1]  [20 28 42 1]  [21 28 42 1]
   ;; 52            53            54            55
   [22 28 42 1]  [23 28 42 1]  [24 28 42 1]  [25 28 42 1]
   ;; 56            57            58            59
   [26 28 42 1]  [27 28 42 1]  [28 28 42 1]  [29 28 42 1]
   ;; 60            61            62            63
   [30 28 42 1]  [31 28 42 1]  [32 28 42 1]  [33 28 42 1]
   ;; 64            65            66            67
   [2  45 59 2]  [3  45 59 2]  [4  45 59 2]  [5  45 59 2]
   ;; 68            69            70            71
   [6  45 59 2]  [7  45 59 2]  [8  45 59 2]  [9  45 59 2]
   ;; 72            73            74            75
   [10 45 59 2]  [11 45 59 2]  [12 45 59 2]  [13 45 59 2]
   ;; 76            77            78            79
   [14 45 59 2]  [15 45 59 2]  [16 45 59 2]  [17 45 59 2]
   ;; 80            81            82            83
   [18 45 59 2]  [19 45 59 2]  [20 45 59 2]  [21 45 59 2]
   ;; 84            85            86            87
   [22 45 59 2]  [23 45 59 2]  [24 45 59 2]  [25 45 59 2]
   ;; 88            89            90            91
   [26 45 59 2]  [27 45 59 2]  [28 45 59 2]  [29 45 59 2]
   ;; 92            93            94            95
   [30 45 59 2]  [31 45 59 2]  [32 45 59 2]  [33 45 59 2]
   ;; 96            97            98            99
   [2  62 76 3]  [3  62 76 3]  [4  62 76 3]  [5  62 76 3]
   ;; 100           101           102           103
   [6  62 76 3]  [7  62 76 3]  [8  62 76 3]  [9  62 76 3]
   ;; 104           105           106           107
   [10 62 76 3]  [11 62 76 3]  [12 62 76 3]  [13 62 76 3]
   ;; 108           109           110           111
   [14 62 76 3]  [15 62 76 3]  [16 62 76 3]  [17 62 76 3]
   ;; 112           113           114           115
   [18 62 76 3]  [19 62 76 3]  [20 62 76 3]  [21 62 76 3]
   ;; 116           117           118           119
   [22 62 76 3]  [23 62 76 3]  [24 62 76 3]  [25 62 76 3]
   ;; 120           121           122           123
   [26 62 76 3]  [27 62 76 3]  [28 62 76 3]  [29 62 76 3]
   ;; 124           125           126           127
   [30 62 76 3]  [31 62 76 3]  [32 62 76 3]  [33 62 80 3]
   ;; 128           129           130           131
   [36 0  17 0]  [37 0  17 0]  [38 0  17 0]  [39 0  17 0]
   ;; 132           133           134           135
   [40 0  17 0]  [41 0  17 0]  [42 0  17 0]  [43 0  17 0]
   ;; 136           137           138           139
   [44 0  17 0]  [45 0  17 0]  [46 0  17 0]  [47 0  17 0]
   ;; 140           141           142           143
   [48 0  17 0]  [49 0  17 0]  [50 0  17 0]  [51 0  17 0]
   ;; 144           145           146           147
   [52 0  17 0]  [53 0  17 0]  [54 0  14 0]  [55 0  17 0]
   ;; 148           149           150           151
   [56 0  17 0]  [57 0  17 0]  [58 0  17 0]  [59 0  17 0]
   ;; 152           153           154           155
   [60 0  17 0]  [61 0  17 0]  [62 0  17 0]  [63 0  17 0]
   ;; 156           157           158           159
   [64 0  17 0]  [65 0  17 0]  [66 0  17 0]  [67 0  17 0]
   ;; 160           161           162           163
   [36 28 42 1]  [37 28 42 1]  [38 28 42 1]  [39 28 42 1]
   ;; 164           165           166           167
   [40 28 42 1]  [41 28 42 1]  [42 28 42 1]  [43 28 42 1]
   ;; 168           169           170           171
   [44 28 42 1]  [45 28 42 1]  [46 28 42 1]  [47 28 42 1]
   ;; 172           173           174           175
   [48 28 42 1]  [49 28 42 1]  [50 28 42 1]  [51 28 42 1]
   ;; 176           177           178           179
   [52 28 42 1]  [53 28 42 1]  [54 28 42 1]  [55 28 42 1]
   ;; 180           181           182           183
   [56 28 42 1]  [57 28 42 1]  [58 28 42 1]  [59 28 42 1]
   ;; 184           185           186           187
   [60 28 42 1]  [61 28 42 1]  [62 28 42 1]  [63 28 42 1]
   ;; 188           189           190           191
   [64 28 42 1]  [65 28 42 1]  [66 28 42 1]  [67 28 42 1]
   ;; 192           193           194           195
   [36 45 59 2]  [37 45 59 2]  [38 45 59 2]  [39 45 59 2]
   ;; 196           197           198           199
   [40 45 59 2]  [41 45 59 2]  [42 45 59 2]  [43 45 59 2]
   ;; 200           201           202           203
   [44 45 59 2]  [45 45 59 2]  [46 45 59 2]  [47 45 59 2]
   ;; 204           205           206           207
   [48 45 59 2]  [49 45 59 2]  [50 45 59 2]  [51 45 59 2]
   ;; 208           209           210           211
   [52 45 59 2]  [53 45 59 2]  [54 45 59 2]  [55 45 59 2]
   ;; 212           213           214           215
   [56 45 59 2]  [57 45 59 2]  [58 45 59 2]  [59 45 59 2]
   ;; 216           217           218           219
   [60 45 59 2]  [61 45 59 2]  [62 45 59 2]  [63 45 59 2]
   ;; 220           221           222           223
   [64 45 59 2]  [65 45 59 2]  [66 45 59 2]  [67 45 59 2]
   ;; 224           225           226           227
   [36 62 76 3]  [37 62 76 3]  [38 62 76 3]  [39 62 76 3]
   ;; 228           229           230           231
   [40 62 76 3]  [41 62 76 3]  [42 62 76 3]  [43 62 76 3]
   ;; 232           233           234           235
   [44 62 76 3]  [45 62 76 3]  [46 62 76 3]  [47 62 76 3]
   ;; 236           237           238           239
   [48 62 76 3]  [49 62 76 3]  [50 62 76 3]  [51 62 76 3]
   ;; 240           241           242           243
   [52 62 76 3]  [53 62 76 3]  [54 62 76 3]  [55 62 76 3]
   ;; 244           245           246           247
   [56 62 76 3]  [57 62 76 3]  [58 62 76 3]  [59 62 76 3]
   ;; 248           249           250           251
   [60 62 76 3]  [61 62 76 3]  [62 62 76 3]  [63 62 76 3]
   ;; 252           253           254           255
   [64 62 76 3]  [65 62 76 3]  [66 62 76 3]  [67 62 76 3]
   )
  "Vector with position of each ASCII code in ASCII buffer.

Each element has the following form:

   [LINE COL-BEG COL-END COL-INDEX]

LINE is the line number in ASCII buffer.
COL-BEG is the ASCII beginning column.
COL-END is the ASCII end column.
COL-INDEX is the ASCII table column index.")

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Internal functions


(defun ascii-post-command ()
  (let* ((char (following-char))
	 (code (if ascii-show-nonascii
		   (string-to-char (string-make-unibyte (char-to-string char)))
		 char))
	 mess)
    (cond ((and (boundp 'ascii-display)
		ascii-display
		(< code 256)
		(ascii-display-code code))
	   (setq mess (ascii-show-table code (< char 256))))
	  ((and (not ascii-keep-window)
		(not (string= (buffer-name) ascii-buffer-name)))
	   (ascii-hide-table))
	  (ascii-overlay
	   (delete-overlay ascii-overlay))
	  )
    ;; display some warning
    (cond ((and (boundp 'ascii-display)
		ascii-display
		ascii-show-nonascii-message
		(cond
		 ((> char 255)
		  (message "Character code above 255 (\\0%o, %d, 0x%x)"
			   char char char))
		 ((< char 0)
		  (message "Character code below 0 (\\0%o, %d, 0x%x)"
			   char char char))
		 )))
	  (mess
	   (message "%s code" mess))
	  )))


(defun ascii-hide-table ()
  (let ((buffer (get-buffer ascii-buffer-name)))
    (and buffer
	 (delete-windows-on buffer))))


(defconst ascii-html-alist
  '(("copy"   . 169) ("reg"    . 174) ("trade"  . 174) ("Aacute" . 192)
    ("Agrave" . 193) ("Acirc"  . 194) ("Atilde" . 195) ("Auml"   . 196)
    ("Aring"  . 197) ("AElig"  . 198) ("Ccedil" . 199) ("Eacute" . 200)
    ("Egrave" . 201) ("Ecirc"  . 202) ("Euml"   . 203) ("Iacute" . 204)
    ("Igrave" . 205) ("Icirc"  . 206) ("Iuml"   . 207) ("ETH"    . 208)
    ("Ntilde" . 209) ("Oacute" . 210) ("Ograve" . 211) ("Ocirc"  . 212)
    ("Otilde" . 213) ("Ouml"   . 214) ("Oslash" . 216) ("Uacute" . 217)
    ("Ugrave" . 218) ("Ucirc"  . 219) ("Uuml"   . 220) ("Yacute" . 221)
    ("THORN"  . 222) ("szlig"  . 223) ("aacute" . 224) ("agrave" . 225)
    ("acirc"  . 226) ("atilde" . 227) ("auml"   . 228) ("aring"  . 229)
    ("aelig"  . 230) ("ccedil" . 231) ("eacute" . 232) ("egrave" . 233)
    ("ecirc"  . 234) ("euml"   . 235) ("iacute" . 236) ("igrave" . 237)
    ("icirc"  . 238) ("iuml"   . 239) ("eth"    . 240) ("ntilde" . 241)
    ("oacute" . 242) ("ograve" . 243) ("ocirc"  . 244) ("otilde" . 245)
    ("ouml"   . 246) ("oslash" . 248) ("uacute" . 249) ("ugrave" . 250)
    ("ucirc"  . 251) ("uuml"   . 252) ("yacute" . 253) ("thorn"  . 254)
    ("yuml"   . 255)))


;; &aacute;  &Aacute;  &#192;
(defconst ascii-html-regexp
  (concat "&\\([aeiouy]acute\\|[aeiou]circ\\|[aeiou]grave\\|[aeiouy]uml\\|"
	   "aelig\\|aring\\|[ano]tilde\\|ccedil\\|copy\\|eth\\|oslash\\|"
	   "reg\\|szlig\\|thorn\\|trade\\|"
	   "#[0-9]+\\);"))


;; \177  \xFF  \t  \Z  \\
(defconst ascii-backslash-regexp
  "\\\\\\([0-7]+\\|x[0-9A-Fa-f]+\\|\n\\|.\\)")


;; ?A  ?\^A  ?\C-A  ?\177  ?\xFF  ?\t  ?\Z  ?\\
(defconst ascii-elisp-regexp
  (concat "?\\(\\\\\\(\\^\\|C-\\)[@A-Za-_]\\|"
	  ascii-backslash-regexp
	  "\\|.\\)"))


(defsubst ascii-string-matched (level)
  (buffer-substring-no-properties
   (match-beginning level) (match-end level)))


(defsubst ascii-string-to-char (str)
  (string-to-char (car (read-from-string (concat "\"" str "\"")))))


(defsubst ascii-char-matched (level)
  (ascii-string-to-char (ascii-string-matched level)))


(defsubst ascii-code (code var-sym)
  (save-match-data
    (cond
     ;; Quoted
     ((and (memq 'quoted ascii-code)
	   (cond ((looking-at "=\n")
		  (set var-sym "Quoted")
		  ?\n)
		 ((looking-at "=\\([0-9A-Fa-f][0-9A-Fa-f]\\)")
		  (set var-sym "Quoted")
		  (string-to-number (ascii-string-matched 1) 16)))))
     ;; HTML
     ((and (memq 'html ascii-code)
	   (let ((case-fold-search t))
	     (looking-at ascii-html-regexp)))
      (set var-sym "HTML")
      (let ((str (ascii-string-matched 1)))
	(cond ((eq (aref str 0) ?#)
	       (aset str 0 ?\ )
	       (let ((int (string-to-number str)))
		 (if (and (<= 0 int) (<= int 255))
		     int
		   (set var-sym nil)
		   code)))
	      ((cdr (assoc str ascii-html-alist)))
	      (t
	       (set var-sym nil)
	       code))))
     ;; backslash
     ((and (memq 'backslash ascii-code)
	   (looking-at ascii-backslash-regexp))
      (set var-sym "Backslash")
      (let* ((str  (ascii-string-matched 0))
	     (last (aref str (1- (length str)))))
	(if (memq last '(?^ ?C ?\n))
	    last
	  (ascii-string-to-char str))))
     ;; elisp
     ((and (memq 'elisp ascii-code)
	   (looking-at ascii-elisp-regexp))
      (set var-sym "Elisp")
      (ascii-char-matched 1))
     ;; ASCII
     (t
      (set var-sym nil)
      code))))


(defvar ascii-sep-len      0)
(defvar ascii-charset-base 0)


(defun ascii-show-table (code ascii-p)
  (let ((buffer (ascii-get-buffer code))
	mess)
    (and
     ;; adjust ascii window
     (cond ((get-buffer-window buffer)
	    t)
	   ((>= (window-height) (+ ascii-window-size ascii-window-size))
	    (set-window-buffer
	     (split-window nil (- (window-height) ascii-window-size))
	     buffer)
	    t)
	   (t
	    (ascii-off)
	    (message "Window height too small for ASCII window.")
	    (ding)
	    nil)
	   )
     ;; adjust overlay
     (let ((code       (ascii-code code 'mess))
	   (window     (get-buffer-window ascii-buffer-name))
	   (old-window (selected-window)))
       (save-excursion
	 (and window
	      (select-window window))
	 (set-buffer ascii-buffer-name)
	 (let ((pos (aref ascii-position code))
	       beg end)
	   (goto-char (point-min))
	   (forward-line (1- (aref pos 0)))
	   (if (and (> code 127) (/= ascii-charset-base 127))
	       (save-match-data
		 (re-search-forward
		  (format "\\\\%o %d %x  \\(\\\\..\\)?."
			  code code code)
		  nil t)
		 (setq beg (match-beginning 0)
		       end (match-end 0)))
	     (let ((here (point))
		   (bias (* (aref pos 3) ascii-sep-len)))
	       (setq end  (+ (aref pos 2) here bias)
		     beg  (+ (aref pos 1) here bias))))
	   (if ascii-overlay
	       (move-overlay ascii-overlay beg end)
	     (setq ascii-overlay (make-overlay beg end)))
	   (overlay-put ascii-overlay 'face (if ascii-p
						ascii-ascii-face
					      ascii-non-ascii-face))))
       (select-window old-window)))
    mess))


(defvar ascii-mark-display-code nil)
(defvar ascii-vector-code (make-vector 256 t))


(defun ascii-display-code (code)
  (or (eq ascii-mark-display-code ascii-display-code)
      (let ((lis  ascii-display-code)
	    (char 0)
	    end)
	(setq ascii-mark-display-code ascii-display-code)
	;; turn off all `ascii-vector-code'
	(while (<= char 255)
	  (aset ascii-vector-code char nil)
	  (setq char (1+ char)))
	;; turn on valid ranges
	(while lis
	  (setq char (car lis)
		lis  (cdr lis)
		end  (cdr char)
		char (car char))
	  (and (<= 0 end)  (<= end 255)
	       (<= 0 char) (<= char 255)
	       (while (<= char end)
		 (aset ascii-vector-code char t)
		 (setq char (1+ char)))))))
  (aref ascii-vector-code code))


(defun ascii-get-buffer (code)
  (let ((base (- (following-char) (- code 127))))
    (or (if (= ascii-charset-base base)
	    (get-buffer ascii-buffer-name)
	  (setq ascii-charset-base base)
	  (let ((buffer (get-buffer ascii-buffer-name)))
	    (when buffer
	      (delete-windows-on buffer)
	      (kill-buffer buffer)))
	  nil)
	(save-excursion
	  (save-match-data
	    (prog1
		;; create buffer
		(set-buffer (get-buffer-create ascii-buffer-name))
	      (set-buffer-multibyte t)
	      (setq buffer-read-only nil
		    ascii-sep-len    (1- (length ascii-table-separator)))
	      (erase-buffer)
	      ;; insert ascii table
	      (insert ascii-table)
	      (goto-char (point-min))
	      (or (= base 127)
		  (save-excursion
		    (let ((char 127))
		      ;; characters from 128 to 159
		      (while (< (setq char (1+ char)) 160)
			(when (search-forward
			       (format "\\%o %d %x  " char char char)
			       nil t)
			  (delete-char 4)
			  (setq base (1+ base))
			  (if (not (characterp base))
			      (insert "?   ")
			    (insert base)
			    (let ((cols (- (current-column)
					   (progn
					     (forward-char -1)
					     (current-column)))))
			      (when (< cols 4)
				(forward-char 1)
				(insert (cond ((= cols 3) " ")
					      ((= cols 2) "  ")
					      (t          "   ")
					      )))))))
		      ;; characters from 160 to 255
		      (setq char (1- char))
		      (while (< (setq char (1+ char)) 256)
			(goto-char (point-min))
			(when (search-forward
			       (format "\\%o %d %x  " char char char)
			       nil t)
			  (delete-char 1)
			  (setq base (1+ base))
			  (if (not (characterp base))
			      (insert "?")
			    (insert base)
			    (let ((cols (- (current-column)
					   (progn
					     (forward-char -1)
					     (current-column)))))
			      (when (> cols 1)
				(forward-char 1)
				(or (equal (following-char) ?\n)
				    (delete-char 1))))))))))
	      ;; adjust column table separator
	      (save-excursion
		(while (search-forward "||" nil t)
		  (replace-match ascii-table-separator t t)))
	      ;; adjust header separator
	      (let ((spaces (make-string (1+ ascii-sep-len) ?\ )))
		(save-excursion
		  (while (search-forward "|-" nil t)
		    (replace-match spaces t t))))
	      (set-buffer-modified-p nil)
	      (setq buffer-read-only t)))))))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(provide 'ascii)


;;; ascii.el ends here
