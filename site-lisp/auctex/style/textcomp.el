;;; textcomp.el --- AUCTeX style for `textcomp.sty' (v1.99g)

;; Copyright (C) 2014, 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-25
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

;; This file adds support for `textcomp.sty' (v1.99g) from 2005/09/27.
;; `textcomp.sty' is a standard LaTeX package and part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "textcomp"
 (lambda ()
   (TeX-add-symbols
    '("capitalgrave"             0)     ; Type: Accent -- Slot: 0
    '("capitalacute"             0)     ; Type: Accent -- Slot: 1
    '("capitalcircumflex"        0)     ; Type: Accent -- Slot: 2
    '("capitaltilde"             0)     ; Type: Accent -- Slot: 3
    '("capitaldieresis"          0)     ; Type: Accent -- Slot: 4
    '("capitalhungarumlaut"      0)     ; Type: Accent -- Slot: 5
    '("capitalring"              0)     ; Type: Accent -- Slot: 6
    '("capitalcaron"             0)     ; Type: Accent -- Slot: 7
    '("capitalbreve"             0)     ; Type: Accent -- Slot: 8
    '("capitalmacron"            0)     ; Type: Accent -- Slot: 9
    '("capitaldotaccent"         0)     ; Type: Accent -- Slot: 10
    '("t"                        0)     ; Type: Accent -- Slot: 26
    '("capitaltie"               0)     ; Type: Accent -- Slot: 27
    '("newtie"                   0)     ; Type: Accent -- Slot: 28
    '("capitalnewtie"            0)     ; Type: Accent -- Slot: 29
    '("textcapitalcompwordmark"  0)     ; Type: Symbol -- Slot: 23
    '("textascendercompwordmark" 0)     ; Type: Symbol -- Slot: 31
    '("textquotestraightbase"    0)     ; Type: Symbol -- Slot: 13
    '("textquotestraightdblbase" 0)     ; Type: Symbol -- Slot: 18
    '("texttwelveudash"          0)     ; Type: Symbol -- Slot: 21
    '("textthreequartersemdash"  0)     ; Type: Symbol -- Slot: 22
    '("textleftarrow"            0)     ; Type: Symbol -- Slot: 24
    '("textrightarrow"           0)     ; Type: Symbol -- Slot: 25
    '("textblank"                0)     ; Type: Symbol -- Slot: 32
    '("textdollar"               0)     ; Type: Symbol -- Slot: 36
    '("textquotesingle"          0)     ; Type: Symbol -- Slot: 39
    '("textasteriskcentered"     0)     ; Type: Symbol -- Slot: 42
    '("textdblhyphen"            0)     ; Type: Symbol -- Slot: 45
    '("textfractionsolidus"      0)     ; Type: Symbol -- Slot: 47
    '("textzerooldstyle"         0)     ; Type: Symbol -- Slot: 48
    '("textoneoldstyle"          0)     ; Type: Symbol -- Slot: 49
    '("texttwooldstyle"          0)     ; Type: Symbol -- Slot: 50
    '("textthreeoldstyle"        0)     ; Type: Symbol -- Slot: 51
    '("textfouroldstyle"         0)     ; Type: Symbol -- Slot: 52
    '("textfiveoldstyle"         0)     ; Type: Symbol -- Slot: 53
    '("textsixoldstyle"          0)     ; Type: Symbol -- Slot: 54
    '("textsevenoldstyle"        0)     ; Type: Symbol -- Slot: 55
    '("texteightoldstyle"        0)     ; Type: Symbol -- Slot: 56
    '("textnineoldstyle"         0)     ; Type: Symbol -- Slot: 57
    '("textlangle"               0)     ; Type: Symbol -- Slot: 60
    '("textminus"                0)     ; Type: Symbol -- Slot: 61
    '("textrangle"               0)     ; Type: Symbol -- Slot: 62
    '("textmho"                  0)     ; Type: Symbol -- Slot: 77
    '("textbigcircle"            0)     ; Type: Symbol -- Slot: 79
    '("textohm"                  0)     ; Type: Symbol -- Slot: 87
    '("textlbrackdbl"            0)     ; Type: Symbol -- Slot: 91
    '("textrbrackdbl"            0)     ; Type: Symbol -- Slot: 93
    '("textuparrow"              0)     ; Type: Symbol -- Slot: 94
    '("textdownarrow"            0)     ; Type: Symbol -- Slot: 95
    '("textasciigrave"           0)     ; Type: Symbol -- Slot: 96
    '("textborn"                 0)     ; Type: Symbol -- Slot: 98
    '("textdivorced"             0)     ; Type: Symbol -- Slot: 99
    '("textdied"                 0)     ; Type: Symbol -- Slot: 100
    '("textleaf"                 0)     ; Type: Symbol -- Slot: 108
    '("textmarried"              0)     ; Type: Symbol -- Slot: 109
    '("textmusicalnote"          0)     ; Type: Symbol -- Slot: 110
    '("texttildelow"             0)     ; Type: Symbol -- Slot: 126
    '("textdblhyphenchar"        0)     ; Type: Symbol -- Slot: 127
    '("textasciibreve"           0)     ; Type: Symbol -- Slot: 128
    '("textasciicaron"           0)     ; Type: Symbol -- Slot: 129
    '("textacutedbl"             0)     ; Type: Symbol -- Slot: 130
    '("textgravedbl"             0)     ; Type: Symbol -- Slot: 131
    '("textdagger"               0)     ; Type: Symbol -- Slot: 132
    '("textdaggerdbl"            0)     ; Type: Symbol -- Slot: 133
    '("textbardbl"               0)     ; Type: Symbol -- Slot: 134
    '("textperthousand"          0)     ; Type: Symbol -- Slot: 135
    '("textbullet"               0)     ; Type: Symbol -- Slot: 136
    '("textcelsius"              0)     ; Type: Symbol -- Slot: 137
    '("textdollaroldstyle"       0)     ; Type: Symbol -- Slot: 138
    '("textcentoldstyle"         0)     ; Type: Symbol -- Slot: 139
    '("textflorin"               0)     ; Type: Symbol -- Slot: 140
    '("textcolonmonetary"        0)     ; Type: Symbol -- Slot: 141
    '("textwon"                  0)     ; Type: Symbol -- Slot: 142
    '("textnaira"                0)     ; Type: Symbol -- Slot: 143
    '("textguarani"              0)     ; Type: Symbol -- Slot: 144
    '("textpeso"                 0)     ; Type: Symbol -- Slot: 145
    '("textlira"                 0)     ; Type: Symbol -- Slot: 146
    '("textrecipe"               0)     ; Type: Symbol -- Slot: 147
    '("textinterrobang"          0)     ; Type: Symbol -- Slot: 148
    '("textinterrobangdown"      0)     ; Type: Symbol -- Slot: 149
    '("textdong"                 0)     ; Type: Symbol -- Slot: 150
    '("texttrademark"            0)     ; Type: Symbol -- Slot: 151
    '("textpertenthousand"       0)     ; Type: Symbol -- Slot: 152
    '("textpilcrow"              0)     ; Type: Symbol -- Slot: 153
    '("textbaht"                 0)     ; Type: Symbol -- Slot: 154
    '("textnumero"               0)     ; Type: Symbol -- Slot: 155
    '("textdiscount"             0)     ; Type: Symbol -- Slot: 156
    '("textestimated"            0)     ; Type: Symbol -- Slot: 157
    '("textopenbullet"           0)     ; Type: Symbol -- Slot: 158
    '("textservicemark"          0)     ; Type: Symbol -- Slot: 159
    '("textlquill"               0)     ; Type: Symbol -- Slot: 160
    '("textrquill"               0)     ; Type: Symbol -- Slot: 161
    '("textcent"                 0)     ; Type: Symbol -- Slot: 162
    '("textsterling"             0)     ; Type: Symbol -- Slot: 163
    '("textcurrency"             0)     ; Type: Symbol -- Slot: 164
    '("textyen"                  0)     ; Type: Symbol -- Slot: 165
    '("textbrokenbar"            0)     ; Type: Symbol -- Slot: 166
    '("textsection"              0)     ; Type: Symbol -- Slot: 167
    '("textasciidieresis"        0)     ; Type: Symbol -- Slot: 168
    '("textcopyright"            0)     ; Type: Symbol -- Slot: 169
    '("textordfeminine"          0)     ; Type: Symbol -- Slot: 170
    '("textcopyleft"             0)     ; Type: Symbol -- Slot: 171
    '("textlnot"                 0)     ; Type: Symbol -- Slot: 172
    '("textcircledP"             0)     ; Type: Symbol -- Slot: 173
    '("textregistered"           0)     ; Type: Symbol -- Slot: 174
    '("textasciimacron"          0)     ; Type: Symbol -- Slot: 175
    '("textdegree"               0)     ; Type: Symbol -- Slot: 176
    '("textpm"                   0)     ; Type: Symbol -- Slot: 177
    '("texttwosuperior"          0)     ; Type: Symbol -- Slot: 178
    '("textthreesuperior"        0)     ; Type: Symbol -- Slot: 179
    '("textasciiacute"           0)     ; Type: Symbol -- Slot: 180
    '("textmu"                   0)     ; Type: Symbol -- Slot: 181
    '("textparagraph"            0)     ; Type: Symbol -- Slot: 182
    '("textperiodcentered"       0)     ; Type: Symbol -- Slot: 183
    '("textreferencemark"        0)     ; Type: Symbol -- Slot: 184
    '("textonesuperior"          0)     ; Type: Symbol -- Slot: 185
    '("textordmasculine"         0)     ; Type: Symbol -- Slot: 186
    '("textsurd"                 0)     ; Type: Symbol -- Slot: 187
    '("textonequarter"           0)     ; Type: Symbol -- Slot: 188
    '("textonehalf"              0)     ; Type: Symbol -- Slot: 189
    '("textthreequarters"        0)     ; Type: Symbol -- Slot: 190
    '("texteuro"                 0)     ; Type: Symbol -- Slot: 191
    '("texttimes"                0)     ; Type: Symbol -- Slot: 214
    '("textdiv"                  0)     ; Type: Symbol -- Slot: 246
    '("textcircled"              1)     ; Type: Command -- Slot: N/A
    '("capitalcedilla"           1)     ; Type: Command -- Slot: N/A
    '("capitalogonek"            1)))   ; Type: Command -- Slot: N/A
 LaTeX-dialect)

(defvar LaTeX-textcomp-package-options
  '("full" "almostfull" "euro" "safe" "force" "warn")
  "Package options for the textcomp package.")

;;; textcomp.el ends here
