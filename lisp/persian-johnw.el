(require 'quail)

(quail-define-package
 "farsi-transliterate-johnw" "Farsi" "ج" t
 "My intuitive transliteration keyboard layout for Persian/Farsi.
" nil t t t t nil nil nil nil nil t)

(quail-define-rules
;;;;;;;;;;;  isiri-6219 Table 5 -- جدول ۵ - حروِفِ اصلیِ فارسی 
 ("~"  ?ء)        ;; hamzeh
 ("A"  ?آ)        ;; U+0622   & ARABIC LETTER ALEF WITH MADDA ABOVE & الف با  کلاه
 ("a"  ?ا)        ;; U+0627   & ARABIC LETTER ALEF  & الف
 ("\\a" ?أ)
 ("b"  ?ب)        ;; U+0628   & ARABIC LETTER BEH  &
 ("p"  ?پ)        ;; U+067e   & ARABIC LETTER PEH  &
 ("t"  ?ت)
 ("tt"  ?ت)
 ("c"  ?ث)
 ("cc"  ?ث)
 ("j"  ?ج)
 ("ch" ?چ)
 ("h"  ?ه)
 ("kh" ?خ)
 ("d"  ?د)
 ("dh"  ?ذ)
 ("r"  ?ر)
 ("z"  ?ز)
 ("zz"  ?ز)
 ("zh" ?ژ)
 ("s"  ?س)
 ("ss"  ?س)
 ("sh" ?ش)
 ("-" ?ش)
 ("S"  ?ص)
 ("D"  ?ض)
 ("T"  ?ط)
 ("TT"  ?ط)
 ("Z"  ?ظ)
 ("`"  ?ع)
 ("Q"  ?غ)
 ("f"  ?ف)
 ("q"  ?ق)
 ("gh" ?غ)
 ("k"  ?ک)
 ("kk"  ?ک)
 ("g"  ?گ)
 ("gg"  ?گ)
 ("l"  ?ل)
 ("m"  ?م)
 ("n"  ?ن)
 ("v"  ?و)
 ("u"  ?و)
 ("V" ?ؤ)
 ("H"  ?ح)
 ("y"  ?ی)
 ("i"  ?ی)
 ("I" ?ئ)


;;;;;;;;;;;  isiri-6219 Table 6 -- جدول ۶ - حروِفِ  عربی 
 ("F" ?إ)
 ("D" ?\u0671)     ;; (ucs-insert #x0671)ٱ   named: حرفِ الفِ وصل
 ("K"  ?ك)         ;;  Arabic kaf
 ("Th" ?ة)         ;; ta marbuteh
 ("Y"  ?ي)
 ("YY"  ?ي)
 ("Yh"  ?ى)

;;;;;;;;;;;  isiri-6219 Table 4 -- جدول ۴ -  ارقام و علائم ریاضی
 ("0"  ?۰)
 ("1"  ?۱)
 ("2"  ?۲)
 ("3"  ?۳)
 ("4"  ?۴)
 ("5"  ?۵)
 ("6"  ?۶)
 ("7"  ?۷)
 ("8"  ?۸)
 ("9"  ?۹)

 ("\\/" ?\u066B)     ;; (ucs-insert #x066B)٫   named: ممیزِ فارسی
 ("\\," ?\u066C)     ;; (ucs-insert #x066C)٬   named: جداکننده‌ی هزارهای فارسی
 ("%" ?\u066A)       ;; (ucs-insert #x066A)٪   named: درصدِ فارسی
 ("+" ?\u002B)     ;; (ucs-insert #x002B)+   named: علامتِ به‌اضافه
 ("-" ?\u2212)     ;; (ucs-insert #x2212)−   named: علامتِ منها
 ("\\*" ?\u00D7)     ;; (ucs-insert #x00D7)×   named: علامتِ ضرب
 ("\\%" ?\u007F)    ;; (ucs-insert #x00F7)÷   named: علامتِ تقسیم
 ("<" ?\u003C)     ;; (ucs-insert #x003C)<   named: علامتِ کوچکتر  
 ("=" ?\u003D)     ;; (ucs-insert #x003D)=   named: علامتِ مساوی
 (">" ?\u003E)     ;; (ucs-insert #x003E)>   named: علامتِ بزرگتر


;;;;;;;;;;;  isiri-6219 Table 2 -- جدول ۲ -  علائم نقطه گذاریِ مشترک
 ;;; Space
 ("."  ?.)  ;;
 (":" ?\u003A)     ;; (ucs-insert #x003A):   named: 
 ("!" ?\u0021)     ;; (ucs-insert #x0021)!   named: 
 ("\\." ?\u2026)     ;; (ucs-insert #x2026)…   named: 
 ("\\-" ?\u2010)     ;; (ucs-insert #x2010)‐   named: 
 ("-" ?\u002D)     ;; (ucs-insert #x002D)-   named: 
 ("|" ?|)
 ;;("\\\\" ?\)
 ("//" ?/)
 ("*" ?\u002A)     ;; (ucs-insert #x002A)*   named: 
 ("(" ?\u0028)     ;; (ucs-insert #x0028)(   named: 
 (")" ?\u0029)     ;; (ucs-insert #x0029))   named: 
 ("[" ?\u005B)     ;; (ucs-insert #x005B)[   named: 
 ("[" ?\u005D)     ;; (ucs-insert #x005D)]   named: 
 ("{" ?\u007B)     ;; (ucs-insert #x007B){   named: 
 ("}" ?\u007D)     ;; (ucs-insert #x007D)}   named: 
 ("\\<" ?\u00AB)     ;; (ucs-insert #x00AB)«   named: 
 ("\\>" ?\u00BB)     ;; (ucs-insert #x00BB)»   named: 


;;;;;;;;;;;  isiri-6219 Table 3 -- جدول ۳ -  علائم نقطه گذاریِ فارسی
 ("," ?،)  ;; farsi
 (";"  ?؛)  ;;
 ("?"  ?؟)  ;; alamat soal
 ("_"  ?ـ)  ;;


;;;;;;;;;;;  isiri-6219 Table 1 -- جدول ۱ -  نویسه‌های کنترلی
 ;; LF
 ;; CR
 ("&zwnj;" ?\u200C) ;; (ucs-insert #x200C)‌   named: فاصله‌ی مجازی
 ("/" ?\u200C)      ;; 
 ("&zwj;" ?\u200D)  ;; (ucs-insert #x200D)‍   named: اتصالِ مجازی
 ("J" ?\u200D)      ;; 
 ("&lrm;" ?\u200E)  ;; (ucs-insert #x200E)‎   named: نشانه‌ی چپ‌به‌راست
 ("&rlm;" ?\u200F)  ;; (ucs-insert #x200F)‏   named: نشانه‌ی راست‌به‌چپ
 ("&ls;" ?\u2028)   ;; (ucs-insert #x2028)    named: جداکننده‌ی سطرها
 ("&ps;" ?\u2028)   ;; (ucs-insert #x2029)    named: جداکننده‌ی بندها
 ("&lre;" ?\u202A)   ;; (ucs-insert #x202A)‪   named: زیرمتنِ چپ‌به‌راست
 ("&rle;" ?\u202B)   ;; (ucs-insert #x202B)   named: زیرمتنِ راست‌به‌چپ
 ("&pdf;" ?\u202C)   ;; (ucs-insert #x202C)   named: پایانِ زیرمتن
 ("&lro;" ?\u202D)   ;; (ucs-insert #x202D)   named: زیرمتنِ اکیداً چپ‌به‌راست
 ("&rlo;" ?\u202D)   ;; (ucs-insert #x202E)   named: زیرمتنِ اکیداً راست‌به‌چپ
 ("&bom;" ?\uFEFF)   ;; (ucs-insert #xFEFF)   named: نشانه‌ی ترتیبِ بایت‌ها
 

;;;;;;;;;;;  isiri-6219 Table 7 -- جدول ۷ -  نشانه‌هایِ فارسی
 ("'"  ?َ)  ;; zbar ;; زبر فارسى
 ("e"  ?ِ)  ;; zir   زير فارسى
 ("o"  ?ُ)  ;; peesh ;; پيش فارسى -- ضمه
 ("E"  ?ٍ)  ;; eizan ;; دو زير فارسى -- تنوين جر
 ("#"  ?ً)  ;; دو زبر
 ("O" ?ٌ)  ;; دو پيش فارسى -- تنوين رفع
 ("w"  ?ّ)  ;; tashdid ;;  تشديد فارسى
 ("W" ?ْ)   ;; ساکن فارسى
 ("U" ?\u0653)  ;; (ucs-insert #x0653)ٓ   named: مدِ فارسی
 ;;("`" ?ٔ)  ;; همزه فارسى بالا
 ("C" ?\u0655)  ;; (ucs-insert #x0655)ٕ   named: همزه فارسى پایین 
 ("$" ?\u0670)  ;; (ucs-insert #x0670)ٰ   named: الفِ مقصوره‌ی فارسی


;;;;;;;;;;;  isiri-6219 Table 8 - Forbidden Characters -- جدول ۸ - نویسه‌هایِ ممنوع
;;  ;; he ye (ucs-insert 1728) kills emacs-24.0.90
;; arabic digits 0-9


;;;;;;;  Latin Extensions
 ("\\" ?\\)  ;; خط اريب وارو
 ("\\\\" ?\\)
 ("\\~" ?~)
 ("\\@" ?@)
 ("\\#" ?#)
 ("\\$" ?\uFDFC)  ;; (ucs-insert #xFDFC)﷼   named: 
 ("\\^" ?^)
 ("\\1" ?1)
 ("\\2" ?2)
 ("\\3" ?3)
 ("\\4" ?4)
 ("\\5" ?5)
 ("\\6" ?6)
 ("\\7" ?7)
 ("\\8" ?8)
 ("\\9" ?9)
 ("\\0" ?0)

)

(provide 'persian-johnw)
