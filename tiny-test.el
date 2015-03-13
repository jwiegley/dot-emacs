(when (require 'undercover nil t)
  (undercover "tiny.el"))

(require 'tiny nil t)

(defun with-text-value (txt fn &rest args)
  "Return the result of (apply 'FN ARGS), in a temp buffer with TXT,
with point at the end of TXT."
  (with-temp-buffer
    (insert txt)
    (apply fn args)))

(ert-deftest tiny-mapconcat-parse ()
  (should (equal (with-text-value "m10" #'tiny-mapconcat-parse)
                 '(nil nil "10" nil nil)))
  (should (equal (with-text-value "m5%x" #'tiny-mapconcat-parse)
                 '(nil nil "5" nil "%x")))
  (should (equal (with-text-value "m5 10" #'tiny-mapconcat-parse)
                 '("5" " " "10" nil nil)))
  (should (equal (with-text-value "m5,10" #'tiny-mapconcat-parse)
                 '("5" "," "10" nil nil)))
  (should (equal (with-text-value "m5 10*xx" #'tiny-mapconcat-parse)
                 '("5" " " "10" "(* x x)" nil)))
  (should (equal (with-text-value "m5 10*xx%x" #'tiny-mapconcat-parse)
                 '("5" " " "10" "(* x x)" "%x")))
  (should (equal (with-text-value "m5 10*xx|0x%x" #'tiny-mapconcat-parse)
                 '("5" " " "10" "(* x x)" "0x%x")))
  (should (equal (with-text-value "m25+x?a%c" #'tiny-mapconcat-parse)
                 '(nil nil "25" "(+ x 97)" "%c")))
  (should (equal (with-text-value "m25+x?A%c" #'tiny-mapconcat-parse)
                 '(nil nil "25" "(+ x 65)" "%c")))
  (should (equal (with-text-value "m97,122stringx" #'tiny-mapconcat-parse)
                 '("97" "," "122" "(string x)" nil)))
  (should (equal (with-text-value "m97,122stringxx" #'tiny-mapconcat-parse)
                 '("97" "," "122" "(string x x)" nil)))
  (should (equal (with-text-value "m97,120stringxupcasex" #'tiny-mapconcat-parse)
                 '("97" "," "120" "(string x (upcase x))" nil)))
  (should (equal (with-text-value "m97,120stringxupcasex)x" #'tiny-mapconcat-parse)
                 '("97" "," "120" "(string x (upcase x) x)" nil)))
  (should (equal (with-text-value "m\\n;; 10|%(+ x x) and %(* x x) and %s" #'tiny-mapconcat-parse)
                 '(nil "\\n;; " "10" nil "%(+ x x) and %(* x x) and %s")))
  (should (equal (with-text-value "m10|%0.2f" #'tiny-mapconcat-parse)
                 '(nil nil "10" nil "%0.2f"))))

(ert-deftest tiny-extract-sexps ()
  (should (equal (tiny-extract-sexps "expr1 %(+ x x), nothing %%  char %c, hex %x, and expr2 %(* x x), float %0.2f and sym %s")
                 '("expr1 %s, nothing %%  char %c, hex %x, and expr2 %s, float %0.2f and sym %s"
                   "(+ x x)" nil nil "(* x x)" nil nil)))
  (should (equal (tiny-extract-sexps "m1\n5| (%c(+ x ?a -1)) %0.1f(* x 0.2)")
                 '("m1
5| (%c) %0.1f" "(+ x ?a -1)" "(* x 0.2)"))))

(ert-deftest tiny-mapconcat ()
  (should (equal (with-text-value "m10" (lambda()(eval (read (tiny-mapconcat)))))
                 "0 1 2 3 4 5 6 7 8 9 10"))
  (should (equal (with-text-value "m5 10" (lambda()(eval (read (tiny-mapconcat)))))
                 "5 6 7 8 9 10"))
  (should (equal (with-text-value "m5 10*xx" (lambda()(eval (read (tiny-mapconcat)))))
                 "25 36 49 64 81 100"))
  (should (equal (with-text-value "m5 10*xx%x" (lambda()(eval (read (tiny-mapconcat)))))
                 "19 24 31 40 51 64"))
  (should (equal (with-text-value "m5 10*xx|0x%x" (lambda()(eval (read (tiny-mapconcat)))))
                 "0x19 0x24 0x31 0x40 0x51 0x64"))
  (should (equal (with-text-value "m25+x?a%c" (lambda()(eval (read (tiny-mapconcat)))))
                 "a b c d e f g h i j k l m n o p q r s t u v w x y z"))
  (should (equal (with-text-value "m25+x?A%c" (lambda()(eval (read (tiny-mapconcat)))))
                 "A B C D E F G H I J K L M N O P Q R S T U V W X Y Z"))
  (should (equal (with-text-value "m97,122(string x)" (lambda()(eval (read (tiny-mapconcat)))))
                 "a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z"))
  (should (equal (with-text-value "m97,122stringxx" (lambda()(eval (read (tiny-mapconcat)))))
                 "aa,bb,cc,dd,ee,ff,gg,hh,ii,jj,kk,ll,mm,nn,oo,pp,qq,rr,ss,tt,uu,vv,ww,xx,yy,zz"))
  (should (equal (with-text-value "m97,120stringxupcasex" (lambda()(eval (read (tiny-mapconcat)))))
                 "aA,bB,cC,dD,eE,fF,gG,hH,iI,jJ,kK,lL,mM,nN,oO,pP,qQ,rR,sS,tT,uU,vV,wW,xX"))
  (should (equal (with-text-value "m97,120stringxupcasex)x" (lambda()(eval (read (tiny-mapconcat)))))
                 "aAa,bBb,cCc,dDd,eEe,fFf,gGg,hHh,iIi,jJj,kKk,lLl,mMm,nNn,oOo,pPp,qQq,rRr,sSs,tTt,uUu,vVv,wWw,xXx"))
  (should (equal (with-text-value "m10|%(+ x x) and %(* x x) and %s" (lambda()(eval (read (tiny-mapconcat)))))
                 "0 and 0 and 0 2 and 1 and 1 4 and 4 and 2 6 and 9 and 3 8 and 16 and 4 10 and 25 and 5 12 and 36 and 6 14 and 49 and 7 16 and 64 and 8 18 and 81 and 9 20 and 100 and 10"))
  (should (equal (with-text-value "m10*2+3x" (lambda()(eval (read (tiny-mapconcat)))))
                 "6 8 10 12 14 16 18 20 22 24 26"))
  (should (equal (with-text-value "m10expx" (lambda()(eval (read (tiny-mapconcat)))))
                 "1.0 2.718281828459045 7.38905609893065 20.085536923187668 54.598150033144236 148.4131591025766 403.4287934927351 1096.6331584284585 2980.9579870417283 8103.083927575384 22026.465794806718"))
  (should (equal (with-text-value "m5 20expx%014.2f" (lambda()(eval (read (tiny-mapconcat)))))
                 "00000000148.41 00000000403.43 00000001096.63 00000002980.96 00000008103.08 00000022026.47 00000059874.14 00000162754.79 00000442413.39 00001202604.28 00003269017.37 00008886110.52 00024154952.75 00065659969.14 00178482300.96 00485165195.41"))
  (should (equal (with-text-value "m, 7|0x%02x" (lambda()(eval (read (tiny-mapconcat)))))
                 "0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07"))
  (should (equal (with-text-value "m1\\n14|*** TODO http://emacsrocks.com/e%02d.html" (lambda()(eval (read (tiny-mapconcat)))))
                 "*** TODO http://emacsrocks.com/e01.html
*** TODO http://emacsrocks.com/e02.html
*** TODO http://emacsrocks.com/e03.html
*** TODO http://emacsrocks.com/e04.html
*** TODO http://emacsrocks.com/e05.html
*** TODO http://emacsrocks.com/e06.html
*** TODO http://emacsrocks.com/e07.html
*** TODO http://emacsrocks.com/e08.html
*** TODO http://emacsrocks.com/e09.html
*** TODO http://emacsrocks.com/e10.html
*** TODO http://emacsrocks.com/e11.html
*** TODO http://emacsrocks.com/e12.html
*** TODO http://emacsrocks.com/e13.html
*** TODO http://emacsrocks.com/e14.html"))
  (should (equal (with-text-value "m1\\n10|convert img%s.jpg -monochrome -resize 50%% -rotate 180 img%s_mono.pdf" (lambda()(eval (read (tiny-mapconcat)))))
                 "convert img1.jpg -monochrome -resize 50% -rotate 180 img1_mono.pdf
convert img2.jpg -monochrome -resize 50% -rotate 180 img2_mono.pdf
convert img3.jpg -monochrome -resize 50% -rotate 180 img3_mono.pdf
convert img4.jpg -monochrome -resize 50% -rotate 180 img4_mono.pdf
convert img5.jpg -monochrome -resize 50% -rotate 180 img5_mono.pdf
convert img6.jpg -monochrome -resize 50% -rotate 180 img6_mono.pdf
convert img7.jpg -monochrome -resize 50% -rotate 180 img7_mono.pdf
convert img8.jpg -monochrome -resize 50% -rotate 180 img8_mono.pdf
convert img9.jpg -monochrome -resize 50% -rotate 180 img9_mono.pdf
convert img10.jpg -monochrome -resize 50% -rotate 180 img10_mono.pdf"))
  (should (equal (with-text-value "m\\n;; 16list*xxx)*xx%s:%s:%s" (lambda()(eval (read (tiny-mapconcat)))))
                 "0:0:0
;; 1:1:1
;; 8:4:2
;; 27:9:3
;; 64:16:4
;; 125:25:5
;; 216:36:6
;; 343:49:7
;; 512:64:8
;; 729:81:9
;; 1000:100:10
;; 1331:121:11
;; 1728:144:12
;; 2197:169:13
;; 2744:196:14
;; 3375:225:15
;; 4096:256:16"))
  (should (equal (with-text-value "m\\n8|**** TODO Learning from Data Week %(+ x 2)\\nSCHEDULED: <%(date \"Oct 7\" (* x 7))> DEADLINE: <%(date \"Oct 14\" (* x 7))>"
                   (lambda()(eval (read (tiny-mapconcat)))))
                 "**** TODO Learning from Data Week 2
SCHEDULED: <2015-10-07 Wed> DEADLINE: <2015-10-14 Wed>
**** TODO Learning from Data Week 3
SCHEDULED: <2015-10-14 Wed> DEADLINE: <2015-10-21 Wed>
**** TODO Learning from Data Week 4
SCHEDULED: <2015-10-21 Wed> DEADLINE: <2015-10-28 Wed>
**** TODO Learning from Data Week 5
SCHEDULED: <2015-10-28 Wed> DEADLINE: <2015-11-04 Wed>
**** TODO Learning from Data Week 6
SCHEDULED: <2015-11-04 Wed> DEADLINE: <2015-11-11 Wed>
**** TODO Learning from Data Week 7
SCHEDULED: <2015-11-11 Wed> DEADLINE: <2015-11-18 Wed>
**** TODO Learning from Data Week 8
SCHEDULED: <2015-11-18 Wed> DEADLINE: <2015-11-25 Wed>
**** TODO Learning from Data Week 9
SCHEDULED: <2015-11-25 Wed> DEADLINE: <2015-12-02 Wed>
**** TODO Learning from Data Week 10
SCHEDULED: <2015-12-02 Wed> DEADLINE: <2015-12-09 Wed>"))
  (should (string= (with-text-value "m\\n4|**** TODO Classical Mechanics Week %(+ x 5)\\nSCHEDULED: <%(date \"Oct 15\" (* x 7))> DEADLINE: <%(date \"Oct 23\" (* x 7))>"
                     (lambda()(eval (read (tiny-mapconcat)))))
                   "**** TODO Classical Mechanics Week 5
SCHEDULED: <2015-10-15 Thu> DEADLINE: <2015-10-23 Fri>
**** TODO Classical Mechanics Week 6
SCHEDULED: <2015-10-22 Thu> DEADLINE: <2015-10-30 Fri>
**** TODO Classical Mechanics Week 7
SCHEDULED: <2015-10-29 Thu> DEADLINE: <2015-11-06 Fri>
**** TODO Classical Mechanics Week 8
SCHEDULED: <2015-11-05 Thu> DEADLINE: <2015-11-13 Fri>
**** TODO Classical Mechanics Week 9
SCHEDULED: <2015-11-12 Thu> DEADLINE: <2015-11-20 Fri>"))
  (should (string= (with-text-value "m7|%(expt 2 x)"
                     (lambda()(eval (read (tiny-mapconcat)))))
                   "1 2 4 8 16 32 64 128"))
  (should (string= (with-text-value "m\\n25+?ax|(\"%c\")"
                     (lambda()(eval (read (tiny-mapconcat)))))
                   "(\"a\")\n(\"b\")\n(\"c\")\n(\"d\")\n(\"e\")\n(\"f\")\n(\"g\")\n(\"h\")\n(\"i\")\n(\"j\")\n(\"k\")\n(\"l\")\n(\"m\")\n(\"n\")\n(\"o\")\n(\"p\")\n(\"q\")\n(\"r\")\n(\"s\")\n(\"t\")\n(\"u\")\n(\"v\")\n(\"w\")\n(\"x\")\n(\"y\")\n(\"z\")")))

(ert-deftest tiny-replace-this-sexp ()
  (should (equal (with-text-value "(mapcar (lambda (x) (* x x)) '(1 2 3))"
                   (lambda()(goto-char 16)(tiny-replace-this-sexp)(buffer-string)))
                 "(1 4 9)"))
  (should (equal (with-text-value "(mapcar (lambda (x) (* x x)) '(1 2 3))"
                   (lambda()(goto-char 2)(tiny-replace-this-sexp)(buffer-string)))
                 "(1 4 9)")))

(ert-deftest tiny-tokenize ()
    (should (equal (tiny-tokenize "stringxx") "(string x x)"))
    (should (equal (tiny-tokenize "*2+xxx") "(* 2 (+ x x x))"))
    (should (equal (tiny-tokenize "*2+xxx") "(* 2 (+ x x x))"))
    (should (equal (tiny-tokenize "*2+xx)x") "(* 2 (+ x x) x)"))
    (should (equal (tiny-tokenize "string x") "(string x)"))
    (should (equal (tiny-tokenize "(string x)") "(string x)"))
    (should (equal (tiny-tokenize "string x)") "(string x)"))
    (should (equal (tiny-tokenize "stringxupcasex)x") "(string x (upcase x) x)"))
    (should (equal (tiny-tokenize "(stringxupcasex)x") "(string x (upcase x) x)"))
    (should (equal (tiny-tokenize "(string xupcasex)x") "(string x (upcase x) x)"))
    (should (equal (tiny-tokenize "(string x upcasex)x") "(string x (upcase x) x)"))
    (should (equal (tiny-tokenize "(string x upcase x) x") "(string x (upcase x) x)"))
    (should (equal (tiny-tokenize "(string x (upcase x) x") "(string x (upcase x) x)"))
    (should (equal (tiny-tokenize "(string x (upcase x) x)") "(string x (upcase x) x)")))

(provide 'tiny-test)
