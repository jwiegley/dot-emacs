[![Build Status](https://travis-ci.org/abo-abo/tiny.svg?branch=master)](https://travis-ci.org/abo-abo/tiny)
[![Coverage Status](https://coveralls.io/repos/abo-abo/tiny/badge.svg?branch=master)](https://coveralls.io/r/abo-abo/tiny?branch=master)

### Main idea:

This is an alternative to inserting numeric ranges with macros (i.e. `F3 F3`).
The advantages are:

1. Brevity: consider `F3 F3 SPC M-1 M-0 F4` vs. `m10 C-;`.
2. Much better undo context: a single `C-_` will undo the whole thing
   and allow you to edit the code. With macros you'd have to undo multiple
   times and restart from scratch, instead of tweaking what you just invoked.
3. The ability to insert the same number several times in a single iteration,
   and transform it with `format`-style expressions
   e.g. `m6\n15%s=0%o=0x%x` will expand to

        6=06=0x6
        7=07=0x7
        8=010=0x8
        9=011=0x9
        10=012=0xa
        11=013=0xb
        12=014=0xc
        13=015=0xd
        14=016=0xe
        15=017=0xf
4. Last but not least, the ability to transform the number with lisp expressions.
   For instance:
    1. `m5 10*xx` -> `25 36 49 64 81 100`
    2. `m5 10*xx|0x%x` -> `0x19 0x24 0x31 0x40 0x51 0x64`
    3. `m10+x?a%c` -> `a b c d e f g h i j k`
    4. `m10+x?A%c` -> `A B C D E F G H I J K`
    5. `m97,105stringx` -> `a,b,c,d,e,f,g,h,i`
    6. `m97,102stringxupcasex` -> `aA,bB,cC,dD,eE,fF`
    7. `m,3|%(+ x x) and %(* x x) and %s` -> `0 and 0 and 0,2 and 1 and 1,4 and 4 and 2,6 and 9 and 3,8 and 16 and 4,10 and 25 and 5`

### Use in conjunction with `org-mode`:

    m1\n14|*** TODO http://emacsrocks.com/e%02d.html

    *** TODO http://emacsrocks.com/e01.html
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
    *** TODO http://emacsrocks.com/e14.html

You can even schedule and deadline:

    m\n8|**** TODO Learning from Data Week %(+ x 2) \nSCHEDULED: <%(date "Oct 7" (* x 7))> DEADLINE: <%(date "Oct 14" (* x 7))>

    **** TODO Learning from Data Week 2
    SCHEDULED: <2013-10-07 Mon> DEADLINE: <2013-10-14 Mon>
    **** TODO Learning from Data Week 3
    SCHEDULED: <2013-10-14 Mon> DEADLINE: <2013-10-21 Mon>
    **** TODO Learning from Data Week 4
    SCHEDULED: <2013-10-21 Mon> DEADLINE: <2013-10-28 Mon>
    **** TODO Learning from Data Week 5
    SCHEDULED: <2013-10-28 Mon> DEADLINE: <2013-11-04 Mon>
    **** TODO Learning from Data Week 6
    SCHEDULED: <2013-11-04 Mon> DEADLINE: <2013-11-11 Mon>
    **** TODO Learning from Data Week 7
    SCHEDULED: <2013-11-11 Mon> DEADLINE: <2013-11-18 Mon>
    **** TODO Learning from Data Week 8
    SCHEDULED: <2013-11-18 Mon> DEADLINE: <2013-11-25 Mon>
    **** TODO Learning from Data Week 9
    SCHEDULED: <2013-11-25 Mon> DEADLINE: <2013-12-02 Mon>
    **** TODO Learning from Data Week 10
    SCHEDULED: <2013-12-02 Mon> DEADLINE: <2013-12-09 Mon>

Here's how to schedule a task that repeats Monday through Friday at 10:00, every week:

    m0\n4|** TODO Something work-related\nSCHEDULED: <%(date "mon" x) 10:00 +1w>

    ** TODO Something work-related
    SCHEDULED: <2013-11-04 Mon 10:00 +1w>
    ** TODO Something work-related
    SCHEDULED: <2013-11-05 Tue 10:00 +1w>
    ** TODO Something work-related
    SCHEDULED: <2013-11-06 Wed 10:00 +1w>
    ** TODO Something work-related
    SCHEDULED: <2013-11-07 Thu 10:00 +1w>
    ** TODO Something work-related
    SCHEDULED: <2013-11-08 Fri 10:00 +1w>

### Setup
In `~/.emacs`:

    (require 'tiny)
    (tiny-setup-default)
