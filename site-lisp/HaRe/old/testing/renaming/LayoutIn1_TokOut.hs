module LayoutIn1 where

--Layout rule applies after 'where','let','do' and 'of'

--In this Example: rename 'sq' to 'square'.

sumSquares x y= square x + square y where square x= x^pow
  --There is a comment.
                                          pow=2
