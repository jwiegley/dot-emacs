module IdIn5 where

{-To rename an identifier name, stop the cursor at any occurrence of the name,
  then input the new name in the mini-buffer, after that, select the 'rename'
  command from the 'Refactor' menu.-}

--Any value variable name declared in this module can  be renamed.

--Rename top level 'x' to 'y' will fail.
x=5

foo=x+3

bar z=x+y+z
    where y=3

main=(foo,bar x, foo)
