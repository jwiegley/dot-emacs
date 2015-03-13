module ListCompIn3 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove the defintion 'xs'. The bar will also be removed.

main = sum [ 4 | let xs=[1,3]]
                      

