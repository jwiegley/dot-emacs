cat Emacs.Duplicate >> haskell-refac.el
sed  -e 's/"Transform Duplicate Code" haskell-refac-refacDupTrans/"Transform Duplicate Code" haskell-refac-goDup/' haskell-refac.el > haskell-refac.el2
sed -e 's/\["Identify Class" haskell-refac-refacIdentify  :active t\]//' haskell-refac.el2 > haskell-refac.el

