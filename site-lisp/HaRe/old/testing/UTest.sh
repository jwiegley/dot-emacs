#!/bin/sh

# Run testcases of a HaRe testsuite.

# If an argument is provided, this has to be a valid directory containing testcases. Then only these tests will be run.
# If no argument is provided, all testcases as listed in the $DIRS variable will be executed.


#BASH="d:\\cygwin\\bin\\bash.exe"
BASH="bash"
#HARE="../../refactorer/pfe"
HARE="../../dist/build/hare/hare"
#HARE="..\\..\\refactorer\\pfe"

DIRS_OLD="asPatterns
      refacRedunDec
      refacSlicing
      typeSigs
      renaming
      demote
      liftOneLevel
      duplication
      liftToToplevel
      rmOneParameter
      addOneParameter
      introNewDef
      removeDef
      generaliseDef
      unfoldDef
      addToExport
      cleanImports
      fromConcreteToAbstract
      mkImpExplicit
      moveDefBtwMods
      rmFromExport
      pointwiseToPointfree
    "

DIRS="addCon
addField
addOneParameter
addToExport
asPatterns
cleanImports
demote
duplication
evalAddEvalMon
evalAddEvalMonCache
evalMonad
foldDef
foldPatterns
fromConcreteToAbstract
generaliseDef
generativeFold
instantiate
introCase
introNewDef
introPattern
introThreshold
letToWhere
liftOneLevel
liftToToplevel
merging
mkImpExplicit
moveDefBtwMods
pointwiseToPointfree
refacDataNewType
refacFunDef
refacRedunDec
refacSlicing
removeCon
removeDef
removeField
renaming
rmFromExport
rmOneParameter
simplifyExpr
subIntroPattern
unfoldAsPatterns
unfoldDef
whereToLet
"

runTest () {
   echo "-- testing $1"
   cd $1 &&
   ../UTest $BASH $HARE 2>&1 | tee log.txt &&
   rm -r hi
   cd ..
}

ghc --make -o UTest UTest.hs
rm *.o *.hi

# avoid spurious error reports due to line-ending conventions..
case `uname` in
  CYGWIN*)
    unix2dos */*.hs */*/*.hs
    ;;
esac

# check if arguemnt is provided
if [ -n "$1" ]; then
    runTest $1
else
    for d in $DIRS
    do
        runTest "$d"
    done
fi
