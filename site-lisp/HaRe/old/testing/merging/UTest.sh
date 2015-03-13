#!/bin/sh

TESTING_DIR="$(pwd)"
#cd ..
#./UTest.sh $TESTING_DIR

BASH="bash"
HARE="../../dist/build/hare/hare"

runTest () {
   echo "-- testing $1"
   cd $1 &&
   ./UTestMerging $BASH $HARE 2>&1 | tee log.txt &&
   rm -r hi
   cd ..
}

ghc --make -o UTestMerging UTestMerging.hs
rm *.o *.hi

# avoid spurious error reports due to line-ending conventions..
case `uname` in
  CYGWIN*)
    unix2dos */*.hs */*/*.hs
    ;;
esac

runTest $TESTING_DIR

