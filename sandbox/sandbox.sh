#!/usr/bin/env sh

# INIT_FILE=$USER_DIR/init.el
INIT_FILE=$(pwd)/init.el

PACKAGE_DIR=$USER_DIR/elpa
    
BASEDIR=$(pwd) #/sandbox

export USER_DIRECTORY=$BASEDIR 
export PACKAGE_DIR=$BASEDIR/elpa 
export DEFAULT_DIR=$(pwd) 
export ORG_WIKI_LOCATION=$BASEDIR/wiki

echo "USER_DIRECTORY = "$USER_DIRECTORY
echo "PACKAGE_DIR = "$PACKAGE_DIR


case $1 in
    run)
        emacs -Q -l init.el 
    ;;
    clean)
        rm -rf elpa/*
        ;;
    *)
        
esac


