#!/usr/bin/env bash

# setup

REPO=$1
PACKAGE=org-trello
CLEAN_INSTALL_FOLDER=$HOME/$PACKAGE-install-$REPO
EMACS_EXECUTE_FILE=test-install-package.el

# prepare

rm -rf $CLEAN_INSTALL_FOLDER
mkdir -p $CLEAN_INSTALL_FOLDER
cp $EMACS_EXECUTE_FILE $CLEAN_INSTALL_FOLDER
cd $CLEAN_INSTALL_FOLDER

# execute
HOME=$CLEAN_INSTALL_FOLDER cask emacs -Q --batch -l $EMACS_EXECUTE_FILE -- $REPO
