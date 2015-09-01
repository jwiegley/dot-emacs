#!/bin/bash

bin=/home/users/hallgren/cgi
. $bin/cgistart.sh

### Horizontal Tree
htree() {
  begin table
  begin caption; h4 "$1";end
  tr;
  ls -1 | while read dir ; do
    if [ -d "$dir" ] ; then
      case "$dir" in
	CVS|objs|junk|hi|tests) : ;;
	*) td; (cd "$dir"; htree "$dir")
      esac
    fi
  done
  end
}

### Vertical Tree
vtree() {
  begin table class=borderless
  tr; th "$2/"
  td
  begin table class=borderless
  tr;td;sed -n "s%^$1 \(.*\)\$%\1%p" <titles
  txt=README
  [ -r "$1/README.html" ] || txt="Files"
  link "$1/" "$txt" ; nl
  if [ $level -ge $maxlevel ] ; then
    link "tree.cgi?$1" more
  else
    ls -1 "$1" | while read node ; do
      dir="$1/$node"
      dir="${dir#./}" # remove ./ prefix
      if ! [ -h "$dir" ] && [ -d "$dir" ] && [ -d "$dir/CVS" ] ; then
	case "$node" in
	  CVS|tests|doc|spec|hsutils|toy|command) : ;;
	  *) tr;td;
	     level=$(($level+1)) vtree "$dir" "$node"
	esac
      fi
    done
  fi
  end
  end
}

maxlevel=6
level=1
pagestart "Directory Tree Overview"
vtree ${1-.} `basename "${1-$PWD}"`
endall
