#!/bin/bash

defaultPROGRAMATICA="/home/project/pacsoft/tools/lib/Programatica"
PROGRAMATICA="${PROGRAMATICA-$defaultPROGRAMATICA}"

###
# Should agree with the corresponding definitions in property/pfe/PFE_Certs.hs:
certsDir=hi/cert/ # Also change function outofdate below if you change this!
certTypesDir="$PROGRAMATICA/types/certificate/"
export PROGRAMATICA certsDir certTypesDir

. "$PROGRAMATICA/functions.sh"

types() {
  cd "$certTypesDir"
  fmt="%-11.11s %-5.5s %-16s\n"
  l="----------------"
  printf "$fmt" Type Ver Description
  printf "$fmt" $l $l $l
  for type in * ; do
    attrs="$type/server.attr"
    if [ -r "$type/server.attr" ] ; then
      desc="`getattr description "$attrs"`"
      ver="`getattr version "$attrs"`"
      printf "$fmt" "$type" "$ver" "$desc"
    fi
  done
}

assertions() {
  #find . -name assert.txt | sed -e 's%^./%%' -e 's%/assert.txt$%%' | sort -u
  pfe assertions "$@" | sed 's% %/%' | sort -u
}


todo() {
  checkproject
  #pfe certscan && cd "$certsDir" || abort "Something went wrong."
  
  certified() {
    [ -d "$certsDir" ] && cd "$certsDir" && grep ^conc: `find . -name cert.attr` /dev/null |
      sed -e 's%^./%%' -e 's%[^/]*/cert.attr:conc: %%' | sort -u
  }

  diff <(certified) <(assertions "$@") | grep '^> '
}

no_certs()
{
  errmsg "Found no certificates. Try 'cert todo'."
  exit 0
}

lscert() {
  checkproject
  cd "$certsDir" 2>/dev/null || no_certs
  fmt="%-16.16s %-16.16s %-10.10s %-8.8s %-18s\n"
  l="--------------------------"
  printf "$fmt" Module Certificate Type Status Assertion
  printf "$fmt" $l $l $l $l $l
  find . -name cert.attr | while read certattrs; do
    echo "$certattrs" | {
      IFS=/ read dot module name rest
      type=`getattr type "$certattrs"`
      conc=`getattr conc "$certattrs"`
      hyp=`getattr hyp "$certattrs"`
      valid="`quickvalidate $module/$name`"
      printf "$fmt" "$module" "$name" "${type-?}" "$valid" "$hyp|-${conc--}"
    }
  done
}

dotgraph() {
  checkproject
  cd "$certsDir" 2>/dev/null || no_certs
  echo "digraph CertGraph {"
  find . -name cert.attr | while read certattrs; do
    echo "$certattrs" | {
      IFS=/ read dot module name rest
      conc=`getattr conc "$certattrs"`
      hyp=`getattr hyp "$certattrs"`
      echo "\"$conc\"->{"
      for h in $hyp ; do
        echo -n "\"$h\"; "
      done
      echo "}"
    }
  done
  echo "}"
}

info() {
  cert="$1"
  [ -n "$cert" ] || abort "Usage: cert info <cert>"
  checkproject
  checkcert "$cert" # sets $attr
  type=`getattr type "$attr"`
  infocmd="$certTypesDir$type/info"
  if [ -x "$infocmd" ] ; then
    "$infocmd" "$attr"
  else
    echo "Generic certificate info:"
    cat "$attr"
    certpath="$certsDir$cert"
    status=`cd $certsDir && quickvalidate $cert`
    echo "Status: $status (use 'cert validate' to be certain)"
    case "$status" in
      Valid*) echo "Last validated: `cat $certpath/valid`" ;;
      Invalid*) echo "Marked invalid on: `cat $certpath/invalid`" ;;
    esac
    #echo Files: `certsDir="" certfiles $certpath` # Can be very long!
  fi
}

rmcert() {
  checkproject
  for cert2 in "$@" ; do
    echo "$cert2" | {
      IFS=/. read module certname bla
      certpath="$certsDir$module/$certname"
      if [ -d "$certpath" ] ; then
	checkmodule "$module" && {
	  pfe pragmas "$module" | grep -q "cert:$certname" &&
	    warning "certiticate annotation still present for $certname in $module."
	  rm -r "$certpath"
	}
      else
        warning "$module/$certname does not seem to exists."
      fi
    }
  done
}

sign() {
  [ -n "$1" ] || abort "Usage: cert sign <cert>"
  checkproject
  certpath="$certsDir$1"
  checkcert "$1" # Sets $attr
  sig="$certpath/cert.attr.sig"
  [ -f "$sig" ] && abort "$1 is already signed."
  gpg -b -a <"$attr" -o "$sig"
}

verify() {
  [ -n "$1" ] || abort "Usage: cert verify <cert>"
  checkproject
  certpath="$certsDir$1"
  checkcert "$1" # Sets  $attr
  sig="$certpath/cert.attr.sig"
  [ -r "$sig" ] || abort  "Didn't find signature for certificate $1"
  gpg --verify "$sig" "$attr"
}

check_certtype() {
  dir="$certTypesDir$1/"
  [ -r "${dir}server.attr" ] ||
    abort "cert $cmd: unknown certificate type: $type"
}

delegate_type() {
  cmd="$1";type="$2"
  [ -n "$type" ] || abort "Usage: cert $cmd <type> ..."
  check_certtype "$type" # sets $dir
  cmdpath="${dir}${cmd}"
  [ -x "$cmdpath" ] || abort "cert $cmd: command not supported by type $type"
  shift;shift
  SERVERDIR="$dir"
  export SERVERDIR
  "$cmdpath" "$@"
}

delegate_cert() {
  cmd="$1"; cert="$2"
  [ -n "$cert" ] || abort "Usage: cert $1 <cert>"
  checkproject
  certpath="$certsDir$cert"
  checkcert "$cert" # Sets $attr
  type=`getattr type "$attr"`
  shift
  delegate_type "$cmd" "$type" "$@"
}

certnames() {
  ( cd "$certsDir" 2>/dev/null || no_certs &&
  find . -name cert.attr ) | while IFS=/ read dot module name rest; do
    echo "$module/$name"
  done
}

validate_all() {
  checkproject
  for cert in `certnames` ; do
    echo "*** $cert"
    delegate_cert validate "$cert"
  done
}

validate() {
  case "$2" in
    -all) validate_all ;;
    *) delegate_cert "$@"
  esac
}

new_all() {
  checkproject
  type="$1" ; shift
  check_certtype "$type" # sets $dir
  attrs="${dir}server.attr"
  case "`getattr has_sequent "$attrs"`" in
    no) abort "'cert new -all' is not implemented for $type certificates."
  esac
  abbr="`getattr abbrev ${dir}/server.attr`"
  [ -n "$abbr" ] || abbr="$type"
  #echo "new_all type=$type $@"
  pfe assertions "$@" | while read module conc ; do
    delegate_type new "$type" "$module/$abbr$conc" "$conc"
  done
}

new() {
  case "$2" in
    -all) shift; shift ; new_all "$@" ;;
    *) delegate_type "$@"
  esac
}

recreate() {
  checkproject
  for cert in `certnames` ; do
    checkcert "$cert" # Sets $attr
    c=$certsDir$cert/cert.attr
    type=`getattr type $c`
    conc=`getattr conc $c`
    hyp=`getattr hyp $c`
    [ "$hyp" = ".." ] && hyp=""
    echo "cert new $type $cert $conc $hyp"
  done
}

setcertattr() {
  checkproject
  cert="$1"
  attrname="$2"
  attrval="$3"
  [ -n "$cert" ] && [ -n "$attrname" ] && [ -n "$attrval" ] ||
    abort "Usage: cert setattr <cert> <attr> <value>"
  checkcert "$cert" # Sets $attr
  setattr "$attrname" "$attrval" "$attr"
}

usage() {
  abort "Usage: cert types|ls|dotgraph|todo|new|info|validate|sign|verify|rm|recreate|setattr ..."
}

case "${1-help}" in
  types) types ;;
  todo) shift; todo "$@" ;;
  ls) lscert ;;
  dotgraph) dotgraph ;;
  new) new "$@" ;;
  info) shift; info "$@" ;;
  validate) validate "$@" ;;
  rm) shift; rmcert "$@" ;;
  recreate) recreate ;;
  sign) shift; sign "$@" ;;
  verify) shift; verify "$@" ;;
  setattr) shift; setcertattr "$@" ;;
  *) usage
esac
