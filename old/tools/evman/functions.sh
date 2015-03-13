
### Functions for use in shell scripts #########################################

errmsg() {
  echo >&2 "$*"
}

warning() {
  echo >&2 "Warning: $*"
}

abort() {
  errmsg "$*"
  exit 1
}

# Reading certificate/server attributes:
getattr() {
  egrep "^$1:" <"$2" | sed "s%^[a-zA-Z/._]*: *%%"
}

getcertattr() {
  getattr $1 "$certsDir$2/cert.attr"
}

listcertattr() {
  for w in `getcertattr "$1" "$2"` ; do
    echo $w
  done
}

getserverattr() {
  getattr "$1" "$SERVERDIR/server.attr"
}

setattr() {
  grep -v "^$1:" <"$3" | { cat ; echo "$1: $2" ; } >"$3.new"
  mv "$3.new" "$3"
}

certauxfiles() {
  attrs="$1/cert.attr"
  echo "$certsDir$attrs"
  getattr "file(/[a-z]*)?" "$attrs"
}

certfiles() {
  certauxfiles "$1"
  cat "$1/srclist.txt"
}

# Check that a module exists:
checkmodule() {
  pfe pragmas "$1" >/dev/null || { echo "$1"; exit 1; }
}

# Check that a project exists:
checkproject() {
  [ -d hi ] ||
    abort "No pfe project in this directory. (Use pfesetup or pfe new.)"

  if pfeclient >/dev/null  2>&1 ; then
    pfe() {
     pfeclient "$@"
    }
  elif [ "$WARNSLOW" != "no" ] ; then
    warning "PFE server not found. Things can get slow..."
    WARNSLOW=no
    export WARNSLOW
  fi
}

# Check that a certificate exists and set $attr:
checkcert() {
  attr="$certsDir$1/cert.attr"
  [ -r "$attr" ] ||
    abort "Didn't find certificate $1. (Use 'cert new' to create certificates.)"
}

checkassertion() {
  m="${1%.*}"
  a="${1##*.}"
  # Check that the argument is a qualified name and that the assertion exists.
  [ "$a" != "$1" ] && pfe assertions "$m" | grep -q "^$m $a\$"
}

checkcertannot() {
  checkmodule "$1"
  pfe pragmas "$1" | grep -q "cert:$2" || {
    warning "found no certiticate annotation for $2 in $1."
  }
}

# List of modules that a specified modules depends on
subgraph() {
  pfe modules $* | tail +2
}

# The list of source files that a specified module depends on
subgraphfiles() {
  pfe file `subgraph $*` | sed 's/^.*: //'
}

# Create a datestamp file when a certificate is marked valid/invalid
# Also save the list of source files that the certificate depends on
datestamp() {
  valid="${1-valid}"
  certpath=$2 # the path of a certificate directory
  module=$3 # the name of the module containing the certificate
  echo -n "Certificate marked $valid on "
  date | tee "$certpath/$valid"
  subgraphfiles $module >$certpath/srclist.txt
}

outofdate() {
  srcs="$1/srclist.txt"
  attrs="$1/cert.attr"
  datestamp="$2"
  if [ -r "$srcs" ] && [ -r "$attrs" ] ; then
    certfiles "$1" |
    while read path ; do
      # Grr. ../../ below is to reverse the effect of cd $certsDir in lscert
      if [ "../../$path" -nt "$datestamp" ] ; then
        echo '?'
	break
      fi
    done
  else
    echo '??'
  fi
}

quickvalidate() {
  # A quick (unreliable) test if a certificate is valid
  certpath="$1"
  valid="$certpath/valid"
  invalid="$certpath/invalid"
  if [ -f "$valid" ] ; then
    if [ -f "$invalid" ] && [ "$invalid" -nt "$valid" ] ; then
      echo Invalid`outofdate $certpath $invalid`
    else
      echo Valid`outofdate $certpath $valid`
    fi
  elif [ -f "$invalid" ] ; then
   echo Invalid`outofdate $certpath $invalid`
  else 
   echo New
  fi
}

# Ask the user to confirm somthing (answer a yes-or-no question)
user_confirmation() {
  tty -s || echo >&2 "+-+ Yes No" # For pfebrowser
  read ans
  case "$ans" in
    [Yy]es) true ;;
    *) false
  esac
}
