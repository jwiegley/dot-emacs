
# Auxiliary functions for validation of certificates.

. "$PROGRAMATICA/functions.sh"


### Functions ##################################################################

trivialmarkvalid() {
 echo '[]' >"$deps" && datestamp valid $certpath $module
}

markvalid() {
  if pfe tasig "$assertion" >"$deps" 2>>"$output" ; then
    datestamp valid $certpath $module
  else
     echo "Validation succeeeded, but computing the dependency info failed."
     return 1
  fi
}

markinvalid() { datestamp invalid $certpath $module; }


### Initialization #############################################################
### Perform some sanity checks and define some useful variables:

[ -n "$certsDir" ] || abort 'Bug: $certsDir is not set'
[ -n "$1" ] || abort 'Bug: validate called without a certificate argument'

cert="$1"
module="${cert%/*}"
certpath="$certsDir$cert"

checkproject
checkcert "$cert" # Sets $attr
deps="$certpath/deps" # Name of file containting PFE dependency information
output="$certpath/output.txt" # Standard place for diagnostic output

case "${has_sequent-yes}" in
  yes)
    conc=`getattr conc "$attr"`
    assertion="$module.$conc"

    checkassertion "$module.$conc" || {
      abort "Did't find the assertion $conc in module $module"
    }
esac
