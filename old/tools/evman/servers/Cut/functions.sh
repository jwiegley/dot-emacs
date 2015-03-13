
## Compute the sequent that results from cut elimination
cut() {
  leftpath="$1"
  rightpath="$2"
  leftmod="${leftpath%%/*}"
  #rightmod="${rightpath%%/*}"

  pivot="$leftmod.`getcertattr conc "$leftpath"`"

  conc="`getcertattr conc "$rightpath"`"
  hyp=`(listcertattr hyp "$leftpath";listcertattr hyp "$rightpath")| sort -u | fgrep -wv "$pivot"`
  # Returns $conc, $hyp and $pivot
}
