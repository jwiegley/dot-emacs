
now="${1-Now.hs}"
new="$now.new"
{
echo "module Now where"
echo "{-# NOINLINE compileDate #-}"
echo 'compileDate = "'`date +%Y-%m-%d`'"'
#echo 'compileTime = "'`date +%T`'"'
} > "$new"
if cmp "$now" "$new"; then
 : #  echo Same date
else
  cat "$new" >"$now"
fi
rm "$new"
