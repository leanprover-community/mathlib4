getDecls () {
  sed 's="c:=\n=g' ".lake/build/lib/${1/%lean/ilean}" | sed '/null},$/{d}; s=".=='
}

(
  for fil in $(git diff --name-only master...HEAD)
  do
    if [ "${fil: -5}" == ".lean" ] && [ "${fil:0:7}" == "Mathlib" ];
    then
      printf "diff'inf .lake/build/lib/${fil/%lean/ilean}"$'\n\n'
#      sed 's="c:=\n=g' ".lake/build/lib/${fil/%lean/ilean}" | sed '/null},$/{d}; s=".=='
    fi
  done
)

fil=Mathlib//Data/Nat/Defs.lean
echo "${fil}"
sed 's="c:=\n=g' ".lake/build/lib/${fil/%lean/ilean}" |
  sed '
    s="usages".*"definition"==g
    s="module":"[^"]*".=\n=
    s=":{:=,=
    s=},$==
  ' |
  sed '
    /,null/d
    /{"version":.,"/d
  ' | tr -d '][' |
  awk -F, -v ti="'" -v fil="$fil" 'BEGIN{ tot=""; max=0 }{
    acc[$2+1]=$1
    if(max < $2+1) { max=$2+1 }
    tot=tot sprintf("  %s,%sp #%s\n", $2+1, $2+1, "$1")
  }END{
    print max
    printf("sed -n %s\n", ti)
    for(i=1; i<=max; i++) if(acc[i]) { gsub(ti, "`", acc[i]); printf("  %s,%sp #%s\n", i, i, acc[i]) }
#    print tot| "sort -t, -n"; close("sort -t, -n")
    printf("%s %s\n", ti, fil) }'

sed -n '

  1848,1848p #Nat.findGreatest_mono
  1853,1853p #Nat.findGreatest_is_greatest
  1857,1857p #Nat.findGreatest_of_ne_zero
  1871,1871p #Nat.decidableLoHi
  1880,1880p #Nat.decidableLoHiLe
' Mathlib//Data/Nat/Defs.lean
