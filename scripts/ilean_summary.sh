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

fil=Mathlib/Data/Nat/Defs.lean
genSumm (){
#  echo "${fil}"
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
    awk -F, -v ti="'" -v fil="$fil" -v pm="+" 'BEGIN{ tot=""; max=0 }{
      acc[$2+1]=$1
      if(max < $2+1) { max=$2+1 }
      tot=tot sprintf("  %s,%sp #%s\n", $2+1, $2+1, "$1")
    }END{
      print max
      printf("sed -n %s\n", ti)
      for(i=1; i<=max; i++) if(acc[i]) {
        gsub(ti, "£", acc[i])
        printf("  %s,%s{s=\(.*\)=|%s:%s|%s|%s|\\1|=p}\n", i, i, fil, i, pm, acc[i]) }
  #    print tot| "sort -t, -n"; close("sort -t, -n")
      printf("%s %s\n", ti, fil) }'
}

genSumm
(
  printf "|File|+-|Declaration|Code|\n|-|-|-|-|\n"
eval "$(genSumm)" |
  sed "s=£='=g" |
  sed 's=|\([^|]*\)|\([^|]*\)|$=|`\1`|`\2`|='
) > sa.md
