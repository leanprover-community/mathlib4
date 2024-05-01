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
  awk -F, -v ti="'" -v fil="$fil" '{
    printf("sed -n %s%s,%sp%s %s #%s\n", ti, $2+1, $2+1, ti, fil, $1)
  }'

sed -n '104,104p' $fil
sed -n '309,309p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_two_iff
sed -n '313,313p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_three_iff
sed -n '286,286p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_right
sed -n '305,305p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_one_iff
sed -n '295,295p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_min_iff
sed -n '294,294p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_max_iff
sed -n '285,285p' Mathlib//Data/Nat/Defs.lean #Nat.add_eq_left
sed -n '281,281p' Mathlib//Data/Nat/Defs.lean #Nat.add_def
sed -n '104,104p' Mathlib//Data/Nat/Defs.lean #LT.lt.nat_succ_le
