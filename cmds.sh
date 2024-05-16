#git ls-files 'Mathlib/*.lean' | xargs cat | grep -v "^$" | wc

statsURL=""

hashAndDate="$(git log master --since='one week ago' --date=short --pretty="%h %ad" | tail -1)"

commit=${hashAndDate/% */}
date=${hashAndDate/#* /}

gdiff="$(git diff --shortstat "${commit}"...HEAD)"

percent="$(git diff --dirstat "${commit}"...HEAD)"

net=$(awk -v gd="${gdiff}" 'BEGIN{
  tot=0
  n=split(gd, gda, " ")
  for(i=2; i<=n; i++) {
    if(gda[i]+0 == gda[i]){ tot=gda[i]-tot }
  }
  print -tot }')

printf '%s, %s total((+)-(-))\n\n%s\n\n since %s (commit: %s).\n\nTake also a look at the [`Mathlib` stats page](%s).\n' "${gdiff}" "${net}" "${percent}" "${date}" "${commit}" "${statsURL}"
