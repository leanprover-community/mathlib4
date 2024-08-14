git diff --name-only master |
  awk -F/ '((3 <= NF) && (($1 == "Mathlib") || ($1 == ".github"))) {
    rootDir=tolower($2)
    if(rootDir == "workflows") { rootDir="CI" } else { rootDir="t-"rootDir }
    roots[rootDir]++
  } END { for(r in roots) {
    printf("%s files modified in `%s`\n", roots[r], r) }
  }'


#git diff --name-only master
git ls-files |
  awk -F/ '(2 <= NF) {
    if ($1 == "Mathlib") {
      rootDir="f-"$2
      #rootDir=tolower($2)
    } else if ($1 == ".github") { rootDir="CI"
    } else { rootDir="f-"$1 }
    roots[rootDir]++
  } END { for(r in roots) {
    printf("`%s`\n", r) }
    #printf("%s,", r) }
    #print ""
  }' | sort
