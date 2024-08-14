git diff --name-only master |
  awk -F/ '((3 <= NF) && (($1 == "Mathlib") || ($1 == ".github"))) {
    rootDir=tolower($2)
    if(rootDie == "workflows") { rootDir="CI" } else { rootDir="t-"rootDir }
    roots[rootDir]++
  } END { for(r in roots) {
    printf("%s files modified in `%s`\n", roots[r], r) }
  }'


git diff --name-only master |
  awk -F/ '((3 <= NF) && (($1 == "Mathlib") || ($1 == ".github"))) {
    rootDir=tolower($2)
    if(rootDie == "workflows") { rootDir="CI" } else { rootDir="t-"rootDir }
    roots[rootDir]++
  } END { for(r in roots) {
    printf("%s,", r) }
    print ""
  }'
