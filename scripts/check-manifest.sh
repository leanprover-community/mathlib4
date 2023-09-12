fail_if_stderr() (
  rc=$({
    ("$@" 2>&1 >&3 3>&- 4>&-; echo "$?" >&4) |
    grep '^' >&2 3>&- 4>&-
  } 4>&1)
  err=$?
  [ "$rc" -eq 0 ] || exit "$rc"
  [ "$err" -ne 0 ] || exit 125
) 3>&1

# `resolve-deps` is an undocumented command for `lake`
# that will print a `warning: manifest out of date` warning on stderr if relevant

fail_if_stderr lake resolve-deps
