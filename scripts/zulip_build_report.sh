#!/bin/bash
shopt -s extglob

lean_outfile=$1

# Skip the lines about build progress.
filtered_out=$(grep -v '^✔' "${lean_outfile}" | grep -v '^trace: ') 
echo "$(wc -l <<<"${filtered_out}") lines of output" >&2

delimiter=$(cat /proc/sys/kernel/random/uuid)
echo "zulip-message<<${delimiter}"
echo "Mathlib's [nightly-testing branch](https://github.com/leanprover-community/mathlib4-nightly-testing/tree/nightly-testing) ([${SHA}](https://github.com/${REPO}/commit/${SHA})) regression run [completed](https://github.com/${REPO}/actions/runs/${RUN_ID})."

# Categorize the output.
counts=()
# Panics are reported as an info message.
# They should be very prominent when debugging, so treat them differently.
if panic_lines=$(grep '^info: .*PANIC at ' <<<"${filtered_out}"); then
  panic_descriptions=${panic_lines//info: *([^:]):*([0-9]):*([0-9]): }
  counts+=( "$(printf 'Panics: %d' "$(wc -l <<<"${panic_lines}")")" )
  echo "$(wc -l <<<"${panic_lines}") lines of panic" >&2
fi
if error_lines=$(grep '^error: ' <<<"${filtered_out}"); then
  error_descriptions=${error_lines//error: *([^:]):*([0-9]):*([0-9]): }
  counts+=( "$(printf 'Errors: %d' "$(wc -l <<<"${error_lines}")")" )
  echo "$(wc -l <<<"${error_lines}") lines of errors" >&2
fi
if warning_lines=$(grep '^warning: ' <<<"${filtered_out}"); then
  warning_descriptions=${warning_lines//warning: *([^:]):*([0-9]):*([0-9]): }
  counts+=( "$(printf 'Warnings: %d' "$(wc -l <<<"${warning_lines}")")" )
  echo "$(wc -l <<<"${warning_lines}") lines of warnings" >&2
fi
if info_lines=$(grep '^info: ' <<<"${filtered_out}" | grep -v 'PANIC at '); then
  info_descriptions=${info_lines//info: *([^:]):*([0-9]):*([0-9]): }
  counts+=( "$(printf 'Info messages: %d' "$(wc -l <<<"${info_lines}")")" )
  echo "$(wc -l <<<"${info_lines}") lines of info" >&2
fi

if (( ${#counts[@]} == 0 )); then
  echo "Build completed without messages."
else
  printf ' %s\n\n' "${counts[@]}"
fi

if [ -n "${panic_lines}" ]; then
  echo "\`\`\`spoiler Panic counts"
  echo "| | Panic description |"
  echo "| ---: | --- |"
  sort <<<"${panic_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

if [ -n "${error_lines}" ]; then
  echo "\`\`\`spoiler Error counts"
  echo "| | Error description |"
  echo "| ---: | --- |"
  sort <<<"${error_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

if [ -n "${warning_lines}" ]; then
  echo "\`\`\`spoiler Warning counts"
  echo "| | Warning description |"
  echo "| ---: | --- |"
  sort <<<"${warning_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

if [ -n "${info_lines}" ]; then
  echo "\`\`\`spoiler Info message counts"
  echo "| | Info message |"
  echo "| ---: | --- |"
  sort <<<"${info_descriptions}" | uniq -c | sort -bgr | sed 's/^\( *[0-9][0-9]*\) \(.*\)$/| \1 | \2 |/'
  echo "\`\`\`"
  echo
fi

echo "${delimiter}" >> "$GITHUB_OUTPUT"
