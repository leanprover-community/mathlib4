#!/usr/bin/env bash
# Run one command and report how many cores it actually kept busy.
#
#   measure.sh <label> <timeout_seconds> <command...>
#
# /proc/stat is not namespaced, so inside the job container it still accounts
# every core on the host. The host runs one job at a time, so whole-machine CPU
# over the command's wall clock is that command's effective core count.
#
# Prints:
#   RESULT <label> wall_s <s>
#   RESULT <label> machine_cpu_s <s>
#   RESULT <label> eff_cores <n>
#   RESULT <label> peak_mem_gb <n>
#   RESULT <label> exit <code>
#   SPAN   <label> <start_epoch> <end_epoch>      (to detect serialisation)
set -uo pipefail

label="${1:?label}"; tmo="${2:?timeout}"; shift 2

busy() { awk '/^cpu /{idle=$5+$6; t=0; for(i=2;i<=NF;i++) t+=$i; print t-idle}' /proc/stat; }
memfree_kb() { awk '/^MemAvailable:/{print $2}' /proc/meminfo; }
hz=$(getconf CLK_TCK 2>/dev/null || echo 100)
memtotal=$(awk '/^MemTotal:/{print $2}' /proc/meminfo)

minfree="$memtotal"
( while :; do
    f=$(memfree_kb)
    [ -n "$f" ] && [ "$f" -lt "$minfree" ] 2>/dev/null && { minfree=$f; echo "$f" > "/tmp/minfree.$label"; }
    sleep 2
  done ) &
sampler=$!
echo "$memtotal" > "/tmp/minfree.$label"

b0=$(busy); t0=$(date +%s.%N); start=$(date +%s)
timeout "$tmo" "$@" > "/tmp/out.$label" 2>&1
rc=$?
end=$(date +%s); t1=$(date +%s.%N); b1=$(busy)
kill "$sampler" 2>/dev/null || true

mf=$(cat "/tmp/minfree.$label" 2>/dev/null || echo "$memtotal")
awk -v l="$label" -v b0="$b0" -v b1="$b1" -v t0="$t0" -v t1="$t1" -v hz="$hz" \
    -v mt="$memtotal" -v mf="$mf" -v rc="$rc" 'BEGIN{
  w=t1-t0; c=(b1-b0)/hz
  printf "RESULT %s wall_s %.1f\n", l, w
  printf "RESULT %s machine_cpu_s %.1f\n", l, c
  printf "RESULT %s eff_cores %.2f\n", l, (w>0? c/w : 0)
  printf "RESULT %s peak_mem_gb %.1f\n", l, (mt-mf)/1048576
  printf "RESULT %s exit %d\n", l, rc
}'
echo "SPAN $label $start $end"
[ "$rc" -eq 124 ] && echo "NOTE $label hit the ${tmo}s timeout"
tail -5 "/tmp/out.$label" | sed "s/^/LOG $label | /"
exit 0
