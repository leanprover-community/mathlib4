#!/usr/bin/env bash
# Whole-machine CPU accounting, so a benchmark can prove it had the box to
# itself. /proc/stat is not namespaced, so inside a container it still reports
# every core on the host. Needed when a second runner shares the machine.
#
#   contention.sh busy                     -> busy jiffies since boot
#   contention.sh sample <file> <seconds>   -> append samples until killed
#   contention.sh report <busy_before> <busy_after> <own_cpu_s> <wall_s>
set -uo pipefail

busy() {
  # Every jiffy that is not idle and not iowait.
  awk '/^cpu /{idle=$5+$6; tot=0; for(i=2;i<=NF;i++) tot+=$i; print tot-idle}' /proc/stat
}

case "${1:-}" in
  busy)
    busy
    ;;
  sample)
    out="${2:?file}"; iv="${3:-15}"
    while :; do
      printf '%s load=%s busy=%s\n' \
        "$(date -u +%H:%M:%S)" "$(cut -d' ' -f1-3 /proc/loadavg)" "$(busy)" >> "$out"
      sleep "$iv"
    done
    ;;
  cputimes)
    # Delta of the "children" line of two `times` snapshots, in seconds.
    # bash prints e.g. "1m2.345s 0m3.456s" (user sys).
    awk 'function sec(x, parts){split(x,parts,"m"); sub("s","",parts[2]); return parts[1]*60+parts[2]}
         FNR==2 && NR==2  {bef=sec($1)+sec($2)}
         FNR==2 && NR!=2  {aft=sec($1)+sec($2)}
         END{printf "%.1f", aft-bef}' "${2:?before}" "${3:?after}"
    ;;
  report)
    before="${2:?}"; after="${3:?}"; own="${4:?}"; wall="${5:?}"
    hz=$(getconf CLK_TCK 2>/dev/null || echo 100)
    nc=$(nproc)
    awk -v b="$before" -v a="$after" -v own="$own" -v w="$wall" -v hz="$hz" -v n="$nc" 'BEGIN{
      m = (a-b)/hz
      printf "CONTENTION machine_cpu_s=%.1f own_cpu_s=%.1f wall_s=%.1f threads=%d\n", m, own, w, n
      share = (m>0 ? own/m : 0)
      printf "CONTENTION own_share=%.3f  (1.00 means the job owned the machine)\n", share
      printf "CONTENTION foreign_cpu_s=%.1f foreign_cores_avg=%.2f\n", m-own, (w>0 ? (m-own)/w : 0)
      if (m>0 && share < 0.90)
        print "CONTENTION VERDICT: CONTAMINATED - another job shared this machine; do not compare this wall clock."
      else
        print "CONTENTION VERDICT: clean - the job accounted for essentially all machine CPU."
    }'
    ;;
  *)
    echo "usage: contention.sh busy | sample <file> <sec> | cputimes <before> <after> | report <busy_before> <busy_after> <own_cpu_s> <wall_s>" >&2
    exit 2
    ;;
esac
