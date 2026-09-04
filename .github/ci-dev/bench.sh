#!/usr/bin/env bash
# Micro-benchmarks for the runner-fleet comparison.
#
# Usage: bench.sh <label> <nfiles> <cpu_seconds> <workdir>
#
# Runs the same work twice from the caller (once under landrun, once under a
# plain shell) so the sandbox cost is a within-machine paired difference.
# Prints one "RESULT <label> <metric> <seconds>" line per measurement.
set -uo pipefail

label="${1:?label}"
n="${2:-20000}"
cpusec="${3:-3}"
root="${4:-.}"

work="$root/bench-work-$label"
rm -rf "$work"; mkdir -p "$work"

now() { date +%s.%N; }
emit() { echo "RESULT $label $1 $2"; }
elapsed() { echo "$1 $2" | awk '{printf "%.3f", $2-$1}'; }

# --- file-operation benchmark -------------------------------------------
# Creating, stat-ing and reading many small files is the syscall-heavy shape
# that `Get cache` (unpacking ~100k olean files) and `mk_all` (scanning the
# source tree) have in the real workflow.
t0=$(now)
python3 -c '
import os,sys
d,n = sys.argv[1], int(sys.argv[2])
buf = b"x"*256
for i in range(n):
    with open(os.path.join(d, "f%06d" % i), "wb") as f:
        f.write(buf)
' "$work" "$n"
t1=$(now)
emit create_"$n"_files "$(elapsed "$t0" "$t1")"

t1=$(now)
python3 -c '
import os,sys
tot=0
for e in os.scandir(sys.argv[1]):
    tot += e.stat().st_size
' "$work"
t2=$(now)
emit stat_"$n"_files "$(elapsed "$t1" "$t2")"

t2=$(now)
python3 -c '
import os,sys
tot=0
for e in os.scandir(sys.argv[1]):
    with open(e.path,"rb") as f: tot += len(f.read())
' "$work"
t3=$(now)
emit read_"$n"_files "$(elapsed "$t2" "$t3")"

t3=$(now)
rm -rf "$work"
t4=$(now)
emit delete_"$n"_files "$(elapsed "$t3" "$t4")"

# --- CPU benchmarks ------------------------------------------------------
# Pure compute, almost no syscalls. Landlock should cost nothing here; this is
# the internal control for the file-operation numbers above.
mkdir -p "$work"
t4=$(now)
openssl speed -seconds "$cpusec" sha256 >"$work/ossl1.txt" 2>&1
t5=$(now)
emit cpu_single_thread "$(elapsed "$t4" "$t5")"
grep -E "^sha256" "$work/ossl1.txt" | tail -1 | sed "s/^/RESULT-RAW $label single /"

ncpu=$(nproc)
t5=$(now)
openssl speed -multi "$ncpu" -seconds "$cpusec" sha256 >"$work/ossln.txt" 2>&1
t6=$(now)
emit cpu_"$ncpu"_threads "$(elapsed "$t5" "$t6")"
grep -E "^sha256" "$work/ossln.txt" | tail -1 | sed "s/^/RESULT-RAW $label multi /"

# --- sequential disk write ----------------------------------------------
t6=$(now)
dd if=/dev/zero of="$work/dd.bin" bs=1M count=512 conv=fdatasync 2>"$work/dd.txt"
t7=$(now)
emit dd_write_512MiB "$(elapsed "$t6" "$t7")"
tail -1 "$work/dd.txt" | sed "s/^/RESULT-RAW $label dd /"

rm -rf "$work"
