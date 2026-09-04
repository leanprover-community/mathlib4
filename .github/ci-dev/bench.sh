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
# Fixed work (hash a fixed buffer), timed by wall clock, so the number is a
# speed. Almost no syscalls, so Landlock should cost nothing here: this is the
# internal control for the file-operation numbers above.
mkdir -p "$work"
head -c 536870912 /dev/zero > "$work/cpu.bin"
cat "$work/cpu.bin" > /dev/null   # warm the page cache

t4=$(now)
openssl dgst -sha256 "$work/cpu.bin" >/dev/null
t5=$(now)
emit cpu_sha256_512MiB_1x "$(elapsed "$t4" "$t5")"

ncpu=$(nproc)
t5=$(now)
for _ in $(seq 1 "$ncpu"); do openssl dgst -sha256 "$work/cpu.bin" >/dev/null & done
wait
t6=$(now)
emit cpu_sha256_512MiB_"$ncpu"x "$(elapsed "$t5" "$t6")"

# --- sequential disk write ----------------------------------------------
t6=$(now)
dd if=/dev/zero of="$work/dd.bin" bs=1M count=512 conv=fdatasync 2>"$work/dd.txt"
t7=$(now)
emit dd_write_512MiB "$(elapsed "$t6" "$t7")"
tail -1 "$work/dd.txt" | sed "s/^/RESULT-RAW $label dd /"

rm -rf "$work"
