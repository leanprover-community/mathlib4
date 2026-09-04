#!/usr/bin/env bash
# Micro-benchmarks for the runner-fleet comparison.
#
# Usage: bench.sh <label> <nfiles> <cpu_seconds> <workdir> [only]
#   only = files | cpu | dd | all   (default all)
#
# Prints one "RESULT <label> <metric> <seconds>" line per measurement, so a
# caller can run the same work against several filesystems or shells and diff
# the labels.
set -uo pipefail

label="${1:?label}"
n="${2:-20000}"
cpusec="${3:-3}"
root="${4:-.}"
only="${5:-all}"

work="$root/bench-work-$label"
rm -rf "$work"; mkdir -p "$work" || { echo "SKIP $label (cannot write $root)"; exit 0; }

now() { date +%s.%N; }
emit() { echo "RESULT $label $1 $2"; }
elapsed() { echo "$1 $2" | awk '{printf "%.3f", $2-$1}'; }
want() { [ "$only" = all ] || [ "$only" = "$1" ]; }

# --- file-operation benchmark -------------------------------------------
# Creating, stat-ing and reading many small files is the syscall- and
# metadata-heavy shape that `Get cache` (unpacking ~100k olean files) and
# `mk_all` (scanning the source tree) have in the real workflow.
if want files; then
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

  # Rewriting every file in place is the overlayfs copy-up path, which is
  # what a build does to its own outputs.
  t3=$(now)
  python3 -c '
import os,sys
buf=b"y"*256
for e in os.scandir(sys.argv[1]):
    with open(e.path,"r+b") as f: f.write(buf)
' "$work"
  t4=$(now)
  emit rewrite_"$n"_files "$(elapsed "$t3" "$t4")"

  t4=$(now)
  rm -rf "$work"
  t5=$(now)
  emit delete_"$n"_files "$(elapsed "$t4" "$t5")"
  mkdir -p "$work"
fi

# --- raw syscall cost ----------------------------------------------------
if want cpu; then
  python3 -c "import ctypes,time;l=ctypes.CDLL('libc.so.6');t=time.perf_counter();[l.syscall(39) for _ in range(1000000)];print('RESULT $label syscall_1e6_getpid %.3f'%(time.perf_counter()-t))" || true
fi

# --- CPU benchmarks ------------------------------------------------------
# Fixed work, timed by wall clock, so the number is a speed. gzip is plain
# integer work; sha256 is accelerated by SHA-NI on AMD Zen and not on older
# Intel server parts, so gzip is the fair cross-vendor comparison.
if want cpu; then
  ncpu=$(nproc)

  head -c 268435456 /dev/urandom > "$work/gz.bin" 2>/dev/null
  if [ -s "$work/gz.bin" ]; then
    t=$(now); gzip -1 -c "$work/gz.bin" > /dev/null; t2=$(now)
    emit cpu_gzip_256MiB_1x "$(elapsed "$t" "$t2")"

    t=$(now)
    for _ in $(seq 1 "$ncpu"); do gzip -1 -c "$work/gz.bin" > /dev/null & done
    wait
    t2=$(now)
    emit cpu_gzip_256MiB_"$ncpu"x "$(elapsed "$t" "$t2")"
    rm -f "$work/gz.bin"
  else
    echo "SKIP $label gzip (no space in $root)"
  fi

  head -c 536870912 /dev/zero > "$work/cpu.bin" 2>/dev/null
  if [ -s "$work/cpu.bin" ]; then
    cat "$work/cpu.bin" > /dev/null   # warm the page cache
    t=$(now); openssl dgst -sha256 "$work/cpu.bin" >/dev/null; t2=$(now)
    emit cpu_sha256_512MiB_1x "$(elapsed "$t" "$t2")"

    t=$(now)
    for _ in $(seq 1 "$ncpu"); do openssl dgst -sha256 "$work/cpu.bin" >/dev/null & done
    wait
    t2=$(now)
    emit cpu_sha256_512MiB_"$ncpu"x "$(elapsed "$t" "$t2")"
    rm -f "$work/cpu.bin"
  else
    echo "SKIP $label sha256 (no space in $root)"
  fi
fi

# --- sequential write ----------------------------------------------------
if want dd; then
  t=$(now)
  dd if=/dev/zero of="$work/dd.bin" bs=1M count=512 conv=fdatasync 2>"$work/dd.txt"
  t2=$(now)
  if [ -s "$work/dd.bin" ]; then
    emit dd_write_512MiB "$(elapsed "$t" "$t2")"
    tail -1 "$work/dd.txt" | sed "s/^/RESULT-RAW $label dd /"
  else
    echo "SKIP $label dd (no space in $root)"
  fi
fi

rm -rf "$work"
