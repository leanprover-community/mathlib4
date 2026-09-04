#!/usr/bin/env bash
# Machine characterisation for a runner host. Prints facts, then locates the
# writable filesystems the job can reach so the caller can run the same file
# benchmark against each one.
set -uo pipefail

echo "=== runner ==="
echo "RUNNER_NAME=${RUNNER_NAME:-?}"

echo "=== kernel ==="
uname -a
echo "landlock_abi (0 or -1 means unsupported):"
python3 -c "import ctypes;l=ctypes.CDLL('libc.so.6');print(' ',l.syscall(444,None,ctypes.c_size_t(0),ctypes.c_uint32(1)))" || true

echo "=== cpu ==="
nproc
lscpu 2>/dev/null | grep -E "Model name|Vendor|^CPU\(s\)|Thread\(s\) per core|Core\(s\) per socket|^Socket|MHz|BogoMIPS|L1d|L2|L3|Hypervisor|Virtualization" || true
grep -m1 -E "^microcode" /proc/cpuinfo 2>/dev/null || echo "microcode: (not exposed)"

echo "=== memory ==="
free -g 2>/dev/null | head -2

echo "=== speculative-execution mitigations ==="
for f in /sys/devices/system/cpu/vulnerabilities/*; do
  printf '  %s: %s\n' "$(basename "$f")" "$(cat "$f" 2>/dev/null)"
done

echo "=== container filesystem ==="
# The number of overlay2 lower layers matters: every path lookup walks them.
root_line=$(awk '$2=="/"{print $0}' /proc/mounts | head -1)
echo "  / -> ${root_line%% *} type $(echo "$root_line" | awk '{print $3}')"
lowers=$(echo "$root_line" | tr ',' '\n' | grep -c "^lowerdir=\|:/var/lib/docker" || true)
echo "  lowerdir layer count: $(echo "$root_line" | sed -n 's/.*lowerdir=\([^,]*\).*/\1/p' | tr ':' '\n' | grep -c . || echo '?')"
df -hT / 2>/dev/null | tail -1

echo "=== writable filesystems reachable from the job ==="
# workspace  = the container's own overlay2 upper layer, where .lake lives
# hoststore  = bind mount of the host warm store (skips the graph driver)
# tmpfs      = RAM, the no-filesystem reference
for p in "$PWD" /home/lean/.cache/mathlib /home/lean/.elan /dev/shm; do
  if [ -d "$p" ]; then
    fs=$(df -T "$p" 2>/dev/null | tail -1 | awk '{print $2}')
    sz=$(df -h "$p" 2>/dev/null | tail -1 | awk '{print $4}')
    mnt=$(awk -v P="$p" '$2==P{print "own-mount"}' /proc/mounts | head -1)
    w=no; [ -w "$p" ] && w=yes
    printf '  %-34s fs=%-8s avail=%-7s writable=%-3s %s\n' "$p" "$fs" "$sz" "$w" "${mnt:-inherits /}"
  else
    printf '  %-34s MISSING\n' "$p"
  fi
done

echo "=== tool versions ==="
python3 --version; openssl version; gzip --version | head -1; bash --version | head -1
