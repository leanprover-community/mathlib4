# Sandboxing a `lean` invocation to verify the declared input set is exhaustive

Companion to [`lean_compile_io_analysis.md`](./lean_compile_io_analysis.md). The IO analysis
established that, under three explicit assumptions (regime 1, toolchain-blob staged, no tactic-IO),
the per-node read/write set of a Lake-driven `lean` compilation is statically determinable. This
document analyzes how to **verify** that determination at runtime — i.e., catch the moment any of
the three assumptions silently breaks.

The running example is still `Mathlib.Algebra.Group.Basic` (266 importArts, all module-style
size 3, no plugins/dynlibs, six output files; see §1 of the IO doc).

---

## 1. Why bother

Today the extractor's correctness is empirically validated end-to-end (`validate-outputs` byte-equal
9/9 modules, 7/8 lean_exes per `lake_graph_extract.md` §6). That checks **outputs**. It does not
directly check **inputs**: the extractor could be over-declaring (harmless but inflates cache keys
and wastes CAS bandwidth) or, more dangerously, under-declaring in a way that happens to produce
the same output bytes today but breaks the day a worker is missing a transitively-needed file.

Three concrete failure modes the IO doc flagged that no current check catches:

1. **Extractor under-declares an input.** Some file the worker would need to stage is missing
   from `inputs`. Today, on the local machine, the file happens to be present anyway (it's a
   neighbor in `.lake/build`), so `validate-outputs` passes. On a remote worker with only
   declared inputs staged, the build fails — and the failure surfaces only in production.
2. **A future tactic introduces IO.** A new `simp` extension reads a config file from disk during
   elaboration. The build still works locally. The output may even be deterministic (the file
   doesn't change). But the *input set is no longer a function of the import graph* — it depends
   on a file the extractor never knew about. A worker without the config produces different
   outputs, and the cache silently lies about freshness.
3. **An upstream package adds a plugin or dynlib.** The §10.5 preflight catches it via
   `setup.json.plugins != []`, but only at extractor-emission time and only if the developer runs
   preflight before emitting. Sandboxing catches it at compile time, on every build.

What we want is a check whose failure mode is "build aborts with a clear error pointing at the
unexpected file," not "build succeeds, distributed worker fails six hours later, debug from
hash diff."

---

## 2. Three escalating tiers

| Tier | Property | Mechanism | Cost | When |
|---|---|---|---|---|
| 1. Tracer-only | *Observe* the actual read set; diff against declared | `fs_usage`/`strace`/`dtruss` | ~10–30% overhead, sample-only | Local dev, CI spot-check |
| 2. Fail-closed sandbox | *Enforce* declared ⊇ actual; build fails on hidden read | `sandbox-exec`/`bwrap` | ~10 ms setup per node | CI nightly full-graph |
| 3. Worker-as-sandbox | Worker stages only declared inputs into a fresh exec-root | CAS staging in the dispatcher | Free (it's the architecture) | Production worker pool |

Tiers 1 and 2 are explicit verification tooling. Tier 3 falls out of the distributed-execution
design itself — if the worker only mounts what was declared, hermeticity is the default rather
than a property to enforce. Tiers 1 and 2 remain useful pre-production checks even when tier 3
exists, because they catch extractor bugs before they reach the worker pool.

---

## 3. Tier 1: tracer-only, observation-only

Cheapest, no-risk, runs alongside the existing `validate-outputs` flow. The build executes
normally; we only observe what was opened.

### 3.1 macOS implementation (`fs_usage`)

This machine has `fs_usage` and `dtruss` but neither `strace` nor `bwrap`. The Mac path is
`fs_usage`-based.

```bash
# Capture every filesystem syscall lean makes during a single-module rebuild.
sudo fs_usage -w -f filesys $(pgrep -f "lean ") 2>/dev/null > trace.log &
TRACER=$!
lean ${args}
kill $TRACER

# Extract opened paths.
awk '/open|stat64|access|fstatat/ { for (i=NF; i>0; i--) if ($i ~ /^\//) {print $i; break} }' \
  trace.log | sort -u > opened.txt

# Diff against declared.
jq -r '.nodes[] | select(.id == "mathlib:Mathlib.Algebra.Group.Basic") | .inputs[].path' \
  build_graph.json | sort -u > declared.txt

# Over-reads (in actual but not declared) — the failure case.
comm -23 opened.txt declared.txt
```

`fs_usage` requires sudo (it taps the kernel syscall log via dtrace). For a developer machine
that's fine; for CI consider running the equivalent `dtruss -f -t open` with a wrapper that
filters output, since `dtruss` is also dtrace-backed but runs as a child process.

### 3.2 Linux implementation (`strace`)

```bash
strace -f -e trace=openat,open -o trace.log lean ${args}
awk -F'"' '/openat\(.*"\/[^"]+"/ && !/= -1/ { print $2 }' trace.log | sort -u > opened.txt
# ... same diff as above
```

`strace` doesn't need root, runs as the parent of the traced process. ~10–30% wall-clock overhead
on lean compilation; acceptable for sample runs.

### 3.3 What to do with the diff

`comm -23 opened.txt declared.txt` — paths actually opened but not declared. Three buckets:

1. **Toolchain paths** (`/Users/chelo/.elan/toolchains/.../bin/lean`, `.../lib/lean/Init.olean`,
   dyld cache, libc, libleanshared, …). Expected; this is the §6 IO-doc "toolchain blob"
   recommendation. Either accept and document, or fold the toolchain into a separate hashed
   input set.
2. **Lake's own reads.** `.hash` sidecars, `lean-toolchain`, `lake-manifest.json`, the lakefile
   itself. These are the parent Lake process, not lean — should not appear if you trace only the
   lean child. If they do, your tracer is capturing too much.
3. **Genuine surprises.** Anything that is neither toolchain nor Lake. **This is the failure
   signal.** A new `Init`-tree path; a config file a tactic decided to read; a plugin's `.so`
   pulled in transitively. Any entry here is a real extractor or assumption violation.

The reverse diff — `comm -13` — gives over-declared paths (declared but never opened). For our
running example this should include all 266 `.olean.server` paths (the §5.1 prediction: size-3
entries list `.olean.server` but `lean` doesn't open it in non-server mode), and most `.ir`
paths (only the `meta`/`importAll`-reachable ones get loaded). That's expected and documents
itself as evidence that the encoding theory holds.

### 3.4 Wiring it into the existing extractor

A new subcommand mirroring `validate-outputs`:

```bash
python3 scripts/lake_graph_extract.py validate-reads Mathlib.Algebra.Group.Basic
```

Implementation: re-use the per-target rebuild loop from `validate-outputs` but wrap the `lean`
invocation in `fs_usage`/`strace`. Compare the resulting opened-path set to the node's `inputs`.
Report the three buckets above.

Run on the same sample as `validate-outputs` (one leaf, one mid-stack, one deep, one per
lean_lib, plus `lean_exe`s). ~ten minutes total. Add to CI as a nightly check; failures point
at a specific path, so debugging is cheap.

This is the version I'd build first. Maximum signal, no behavior change to the build itself.

---

## 4. Tier 2: fail-closed sandbox

Same goal as tier 1 but with enforcement: `lean` runs in an environment where files outside the
declared set *do not exist*. If `lean` tries to open one, the build fails with `ENOENT` or
`EACCES` immediately, pointing at the offending path.

### 4.1 macOS — `sandbox-exec`

`sandbox-exec` is built in (`/usr/bin/sandbox-exec`) and uses TinyScheme profiles. Apple has
marked it deprecated for years but Homebrew, Nix, and others continue to use it because the
replacement (App Sandbox) is unsuitable for command-line build tooling. It works.

A profile for one mathlib node, generated by the extractor:

```scheme
(version 1)
(deny default)

;; Process control.
(allow process-fork)
(allow process-exec*)
(allow signal (target self))

;; dyld and libsystem.
(allow file-read*
  (literal "/usr/lib/dyld")
  (subpath "/usr/lib/system")
  (subpath "/System/Library/dyld"))
(allow mach-lookup)
(allow ipc-posix-shm)
(allow sysctl-read)

;; Toolchain — read-only.
(allow file-read*
  (subpath "/Users/chelo/.elan/toolchains/leanprover--lean4---v4.30.0-rc2"))

;; Per-node declared inputs (one entry per .olean / .ir / .olean.server).
(allow file-read*
  (literal "/Users/chelo/mathlib4/Mathlib/Algebra/Group/Basic.lean")
  (literal "/Users/chelo/mathlib4/.lake/build/ir/Mathlib/Algebra/Group/Basic.setup.json")
  (literal "/Users/chelo/mathlib4/.lake/build/lib/lean/Mathlib/Util/ParseCommand.olean")
  (literal "/Users/chelo/mathlib4/.lake/build/lib/lean/Mathlib/Util/ParseCommand.ir")
  (literal "/Users/chelo/mathlib4/.lake/build/lib/lean/Mathlib/Util/ParseCommand.olean.server")
  ;; ... 263 more triples ...
)

;; Output paths — read+write.
(allow file-write*
  (subpath "/Users/chelo/mathlib4/.lake/build/lib/lean/Mathlib/Algebra/Group")
  (subpath "/Users/chelo/mathlib4/.lake/build/ir/Mathlib/Algebra/Group"))
(allow file-read*
  (subpath "/Users/chelo/mathlib4/.lake/build/lib/lean/Mathlib/Algebra/Group")
  (subpath "/Users/chelo/mathlib4/.lake/build/ir/Mathlib/Algebra/Group"))
```

Then `sandbox-exec -f profile.sb lean ${args}`. Anything not allowed returns EPERM.

For a 266-import node, the profile has ~800 `(literal ...)` lines. Generation is a templating
exercise; sandbox-exec parses the profile in a few ms. Per-node overhead: a single-digit ms.

### 4.2 Linux — `bwrap`

`bwrap` (bubblewrap) is the modern user-namespace sandbox; it's what Flatpak uses. The
equivalent of the macOS profile:

```bash
bwrap \
  --ro-bind <TOOLCHAIN_ROOT> <TOOLCHAIN_ROOT> \
  --ro-bind <WORKSPACE>/Mathlib/Algebra/Group/Basic.lean <SAME> \
  --ro-bind <WORKSPACE>/.lake/build/ir/Mathlib/Algebra/Group/Basic.setup.json <SAME> \
  $(for f in <each declared importArt>; do echo --ro-bind $f $f; done) \
  --bind <output-dir-libpath> <SAME> \
  --bind <output-dir-irpath> <SAME> \
  --proc /proc --tmpfs /tmp --dev /dev \
  --setenv LEAN_PATH "<LEAN_PATH>" \
  --chdir <WORKSPACE> \
  -- lean ${args}
```

bwrap creates a fresh user namespace, mounts only the declared paths, then runs lean inside.
Anything not in the bind list literally is not on the filesystem from lean's perspective —
`open()` returns ENOENT. Setup time per node: ~10 ms (kernel namespace ops).

This is what Bazel's `linux-sandbox` does; it's the same blueprint we'd inherit.

### 4.3 Practical issues that bite

These apply to either macOS or Linux flavors. Worth listing because they're easy to hit:

1. **Realpath dereferencing.** `loadPlugin` calls `IO.FS.realPath`; `findOLean` walks search-path
   entries that may be symlinks. The allow-list / bind-mount list must include the
   realpath'd targets, not just the symlink names. For our example, `~/.elan/toolchains/...` is
   a symlink whose realpath you must allow. Generate the allow-list with `realpath` applied to
   every entry; otherwise the first symlink resolution fails.
2. **Output directory must exist.** Lean writes to paths but doesn't `mkdir -p` intermediates.
   The sandbox setup must `mkdir -p .lake/build/lib/lean/Mathlib/Algebra/Group/` and
   `.lake/build/ir/Mathlib/Algebra/Group/` before invoking lean. (`run_graph.py` already does
   this for the unsandboxed case; reuse the same code path.)
3. **Don't bind-mount whole directories you didn't fully enumerate.** Tempting shortcut:
   `--ro-bind .lake/build/lib/lean .lake/build/lib/lean`. But that exposes every olean in the
   workspace, including stale ones from previous builds. The sandbox would silently let lean use
   a stale dependency that the extractor *should* have declared. Per-file binds (or symlink
   farms in a fresh exec-root) are tedious but necessary.
4. **dyld shared cache, ld.so cache, /proc/self/exe.** The OS loader needs these or the binary
   doesn't even start. bwrap's `--proc /proc` covers `/proc/self/exe`; the macOS profile above
   covers dyld. If you run a stripped-down profile and lean dies with `dyld: library not loaded`
   *before* main, you've over-restricted.
5. **Lake itself is outside the sandbox.** The wrapper sandboxes only the inner `lean`
   subprocess, not Lake's orchestration. That's the right boundary — Lake reads `.hash`
   sidecars, `lake-manifest.json`, etc. and there's no point pretending it doesn't. The
   distributed-execution worker calls `lean` directly anyway, so the sandboxed-just-lean shape
   matches production.
6. **macOS `sandbox-exec` is officially deprecated.** It still works. Apple has not provided a
   replacement suitable for build tooling. The risk is "Apple removes it in macOS 28"; the
   mitigation is "Homebrew, Nix, and a substantial fraction of Mac dev tooling depends on it,
   so removal would have an enormous blast radius." Plan accordingly but don't avoid it on
   deprecation grounds alone.
7. **Tactic that genuinely needs IO.** If a future mathlib tactic legitimately needs to read a
   data file (a lookup table, a generated proof corpus, etc.), the fail-closed sandbox will
   refuse it. The fix is to declare the data file as an input on every consuming module's node.
   That's the *correct* answer for hermeticity — but it requires the extractor to know about
   the dependency. Discoverability is a problem; tier 1 finds it (the over-read shows up in the
   diff), then you decide whether to add the file to declared inputs or to refactor the tactic.

### 4.4 What this verifies that nothing else does

Tier 2's selling point is the no-tactic-IO assumption from §6 of the IO doc. That assumption is
currently a property of mathlib's culture, not of the build system. Under tier 2:

- A new tactic that calls `IO.FS.readFile` → EPERM/ENOENT → elaboration fails → build fails at
  the offending commit, not later via a hash mismatch.
- An `initialize` block that reads a config file → same.
- A plugin that tries to dlopen an undeclared `.so` → ENOENT → loud failure.

This converts "we trust mathlib doesn't do tactic IO" into "the build fails the moment that
trust is violated." Strictly stronger property; it's the reason to escalate from tier 1 to
tier 2 even when the extractor's input set looks complete.

---

## 5. Tier 3: the worker *is* the sandbox

For distributed execution, the cleanest property is that hermeticity falls out of how the worker
fetches inputs, not from a separate enforcement layer.

The pattern (Bazel RBE, Nix builder, custom CAS+queue):

1. Dispatcher sends `{node_id, command, env, input_hashes, output_paths}` to a worker.
2. Worker fetches each `input_hash` from the CAS, materializes them at the declared paths in a
   fresh exec-root.
3. Worker invokes `lean ${args}` with `cwd` = exec-root.
4. Worker uploads outputs to CAS, returns hashes to dispatcher.

After step 2, the worker's exec-root contains *exactly* the declared inputs and *nothing else*.
Lean cannot read what isn't there. No bwrap, no sandbox-exec, no profile generation. The
hermeticity is structural.

The toolchain still has to be staged — but it's hashed once at extractor time and pinned across
the worker fleet, mounted read-only at every node. (The §6 IO-doc recommendation: fold the
toolchain into the cache key as a single platform-blob hash.)

So the architectural decision is: **if the worker is built right, tier 2 is free.** The local
sandbox (tier 1 / tier 2) remains useful as a development-time tool to catch extractor bugs
before they reach the worker pool, but it's not load-bearing for production.

---

## 6. Recommendation

Concrete, in escalating order:

1. **Build tier 1 first.** Add `validate-reads` to `lake_graph_extract.py`, mirroring
   `validate-outputs`. Use `fs_usage` on macOS, `strace` on Linux. Diff opened paths against
   declared `inputs`. Report the three buckets from §3.3 (toolchain / Lake / surprises). Run on
   the same sample as `validate-outputs` in CI. ~few hundred lines of Python, one afternoon.
   This catches extractor bugs and the "new tactic does IO" regression with high signal.
2. **Build tier 2 for nightly CI.** Wrap `lean` in `bwrap` (Linux runner) for the full-graph
   `validate-outputs --full` run. If it passes, you have empirical proof of hermeticity for
   that toolchain version. ~one to two days of work; depends on getting the bind-mount list and
   the realpath handling right.
3. **For production:** *don't* build a separate sandbox layer for the worker pool. Make the
   worker stage only declared inputs (CAS-driven exec-root construction) and tier 2 is the
   default behavior. The local sandbox stays as a dev-time tool.

Tier 1 is a clear win regardless of distribution plans — it tells you whether the existing
extractor is honest about what it declares, with no risk and no architectural commitment. That's
where to start.

---

## 7. What this gives you back

End state, after tiers 1 and 2 plus a CAS-staging worker:

- The extractor's `inputs` are *verified exhaustive* against the actual `lean` read set, on
  every CI run.
- The "no tactic IO" assumption is *enforced*, not assumed.
- Plugin/dynlib introduction is caught at compile time, even if the §10.5 preflight scan was
  skipped.
- Distributed workers are correct by construction — they cannot stumble on hidden inputs because
  hidden inputs literally aren't on their filesystem.

That's a meaningful step from "the extractor passes its current validators" to "the extractor's
contract is enforced end-to-end." For a distributed mathlib build, that's the property that
matters.

---

## 8. Source pointers

| Topic | File / source |
|---|---|
| `loadPlugin` realpath behavior | `Lean/LoadDynlib.lean:93-115` |
| `findOLean` search-path walk | `Lean/Util/Path.lean:116-124` |
| Per-import file-open decision | `Lean/Environment.lean:2129-2143` |
| Bazel's macOS sandbox (`sandbox-exec` profile generator) | `bazel/src/main/tools/sandbox-exec.sb` (upstream reference) |
| Bazel's Linux sandbox (`linux-sandbox`) | `bazel/src/main/tools/linux-sandbox.cc` (upstream reference) |
| Nix's macOS sandbox profile | `nix/src/libstore/build/sandbox.sb` (upstream reference) |
| `sandbox-exec` profile syntax | `man sandbox-exec`, `man sandbox` (deprecated but installed) |
| `bwrap` flags | `man bwrap` |
| `fs_usage` syntax | `man fs_usage` (requires root for filesys filter) |
