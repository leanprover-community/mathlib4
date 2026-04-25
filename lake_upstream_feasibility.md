# Upstreaming build-graph extraction into Lake itself

Companion to `lake_build_graph_analysis.md`. That document establishes that mathlib4's Lake build is statically reconstructible and proposes a downstream extraction tool. This document asks the inverse: which pieces of that tool belong in Lake itself, and how feasible is it to put them there?

**Summary.** High feasibility for introspection features (command emission, graph emission, standalone node execution, content-hash API). Low feasibility (and questionable desirability) for orchestration features (distributed execution, fingerprint-based invalidation). A staged upstreaming path exists and is outlined in §8.

---

## 1. What Lake already provides

Partial credit before any patches:

- **`FetchM`** (`Lake/Build/Fetch.lean:17-100`) walks the build graph, eagerly registering facets and lazily resolving them. Emission-at-fetch-time is a natural hook — Lake already materialises nodes in topological order; a `--emit` mode just records them instead of running them.
- **`lake setup-file`** (`Lake/CLI/Serve.lean:43-85`) already emits `ModuleSetup` JSON per module — an 80% solution for per-module inputs/options. Limitation: it *builds* dependencies as a side effect (calls `ws.runBuild` around `setupServerModule`). Not a pure extractor.
- **`lake build -v`** prints each command with its env vars when a node executes. The empirical data in the companion doc was harvested with `grep` over this output.
- **`compileLeanModule` / `compileO` / `compileExe`** (`Lake/Build/Actions.lean:28-168`) are cleanly factored, take-all-args-explicitly functions. They read nothing from ambient state beyond their arguments. A remote-worker executor would call these same functions.
- **Input/output content hashes.** Lake already computes these for its own up-to-date checking — the `*.hash` sidecar files. The content-addressing primitive exists; it's just not exposed as an API.

So Lake's internals are already in the right shape. The missing piece is *exposure*.

---

## 2. Feasibility by feature, increasing scope

### Phase 1 — `lake build --emit-commands=file.jsonl`

**What it does.** For every node Lake would execute, emit one JSON line `{cmd, args, env, cwd}` to the named file instead of spawning the subprocess.

**Implementation.** Intercept in `Lake/Util/Proc.lean` (central choke-point for `proc` / `rawProc`) or wrap at the `compile*` call sites. ~50 lines. No new dependencies.

**Why upstream-friendly.** Opt-in, zero default-path change, trivially useful for debugging (`why is this build invoking clang with these flags?`), no schema commitment beyond "JSON lines with obvious fields."

**What it unlocks.** Command-level extraction without patching Lake or reverse-engineering path conventions. Replaces the downstream extractor's empirical `grep '^trace: \.>'` dependency.

### Phase 2 — `lake build --emit-graph=dir/`

**What it does.** Emit a full build graph with per-node records: `{id, command, env, inputs, outputs, setup_json}`. Paths canonicalised to `$WORKSPACE` / `$LAKE_HOME` / `$TOOLCHAIN` placeholders. Pre-computed `setup.json` emitted as a sibling blob per module.

**Implementation.** Same interception points as Phase 1; additionally capture `inputs` from values already in scope at `compileLeanModule` (`setup.importArts`, `setupFile`, `leanFile`) and `outputs` from `arts` (`ModuleArtifacts`). ~200 lines, mostly schema definitions and path canonicalisation. Needs a JSON schema blessed by upstream.

**Why upstream-friendly.** Same reasoning as Phase 1 but at higher fidelity. Useful for CI dashboards, build auditing, LSP integrations, and — as a side effect — distributed orchestration.

**What it unlocks.** This is the feature that **obsoletes the downstream extractor**. Instead of re-deriving the conventions in §6 of the companion doc (path layout, which outputs exist when, how `LEAN_PATH` is assembled), the caller gets authoritative ground truth from Lake itself. The companion doc's §10 regime-detection scan becomes unnecessary — Lake emits whatever it actually does, regime-3 dynamism included, because it emits *while walking*.

### Phase 3 — `lake exec-node <node.json>`

**What it does.** Read one graph node's JSON, execute its `command` with its `env`, verify declared outputs exist.

**Implementation.** Thin wrapper around `compileLeanModule` / `compileO` / `compileExe`, minus the `FetchM` registration dance. ~100 lines.

**Why upstream-friendly.** Completes the round-trip that Phase 2 starts. Also genuinely useful for local debugging: "run just this failing module's node standalone, no cache, no wrapper."

**What it unlocks.** The `run_graph.py` reference executor in the companion doc (§7.2) stops being necessary — workers (local or remote) call `lake exec-node`. The end-to-end output-equivalence test becomes `lake build --emit-graph=… && for-each-node lake exec-node …; diff`.

### Phase 4 — content-hash query API

**What it does.** `lake query <target> :input-hash` / `:output-hash` returning Lake's own computed content hashes (already used for `*.hash` sidecars).

**Implementation.** Plumb through `lake query`. ~50 lines.

**Why upstream-friendly.** Lake already exposes `lake query` for target results; adding hash facets is consistent with the existing surface.

**What it unlocks.** Node-level cache keys without reimplementing Lake's hash algorithm. Orchestrators can compose `(input-hash, command, env) → cache_key` and trust byte-exact agreement with Lake's own caching decisions.

### Phase 5 — pluggable executor interface

**What it does.** Replace the direct `compile*` calls with typeclass-dispatched execution, so a `RemoteExecutor` plugin can take over.

**Why it's hard.** Real design work: protocol shape, streaming output, cancellation, backend abstraction. Opinionated — every remote-execution system (Bazel RBE, Nix builders, Buildbarn, custom queues) wants slightly different shape.

**Recommendation.** Stays downstream. Phase 2 + Phase 3 give orchestrators what they need without forcing Lake to commit to a remote-execution protocol.

### Phase 6 — fingerprint / regime-3 invalidation

**What it does.** Cache the emitted graph, invalidate when graph-construction inputs change.

**Why it's hard.** This is a build-orchestrator's job, not a build-tool's. Lake exposes the primitives (content hashes via Phase 4); the orchestrator composes them into invalidation logic.

**Recommendation.** Stays downstream.

---

## 3. What gets worse by being in-tree

- **Coupling to Lake version.** In-tree features release when Lake releases. For mathlib that's acceptable (`lean-toolchain` pins Lake). For a tool supporting multiple Lean versions, this is friction.
- **Review latency.** Upstream PRs have weeks-to-months turnaround. Iteration speed suffers if the schema is still being designed.
- **Schema ossification.** Once a schema is upstreamed, changing it requires deprecation cycles. Iterate downstream until the shape is right.
- **Scope resistance.** Lake's maintainer may view "distributed build features" as out of scope. Framing matters — see §6.

---

## 4. What gets better

- **Authoritative truth.** No reverse engineering of `compileLeanModule`'s arg order, path conventions, or "does `.olean.server` exist for this module?". Lake emits what it actually does.
- **Regime-3 survival.** Downstream extraction degrades or fails when a project uses custom `target`s / `module_facet`s that compute inputs from upstream build outputs (regime 3 in the companion doc §11). In-tree emission sidesteps this entirely: the emitter hooks into `FetchM` itself, so dynamically discovered edges are captured as they happen.
- **No path-convention fragility.** When Lean v4.31 changes an olean layout detail, a downstream extractor breaks silently; in-tree emission tracks the change automatically.
- **No instrumentation patch to maintain.** Companion doc §9 proposes a downstream Lake patch as the regime-2/3 fallback. Phases 1–2 upstream make that patch permanent and supported.
- **Ecosystem benefit.** Every Lean project — not just mathlib — gets graph extraction. Tooling for Lean (LSPs, formatters, linters, custom build orchestrators) benefits.

---

## 5. Specific implementation sketches

### `--emit-commands` (Phase 1)

```lean
-- In Lake/Util/Proc.lean, around `proc` / `rawProc`:
public def maybeEmit (p : ProcessInput) (buildConfig : BuildConfig) : BaseIO Unit := do
  if let some path := buildConfig.emitCommands? then
    let record := Json.mkObj [
      ("cmd",  p.cmd),
      ("args", toJson p.args),
      ("env",  toJson p.env),
      ("cwd",  toJson p.cwd?)
    ]
    IO.FS.writeFile path (record.compress ++ "\n") -- append-mode in real impl

public def rawProc (p : ProcessInput) : LogIO Output := do
  if (← getBuildConfig).emitCommands?.isSome then
    maybeEmit p (← getBuildConfig)
    return ⟨0, "", ""⟩ -- stub; caller must handle
  else
    -- existing implementation
```

Needs a proper append-mode file handle, lock for parallel emission, and a decision for how "stub" return values propagate (probably: in `--emit-commands` mode, downstream nodes that depend on this output are also emitted-not-run; Lake's existing up-to-date logic handles the replay).

### `--emit-graph` (Phase 2)

Hook at `compileLeanModule`:

```lean
public def compileLeanModule ... : LogIO Unit := do
  let node := LeanModuleNode.mk
    (command := lean.toString :: args.toList)
    (env := #[("LEAN_PATH", leanPath.toString)])
    (inputs :=
      #[leanFile, setupFile] ++
      setup.importArts.toArray.flatMap (·.2) ++
      setup.plugins ++
      setup.dynlibs)
    (outputs := arts.declaredFiles)
    (setupJson := toJson setup)
  if let some dir := (← getBuildConfig).emitGraph? then
    emitNode dir node
  else
    -- existing subprocess invocation
    ...
```

`arts.declaredFiles` is a small helper over `ModuleArtifacts` that returns the union of present-by-construction output paths.

Canonicalisation happens in `emitNode`: replace `workspace.root` prefix with `$WORKSPACE`, `lakeEnv.lean.root` with `$TOOLCHAIN`, etc.

### `lake exec-node` (Phase 3)

```lean
public def execNode (nodePath : FilePath) : LogIO Unit := do
  let node ← readJsonFile nodePath
  match node.kind with
  | .leanModule =>
    let setup := node.setupJson
    IO.FS.writeFile node.setupFilePath (toJson setup).pretty
    rawProc { cmd := node.command[0]!, args := node.command[1:].toArray, env := node.env }
  | .ccCompile => ...
  | .ccLink    => ...
```

About 100 lines including path re-absolutisation from `$WORKSPACE` placeholders supplied via env.

---

## 6. Getting it upstream: framing and sequencing

### Framing

Lake's maintainer (Mac Malone) and the Lean FRO have finite review bandwidth and opinions about scope. Distributed-build-orchestration is almost certainly out of scope for Lake itself. But **introspection features that happen to enable distributed orchestration** are a much easier sell — they are also useful for:

- LSPs and IDEs (showing exactly what a module's build dependencies are).
- Build auditing and diagnostics (`why is my build slow? dump the graph and analyse it`).
- CI (generate targeted sub-builds for changed files without running full discovery).
- Research and teaching (Lake itself is a clean reference design; exposing its internal graph is pedagogically useful).

Lead with these motivations; distributed execution is a happy consequence mentioned at the end.

### Sequencing

1. **Ship the downstream extractor first.** See the companion doc §15. Fast iteration, stable schema, empirical proof that the graph format is correct against `lake build` ground truth (companion §7.2).
2. **Propose Phase 1 upstream.** Small PR, hard to object to. Validate command emission against the downstream extractor's output — if they disagree, one or the other is wrong, and that's a concrete bug report rather than a design argument.
3. **Iterate on the Phase 2 schema downstream** until the end-to-end output-equivalence test (companion §7.2) passes reliably on full mathlib.
4. **Propose Phase 2 upstream** with the settled schema. Cite the downstream extractor as design precedent and prior art. The PR's evidence of soundness is the empirical match against `lake build`.
5. **Phases 3 and 4** follow naturally. Phase 3 is "complete the round-trip"; Phase 4 is "expose the hashes you already compute."
6. **Maintain Phases 5 and 6 outside Lake.** Orchestration is your problem, not Lake's.

By the time Phase 2 lands upstream, the downstream extractor becomes a thin compatibility shim that calls `lake build --emit-graph=…` and post-processes. Eventually it retires.

---

## 7. Risks specific to upstreaming

- **Mac Malone's bandwidth.** Lake is largely one-maintainer. Large PRs stall. Keep each phase independently useful and mergeable.
- **Lean core RFC process.** If the Lean FRO considers this a public-surface feature, it may require an RFC rather than a direct PR. Phase 1 is small enough to not trigger that; Phase 2 probably does.
- **Schema bikeshedding.** JSON field names, path placeholder conventions, hash algorithm choice — these attract opinions. Minimise by matching existing Lake conventions wherever possible (e.g., `ModuleSetup`'s current field names for `setup_json`).
- **Feature interactions.** `--emit-graph` must compose sensibly with `--no-build`, `-R`, `-K`, `--packages`, `--old`, `--rehash`. Each combination needs a documented semantics. This is the real implementation tax.

---

## 8. Recommended path

Phase 1 → Phase 2 → Phase 3 → Phase 4 upstream, over ~4 PRs spanning months. Phase 5+ stays downstream permanently.

Start by building the downstream extractor per the companion doc. Use its emission schema as the strawman for Phase 2's upstream schema. The extractor's `--validate-outputs` test (companion §7.2) is the objective function: when Lake's Phase 2 output passes the same test, Phase 2 is done.

The distributed-execution features (scheduler, CAS integration, remote dispatch, fingerprint invalidation) never live in Lake. They consume Lake's emitted graph, which is the correct separation of concerns: Lake is the Lean build tool; your orchestrator is the distribution layer.
