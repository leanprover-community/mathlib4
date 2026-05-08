# Upstreaming `lake graph-extract` into Lake

Companion to `lake_build_graph_analysis.md` and `lake_graph_extract_handoff.md`. This document covers the strategy for landing the `lake graph-extract` subcommand upstream in `leanprover/lean4`.

**Summary.** The Lake-side commits on the `graph-extract-v1` branch are designed to be mergeable as-is — opt-in subcommand, no breaking API changes, only `private` → `public` promotions where helpers are reused. Distributed-execution machinery stays downstream entirely; that's the orchestrator's job, not Lake's.

---

## 1. What's being upstreamed

Five commits (commit hashes from the `graph-extract-v1` branch in `/Users/chelo/mathlib4/lean4-src`):

1. `f703a7a0` — `Lake/Build/Actions.lean`: extract `mkLeanModuleArgs`, `mkCcCompileArgs`, `renderRspContents` as pure helpers. Wrappers (`compileLeanModule`, `compileO`, `compileExe`) keep their existing signatures and behaviour. Pure refactor.
2. `ac0179e3` — `Lake/Build/Common.lean`: `private def mkLinkObjArgs` → `public def`. One-line visibility change.
3. `0b814ce7` — new module `Lake/Build/GraphExtract.lean` (~600 LoC). The walker. Uses only pure facets (`:input`/`:imports`/`:transImports`); reconstructs `setup.json` and importArts via path conventions; emits a v2 schema with interned module index.
4. `64d36c68` — `Lake/CLI/Main.lean`: `protected def graphExtract`, dispatch entry, import. CLI signature: `lake graph-extract <target> [<manifest> [<sidecar-dir>]]`.
5. `49b60ec9` — per-node sidecar emission. With sidecar dir provided, writes `<sanitized-id>.node.json` per node and emits a slim summary in the main manifest.

The framing for the upstream PR: **structural metadata for shard planning + offline graph analysis**. The walker is post-elaboration introspection. It does not change build behaviour, does not introduce new executors, and does not commit Lake to a remote-execution protocol.

---

## 2. What's NOT being upstreamed

- **The Python validators (`scripts/lake_graph_extract.py`)** — these are mathlib-side regression checks during continued Lake-side iteration. Not part of the upstream surface.
- **`scripts/run_graph.py`** — a sequential reference executor. Lake itself is the executor for any real distributed-build pipeline (Lake's native cache + `lake build`); `run_graph.py` exists only to validate the extractor's correctness end-to-end.
- **Distributed-build orchestration** (CI shard planner, GHA matrix workflow, CAS protocol). All downstream. Lake's `Lake.Artifact` + `lake cache get/put` already handles content-addressed remote caching natively (as of v4.30); the orchestrator composes a partition over Lake's existing primitives.
- **SHA256 / cache_key API** — Lake already exposes `Lake.Hash` and `cache.readOutputs?`; no need for a separate "extract gives you cache keys" feature.

---

## 3. What gets better when this is upstream

- **Authoritative truth.** No reverse engineering of `compileLeanModule`'s arg order, path conventions, or "does `.olean.server` exist for this module?". Lake emits what it actually does.
- **Path-convention drift survives toolchain bumps automatically.** When Lake changes an output convention, the walker tracks the change because it calls Lake's own `mkLeanModuleArgs`.
- **Ecosystem benefit.** Every Lean project — not just mathlib — gets graph extraction. LSP integrations, build auditing tools, CI selective-rebuild logic, and pedagogical use cases all benefit.
- **Removes an instrumentation patch class.** Without `lake graph-extract`, the only options for graph extraction are (a) hand-mirroring Lake (fragile, what mathlib's old Python script did) or (b) patching Lake at action sites to log commands (invasive). The upstream subcommand obviates both.

---

## 4. What gets harder by being in-tree

- **Coupling to Lake version.** In-tree features release when Lake releases. For mathlib that's acceptable (`lean-toolchain` pins Lake). Tools supporting multiple Lean versions need to detect the feature.
- **Schema ossification.** Once a schema is upstreamed, changing it requires deprecation cycles. The current v2 schema (interned modules + per-node references) is the result of one round of iteration; another round may be desirable before locking it in.
- **Review latency.** Upstream PRs have weeks-to-months turnaround.
- **Scope debate.** The upstream maintainer may view some of this as out of scope. Framing matters — see §6.

---

## 5. Implementation sketches

### Pure helpers in `Build/Actions.lean` (commit `f703a7a0`)

```lean
public def mkLeanModuleArgs
  (leanFile : FilePath) (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts) (leanArgs : Array String := #[])
: Array String × Bool := ...
```

Returns the pure argv + a `postponeCompile` flag. The wrapper `compileLeanModule` calls `mkLeanModuleArgs`, then handles the I/O (`createParentDirs`, write `setupFile`, `rawProc`) and the postpone-compile branch. No call sites change.

Same shape for `mkCcCompileArgs` (used by `compileO`) and `renderRspContents` (used by both `mkArgs` for I/O and the graph emitter for `rsp_args`).

### `lake graph-extract` CLI handler (commit `64d36c68`)

```lean
protected def graphExtract : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  let target   ← takeArg "target"
  let manifest? ← takeArg?
  let sidecar?  ← takeArg?
  noArgsRem
  let buildConfig := mkBuildConfig opts
  ws.runFetchM (cfg := buildConfig) <|
    GraphExtract.emit ws (← parseTargetSpecs ws #[target]) manifest? sidecar?
```

Dispatched in `Lake/CLI/Main.lean:cacheCli`-adjacent dispatch logic. Argv shape mirrors existing `query` / `setup-file` patterns. Help entry added to `Lake/CLI/Help.lean`.

### Walker module (commit `0b814ce7`)

Pure-facet walker (only `:input` / `:imports` / `:transImports`); `runPreflight` for regime-1 dynamism guards; `enumerateModuleClosure` reconstructs `ImportArtifacts` and `setup.json` content from path conventions; `composeLeanModuleNode` errors on `dynlibs`/`plugins` non-empty. See `Lake/Build/GraphExtract.lean` and `lake_facets_for_extraction.md` for the rationale.

---

## 6. Framing and sequencing

### Framing

Lake's maintainer (Mac Malone) and the Lean FRO have finite review bandwidth. Distributed-build orchestration is out of scope for Lake itself. But **introspection features that happen to enable distributed orchestration** are a much easier sell — they are also useful for:

- LSPs and IDEs (showing exactly what a module's build dependencies are).
- Build auditing and diagnostics ("why is my build slow? dump the graph and analyse it").
- CI selective rebuilds (which modules does this PR's diff affect?).
- Research and teaching (Lake's build graph is a clean reference design; exposing it is pedagogically useful).

Lead with these motivations.

### Sequencing for the PR

The five commits already sequence cleanly:

1. **Pure refactor** (`f703a7a0`) — easy to review, no behaviour change.
2. **Visibility bump** (`ac0179e3`) — one line.
3. **New module** (`0b814ce7`) — the substantive change. Self-contained, no dependents.
4. **CLI wiring** (`64d36c68`) — small surface change.
5. **Sidecar emission** (`49b60ec9`) — additive; orthogonal to the schema.

Land as one PR or two (refactor + everything else). Each commit is independently revertable if review surfaces issues.

### Open items before the PR

Before opening the PR, clean up:

- **Custom-target preflight check** — currently deferred due to a v4.30.0-rc2 codegen issue (see handoff doc). Decide whether to wait for a toolchain bump or land without that check (the substantive checks already cover regime-1 dynamism mathlib cares about).
- **`cc_compile` / `cc_link` / `package_extra_dep` node kinds** — currently the walker emits `lean_module` only. Upstream review may want feature completeness; alternatively, land with `lean_module` only and follow up.
- **Sidecar import_arts trimming** — sidecars currently embed the full transitive import set. Possible optimization (see handoff doc) — not blocking.

---

## 7. Risks

- **Mac Malone's bandwidth.** Lake is largely one-maintainer. Keep each commit independently useful and mergeable.
- **RFC process.** If the Lean FRO considers this a public-surface feature, it may require an RFC rather than a direct PR. The CLI surface is small but the schema is a commitment.
- **Schema bikeshedding.** Field names, path placeholder conventions, the v2 interning scheme — these attract opinions. Minimise by matching existing Lake conventions where possible (e.g., `ModuleSetup`'s field names).
- **Feature interactions.** `lake graph-extract` must compose sensibly with `--no-build`, `-R`, `-K`, `--packages`. Each combination needs documented semantics. This is the real implementation tax.

---

## 8. Recommended path

The Lake-side commits are ready as-is. The remaining gating items (custom-target preflight, cc nodes) are low-priority for the distributed-build use case (Lake's executor handles them). Either:

- **Land minimal first**: open the PR with the current `lean_module`-only walker. Faster review, smaller scope. Follow up with cc nodes and custom-target preflight once the schema is locked in.
- **Land complete**: implement cc nodes first, then PR. Larger but more compelling — the walker covers every node Lake builds.

The minimal-first path is recommended unless upstream review explicitly asks for completeness up front.
