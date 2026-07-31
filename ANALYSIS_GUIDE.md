# Writing a good `instanceTypes` site analysis

Guidance for agents documenting why a Mathlib site needs
`set_option backward.isDefEq.instanceTypes "none"` (the strict instance-typed-mvar check from
lean4 PR #9077). Distilled from the analyses in e.g. `Mathlib/CategoryTheory/Filtered/CostructuredArrow.lean`,
`Mathlib/LinearAlgebra/AffineSpace/Ordered.lean`, `Mathlib/RingTheory/Kaehler/JacobiZariski.lean`.

## The `markOrSynth` outcome, in words

The project default is `"markOrSynth"` (set in the lakefile's `leanOptions`, NOT the register
default). An assignment to an instance-typed mvar succeeds if either
1. the **direct type check** accepts: the value's type matches the mvar's type at `.instances`
   transparency (spine mvars admissible), or
2. the **fallback**: the instance is synthesized for the mvar's type, and the candidate value is
   defeq to the **synthesized instance**.
A site needs `"none"` only when both fail. The write-up must say, in these words, where the
failure lands: the direct type check rejects, and then either *the fallback synthesis fails*, or
*synthesis succeeds but the candidate is not defeq to the synthesized instance*. Spell the path
out in self-contained prose — never letter/number codes for the paths.

A site that also carries `respectTransparency false` deserves suspicion: that option suppresses
all `.implicit` bumps, so first-pass easy-case unifications and the fallback's
candidate-vs-synthesized comparison run at the ambient `.instances` transparency — often the
very strictness being worked around. An `implicit_reducible` annotation on the blocking synonym
frequently removes the need for BOTH options at once: with `respectTransparency` restored to
`true`, the bumped `.implicit` comparisons unfold the annotation.

Classify every site as one of the **two underlying issues**:
- **Missing `implicit_reducible` annotation in Mathlib**: candidate and synthesized instance are
  the same instance up to a synonym/projection spelling that merely fails to unfold at the
  operative transparency. The real fix is an annotation (or a proof-local respelling).
- **Actual mismatch between unified and synthesized instances**: genuinely different instances
  (e.g. TopCatAdjunction's coinduced topology vs `compactOpen`, not defeq at any transparency).
  Re-synthesis would silently change the statement's meaning; the fix must respell the
  statement/proof.

## What the write-up is for

A maintainer reading the file should be able to judge, without re-running anything, (a) what
exactly fails and why, (b) whether the failure is harmless-but-strict or a genuine defeq abuse,
and (c) what a real fix would look like. The write-up is **show-don't-tell**: one compact
guarded trace demonstrates the mechanism; prose is reduced to a few pointer lines. There are no
long comment blocks.

## In-file format (show-don't-tell)

Exemplars: `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`,
`Mathlib/CategoryTheory/Abelian/Subobject.lean`, `Mathlib/Condensed/TopCatAdjunction.lean`.

- Module-docstring headers structure the site: `/-! # Issue -/` (or `# First issue: \`decl\``),
  then the **real declaration first** (its options unchanged), then `/-! ## Explanation -/`.
- The Explanation is at most a few comment lines (which synonym boundary, cross-reference,
  which of the two underlying issues) plus **one** `#guard_msgs`-guarded `postprocess_traces`
  demo: a copy of the declaration as an `example`, pinned
  `set_option backward.isDefEq.instanceTypes "markOrSynth"`, with
  `trace.Meta.synthInstance`, `trace.Meta.isDefEq`, `trace.Meta.isDefEq.printTransparency`,
  `trace.Meta.isDefEq.assign.checkTypes` scoped inside the proof at the decisive step.
- The trace must show the decisive `isDefEq.assign.checkTypes` node **with its internals**: the
  direct `.instances` type check, whether the fallback re-synthesis succeeds (elide its subtree:
  `[Meta.synthInstance] ✅ … (truncated)`), and whether the following unification of the
  unified vs synthesized instance succeeds. That trace answers the mark/markOrSynth questions
  by itself.
- Canonical postprocessor chain (copy the `private meta partial def elideBelow` helper, and
  `dropSubtrees` where needed, from an exemplar):
  `filterSubtrees (fun x => (ofClass `Meta.isDefEq.assign.checkTypes x) <&&> failed x)
   >=> elideBelow (fun x => (ofClass `Meta.synthInstance x) <&&> succeeded x)`
  plus site-specific pruning disjuncts. Guards of ~60–110 lines are acceptable.
- Sites whose real declaration compiles at `"markOrSynth"` (fallback-rescued or lever-fixed):
  the demo reproduces the *problem form* (without the lever/proof-local fix); if the decisive
  checkTypes node succeeds overall, filter on `ofClass checkTypes` plus a `containsString`
  instead of `failed`.
- Several sites sharing one cause: full trace at the primary site, few-line pointer comments at
  the siblings.
- An optional `/-! # Fix -/` section holds a passing variant (lever example or respelled form)
  only when the main trace cannot show it.
- Delete every other trace excerpt, counterfactual, and prose paragraph whose message the main
  trace subsumes. Do not discuss the Prop-exemption.

## Debugging workflow (Paul's recipe)

Enable `trace.Meta.isDefEq` (+ `trace.Meta.isDefEq.printTransparency`), `trace.Meta.synthInstance`,
and `trace.Meta.isDefEq.assign.checkTypes` on the failing tactic. Then postprocess, usually as a
chain: start with a filter that keeps only the `synthInstance` trace tree for the instance of
interest, then `filterSubtrees` to expose the node of interest (e.g. a failing `checkTypes`)
*with its context*, and `elideBelow` (copy the helper from existing demo sections, e.g.
`Mathlib/FieldTheory/Galois/Profinite.lean`) to cut the tree below the — usually succeeding —
fallback instance synthesis inside `checkTypes`, keeping the trace manageable.

Read the result against this decision tree:
- **A `checkTypes` node is marked failed** (the expected manifestation). Distinguish:
  - the fallback synthesis for the mvar's expected type *fails*, or
  - synthesis succeeds and the unification of synthesized vs unified instance fails — note the
    transparency level at which it fails (this is what `printTransparency` is for).
- **Every mvar assignment succeeds**: unexpected — the toolchain change should manifest via a
  failing `checkTypes`. Re-examine where the failure actually comes from before blaming the
  option.

## Evidence standards

- **Every causal claim is trace-backed.** No "presumably" in the final prose.
- **Separate load-bearing from noise.** A ❌ that also occurs with the option *disabled* is
  noise. Always produce one strict-mode and one option-on log and diff them; only failures
  unique to strict mode can be load-bearing.
- **Find the diverging simp lemma by diffing** `trace.Meta.Tactic.simp.rewrite` counts between
  the two modes — this localizes the failure to a lemma before you read any synthesis trace.
- **Substantiate defeq claims at the right transparency, on the exact terms from the rejected
  assignment, not simplified stand-ins.** For the two *types*, use
  `with_reducible_and_instances apply_rfl` (mirrors the check itself). For comparing the
  *instance values* (candidate vs synthesized), use `with_implicit apply_rfl`. `with_reducible`
  is the wrong level for both — do not use it as a proxy. Plain `apply_rfl` at default is the
  counterfactual showing the assignment was harmless.
- **Two orthogonal facts, never conflated:** the check compares the instance mvar's *types* at
  `.instances`; whether the instance *values* are defeq (and at what level) is a separate
  question about whether the rejection is harmful. State both, separately.
- Pretty-printed-identical types can still desync in an implicit argument — check with
  `pp.explicit` before concluding "the types look equal".

## Demos

- The single trace demo runs on an **actual copy of the failing declaration** (options flipped
  so the behavior shows), never on a simplified stand-in. Do not hoist the failing synthesis
  goal into a standalone `#synth`/`example` — the context of how elaboration arrived at that
  synthInstance is part of the evidence.
- Scope traces to the single relevant tactic with `set_option trace.… true in` *inside* the
  proof — this shrinks postprocessor filters to 1–2 disjuncts.
- Prune with `postprocess_traces` (`filterSubtrees`, `ofClass`, `containsString`, `failed`,
  `>=>`), keeping the ancestry `synthInstance → apply → tryResolve → checkTypes` so the reader
  sees *whose* mvar rejects. `containsString` sees full-name formatting: use several short
  fragments joined with `<&&>` rather than one string crossing constant-name boundaries.
- Pin `#guard_msgs` via the PLACEHOLDER flow: write `error: PLACEHOLDER`, compile, splice the
  `+`-lines from the mismatch diff back in, recompile to exit 0. Re-verify with
  `-Dpp.unicode.fun=true` (editor and CLI print lambdas differently).
- **Keep guards small.** Drop `trace.Meta.isDefEq` when the checkTypes ❌ lines alone carry both
  types; silence unrelated linters (`linter.unusedSimpArgs`, `linter.style.longLine`) with a
  note in the prose if the linter output was itself evidence; `sorry`-scaffold induction
  branches you are not demonstrating. Target ≲ 40 guard lines.

## Pitfalls (all cost real time once)

- `convert`/`congr` roll back failed branches (`commitWhen`) and **discard their traces** —
  the substantive ❌ appears only when you trace the *follow-up* tactic (usually the closing
  `simp`).
- `trace_state` always triggers the `unusedTactic` "does nothing" warning; it does not mean
  the goal list is empty.
- Compile single files from the repo root:
  `lake env lean -DmaxSynthPendingDepth=3 -Dpp.unicode.fun=true -Dbackward.isDefEq.instanceTypes=markOrSynth <file>`
  — never `lake build`, and never from another working directory. The mode flag is NOT optional:
  bare `lake env lean` runs the register default `"mark"`, not the lakefile's `"markOrSynth"`,
  and the same site can fail under both modes *for different reasons*. Demos written into files
  pin `set_option backward.isDefEq.instanceTypes "markOrSynth"` for the same reason.
- The `diagnostics`-mode "Workaround: …" messages for the fallback paths are emitted inside
  `checkpointDefEq` (and often inside simp's speculative `tryResolve`) and get rolled back —
  they usually never surface. Identify the failing path from the trace-tree shape instead: a
  successful `[Meta.synthInstance] … result <inst>` child nested under a ❌
  `Meta.isDefEq.assign.checkTypes` node means synthesis succeeded and the candidate-vs-
  synthesized comparison failed.
- Error positions in long `have`/`suffices` chains are easy to misattribute — read the probe
  file at the reported line instead of guessing which tactic failed.
- When replicating a `private` declaration in a probe, carry over *all* of the original site's
  `set_option`s — elaboration can diverge wildly with a partial option set.

## Style

- Complete sentences, no arrow-chain shorthand in prose (arrows are fine inside quoted traces).
- Cross-references cite files, not survey-internal category letters.
- The demo section is named (`section InstanceTypesDemos`) and self-contained, so it can be
  deleted wholesale once the underlying issue is fixed upstream.
