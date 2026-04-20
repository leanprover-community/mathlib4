# Universal Cover Plan

## Summary

This directory now has the correct foundation for the universal cover construction:

- `SemilocallySimplyConnected.lean` provides the reusable tube/ladder engine, including the variable-endpoint telescoping theorem `Path.paste_segment_homotopies` and the one-sided specialization `Path.paste_segment_homotopies_slsc_source`.
- `UniversalCover.lean` provides the based-path model, the quotient topology, the projection `UniversalCover.proj`, the raw quotient/homeomorphism bookkeeping, and the compact-open proof that `BasedPath.endpoint` is an open map.

The remaining work is to turn the surviving “last rung” into a path-component statement in the based-path space, use that to prove that `UniversalCover.proj` is a covering map, and then build the path-connectedness / simply-connectedness / universal-property theorems on top.

The implementation should reuse the `#31576` machinery rather than duplicate any ladder/tube proof.

## Status on This Branch

As of commit `74ec3326354` plus the follow-up proofs completed in this worktree:

- Step 1 is implemented as `BasedPath.joinedIn_preimage_of_append`.
- Step 2 is implemented as `BasedPath.exists_open_nhd_pathComponent_preimage`.
- Step 3 is implemented as `BasedPath.isOpen_pathComponent_preimage`.
- Step 4 is implemented as `BasedPath.pathComponent_preimage_saturated`.
- Step 4b is implemented as `UniversalCover.isOpenMap_proj`.
- The quotient-saturation bridge needed by step 5 is now implemented as
  `UniversalCover.pathComponentIn_endpoint_preimage_eq_of_ofBasedPath_eq`.
- Step 5 is implemented through:
  `UniversalCover.basedPathSheet`,
  `UniversalCover.sheet`,
  `UniversalCover.preimage_sheet`,
  `UniversalCover.isOpen_sheet`,
  `UniversalCover.mem_sheet_self`.
- Step 6 is implemented via:
  `BasedPath.toPath_homotopic_of_joinedIn_slsc` (the rectangle homotopy lemma) and
  `UniversalCover.sheet_proj_injOn`. Supporting lemma
  `UniversalCover.ofBasedPath_eq_of_homotopic_toPath` bridges homotopy to `UniversalCover` equality.
- Step 7 helpers:
  `UniversalCover.sheet_surjOn`, `UniversalCover.sheet_pairwise_disjoint`,
  `UniversalCover.sheet_exhaustive`.
- Step 7 (`UniversalCover.isCoveringMap`) is implemented using
  `IsOpen.trivializationDiscrete` with the sheet family.
- Step 8 (`UniversalCover.discreteTopology_fiber`) derives from the covering-map result.
- Step 9 (`UniversalCover.pathConnectedSpace`) is implemented via the direct
  quotient-model construction `joined_basepoint_of_ofBasedPath` using the
  reparameterization `(s, t) ↦ α.1 (s * t)`.
- Step 10 (`UniversalCover.simplyConnectedSpace`) is implemented by:
  a canonical-lift computation for `IsCoveringMap.liftPath`, identifying the lift of
  `γ : Path (endpoint α) y` from `ofBasedPath α` with `ofBasedPath (append α γ)`, and then
  applying groupoid cancellation plus
  `IsCoveringMap.injective_path_homotopic_map` to show every loop in the universal cover is
  nullhomotopic.

Step 6 was completed via a direct rectangle-homotopy construction
(`BasedPath.toPath_homotopic_of_joinedIn_slsc`) rather than the globalization route
originally proposed: given `α, β` joined inside `endpoint ⁻¹' U` with the same endpoint
`v ∈ U`, we build an explicit `Path.Homotopy (α'.trans L) (β.trans (refl v))` using the
endpoint trace `L(t) = endpoint (F t)` of the joining path `F`, combine it with `L ≃ refl v`
(from `hU_slsc`), and conclude `α.toPath ≃ β.toPath` via three `trans_refl`-style steps.

The original step-10 blocker is now resolved in the explicit-lift style sketched above.

## Current Foundation

### In `SemilocallySimplyConnected.lean`

Already available and intended for reuse:

- `exists_pathConnected_slsc_neighborhood`
  Gives open path-connected neighborhoods `U` with the strong local path-uniqueness property: any two paths in `U` with the same endpoints are homotopic in `X`.
- `Path.exists_partition_in_slsc_neighborhoods`
  Gives the partition/tube setup from compactness.
- `Path.exists_rung_paths`
  Produces rung paths between partition points of two paths in the same tube.
- `Path.segment_rung_homotopy`
  Produces the rectangle homotopies inside a path-unique neighborhood.
- `Path.paste_segment_homotopies`
  The genuine variable-endpoint telescoping lemma.
- `Path.paste_segment_homotopies_slsc_source`
  Kills only the initial loop and keeps the final rung.
- `Path.paste_segment_homotopies_slsc`
  The fixed-endpoint specialization.
- `Path.tube_subset_homotopy_class`
  The fixed-endpoint tube consumer.
- `Path.Homotopic.Quotient.discreteTopology`
  Discreteness of fixed-endpoint path-homotopy quotients.

### In `UniversalCover.lean`

Already available and intended for reuse:

- `BasedPath x₀ := {γ : C(I, X) // γ 0 = x₀}`
- `BasedPath.endpoint`
- `BasedPath.toPath`, `ofPath`, `append`
- `BasedPath.terminalTail`, `deformTerminal`
- `Path.truncateOfLE_range_subset_preimage`
- `BasedPath.isOpenMap_endpoint`
- `BasedPath.joined_of_homotopic`
- `BasedPath.joinedIn_preimage_singleton_of_homotopic`
- `UniversalCover x₀ := Σ x, Path.Homotopic.Quotient x₀ x`
  with topology coinduced from `ofBasedPath`
- `UniversalCover.RawUniversalCover`
- `UniversalCover.quotientHomeomorph`
- `UniversalCover.proj`
- `UniversalCover.fiberEquiv`

These are the only foundations needed before starting the covering proof.

## Remaining Work: Covering Theorem

### 1. Add the endpoint-motion lemma in `UniversalCover.lean`

Add a theorem in the `BasedPath` namespace, with public name
`BasedPath.joinedIn_preimage_of_append`, stating:

- If `γ : BasedPath x₀`, `endpoint γ ∈ U`, and `δ : Path (endpoint γ) z` has `Set.range δ ⊆ U`, then `γ` and `append γ δ` lie in the same path component of `endpoint ⁻¹' U`.

Caveat: the naive family `t ↦ append γ (δ|[0,t])` does **not** start at `γ`. Because `append γ δ` is defined as `ofPath (γ.toPath.trans δ)`, at `t = 0` the family evaluates to `append γ (Path.refl (endpoint γ))`, which is `γ.toPath.trans refl` — only path-homotopic to `γ`, not equal. The proof therefore has two legs:

- **Leg A** (fixed endpoint): `γ` and `append γ (Path.refl (endpoint γ))` are `JoinedIn (endpoint ⁻¹' {endpoint γ})` via the standard `trans_refl` homotopy, fed through `BasedPath.joinedIn_preimage_singleton_of_homotopic`. Since `{endpoint γ} ⊆ U`, this gives `JoinedIn (endpoint ⁻¹' U)`.
- **Leg B** (moving endpoint): the family `t ↦ append γ (δ.truncate 0 t)` connects `append γ (Path.refl (endpoint γ))` (at `t = 0`) to `append γ δ` (at `t = 1`). Continuity uses `Path.truncate_continuous_family`, `Path.continuous_uncurry_iff`, `Continuous.path_trans`; endpoints lie in `U` because the endpoint at time `t` is `δ t ∈ U`.

Compose the two `JoinedIn` facts.

Note on `deformTerminal`. The file already defines `BasedPath.deformTerminal`, used by `isOpenMap_endpoint`, which also “moves the endpoint along an appended path” but additionally compresses the original `γ` so that the total reparameterization lives on `[0,1]`. It is **not** the right tool for step 1: `deformTerminal` produces a based path that reparameterizes `γ`, so using it would reintroduce the same `t = 0` mismatch. The simpler `append + truncate` construction above is deliberately chosen; do not attempt to replace it with `deformTerminal`.

### 2. Add the variable-endpoint tube/component theorem

Add a theorem, preferably in `UniversalCover.lean` in the `BasedPath` namespace, whose statement is:

- Let `hX : SemilocallySimplyConnected X` and `[LocPathConnectedSpace X]`.
- Let `U` be one of the neighborhoods produced by `exists_pathConnected_slsc_neighborhood`.
- Let `α : BasedPath x₀` with `endpoint α ∈ U`.
- Then there exists an open set `N ⊆ BasedPath x₀` such that:
  - `α ∈ N`,
  - `N ⊆ endpoint ⁻¹' U`,
  - every `β ∈ N` lies in the same path component of `endpoint ⁻¹' U` as `α`.

Implementation must reuse the existing `SemilocallySimplyConnected` machinery exactly:

- Apply `Path.exists_partition_in_slsc_neighborhoods` to `α.toPath`.
- Use the chosen neighborhood `U` only at the final overlap.
- Package the partition/tube conditions as an open set in `BasedPath x₀` by pulling back the path-space tube (which is open in `C(I, X)` by `TubeData.isOpen`) along the subtype coercion `(·).1 : BasedPath x₀ → C(I, X)`. Openness is preserved because `BasedPath x₀` carries the induced subtype topology.
- For `β` in that tube:
  - convert `β` to a path with varying endpoint,
  - obtain rungs via `Path.exists_rung_paths`,
  - obtain rectangle homotopies by the path-uniqueness property of the segment neighborhoods,
  - apply `Path.paste_segment_homotopies_slsc_source` to get `α.toPath.trans ρₙ ≃ β.toPath`,
  - use the endpoint-motion lemma from step 1 to show `α` is joined to `append α ρₙ` inside `endpoint ⁻¹' U`,
  - use `BasedPath.joinedIn_preimage_singleton_of_homotopic` to show `append α ρₙ` is joined to `β` in `endpoint ⁻¹' U`,
  - compose the two `JoinedIn` facts.

Important implementation rule:

- do not duplicate `tube_subset_homotopy_class`;
- the only new ingredient compared to the fixed-endpoint proof is that the final rung is interpreted via endpoint motion instead of being nullhomotoped away.

### 3. Prove path components of `endpoint ⁻¹' U` are open

From the theorem above, derive:

- For such a good `U`, every path component of `BasedPath.endpoint ⁻¹' U` is open.

Use:

- the standard “every point has an open neighborhood contained in its path component” argument,
- no new path-space constructions.

This should be stated explicitly as a theorem because it is the exact topological input needed for the quotient-sheet proof.

### 4. Prove path components are saturated under endpoint-preserving homotopy

Add a theorem:

- If `C` is a path component of `endpoint ⁻¹' U` and `γ ∈ C`, and `γ'` is endpoint-preserving-homotopic to `γ`, then `γ' ∈ C`.

Use the already available theorem:

- `BasedPath.joinedIn_preimage_singleton_of_homotopic`.

This is the saturation statement needed to push components through the quotient map.

### 4b. Prove `UniversalCover.proj` is an open map

Add a standalone theorem `UniversalCover.isOpenMap_proj` stating that `proj : UniversalCover x₀ → X` is an open map. The argument:

- `proj_ofBasedPath` gives `proj ∘ ofBasedPath = BasedPath.endpoint`.
- `ofBasedPath` is a surjective quotient map (`isQuotientMap_ofBasedPath`).
- For `V ⊆ UniversalCover x₀` open, `ofBasedPath ⁻¹' V` is open (quotient map), and surjectivity gives `proj V = endpoint (ofBasedPath ⁻¹' V)`, which is open by `BasedPath.isOpenMap_endpoint`.

This lemma is assumed by step 6 (sheet openness) and should exist before step 5.

### 5. Build sheets in `UniversalCover.proj ⁻¹' U`

For a fixed good neighborhood `U`, define the sheets as quotient images of path components of `endpoint ⁻¹' U`.

Do not index them abstractly by arbitrary component objects in the final theorem. Instead use the existing covering API’s preferred fiber indexing:

- For `x ∈ U`, take the fiber `proj ⁻¹' {x}` as the discrete index set.
- For `e : proj ⁻¹' {x}`, define the corresponding sheet as the set of universal-cover points represented by based paths in the same path component of `endpoint ⁻¹' U` as a chosen representative of `e`.

Implementation details:

- Pick a representative of each fiber point using `surjective_ofBasedPath`.
- Show the sheet definition is independent of representative because the component is saturated.
- Show sheets are open because components are open and saturated, and `ofBasedPath` is a quotient map.
- Show sheets are pairwise disjoint and cover `proj ⁻¹' U`.

This is the first place where quotient topology and component openness interact.

### 6. Prove each sheet maps homeomorphically to `U`

For a fixed sheet:

- Surjectivity:
  use the endpoint-motion lemma from step 1.
- Injectivity:
  if two points in the same sheet lie over the same `v ∈ U`, then a path in the component gives a homotopy through based paths whose endpoint trace is a loop in `U`, and path-uniqueness in `U` kills that loop.
- Continuity:
  inherited from `proj`.
- Openness:
  inherited from `proj` via `UniversalCover.isOpenMap_proj` (step 4b).

Conclude that the restriction `sheet → U` is a homeomorphism.

This proof should be written once in sheet form and then fed to the covering API.

### 7. Package `UniversalCover.proj` as `IsEvenlyCovered` and `IsCoveringMap`

Add:

- `theorem UniversalCover.isEvenlyCovered_at`
- `theorem UniversalCover.isCoveringMap`

Preferred shape:

- `isEvenlyCovered_at`: for each `x : X`, choose `U` from `exists_pathConnected_slsc_neighborhood hX x`, build the sheet family indexed by `proj ⁻¹' {x}`, and apply `IsOpen.trivializationDiscrete` from `Topology.Covering.Basic`.
- `isCoveringMap`: conclude by `isCoveringMap_iff_isCoveringMapOn_univ` or directly via `IsCoveringMapOn.mk`.

Do not build a bespoke covering-space notion. Use `Topology.Covering.Basic` throughout.

### 8. Fiber discreteness theorem

After `isCoveringMap`, add a short theorem:

- `DiscreteTopology (UniversalCover.Fiber x₀ x)`.

Preferred proof: derive directly from `UniversalCover.isCoveringMap`, since a covering map has discrete fibers by the trivialization. This is the cleanest route and requires no new topological bridges.

The bare `fiberEquiv` is **not** sufficient on its own for this: it is an `Equiv`, not a `Homeomorph`, so `DiscreteTopology` does not transport across it automatically. If one wanted to go through the existing `Path.Homotopic.Quotient.discreteTopology`, one would first need to upgrade `fiberEquiv` to a homeomorphism (by checking that the subtype topology on `Fiber x₀ x` coincides with the discrete topology on `Path.Homotopic.Quotient x₀ x`), which is strictly more work than invoking the covering-map result.

This theorem is exposed because it validates that the fiber model matches the original `#31576` result, not because it is needed for the covering proof itself.

## Remaining Work: Path-Connectedness and Simply Connectedness

### 9. Prove `PathConnectedSpace (UniversalCover x₀)`

Preferred route:

- Use the quotient model directly.
- For `z : UniversalCover x₀`, choose a based-path representative `γ`.
- Connect the basepoint class `ofBasedPath x₀ (BasedPath.ofPath (Path.refl x₀))` to `z` by the path of initial subpaths of `γ`.

Implementation shape:

- Define a continuous map `I → BasedPath x₀` by `t ↦ BasedPath.ofPath ((γ.toPath.subpathOn 0 t).cast toPath_source rfl)`. The cast is at the **source**: `γ.toPath.subpathOn 0 t : Path (γ.toPath 0) (γ.toPath t)` has propositional source `x₀` via `toPath_source`, not definitional. The target is already `γ.toPath t`, which `ofPath` accepts as the implicit endpoint with no cast.
- Descend that path through `ofBasedPath`.
- Show the resulting path starts at the basepoint class and ends at `z`.

If dependent casts make this too awkward, an acceptable backup is:

- first prove `UniversalCover.isCoveringMap`,
- then use path lifting from the path-connected base `X` to construct connecting paths upstairs.

But the quotient-model path is preferred because it is more direct and keeps the universal-cover construction self-contained.

### 10. Prove `SimplyConnectedSpace (UniversalCover x₀)`

Use the covering-map lifting API, not a bespoke quotient-space proof.

Preferred route:

- Use `UniversalCover.isCoveringMap`.
- Show any loop in `UniversalCover x₀` projects to a loop in `X`.
- Use uniqueness of lifts and the canonical path-space description of points of `UniversalCover` to show that a loop upstairs has trivial endpoint effect and is nullhomotopic.
- Then conclude `SimplyConnectedSpace (UniversalCover x₀)` via the existing characterization in mathlib.

If the loop-nullhomotopy route is awkward, an equivalent acceptable route is:

- use `simply_connected_iff_paths_homotopic'`,
- show any two paths upstairs with the same endpoints have the same projection behavior and therefore coincide up to homotopy by lift uniqueness.

Key rule:

- reuse `Topology.Homotopy.Lifting`;
- do not add a second ad hoc lifting theory in `UniversalCover.lean`.

### 11. State the universal property as thin wrappers

After `isCoveringMap` and `SimplyConnectedSpace` are available, add thin wrappers for the usual universal-cover lifting property.

Preferred theorem shape:

- a theorem saying maps from a simply connected space into `X` lift uniquely to `UniversalCover x₀` after choosing a lift of one basepoint.

Implementation should directly reuse the generic theorem:

- `IsCoveringMap.existsUnique_continuousMap_lifts`
  or the closest existing lifting theorem in `Topology.Homotopy.Lifting`.

Do not prove existence/uniqueness from scratch.

## Public API To Add

### In `UniversalCover.lean`

Add the following public theorems in roughly this order:

- `BasedPath.joinedIn_preimage_of_append` (step 1)
- `BasedPath.exists_open_neighborhood_subset_pathComponent_preimage` (step 2)
  or a better but equally explicit name for the variable-endpoint tube/component theorem
- `BasedPath.isOpen_pathComponent_preimage` (step 3)
- `BasedPath.pathComponent_preimage_saturated` (step 4)
- `UniversalCover.isOpenMap_proj` (step 4b)
- `UniversalCover.isEvenlyCovered_at` (step 7)
- `UniversalCover.isCoveringMap` (step 7)
- `UniversalCover.discreteTopology_fiber` (step 8)
- `UniversalCover.pathConnectedSpace` (step 9)
- `UniversalCover.simplyConnectedSpace` (step 10)
- `UniversalCover.existsUnique_continuousMap_lifts` (step 11 wrapper)

The exact names can be adjusted to fit house style, but the theorem boundaries above should not be collapsed together. Each is a useful reuse point.

## Tests and Acceptance Criteria

The implementation is complete when all of the following hold.

### Build checks

- `lake build Mathlib.AlgebraicTopology.FundamentalGroupoid.SemilocallySimplyConnected`
- `lake build Mathlib.AlgebraicTopology.FundamentalGroupoid.UniversalCover`
- `lake build Mathlib`

### Theorem-level acceptance

- `BasedPath.isOpenMap_endpoint` remains green.
- There is a theorem proving endpoint-motion inside `U` gives a path in `endpoint ⁻¹' U`.
- There is a theorem proving path components of `endpoint ⁻¹' U` are open for good `U`.
- `UniversalCover.isCoveringMap` is proved under:
  `PathConnectedSpace X`, `LocPathConnectedSpace X`, `SemilocallySimplyConnected X`.
- `UniversalCover.fiberEquiv` together with `Path.Homotopic.Quotient.discreteTopology`
  gives the fiber discreteness theorem.
- `PathConnectedSpace (UniversalCover x₀)` is proved.
- `SimplyConnectedSpace (UniversalCover x₀)` is proved.
- The universal lifting statement is a thin wrapper over existing covering-map lifting API.

## Assumptions and Defaults

- The public `UniversalCover` type remains `Σ x : X, Path.Homotopic.Quotient x₀ x` with topology coinduced from `ofBasedPath`.
- The raw quotient remains an internal proof model exposed via `quotientHomeomorph`.
- The variable-endpoint component theorem belongs in `UniversalCover.lean`, not back in `SemilocallySimplyConnected.lean`, because it is about the based-path-space topology rather than just path homotopy.
- No scratch files should survive in the final branch; once the append-motion theorem is finished, its proof should be moved directly into `UniversalCover.lean`.
- The current one-line `subpathOn` cleanup in `SemilocallySimplyConnected.lean` is treated as part of the stack foundation if needed for the build here.
