/-
Copyright (c) 2026 <names>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <names>
-/
module

public import Mathlib.Topology.Algebra.OrbitSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Manifold structure on orbit spaces

Let `G` be a group acting properly discontinuously on a manifold `M`.
In this file we endow the orbit space `orbitRel.Quotient G M`
with a manifold structure modeled on the same model space as `M`.

## Main results

Let `M` be a topological manifold modeled on `I : ModelWithCorners 𝕜 E H`.
Assume:

* `G` acts on `M`
* the action is properly discontinuous
* the quotient map `Quotient.mk : M → orbitRel.Quotient G M`
  is a covering map

Then:

* `orbitRel.Quotient G M` inherits a `ChartedSpace H` structure.

## TO-DO

* show that the quotient is an `IsManifold I n`
* show smoothness of the projection map

## Implementation notes

The atlas is obtained by composing a local inverse of the quotient map
(from covering theory) with a chart of `M`
-/

@[expose] public section

noncomputable section

open scoped Manifold
open MulAction QuotientMk

variable {M : Type*} [TopologicalSpace M]
variable {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]
variable {H : Type*} [TopologicalSpace H]
variable [ChartedSpace H M]

/-!
## Charted space structure on the orbit space
-/

/-- The orbit space of a properly discontinuous group action on a
manifold inherits a `ChartedSpace` structure modeled on the same space. -/
instance : ChartedSpace H (orbitRel.Quotient G M) where
  atlas := {(localInverseAt q.out).trans (chartAt H q.out) | q : orbitRel.Quotient G M}
  chartAt := fun q => (localInverseAt q.out).trans (chartAt H q.out)
  mem_chart_source q := by
    simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialEquiv.trans_source, OpenPartialHomeomorph.toFun_eq_coe,
      Set.mem_inter_iff, Set.mem_preimage]
    set p := q.out
    rw [← q.out_eq, localInverseAt_apply_self]
    exact ⟨mem_localInverseAt_source, mem_chart_source H p⟩
  chart_mem_atlas := by simp

end


/- We will need this later for the IsManifold part
--variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
--variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
--variable (I : ModelWithCorners 𝕜 E H)
--variable {n : ℕ∞} [IsManifold I n M]
-/
