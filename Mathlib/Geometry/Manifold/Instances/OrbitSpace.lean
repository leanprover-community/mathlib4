/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Algebra.OrbitSpace

/-!
# Manifold structure on orbit spaces

Let `G` be a group acting freely and properly discontinuously on a `C^k` manifold `M`.
In this file we will endow the orbit space `orbitRel.Quotient G M`
with a natural `C^k` manifold structure, on the same model space as `M`.

## Main results

Let `M` be a topological space equipped with a `ChartedSpace H M` structure.
Assume that a group `G` acts properly discontinuously on `M`.
Then the orbit space `orbitRel.Quotient G M` inherits a `ChartedSpace H` structure.

## TODO

* if `G` acts smoothly, the quotient is an `IsManifold I n` for a suitable `ModelWithCorners I`.
* if `G` acts smoothly, the projection map is smooth

## tags
smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

open MulAction QuotientMk

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

/-!
## Charted space structure on the orbit space
-/

/-- The orbit space of a properly discontinuous group action on a manifold inherits a
`ChartedSpace` structure modeled on the same space. -/
instance : ChartedSpace H (orbitRel.Quotient G M) where
  atlas := {(localInverseAt G q.out).trans (chartAt H q.out) | q : orbitRel.Quotient G M}
  chartAt q := (localInverseAt G q.out).trans (chartAt H q.out)
  mem_chart_source q := by
    simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialEquiv.trans_source, OpenPartialHomeomorph.toFun_eq_coe,
      Set.mem_inter_iff, Set.mem_preimage]
    set p := q.out
    rw [← q.out_eq, localInverseAt_apply_self]
    exact ⟨mem_localInverseAt_source, mem_chart_source H p⟩
  chart_mem_atlas := by simp

end
