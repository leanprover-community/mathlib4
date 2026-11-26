/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.IsManifold.ContMDiffTransitions
public import Mathlib.Topology.Covering.Quotient

/-!
# Quotients of manifolds

This file contains results about quotients of manifolds by group actions.

## Main results

* `MulAction.instChartedSpaceQuotient`: a choice of charted space structure on the quotient of a
  charted space by a free, properly-discontinuous group action.

## TODO

* if `G` acts smoothly, the quotient is an `IsManifold I n` for a suitable `ModelWithCorners I`.
* if `G` acts smoothly, the projection map is smooth

## Tags

smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

open scoped ContDiff

namespace MulAction

variable {M : Type*} [TopologicalSpace M] {G : Type*} [Group G] [MulAction G M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [ContMDiffConstSMul I n G M]

/-!
## `C^n` transitions of the quotient map
-/

/-- For a group action such that the scalar multiplication `fun p : M ↦ g • p` is `C^n`, the
quotient map `M → orbitRel.Quotient G M` satisfies `ContMDiffTransitions`. -/
@[to_additive /-- For an additive group action such that the translation `fun p : M ↦ g +ᵥ p` is
`C^n`, the quotient map `M → orbitRel.Quotient G M` satisfies `ContMDiffTransitions`. -/]
lemma contMDiffTransitions_quotientMk_of_contMDiffConstSMul :
    ContMDiffTransitions I n (Quotient.mk (orbitRel G M)) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (Quotient.exact hxy.symm)
  refine ⟨(g • ·), rfl, (contMDiff_const_smul g).contMDiffAt, .of_eq ?_⟩
  ext z
  exact Quotient.sound (mem_orbit z g)

/-!
## Charted space structure on quotient by a group
-/

variable [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]

/-- The induced charted space structure on the quotient of a charted space by a free, properly
discontinuous group action. -/
@[to_additive /-- The induced charted space structure on the quotient of a charted space by a free,
properly discontinuous additive group action. -/]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective

end MulAction
