/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Topology.Covering.Quotient

/-!
# Quotients of manifolds

This file contains results about quotients of manifolds by group actions.

## Main results

* `MulAction.instChartedSpaceQuotient`: a choice of charted space structure on the quotient of a
  charted space by a free, properly discontinuous group action.
* `MulAction.isManifold_quotient_of_contMDiffConstSMul`: if, additionally, the action is `C^n`,
  the quotient is a `C^n` manifold.

## TODO

* if the action is free, properly discontinuous and `C^n`, the projection `M → M⧸G` is `C^n`.

## Tags

smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

open scoped ContDiff Manifold

namespace MulAction

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

/-!
## Charted space structure on quotient by a group
-/

/-- The induced charted space structure on the quotient of a charted space by a free, properly
discontinuous group action. -/
@[to_additive /-- The induced charted space structure on the quotient of a charted space by a free,
properly discontinuous additive group action. -/]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.chartedSpaceOfRightInverse
    Quotient.out_eq

namespace orbitRel.Quotient

/-!
## Local sections of the quotient map
-/

variable {p q : orbitRel.Quotient G M}

variable (p) in
/-- A choice of local section of the quotient map `M → orbitRel.Quotient G M` around `p`. -/
@[to_additive
/-- A choice of local section of the quotient map `M → orbitRel.Quotient G M` around `p`. -/]
abbrev localInverseAt : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.localInverseAt p.out

@[to_additive]
lemma localInverseAt_apply_mk_eq_smul {g : G} {m : M} (hm : g • m ∈ (p.localInverseAt).target) :
    p.localInverseAt ⟦m⟧ = g • m := by
  rw [← quotient_smul_eq (g := g),
    ← isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.localInverseAt_symm,
    (p.localInverseAt).right_inv hm]

variable (p q) in
/-- On the open set `(g • ·) ⁻¹' (q.localInverseAt).target`, the section comparison
`(p.localInverseAt).symm.trans (q.localInverseAt)` is the action of `g`. -/
@[to_additive /-- On the open set `(g +ᵥ ·) ⁻¹' (q.localInverseAt).target`, the section comparison
`(p.localInverseAt).symm.trans (q.localInverseAt)` is the additive action of `g`. -/]
lemma localInverseAt_symm_trans_eqOn_smul (g : G) :
    ((g • ·) ⁻¹' (q.localInverseAt).target).EqOn
      ((p.localInverseAt).symm.trans (q.localInverseAt)) (g • ·) := by
  intro _ hm
  simpa using localInverseAt_apply_mk_eq_smul hm

/-- If `⟦m⟧` is in the source of `p.localInverseAt`, then there is some `g ∈ G` such that
`g • m` lies in the target of `p.localInverseAt`. -/
@[to_additive /-- If `⟦m⟧` is in the source of `p.localInverseAt`, then there is some `g ∈ G` such
that `g +ᵥ m` lies in the target of `p.localInverseAt`. -/]
lemma exists_smul_mem_localInverseAt_target {m : M} (hm : ⟦m⟧ ∈ p.localInverseAt.source) :
    ∃ g : G, g • m ∈ (p.localInverseAt).target := by
  obtain ⟨g, hg⟩ := orbitRel_apply.mp (Quotient.exact
    (isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.apply_localInverseAt_of_mem hm))
  use g
  simpa [hg] using (p.localInverseAt).map_source hm

/-!
## Transition maps between charts
-/

variable (p q) in
/-- The transition map between the charts of the quotient associated to `p` and `q`. -/
@[to_additive
/-- The transition map between the charts of the quotient associated to `p` and `q`. -/]
def transitionMap : OpenPartialHomeomorph H H :=
  (chartAt H p.out).symm ≫ₕ ((p.localInverseAt).symm ≫ₕ q.localInverseAt) ≫ₕ chartAt H q.out

variable (p q) in
/-- Wherever `g` carries a point of `M` into the target of the local section at `q`, the transition
map of the quotient is just the action of `g`, read in the charts of `M` at `p.out` and `q.out`. -/
@[to_additive /-- Wherever `g` carries a point of `M` into the target of the local section at `q`,
the transition map of the quotient is just the additive action of `g`, read in the charts of `M`
at `p.out` and `q.out`. -/]
lemma transitionMap_eqOn_smul (g : G) : Set.EqOn (transitionMap p q)
    ((chartAt H p.out).symm ≫ₕ (Homeomorph.smul g).toOpenPartialHomeomorph ≫ₕ chartAt H q.out)
    ((chartAt H p.out).symm ⁻¹' ((g • ·) ⁻¹' (q.localInverseAt).target)) := by
  intro _ hx
  simpa [transitionMap] using
    congr((chartAt H q.out) $(localInverseAt_symm_trans_eqOn_smul p q g hx))

@[to_additive]
lemma mk_chartAt_symm_mem_localInverseAt_source {x : H} (hx : x ∈ (transitionMap p q).source) :
    ⟦(chartAt H p.out).symm x⟧ ∈ q.localInverseAt.source := by
  simp only [transitionMap, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
    isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.localInverseAt_symm] at hx
  exact hx.2.1.2

end orbitRel.Quotient

/-!
## Smooth manifold structure on quotient by a smooth action
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]

open orbitRel.Quotient IsManifold

variable (I) in
/-- The quotient of a `C^n` manifold by a free, properly discontinuous group action such that the
scalar multiplication `fun m : M ↦ g • m` is `C^n` is itself a `C^n` manifold, for the charts of
`MulAction.instChartedSpaceQuotient`. -/
@[to_additive /-- The quotient of a `C^n` manifold by a free, properly discontinuous additive group
action such that the translation `fun m : M ↦ g +ᵥ m` is `C^n` is itself a `C^n` manifold, for the
charts of `AddAction.instChartedSpaceQuotient`. -/]
instance isManifold_quotient_of_contMDiffConstSMul [ContMDiffConstSMul I n G M] :
    IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    rw [(localInverseAt p).trans_symm_eq_symm_trans_symm, (chartAt H p.out).symm.trans_assoc,
      ← (localInverseAt p).symm.trans_assoc]
    apply StructureGroupoid.locality
    intro x hx
    obtain ⟨g, hg⟩ :=
      exists_smul_mem_localInverseAt_target (mk_chartAt_symm_mem_localInverseAt_source hx)
    let t := ((chartAt H p.out).symm.source ∩ (chartAt H p.out).symm ⁻¹'
      ((g • ·) ⁻¹' (localInverseAt q).target))
    have ht : IsOpen t := (chartAt H p.out).symm.isOpen_inter_preimage <|
      (localInverseAt q).open_target.preimage (continuous_const_smul _)
    refine ⟨t, ht, ⟨hx.1, hg⟩, ?_⟩
    refine StructureGroupoid.restr_mem_of_eqOn (symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
      (chart_mem_maximalAtlas p.out) (chart_mem_maximalAtlas q.out) ?_ ?_) ht
      ((transitionMap_eqOn_smul p q g).mono Set.inter_subset_right).symm ?_
    · rw [Homeomorph.toOpenPartialHomeomorph_apply]
      exact (ContMDiffConstSMul.contMDiff_const_smul g).contMDiffOn
    · rw [Homeomorph.toOpenPartialHomeomorph_symm_apply]
      exact (ContMDiffConstSMul.contMDiff_const_smul g⁻¹).contMDiffOn
    · rintro y ⟨⟨hy₁, _, hy₂⟩, _, hy₃⟩
      refine ⟨hy₁, Set.mem_univ _, ?_⟩
      simpa [← localInverseAt_symm_trans_eqOn_smul p q g hy₃] using hy₂

end MulAction

end
