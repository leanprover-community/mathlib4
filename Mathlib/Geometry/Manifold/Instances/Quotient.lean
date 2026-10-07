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

variable {x : orbitRel.Quotient G M}

variable (x) in
/-- A choice of local section of the quotient map `M → orbitRel.Quotient G M` around `x`. -/
@[to_additive
/-- A choice of local section of the quotient map `M → orbitRel.Quotient G M` around `x`. -/]
abbrev localInverseAt : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.localInverseAt x.out

@[to_additive]
lemma localInverseAt_apply_mk_eq_smul {g : G} {m : M} (hm : g • m ∈ (x.localInverseAt).target) :
    x.localInverseAt ⟦m⟧ = g • m := by
  rw [← orbitRel.Quotient.quotient_smul_eq (g := g),
    ← isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.localInverseAt_symm,
    (x.localInverseAt).right_inv hm]

/-- On the open set `(g • ·) ⁻¹' (y.localInverseAt).target`, the section comparison
`(x.localInverseAt).symm.trans (y.localInverseAt)` is the action of `g`. -/
@[to_additive /-- On the open set `(g +ᵥ ·) ⁻¹' (y.localInverseAt).target`, the section comparison
`(x.localInverseAt).symm.trans (y.localInverseAt)` is the additive action of `g`. -/]
lemma localInverseAt_symm_trans_eqOn_smul (x y : orbitRel.Quotient G M) (g : G) :
    ((g • ·) ⁻¹' (y.localInverseAt).target).EqOn
      ((x.localInverseAt).symm.trans (y.localInverseAt)) (g • ·) := by
  intro _ hm
  simpa using localInverseAt_apply_mk_eq_smul hm

/-- If `⟦m⟧` is in the source of `x.localInverseAt`, then there is some `g ∈ G` such that
`g • m` lies in the target of `x.localInverseAt`. -/
@[to_additive /-- If `⟦m⟧` is in the source of `x.localInverseAt`, then there is some `g ∈ G` such
that `g +ᵥ m` lies in the target of `x.localInverseAt`. -/]
def foo {m : M} (hm : (⟦m⟧ : orbitRel.Quotient G M) ∈ (x.localInverseAt).source) : G :=
  Classical.choose <| orbitRel_apply.mp (Quotient.exact
    (isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.apply_localInverseAt_of_mem hm))

@[to_additive]
lemma foo_spec {m : M} (hm : (⟦m⟧ : orbitRel.Quotient G M) ∈ (x.localInverseAt).source) :
    (foo hm) • m =
      (isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul (G := G)).localInverseAt
        x.out ⟦m⟧ :=
  Classical.choose_spec <| orbitRel_apply.mp (Quotient.exact
    (isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.apply_localInverseAt_of_mem hm))

@[to_additive]
lemma bar {m : M}
    (hm : (⟦m⟧ : orbitRel.Quotient G M) ∈ (x.localInverseAt).source) :
    (foo hm) • m ∈ (x.localInverseAt).target := by
  simpa [foo_spec hm] using (x.localInverseAt).map_source hm

/-!
## Transition maps between charts
-/

variable (x y : orbitRel.Quotient G M)

/-- The transition map between the charts of the quotient associated to `x` and `y`. -/
@[to_additive
/-- The transition map between the charts of the quotient associated to `x` and `y`. -/]
def transitionMap : OpenPartialHomeomorph H H :=
  (chartAt H x.out).symm ≫ₕ ((x.localInverseAt).symm ≫ₕ y.localInverseAt) ≫ₕ chartAt H y.out

/-- Wherever `g` carries a point of `M` into the target of the local section at `y`, the transition
map of the quotient is just the action of `g`, read in the charts of `M` at `x.out` and `y.out`. -/
@[to_additive /-- Wherever `g` carries a point of `M` into the range of the local section at `y`,
the transition map of the quotient is just the additive action of `g`, read in the charts of `M`
at `x.out` and `y.out`. -/]
lemma transitionMap_eqOn_smul (g : G) : Set.EqOn (transitionMap x y)
    ((chartAt H x.out).symm ≫ₕ (Homeomorph.smul g).toOpenPartialHomeomorph ≫ₕ chartAt H y.out)
    ((chartAt H x.out).symm ⁻¹' ((g • ·) ⁻¹' (y.localInverseAt).target)) := by
  intro _ hh
  simpa [transitionMap] using
    congr((chartAt H y.out) $(localInverseAt_symm_trans_eqOn_smul x y g hh))

variable {x y : orbitRel.Quotient G M} in
@[to_additive]
lemma hoge {h : H} (hh : h ∈ (transitionMap x y).source) :
    ⟦(chartAt H (Quotient.out x)).symm h⟧ ∈ y.localInverseAt.source := by
  simp only [transitionMap, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
    isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul.localInverseAt_symm] at hh
  exact hh.2.1.2

end orbitRel.Quotient

/-!
## Smooth manifold structure on quotient by a smooth action
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) {n : ℕ∞ω} [IsManifold I n M]

open orbitRel.Quotient

/-- The quotient of a Cⁿ manifold by a free, properly discontinuous group action such that the
scalar multiplication `fun x : M ↦ g • x` is Cⁿ is itself a Cⁿ manifold, for the charts of
`MulAction.instChartedSpaceQuotient`. -/
@[to_additive /-- The quotient of a Cⁿ manifold by a free, properly discontinuous additive group
action such that the translation `fun x : M ↦ g +ᵥ x` is Cⁿ is itself a Cⁿ manifold, for the charts
of `AddAction.instChartedSpaceQuotient`. -/]
instance isManifold_quotient_of_contMDiffConstSMul [ContMDiffConstSMul I n G M] :
    IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [(localInverseAt x).trans_symm_eq_symm_trans_symm, (chartAt H x.out).symm.trans_assoc,
      ← (localInverseAt x).symm.trans_assoc]
    apply StructureGroupoid.locality
    intro _ hh
    have hto : IsOpen ((chartAt H x.out).symm.source ∩
        (chartAt H x.out).symm ⁻¹' ((foo (hoge hh) • ·) ⁻¹' (localInverseAt y).target)) :=
      (chartAt H x.out).symm.isOpen_inter_preimage
        ((localInverseAt y).open_target.preimage (continuous_const_smul (foo (hoge hh))))
    refine ⟨_, hto, ⟨hh.1, bar (hoge hh)⟩, ?_⟩
    refine StructureGroupoid.restr_mem_of_eqOn (symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
      (IsManifold.chart_mem_maximalAtlas x.out) (IsManifold.chart_mem_maximalAtlas y.out) ?_ ?_)
      hto ((transitionMap_eqOn_smul x y (g := foo (hoge hh))).mono Set.inter_subset_right).symm ?_
    · rw [Homeomorph.toOpenPartialHomeomorph_apply]
      exact (ContMDiffConstSMul.contMDiff_const_smul (foo (hoge hh))).contMDiffOn
    · rw [Homeomorph.toOpenPartialHomeomorph_symm_apply]
      exact (ContMDiffConstSMul.contMDiff_const_smul (foo (hoge hh))⁻¹).contMDiffOn
    · rintro h' ⟨⟨hQ1, _, hQ4⟩, _, hh'⟩
      refine ⟨hQ1, Set.mem_univ _, ?_⟩
      simpa [← localInverseAt_symm_trans_eqOn_smul x y (foo (hoge hh)) hh'] using hQ4

end MulAction

end
