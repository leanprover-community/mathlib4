/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option linter.tacticCheckInstances true

public noncomputable section

open IsManifold
open scoped ContDiff

lemma ContMDiffSMul.contMDiff_const_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {H' E' : Type*} [TopologicalSpace H'] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {I' : ModelWithCorners 𝕜 E' H'}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [SMul G M] {n : ℕ∞ω} [ContMDiffSMul I I' n G M] (g : G) :
  ContMDiff I' I' n fun (x : M) ↦ g • x := sorry

namespace MulAction

variable {M : Type*} [TopologicalSpace M]
  {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  {H : Type*} [TopologicalSpace H] [ChartedSpace H M]

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞}

/-- If `h` is an open partial homeomorphism of `M` that is `C^n` on its source, with `C^n`
inverse on its target, then reading `h` through two members of the maximal atlas yields an
element of `contDiffGroupoid n I`. -/
lemma symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M)
    {h : OpenPartialHomeomorph M M}
    (hh : ContMDiffOn I I n h h.source) (hhsymm : ContMDiffOn I I n h.symm h.target) :
    e.symm.trans (h.trans e') ∈ contDiffGroupoid n I := by
  sorry

end

variable [T2Space M] [LocallyCompactSpace M]

/- alternative instance
@[to_additive]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective -/

instance instChartedSpaceQuotient' : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpaceOfRightInverse Quotient.out_eq

lemma quotient_IsLocalHomeomorph : IsLocalHomeomorph (Quotient.mk (orbitRel G M)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.isLocalHomeomorph

variable (x y : orbitRel.Quotient G M)

-- should this be deleted??
/-- A choice of local section of the quotient map `M → orbitRel.Quotient G M` around `x`. -/
abbrev πinv : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  quotient_IsLocalHomeomorph.localInverseAt (Y := orbitRel.Quotient G M) x.out

variable {x} in
/-- If `g • m` is in the target of `πinv x`, then `πinv x ⟦m⟧` is just `g • m`. -/
lemma πinv_mk_eq_smul {g : G} {m : M} (hm : g • m ∈ (πinv x).target) :
    πinv x ⟦m⟧ = g • m := by
  sorry

/-- Locally, the comparison of two local sections is the action of a single group element. -/
lemma locally_smul (m : M) (hm : m ∈ ((πinv x).symm.trans (πinv y)).source) :
    ∃ g : G, m ∈ (g • ·) ⁻¹' (πinv y).target ∧
      ((g • ·) ⁻¹' (πinv y).target).EqOn ((πinv x).symm.trans (πinv y)) (g • ·)  := by
  sorry

/-- The transition map between the charts of the quotient associated to `x` and `y`. -/
def quotientTransitionMap : OpenPartialHomeomorph H H :=
  (chartAt H x.out).symm.trans (((πinv x).symm.trans (πinv y)).trans (chartAt H y.out))

/-- Locally, the transition map of the quotient is `φ x⁻¹ ≫ (g • ·) ≫ φ y` for a single group
element `g`. -/
lemma quotientTransitionMap_locally_smul {h : H} (hh : h ∈ (quotientTransitionMap x y).source) :
    ∃ g : G, h ∈ (chartAt H x.out).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target) ∧
      ((chartAt H x.out).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target)).EqOn
        (quotientTransitionMap x y)
        ((chartAt H x.out).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans
          (chartAt H y.out))) := by
  sorry

variable {x y : orbitRel.Quotient G M}

section

-- move this

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : OpenPartialHomeomorph X Y}

theorem OpenPartialHomeomorph.restr_eqOnSource_of_eqOn
    {e e' : OpenPartialHomeomorph X Y} {s : Set X} (hs : IsOpen s)
    (heq : s.EqOn e e') (hsub : e.source ∩ s ⊆ e'.source) :
    e.restr s ≈ e'.restr (e.source ∩ s) := by
  sorry

lemma StructureGroupoid.restr_mem_of_eqOn {G : StructureGroupoid X}
    [ClosedUnderRestriction G] {e e' : OpenPartialHomeomorph X X} {s : Set X}
    (he' : e' ∈ G) (hs : IsOpen s) (heq : s.EqOn e e') (hsub : e.source ∩ s ⊆ e'.source) :
    e.restr s ∈ G :=
  sorry

end

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) {n : ℕ∞} [IsManifold I n M]
variable {HG : Type*} [TopologicalSpace HG] [TopologicalSpace G] [ChartedSpace HG G]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] (IG : ModelWithCorners 𝕜 EG HG)
  [ContMDiffSMul IG I n G M]

/--
error: cannot find synthesization order for instance @foo with type
  ∀ {M : Type u_1} [inst : TopologicalSpace M] {G : Type u_2} [inst_1 : Group G] [inst_2 : MulAction G M]
    [inst_3 : ProperlyDiscontinuousSMul G M] [inst_4 : ContinuousConstSMul G M] [inst_5 : IsCancelSMul G M]
    {H : Type u_3} [inst_6 : TopologicalSpace H] [inst_7 : ChartedSpace H M] [inst_8 : T2Space M]
    [inst_9 : LocallyCompactSpace M] {𝕜 : Type u_4} [inst_10 : NontriviallyNormedField 𝕜] {E : Type u_5}
    [inst_11 : NormedAddCommGroup E] [inst_12 : NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H) {n : ℕ∞}
    [IsManifold I (↑n) M] {HG : Type u_6} [inst_14 : TopologicalSpace HG] [inst_15 : TopologicalSpace G]
    [inst_16 : ChartedSpace HG G] {EG : Type u_7} [inst_17 : NormedAddCommGroup EG] [inst_18 : NormedSpace 𝕜 EG]
    (IG : ModelWithCorners 𝕜 EG HG) [ContMDiffSMul IG I (↑n) G M], IsManifold I (↑n) (orbitRel.Quotient G M)
all remaining arguments have metavariables:
  TopologicalSpace ?HG
  @ChartedSpace ?HG ?inst✝ G inst✝⁴
  NormedAddCommGroup ?EG
  @NormedSpace 𝕜 ?EG inst✝⁹.toNormedField NormedAddCommGroup.toSeminormedAddCommGroup
  @ContMDiffSMul 𝕜 inst✝⁹ ?HG ?inst✝ ?EG ?inst✝¹ ?inst✝² ?IG H inst✝¹³ E inst✝⁸ inst✝⁷ I (↑n) G inst✝⁴ ?inst✝³ M inst✝¹⁹
    inst✝¹² inst✝¹⁷.toSMul
---
warning: declaration uses `sorry`
-/
#guard_msgs in
instance foo : IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [(πinv x).trans_symm_eq_symm_trans_symm, (chartAt H x.out).symm.trans_assoc,
      ← (πinv x).symm.trans_assoc]
    apply StructureGroupoid.locality
    intro h hh
    obtain ⟨g0, hg0, hg0'⟩ := quotientTransitionMap_locally_smul x y hh
    have hto : IsOpen ((chartAt H x.out).symm.source ∩
        (chartAt H x.out).symm ⁻¹' ((g0 • ·) ⁻¹' (πinv y).target)) :=
      (chartAt H x.out).symm.isOpen_inter_preimage
        ((πinv y).open_target.preimage (continuous_const_smul g0))
    refine ⟨_, hto, ⟨hh.1, hg0⟩, ?_⟩
    refine StructureGroupoid.restr_mem_of_eqOn (symm_trans_trans_mem_contDiffGroupoid_of_contMDiffOn
      (IsManifold.chart_mem_maximalAtlas x.out) (IsManifold.chart_mem_maximalAtlas y.out) ?_ ?_)
      hto (hg0'.mono Set.inter_subset_right) ?_
    · rw [Homeomorph.toOpenPartialHomeomorph_apply]
      apply ContMDiff.contMDiffOn
      -- This line causes the error!
      apply ContMDiffSMul.contMDiff_const_smul (I := IG)
      -- This version also causes an error
      -- apply (Diffeomorph.smul IG I n g0 (M := M)).contMDiff_toFun
    · sorry
    · sorry

end MulAction

end
