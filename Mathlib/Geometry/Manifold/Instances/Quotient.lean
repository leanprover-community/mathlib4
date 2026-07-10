/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Quotients of manifolds

This file contains results about quotients of manifolds by group actions.

## Main results

* `MulAction.instChartedSpaceQuotient`: a choice of charted space structure on the quotient of a
  charted space by a free, properly-discontinuous group action.

## TODO

* if `G` acts smoothly, the quotient is an `IsManifold I n` for a suitable `ModelWithCorners I`.
* if `G` acts smoothly, the projection map is smooth

## tags
smooth manifold, smooth action, quotient manifold
-/

public noncomputable section

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
@[to_additive]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective

-- maybe we should change the ChartedSpace instance to this
--(so we can use x.out and delete the right inverse choice)
instance instChartedSpaceQuotient' : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpaceOfRightInverse Quotient.out_eq


/-
TO-DO:
* Move new results into the right places
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) {n : ℕ∞} [IsManifold I n M]

omit [T2Space M] [LocallyCompactSpace M] in
lemma mem_contDiffGroupoid_of_contMDiff_chartAt {x y : M} {h : OpenPartialHomeomorph M M}
    (hh : ContMDiff I I n h) (hhsymm : ContMDiff I I n h.symm) :
    (chartAt H x).symm.trans (h.trans (chartAt H y)) ∈ (contDiffGroupoid (↑n) I) := by
  refine mem_groupoid_of_pregroupoid.mpr ⟨?_, ?_⟩
  · refine ((contMDiff_iff.mp hh).2 x y).mono (fun v hv ↦ ?_)
    simpa using ⟨⟨hv.2, hv.1.1⟩, hv.1.2.2⟩
  · refine ((contMDiff_iff.mp hhsymm).2 y x).mono (fun v hv ↦ ?_)
    simpa using ⟨⟨hv.2, hv.1.1.1⟩, hv.1.2⟩

open Set

lemma quotient_IsLocalHomeomorph : IsLocalHomeomorph (Quotient.mk (orbitRel G M)) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.isLocalHomeomorph

variable (x y : orbitRel.Quotient G M)

-- should this be deleted??
abbrev πinv : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  quotient_IsLocalHomeomorph.localInverseAt (Y := orbitRel.Quotient G M) x.out

variable {x} in
/-- If `g • m` is in the target of `πinv x`, then `πinv x ⟦m⟧` is just `g • m`. -/
lemma πinv_mk_eq_smul {g : G} {m : M} (hm : g • m ∈ (πinv x).target) :
    πinv x ⟦m⟧ = g • m := by
  rw [← orbitRel.Quotient.quotient_smul_eq (g := g),
    ← quotient_IsLocalHomeomorph.localInverseAt_symm, (πinv x).right_inv hm]

/-- On the open set `(g • ·) ⁻¹' (πinv y).target`, the section comparison
`(πinv x).symm.trans (πinv y)` is the action of `g`. -/
lemma smul_eqOn (g : G) :
    ((g • ·) ⁻¹' (πinv y).target).EqOn ((πinv x).symm.trans (πinv y)) (g • ·) := by
  intro m hm
  simpa only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    quotient_IsLocalHomeomorph.localInverseAt_symm] using πinv_mk_eq_smul hm

variable {x} in
/-- If `⟦m⟧` is in the target of `πinv x`, then there is some `g ∈ G` such that
`g • m` is also in the target of `πinv x`.
-/
lemma exists_smul_mem_πinv_target (m : M) (hm : (⟦m⟧ : orbitRel.Quotient G M) ∈ (πinv x).source) :
    ∃ g : G, g • m ∈ (πinv x).target := by
  obtain ⟨g, hg⟩ := orbitRel_apply.mp
    (Quotient.exact (quotient_IsLocalHomeomorph.apply_localInverseAt_of_mem hm))
  exact ⟨g, by simpa [hg] using (πinv x).map_source hm⟩

/-- Locally, the comparison of two local sections is the action of a single group element. -/
lemma locally_smul (m : M) (hm : m ∈ ((πinv x).symm.trans (πinv y)).source) :
    ∃ g : G, m ∈ (g • ·) ⁻¹' (πinv y).target ∧
      ((g • ·) ⁻¹' (πinv y).target).EqOn ((πinv x).symm.trans (πinv y)) (g • ·)  := by
  rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    quotient_IsLocalHomeomorph.localInverseAt_symm] at hm
  obtain ⟨g, hg⟩ := exists_smul_mem_πinv_target m hm.2
  exact ⟨g, hg, smul_eqOn x y g⟩

/-- The transition map between the charts of the quotient associated to `x` and `y`. -/
def quotientTransitionMap : OpenPartialHomeomorph H H :=
  (chartAt H x.out).symm.trans (((πinv x).symm.trans (πinv y)).trans (chartAt H y.out))

/-- For a fixed `g`, the transition map of the quotient agrees with `φ x⁻¹ ≫ (g • ·) ≫ φ y` on
the preimage under `(φ x).symm` of the set where the section comparison is the action of `g`. -/
lemma quotientTransitionMap_eqOn_smul (g : G) :
    ((chartAt H x.out).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target)).EqOn
      (quotientTransitionMap x y)
      ((chartAt H x.out).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans
        (chartAt H y.out))) := by -- QUESTION: should this `φ x⁻¹ ≫ (g • ·) ≫ φ y` also be a def
  intro h hh
  simp only [quotientTransitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  simpa using congrArg (chartAt H y.out) (smul_eqOn x y g hh)

/-- Locally, the transition map of the quotient is `φ x⁻¹ ≫ (g • ·) ≫ φ y` for a single group
element `g`. -/
lemma quotientTransitionMap_locally_smul {h : H} (hh : h ∈ (quotientTransitionMap x y).source) :
    ∃ g : G, h ∈ (chartAt H x.out).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target) ∧
      ((chartAt H x.out).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target)).EqOn
        (quotientTransitionMap x y)
        ((chartAt H x.out).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans
          (chartAt H y.out))) := by
  simp only [quotientTransitionMap, OpenPartialHomeomorph.trans_source, mem_inter_iff,
    mem_preimage] at hh
  obtain ⟨-, ⟨-, hmid⟩, -⟩ := hh
  obtain ⟨g, hg⟩ := exists_smul_mem_πinv_target ((chartAt H x.out).symm h)
    (by rwa [quotient_IsLocalHomeomorph.localInverseAt_symm] at hmid)
  exact ⟨g, hg, quotientTransitionMap_eqOn_smul x y g⟩

variable {x y : orbitRel.Quotient G M}

section

-- move this

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : OpenPartialHomeomorph X Y}

theorem OpenPartialHomeomorph.restr_eqOnSource_of_eqOn
    {e e' : OpenPartialHomeomorph X Y} {s : Set X} (hs : IsOpen s)
    (heq : s.EqOn e e') (hsub : e.source ∩ s ⊆ e'.source) :
    e.restr s ≈ e'.restr (e.source ∩ s) := by
  refine ⟨?_, ?_⟩
  · rw [e.restr_source' s hs, e'.restr_source' _ (e.open_source.inter hs),
      inter_eq_right.mpr hsub]
  · exact fun z hz ↦ heq (e.restr_source' s hs ▸ hz).2

lemma StructureGroupoid.restr_mem_of_eqOn {G : StructureGroupoid X}
    [ClosedUnderRestriction G] {e e' : OpenPartialHomeomorph X X} {s : Set X}
    (he' : e' ∈ G) (hs : IsOpen s) (heq : s.EqOn e e') (hsub : e.source ∩ s ⊆ e'.source) :
    e.restr s ∈ G :=
  G.mem_of_eqOnSource (closedUnderRestriction' he' (e.open_source.inter hs))
    (OpenPartialHomeomorph.restr_eqOnSource_of_eqOn hs heq hsub)

end

-- the action is smooth
variable [TopologicalSpace G] [ChartedSpace H G] [ContMDiffSMul I I n G M]

instance : IsManifold I n (orbitRel.Quotient G M) where
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
    refine StructureGroupoid.restr_mem_of_eqOn (mem_contDiffGroupoid_of_contMDiff_chartAt I ?_ ?_)
      hto (hg0'.mono inter_subset_right) ?_
    · rw [Homeomorph.toOpenPartialHomeomorph_apply]
      exact ContMDiffSMul.contMDiff_const_smul (I := I) g0
    · rw [Homeomorph.toOpenPartialHomeomorph_symm_apply]
      exact ContMDiffSMul.contMDiff_const_smul (I := I) g0⁻¹
    · rintro h' ⟨⟨hQ1, -, hQ4⟩, -, hcert⟩
      exact ⟨hQ1, mem_univ _, by simpa [← smul_eqOn x y g0 hcert] using hQ4⟩

end MulAction

end

#min_imports
