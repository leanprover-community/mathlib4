/-
Copyright (c) 2025 Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz,
Juan José Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Pepa Montero, Archibald Browne, Enrique Díaz, Juan José Madrigal
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

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
@[expose, to_additive]
instance instChartedSpaceQuotient : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpace Quotient.mk_surjective

-- maybe we should change the ChartedSpace instance to this
--(so we can use x.out and delete the right inverse choice)
instance instChartedSpaceQuotient' : ChartedSpace H (orbitRel.Quotient G M) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    |>.isLocalHomeomorph.chartedSpaceOfRightInverse Quotient.out_eq






variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H)
  {n : ℕ∞} [IsManifold I n M]

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

abbrev φ : OpenPartialHomeomorph M H := chartAt H x.out

abbrev πinv : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  quotient_IsLocalHomeomorph.localInverseAt (Y := orbitRel.Quotient G M) x.out

section

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


end

/-- The transition map between the charts of the quotient associated to `x` and `y`. -/
def quotientTransitionMap : OpenPartialHomeomorph H H :=
  (φ (H := H) x).symm.trans (((πinv x).symm.trans (πinv y)).trans (φ y))

/-- For a fixed `g`, the transition map of the quotient agrees with `φ x⁻¹ ≫ (g • ·) ≫ φ y` on
the preimage under `(φ x).symm` of the set where the section comparison is the action of `g`. -/
lemma quotientTransitionMap_eqOn_smul (g : G) :
    ((φ (H := H) x).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target)).EqOn
      (quotientTransitionMap x y)
      ((φ x).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans (φ y))) := by
  intro h hh
  simp only [quotientTransitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  simpa using congrArg (φ y) (smul_eqOn x y g hh)

/-- Locally, the transition map of the quotient is `φ x⁻¹ ≫ (g • ·) ≫ φ y` for a single group
element `g`. -/
lemma quotientTransitionMap_locally_smul {h : H} (hh : h ∈ (quotientTransitionMap x y).source) :
    ∃ g : G, h ∈ (φ x).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target) ∧
      ((φ (H := H) x).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target)).EqOn
        (quotientTransitionMap x y)
        ((φ x).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans (φ y))) := by
  simp only [quotientTransitionMap, OpenPartialHomeomorph.trans_source, mem_inter_iff,
    mem_preimage] at hh
  obtain ⟨-, ⟨-, hmid⟩, -⟩ := hh
  obtain ⟨g, hg⟩ := exists_smul_mem_πinv_target ((φ x).symm h)
    (by rwa [quotient_IsLocalHomeomorph.localInverseAt_symm] at hmid)
  exact ⟨g, hg, quotientTransitionMap_eqOn_smul x y g⟩

variable {x y : orbitRel.Quotient G M}

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : OpenPartialHomeomorph X Y}

example (y : Y) (hy : y ∈ f.target) :
  f (f.symm y) = y := by exact OpenPartialHomeomorph.right_inv f hy

lemma aux (y : Y) (hy : y ∈ f.target) :
  ∃ x ∈ f.source, f x = y := by
  use f.symm y
  sorry

example (m : M) (g : G) :
    (πinv x).symm.trans (πinv y) m = g • m := by
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [quotient_IsLocalHomeomorph.localInverseAt_symm,
  ← orbitRel.Quotient.quotient_smul_eq (g:=g),
  ← quotient_IsLocalHomeomorph.localInverseAt_symm m]

  sorry

lemma general_hfg_t
    (t : Set M) (g : G)
    (ht : t ⊆ (φ (H := H) x).source)
    (is_open_t : IsOpen t)
    (ht' : Homeomorph.smul g '' t ⊆ (φ (H := H) y).source)
    (ht'' : Homeomorph.smul g '' t ⊆ (πinv y).target) :
    (((φ (H := H) x).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans (φ y))).restr
      ((φ x '' t) ∩ (quotientTransitionMap x y).source)).EqOnSource
      ((quotientTransitionMap x y).restr (φ x '' t))
    := by
  have is_open_at := ((φ (H := H) x).isOpen_image_iff_of_subset_source ht).mpr is_open_t
  refine ⟨?_, ?_⟩
  · ext z
    refine ⟨?_, ?_⟩
    · intro ⟨_, hzt⟩
      rw [(quotientTransitionMap (H := H) x y).restr_source, is_open_at.interior_eq, inter_comm]
      simpa [(is_open_at.inter (quotientTransitionMap (H := H) x y).open_source).interior_eq]
        using hzt
    · intro ⟨hzf, hzt⟩
      rw [is_open_at.interior_eq] at hzt
      obtain ⟨u, hu, hz⟩ := hzt
      refine ⟨?_, ?_⟩
      · rw [← hz]
        refine ⟨(φ x).map_source' (ht hu), ?_⟩
        suffices h : g • (φ x).symm (φ x u) ∈ (φ y).source by simpa using h
        rw [(φ x).left_inv (ht hu)]
        apply ht'
        simp [hu]
      · rw [(is_open_at.inter (quotientTransitionMap (H := H) x y).open_source).interior_eq]
        refine ⟨by use u;, by exact hzf⟩
  · intro z ⟨_, hz⟩
    rw [(is_open_at.inter (quotientTransitionMap (H := H) x y).open_source).interior_eq] at hz
    obtain ⟨⟨u, hut, hu⟩, _⟩ := hz
    have hmem : φ x u ∈ (φ (H := H) x).symm ⁻¹' ((g • ·) ⁻¹' (πinv y).target) := by
      simpa [(φ x).left_inv (ht hut)] using ht'' (mem_image_of_mem _ hut)
    simpa [hu] using (quotientTransitionMap_eqOn_smul x y g hmem).symm


instance : IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩

    change ((πinv x).trans (φ x)).symm.trans ((πinv y).trans (φ y)) ∈ contDiffGroupoid (↑n) I

    rw [(πinv x).trans_symm_eq_symm_trans_symm, (φ x).symm.trans_assoc, ← (πinv x).symm.trans_assoc]

    change quotientTransitionMap x y ∈ contDiffGroupoid (↑n) I

    apply StructureGroupoid.locality

    intro h hh

    have aux := quotientTransitionMap_locally_smul x y hh
    obtain ⟨g0, hg1, hg2⟩ := aux

    let Up := (πinv x).target ∩ (φ (H := H) x).source -- U H x
    let Uq := (πinv y).target ∩ (φ (H := H) y).source -- U H y
    let Up' := Up ∩ Homeomorph.smul g0⁻¹ '' Uq
    let t := φ (H:=H) x '' Up'

    refine ⟨t, sorry, sorry, ?_⟩

    #check closedUnderRestriction'

    intro h ⟨hh1, ⟨hh2, hh3⟩, hh4⟩

    have heq : (⟦(φ x).symm h⟧ : orbitRel.Quotient G M) =
      ⟦(πinv y) ((πinv x).symm ((φ x).symm h))⟧ := by
      rw [← quotient_IsLocalHomeomorph.localInverseAt_symm y.out,
        OpenPartialHomeomorph.left_inv _ hh3, quotient_IsLocalHomeomorph.localInverseAt_symm,
        quotient_IsLocalHomeomorph.localInverseAt_symm]

    /-
    the second rw could be
    (πinv y).left_inv (x := (πinv x).symm ((φ x).symm h)) hh3
    or
    (πinv y).left_inv (by simpa using hh3)
    neither of them feel a lot better.
    -/

    obtain ⟨g0, hg0⟩ := MulAction.orbitRel_apply.mp (Quotient.exact heq.symm)

    let Up := (πinv x).target ∩ (φ (H := H) x).source -- U H x
    let Uq := (πinv y).target ∩ (φ (H := H) y).source -- U H y
    let Up' := Up ∩ Homeomorph.smul g0⁻¹ '' Uq
    let t := φ (H:=H) x '' Up'

    have is_open_Up' : IsOpen Up' := ((πinv x).open_target.inter (φ x).open_source).inter
      ((Homeomorph.isOpen_image _).mpr ((πinv y).open_target.inter (φ y).open_source))

    have is_open_t : IsOpen t := (φ x).isOpen_image_of_subset_source is_open_Up'
      (inter_subset_left.trans inter_subset_right)

    have h_in_t : h ∈ t := by
      refine ⟨(φ x).symm h, ?_, (φ x).right_inv hh1⟩
      refine ⟨⟨hh2, (φ x).map_target hh1⟩, ?_⟩
      refine ⟨(πinv y) ((πinv x).symm ((φ x).symm h)), ?_⟩
      exact ⟨⟨(πinv y).map_source hh3, hh4⟩, (Homeomorph.smul g0).injective (by simp [hg0])⟩

    refine ⟨t, is_open_t, h_in_t, ?_⟩

    have hfg_t := general_hfg_t (x:=x) (y:=y) Up' g0 (fun x hx => hx.1.2) is_open_Up'
      (fun m ⟨_, ⟨_, _, hw⟩, hu2⟩ ↦ by simpa [← hu2, ← hw.2] using hw.1.2)
      (fun m ⟨_, ⟨_, _, hw⟩, hu2⟩ ↦ by simpa [← hu2, ← hw.2] using hw.1.1)

    refine (StructureGroupoid.mem_iff_of_eqOnSource hfg_t).mp ?_

    refine closedUnderRestriction' ?_ ?_
    · refine mem_contDiffGroupoid_of_contMDiff_chartAt I ?_ ?_
      · sorry
      · sorry
    · exact is_open_t.inter (quotientTransitionMap (H := H) x y).open_source

end MulAction

end
