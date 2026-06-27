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

def quotient_RightInverse : Quotient (orbitRel G M) → M :=
  Quotient.mk_surjective.hasRightInverse.choose

variable (x y : orbitRel.Quotient G M)

abbrev φ : OpenPartialHomeomorph M H := chartAt H (quotient_RightInverse x)

abbrev πinv : OpenPartialHomeomorph (orbitRel.Quotient G M) M :=
  quotient_IsLocalHomeomorph.localInverseAt (Y := orbitRel.Quotient G M) (quotient_RightInverse x)

def quotientTransitionMap : OpenPartialHomeomorph H H :=
  (φ x).symm.trans (((πinv x).symm.trans (πinv y)).trans (φ y))

variable {x y : orbitRel.Quotient G M}

lemma lemma_f_eq_φρφ_t {t : Set M} (ht : t ⊆ ((φ (H := H) x).source))
    {g : G} {u : M} (hu : u ∈ t)
    (hu' : (Homeomorph.smul g) u ∈ (πinv y).target) :
    (quotientTransitionMap x y) (φ (H := H) x u) =
      φ y (Homeomorph.smul g (((φ (H := H) x).symm (φ x u)))) := by
  simp only [quotientTransitionMap, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [(φ x).left_inv (ht hu), quotient_IsLocalHomeomorph.localInverseAt_symm,
        ← orbitRel.Quotient.quotient_smul_eq (g:=g)]
  apply mem_image_of_mem (Homeomorph.smul g) at hu
  rw [← quotient_IsLocalHomeomorph.localInverseAt_symm, ← Homeomorph.smul_apply,
    (πinv y).right_inv hu']

lemma lemma_hfg_t
    (t : Set M) (g : G)
    (ht : t ⊆ (φ (H := H) x).source)
    (is_open_t : IsOpen t)
    (ht' : Homeomorph.smul g '' t ⊆ (φ (H := H) y).source)
    (ht'' : Homeomorph.smul g '' t ⊆ (πinv y).target) :
    (((φ (H := H) x).symm.trans (((Homeomorph.smul g).toOpenPartialHomeomorph).trans (φ y))).restr
      ((φ x '' t) ∩ (quotientTransitionMap x y).source)).EqOnSource
      ((quotientTransitionMap x y).restr (φ x '' t))
    := by
  have is_open_φt := ((φ x).isOpen_image_iff_of_subset_source ht).mpr is_open_t
  refine ⟨?_, ?_⟩
  · ext z
    refine ⟨?_, ?_⟩
    · intro ⟨_, hzt⟩
      rw [(quotientTransitionMap x y).restr_source, is_open_φt.interior_eq, inter_comm]
      simpa [(is_open_φt.inter (quotientTransitionMap x y).open_source).interior_eq] using hzt
    · intro ⟨hzf, hzt⟩
      rw [is_open_φt.interior_eq] at hzt
      obtain ⟨u, hu, hz⟩ := hzt
      refine ⟨?_, ?_⟩
      · rw [← hz]
        refine ⟨(φ x).map_source' (ht hu), ?_⟩
        suffices h : g • (φ x).symm ((φ x) u) ∈ (φ y).source by simpa using h
        rw [(φ x).left_inv (ht hu)]
        apply ht'
        simp [hu]
      · rw [(is_open_φt.inter (quotientTransitionMap x y).open_source).interior_eq]
        refine ⟨by use u;, by exact hzf⟩
  · intro z ⟨_, hz⟩
    rw [(is_open_φt.inter (quotientTransitionMap x y).open_source).interior_eq] at hz
    obtain ⟨⟨_, hut, hu⟩, _⟩ := hz
    simpa [hu] using (lemma_f_eq_φρφ_t ht hut (ht'' (mem_image_of_mem _ hut))).symm




instance : IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩

    change ((πinv x).trans (φ x)).symm.trans ((πinv y).trans (φ y)) ∈ contDiffGroupoid (↑n) I

    rw [(πinv x).trans_symm_eq_symm_trans_symm, (φ x).symm.trans_assoc, ← (πinv x).symm.trans_assoc]

    apply StructureGroupoid.locality

    intro h ⟨hh1, ⟨hh2, hh3⟩, hh4⟩

    have heq : (⟦(φ x).symm h⟧ : orbitRel.Quotient G M) =
      ⟦(πinv y) ((πinv x).symm ((φ x).symm h))⟧ := by
      rw [← quotient_IsLocalHomeomorph.localInverseAt_symm (quotient_RightInverse y),
        OpenPartialHomeomorph.left_inv _ hh3, quotient_IsLocalHomeomorph.localInverseAt_symm,
        quotient_IsLocalHomeomorph.localInverseAt_symm]

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

    have hfg_t :
      (((φ x).symm.trans (((Homeomorph.smul g0).toOpenPartialHomeomorph).trans (φ y))).restr
      (t ∩ (quotientTransitionMap x y).source)).EqOnSource ((quotientTransitionMap x y).restr t)
      := by
      apply lemma_hfg_t
      · exact fun x hx => hx.1.2
      · exact is_open_Up'
      · intro m ⟨_, ⟨_, _, hw⟩, hu2⟩
        simpa [← hu2, ← hw.2] using hw.1.2
      · intro m ⟨_, ⟨_, _, hw⟩, hu2⟩
        simpa [← hu2, ← hw.2] using hw.1.1

    apply (StructureGroupoid.mem_iff_of_eqOnSource hfg_t).mp

    apply closedUnderRestriction'
    · apply mem_contDiffGroupoid_of_contMDiff_chartAt
      · sorry
      · sorry
    · exact is_open_t.inter (quotientTransitionMap x y).open_source

end MulAction

end
