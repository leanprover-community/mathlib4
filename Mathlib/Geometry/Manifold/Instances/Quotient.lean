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

instance : IsManifold I n (orbitRel.Quotient G M) where
  compatible := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩

    set πinv := Quotient.mk_surjective.hasRightInverse.choose

    set φy := chartAt H (πinv y)
    set φx := chartAt H (πinv x)

    have hQ : IsLocalHomeomorph (Quotient.mk (orbitRel G M)) :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.isLocalHomeomorph

    set πinvx := hQ.localInverseAt (πinv x)
    set πinvy := hQ.localInverseAt (πinv y)

    rw [πinvx.trans_symm_eq_symm_trans_symm, φx.symm.trans_assoc, ← πinvx.symm.trans_assoc]

    apply StructureGroupoid.locality

    intro h ⟨hh1, ⟨hh2, hh3⟩, hh4⟩

    let Up := πinvx.target ∩ φx.source -- U H x
    let Uq := πinvy.target ∩ φy.source -- U H y

    have heq : (⟦φx.symm h⟧ : orbitRel.Quotient G M) = ⟦πinvy (πinvx.symm (φx.symm h))⟧ := by
      rw [← hQ.localInverseAt_symm (πinv y), OpenPartialHomeomorph.left_inv _ hh3,
        hQ.localInverseAt_symm, hQ.localInverseAt_symm]

    obtain ⟨g0, hg0⟩ := MulAction.orbitRel_apply.mp (Quotient.exact heq.symm)
    simp only at hg0

    set Up' := Up ∩ Homeomorph.smul g0⁻¹ '' Uq

    set t := φx '' (Up')

    have is_open_Up' : IsOpen Up' := (πinvx.open_target.inter φx.open_source).inter
      ((Homeomorph.isOpen_image _).mpr (πinvy.open_target.inter φy.open_source))

    have is_open_t : IsOpen t := φx.isOpen_image_of_subset_source is_open_Up'
      (Subset.trans inter_subset_left inter_subset_right)

    have h_in_t : h ∈ t := by
      refine ⟨φx.symm h, ?_, φx.right_inv hh1⟩
      refine ⟨⟨hh2, φx.map_target hh1⟩, ?_⟩
      refine ⟨πinvy (πinvx.symm (φx.symm h)), ?_⟩
      exact ⟨⟨πinvy.map_source hh3, hh4⟩, (Homeomorph.smul g0).injective (by simp [hg0])⟩

    refine ⟨t, is_open_t, h_in_t, ?_⟩
    set f := (φx.symm.trans ((πinvx.symm.trans πinvy).trans φy))

    have f_source_t : (f.restr t).source ⊆ t := by
      simp [IsOpen.interior_eq is_open_t]

    have f_eq_φρφ_t : ∀ x ∈ (f.restr t).source, f x = φy (Homeomorph.smul g0 (φx.symm x)) := by
      intro z hz
      obtain ⟨u, hu, hz⟩ := f_source_t hz
      simp only [f, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
      rw [← hz, φx.left_inv hu.1.2, hQ.localInverseAt_symm,
        ← orbitRel.Quotient.quotient_smul_eq (g:=g0)]
      apply mem_image_of_mem (Homeomorph.smul g0) at hu
      simp only [Up', ← Homeomorph.smul_symm, Homeomorph.image_symm, Homeomorph.smul_apply,
        mem_image, mem_inter_iff, mem_preimage, smul_left_cancel_iff, exists_eq_right]
        at hu
      rw [← hQ.localInverseAt_symm, ← Homeomorph.smul_apply, πinvy.right_inv (by exact hu.2.1)]

    have hfg_t : ((φx.symm.trans (((Homeomorph.smul g0).toOpenPartialHomeomorph).trans φy)).restr
      (t ∩ f.source)).EqOnSource (f.restr t) := by
      refine ⟨?_, ?_⟩
      · ext z
        refine ⟨?_, ?_⟩
        · intro ⟨_, hzt⟩
          rw [f.restr_source, is_open_t.interior_eq, inter_comm]
          simpa [(is_open_t.inter f.open_source).interior_eq] using hzt
        · intro ⟨hzf, hzt⟩
          rw [is_open_t.interior_eq] at hzt
          obtain ⟨u, hu, hz⟩ := hzt
          refine ⟨?_, ?_⟩
          · rw [← hz]
            refine ⟨φx.map_source' hu.1.2, ?_⟩
            obtain ⟨u', hu'⟩ := hu.2
            suffices h : (Homeomorph.smul g0) (φx.symm (φx u)) ∈ φy.source by simpa using h
            rw [φx.left_inv hu.1.2, ← hu'.2, Homeomorph.smul_apply, Homeomorph.smul_apply,
              smul_inv_smul]
            exact hu'.1.2
          · rw [interior_inter, is_open_t.interior_eq, f.open_source.interior_eq]
            exact ⟨⟨u, ⟨hu, hz⟩⟩, hzf⟩
      · intro z ⟨_, hz⟩
        refine Eq.symm (f_eq_φρφ_t z ?_)
        simpa [interior_inter, f.open_source.interior_eq, And.comm] using hz

    apply (StructureGroupoid.mem_iff_of_eqOnSource hfg_t).mp

    apply closedUnderRestriction'
    · apply mem_contDiffGroupoid_of_contMDiff_chartAt
      · sorry
      · sorry
    · exact is_open_t.inter f.open_source

end MulAction

end
