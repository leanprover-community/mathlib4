/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Uniformizable Spaces

A topological space is uniformizable (there exists a uniformity that
generates the same topology) if it is completely regular.

TODO: Prove the reverse implication too.

## References

* [S. Willard, *General Topology*][Wil04]
-/

variable {α : Type*}

open Filter Set

section UniformSpace
variable [UniformSpace α]

proof_wanted UniformSpace.completelyRegularSpace : CompletelyRegularSpace α

end UniformSpace

section TopologicalSpace
variable [TopologicalSpace α]
open Real

variable (α) in
/-
This definition could be useful in other places, but I've not seen a use yet
so this is private for now (mainly so I don't have to write api).
-/
private def inducedUniformity : UniformSpace α :=
  UniformSpace.ofCore {
    uniformity := ⨅ (f : C(α, ℝ)) (ε : ℝ) (_ : ε > 0),
      principal ((fun p => dist (f p.fst) (f p.snd)) ⁻¹' Iio ε)
    refl := by
      simp_rw [le_iInf_iff]
      simp +contextual
    symm := by
      rw [tendsto_iff_comap]
      apply le_of_eq
      simp_rw [Filter.comap_iInf, comap_principal, preimage_preimage,
        Prod.fst_swap, Prod.snd_swap, dist_comm]
    -- this proof takes four seconds to elaborate on my machine
    -- TODO: speed this up
    comp := by
      intro s hs
      simp_rw [mem_iInf, iInf_eq_if] at hs
      obtain ⟨I, hI, U, hs, rfl⟩ := hs
      have := hI.to_subtype
      choose J hJ V hs hU using hs
      have := fun i => (hJ i).to_subtype
      replace hU : U = fun i => ⋂ j, V i j := funext hU
      subst hU
      suffices h : ((fun s => compRel s s) <| ⋂ (i : I) (j : J i) (_ : j.val > 0),
          (fun p ↦ dist (i.val p.fst) (i.val p.snd)) ⁻¹' Iio (j / 2)) ⊆ ⋂ (i) (j), V i j by
        refine mem_of_superset ?_ h
        apply mem_lift'
        simp_rw [mem_iInf, iInf_eq_if, mem_ite, mem_principal, mem_top]
        refine ⟨I, hI, _, fun i => ?_, rfl⟩
        refine ⟨(· / 2) '' J i, (hJ i).image (· / 2),
          fun j => ⋂ (_ : j.val > 0), (fun p ↦ dist (i.val p.fst) (i.val p.snd)) ⁻¹' Iio j,
            fun j => ⟨fun hj => ?_, fun hj => by simp [hj]⟩, ?_⟩
        · simp_rw [iInter_eq_if, if_pos hj, subset_rfl]
        · apply iInter_congr_of_surjective _ surjective_onto_image
          intro j
          simp only [imageFactorization]
          exact iInter_congr_Prop (by simp) fun _ => rfl
      simp_rw [subset_iInter_iff]
      intro i j
      specialize hs i j
      split_ifs at hs with hj
      · intro x hx
        apply hs
        rw [mem_compRel] at hx
        obtain ⟨z, hxz, hzx⟩ := hx
        simp_rw [mem_iInter] at hxz hzx
        apply (dist_triangle (i.val x.fst) (i.val z) (i.val x.snd)).trans_lt
        rw [← add_halves j.val]
        exact add_lt_add (hxz i j hj) (hzx i j hj)
      · rw [mem_top] at hs
        simp [hs]
  }

private theorem le_u_l :
    ‹TopologicalSpace α› ≤ (inducedUniformity α).toTopologicalSpace := by
  intro s hs
  rw [isOpen_iff_forall_mem_open]
  rw [@isOpen_iff_ball_subset] at hs
  intro x hx
  obtain ⟨V, hV, hVs⟩ := hs x hx
  change V ∈ iInf _ at hV
  simp_rw [mem_iInf] at hV
  obtain ⟨I, hI, U, hU, rfl⟩ := hV
  have := hI.to_subtype
  choose J hJ V hV hU using hU
  have := fun i => (hJ i).to_subtype
  replace hU : U = fun i => ⋂ j, V i j := funext hU
  subst hU
  refine ⟨⋂ (i : I) (j : J i) (_ : j.val > 0), (fun y => dist (i.val x) (i.val y)) ⁻¹' Iio j,
    ?_, ?_, ?_⟩
  · apply hVs.trans'
    simp_rw [UniformSpace.ball, preimage_iInter]
    apply iInter₂_mono
    intro i j
    simp_rw [iInf_eq_if, mem_ite, mem_principal, mem_top] at hV
    rw [iInter_eq_if]
    split_ifs with hj
    · apply (preimage_mono ((hV i j).left hj)).trans'
      intro y hy
      simpa using hy
    · simp [(hV i j).right hj]
  · exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun hj =>
          isOpen_Iio.preimage (continuous_const.dist i.val.continuous)
  · simp_rw [mem_iInter]
    intro i j hj
    simp [hj]

section CompletelyRegularSpace
variable [CompletelyRegularSpace α]

private theorem u_l_le :
    (inducedUniformity α).toTopologicalSpace ≤ ‹TopologicalSpace α› := by
  intro s hs
  rw [@isOpen_iff_ball_subset]
  intro x hx
  obtain ⟨f, hf, hf0, hf1⟩ :=
    CompletelyRegularSpace.completely_regular x sᶜ hs.isClosed_compl (not_mem_compl_iff.mpr hx)
  use ((fun p : α × α => dist (f p.fst : ℝ) (f p.snd)) ⁻¹' Iio 2⁻¹)
  constructor
  · have hf' : Continuous (fun i => (f i : ℝ)) := continuous_subtype_val.comp hf
    suffices h : (_ : Filter _) ≤ _ from h (mem_principal_self _)
    apply iInf₂_le_of_le ⟨_, hf'⟩ 2⁻¹
    exact iInf_le _ (by norm_num)
  · rw [UniformSpace.ball]
    intro a ha
    by_contra has
    norm_num [hf0, hf1 has] at ha

theorem CompletelyRegularSpace.exists_uniformity :
    ∃ (u : UniformSpace α), u.toTopologicalSpace = ‹TopologicalSpace α› :=
  ⟨inducedUniformity α, u_l_le.antisymm le_u_l⟩

end CompletelyRegularSpace

end TopologicalSpace
