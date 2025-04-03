/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic.Peel
import Mathlib.Topology.ContinuousFunction.FunctionalCalculus

/-! # Conditions on unitary elements imposed by the continuous functional calculus

## Main theorems

* `unitary_iff_isStarNormal_and_spectrum_subset_circle`: An element is unitary if and only if it is
  star-normal and its spectrum lies on the unit circle.

-/
section Unitary

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

lemma unitary_iff_isStarNormal_and_spectrum_subset_circle {u : A} :
    u ∈ unitary A ↔ IsStarNormal u ∧ spectrum ℂ u ⊆ circle := by
  refine ⟨fun hu ↦ ?_, ?_⟩
  · have h_normal := isStarNormal_of_mem_unitary hu
    refine ⟨h_normal, ?_⟩
    have h := unitary.star_mul_self_of_mem hu
    rw [← cfc_id ℂ u, ← cfc_star id u, ← cfc_mul .., ← cfc_one ℂ u] at h
    have := eqOn_of_cfc_eq_cfc h
    peel this with x hx _
    rw [SetLike.mem_coe, mem_circle_iff_normSq]
    simpa using congr($(this).re)
  · rintro ⟨_, hu⟩
    rw [unitary.mem_iff, ← cfc_id ℂ u, ← cfc_star, ← cfc_mul .., ← cfc_mul .., ← cfc_one ℂ u]
    simp only [id_eq]
    constructor
    all_goals
      apply cfc_congr (fun x hx ↦ ?_)
      simp only [RCLike.star_def, mul_comm x]
      apply hu at hx
      rwa [SetLike.mem_coe, mem_circle_iff_normSq, ← Complex.ofReal_injective.eq_iff,
        Complex.normSq_eq_conj_mul_self] at hx

lemma mem_unitary_of_spectrum_subset_circle {u : A}
    [IsStarNormal u] (hu : spectrum ℂ u ⊆ circle) : u ∈ unitary A :=
  unitary_iff_isStarNormal_and_spectrum_subset_circle.mpr ⟨‹_›, hu⟩

lemma spectrum_subset_circle_of_mem_unitary {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ circle :=
  unitary_iff_isStarNormal_and_spectrum_subset_circle.mp hu |>.right

end Unitary
