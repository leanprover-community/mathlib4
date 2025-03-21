/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Tactic.Peel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Complex.Basic

/-! # Conditions on unitary elements imposed by the continuous functional calculus

## Main theorems

* `unitary_iff_isStarNormal_and_spectrum_subset_unitary`: An element is unitary if and only if it is
  star-normal and its spectrum lies on the unit circle.

-/

section Generic

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [ContinuousFunctionalCalculus R A p]

lemma cfc_unitary_iff (f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc f a ∈ unitary A ↔ ∀ x ∈ spectrum R a, star (f x) * f x = 1 := by
  simp only [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [← IsStarNormal.cfc_map (p := p) f a |>.star_comm_self |>.eq, and_self, ← cfc_one R a,
    ← cfc_star, ← cfc_mul .., cfc_eq_cfc_iff_eqOn]
  exact Iff.rfl

end Generic

section Complex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

lemma unitary_iff_isStarNormal_and_spectrum_subset_unitary {u : A} :
    u ∈ unitary A ↔ IsStarNormal u ∧ spectrum ℂ u ⊆ unitary ℂ := by
  rw [← and_iff_right_of_imp isStarNormal_of_mem_unitary]
  refine and_congr_right fun hu ↦ ?_
  nth_rw 1 [← cfc_id ℂ u]
  rw [cfc_unitary_iff id u, Set.subset_def]
  simp only [id_eq, RCLike.star_def, SetLike.mem_coe, unitary.mem_iff_star_mul_self]

lemma mem_unitary_of_spectrum_subset_unitary {u : A}
    [IsStarNormal u] (hu : spectrum ℂ u ⊆ unitary ℂ) : u ∈ unitary A :=
  unitary_iff_isStarNormal_and_spectrum_subset_unitary.mpr ⟨‹_›, hu⟩

lemma spectrum_subset_unitary_of_mem_unitary {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ unitary ℂ :=
  unitary_iff_isStarNormal_and_spectrum_subset_unitary.mp hu |>.right

end Complex
