/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic.Peel
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.Unital

/-! # Conditions on unitary elements imposed by the continuous functional calculus

## Main theorems

* `unitary_iff_isStarNormal_and_spectrum_subset_circle`: An element is unitary if and only if it is
  star-normal and its spectrum lies on the unit circle.

-/

section prereq

instance IsStarNormal.cfc_map {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R p] (a : A) (f : R → R) :
    IsStarNormal (cfc f a) where
  star_comm_self := by
    rw [Commute, SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

theorem sq_eq_one_iff_of_pos {R : Type*} [LinearOrderedRing R] {a : R} (ha : 0 ≤ a) :
    a ^ 2 = 1 ↔ a = 1 := by
  rw [sq_eq_one_iff, or_iff_left_iff_imp]
  rintro rfl
  norm_num at ha



end prereq

section Unitary

variable {R A : Type*} {p : A → Prop}
variable [CommRing R] [StarRing R] [MetricSpace R] [TopologicalRing R] [ContinuousStar R]
variable [TopologicalSpace A] [Ring A] [StarRing A] [Algebra R A] [StarModule R A]
variable [ContinuousFunctionalCalculus R p]

lemma cfc_unitary_iff (f : R → R) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    cfc f a ∈ unitary A ↔ ∀ x ∈ spectrum R a, star (f x) * f x = 1 := by
  simp only [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [← IsStarNormal.cfc_map (p := p) a f |>.star_comm_self |>.eq, and_self, ← cfc_one R a,
    ← cfc_star, ← cfc_mul .., cfc_eq_cfc_iff_eqOn]
  exact Iff.rfl

end Unitary

section Unitary

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

lemma unitary_iff_isStarNormal_and_spectrum_subset_sphere {u : A} :
    u ∈ unitary A ↔ IsStarNormal u ∧ spectrum ℂ u ⊆ Metric.sphere 0 1 := by
  rw [← and_iff_right_of_imp isStarNormal_of_mem_unitary]
  refine and_congr_right fun hu ↦ ?_
  nth_rw 1 [← cfc_id ℂ u]
  rw [cfc_unitary_iff id u, Set.subset_def]
  congr! with x -
  simp only [id_eq, RCLike.star_def, mem_sphere_iff_norm, sub_zero, Complex.conj_mul']
  exact_mod_cast sq_eq_one_iff_of_pos (norm_nonneg x)

lemma mem_unitary_of_spectrum_subset_sphere {u : A}
    [IsStarNormal u] (hu : spectrum ℂ u ⊆ circle) : u ∈ unitary A :=
  unitary_iff_isStarNormal_and_spectrum_subset_sphere.mpr ⟨‹_›, hu⟩

lemma spectrum_subset_circle_of_mem_unitary {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ circle :=
  unitary_iff_isStarNormal_and_spectrum_subset_sphere.mp hu |>.right

end Unitary
