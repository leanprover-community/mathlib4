/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Topology.ContinuousMap.StarOrdered

/-! # The positive (and negative) parts of a selfadjoint element in a C⋆-algebra

This file defines the positive and negative parts of a selfadjoint element in a C⋆-algebra via
the continuous functional calculus and develops the basic API.

## TODO

+ Prove that the positive and negative parts are unique.

-/

variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

namespace CStarAlgebra

noncomputable instance : PosPart A where
  posPart := cfcₙ (·⁺ : ℝ → ℝ)

noncomputable instance : NegPart A where
  negPart := cfcₙ (·⁻ : ℝ → ℝ)

end CStarAlgebra

namespace CFC

lemma posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : ℝ → ℝ) a := rfl

lemma negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : ℝ → ℝ) a := rfl

@[simp]
lemma posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

@[simp]
lemma negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total 0 x
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : a⁺ - a⁻ = a := by
  rw [posPart_def, negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id ℝ a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

section Unique

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

@[simp]
lemma posPart_neg (a : A) : (-a)⁺ = a⁻ := by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h ↦ ha (by simpa using h.neg)
    rw [posPart_def, negPart_def, cfcₙ_apply_of_not_predicate a ha,
      cfcₙ_apply_of_not_predicate _ ha']

@[simp]
lemma negPart_neg (a : A) : (-a)⁻ = a⁺ := by
  rw [← eq_comm, ← sub_eq_zero, ← posPart_neg, neg_neg, sub_self]

end Unique

variable [PartialOrder A] [StarOrderedRing A]

@[aesop norm apply (rule_sets := [CStarAlgebra])]
lemma posPart_nonneg (a : A) :
    0 ≤ a⁺ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

@[aesop norm apply (rule_sets := [CStarAlgebra])]
lemma negPart_nonneg (a : A) :
    0 ≤ a⁻ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

variable [NonnegSpectrumClass ℝ A]

lemma eq_posPart_iff (a : A) : a = a⁺ ↔ 0 ≤ a := by
  refine ⟨fun ha ↦ ha ▸ posPart_nonneg a, fun ha ↦ ?_⟩
  conv_lhs => rw [← cfcₙ_id ℝ a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx ↦ ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

lemma negPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a) :
    a⁻ = 0 ↔ 0 ≤ a := by
  rw [← eq_posPart_iff]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

lemma eq_negPart_iff (a : A) : a = -a⁻ ↔ a ≤ 0 := by
  refine ⟨fun ha ↦ by rw [ha, neg_nonpos]; exact negPart_nonneg a, fun ha ↦ ?_⟩
  rw [← neg_nonneg] at ha
  rw [negPart_def, ← cfcₙ_neg]
  have _ : IsSelfAdjoint a := neg_neg a ▸ (IsSelfAdjoint.neg <| .of_nonneg ha)
  conv_lhs => rw [← cfcₙ_id ℝ a]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [Unitization.quasispectrum_eq_spectrum_inr ℝ, ← neg_neg x, ← Set.mem_neg,
    spectrum.neg_eq, ← Unitization.inr_neg, ← Unitization.quasispectrum_eq_spectrum_inr ℝ] at hx
  rw [← neg_eq_iff_eq_neg, eq_comm]
  simpa using quasispectrum_nonneg_of_nonneg _ ha _ hx

lemma posPart_eq_zero_iff (a : A) (ha : IsSelfAdjoint a) :
    a⁺ = 0 ↔ a ≤ 0 := by
  rw [← eq_negPart_iff]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

end CFC
