/-
Copyright (c) 2025 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# (Naive) height of polynomials

In this file we define the (naive) height of a polynomial and prove some basic properties.
See its relationships with Mahler measure in `Mathlib/Analysis/Polynomial/MahlerMeasure.lean`.

## Main definitions

- `Polynomial.height p`: the (naive) height of a polynomial, equal to the maximum norm of its
  coefficients (or zero for the zero polynomial)
-/

@[expose] public section basic

variable {A : Type*} [SeminormedRing A] (p : Polynomial A) {a : A}

namespace Polynomial

/-- The (naive) height of a polynomial, defined as the maximum of its coefficients (or `0` when
`p = 0`) -/
noncomputable def height : ℝ :=
  if h : p.support.Nonempty then
    p.support.sup' h (fun i => ‖p.coeff i‖)
  else
    0

lemma height_def_of_ne_zero (hp : p ≠ 0) :
    p.height = p.support.sup' (p.support_nonempty.mpr hp) (fun i => ‖p.coeff i‖) := by
  simp [height, p.support_nonempty.mpr hp]

lemma height_zero : height (0 : Polynomial A) = 0 := by simp [height]

lemma height_C : height (C a) = ‖a‖ := by
  by_cases ha : a = 0
  · simp [height, ha]
  · simp [height, Polynomial.support_C ha]

lemma height_one [NormOneClass A] : Polynomial.height (1 : Polynomial A) = 1 := by
  rw [← Polynomial.C_1, height_C]
  norm_num

lemma height_X [Nontrivial A] [NormOneClass A] : Polynomial.height (X : Polynomial A) = 1 := by
  simp [height, support_X]

lemma norm_coeff_le_height (i : ℕ) : ‖p.coeff i‖ ≤ p.height := by
  simp only [height, support_nonempty, ne_eq]
  split_ifs with h
  · by_cases hi : i ∈ p.support
    · rw [Finset.le_sup'_iff]
      refine ⟨i, ⟨hi, by simp⟩⟩
    · rw [mem_support_iff] at hi
      push_neg at hi
      rw [hi]
      simp only [norm_zero, Finset.le_sup'_iff, norm_nonneg, and_true]
      obtain ⟨j, hj⟩ := h
      use j
  · simp only [support_nonempty, ne_eq, not_not] at h
    simp [h]

lemma height_nonneg : 0 ≤ p.height := by
  calc 0 ≤ ‖p.coeff 0‖ := norm_nonneg _
    _ ≤ p.height := p.norm_coeff_le_height _

end Polynomial

end basic

@[expose] public section normed

namespace Polynomial

variable {A : Type*} [NormedRing A] (p : Polynomial A) {a : A}

lemma height_pos_iff_ne_zero : 0 < p.height ↔ p ≠ 0 := by
  constructor
  · intros hp
    by_contra! h
    rw [h, Polynomial.height_zero] at hp
    linarith [hp]
  · intros hp
    rw [← Polynomial.support_nonempty] at hp
    obtain ⟨i, hi⟩ := hp
    calc 0 < ‖p.coeff i‖ := norm_pos_iff.mpr (p.mem_support_iff.mp hi)
        _ ≤ p.height := p.norm_coeff_le_height i

lemma height_pos_of_ne_zero (hp : p ≠ 0) : 0 < p.height :=
  p.height_pos_iff_ne_zero.mpr hp

lemma ne_zero_of_height_pos (hp : 0 < p.height) : p ≠ 0 :=
  p.height_pos_iff_ne_zero.mp hp

end Polynomial

end normed
