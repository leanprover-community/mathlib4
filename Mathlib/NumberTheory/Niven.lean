/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Peel
import Mathlib.Tactic.Rify

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

namespace IsIntegral

variable {α R : Type*} [DivisionRing α] [CharZero α] {q : ℚ} {x : α}

theorem lift_rat (h₁ : IsIntegral ℤ (q : α)) : IsIntegral ℤ q := by
  rcases h₁ with ⟨P, hP₁, hP₂⟩
  refine ⟨P, hP₁, ?_⟩
  simpa [Polynomial.eval₂_eq_sum_range, ← @Rat.cast_inj α] using hP₂

theorem exists_int_of_exists_rat (h₁ : IsIntegral ℤ x) : (∃ q : ℚ, x = q) → ∃ k : ℤ, x = k := by
  rintro ⟨q, rfl⟩
  peel IsIntegrallyClosed.algebraMap_eq_of_integral h₁.lift_rat with h
  simp [← h]

theorem exists_int_iff_exists_rat (h₁ : IsIntegral ℤ x) : (∃ q : ℚ, x = q) ↔ (∃ k : ℤ, x = k) :=
  ⟨h₁.exists_int_of_exists_rat, fun ⟨w, h⟩ ↦ ⟨w, by simp [h]⟩⟩

end IsIntegral

variable {θ : ℝ}

open Real

/-- **Niven's theorem**: The only rational values of `cos` that occur at rational multiples of π
are `[-1, -1/2, 0, 1/2, 1]`. -/
theorem niven (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q) :
    cos θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  -- Since `2 cos θ ` is an algebraic integer and rational, it must be an integer.
  -- Hence, `2 cos θ ∈ {-2, -1, 0, 1, 2}`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * cos θ = k := by
    have h_int : IsIntegral ℤ (2 * cos θ) := by
      rcases hθ with ⟨r, hr⟩
      obtain ⟨p, q, hq_pos, rfl⟩ : ∃ p q : ℤ, q > 0 ∧ r = p / q :=
        ⟨r.num, r.den, by positivity, r.num_div_den.symm⟩
      -- Let `z = e^{i π p / q}`, which is a root of unity.
      set z : ℂ := .exp (.I * θ)
      have hz_root : z ^ (2 * q.natAbs) = 1 := by
        rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
        use p
        rw [Nat.cast_mul, ← Int.cast_natCast q.natAbs, ← Int.eq_natAbs_of_nonneg hq_pos.le]
        field_simp [hr, hq_pos.ne']
        group
      -- Since z is a root of unity, `2 cos⁡ θ = z` and `z⁻¹` are algebraic integers, and their sum.
      obtain ⟨f, hf₁, hf₂⟩ : IsIntegral ℤ (z + z⁻¹) := by
        have hz : IsIntegral ℤ z ∧ IsIntegral ℤ z⁻¹ := by
          constructor
          all_goals (
            use .X ^ (2 * q.natAbs) - 1
            constructor
            · apply Polynomial.monic_X_pow_sub_C
              positivity
            · simp [hr, hz_root]
          )
        exact hz.left.add hz.right
      use f, hf₁
      have h_cos_eq : 2 * cos (p / q * π) = z + z⁻¹ := by
        simpa [Complex.cos, Complex.exp_neg, hr, z] using by ring_nf
      simp_all [Polynomial.eval₂_eq_sum_range, ← Complex.ofReal_inj]
    -- Since `2 cos θ` is an algebraic integer and rational, it must be an integer.
    rw [← h_int.exists_int_iff_exists_rat]
    exact ⟨2 * hcos.choose, by push_cast; linarith [hcos.choose_spec]⟩
  obtain ⟨r, rfl⟩ := hθ
  obtain ⟨q, hq⟩ := hcos
  -- Since k is an integer and `2 * cos (w * pi) = k`, we have $k ∈ {-2, -1, 0, 1, 2}$.
  have hk_values : k ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
    have : k ≤ 2 := Int.le_of_lt_add_one <| by rify; linarith [(r * π).cos_le_one]
    have : k ≥ -2 := Int.le_of_lt_add_one <| by rify; linarith [(r * π).neg_one_le_cos]
    interval_cases k <;> norm_num
  rcases hk_values with (rfl | rfl | rfl | rfl | rfl) <;> simp_all
  · simp [show (q : ℝ) = -1 by linarith]
  · simp [show (q : ℝ) = -1/2 by linarith]
  · simp [show (q : ℝ) = 1/2 by linarith]

/-- Niven's theorem, but stated for `sin` instead of `cos`. -/
theorem niven_sin (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, sin θ = q) :
    sin θ ∈ ({-1, -1 / 2, 0, 1 / 2, 1} : Set ℝ) := by
  convert ← niven (θ := θ - π/2) ?_ ?_ using 1
  · exact cos_sub_pi_div_two θ
  · exact hθ.imp' (· - 1 / 2) (by intros; push_cast; linarith)
  · simpa [cos_sub_pi_div_two]

/-- Niven's theorem, giving the possible angles for `θ` in the range `0 .. π`. -/
theorem niven_theta_eq (hθ : ∃ r : ℚ, θ = r * π) (hcos : ∃ q : ℚ, cos θ = q)
    (h_bnd : θ ∈ Set.Icc 0 π) : θ ∈ ({0, π / 3, π / 2, π * (2 / 3), π} : Set ℝ) := by
  have h := niven hθ hcos
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with (h | h | h | h | h) <;> [
    have h₂ := cos_pi;
    have h₂ : cos (π * (2 / 3)) = -1 / 2 := by
      have := cos_pi_sub (π / 3)
      have := cos_pi_div_three
      ring_nf at *
      linarith;;
    have h₂ := cos_pi_div_two;
    have h₂ := cos_pi_div_three;
    have h₂ := cos_zero
  ] <;> simp [injOn_cos h_bnd ⟨by positivity, by linarith [pi_nonneg]⟩ (h₂ ▸ h)]
