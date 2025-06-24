import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.Rify

/-! # Niven's Theorem

This file proves Niven's theorem, stating that the only rational angles _in degrees_ which
also have rational cosines, are 0, 30 degrees, and 90 degrees - up to reflection and shifts
by π. Equivalently, the only rational numbers that occur as `cos(π * p / q)` are the five
values `{-1, -1/2, 0, 1/2, 1}`.
-/

theorem niven {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * Real.pi) (hcos : ∃ q : ℚ, Real.cos θ = q) :
      Real.cos θ = 0 ∨ Real.cos θ = 1/2 ∨ Real.cos θ = -1/2 ∨ Real.cos θ = 1 ∨ Real.cos θ = -1 := by
    -- Since $2 \cos(\theta)$ is an algebraic integer and rational, it must be an integer.
    -- Hence, $2 \cos(\theta) \in \{-2, -1, 0, 1, 2\}$.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, 2 * Real.cos θ = k := by
      have h_alg_int : IsIntegral ℤ (2 * Real.cos θ) := by
        rcases hθ with ⟨r, hr⟩
        obtain ⟨p, q, hq_pos, rfl⟩ : ∃ p q : ℤ, q > 0 ∧ r = p / q :=
          ⟨r.num, r.den, by positivity, r.num_div_den.symm⟩
        -- Let $z = e^{i π p / q}$, which is a root of unity.
        set z : ℂ := .exp (.I * θ)
        have hz_root : z ^ (2 * q.natAbs) = 1 := by
          rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
          use p
          simpa [*, field_simps, hq_pos.ne'] using by
            rw [← Int.cast_natCast, ← Int.eq_natAbs_of_nonneg hq_pos.le]
            ring
        -- Since z is a root of unity, 2cos⁡(θ)=z+1z is an algebraic integer.
        rcases (
          have h_sum_int : IsIntegral ℤ z ∧ IsIntegral ℤ z⁻¹ := by
            constructor <;> exact
              ⟨.X ^ (2 * q.natAbs) - 1, Polynomial.monic_X_pow_sub_C _ <| by positivity, by aesop⟩
          h_sum_int.1.add h_sum_int.2) with ⟨f, hf₁, hf₂⟩
        refine ⟨f, hf₁, ?_⟩
        have h_cos_eq : 2 * Real.cos (p / q * Real.pi) = z + z⁻¹ := by
          simpa [Complex.cos, Complex.exp_neg, hr, z] using by ring_nf
        simp_all [Polynomial.eval₂_eq_sum_range, ← Complex.ofReal_inj]
      -- Since $2 \cos(\theta)$ is an algebraic integer and rational, it must be an integer.
      have h_alg_int_rational : ∀ {x : ℝ}, IsIntegral ℤ x → (∃ q : ℚ, x = q) → ∃ k : ℤ, x = k := by
        rintro x h₁ ⟨q, rfl⟩
        replace h₁ : IsIntegral ℤ q := by
          rcases h₁ with ⟨P, hP₁, hP₂⟩
          refine ⟨P, hP₁, ?_⟩
          simpa [Polynomial.eval₂_eq_sum_range, ← @Rat.cast_inj ℝ] using hP₂
        rcases IsIntegrallyClosed.algebraMap_eq_of_integral h₁ with ⟨_, rfl⟩
        exact ⟨_, rfl⟩
      exact h_alg_int_rational h_alg_int ⟨2 * hcos.choose, (by
        push_cast
        linarith [hcos.choose_spec])⟩
    obtain ⟨wθ, rfl⟩ := hθ
    obtain ⟨wc, hwc⟩ := hcos
    -- Since $k$ is an integer and $2 * cos(w * pi) = k$, we have $k ∈ \{-2, -1, 0, 1, 2\}$.
    have hk_values : k ∈ ({ -2, -1, 0, 1, 2 } : Set ℤ) := by
      have : k ≤ 2 := Int.le_of_lt_add_one (by
        rify
        linarith [Real.cos_le_one (wθ * Real.pi)])
      have : k ≥ -2 := Int.le_of_lt_add_one (by
        rify
        linarith [Real.neg_one_le_cos (wθ * Real.pi)])
      interval_cases k <;> norm_num
    rcases hk_values with (rfl|rfl|rfl|rfl|rfl) <;> simp_all
    · simp [show (wc : ℝ) = -1 by linarith]
    · simp [show (wc : ℝ) = -1/2 by linarith]
    · simp [show (wc : ℝ) = 1/2 by linarith]
