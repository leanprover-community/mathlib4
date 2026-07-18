/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The digamma function

This file defines the digamma function as the logarithmic derivative of the Gamma function and
proves some basic properties.

## Main definitions

* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Complex.digamma_apply_add_one`: The digamma function satisfies the functional equation
  `digamma (s + 1) = digamma s + s⁻¹`.
* `Complex.digamma_apply_add_nat`: The iterated recurrence
  `digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹`.
* `Complex.digamma_reflection`: The reflection formula
  `digamma (1 - s) - digamma s = π * cot (π * s)`.
* `Complex.digamma_two_mul`: The duplication formula
  `digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2`.
* `Complex.meromorphic_digamma`: The digamma function is meromorphic.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

@[expose] public section

namespace Complex

/-- The digamma function, defined as the logarithmic derivative of the Gamma function. -/
noncomputable def digamma : ℂ → ℂ := logDeriv Gamma

theorem digamma_def : digamma = logDeriv Gamma := rfl

@[simp]
theorem digamma_zero : digamma 0 = 0 :=
  logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

theorem digamma_one : digamma 1 = - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, hasDerivAt_Gamma_one.deriv, Gamma_one, div_one]

theorem digamma_one_half : digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, hasDerivAt_Gamma_one_half.deriv, add_comm, Gamma_one_half_eq,
    neg_mul, ← mul_neg, neg_add', Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
  simp

theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ - m) :
    digamma (s + 1) = digamma s + s⁻¹ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  rw [digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_add_one s hs0, Gamma_add_one s hs0,
    add_div, div_mul_cancel_right₀ (Gamma_ne_zero hs), mul_div_mul_left _ _ hs0, add_comm]

/-- **The iterated digamma recurrence** `ψ(s + n) = ψ(s) + ∑_{k < n} 1 / (s + k)`, for
`s ∉ {0, -1, -2, …}`. Proved by induction from `digamma_apply_add_one`. -/
theorem digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) (n : ℕ) :
    digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn (m : ℕ) : s + (n : ℂ) ≠ -(m : ℂ) := fun h ↦
      hs (m + n) (by push_cast at h ⊢; linear_combination h)
    rw [show s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 by push_cast; ring,
      digamma_apply_add_one _ hsn, ih, Finset.sum_range_succ]
    ring

end Complex

open Complex in
/-- The logarithmic derivative of `Gamma ∘ g` at `s` is `deriv g s * digamma (g s)`.
Auxiliary lemma used to prove the reflection and duplication formulas below. -/
theorem HasDerivAt.logDeriv_Gamma {g : ℂ → ℂ} {a s : ℂ} (hg : HasDerivAt g a s)
    (h : ∀ m : ℕ, g s ≠ -(m : ℂ)) :
    logDeriv (fun z ↦ Gamma (g z)) s = a * digamma (g s) := by
  rw [show (fun z ↦ Gamma (g z)) = Gamma ∘ g from rfl,
    logDeriv_comp (differentiableAt_Gamma _ h) hg.differentiableAt, hg.deriv, digamma_def]
  exact mul_comm _ _

namespace Complex

/-- **The digamma reflection formula** `ψ(1 - s) - ψ(s) = π cot (π s)`, for `s ∉ ℤ`.
Proved from `Complex.Gamma_mul_Gamma_one_sub` by taking logarithmic derivatives. -/
theorem digamma_reflection {s : ℂ} (hs : ∀ m : ℤ, s ≠ m) :
    digamma (1 - s) - digamma s = (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * s) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs₀ (m : ℕ) : s ≠ -m := fun h ↦ hs (-m) (by push_cast; exact h)
  have hs₁ (m : ℕ) : 1 - s ≠ -m := fun h ↦ hs (1 + m) (by push_cast; linear_combination -h)
  have hsin : sin ((Real.pi : ℂ) * s) ≠ 0 := fun h ↦ by
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp h
    exact hs k (mul_left_cancel₀ hπ (hk.trans (mul_comm _ _)))
  -- take logarithmic derivatives of Euler's reflection formula `Γ(s) Γ(1 - s) = π / sin (π s)`
  have key : digamma s - digamma (1 - s)
      = -((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * s)) := by
    calc digamma s - digamma (1 - s)
        = logDeriv (fun z ↦ Gamma z * Gamma (1 - z)) s := by
          rw [logDeriv_mul (f := Gamma) (g := fun z ↦ Gamma (1 - z)) s (Gamma_ne_zero hs₀)
              (Gamma_ne_zero hs₁) (differentiableAt_Gamma s hs₀)
              ((differentiableAt_Gamma _ hs₁).comp s (by fun_prop)),
            ((hasDerivAt_id' (x := s)).const_sub 1).logDeriv_Gamma hs₁, ← digamma_def]
          ring
      _ = logDeriv (fun z ↦ (Real.pi : ℂ) / sin ((Real.pi : ℂ) * z)) s := by
          rw [funext Gamma_mul_Gamma_one_sub]
      _ = -((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * s)) := by
          rw [logDeriv_div (f := fun _ ↦ (Real.pi : ℂ)) (g := fun z ↦ sin ((Real.pi : ℂ) * z)) s hπ
                hsin (by fun_prop) (differentiableAt_sin.comp s (by fun_prop)),
              logDeriv_const, Pi.zero_apply,
              show (fun z : ℂ ↦ sin ((Real.pi : ℂ) * z)) = sin ∘ ((Real.pi : ℂ) * ·) from rfl,
              logDeriv_comp differentiableAt_sin (by fun_prop), logDeriv_sin, deriv_const_mul_id]
          ring
  linear_combination -key

/-- **The digamma duplication formula** `ψ(2s) = ½(ψ(s) + ψ(s + ½)) + log 2`, for
`s, s + ½ ∉ {0, -1, -2, …}`. Proved from Legendre's doubling
`Complex.Gamma_mul_Gamma_add_half` by taking logarithmic derivatives. -/
theorem digamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ))
    (hsh : ∀ m : ℕ, s + 1 / 2 ≠ -(m : ℂ)) :
    digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + Complex.log 2 := by
  have h2s (m : ℕ) : 2 * s ≠ -(m : ℂ) := fun h ↦ by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact hs k (by subst hk; push_cast at h ⊢; linear_combination h / 2)
    · exact hsh k (by subst hk; push_cast at h ⊢; linear_combination h / 2)
  have hsqrt : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hpow : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by simp [cpow_eq_zero_iff]
  have hd2 := (((hasDerivAt_id' (x := s)).const_mul 2).const_sub 1).const_cpow
    (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  have hcpow : logDeriv (fun z : ℂ ↦ (2 : ℂ) ^ (1 - 2 * z)) s = -2 * Complex.log 2 := by
    rw [logDeriv_apply, hd2.deriv, div_eq_iff hpow]
    ring
  -- take logarithmic derivatives of Legendre's formula `Γ(s) Γ(s + 1/2) = Γ(2s) 2^(1-2s) √π`
  have key : digamma s + digamma (s + 1 / 2) = 2 * digamma (2 * s) - 2 * Complex.log 2 := by
    calc digamma s + digamma (s + 1 / 2)
        = logDeriv (fun z ↦ Gamma z * Gamma (z + 1 / 2)) s := by
          rw [logDeriv_mul (f := Gamma) (g := fun z ↦ Gamma (z + 1 / 2)) s (Gamma_ne_zero hs)
              (Gamma_ne_zero hsh) (differentiableAt_Gamma s hs)
              ((differentiableAt_Gamma _ hsh).comp s (by fun_prop)),
            ((hasDerivAt_id' (x := s)).add_const (1 / 2)).logDeriv_Gamma hsh, ← digamma_def]
          ring
      _ = logDeriv (fun z ↦ Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z)
            * ((Real.sqrt Real.pi : ℝ) : ℂ)) s := by
          rw [funext Gamma_mul_Gamma_add_half]
      _ = 2 * digamma (2 * s) - 2 * Complex.log 2 := by
          rw [logDeriv_mul_const s _ hsqrt,
            logDeriv_mul (f := fun z ↦ Gamma (2 * z)) (g := fun z ↦ (2 : ℂ) ^ (1 - 2 * z)) s
              (Gamma_ne_zero h2s) hpow ((differentiableAt_Gamma _ h2s).comp s (by fun_prop))
              hd2.differentiableAt,
            ((hasDerivAt_id' (x := s)).const_mul 2).logDeriv_Gamma h2s, hcpow]
          ring
  linear_combination (-1 / 2 : ℂ) * key

theorem meromorphic_digamma : Meromorphic digamma :=
  Meromorphic.Gamma.logDeriv

end Complex
