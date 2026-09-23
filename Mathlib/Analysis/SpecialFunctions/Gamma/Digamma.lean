/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv


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
* `Complex.digamma_nat_add_one`: The digamma function at positive integers, in terms of harmonic
  numbers: `digamma (n + 1) = harmonic n - eulerMascheroniConstant`.
* `Complex.digamma_one_sub`: Euler's reflection formula
  `digamma (1 - s) = digamma s + π * cot (π * s)`.
* `Complex.digamma_two_mul`: The duplication formula
  `digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2`.
* `Complex.meromorphic_digamma`: The digamma function is meromorphic.

## TODO

* Prove Gauss' integral representation of the digamma function.
-/

@[expose] public section

open scoped Real

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

open scoped ComplexOrder in
/-- The digamma function at a positive integer, in terms of harmonic numbers. -/
theorem digamma_nat_add_one (n : ℕ) :
    digamma (n + 1) = harmonic n - Real.eulerMascheroniConstant := by
  rw [add_comm _ 1, digamma_apply_add_nat (by grind) n, digamma_one, harmonic]
  push_cast [add_comm (1 : ℂ)]
  ring

open scoped Real in
/-- **Euler's reflection formula for the digamma function**:
`ψ (1 - s) = ψ s + π * cot (π * s)` for `s` not an integer. -/
theorem digamma_one_sub {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    digamma (1 - s) = digamma s + π * cot (π * s) := by
  -- The idea is to apply `logDeriv` to both sides of `Gamma_mul_Gamma_one_sub`. This produces
  -- side conditions, which the two `have`s below allow the `<;> try ...` line to discharge.
  have (m : ℕ) : s ≠ -m := by simpa using hs (-m)
  have (m : ℕ) : 1 - s ≠ -m := fun _ ↦ hs (1 + m) (by push_cast; grind)
  have := congr(logDeriv $(funext Gamma_mul_Gamma_one_sub) s)
  rw [logDeriv_fun_mul, logDeriv_fun_div, ← Function.comp_def Gamma, ← Function.comp_def sin,
    logDeriv_comp, logDeriv_comp] at this <;>
    try first | fun_prop | grind [sin_eq_zero_iff, ofReal_ne_zero, Real.pi_ne_zero]
  simp [digamma_def] at this ⊢
  grind

@[fun_prop]
theorem meromorphic_digamma : Meromorphic digamma :=
  Meromorphic.Gamma.logDeriv

/-- If `g` has derivative `a` at `s`, then the logarithmic derivative of `Gamma ∘ g` at `s` is
`a * digamma (g s)`. -/
theorem _root_.HasDerivAt.logDeriv_Gamma {g : ℂ → ℂ} {a s : ℂ} (hg : HasDerivAt g a s)
    (h : ∀ m : ℕ, g s ≠ -(m : ℂ)) :
    logDeriv (fun z ↦ Gamma (g z)) s = a * digamma (g s) := by
  rw [show (fun z ↦ Gamma (g z)) = Gamma ∘ g from rfl,
    logDeriv_comp (differentiableAt_Gamma _ h) hg.differentiableAt, hg.deriv, digamma_def]
  exact mul_comm _ _

/-- **The digamma duplication formula** `ψ(2s) = ½(ψ(s) + ψ(s + ½)) + log 2`, for
`2s ∉ {0, -1, -2, …}`, which is equivalent to `s` and `s + ½` both avoiding the poles of `ψ`.
Proved from Legendre's doubling `Complex.Gamma_mul_Gamma_add_half` by taking logarithmic
derivatives. -/
theorem digamma_two_mul {s : ℂ} (hs : ∀ m : ℕ, 2 * s ≠ -(m : ℂ)) :
    digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2 := by
  have hs₀ (m : ℕ) : s ≠ -(m : ℂ) := fun h ↦
    hs (2 * m) (by push_cast; linear_combination 2 * h)
  have hs₁ (m : ℕ) : s + 1 / 2 ≠ -(m : ℂ) := fun h ↦
    hs (2 * m + 1) (by push_cast; linear_combination 2 * h)
  have hpow : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by simp [cpow_eq_zero_iff]
  have hd2 := hasDerivAt_id' s |>.const_mul 2 |>.const_sub 1 |>.const_cpow <|
    .inl (by norm_num : (2 : ℂ) ≠ 0)
  -- take logarithmic derivatives of Legendre's formula `Γ(s) Γ(s + 1/2) = Γ(2s) 2^(1-2s) √π`
  suffices key : digamma s + digamma (s + 1 / 2) = 2 * digamma (2 * s) - 2 * log 2 by
    linear_combination (-1 / 2 : ℂ) * key
  calc
    digamma s + digamma (s + 1 / 2) = logDeriv (fun z ↦ Gamma z * Gamma (z + 1 / 2)) s := by
      rw [logDeriv_fun_mul (g := fun z ↦ Gamma (z + 1 / 2)) s (Gamma_ne_zero hs₀)
        (Gamma_ne_zero hs₁) (by fun_prop) (by fun_prop),
        ((hasDerivAt_id' s).add_const (1 / 2)).logDeriv_Gamma hs₁, ← digamma_def]
      ring
    _ = logDeriv (fun z ↦ Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * (√π : ℂ)) s := by
      rw [funext Gamma_mul_Gamma_add_half]
    _ = 2 * digamma (2 * s) - 2 * log 2 := by
      rw [logDeriv_mul_const s (√π : ℂ) (by grind [ofReal_eq_zero, Real.pi_pos]),
        logDeriv_fun_mul (f := fun z ↦ Gamma (2 * z)) s
          (Gamma_ne_zero hs) hpow (by fun_prop) (by fun_prop),
        ((hasDerivAt_id' s).const_mul 2).logDeriv_Gamma hs, mul_one, sub_eq_add_neg]
      congr! 1
      rw [logDeriv_apply, hd2.deriv, div_eq_iff hpow]
      ring

end Complex
