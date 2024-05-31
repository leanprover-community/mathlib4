/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.PSeriesComplex

#align_import number_theory.zeta_function from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function `ζ : ℂ → ℂ`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / (s - 1) - 1 / s` wherever the RHS is defined.

Note that mathematically `ζ(s)` is undefined at `s = 1`, while `Λ(s)` is undefined at both `s = 0`
and `s = 1`. Our construction assigns some values at these points; exact formulae involving the
Euler-Mascheroni constant will follow in a subsequent PR.

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`

For special-value formulae expressing `ζ (2 * k)` and `ζ (1 - 2 * k)` in terms of Bernoulli numbers
see `Mathlib.NumberTheory.LSeries.HurwitzZetaValues`. For computation of the constant term as
`s → 1`, see `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib.NumberTheory.LSeries.HurwitzZetaEven`.
-/


open MeasureTheory Set Filter Asymptotics TopologicalSpace Real Asymptotics
  Classical HurwitzZeta

open Complex hiding exp norm_eq_abs abs_of_nonneg abs_two continuous_exp

open scoped Topology Real Nat

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s
#align riemann_completed_zeta₀ completedRiemannZeta₀

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s
#align riemann_completed_zeta completedRiemannZeta

lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ) :
    completedHurwitzZetaEven 0 s = completedRiemannZeta s := rfl

lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := rfl

lemma HurwitzZeta.completedCosZeta_zero (s : ℂ) :
    completedCosZeta 0 s = completedRiemannZeta s := by
  rw [completedRiemannZeta, completedHurwitzZetaEven, completedCosZeta, hurwitzEvenFEPair_zero_symm]

lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, completedCosZeta₀,
    hurwitzEvenFEPair_zero_symm]

lemma completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simp_rw [completedRiemannZeta, completedRiemannZeta₀, completedHurwitzZetaEven_eq, if_true]

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s + 1 / (1 - s)` is entire. -/
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0
#align differentiable_completed_zeta₀ differentiable_completedZeta₀

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`. -/
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]
#align riemann_completed_zeta₀_one_sub completedRiemannZeta₀_one_sub

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]
#align riemann_completed_zeta_one_sub completedRiemannZeta_one_sub

/-- The residue of `Λ(s)` at `s = 1` is equal to `1`. -/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. -/
def riemannZeta := hurwitzZetaEven 0
#align riemann_zeta riemannZeta

lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl

lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
  ext1 s
  rw [expZeta, cosZeta_zero, add_right_eq_self, mul_eq_zero, eq_false_intro I_ne_zero, false_or,
    ← eq_neg_self_iff, ← sinZeta_neg, neg_zero]

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_hurwitzZetaEven _ hs'
#align differentiable_at_riemann_zeta differentiableAt_riemannZeta

/-- We have `ζ(0) = -1 / 2`. -/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_same, if_true]
#align riemann_zeta_zero riemannZeta_zero

lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
  rw [riemannZeta, hurwitzZetaEven, Function.update_noteq hs, completedHurwitzZetaEven_zero]

/-- The trivial zeroes of the zeta function. -/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n
#align riemann_zeta_neg_two_mul_nat_add_one riemannZeta_neg_two_mul_nat_add_one

/-- Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we have
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`. -/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta, hurwitzZetaEven_one_sub 0 hs (Or.inr hs'), cosZeta_zero, hurwitzZetaEven_zero]
#align riemann_zeta_one_sub riemannZeta_one_sub

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
#align riemann_hypothesis RiemannHypothesis

/-!
## Relating the Mellin transform to the Dirichlet series
-/

theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta s =
      (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  have := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simp only [QuotientAddGroup.mk_zero, completedCosZeta_zero] at this
  simp only [this, Gammaℝ_def, mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div,
    ← tsum_mul_left]
  congr 1 with n
  split_ifs with h
  · simp only [h, Nat.cast_zero, zero_cpow (Complex.ne_zero_of_one_lt_re hs), div_zero]
  · rfl
#align completed_zeta_eq_tsum_of_one_lt_re completedZeta_eq_tsum_of_one_lt_re

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm
#align zeta_eq_tsum_one_div_nat_cpow zeta_eq_tsum_one_div_nat_cpow

/-- Alternate formulation of `zeta_eq_tsum_one_div_nat_cpow` with a `+ 1` (to avoid relying
on mathlib's conventions for `0 ^ s`).  -/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]
#align zeta_eq_tsum_one_div_nat_add_one_cpow zeta_eq_tsum_one_div_nat_add_one_cpow

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]
#align zeta_nat_eq_tsum_of_gt_one zeta_nat_eq_tsum_of_gt_one

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  exact hurwitzZetaEven_residue_one 0

/- naming scheme was changed from from `riemannCompletedZeta` to `completedRiemannZeta`; add
aliases for the old names -/
section aliases

@[deprecated (since := "2024-05-27")]
noncomputable alias riemannCompletedZeta₀ := completedRiemannZeta₀

@[deprecated (since := "2024-05-27")]
noncomputable alias riemannCompletedZeta := completedRiemannZeta

@[deprecated (since := "2024-05-27")]
alias riemannCompletedZeta₀_one_sub := completedRiemannZeta₀_one_sub

@[deprecated (since := "2024-05-27")]
alias riemannCompletedZeta_one_sub := completedRiemannZeta_one_sub

@[deprecated (since := "2024-05-27")]
alias riemannCompletedZeta_residue_one := completedRiemannZeta_residue_one

end aliases
