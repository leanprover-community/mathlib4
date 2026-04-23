/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.Analytic.Basic
import Batteries.Tactic.Congr
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.Tendsto
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.NhdsWithin

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
see `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`. For computation of the constant term as
`s → 1`, see `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`.
-/

@[expose] public section


open CharZero Set Filter HurwitzZeta

open Complex hiding exp continuous_exp

open scoped Topology Real

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s

/-- The completed Riemann zeta function, `Λ(s)`, which satisfies
`Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (up to a minor correction at `s = 0`). -/
def completedRiemannZeta (s : ℂ) : ℂ := completedHurwitzZetaEven 0 s

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

/-- The completed Riemann zeta function `Λ(s)` is differentiable away from `s = 0` and `s = 1`. -/
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s :=
  differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'

/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]

/-- The residue of `Λ(s)` at `s = 1` is equal to `1`. -/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
  completedHurwitzZetaEven_residue_one 0

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. -/
def riemannZeta := hurwitzZetaEven 0

lemma HurwitzZeta.hurwitzZetaEven_zero : hurwitzZetaEven 0 = riemannZeta := rfl

lemma HurwitzZeta.cosZeta_zero : cosZeta 0 = riemannZeta := by
  simp_rw [cosZeta, riemannZeta, hurwitzZetaEven, if_true, completedHurwitzZetaEven_zero,
    completedCosZeta_zero]

lemma HurwitzZeta.hurwitzZeta_zero : hurwitzZeta 0 = riemannZeta := by
  ext1 s
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

lemma HurwitzZeta.expZeta_zero : expZeta 0 = riemannZeta := by
  ext1 s
  rw [expZeta, cosZeta_zero, add_eq_left, mul_eq_zero, eq_false_intro I_ne_zero, false_or,
    ← eq_neg_self_iff, ← sinZeta_neg, neg_zero]

/-- The Riemann zeta function is differentiable away from `s = 1`. -/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) : DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_hurwitzZetaEven _ hs'

lemma differentiableOn_riemannZeta :
    DifferentiableOn ℂ riemannZeta {1}ᶜ :=
  fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt

lemma analyticOn_riemannZeta :
    AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton

/-- We have `ζ(0) = -1 / 2`. -/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simp_rw [riemannZeta, hurwitzZetaEven, Function.update_self, if_true]

lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
  rw [riemannZeta, hurwitzZetaEven, Function.update_of_ne hs, completedHurwitzZetaEven_zero]

/-- The trivial zeroes of the zeta function. -/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

/-- Riemann zeta functional equation, formulated for `ζ`: if `1 - s ∉ ℕ`, then we have
`ζ (1 - s) = 2 ^ (1 - s) * π ^ (-s) * Γ s * sin (π * (1 - s) / 2) * ζ s`. -/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta, hurwitzZetaEven_one_sub 0 hs (Or.inr hs'), cosZeta_zero, hurwitzZetaEven_zero]

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2

/-!
## Relating the Mellin transform to the Dirichlet series
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

/-- The Riemann zeta function agrees with the naive Dirichlet-series definition when the latter
converges. (Note that this is false without the assumption: when `re s ≤ 1` the sum is divergent,
and we use a different definition to obtain the analytic continuation to all `s`.) -/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero, mul_zero, zero_mul, Real.cos_zero,
    ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

/-- Alternate formulation of `zeta_eq_tsum_one_div_nat_cpow` with a `+ 1` (to avoid relying
on mathlib's conventions for `0 ^ s`). -/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s := by
  have := zeta_eq_tsum_one_div_nat_cpow hs
  rw [Summable.tsum_eq_zero_add] at this
  · simpa [zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · rwa [Complex.summable_one_div_nat_cpow]

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) :
    2 * riemannZeta k = ∑' (n : ℤ), ((n : ℂ) ^ k)⁻¹ := by
  have hkk : 1 < k := by linarith
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat]
  · have h0 : (0 ^ k : ℂ)⁻¹ = 0 := by simp; lia
    norm_cast
    simp [h0, zeta_eq_tsum_one_div_nat_add_one_cpow (s := k) (by simp [hkk]),
      tsum_pnat_eq_tsum_succ (f := fun n => ((n : ℂ) ^ k)⁻¹)]
  · intro n
    simp [Even.neg_pow hk2]
  · exact (Summable.of_nat_of_neg (by simp [hkk]) (by simp [hkk])).of_norm

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
lemma riemannZeta_residue_one : Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by
  exact hurwitzZetaEven_residue_one 0

/-- The residue of `ζ(s)` at `s = 1` is equal to 1, expressed using `tsum`. -/
theorem tendsto_sub_mul_tsum_nat_cpow :
    Tendsto (fun s : ℂ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℂ) ^ s) (𝓝[{s | 1 < re s}] 1) (𝓝 1) := by
  refine (tendsto_nhdsWithin_mono_left ?_ riemannZeta_residue_one).congr' ?_
  · simp
  · filter_upwards [eventually_mem_nhdsWithin] with s hs using
      congr_arg _ <| zeta_eq_tsum_one_div_nat_cpow hs

/-- The residue of `ζ(s)` at `s = 1` is equal to 1 expressed using `tsum` and for a
real variable. -/
theorem tendsto_sub_mul_tsum_nat_rpow :
    Tendsto (fun s : ℝ ↦ (s - 1) * ∑' (n : ℕ), 1 / (n : ℝ) ^ s) (𝓝[>] 1) (𝓝 1) := by
  rw [← tendsto_ofReal_iff, ofReal_one]
  have : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[{s | 1 < re s}] 1) :=
    continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ ↦ by simp_all)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp this).congr fun s ↦ ?_
  simp only [one_div, Function.comp_apply, ofReal_mul, ofReal_sub, ofReal_one, ofReal_tsum,
    ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
