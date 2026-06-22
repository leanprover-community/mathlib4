/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Pietro Monticone, Terence Tao, Yi Yuan
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens theorems

This file establishes the Mertens theorems that estimate sums and products involving primes
or the von Mangoldt function.

## Main definitions

- `E₁Λ`: The error `∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x` in the von Mangoldt form
of Mertens' first theorem.
- `E₁p`: The error `∑ p ∈ primesLE ⌊x⌋₊, (log p) / p - log x` in the prime form of Mertens' first
theorem.

## Main results

- Mertens' first theorem: `|E₁Λ x|` and `|E₁p x|` are both bounded (by `log 4 + 1` and `3`
respectively).  For natural numbers `N`, we obtain the improvement `|E₁p x| ≤ 2`.
- Abstract conversion from first theorem to second theorem

## TODO

Add Mertens' second and third theorems.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al,
https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

/- Move elsewhere-/
namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

namespace Mertens

open Nat hiding log log_pos
open Finset Filter Real Chebyshev intervalIntegral Asymptotics MeasureTheory
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-!
## Bounds on the partial sum of the logarithm

The partial sum of the logarithm can also be expressed as the logarithm of the factorial, as well
as a sum involving the von Mangoldt function.  Here we state these identities and also provide
some upper and lower bounds on the partial sum of `log n`.

TODO: add sharper bounds arising from the Euler-Maclaurin formula.

-/

/-- The partial sum of the logarithm is equal to the log of the factorial. -/
theorem sum_log_eq_log_factorial (N : ℕ) : ∑ n ∈ Ioc 0 N, log n = log N.factorial := by
  rw [← prod_Ico_id_eq_factorial, ← log_prod (by intros; simp; grind), prod_natCast]
  rfl

/-- The partial sum of the logarithm is equal to a weighted sum of the von Mangoldt function. -/
theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have (n : ℕ) : log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← floor_div_natCast]

/-- A crude upper bound on the partial sum of the logarithm. -/
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x - x + log x + 1
    := by
  have h1 := floor_le (by linarith : 0 ≤ x)
  have h2 : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ = ∑ n ∈ Icc 1 ⌊x⌋₊, log n := by rfl
    _ ≤ (∫ t in (1:ℕ)..⌊x⌋₊, log t) + log x := by
      rw [← sum_Ico_add_eq_sum_Icc (by simpa)]
      gcongr
      exact (strictMonoOn_log.monotoneOn.mono (by grind)).sum_le_integral_Ico (f := log) h2
    _ ≤ (∫ t in 1..x, log t) + log x := by
      norm_cast; gcongr
      apply integral_mono_interval (by rfl) (mod_cast h2) h1 _ intervalIntegrable_log'
      exact ae_restrict_of_forall_mem (by measurability) (fun _ _ ↦ (Real.log_pos (by grind)).le)
    _ = _ := by simp; ring

/-- An even cruder upper bound on the partial sum of the logarithm. -/
theorem sum_log_le' {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := by
  linarith [sum_log_le hx, log_le_sub_one_of_pos (by linarith)]

/-- A crude lower bound on the partial sum of the logarithm. -/
theorem le_sum_log {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x - log x + 1 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊x⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊x⌋₊ + 1), log n := by simp [← add_sum_Ioc_eq_sum_Icc this]; rfl
  _ = ∑ n ∈ Ico 1 ⌊x⌋₊, log (n + 1 : ℕ) := by rw [← sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert ((strictMonoOn_log.mono (by grind)).monotoneOn.integral_le_sum_Ico this).ge
    norm_cast
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [integral_symm]
    rw [sub_neg_eq_add, integral_add_adjacent_intervals] <;> exact intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log x := by
    gcongr
    apply integral_mono_on (floor_le (by linarith)) intervalIntegrable_log'
      intervalIntegrable_const
    intro _ _; rify at this; gcongr <;> grind
  _ ≥ _ := by
    have : 0 ≤ log x := log_nonneg hx
    have : x - ⌊x⌋₊ ≤ 1 := by linarith [lt_floor_add_one x]
    grw [integral_log, log_one, intervalIntegral.integral_const, smul_eq_mul, this]
    linarith

/-- An even cruder lower bound on the partial sum of the logarithm. -/
theorem le_sum_log' {x : ℝ} (hx : 1 ≤ x) : x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  linarith [le_sum_log hx, log_le_self (by linarith)]

/-- A sharper bound on the partial sum of the logarithm in the natural number case. -/
theorem le_sum_log_nat {N : ℕ} : N * log N - N ≤ ∑ n ∈ Ioc 0 N, log n := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 0 ≤ log N := by positivity
  have : 0 ≤ log (2 * Real.pi) := log_nonneg (by linarith [two_le_pi])
  grw [sum_log_eq_log_factorial, ←Stirling.le_log_factorial_stirling hN]
  linarith


/-!
## An abstract theory of Mertens weights

We introduce the notion of a _Mertens weight_, which is a function `f : ℕ → ℝ` vanishing at
`0` and `1` that obeys upper and lower bounds on the quantity `∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x`.
Such weights automatically obey versions of Mertens' first and second theorems.  Later we will
construct two specific Mertens weights, the von Mangoldt weight and the prime weight, which give
the two standard forms of these theorems.
-/

/-- A weight `F` is a bundled function `F.f : ℕ → ℝ` for which the quantity
`∑ n ∈ Icc 0 ⌊x⌋₊, F.f n - log x` is bounded above and below for `x ≥ 1`, and which vanishes
at `0` and `1`. -/
class Weight where
  f : ℕ → ℝ
  h0 : f 0 = 0
  h1 : f 1 = 0
  C_lo : ℝ
  C_hi : ℝ
  le_first' : ∀ x ≥ 1, C_lo ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x
  first_le' : ∀ x ≥ 1, ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x ≤ C_hi
namespace Weight

open intervalIntegral

/- Move? -/
attribute [fun_prop] measurable_from_top

variable (F : Weight) (x : ℝ) (N : ℕ)

/-- The first Mertens error for a weight `F` is defined as
`F.E₁ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, F.f n - log x`. -/
noncomputable def E₁ := ∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x

lemma sum_f_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, f n = log x + F.E₁ x := by grind [E₁]

lemma sum_f_eq' : ∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + F.E₁ x := by
  simpa [← add_sum_Ioc_eq_sum_Icc, h0] using F.sum_f_eq x

lemma sum_f_eq_nat : ∑ n ∈ Ioc 0 N, f n = log N + F.E₁ N := by
  simpa using F.sum_f_eq N

lemma le_first {t : ℝ} (ht : t ≥ 1) : C_lo ≤ F.E₁ t := le_first' t ht

lemma first_le {t : ℝ} (ht : t ≥ 1) : F.E₁ t ≤ C_hi := first_le' t ht

lemma hi_nonneg : 0 ≤ F.C_hi := by
  simpa [h0, h1, show Icc 0 1 = {0, 1} by rfl] using first_le' 1 (by rfl)

lemma lo_nonpos : F.C_lo ≤ 0 := by
  simpa [h0, h1, show Icc 0 1 = {0, 1} by rfl] using le_first' 1 (by rfl)

/-- An absolute value bound for the first Mertens error. -/
noncomputable def C₁ := max (-C_lo) C_hi

lemma C₁_nonneg : 0 ≤ F.C₁ := by simp [C₁, hi_nonneg, lo_nonpos]

/-- The abstract Mertens first theorem. -/
theorem first_theorem' {x : ℝ} (hx : 1 ≤ x) : |F.E₁ x| ≤ F.C₁ := by
  grw [abs_le, ← F.le_first hx, F.first_le hx]; grind [Weight.C₁]

theorem first_theorem {x : ℝ} (hx : 1 ≤ x) : |∑ n ∈ Ioc 0 ⌊x⌋₊, f n - log x| ≤ F.C₁ := by
  simpa [F.sum_f_eq x] using F.first_theorem' hx

theorem first_theorem_nat : |∑ n ∈ Ioc 0 N, f n - log N| ≤ F.C₁ := by
  by_cases! hN : N = 0
  · simp [hN, C₁_nonneg]
  simpa using F.first_theorem (mod_cast (by lia) : 1 ≤ (N : ℝ))

theorem first_theorem_error_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, F.f n - log x)
    =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one, eventually_atTop]
  exact ⟨F.C₁, 1, fun _ ↦ F.first_theorem⟩

theorem first_theorem_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, F.f n) ~[atTop] log :=
  (F.first_theorem_error_bounded.trans_isLittleO (isLittleO_const_log_atTop)).isEquivalent

/-- The Meissel--Mertens constant associated to a weight `F` is defined as
`M = (∫ t in .Ioi 2, (t * log t^2)⁻¹ * E₁ t) + 1 - log (log 2)`.
-/
noncomputable def M := (∫ t in .Ioi 2, (t * log t^2)⁻¹ * F.E₁ t) + 1 - log (log 2)

/- The second Mertens error for a weight `F` is defined as
`E₂ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - M`. -/
noncomputable def E₂ := ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - F.M

lemma sum_f_div_log_eq' : ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + F.M + F.E₂ x := by
  grind [E₂]

lemma sum_f_div_log_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n = log (log x) + F.M + F.E₂ x := by
  simpa [← add_sum_Ioc_eq_sum_Icc, h0] using F.sum_f_div_log_eq' x

private noncomputable def inv : ℝ → ℝ := (·⁻¹)
private noncomputable def inv_log : ℝ → ℝ := inv ∘ log
private noncomputable def log_log : ℝ → ℝ := fun x ↦ log (log x)

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv log_log x = (inv * inv_log^2 * log) x := by
  unfold log_log
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  simp [inv, inv_log, field]

@[fun_prop]
private lemma ContinuousOn.log_Ioi_one : ContinuousOn log (.Ioi 1) :=
  continuousOn_log.mono (by grind)

@[fun_prop]
private lemma ContinuousOn.log_inv_Ioi_one : ContinuousOn inv_log (.Ioi 1) :=
  log_Ioi_one.inv₀ (by simp; grind)

@[fun_prop]
private lemma ContinuousOn.inv_Ioi_one : ContinuousOn inv (.Ioi 1) :=
  continuousOn_inv₀.mono (by grind)

@[fun_prop]
private lemma DifferentiableOn.log_log : DifferentiableOn ℝ log_log (.Ioi 1) :=
  (differentiableOn_log.mono (by grind)).log (by simp; grind)

/-- Remove after #40872 lands -/
@[fun_prop]
theorem ContinuousOn.const_smul' {M : Type*} {α : Type*} {β : Type*} [TopologicalSpace α]
    [SMul M α] [ContinuousConstSMul M α] [TopologicalSpace β] {g : β → α} {s : Set β}
    (hg : ContinuousOn g s) (c : M) : ContinuousOn (c • g) s := hg.const_smul c

/-- Remove after #40872 lands -/
@[to_additive (attr := fun_prop)]
theorem ContinuousOn.inv' {G : Type*} {X : Type*} [TopologicalSpace X] [TopologicalSpace G] [Inv G]
[ContinuousInv G] {f : X → G} {s : Set X}
    (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s := hf.inv

/-- Remove after #40872 lands -/
@[fun_prop]
theorem ContinuousOn.pow' {M : Type*} {X : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [Monoid M] [ContinuousMul M] {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (f^n) s := hf.pow n

private lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    (∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * log t) = log (log x) - log (log 2) := by
  suffices ∫ (t : ℝ) in 2..x, (inv * inv_log ^ 2 * log) t = log_log x - log_log 2 by
    unfold inv_log inv log_log at this; convert this; simp [field]
  rw [← integral_deriv_eq_sub (f := log_log)]
  · exact intervalIntegral.integral_congr
      fun _ _ ↦ (deriv_log_log (by grind [Set.uIcc_of_le])).symm
  · intro t ht
    exact DifferentiableOn.log_log.differentiableAt (Ioi_mem_nhds (by grind [Set.uIcc_of_le]))
  · refine (ContinuousOn.congr (f := inv * inv_log^2 * log) ?_ ?_).intervalIntegrable
    · apply ContinuousOn.mono (s := .Ioi 1) _ (by grind [Set.uIcc_of_le])
      fun_prop
    · intro t ht
      exact deriv_log_log (by grind [Set.uIcc_of_le])

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (c • (inv * inv_log^2)) (.Ioi x) volume := by
  apply Integrable.const_mul
  refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log, inv, inv_log, field]
  · intro t ht
    have : 0 < t := by grind
    simp only [Pi.mul_apply, inv, Pi.pow_apply]; positivity

theorem E₁_div_integrable {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t ↦ (t * log t^2)⁻¹ * F.E₁ t) (.Ioi x) volume := by
  apply Integrable.mono (integrable_const_div_mul_log_sq F.C₁ hx)
  · exact Measurable.aestronglyMeasurable (by unfold Weight.E₁; fun_prop)
  filter_upwards [ae_restrict_mem (by measurability)] with t ht
  simp only [Set.mem_Ioi, mul_inv_rev, norm_mul, norm_inv, norm_pow, norm_eq_abs, sq_abs, inv_log,
    Pi.smul_apply, Pi.mul_apply, inv, Pi.pow_apply, Function.comp_apply, inv_pow,
    smul_eq_mul] at ht ⊢
  have : 0 < log t := log_pos (by linarith)
  grw [F.first_theorem' (by linarith), le_abs_self F.C₁]
  simp [field]

theorem E₂_eq {x : ℝ} (hx : 2 ≤ x) :
    F.E₂ x = (log x)⁻¹ * F.E₁ x - ∫ t in .Ioi x, (t * log t^2)⁻¹ * F.E₁ t := by
  have : 0 < log x := log_pos (by linarith)
  suffices ∫ t in 2..x, (t * log t^2)⁻¹ * F.E₁ t = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n -
    (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - log (log x) + log (log 2) by
    have : (∫ t in 2..x, (t * log t^2)⁻¹ * F.E₁ t) + ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * F.E₁ t
      = ∫ t in .Ioi 2, (t * log t^2)⁻¹ * F.E₁ t := integral_interval_add_Ioi
        (F.E₁_div_integrable (by rfl)) (F.E₁_div_integrable hx)
    have : (log x)⁻¹ * F.E₁ x = (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - 1 := by
      rw [F.sum_f_eq']; field_simp; abel
    unfold Weight.E₂ Weight.M; linarith
  have : ∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, f n =
      (∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * log t)
      + ∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * F.E₁ t := by
    simp only [mul_inv_rev, sum_f_eq', mul_add]
    apply intervalIntegral.integral_add
    <;> rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.mono (s := .Ioi 1) _ (by grind)
      convert (by fun_prop : ContinuousOn (inv * inv_log^2 * log) (.Ioi 1)) using 2
      simp [inv, inv_log, field]
    apply Integrable.mono (g := fun t ↦ (log 2 ^ 2)⁻¹ * t⁻¹ * F.C₁)
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.mono (s := .Ioi 1) _ (by grind)
      convert (by fun_prop : ContinuousOn (((log 2 ^ 2)⁻¹ * F.C₁) • inv) (.Ioi (1:ℝ))) using 2
      simp [inv, field]
    · exact Measurable.aestronglyMeasurable (by unfold Weight.E₁; fun_prop)
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp [Set.mem_Ioc] at ht
    simp only [norm_mul, norm_inv, norm_pow, norm_eq_abs, sq_abs]
    grw [F.first_theorem' (by linarith), le_abs_self F.C₁]; gcongr; order
  rw [integral_one_div_mul_log hx] at this
  rw [sum_mul_eq_sub_integral_mul₁ _ h0 h1 x (f := fun t ↦ (log t)⁻¹)]
  · suffices ∫ t in .Ioc 2 x, deriv (fun t ↦ (log t)⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
        - ∫ t in 2..x, (t * log t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, f n by linarith
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_of_le hx]
    apply setIntegral_congr_fun (by measurability)
    intro t ht
    simp [field]
  · intro t ht
    simp at ht
    exact DifferentiableAt.fun_inv (by simp; linarith) (by simp; grind)
  · apply (ContinuousOn.mono (s := .Ioi 1) _ (by grind)).integrableOn_Icc
    rw [deriv_inv_log']
    convert (by fun_prop : ContinuousOn (-inv * inv_log^2) (.Ioi (1:ℝ))) using 2
    simp [inv, inv_log, field]

private theorem integ_div_mul_log_sq {x : ℝ} (C : ℝ) (hx : 2 ≤ x) :
    ∫ (t : ℝ) in .Ioi x, (t * log t ^ 2)⁻¹ * C = C / log x := by
    convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := (- C / log ·)) ?_
      (integrable_const_div_mul_log_sq C hx) ?_ using 1
    · simp [inv, inv_log]; grind
    · field
    · intro t ht; simp at ht
      convert! (hasDerivAt_const _ (-C)).fun_div (hasDerivAt_log (by linarith)) ?_ using 1
      · simp [inv, inv_log]; grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-C) using 1
    simp

private lemma inv_mul_sq_nonneg {x t : ℝ} (ht : t ∈ Set.Ioi x) (hx : 1 < x)
    : 0 ≤ (t * log t ^ 2)⁻¹ := by
  simp at ht
  have : 0 < t := by linarith
  have : 0 < log t := log_pos (by linarith)
  positivity

theorem M_bounds :
    F.M ≤ C_hi / (log 2) + 1 - log (log 2) ∧ C_lo / (log 2) + 1 - log (log 2) ≤ F.M := by
  have hbound : ∀ t ≥ 1, |F.E₁ t| ≤ max (-C_lo) C_hi := by
    intro t ht; grw [abs_le, ← F.le_first ht, F.first_le ht]; grind
  unfold Weight.M
  rw [← integ_div_mul_log_sq C_hi (by rfl), ← integ_div_mul_log_sq C_lo (by rfl)]
  have := F.E₁_div_integrable (by rfl)
  have hinteg (C : ℝ) : IntegrableOn (fun t ↦ (t * log t ^ 2)⁻¹ * C) (.Ioi 2) volume := by
    convert integrable_const_div_mul_log_sq C (by rfl) using 2 with x; simp [inv_log, inv]; grind
  have : NullMeasurableSet (.Ioi (2 : ℝ)) volume := by measurability
  constructor <;> gcongr with t ht
  exacts [hinteg C_hi, inv_mul_sq_nonneg ht (by norm_num), F.first_le (by grind),
          hinteg C_lo, inv_mul_sq_nonneg ht (by norm_num), F.le_first (by grind)]

theorem second_theorem' {x : ℝ} (hx : 2 ≤ x) :
    |F.E₂ x| ≤ (C_hi - C_lo) / log x := by
  have : 0 < log x := log_pos (by linarith)
  have := F.E₁_div_integrable hx
  have hinteg (C : ℝ) : IntegrableOn (fun t ↦ (t * log t ^ 2)⁻¹ * C) (.Ioi x) volume := by
    convert integrable_const_div_mul_log_sq C hx using 2 with x; simp [inv_log, inv]; grind
  have : NullMeasurableSet (.Ioi x) volume := by measurability
  rw [F.E₂_eq hx, abs_le]
  constructor
  · calc
      _ ≥ (log x)⁻¹ * C_lo - ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * C_hi := by
        gcongr with t ht
        exacts [F.le_first (by linarith : 1 ≤ x), hinteg C_hi,
          inv_mul_sq_nonneg ht (by linarith), F.first_le (by grind)]
      _ = _ := by rw [integ_div_mul_log_sq C_hi hx]; simp [field]
  · calc
      _ ≤ (log x)⁻¹ * C_hi - ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * C_lo := by
        gcongr with t ht
        exacts [F.first_le (by linarith : 1 ≤ x), hinteg C_lo,
          inv_mul_sq_nonneg ht (by linarith), F.le_first (by grind)]
      _ = _ := by rw [integ_div_mul_log_sq C_lo hx]; simp [field]

theorem second_theorem {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - F.M| ≤ (C_hi - C_lo) / log x := by
  grw [← F.second_theorem' hx, F.sum_f_div_log_eq x]; ring_nf; rfl

theorem second_theorem_nat (hN : 2 ≤ N) :
  |∑ n ∈ Ioc 0 N, (log n)⁻¹ * f n - log (log N) - F.M| ≤ (C_hi - C_lo) / log N := by
  simpa using F.second_theorem (mod_cast (by lia) : 2 ≤ (N : ℝ))

theorem second_theorem_error_bigO_inv_log :
  (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - F.M) =O[atTop] (1 / log ·) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use C_hi - C_lo, 2
    intro x hx
    convert F.second_theorem hx using 1
    have : 0 < log x := log_pos (by linarith)
    grind [abs_of_pos this]

theorem second_theorem_error_littleO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - F.M) =o[atTop] (fun _ ↦ (1:ℝ)) :=
  F.second_theorem_error_bigO_inv_log.trans_isLittleO inv_log_eq_o_one

theorem second_theorem_error_bounded : ∃ C, ∀ x ≥ 2,
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)| ≤ C := by
  refine ⟨ |F.M| + (C_hi - C_lo) / log 2, fun x hx ↦ ?_ ⟩
  have : 0 ≤ C_hi - C_lo := by linarith [F.hi_nonneg, F.lo_nonpos]
  grw [← hx, ← F.second_theorem hx, ← abs_add_le]
  ring_nf; rfl

theorem second_theorem_error_bigO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
  obtain ⟨ C, _ ⟩ := F.second_theorem_error_bounded
  use C, 2

theorem second_theorem_asymp :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, (log n)⁻¹ * f n) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! F.second_theorem_error_bigO_one using 1

end Weight



section ConstructWeights

/-!
## Constructing the two Mertens weights

In this section we construct the two standard Mertens weights:

* The von Mangoldt weight `fΛ n = Λ n / n`, where `Λ` is the von Mangoldt function.
* The prime weight `fp n = log n / n` if `n` is prime and `0` otherwise.

-/

variable (x : ℝ) (N : ℕ)

noncomputable def fΛ : ℕ → ℝ := fun n ↦ Λ n / n

noncomputable def fp : ℕ → ℝ := fun n ↦ if n.Prime then log n / n else 0

private theorem sum_fp_le_sum_fΛ : ∑ n ∈ Ioc 0 ⌊x⌋₊, fp n ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, fΛ n := by
  unfold fp fΛ
  gcongr with p _
  split_ifs with hp
  · simp [vonMangoldt_apply_prime hp]
  have : 0 ≤ Λ p := vonMangoldt_nonneg
  positivity

private theorem le_mul_sum_fΛ {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, fΛ n := calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by simp [mul_sum, fΛ]; ring_nf
  _ ≥ _ := by
    rw [sum_log_eq_sum_mangoldt]
    gcongr; exacts [vonMangoldt_nonneg, floor_le <| div_nonneg (by linarith) (by linarith)]

private theorem sum_fp_eq : ∑ n ∈ Ioc 0 ⌊x⌋₊, fp n = ∑ p ∈ primesLE ⌊x⌋₊, log p / p := by
  simp [fp, primesLE_eq_filter_Ioc_zero, sum_filter]

private theorem mul_sum_fp_le :
    x * ∑ n ∈ Ioc 0 ⌊x⌋₊, fp n ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n + θ x := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * (x / p) := by
    rw [sum_fp_eq, mul_sum]; ring_nf
  _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p * (⌊x / p⌋₊ + 1) := by gcongr; exact lt_floor_add_one _|>.le
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p * ⌊x / p⌋₊ + θ x := by
    simp [mul_add, sum_add_distrib, theta, primesLE_eq_filter_Ioc_zero]
  _ ≤ _ := by
    rw [sum_log_eq_sum_mangoldt, primesLE_eq_filter_Ioc_zero, sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

private theorem sum_fp_le {x : ℝ} (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, fp n ≤ log x + log 4 := by
  apply le_of_mul_le_mul_left _ (by linarith : 0 < x)
  grw [mul_sum_fp_le, theta_le_log4_mul_x (by linarith), sum_log_le' hx]
  ring_nf; rfl

/-- The summand defining the constant `E₁` below. -/
noncomputable def e₁ : ℕ → ℝ := fun p ↦ if p.Prime then log p / (p * (p - 1)) else 0

/-- The constant `E₁ = 0.755366...` (https://oeis.org/A138312) is defined as the sum of
`log p / (p * (p-1))` over primes `p`. -/
noncomputable def E₁ : ℝ := ∑' p : ℕ, e₁ p

lemma e₁_nonneg (p : ℕ) : 0 ≤ e₁ p := by
  unfold e₁
  split_ifs with h
  · have : 1 ≤ (p : ℝ) := mod_cast h.one_le
    positivity
  rfl

theorem e₁_summable : Summable e₁ := by
  refine (summable_one_div_nat_rpow.mpr (by norm_num : 1 < (3 : ℝ) / 2) |>.const_div
    4).of_nonneg_of_le e₁_nonneg fun p ↦ ?_
  unfold e₁
  split_ifs with h
  · have : 2 ≤ (p : ℝ) := mod_cast h.two_le
    have denom : p * ((p : ℝ) - 1) ≥ p ^ 2 / 2 := by nlinarith
    grw [log_le_rpow_div (cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2), denom]
    · field_simp
      rw [mul_assoc, ← rpow_add (by positivity)]
      ring_nf; norm_cast
    grind
  · positivity

/-- An upper bound for `E₁`. -/
theorem E₁_le : E₁ ≤ 1 := by
  refine e₁_summable.tsum_le_of_sum_range_le (fun N ↦ ?_)
  have : ∑ n ∈ range N, e₁ n ≤ ∑ n ∈ range (2 * N + 5), e₁ n :=
    sum_le_sum_of_subset_of_nonneg (by grind) (fun n _ _ ↦ e₁_nonneg n)
  have : ∑ n ∈ range (2 * N + 5), e₁ n = log 2 / 2 + log 3 / 6 + ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n
      := by
    convert sum_union (s₁ := {0,1,2,3,4}) (s₂ := .Ico 5 (2 * N + 5)) (by grind [disjoint_left])
    · ext; simp; lia
    simp [e₁, prime_two, prime_three, not_prime_four]
    ring_nf
  have : ∑ n ∈ .Ico 5 (2 * N + 5), e₁ n = ∑ n ∈ .range N, e₁ (2 * n + 5) := by
    apply (sum_of_injOn (2 * · + 5) (by intro; grind) (by intro; grind) _ (by simp)).symm
    simp only [mem_Ico, coe_range, Set.mem_image, Set.mem_Iio, not_exists, not_and, e₁,
      ite_eq_right_iff, div_eq_zero_iff, log_eq_zero, cast_eq_zero, cast_eq_one,
      _root_.mul_eq_zero, and_imp]
    intro p _ _ h hp
    obtain ⟨ m, rfl ⟩ := hp.odd_of_ne_two (by lia)
    specialize h (m - 2)
    lia
  let g : ℝ → ℝ := fun t ↦ log (2 * t + 3) / (2 * t + 3)^2
  have : ∑ n ∈ .range N, e₁ (2 * n + 5) ≤ (5/4) * ∑ n ∈ .range N, g (n + 1) := by
    simp only [e₁, g, cast_add, cast_mul, cast_ofNat, mul_sum]
    gcongr with i hi
    ring_nf
    have : 0 ≤ log (5 + (i : ℝ) * 2) := log_nonneg (by norm_cast; lia)
    split_ifs
    · field_simp; ring_nf; gcongr <;> norm_num
    positivity
  have : ∑ n ∈ .range N, g (n + 1) ≤ ∫ x in 0..N, g x := by
    convert (antitoneOn_of_deriv_nonpos (convex_Icc 0 _) ..).sum_le_integral (a := N) (f := g)
        using 1
    · simp
    · simp
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      simp only [Set.mem_Icc, g] at ht ⊢
      have : (2 * t + 3) ≠ 0 := by linarith
      fun_prop (disch := grind)
    · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
      rw [interior_Icc, Set.mem_Ioo] at ht
      have : (2 * t + 3) ^ 2 ≠ 0 := by simp; linarith
      fun_prop (disch := grind)
    · intro t ht
      simp at ht
      rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind),
        deriv_comp_mul_left 2 (fun t ↦ log (t + 3)), deriv_comp_add_const, deriv_log,
        deriv_comp_mul_left 2 (fun t ↦ (t + 3) ^ 2)]
      simp
      field_simp
      have : 3 ≤ 2 * t + 3 := by linarith
      have : 2 * log (2 * t + 3) ≥ 1 := by grw [← ht.1]; simp; linarith [log_three_gt_d9]
      grw [this]; simp
  have : ∫ x in 0..N, g x ≤ (log 3 + 1) / 6 := by
    let f : ℝ → ℝ := fun t ↦ (-log (2 * t + 3) - 1) / (2 * (2 * t + 3))
    have {x : ℝ} (hx : 0 ≤ x) : HasDerivAt f (g x) x := by
      have : HasDerivAt (2 * · + 3) 2 x := HasDerivAt.add_const _ (hasDerivAt_const_mul 2)
      convert! HasDerivAt.comp x ?_ this (h₂ := fun t ↦ (-log t - 1) / (2 * t))
          (h₂' := log (2 * x + 3) / (2 * (2 * x + 3)^2)) using 1
      · grind
      convert! HasDerivAt.fun_div (c' := -1 / (2 * x + 3)) _ (hasDerivAt_const_mul 2) _ using 1
      · field
      · convert! ((hasDerivAt_log (by linarith : 2 * x + 3 ≠ 0)).neg).sub_const _ using 1
        grind
      linarith
    have hN : 0 ≤ (N : ℝ) := cast_nonneg' N
    rw [integral_eq_sub_of_hasDerivAt (f := f)]
    · have : 0 ≤ log (3 + N * 2) := log_nonneg (by norm_cast; linarith)
      simp [f]; field_simp; grind
    · grind [Set.uIcc_of_le]
    apply ((ContinuousOn.log (f := (2 * · + 3)) (by fun_prop) (by grind [Set.uIcc_of_le])).div₀
        (by fun_prop) _).intervalIntegrable
    rw [Set.uIcc_of_le hN]; simp; grind
  linarith [log_two_lt_d9, log_three_lt_d9]

theorem E₁_nonneg : 0 ≤ E₁ := tsum_nonneg e₁_nonneg

theorem sum_von_mangoldt_div_le_sum_log_prime_div_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p + E₁ := by
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, sum_PrimePow_eq_sum_sum _
    (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x ^ (1 / (k : ℝ))⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Prime.pow_minFac (by simp_all) (by grind)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp only [primesLE_eq_filter_Ioc_zero]
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    rw [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity))
    gcongr
    apply le_max_right
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log p / p +
    ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ primesLE ⌊x⌋₊, log p / (p ^ k : ℕ) := by
    simp [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
  _ ≤ _ := by
    gcongr
    calc
    _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / (p * (p - 1)) := by
      rw [sum_comm]
      gcongr with p hp
      simp_rw [← mul_one_div (log p), cast_pow, ← one_div_pow, ← mul_sum]
      rw [primesLE_eq_filter_Ioc_zero, mem_filter, mem_Ioc] at hp
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [primesLE_eq_filter_Ioc_zero, sum_filter]
      exact e₁_summable.sum_le_tsum _ fun p _ ↦ e₁_nonneg p

/-- The von Mangoldt weight `f : ℕ → ℝ := fun n ↦ Λ n / n`. -/
@[reducible]
noncomputable def Weight.vonMangoldt : Weight := {
  f := fΛ
  h0 := by simp [fΛ]
  h1 := by simp [fΛ]
  C_lo := -2
  C_hi := log 4 + 1
  le_first' x hx := by
    suffices x * (log x - 2) ≤ x * ∑ n ∈ Ioc 0 ⌊x⌋₊, fΛ n by
      linarith [le_of_mul_le_mul_left this (by linarith)]
    grw [← le_mul_sum_fΛ (by linarith), ← le_sum_log' hx]
    linarith [log_le_self (by linarith : 0 ≤ x)]
  first_le' x hx := by
    unfold fΛ
    linarith [sum_fp_le hx, E₁_le, sum_von_mangoldt_div_le_sum_log_prime_div_add_E₁ hx, sum_fp_eq x]
}

theorem Weight.vonMangoldt_f_eq : vonMangoldt.f = fΛ := rfl

theorem Weight.vonMangoldt_C_lo_eq : vonMangoldt.C_lo = -2 := rfl

theorem Weight.vonMangoldt_C_hi_eq : vonMangoldt.C_hi = log 4 + 1 := rfl

theorem Weight.vonMangoldt_C_eq : vonMangoldt.C₁ = log 4 + 1 := by
  simp [C₁, vonMangoldt_C_lo_eq, vonMangoldt_C_hi_eq]
  linarith [log_four_eq, log_two_gt_d9]

/-- The prime weight `f : ℕ → ℝ := fun n ↦ 1 / n` if `n` is prime and `0` otherwise. -/
@[reducible]
noncomputable def Weight.prime : Weight := {
  f := fp
  h0 := by simp [fp]
  h1 := by simp [fp]
  C_lo := -3
  C_hi := log 4
  le_first' x hx := by
    have : -2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x := Weight.vonMangoldt.le_first' x hx
    linarith [E₁_le, sum_von_mangoldt_div_le_sum_log_prime_div_add_E₁ hx, sum_fp_eq x]
  first_le' x hx := by linarith [sum_fp_le hx]
}

theorem Weight.prime_f_eq : prime.f = fp := rfl

theorem Weight.prime_C_lo_eq : prime.C_lo = -3 := rfl

theorem Weight.prime_C_hi_eq : prime.C_hi = log 4 := rfl

theorem Weight.prime_C_eq : prime.C₁ = 3 := by
  simp [C₁, prime_C_lo_eq, prime_C_hi_eq]
  linarith [log_four_eq, log_two_lt_d9]

end ConstructWeights

section FirstTheorem

/-
## The first Mertens theorem

-/

variable {x : ℝ} (N : ℕ)

theorem le_sum_von_Mangoldt_div_sub (hx : 1 ≤ x) : - 2 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x :=
 Weight.vonMangoldt.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_von_Mangoldt_div_sub_nat : - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / n - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  suffices N * (log N - 1) ≤ N * ∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, fΛ n by
    simp [fΛ] at this
    linarith [le_of_mul_le_mul_left this (by norm_cast; lia)]
  have : 0 ≤ (N : ℝ) := mod_cast (by lia)
  have := le_mul_sum_fΛ this
  grw [← le_mul_sum_fΛ (mod_cast (by lia)), floor_natCast, ←le_sum_log_nat]
  ring_nf; rfl

theorem le_sum_log_prime_div_sub (hx : 1 ≤ x) : - 3 ≤ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x
    := (sum_fp_eq x).symm ▸ Weight.prime.le_first' x hx

/-- A sharper lower bound in the case of natural numbers. -/
theorem le_sum_log_prime_div_sub_nat : - 2 ≤ ∑ p ∈ primesLE N, log p / p - log N := by
  by_cases! hN : N = 0
  · simp [hN]
  have := sum_von_mangoldt_div_le_sum_log_prime_div_add_E₁ (mod_cast (by lia) : 1 ≤ (N : ℝ))
  simp at this
  linarith [le_sum_von_Mangoldt_div_sub_nat N, E₁_le]

theorem sum_von_Mangoldt_div_sub_le (hx : 1 ≤ x) : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x ≤ log 4 + 1
    := Weight.vonMangoldt.first_le' x hx

theorem sum_log_prime_div_sub_le (hx : 1 ≤ x) : ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x ≤ log 4
    := (sum_fp_eq x).symm ▸ Weight.prime.first_le' x hx

theorem abs_sum_von_Mangoldt_div_sub_le (hx : 1 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x| ≤ log 4 + 1 := by
    convert! Weight.vonMangoldt.first_theorem hx
    rw [Weight.vonMangoldt_C_eq]

theorem abs_sum_von_Mangoldt_div_sub_le_nat :
    |∑ n ∈ Ioc 0 N, Λ n / n - log N| ≤ log 4 + 1 := by
    convert! Weight.vonMangoldt.first_theorem_nat N
    rw [Weight.vonMangoldt_C_eq]

theorem abs_sum_log_prime_div_sub_le (hx : 1 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x| ≤ 3 := by
    convert! (sum_fp_eq x).symm ▸ Weight.prime.first_theorem hx
    rw [Weight.prime_C_eq]

/-- A sharper bound in the case of natural numbers. -/
theorem abs_sum_log_prime_div_sub_le_nat : |∑ p ∈ primesLE N, log p / p - log N| ≤ 2 := by
  by_cases! hN : N = 0
  · simp [hN]
  have : 1 ≤ (N:ℝ) := mod_cast (by lia)
  rw [abs_le']; constructor
  · trans log 4
    · simpa using sum_log_prime_div_sub_le this
    linarith [log_four_eq, log_two_lt_d9]
  linarith [le_sum_log_prime_div_sub_nat N]

theorem sum_von_Mangoldt_div_sub_bounded : (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n - log x)
    =O[atTop] (fun _ ↦ (1 : ℝ)) := Weight.vonMangoldt.first_theorem_error_bounded

theorem sum_log_prime_div_sub_bounded : (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, log p / p - log x)
    =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  convert Weight.prime.first_theorem_error_bounded using 3; rw [← sum_fp_eq]; rfl

theorem sum_von_Mangoldt_div_asymp : (∑ n ∈ Ioc 0 ⌊·⌋₊, Λ n / n) ~[atTop] log :=
  Weight.vonMangoldt.first_theorem_asymp

theorem sum_log_prime_div_asymp : (∑ p ∈ primesLE ⌊·⌋₊, log p / p) ~[atTop] log := by
  convert Weight.prime.first_theorem_asymp using 2; rw [← sum_fp_eq]; rfl

end FirstTheorem

section SecondTheorem

/-
## The second Mertens theorem

We give most of the second Mertens theorem here, except for the specification of the `M` constant
for the von Mangoldt function, which will turn out to equal the Euler--Mascheroni constant `γ`.
-/

variable {x : ℝ} (N : ℕ)

lemma Weight.vonMangoldt_sum_inv_log_mul_eq :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * Weight.vonMangoldt.f n = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) := by
  congr! 1 with n hn
  simp [Weight.vonMangoldt_f_eq, fΛ]; field

lemma Weight.prime_sum_inv_log_mul_eq :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (log n)⁻¹ * Weight.prime.f n = ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) := by
  simp only [Weight.prime_f_eq, fp, mul_ite, mul_zero, primesLE_eq_filter_Ioc_zero, one_div,
    sum_filter]
  congr! 2 with p h hp
  have : 0 < log p := log_pos (mod_cast hp.one_lt)
  field_simp

theorem sum_von_Mangoldt_div_mul_log_bound (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - Weight.vonMangoldt.M| ≤
      (log 4 + 3) / log x := by
    convert! Weight.vonMangoldt.second_theorem hx using 2
    · rw [Weight.vonMangoldt_sum_inv_log_mul_eq]
    linarith [Weight.vonMangoldt_C_lo_eq, Weight.vonMangoldt_C_hi_eq]

theorem sum_von_Mangoldt_div_mul_log_bound_nat (hN : 2 ≤ N) :
    |∑ n ∈ Ioc 0 N, Λ n / (n * log n) - log (log N) - Weight.vonMangoldt.M| ≤
      (log 4 + 3) / log N := by
    convert sum_von_Mangoldt_div_mul_log_bound (x := ↑N) (mod_cast hN)
    simp

theorem sum_prime_div_mul_log_bound (hx : 2 ≤ x) :
    |∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M| ≤
      (log 4 + 3) / log x := by
    convert! Weight.prime.second_theorem hx using 2
    · rw [Weight.prime_sum_inv_log_mul_eq]
    linarith [Weight.prime_C_lo_eq, Weight.prime_C_hi_eq]

theorem sum_prime_div_mul_log_bound_nat (hN : 2 ≤ N) :
    |∑ p ∈ primesLE N, 1 / (p : ℝ) - log (log N) - Weight.prime.M| ≤
      (log 4 + 3) / log N := by
    convert sum_prime_div_mul_log_bound (x := ↑N) (mod_cast hN)
    simp

theorem sum_von_Mangoldt_div_mul_log_bound_bigO_inv_log :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - Weight.vonMangoldt.M)
    =O[atTop] (1 / log ·) := by
  convert Weight.vonMangoldt.second_theorem_error_bigO_inv_log using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_bigO_inv_log :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M)
    =O[atTop] (1 / log ·) := by
  convert Weight.prime.second_theorem_error_bigO_inv_log using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_von_Mangoldt_div_mul_log_bound_littleO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x) - Weight.vonMangoldt.M)
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.vonMangoldt.second_theorem_error_littleO_one using 4
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_littleO_one :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x) - Weight.prime.M)
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.prime.second_theorem_error_littleO_one using 4
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_von_Mangoldt_div_mul_log_bound_bigO_one :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.vonMangoldt.second_theorem_error_bigO_one using 3
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_bigO_one :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
  convert Weight.prime.second_theorem_error_bigO_one using 3
  rw [Weight.prime_sum_inv_log_mul_eq]

theorem sum_von_Mangoldt_div_mul_log_bound_asymp :
    (fun x ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n)) ~[atTop] (fun x ↦ log (log x)) := by
  convert Weight.vonMangoldt.second_theorem_asymp using 2
  rw [Weight.vonMangoldt_sum_inv_log_mul_eq]

theorem sum_prime_div_mul_log_bound_asymp :
    (fun x ↦ ∑ p ∈ primesLE ⌊x⌋₊, 1 / (p : ℝ)) ~[atTop] (fun x ↦ log (log x)) := by
  convert Weight.prime.second_theorem_asymp using 2
  rw [Weight.prime_sum_inv_log_mul_eq]

end SecondTheorem

end Mertens
