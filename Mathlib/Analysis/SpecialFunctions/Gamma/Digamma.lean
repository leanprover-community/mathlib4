/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional


/-!
# The digamma function

This file defines the (real and complex) digamma function as the logarithmic derivative of the
Gamma function and proves some basic properties.

## Main definitions

* `Real.digamma`: The digamma function of a real variable.
* `Complex.digamma`: The digamma function of a complex variable.

## Main statements

* `Real.digamma_apply_add_one`, `Complex.digamma_apply_add_one`: The digamma function satisfies
the functional equation `digamma (s + 1) = digamma s + s⁻¹`.
* `Real.digamma_apply_add_nat`, `Complex.digamma_apply_add_nat`: The iterated recurrence
  `digamma (s + n) = digamma s + ∑ k ∈ Finset.range n, (s + k)⁻¹`.
* `Real.digamma_nat_add_one`, `Complex.digamma_nat_add_one`: The digamma function at positive
integers, in terms of harmonic numbers: `digamma (n + 1) = harmonic n - eulerMascheroniConstant`.
* `Real.digamma_one_sub`, `Complex.digamma_one_sub`: Euler's reflection formula
  `digamma (1 - s) = digamma s + π * cot (π * s)`.
* `Real.digamma_two_mul`,`Complex.digamma_two_mul`: The duplication formula
  `digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2`.
* `Complex.meromorphic_digamma`, `Complex.differentiableOn_digamma`: The digamma function
is meromorphic, and analytic away from non-positive integers.
* `Real.digamma_eq_gaussSeries`, `Complex.digamma_eq_gaussSeries`: Gauss' series for the digamma
function:
  `digamma s = -γ + ∑ n, (1/(n+1) - 1/(s+n))` for `s` not a non-positive integer.
* `Real.monotoneOn_digamma`: The digamma function is monotone on the positive reals.
* `Real.abs_digamma_sub_log_le`: The digamma function is asymptotic to the logarithm on the
  positive reals: `|digamma x - log x| ≤ 1 / x`.

-/

@[expose] public section

namespace Real

/-- The real digamma function, defined as the logarithmic derivative of the real
Gamma function. -/
noncomputable def digamma : ℝ → ℝ := logDeriv Gamma

theorem digamma_def : digamma = logDeriv Gamma := rfl

end Real

namespace Complex

open scoped Real

/-- The complex digamma function, defined as the logarithmic derivative of the complex Gamma
function. -/
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
theorem digamma_apply_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) (n : ℕ) :
    digamma (s + n) = digamma s + ∑ k ∈ .range n, (s + k)⁻¹ := by
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

/-- **`Complex.digamma` agrees with `Real.digamma` along the reals.** -/
@[simp]
theorem digamma_ofReal {x : ℝ} : digamma x = x.digamma := by
  by_cases hx : ∀ m : ℕ, x ≠ -m
  · rw [Real.digamma_def, digamma_def, ← logDeriv_comp_ofReal]
    · convert logDeriv_ofReal_comp (x.differentiableAt_Gamma hx)
      grind [Gamma_ofReal]
    · exact differentiableAt_Gamma _ (mod_cast hx ·)
  · simp only [not_forall, ne_eq, not_not] at hx
    obtain ⟨m, rfl⟩ := hx
    simp [Real.digamma_def, digamma_def, logDeriv_eq_zero_of_not_differentiableAt _ _
      (Real.not_differentiableAt_Gamma_neg_nat m),
      logDeriv_eq_zero_of_not_differentiableAt _ _ (not_differentiableAt_Gamma_neg_nat m)]

theorem digamma_eq_re {x : ℝ} : x.digamma = (digamma x).re := by simp

end Complex

namespace Real

open Complex Set

variable {x : ℝ}

theorem pos_ne_neg_nat (hx : 0 < x) : ∀ m : ℕ, x ≠ -m := by grind

theorem differentiableAt_log_Gamma (hx : ∀ m : ℕ, x ≠ -m) : DifferentiableAt ℝ (·.Gamma.log) x :=
  (differentiableAt_log (Gamma_ne_zero hx)).comp x (differentiableAt_Gamma hx)

theorem monotoneOn_deriv_log_Gamma : MonotoneOn (deriv (·.Gamma.log)) (Ioi (0 : ℝ)) :=
  convexOn_log_Gamma.monotoneOn_deriv fun _ hx ↦ differentiableAt_log_Gamma (pos_ne_neg_nat hx)

theorem digamma_eq_deriv_log_Gamma (hx : ∀ m : ℕ, x ≠ -m) : digamma x = deriv (·.Gamma.log) x := by
  rw [digamma_def]
  exact (deriv_log_comp_eq_logDeriv (differentiableAt_Gamma hx) (Gamma_ne_zero hx)).symm

theorem digamma_apply_add_one (hx : ∀ m : ℕ, x ≠ -m) :
    digamma (x + 1) = digamma x + 1 / x := by
  rw [← Complex.ofReal_inj]; push_cast
  convert Complex.digamma_apply_add_one x (mod_cast hx) <;> simp [← digamma_ofReal]

theorem digamma_apply_add_nat (hx : ∀ m : ℕ, x ≠ -m) (n : ℕ) :
    digamma (x + n) = digamma x + ∑ k ∈ .range n, (x + k)⁻¹ := by
  rw [← Complex.ofReal_inj]; push_cast
  convert Complex.digamma_apply_add_nat (s := x) (mod_cast hx) n <;> simp [← digamma_ofReal]

theorem digamma_nat_add_one (n : ℕ) : digamma (n + 1) = harmonic n - eulerMascheroniConstant := by
  rw [← Complex.ofReal_inj]; push_cast
  convert Complex.digamma_nat_add_one n; simp [← digamma_ofReal]

theorem digamma_one_sub (hx : ∀ n : ℤ, x ≠ n) : digamma (1 - x) = digamma x + π * cot (π * x) := by
  rw [← Complex.ofReal_inj]; push_cast
  convert Complex.digamma_one_sub (s := x) (mod_cast hx) <;> simp [← digamma_ofReal]

theorem digamma_two_mul (hx : ∀ m : ℕ, 2 * x ≠ -m) :
    digamma (2 * x) = (1 / 2) * (digamma x + digamma (x + 1 / 2)) + log 2 := by
  rw [← Complex.ofReal_inj]; push_cast
  convert Complex.digamma_two_mul (s := x) (mod_cast hx) <;> simp [← digamma_ofReal]

/-- `ψ` is monotone on the positive reals. -/
theorem monotoneOn_digamma : MonotoneOn digamma (Ioi 0) :=
  monotoneOn_deriv_log_Gamma.congr fun _ _ ↦ by grind [digamma_eq_deriv_log_Gamma]

/-- `ψ(x) ≤ log x ≤ ψ(x + 1)`. -/
theorem digamma_le_log_le (hx : 0 < x) : digamma x ≤ x.log ∧ x.log ≤ digamma (x + 1) := by
  have : ContinuousOn (·.Gamma.log) (Icc x (x + 1)) := fun _ _ ↦
    (differentiableAt_log_Gamma (by grind [pos_ne_neg_nat])).continuousAt.continuousWithinAt
  obtain ⟨c, _, hcs⟩ := exists_deriv_eq_slope (·.Gamma.log) (by linarith) this
      fun _ _ ↦ (differentiableAt_log_Gamma (by grind [pos_ne_neg_nat hx])).differentiableWithinAt
  have : x.log = deriv (·.Gamma.log) c := by grind [Gamma_add_one, log_mul, Gamma_pos_of_pos]
  rw [digamma_eq_deriv_log_Gamma (pos_ne_neg_nat hx),
    digamma_eq_deriv_log_Gamma (pos_ne_neg_nat (by linarith)), this]
  constructor <;> apply monotoneOn_deriv_log_Gamma <;> grind

/-- **`|ψ(x) − log x| ≤ 1 / x` for real `x > 0`**. -/
theorem abs_digamma_sub_log_le (hx : 0 < x) : |digamma x - x.log| ≤ 1 / x := by
  grind [abs_le, digamma_apply_add_one (pos_ne_neg_nat hx), digamma_le_log_le hx]

end Real

/-!
### Gauss' series for the digamma function

`ψ(s) = −γ + ∑ₙ (1/(n+1) − 1/(s+n))` on the region of analyticity of `Gamma`, that is say away from
the non-positive integers.
-/

namespace Complex

open scoped Real Topology
open Filter Set

variable {s : ℂ} {x : ℝ}

/-- The set where `Gamma` or `digamma` is analytic: the complement of the non-positive integers. -/
def gammaAnalyticSet : Set ℂ := {s | ∀ m : ℕ, s ≠ -m}

theorem ofReal_mem_gammaAnalyticSet (hx : 0 < x) : ↑x ∈ gammaAnalyticSet := by
  simp only [gammaAnalyticSet, mem_ofPred_eq]
  exact_mod_cast (Real.pos_ne_neg_nat hx)

private theorem gammaAnalyticSet_eq_compl : gammaAnalyticSet = ((↑) '' {n : ℤ | n ≤ 0} : Set ℂ)ᶜ
    := by
  ext
  simp only [gammaAnalyticSet, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, not_exists,
    not_and]
  constructor
  · rintro h n hn rfl
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact h m (by push_cast; ring)
  · rintro h m hsm
    exact h (-m) (by omega) (by push_cast; tauto)

theorem mem_gammaAnalyticSet_add_one (hs : s ∈ gammaAnalyticSet) :
    s + 1 ∈ gammaAnalyticSet := fun m _ ↦ by grind [hs (m + 1)]

theorem isOpen_gammaAnalyticSet : IsOpen gammaAnalyticSet := by
  rw [gammaAnalyticSet_eq_compl]
  exact (Complex.isClosedEmbedding_intCast.isClosedMap _ (isClosed_discrete _)).isOpen_compl

theorem isPreconnected_gammaAnalyticSet : IsPreconnected gammaAnalyticSet := by
  rw [gammaAnalyticSet_eq_compl]
  exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    ((Set.to_countable _).image _)).2

theorem differentiableOn_Gamma : DifferentiableOn ℂ Gamma gammaAnalyticSet :=
  fun z hz ↦ (differentiableAt_Gamma z hz).differentiableWithinAt

theorem differentiableOn_digamma : DifferentiableOn ℂ digamma gammaAnalyticSet := by
  rw [digamma_def, logDeriv]
  intro s hs
  exact ((differentiableOn_Gamma.analyticOnNhd isOpen_gammaAnalyticSet
    s hs).deriv.differentiableAt.div (differentiableAt_Gamma s hs)
    (Gamma_ne_zero hs)).differentiableWithinAt

/-- The `n`-th summand of Gauss' series for the digamma function. -/
private noncomputable def gaussTerm (s : ℂ) (n : ℕ) : ℂ := 1 / (n + 1) - 1 / (s + n)

/-- Gauss' series for the digamma function. -/
private noncomputable def gaussSeries (s : ℂ) : ℂ :=
  -Real.eulerMascheroniConstant + ∑' n, gaussTerm s n

/-- The error between `digamma` and its Gauss series; we show it is identically zero. -/
private noncomputable def gaussErr (s : ℂ) : ℂ := digamma s - gaussSeries s

private theorem gaussTerm_eq (hs : s ∈ gammaAnalyticSet) (n : ℕ) :
    gaussTerm s n = (s - 1) / ((n + 1) * (s + n)) := by
  rw [gaussTerm, div_sub_div _ _ n.cast_add_one_ne_zero (by grind [hs n])]
  ring_nf

private theorem summable_gaussTerm (hs : s ∈ gammaAnalyticSet) : Summable (gaussTerm s) := by
  apply Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ ↦ 2 * ‖s - 1‖ / n ^ 2)
  · exact ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 * ‖s - 1‖)).congr fun _ ↦ by
      ring
  · filter_upwards [eventually_ge_atTop (2 * ⌈‖s‖⌉₊ + 1)] with n hn
    have : (2 * ⌈‖s‖⌉₊ + 1 : ℝ) ≤ n := mod_cast hn
    have : (0 : ℝ) < n := by linarith
    have : n / 2 ≤ ‖s + n‖ := by
      grind [add_comm, norm_sub_le_norm_add, norm_natCast, Nat.le_ceil ‖s‖]
    grw [gaussTerm_eq hs, norm_div, norm_mul, (by norm_cast : ‖(n : ℂ) + 1‖ = n + 1),
      (by nlinarith : (n + 1) * ‖s + n‖ ≥ n ^2 / 2)]
    ring_nf; rfl

private theorem summable_recipDiff (hs : s ∈ gammaAnalyticSet) :
    Summable fun k : ℕ ↦ 1 / (s + k) - 1 / (s + k + 1) :=
  ((summable_gaussTerm (mem_gammaAnalyticSet_add_one hs)).sub (summable_gaussTerm hs)).congr
    (by grind [gaussTerm])

private theorem tsum_recipTelescope (hs : s ∈ gammaAnalyticSet) :
    ∑' k : ℕ, (1 / (s + k) - 1 / (s + k + 1)) = 1 / s := by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_ |>.mpr ?_).tsum_eq
  · exact summable_norm_iff.mpr (summable_recipDiff hs)
  have (n : ℕ) : ∑ k ∈ .range n, (1 / (s + k) - 1 / (s + k + 1)) = 1 / s - 1 / (s + n) := by
    grind [Finset.sum_congr, Nat.cast_zero, Finset.sum_range_sub' (fun k ↦ 1 / (s + k)) n]
  simp_rw [this]
  suffices Tendsto (fun n : ℕ ↦ (1 : ℂ) / (s + n)) atTop (𝓝 0) by
    simpa using tendsto_const_nhds.sub this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [one_div, norm_inv]
  refine tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n ↦ ?_)
    (tendsto_atTop_add_const_right atTop (-‖s‖) tendsto_natCast_atTop_atTop))
  grind [norm_natCast, norm_neg, norm_sub_norm_le (n : ℂ) (-s)]

/-- The error is 1-periodic. -/
private theorem gaussErr_add_one (hs : s ∈ gammaAnalyticSet) : gaussErr (s + 1) = gaussErr s := by
  have : gaussSeries (s + 1) - gaussSeries s = 1 / s := by
    simp only [gaussSeries, add_sub_add_left_eq_sub, ← Summable.tsum_sub,
      mem_gammaAnalyticSet_add_one hs, summable_gaussTerm, hs]
    convert! tsum_recipTelescope hs using 3 with k
    grind [gaussTerm]
  grind [gaussErr, digamma_apply_add_one s hs]

/-- **Base case**: the error vanishes at the positive integers. -/
private theorem gaussErr_natCast_add_one (n : ℕ) : gaussErr (n + 1) = 0 := by
  induction n with
  | zero => grind [gaussErr, gaussSeries, tsum_zero, gaussTerm, digamma_one]
  | succ n =>
    have : ((n : ℂ) + 1) ∈ gammaAnalyticSet := by simp [gammaAnalyticSet]; norm_cast; grind
    grind [Nat.cast_add, Nat.cast_one, gaussErr_add_one]

private theorem partialSum_gaussTerm_ofReal (hx : ↑x ∈ gammaAnalyticSet) (N : ℕ) :
    ∑ k ∈ .range N, gaussTerm x k
      = digamma (N + 1) + Real.eulerMascheroniConstant - digamma (x + N) + digamma x := by
  have : harmonic N = ∑ k ∈ .range N, (1 / ((k : ℂ) + 1)) := by simp [harmonic]
  simp_rw [gaussTerm, Finset.sum_sub_distrib, digamma_nat_add_one]
  grind [digamma_apply_add_nat hx]

private theorem tendsto_digamma_diff :
    Tendsto (fun N : ℕ ↦ digamma (N + 1) - digamma (x + N)) atTop (𝓝 0) := by
  suffices Tendsto (fun N : ℕ ↦ (N + 1 : ℝ).digamma - (x + N : ℝ).digamma) atTop (𝓝 0) by
    refine ((continuous_ofReal.tendsto 0).comp this).congr (fun N ↦ ?_)
    simp only [Function.comp_apply]
    push_cast
    simp [← Complex.digamma_ofReal]
  have (N) (hN : ⌈-x⌉₊ + 1 ≤ N) : 0 < x + (N : ℝ) := by
    have : (⌈-x⌉₊ : ℝ) + 1 ≤ N := mod_cast hN
    grind [Nat.le_ceil (-x)]
  have hA : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ).digamma - (N + 1 : ℝ).log)
      atTop (𝓝 0) := by
    have (N : ℕ) : ‖(N + 1 : ℝ).digamma - (N + 1 : ℝ).log‖ ≤ 1 / (N + 1 : ℝ) := by
      rw [Real.norm_eq_abs]; exact Real.abs_digamma_sub_log_le (by positivity)
    exact squeeze_zero_norm this (Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  have hB : Tendsto (fun N : ℕ ↦ (x + N).digamma - (x + N).log) atTop (𝓝 0) := by
    have : ∀ᶠ N : ℕ in atTop, ‖(x + N).digamma - (x + N).log‖ ≤ 1 / (x + N) := by
      filter_upwards [eventually_ge_atTop (⌈-x⌉₊ + 1)]
      grind [Real.norm_eq_abs, Real.abs_digamma_sub_log_le]
    exact squeeze_zero_norm' this (Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop))
  have hC : Tendsto (fun N : ℕ ↦ (N + 1 : ℝ).log - (x + N).log) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ ↦ (N + 1) / (x + N)) atTop (𝓝 1) := by
      have : Tendsto (fun N : ℕ ↦ 1 + (1 - x) / (x + N)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (Tendsto.div_atTop tendsto_const_nhds
          (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop))
      convert this.congr' ?_
      · simp
      · filter_upwards [eventually_ge_atTop (⌈-x⌉₊ + 1)]; grind
    convert ((Real.continuousAt_log one_ne_zero).tendsto.comp this).congr' ?_
    · simp
    · filter_upwards [eventually_ge_atTop (⌈-x⌉₊ + 1)]; grind [Real.log_div]
  grind [((hA.sub hB).add hC).congr]

/-- **Real case**: the error vanishes on the reals (off the poles). -/
private theorem gaussErr_ofReal (hx : ↑x ∈ gammaAnalyticSet) : gaussErr x = 0 := by
  have hsum : Summable (‖gaussTerm x ·‖) := summable_norm_iff.mpr (summable_gaussTerm hx)
  suffices HasSum (gaussTerm x) (digamma x + Real.eulerMascheroniConstant) by
    grind [gaussErr, gaussSeries, HasSum.tsum_eq]
  have : (∑ k ∈ .range ·, gaussTerm x k) = fun N : ℕ ↦ (digamma (N + 1) - digamma (x + N))
      + (digamma x + Real.eulerMascheroniConstant) := by grind [partialSum_gaussTerm_ofReal hx]
  simpa [hasSum_iff_tendsto_nat_of_summable_norm hsum, this] using tendsto_digamma_diff.add_const _

private theorem differentiableOn_gaussSeries :
    DifferentiableOn ℂ gaussSeries gammaAnalyticSet := by
  have hterm (N : Finset ℕ) :
      DifferentiableOn ℂ (fun s ↦ ∑ n ∈ N, gaussTerm s n) gammaAnalyticSet := by
    refine DifferentiableOn.fun_sum fun n _ ↦ ?_
    simp only [gaussTerm]
    exact (differentiableOn_const _).sub
      ((differentiableOn_const _).div (by fun_prop) fun s hs ↦ by grind [hs n])
  obtain ⟨g, hg⟩ : SummableLocallyUniformlyOn (fun n s ↦ gaussTerm s n) gammaAnalyticSet := by
    apply SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_gammaAnalyticSet
    intro K hK hKc
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hKc.isBounded
    refine ⟨fun n ↦ 2 * (R + 1) / n ^ 2, ?_, ?_⟩
    · exact ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 * (R + 1))).congr
        (by grind)
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop (2 * ⌈R⌉₊ + 1)] with n hn s hs
      have := hR s hs
      have : (2 * ⌈R⌉₊ + 1 : ℝ) ≤ n := mod_cast hn
      have : (0 : ℝ) < n := by grind
      rw [gaussTerm_eq (hK hs), norm_div, norm_mul]
      norm_cast; push_cast
      have : ↑n ^ 2 / 2 ≤ (↑n + 1) * ‖s + ↑n‖ := by
        have := norm_sub_le_norm_add (n : ℂ) s
        rw [norm_natCast, add_comm] at this
        nlinarith [Nat.le_ceil R]
      grw [← this]
      field_simp; grind [norm_sub_le, norm_one]
  exact ((hg.differentiableOn (Eventually.of_forall hterm) isOpen_gammaAnalyticSet).congr
    (fun s hs ↦ hg.tsum_eqOn hs)).const_add _

private theorem analyticOnNhd_gaussErr : AnalyticOnNhd ℂ gaussErr gammaAnalyticSet :=
  (differentiableOn_digamma.sub differentiableOn_gaussSeries).analyticOnNhd
    isOpen_gammaAnalyticSet

private theorem gaussErr_eq_zero (hs : s ∈ gammaAnalyticSet) : gaussErr s = 0 := by
  have h1 : 1 ∈ gammaAnalyticSet := by simpa using ofReal_mem_gammaAnalyticSet one_pos
  have : Tendsto (fun k : ℕ ↦ ((1 + 1 / (k + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · convert! (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.add
        (Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop)))
      simp
    · filter_upwards
      grind [Complex.ofReal_eq_one]
  refine analyticOnNhd_gaussErr.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_gammaAnalyticSet h1 ?_ hs
  exact this.frequently (Eventually.of_forall fun _ ↦ gaussErr_ofReal
      (ofReal_mem_gammaAnalyticSet (by positivity))).frequently

theorem summable_gaussSeries (hs : ∀ m : ℕ, s ≠ -m) :
    Summable (fun n : ℕ ↦ 1 / (n + 1) - 1 / (s + n)) := summable_gaussTerm hs

/-- **Gauss' series for the digamma function**:
`ψ(s) = −γ + ∑ₙ (1/(n+1) − 1/(s+n))` for `s` not a non-positive integer. -/
theorem digamma_eq_gaussSeries (hs : ∀ m : ℕ, s ≠ -m) :
    digamma s = -Real.eulerMascheroniConstant + ∑' n : ℕ, (1 / (n + 1) - 1 / (s + n)) := by
  simpa [gaussErr, gaussSeries, gaussTerm, sub_eq_zero] using gaussErr_eq_zero (s := s) hs

end Complex

namespace Real

theorem summable_gaussSeries {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    Summable (fun n : ℕ ↦ 1 / (n + 1) - 1 / (x + n)) := by
  rw [← Complex.summable_ofReal]; push_cast
  exact Complex.summable_gaussSeries (s := x) (mod_cast hx)

/-- **Gauss' series for the digamma function (real version)** -/
theorem digamma_eq_gaussSeries {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    digamma x = -eulerMascheroniConstant + ∑' n : ℕ, (1 / (n + 1) - 1 / (x + n)) := by
  rw [← Complex.ofReal_inj]; push_cast
  convert Complex.digamma_eq_gaussSeries (s := x) (mod_cast hx)
  simp [← Complex.digamma_ofReal]

end Real
