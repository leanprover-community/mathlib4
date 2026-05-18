/-
Copyright (c) 2026 Yan Senez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Senez
-/
module

public import Mathlib.NumberTheory.MertensFirst
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog

/-!
# Mertens' Third Theorem and the Meissel-Mertens constant

The present file establishes **Mertens' Third Theorem** (1874): the partial sums
of prime reciprocals admit the second-order asymptotic
$$\sum_{p \le x} \frac{1}{p} \;=\; \log\log x \,+\, M \,+\, O\!\left(\frac{1}{\log x}\right),$$
where `M ≈ 0.26149721…` is the **Meissel-Mertens constant**.

The proof rests on Abel summation, used to pivot from `Mertens.first` (Mertens'
First Theorem, established in `Mathlib.NumberTheory.MertensFirst`) by means of
the antiderivatives `∫ 1/(t log t) dt = log log t` and
`∫ 1/(t log²t) dt = -1/log t`. One then obtains a Cauchy-style oscillation bound
`|F(x) - F(y)| ≤ C/log y`, from which both existence (`third_exists`) and the
quantitative rate (`third`) follow.

## Main definitions

* `Mertens.meisselMertensConstant` — the Meissel-Mertens constant
  `M ≈ 0.26149721…`, defined as the classical limit
  `M := lim_{x → ∞} (partialSum x - log log x)`.

## Main theorems

* `Mertens.third_exists` — existence form: the limit defining `M` exists.
* `Mertens.third` — quantitative form:
  `∃ C, ∀ x ≥ 2, |partialSum x - log log x - meisselMertensConstant| ≤ C / log x`.
* `Mertens.partialSum_sub_log_log_bounded` — boundedness corollary, useful for
  applications that only require compactness of the partial-sum orbit.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math.
  78 (1874), 46–62.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*,
  6th ed., Oxford University Press (2008), Theorem 427.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*,
  3rd ed., Graduate Studies in Mathematics 163 (2015), §I.1.6.
-/
@[expose] public section

namespace Mertens

open Real Nat Finset
open scoped BigOperators

/-! ### Mertens' Third Theorem (M3) -/

/-! #### Abel summation pivot for `partialSum` (foundation for M3)

The classical proof of M3 begins with a second Abel-summation step — this time
expressing `partialSum x = ∑_{p ≤ x} 1/p` in terms of `partialSumLog`:

$$\sum_{p \le x} \frac{1}{p}
   \;=\; \frac{\mathcal{L}(x)}{\log x} \,+\, \int_2^x \frac{\mathcal{L}(t)}{t \log^2 t}\,dt,
\quad \text{where } \mathcal{L}(t) = \sum_{p \le t} \frac{\log p}{p}.$$

It is the analogue of `partialSumLog_eq_theta_div_x_add_integral`, but with
`f(t) = (\log t)^{-1}` (whose derivative is `-1/(t \log^2 t)`, by virtue of
`deriv_inv_log`) in place of `f(t) = t^{-1}`.

Combined with `first` (`partialSumLog x = log x + O(1)`), this identity then
yields `partialSum x = log log x + M_3 + O(1/\log x)`, the headline M3 theorem.
-/

open Asymptotics Filter MeasureTheory in
/-- **Abel-summation pivot for Mertens M3.**

For every `x ≥ 2`,
$$\sum_{p \le x} \frac{1}{p}
   \;=\; \frac{\mathcal{L}(x)}{\log x} \,+\, \int_2^x \frac{\mathcal{L}(t)}{t \log^2 t}\,dt,$$
where `\mathcal{L}(t) = partialSumLog t = ∑_{p ≤ t} (log p)/p`.

This is the Mertens M3 analogue of Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral`, applied to the sequence
`(log p / p) · [p prime]` rather than `log p · [p prime]`. Such is the
analytic backbone of **Mertens' Third Theorem**. -/
theorem partialSum_eq_partialSumLog_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    partialSum x = partialSumLog x / Real.log x
      + ∫ t in (2 : ℝ)..x, partialSumLog t / (t * (Real.log t) ^ 2) := by
  unfold partialSum
  rw [Nat.primesBelow_eq_filter_range, Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
  -- Abel-summation "sequence" `b(n) = (log n / n) · [n prime]`.
  let b : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n ↦ Real.log n / n)
  trans ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * b n
  · refine Finset.sum_congr rfl fun n _hn ↦ ?_
    by_cases h : Nat.Prime n
    · have hn_pos : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h.one_lt
      have hlog_ne : Real.log n ≠ 0 := by
        have hlog_pos : 0 < Real.log n := Real.log_pos hn_pos
        exact ne_of_gt hlog_pos
      have hn_ne : (n : ℝ) ≠ 0 := by
        have : 0 < (n : ℝ) := by exact_mod_cast h.pos
        exact ne_of_gt this
      simp only [b, Set.indicator_of_mem, Set.mem_setOf_eq, h, if_true]
      field_simp
    · simp [b, h, Set.indicator_of_notMem]
  rw [sum_mul_eq_sub_integral_mul₁ b (f := fun t ↦ (Real.log t)⁻¹)
        (by simp [b]) (by simp [b, Nat.not_prime_one]),
      ← intervalIntegral.integral_of_le hx]
  · -- `(d/dt) (log t)⁻¹ = -t⁻¹ / (log t)^2` via `deriv_inv_log`.
    have hderiv : ∀ u ∈ Set.uIcc (2 : ℝ) x,
        deriv (fun t : ℝ ↦ (Real.log t)⁻¹) u = -u⁻¹ / (Real.log u) ^ 2 := by
      intro u _; exact deriv_inv_log
    have int_deriv (g : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..x, deriv (fun t : ℝ ↦ (Real.log t)⁻¹) u * g u
          = ∫ u in (2 : ℝ)..x, g u * (-u⁻¹ / (Real.log u) ^ 2) :=
      intervalIntegral.integral_congr fun u hu ↦ by
        rw [hderiv u hu]; ring
    rw [int_deriv]
    have hL_sum : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, b k = partialSumLog x := by
      unfold partialSumLog
      rw [Nat.primesBelow_eq_filter_range, Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      by_cases h : Nat.Prime n
      · simp [b, h, Set.indicator_of_mem]
      · simp [b, h, Set.indicator_of_notMem]
    have hL_partial : ∀ t : ℝ,
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, b k = partialSumLog t := by
      intro t
      unfold partialSumLog
      rw [Nat.primesBelow_eq_filter_range, Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      by_cases h : Nat.Prime n
      · simp [b, h, Set.indicator_of_mem]
      · simp [b, h, Set.indicator_of_notMem]
    rw [hL_sum]
    have hint_eq :
        ∫ u in (2 : ℝ)..x, partialSumLog u * (-u⁻¹ / (Real.log u) ^ 2)
          = -∫ u in (2 : ℝ)..x, partialSumLog u / (u * (Real.log u) ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u _ ↦ ?_
      simp only [neg_div]
      field_simp
    have hint_eq' :
        ∫ u in (2 : ℝ)..x, (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, b k) * (-u⁻¹ / (Real.log u) ^ 2)
          = ∫ u in (2 : ℝ)..x, partialSumLog u * (-u⁻¹ / (Real.log u) ^ 2) :=
      intervalIntegral.integral_congr fun u _ ↦ by rw [hL_partial u]
    rw [hint_eq', hint_eq]
    rw [sub_neg_eq_add]
    congr 1
    rw [mul_comm, div_eq_mul_inv]
  · -- Differentiability of `t ↦ (log t)⁻¹` on `[2, x]` (avoiding zeros of `log`).
    intro z hz
    have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
    have hz_pos : (0 : ℝ) < z := by linarith
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hz_gt_1 : (1 : ℝ) < z := by linarith
    have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
    have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
    exact (Real.differentiableAt_log hz_ne).inv hlog_ne
  · -- Integrability of `deriv ((log ·)⁻¹) = -(·)⁻¹ / (log ·)^2` on `[2, x]`:
    -- pointwise equality via `deriv_inv_log` reduces to continuity on a compact.
    refine ContinuousOn.integrableOn_Icc ?_
    intro z hz
    have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
    have hz_pos : (0 : ℝ) < z := by linarith
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hz_gt_1 : (1 : ℝ) < z := by linarith
    have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
    have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
    have hlog2_ne : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    refine ContinuousAt.continuousWithinAt ?_
    have h_eq : (deriv fun t : ℝ ↦ (Real.log t)⁻¹)
        = fun y : ℝ ↦ -y⁻¹ / (Real.log y) ^ 2 := by
      funext y; exact deriv_inv_log
    rw [h_eq]
    fun_prop

/-! #### Antiderivative `∫ 1/(t log t) dt = log log t`

This evaluates the principal-term integral that arises when one combines the
Abel pivot `partialSum = partialSumLog/log + ∫ partialSumLog/(t log² t)` with
`first` (`partialSumLog t = log t + O(1)`). Since the leading-order contribution
to the integrand is `(log t)/(t log² t) = 1/(t log t)`, its integral on `[2, x]`
is precisely `log log x - log log 2`. -/

open Asymptotics Filter MeasureTheory in
/-- **Antiderivative `∫ 1/(t log t) dt = log log t` on `[2, x]`.**

For every `x ≥ 2`,
$$\int_2^x \frac{1}{t \log t}\,dt \;=\; \log\log x \,-\, \log\log 2.$$

The Lean proof rests on the fundamental theorem of calculus
(`integral_deriv_eq_sub'`), together with the chain rule
`(d/dt)(\log\log t) = 1/(t \log t)`, valid for `t > 1`. -/
theorem integral_one_div_t_log_t {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / (t * Real.log t)
      = Real.log (Real.log x) - Real.log (Real.log 2) := by
  -- Antiderivative `F(t) = log (log t)`; for `t > 1`,
  -- `F'(t) = (1 / log t) · (1 / t) = 1 / (t · log t)`.
  set F : ℝ → ℝ := fun t ↦ Real.log (Real.log t) with hF
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x, HasDerivAt F (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_gt_1 : 1 < t := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos ht_gt_1
    have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
    -- chain rule
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht_ne
    have h2 : HasDerivAt (fun y ↦ Real.log (Real.log y)) (t⁻¹ / Real.log t) t :=
      h1.log hlog_ne
    convert h2 using 1
    field_simp
  have h_cont : ContinuousOn (fun t : ℝ ↦ 1 / (t * Real.log t)) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_gt_1 : 1 < t := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos ht_gt_1
    have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
    have hprod_ne : t * Real.log t ≠ 0 := mul_ne_zero ht_ne hlog_ne
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_cont.intervalIntegrable
  simpa [F] using this

/-- **Antiderivative `∫ 1/(t log² t) dt = -1/log t` on `[2, x]`.**

For every `x ≥ 2`,
$$\int_2^x \frac{1}{t \log^2 t}\,dt \;=\; \frac{1}{\log 2} \,-\, \frac{1}{\log x}.$$

Such is the **error-term integral** for Mertens M3: combined with the `first`
bound `|partialSumLog t - log t| ≤ C`, it furnishes an absolutely convergent
correction, whence the existence of the limit `M_3`. -/
theorem integral_one_div_t_log_sq {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / (t * (Real.log t) ^ 2)
      = 1 / Real.log 2 - 1 / Real.log x := by
  -- Antiderivative `G(t) = -(log t)⁻¹`; then
  -- `G'(t) = -(d/dt)(log t)⁻¹ = -(-(t⁻¹) / (log t)^2) = 1 / (t · (log t)^2)`.
  set G : ℝ → ℝ := fun t ↦ -(Real.log t)⁻¹ with hG
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x, HasDerivAt G (1 / (t * (Real.log t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_gt_1 : 1 < t := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos ht_gt_1
    have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
    have hlog2_ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    have h_inv_log_diff : DifferentiableAt ℝ (fun y ↦ (Real.log y)⁻¹) t :=
      (Real.differentiableAt_log ht_ne).inv hlog_ne
    have h_deriv_inv_log : deriv (fun y ↦ (Real.log y)⁻¹) t = -t⁻¹ / (Real.log t) ^ 2 :=
      deriv_inv_log
    have h1 : HasDerivAt (fun y ↦ (Real.log y)⁻¹) (-t⁻¹ / (Real.log t) ^ 2) t := by
      rw [← h_deriv_inv_log]; exact h_inv_log_diff.hasDerivAt
    have h2 : HasDerivAt G (-(-t⁻¹ / (Real.log t) ^ 2)) t := h1.neg
    convert h2 using 1
    field_simp
  have h_cont : ContinuousOn (fun t : ℝ ↦ 1 / (t * (Real.log t) ^ 2)) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht_pos : 0 < t := by linarith [ht.1]
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_gt_1 : 1 < t := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos ht_gt_1
    have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
    have hlog2_ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    have hprod_ne : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero ht_ne hlog2_ne
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_cont.intervalIntegrable
  simp only [G] at this
  rw [this]
  ring

/-! #### Cauchy step: `F(x) := partialSum x - log log x` has uniformly small
oscillation on `[Y, ∞)` for `Y` large.

The proof of `third_exists` follows the standard 19th-century recipe: one
combines the M3-Abel pivot `partialSum_eq_partialSumLog_div_log_add_integral`
with M1 (`|partialSumLog t - log t| ≤ C`) and the closed-form antiderivatives
`integral_one_div_t_log_t`, `integral_one_div_t_log_sq`, so as to bound
`|F(x) - F(y)|` by `2·C_{M1} / \log y` for `2 ≤ y ≤ x`. Recall that the pivot
gives:

```
F(x) - F(y)
  = partialSumLog x / log x − partialSumLog y / log y
    + ∫_y^x partialSumLog(t) / (t · log²t)  dt
    − ∫_y^x 1/(t · log t)  dt.
```

Writing `partialSumLog t = log t + δ(t)` with `|δ(t)| ≤ C_{M1}` (thanks to M1),
the latter then collapses to:

```
F(x) - F(y) = δ(x)/log x − δ(y)/log y + ∫_y^x δ(t) / (t · log²t) dt,
```

and the closed-form `∫_y^x 1/(t log² t) = 1/log y − 1/log x` then yields
`|F(x) - F(y)| ≤ 2 C_{M1} / log y`. -/

-- The full proof of `third_exists` is given below, after the
-- supporting helper lemmas `partialSumLog_monotone`,
-- `partialSumLog_div_intervalIntegrable`, and `partialSum_sub_log_log_oscillation`.

/-- Monotonicity of `partialSumLog` on `ℝ` (as a function of the cutoff). -/
private lemma partialSumLog_monotone : Monotone partialSumLog := by
  intro a b hab
  unfold partialSumLog
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Nat.primesBelow_eq_filter_range, Finset.mem_filter] at hp ⊢
    refine ⟨?_, hp.2⟩
    have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hp.1) (by omega))
  · intro p hp _
    have hp_prime : Nat.Prime p := by
      rw [Nat.primesBelow_eq_filter_range, Finset.mem_filter] at hp
      exact hp.2
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hp_ge2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
    have hlogp_nn : 0 ≤ Real.log p :=
      Real.log_nonneg (by linarith)
    positivity

/-- Integrability of `partialSumLog t / (t · log²t)` on `[2, x]`. -/
private lemma partialSumLog_div_intervalIntegrable {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t => partialSumLog t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x := by
  -- Rewrite as partialSumLog t * (1/(t · log²t)).
  have hrw : (fun t => partialSumLog t / (t * (Real.log t) ^ 2))
           = (fun t => partialSumLog t * (1 / (t * (Real.log t) ^ 2))) := by
    funext t; ring
  rw [hrw]
  refine IntervalIntegrable.mul_continuousOn ?_ ?_
  · exact partialSumLog_monotone.intervalIntegrable
  · rw [Set.uIcc_of_le hx]
    intro z hz
    have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
    have hz_pos : (0 : ℝ) < z := by linarith
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hz_gt_1 : (1 : ℝ) < z := by linarith
    have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
    have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
    have hlog2_ne : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    have hprod_ne : z * (Real.log z) ^ 2 ≠ 0 := mul_ne_zero hz_ne hlog2_ne
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop

/-- **Oscillation bound for `F(x) := partialSum x - log log x`.**

For `2 ≤ y ≤ x`, the difference `F(x) - F(y)` is bounded, in absolute value,
by `3 C / log y`, where `C ≥ 0` denotes the M1 constant. -/
private lemma partialSum_sub_log_log_oscillation
    {y x : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    |(partialSum x - Real.log (Real.log x)) -
      (partialSum y - Real.log (Real.log y))| ≤
      3 * (|Classical.choose first| + 1) / Real.log y := by
  set C₀ : ℝ := Classical.choose first with hC₀def
  have hC₀spec : ∀ x : ℝ, 2 ≤ x → |partialSumLog x - Real.log x| ≤ C₀ :=
    Classical.choose_spec first
  -- `C := |C₀| + 1` (strictly positive, simplifies positivity reasoning).
  set C : ℝ := |C₀| + 1 with hCdef
  have hC_pos : 0 < C := by positivity
  have hC_ge : ∀ t : ℝ, 2 ≤ t → |partialSumLog t - Real.log t| ≤ C := by
    intro t ht
    have h1 : |partialSumLog t - Real.log t| ≤ C₀ := hC₀spec t ht
    have h2 : C₀ ≤ |C₀| := le_abs_self _
    have h3 : |C₀| ≤ C := by simp [hCdef]
    linarith
  have hx : 2 ≤ x := le_trans hy hyx
  have hy_pos : 0 < y := by linarith
  have hx_pos : 0 < x := by linarith
  have hy_gt_1 : 1 < y := by linarith
  have hx_gt_1 : 1 < x := by linarith
  have hlogy_pos : 0 < Real.log y := Real.log_pos hy_gt_1
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt_1
  have hlogy_ne : Real.log y ≠ 0 := ne_of_gt hlogy_pos
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hlogx_ge_logy : Real.log y ≤ Real.log x := Real.log_le_log hy_pos hyx
  -- Abel pivot at `x` and at `y`; difference of integrals = `∫_y^x`.
  have piv_x : partialSum x = partialSumLog x / Real.log x
      + ∫ t in (2 : ℝ)..x, partialSumLog t / (t * (Real.log t) ^ 2) :=
    partialSum_eq_partialSumLog_div_log_add_integral hx
  have piv_y : partialSum y = partialSumLog y / Real.log y
      + ∫ t in (2 : ℝ)..y, partialSumLog t / (t * (Real.log t) ^ 2) :=
    partialSum_eq_partialSumLog_div_log_add_integral hy
  -- The difference of the integrals = ∫_y^x partialSumLog/(t · log²t).
  have hint_y : IntervalIntegrable (fun t => partialSumLog t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 y := partialSumLog_div_intervalIntegrable hy
  have hint_x : IntervalIntegrable (fun t => partialSumLog t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x := partialSumLog_div_intervalIntegrable hx
  have hdiff_int : (∫ t in (2 : ℝ)..x, partialSumLog t / (t * (Real.log t) ^ 2))
      - (∫ t in (2 : ℝ)..y, partialSumLog t / (t * (Real.log t) ^ 2))
      = ∫ t in y..x, partialSumLog t / (t * (Real.log t) ^ 2) :=
    intervalIntegral.integral_interval_sub_left hint_x hint_y
  have hsubpiv : partialSum x - partialSum y =
      (partialSumLog x / Real.log x - partialSumLog y / Real.log y)
      + ∫ t in y..x, partialSumLog t / (t * (Real.log t) ^ 2) := by
    rw [piv_x, piv_y]; linarith
  have hint_log_2y : IntervalIntegrable (fun t => 1 / (t * Real.log t))
      MeasureTheory.volume 2 y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hy]
    intro z hz
    have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
    have hz_pos : (0 : ℝ) < z := by linarith
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hz_gt_1 : (1 : ℝ) < z := by linarith
    have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
    have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
    have hprod_ne : z * Real.log z ≠ 0 := mul_ne_zero hz_ne hlog_ne
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have hint_log_2x : IntervalIntegrable (fun t => 1 / (t * Real.log t))
      MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hx]
    intro z hz
    have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
    have hz_pos : (0 : ℝ) < z := by linarith
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hz_gt_1 : (1 : ℝ) < z := by linarith
    have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
    have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
    have hprod_ne : z * Real.log z ≠ 0 := mul_ne_zero hz_ne hlog_ne
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have hint_log_split : ∫ t in y..x, 1 / (t * Real.log t)
      = Real.log (Real.log x) - Real.log (Real.log y) := by
    have h2x : ∫ t in (2 : ℝ)..x, 1 / (t * Real.log t)
        = Real.log (Real.log x) - Real.log (Real.log 2) :=
      integral_one_div_t_log_t hx
    have h2y : ∫ t in (2 : ℝ)..y, 1 / (t * Real.log t)
        = Real.log (Real.log y) - Real.log (Real.log 2) :=
      integral_one_div_t_log_t hy
    have hsplit := intervalIntegral.integral_interval_sub_left hint_log_2x hint_log_2y
    linarith
  -- Algebraic identity (no symbolic simplification — bound directly):
  -- writing `δ(t) = partialSumLog t − log t`,
  --   `partialSumLog t / log t = 1 + δ(t) / log t`,
  -- and
  --   `∫_y^x partialSumLog / (t · log²t)`
  --     `= ∫_y^x log(t) / (t · log²t) + ∫_y^x δ(t) / (t · log²t)`
  --     `= ∫_y^x 1 / (t · log t) + ∫_y^x δ(t) / (t · log²t)`,
  -- split via integrability of each part.
  have hsimpx : partialSumLog x / Real.log x = 1 + (partialSumLog x - Real.log x) / Real.log x := by
    rw [sub_div]; rw [div_self hlogx_ne]; ring
  have hsimpy : partialSumLog y / Real.log y = 1 + (partialSumLog y - Real.log y) / Real.log y := by
    rw [sub_div]; rw [div_self hlogy_ne]; ring
  have hint_log_yx : IntervalIntegrable (fun t => Real.log t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume y x := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hyx]
    intro z hz
    have hz_ge_y : y ≤ z := hz.1
    have hz_ge_2 : (2 : ℝ) ≤ z := le_trans hy hz_ge_y
    have hz_pos : (0 : ℝ) < z := by linarith
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hz_gt_1 : (1 : ℝ) < z := by linarith
    have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
    have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
    have hlog2_ne : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    have hprod_ne : z * (Real.log z) ^ 2 ≠ 0 := mul_ne_zero hz_ne hlog2_ne
    refine ContinuousAt.continuousWithinAt ?_
    fun_prop
  have hint_partialSumLog_yx : IntervalIntegrable
      (fun t => partialSumLog t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume y x := by
    have := hint_x
    have hyx_in_2x : Set.uIcc y x ⊆ Set.uIcc 2 x := by
      rw [Set.uIcc_of_le hyx, Set.uIcc_of_le hx]
      intro t ht
      exact ⟨le_trans hy ht.1, ht.2⟩
    exact this.mono_set hyx_in_2x
  have hint_delta_yx : IntervalIntegrable
      (fun t => (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2))
      MeasureTheory.volume y x := by
    have heq : (fun t => (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2))
        = (fun t => partialSumLog t / (t * (Real.log t) ^ 2)
                    - Real.log t / (t * (Real.log t) ^ 2)) := by
      funext t; ring
    rw [heq]
    exact hint_partialSumLog_yx.sub hint_log_yx
  -- `1 / (t · log t) = log(t) / (t · log²t)` pointwise on `Ioc y x`.
  have hint_rec : (fun t : ℝ => Real.log t / (t * (Real.log t) ^ 2))
                  =ᵐ[MeasureTheory.volume.restrict (Set.Ioc y x)]
                  (fun t : ℝ => 1 / (t * Real.log t)) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht_ge_y : y < t := ht.1
    have ht_ge_2 : (2 : ℝ) ≤ t := by linarith
    have ht_pos : 0 < t := by linarith
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_gt_1 : 1 < t := by linarith
    have hlog_pos : 0 < Real.log t := Real.log_pos ht_gt_1
    have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
    have hlog2_ne : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    have hprod_ne : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero ht_ne hlog2_ne
    have hprod1_ne : t * Real.log t ≠ 0 := mul_ne_zero ht_ne hlog_ne
    change Real.log t / (t * (Real.log t) ^ 2) = 1 / (t * Real.log t)
    rw [pow_two]; field_simp
  have hint_log_eq : ∫ t in y..x, Real.log t / (t * (Real.log t) ^ 2)
                  = ∫ t in y..x, 1 / (t * Real.log t) := by
    rw [intervalIntegral.integral_of_le hyx, intervalIntegral.integral_of_le hyx]
    exact MeasureTheory.integral_congr_ae hint_rec
  have hint_decomp : ∫ t in y..x, partialSumLog t / (t * (Real.log t) ^ 2)
      = (Real.log (Real.log x) - Real.log (Real.log y))
      + ∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2) := by
    have heq : (fun t : ℝ => partialSumLog t / (t * (Real.log t) ^ 2))
             = (fun t : ℝ => Real.log t / (t * (Real.log t) ^ 2)
                + (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)) := by
      funext t; ring
    rw [show (fun t : ℝ => partialSumLog t / (t * (Real.log t) ^ 2)) =
        (fun t : ℝ => Real.log t / (t * (Real.log t) ^ 2)
         + (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)) from heq]
    rw [intervalIntegral.integral_add hint_log_yx hint_delta_yx]
    rw [hint_log_eq, hint_log_split]
  -- Assembled: `F(x) − F(y) = δ(x)/log x − δ(y)/log y + ∫_y^x δ(t) / (t · log²t)`.
  have hF_diff :
      (partialSum x - Real.log (Real.log x)) -
        (partialSum y - Real.log (Real.log y))
      = (partialSumLog x - Real.log x) / Real.log x
        - (partialSumLog y - Real.log y) / Real.log y
        + ∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2) := by
    have : partialSum x - partialSum y =
        ((partialSumLog x - Real.log x) / Real.log x + 1)
        - ((partialSumLog y - Real.log y) / Real.log y + 1)
        + ((Real.log (Real.log x) - Real.log (Real.log y))
           + ∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)) := by
      rw [hsubpiv]
      have hxsim : partialSumLog x / Real.log x =
          (partialSumLog x - Real.log x) / Real.log x + 1 := by
        rw [hsimpx]; ring
      have hysim : partialSumLog y / Real.log y =
          (partialSumLog y - Real.log y) / Real.log y + 1 := by
        rw [hsimpy]; ring
      rw [hxsim, hysim, hint_decomp]
    linarith
  rw [hF_diff]
  -- Bound each of the three terms by `C / log y`.
  have hδx_abs : |partialSumLog x - Real.log x| ≤ C := hC_ge x hx
  have hδy_abs : |partialSumLog y - Real.log y| ≤ C := hC_ge y hy
  have hT1 : |(partialSumLog x - Real.log x) / Real.log x| ≤ C / Real.log y := by
    rw [abs_div]
    have hlogx_abs : |Real.log x| = Real.log x := abs_of_pos hlogx_pos
    rw [hlogx_abs]
    have hbnd1 : |partialSumLog x - Real.log x| / Real.log x ≤ C / Real.log x := by
      apply div_le_div_of_nonneg_right hδx_abs (le_of_lt hlogx_pos)
    have hbnd2 : C / Real.log x ≤ C / Real.log y := by
      apply div_le_div_of_nonneg_left (le_of_lt hC_pos) hlogy_pos hlogx_ge_logy
    linarith
  have hT2 : |(partialSumLog y - Real.log y) / Real.log y| ≤ C / Real.log y := by
    rw [abs_div]
    have hlogy_abs : |Real.log y| = Real.log y := abs_of_pos hlogy_pos
    rw [hlogy_abs]
    apply div_le_div_of_nonneg_right hδy_abs (le_of_lt hlogy_pos)
  -- Term 3: |∫_y^x δ(t)/(t·log²t)| ≤ C·(1/log y - 1/log x) ≤ C/log y.
  have hT3 : |∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)|
              ≤ C / Real.log y := by
    -- Bound the integrand: |δ(t)/(t·log²t)| ≤ C/(t·log²t) for t ∈ [y, x].
    have habs_bound : ∀ t ∈ Set.uIoc y x,
        ‖(partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)‖
          ≤ C * (1 / (t * (Real.log t) ^ 2)) := by
      intro t ht
      rw [Set.uIoc_of_le hyx] at ht
      have ht_ge_y : y < t := ht.1
      have ht_ge_2 : (2 : ℝ) ≤ t := by linarith
      have ht_pos : 0 < t := by linarith
      have ht_ne : t ≠ 0 := ne_of_gt ht_pos
      have ht_gt_1 : 1 < t := by linarith
      have hlog_pos : 0 < Real.log t := Real.log_pos ht_gt_1
      have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
      have hlog2_pos : 0 < (Real.log t) ^ 2 := by positivity
      have hprod_pos : 0 < t * (Real.log t) ^ 2 := by positivity
      have hδt : |partialSumLog t - Real.log t| ≤ C := hC_ge t ht_ge_2
      rw [Real.norm_eq_abs, abs_div]
      have h1 : |t * (Real.log t) ^ 2| = t * (Real.log t) ^ 2 := abs_of_pos hprod_pos
      rw [h1]
      rw [mul_one_div]
      exact (div_le_div_iff_of_pos_right hprod_pos).mpr hδt
    have hbound_int : IntervalIntegrable (fun t => C * (1 / (t * (Real.log t) ^ 2)))
        MeasureTheory.volume y x := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hyx]
      intro z hz
      have hz_ge_y : y ≤ z := hz.1
      have hz_ge_2 : (2 : ℝ) ≤ z := le_trans hy hz_ge_y
      have hz_pos : (0 : ℝ) < z := by linarith
      have hz_ne : z ≠ 0 := ne_of_gt hz_pos
      have hz_gt_1 : (1 : ℝ) < z := by linarith
      have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
      have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
      have hlog2_ne : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
      have hprod_ne : z * (Real.log z) ^ 2 ≠ 0 := mul_ne_zero hz_ne hlog2_ne
      refine ContinuousAt.continuousWithinAt ?_
      fun_prop
    have hineq : |∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)|
        ≤ ∫ t in y..x, C * (1 / (t * (Real.log t) ^ 2)) := by
      have habs_bound' : ∀ᵐ (t : ℝ) ∂MeasureTheory.volume,
          t ∈ Set.Ioc y x →
            ‖(partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)‖
              ≤ C * (1 / (t * (Real.log t) ^ 2)) := by
        refine Filter.Eventually.of_forall ?_
        intro t ht
        have : t ∈ Set.uIoc y x := by
          rw [Set.uIoc_of_le hyx]; exact ht
        exact habs_bound t this
      have hint_abs : ‖∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)‖
          ≤ ∫ t in y..x, C * (1 / (t * (Real.log t) ^ 2)) :=
        intervalIntegral.norm_integral_le_of_norm_le hyx habs_bound' hbound_int
      have h_norm_eq : ‖∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)‖
          = |∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)| := by
        rfl
      linarith [hint_abs, h_norm_eq.symm.le, h_norm_eq.le]
    -- Compute ∫_y^x C · (1/(t·log²t)) = C · (1/log y - 1/log x).
    have h_int_sq_yx : ∫ t in y..x, 1 / (t * (Real.log t) ^ 2)
        = 1 / Real.log y - 1 / Real.log x := by
      have h1 : ∫ t in (2 : ℝ)..x, 1 / (t * (Real.log t) ^ 2) =
          1 / Real.log 2 - 1 / Real.log x := integral_one_div_t_log_sq hx
      have h2 : ∫ t in (2 : ℝ)..y, 1 / (t * (Real.log t) ^ 2) =
          1 / Real.log 2 - 1 / Real.log y := integral_one_div_t_log_sq hy
      have hint_sq_2y : IntervalIntegrable (fun t => 1 / (t * (Real.log t) ^ 2))
          MeasureTheory.volume 2 y := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hy]
        intro z hz
        have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
        have hz_pos : (0 : ℝ) < z := by linarith
        have hz_ne : z ≠ 0 := ne_of_gt hz_pos
        have hz_gt_1 : (1 : ℝ) < z := by linarith
        have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
        have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
        have hlog2_ne : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
        have hprod_ne : z * (Real.log z) ^ 2 ≠ 0 := mul_ne_zero hz_ne hlog2_ne
        refine ContinuousAt.continuousWithinAt ?_
        fun_prop
      have hint_sq_2x : IntervalIntegrable (fun t => 1 / (t * (Real.log t) ^ 2))
          MeasureTheory.volume 2 x := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hx]
        intro z hz
        have hz_ge_2 : (2 : ℝ) ≤ z := hz.1
        have hz_pos : (0 : ℝ) < z := by linarith
        have hz_ne : z ≠ 0 := ne_of_gt hz_pos
        have hz_gt_1 : (1 : ℝ) < z := by linarith
        have hlog_pos : 0 < Real.log z := Real.log_pos hz_gt_1
        have hlog_ne : Real.log z ≠ 0 := ne_of_gt hlog_pos
        have hlog2_ne : Real.log z ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
        have hprod_ne : z * (Real.log z) ^ 2 ≠ 0 := mul_ne_zero hz_ne hlog2_ne
        refine ContinuousAt.continuousWithinAt ?_
        fun_prop
      have hsplit := intervalIntegral.integral_interval_sub_left hint_sq_2x hint_sq_2y
      linarith
    -- `∫_y^x C · 1/(t · log²t) = C · (1/log y − 1/log x)`.
    have h_int_eq : ∫ t in y..x, C * (1 / (t * (Real.log t) ^ 2))
        = C * (1 / Real.log y - 1 / Real.log x) := by
      rw [intervalIntegral.integral_const_mul, h_int_sq_yx]
    have hineq' : |∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)|
        ≤ C * (1 / Real.log y - 1 / Real.log x) := by
      rw [h_int_eq] at hineq
      exact hineq
    have hbnd_final : C * (1 / Real.log y - 1 / Real.log x) ≤ C / Real.log y := by
      have h1 : 0 ≤ 1 / Real.log x := by positivity
      have ha : C * (1 / Real.log y - 1 / Real.log x) ≤ C * (1 / Real.log y) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
        linarith
      have hb : C * (1 / Real.log y) = C / Real.log y := by ring
      linarith
    linarith
  have htri : |(partialSumLog x - Real.log x) / Real.log x
              - (partialSumLog y - Real.log y) / Real.log y
              + ∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)|
      ≤ |(partialSumLog x - Real.log x) / Real.log x|
        + |(partialSumLog y - Real.log y) / Real.log y|
        + |∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)| := by
    set A := (partialSumLog x - Real.log x) / Real.log x
    set B := (partialSumLog y - Real.log y) / Real.log y
    set I := ∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)
    have h1 : |A - B + I| ≤ |A - B| + |I| := abs_add_le _ _
    have h2 : |A - B| ≤ |A| + |B| := by
      have := abs_add_le A (-B)
      simpa [sub_eq_add_neg, abs_neg] using this
    linarith
  have hcombined : |(partialSumLog x - Real.log x) / Real.log x
          - (partialSumLog y - Real.log y) / Real.log y
          + ∫ t in y..x, (partialSumLog t - Real.log t) / (t * (Real.log t) ^ 2)|
      ≤ 3 * C / Real.log y := by
    have hsum : C / Real.log y + C / Real.log y + C / Real.log y = 3 * C / Real.log y := by
      ring
    linarith
  have : 3 * C / Real.log y = 3 * (|C₀| + 1) / Real.log y := by rw [hCdef]
  linarith

/--
**Mertens' Third Theorem — existence of the Meissel–Mertens limit.**

The sequence `x ↦ partialSum x - log log x` converges as `x → ∞`; its limit is
the **Meissel–Mertens constant** `M₃ ≈ 0.26149721…`.

The proof is the standard Cauchy-criterion argument: by combining the M3 Abel
pivot `partialSum_eq_partialSumLog_div_log_add_integral`, the M1 bound, and the
closed-form antiderivatives `integral_one_div_t_log_t`, `integral_one_div_t_log_sq`,
one establishes that `|F(x) - F(y)| ≤ K / log y` for `2 ≤ y ≤ x`, where
`F(x) := partialSum x - log log x`. Completeness of `ℝ` then delivers the
limit. -/
theorem third_exists :
    ∃ M : ℝ, ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X,
      |partialSum x - Real.log (Real.log x) - M| < ε := by
  -- Oscillation constant: `|F(x) − F(y)| ≤ K / log y` for `2 ≤ y ≤ x`.
  set K : ℝ := 3 * (|Classical.choose first| + 1) with hKdef
  have hK_pos : 0 < K := by
    have : 0 < |Classical.choose first| + 1 := by positivity
    positivity
  -- Cauchy sequence `u n := F(n + 2)`; for `m ≤ n`, `|u n − u m| ≤ K / log (m + 2)`.
  set u : ℕ → ℝ := fun n => partialSum (n + 2 : ℝ) - Real.log (Real.log (n + 2 : ℝ)) with hudef
  have hu_cauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- `K / log (n + 2) → 0` since `log` is unbounded.
    have hlog_tend : Filter.Tendsto (fun n : ℕ => K / Real.log ((n : ℝ) + 2))
        Filter.atTop (nhds 0) := by
      have h_cast : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2))
          Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h1 : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2))
          Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp h_cast
      exact Filter.Tendsto.div_atTop (f := fun _ : ℕ => K)
        (tendsto_const_nhds (x := K) (f := Filter.atTop)) h1
    obtain ⟨N, hN⟩ := (tendsto_atTop_nhds.mp hlog_tend) (Set.Ioo (-ε) ε)
      (by constructor <;> [linarith; linarith]) isOpen_Ioo
    refine ⟨N, ?_⟩
    have helper : ∀ {m n : ℕ}, N ≤ m → m ≤ n →
        |(partialSum ((n : ℝ) + 2) - Real.log (Real.log ((n : ℝ) + 2)))
          - (partialSum ((m : ℝ) + 2) - Real.log (Real.log ((m : ℝ) + 2)))| < ε := by
      intro m n hmN hmn
      have hy : (2 : ℝ) ≤ ((m : ℝ) + 2) := by
        have : (0 : ℝ) ≤ m := by exact_mod_cast (Nat.zero_le m)
        linarith
      have hyx : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
        have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
        linarith
      have hosc := partialSum_sub_log_log_oscillation
        (y := ((m : ℝ) + 2)) (x := ((n : ℝ) + 2)) hy hyx
      have hbnd :
          |(partialSum ((n : ℝ) + 2) - Real.log (Real.log ((n : ℝ) + 2)))
            - (partialSum ((m : ℝ) + 2) - Real.log (Real.log ((m : ℝ) + 2)))| ≤
          K / Real.log ((m : ℝ) + 2) := by
        have := hosc
        rw [hKdef]
        exact this
      have hN_app : K / Real.log ((m : ℝ) + 2) ∈ Set.Ioo (-ε) ε := hN m hmN
      have hKlt : K / Real.log ((m : ℝ) + 2) < ε := hN_app.2
      linarith
    intro m hm n hn
    have hu_eq_m : u m = partialSum ((m : ℝ) + 2) - Real.log (Real.log ((m : ℝ) + 2)) := rfl
    have hu_eq_n : u n = partialSum ((n : ℝ) + 2) - Real.log (Real.log ((n : ℝ) + 2)) := rfl
    by_cases hmn : m ≤ n
    · rw [Real.dist_eq, hu_eq_m, hu_eq_n, abs_sub_comm]
      exact helper hm hmn
    · have hmn' : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_le hmn)
      rw [Real.dist_eq, hu_eq_m, hu_eq_n]
      exact helper hn hmn'
  obtain ⟨M, hM⟩ := cauchySeq_tendsto_of_complete hu_cauchy
  refine ⟨M, ?_⟩
  intro ε hε
  -- Pick `N₁` for `u → M` (within `ε/2`) and `N₂` so the oscillation bound is `< ε/2`.
  have hε2 : 0 < ε / 2 := by linarith
  rw [Metric.tendsto_atTop] at hM
  obtain ⟨N₁, hN₁⟩ := hM (ε / 2) hε2
  have hlog_tend : Filter.Tendsto (fun n : ℕ => K / Real.log (n + 2 : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2))
        Filter.atTop Filter.atTop := by
      have h_cast : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2))
          Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact Real.tendsto_log_atTop.comp h_cast
    have h2 := Filter.Tendsto.div_atTop (f := fun _ : ℕ => K)
      (tendsto_const_nhds (x := K) (f := Filter.atTop)) h1
    exact h2
  obtain ⟨N₂, hN₂⟩ := (tendsto_atTop_nhds.mp hlog_tend) (Set.Ioo (-(ε/2)) (ε/2))
    (by constructor <;> [linarith; linarith]) isOpen_Ioo
  set N := max N₁ N₂ with hNdef
  refine ⟨(N + 2 : ℝ), ?_⟩
  intro x hx
  have hy : (2 : ℝ) ≤ (N + 2 : ℝ) := by
    have : (0 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_le N)
    linarith
  have hyx : ((N : ℝ) + 2) ≤ x := hx
  have hosc := partialSum_sub_log_log_oscillation
    (y := ((N : ℝ) + 2)) (x := x) hy hyx
  have hN_use : N₁ ≤ N := le_max_left _ _
  have hN_to_M : dist (u N) M < ε / 2 := hN₁ N hN_use
  have hN_log : K / Real.log (N + 2 : ℝ) < ε / 2 := by
    have hN_use : N₂ ≤ N := le_max_right _ _
    have hN₂_app : K / Real.log (N + 2 : ℝ) ∈ Set.Ioo (-(ε/2)) (ε/2) := hN₂ N hN_use
    exact hN₂_app.2
  have hu_eq : u N = partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ)) := rfl
  rw [Real.dist_eq] at hN_to_M
  have hbnd : |(partialSum x - Real.log (Real.log x))
      - (partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ)))| ≤
      K / Real.log (N + 2 : ℝ) := by
    have := hosc
    rw [hKdef]
    exact this
  have := abs_add_le
    ((partialSum x - Real.log (Real.log x)) -
      (partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ))))
    ((partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ))) - M)
  have hsimp :
    ((partialSum x - Real.log (Real.log x)) -
      (partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ)))) +
      ((partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ))) - M) =
      partialSum x - Real.log (Real.log x) - M := by ring
  have hfinal :
      |partialSum x - Real.log (Real.log x) - M| ≤
      |(partialSum x - Real.log (Real.log x)) -
        (partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ)))| +
      |(partialSum (N + 2 : ℝ) - Real.log (Real.log (N + 2 : ℝ))) - M| := by
    rw [← hsimp]
    exact this
  rw [hu_eq] at hN_to_M
  linarith

/-- **`meisselMertensConstant`**: the Meissel–Mertens constant `M₃ ≈ 0.26149721…`,
    defined as the limit whose existence is guaranteed by `third_exists`. -/
noncomputable def meisselMertensConstant : ℝ := Classical.choose third_exists

/-- Defining property of `meisselMertensConstant`, an immediate consequence of
    `Classical.choose_spec` applied to `third_exists`. -/
theorem meisselMertensConstant_spec :
    ∀ ε > (0 : ℝ), ∃ X : ℝ, ∀ x ≥ X,
      |partialSum x - Real.log (Real.log x) - meisselMertensConstant| < ε :=
  Classical.choose_spec third_exists

/--
**Headline Mertens M3 with explicit `O(1/log x)` rate.**

$$\sum_{p \le x} \frac{1}{p} \;=\; \log\log x \,+\, M_3 \,+\, O\!\left(\frac{1}{\log x}\right).$$

Such is the quantitative refinement of `third_exists`: the rate `O(1/log x)`
follows from the `O(1)` error term in `first`, once one applies Abel summation
with the weight `1/(t log² t)`.
-/
theorem third :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
      |partialSum x - Real.log (Real.log x) - meisselMertensConstant| ≤ C / Real.log x := by
  -- The oscillation bound with `y := x` and `z ≥ x` gives `|F(x) − F(z)| ≤ K / log x`.
  -- Sending `z → ∞`, `F(z) → meisselMertensConstant`, so `|F(x) − …| ≤ K / log x`.
  set K : ℝ := 3 * (|Classical.choose first| + 1) with hKdef
  have hK_pos : 0 < K := by
    have : 0 < |Classical.choose first| + 1 := by positivity
    positivity
  refine ⟨K, ?_⟩
  intro x hx
  have hx_pos : 0 < x := by linarith
  have hx_gt_1 : 1 < x := by linarith
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt_1
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hspec := meisselMertensConstant_spec
  -- Argue by contradiction: if `|F(x) − …| > K / log x`, set
  -- `δ := |F(x) − …| − K / log x > 0` and pick `z` with `|F(z) − …| < δ/2`;
  -- the triangle inequality then forces `δ ≤ δ/2`.
  by_contra hcontra
  have h : K / Real.log x < |partialSum x - Real.log (Real.log x) - meisselMertensConstant| :=
    not_le.mp hcontra
  set δ : ℝ := |partialSum x - Real.log (Real.log x) - meisselMertensConstant| - K / Real.log x
    with hδdef
  have hδ_pos : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨X, hX⟩ := hspec (δ / 2) (by linarith)
  set z : ℝ := max x X + 1 with hzdef
  have hz_ge_x : x ≤ z := by
    rw [hzdef]; linarith [le_max_left x X]
  have hz_ge_X : X ≤ z := by
    rw [hzdef]; linarith [le_max_right x X]
  have hosc := partialSum_sub_log_log_oscillation
    (y := x) (x := z) hx hz_ge_x
  have hbnd : |(partialSum z - Real.log (Real.log z))
              - (partialSum x - Real.log (Real.log x))| ≤
              K / Real.log x := by
    have := hosc
    rw [hKdef]
    exact this
  have hX_app := hX z hz_ge_X
  have htri := abs_add_le
    ((partialSum x - Real.log (Real.log x)) - (partialSum z - Real.log (Real.log z)))
    ((partialSum z - Real.log (Real.log z)) - meisselMertensConstant)
  have hsimp :
      ((partialSum x - Real.log (Real.log x)) - (partialSum z - Real.log (Real.log z))) +
      ((partialSum z - Real.log (Real.log z)) - meisselMertensConstant) =
      partialSum x - Real.log (Real.log x) - meisselMertensConstant := by ring
  have hT1 : |((partialSum x - Real.log (Real.log x)) - (partialSum z - Real.log (Real.log z)))| ≤
             K / Real.log x := by
    rw [abs_sub_comm]; exact hbnd
  have hT2 : |((partialSum z - Real.log (Real.log z)) - meisselMertensConstant)| < δ / 2 := hX_app
  have : |partialSum x - Real.log (Real.log x) - meisselMertensConstant| ≤
         K / Real.log x + δ / 2 := by
    have hsim2 :
      |partialSum x - Real.log (Real.log x) - meisselMertensConstant| ≤
      |((partialSum x - Real.log (Real.log x)) - (partialSum z - Real.log (Real.log z)))|
        + |((partialSum z - Real.log (Real.log z)) - meisselMertensConstant)| := by
      rw [← hsimp]; exact htri
    linarith
  linarith [hδ_pos]

/--
**Bounded form of Mertens' third theorem.**

A direct consequence of `third`: the difference `partialSum x - log log x` is
*bounded* on `[2, ∞)`, without an explicit rate. Such is the form invoked by
applications that only require compactness of the orbit of partial sums; the
headline asymptotic `third` (with the `O(1/log x)` rate) is, of course,
strictly stronger.
-/
theorem partialSum_sub_log_log_bounded :
    ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x →
      |partialSum x - Real.log (Real.log x)| ≤ K := by
  -- From `third_exists`, the function is bounded for large `x`. On the finite head
  -- `[2, X']`, `partialSum x ≤ partialSum X'` (monotone in `⌊x⌋₊`) and
  -- `|log log x| ≤ max |log log 2| |log log X'|`.
  obtain ⟨M, hM⟩ := third_exists
  obtain ⟨X, hX⟩ := hM 1 one_pos
  set X' : ℝ := max X 2 with hX'def
  have hX'_ge_X : X ≤ X' := le_max_left _ _
  have hX'_ge_2 : (2 : ℝ) ≤ X' := le_max_right _ _
  -- Tail bound `x ≥ X'`: `|f(x)| ≤ |M| + 1`.
  have htail : ∀ x ≥ X', |partialSum x - Real.log (Real.log x)| ≤ |M| + 1 := by
    intro x hx
    have hx_ge_X : X ≤ x := le_trans hX'_ge_X hx
    have hbnd := hX x hx_ge_X
    have htriangle : |partialSum x - Real.log (Real.log x)|
        ≤ |partialSum x - Real.log (Real.log x) - M| + |M| := by
      have := abs_add_le (partialSum x - Real.log (Real.log x) - M) M
      simpa [sub_add_cancel] using this
    linarith
  -- Head bound `x ∈ [2, X']`: `partialSum x ≤ Sbound` (finite sum over `primesBelow N`,
  -- with `N := ⌊X'⌋₊ + 1`), and `|log log x| ≤ Lbound`. The `log ∘ log` bound uses
  -- monotonicity of `log` on `[2, ∞)` (where `log ≥ log 2 > 0`).
  set N : ℕ := ⌊X'⌋₊ + 1 with hNdef
  set Sbound : ℝ := ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p with hSbound
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  set Lbound : ℝ := max |Real.log (Real.log 2)| |Real.log (Real.log X')| with hLbound
  refine ⟨max (Sbound + Lbound) (|M| + 1), ?_⟩
  intro x hx
  by_cases hxX' : X' ≤ x
  · exact le_trans (htail x hxX') (le_max_right _ _)
  · have hx_lt_X' : x < X' := lt_of_not_ge hxX'
    have hfloor_le : ⌊x⌋₊ + 1 ≤ N := by
      have h1 : ⌊x⌋₊ ≤ ⌊X'⌋₊ := Nat.floor_le_floor (le_of_lt hx_lt_X')
      omega
    have hSum_le : partialSum x ≤ Sbound := by
      unfold partialSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · -- `Nat.primesBelow` is monotone in `n`.
        intro p hp
        rw [Nat.primesBelow_eq_filter_range, Finset.mem_filter] at hp ⊢
        refine ⟨?_, hp.2⟩
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hp.1) hfloor_le)
      · intro p hp _
        have hp_prime : Nat.Prime p := by
          rw [Nat.primesBelow_eq_filter_range, Finset.mem_filter] at hp
          exact hp.2
        have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_prime.pos
        positivity
    have hSum_nonneg : 0 ≤ partialSum x := partialSum_nonneg x
    have hlog_x_pos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le one_lt_two hx)
    have hlog_2_le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hlog_x_le : Real.log x ≤ Real.log X' :=
      Real.log_le_log (by linarith) (le_of_lt hx_lt_X')
    have hloglog_x_lb : Real.log (Real.log 2) ≤ Real.log (Real.log x) :=
      Real.log_le_log hlog2_pos hlog_2_le
    have hloglog_x_ub : Real.log (Real.log x) ≤ Real.log (Real.log X') :=
      Real.log_le_log hlog_x_pos hlog_x_le
    have hloglog_abs : |Real.log (Real.log x)| ≤ Lbound := by
      rw [abs_le]
      constructor
      · have h1 : -|Real.log (Real.log 2)| ≤ Real.log (Real.log 2) := neg_abs_le _
        have h2 : -Lbound ≤ -|Real.log (Real.log 2)| := by
          rw [neg_le_neg_iff]; exact le_max_left _ _
        linarith
      · have h1 : Real.log (Real.log X') ≤ |Real.log (Real.log X')| := le_abs_self _
        have h2 : |Real.log (Real.log X')| ≤ Lbound := le_max_right _ _
        linarith
    have : |partialSum x - Real.log (Real.log x)|
        ≤ |partialSum x| + |Real.log (Real.log x)| := abs_sub _ _
    have habs_sum : |partialSum x| ≤ Sbound := by
      rw [abs_of_nonneg hSum_nonneg]; exact hSum_le
    have : |partialSum x - Real.log (Real.log x)| ≤ Sbound + Lbound := by
      linarith
    exact le_trans this (le_max_left _ _)

end Mertens
