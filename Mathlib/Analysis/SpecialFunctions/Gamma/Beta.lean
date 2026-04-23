/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Batteries.Tactic.Congr
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness
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
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# The Beta function, and further properties of the Gamma function

In this file we define the Beta integral, relate Beta and Gamma functions, and prove some
refined properties of the Gamma function using these relations.

## Results on the Beta function

* `Complex.betaIntegral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `Complex.Gamma_mul_Gamma_eq_betaIntegral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * betaIntegral u v`.

## Results on the Gamma function

* `Complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `Complex.GammaSeq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `Complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.
* `Complex.differentiable_one_div_Gamma`: the function `1 / Γ(s)` is differentiable everywhere.
* `Complex.Gamma_mul_Gamma_add_half`: Legendre's duplication formula
  `Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π`.
* `Real.Gamma_ne_zero`, `Real.GammaSeq_tendsto_Gamma`,
  `Real.Gamma_mul_Gamma_one_sub`, `Real.Gamma_mul_Gamma_add_half`: real versions of the above.
-/

@[expose] public section


noncomputable section


open Filter intervalIntegral Set Real MeasureTheory

open scoped Nat Topology Real

section BetaIntegral

/-! ## The Beta function -/


namespace Complex

/-- The Beta function `Β (u, v)`, defined as `∫ x:ℝ in 0..1, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def betaIntegral (u v : ℂ) : ℂ :=
  ∫ x : ℝ in 0..1, (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)

/-- Auxiliary lemma for `betaIntegral_convergent`, showing convergence at the left endpoint. -/
theorem betaIntegral_convergent_left {u : ℂ} (hu : 0 < re u) (v : ℂ) :
    IntervalIntegrable (fun x =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) := by
  apply IntervalIntegrable.mul_continuousOn
  · refine intervalIntegral.intervalIntegrable_cpow' ?_
    rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 1 / 2)] at hx
    apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
    norm_cast
    exact ofReal_mem_slitPlane.2 <| by linarith only [hx.2]

/-- The Beta integral is convergent for all `u, v` of positive real part. -/
theorem betaIntegral_convergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    IntervalIntegrable (fun x =>
      (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1) : ℝ → ℂ) volume 0 1 := by
  refine (betaIntegral_convergent_left hu v).trans ?_
  rw [IntervalIntegrable.iff_comp_neg]
  convert ((betaIntegral_convergent_left hv u).comp_add_right 1).symm using 1
  · ext1 x
    conv_lhs => rw [mul_comm]
    congr 2 <;> · push_cast; ring
  · norm_num
  · simp

theorem betaIntegral_symm (u v : ℂ) : betaIntegral v u = betaIntegral u v := by
  simpa [betaIntegral, ← intervalIntegral.integral_symm, add_comm, mul_comm, sub_eq_add_neg]
    using intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := -1)
      (fun x : ℝ => (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)) neg_one_lt_zero.ne 1

theorem betaIntegral_eval_one_right {u : ℂ} (hu : 0 < re u) : betaIntegral u 1 = 1 / u := by
  simp_rw [betaIntegral, sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl _)]
  · rw [ofReal_zero, ofReal_one, one_cpow, zero_cpow, sub_zero, sub_add_cancel]
    rw [sub_add_cancel]
    contrapose! hu; rw [hu, zero_re]
  · rwa [sub_re, one_re, ← sub_pos, sub_neg_eq_add, sub_add_cancel]

set_option backward.isDefEq.respectTransparency false in
theorem betaIntegral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ x in 0..a, (x : ℂ) ^ (s - 1) * ((a : ℂ) - x) ^ (t - 1) =
    (a : ℂ) ^ (s + t - 1) * betaIntegral s t := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  rw [betaIntegral]
  have A : (a : ℂ) ^ (s + t - 1) = a * ((a : ℂ) ^ (s - 1) * (a : ℂ) ^ (t - 1)) := by
    rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1)), cpow_add _ _ ha', cpow_add 1 _ ha', cpow_one,
      mul_assoc]
  rw [A, mul_assoc, ← intervalIntegral.integral_const_mul, ← real_smul, ← zero_div a, ←
    div_self ha.ne', ← intervalIntegral.integral_comp_div _ ha.ne', zero_div]
  simp_rw [intervalIntegral.integral_of_le ha.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [mul_mul_mul_comm]
  congr 1
  · rw [← mul_cpow_ofReal_nonneg ha.le (div_pos hx.1 ha).le, ofReal_div, mul_div_cancel₀ _ ha']
  · rw [(by norm_cast : (1 : ℂ) - ↑(x / a) = ↑(1 - x / a)), ←
      mul_cpow_ofReal_nonneg ha.le (sub_nonneg.mpr <| (div_le_one ha).mpr hx.2)]
    push_cast
    rw [mul_sub, mul_one, mul_div_cancel₀ _ ha']

set_option backward.isDefEq.respectTransparency false in
/-- Relation between Beta integral and Gamma function. -/
theorem Gamma_mul_Gamma_eq_betaIntegral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t := by
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_posConvolution
    (GammaIntegral_convergent hs) (GammaIntegral_convergent ht) (ContinuousLinearMap.mul ℝ ℂ)
  simp_rw [ContinuousLinearMap.mul_apply'] at conv_int
  have hst : 0 < re (s + t) := by rw [add_re]; exact add_pos hs ht
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, GammaIntegral,
    GammaIntegral, GammaIntegral, ← conv_int, ← MeasureTheory.integral_mul_const (betaIntegral _ _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [mul_assoc, ← betaIntegral_scaled s t hx, ← intervalIntegral.integral_const_mul]
  congr 1 with y : 1
  push_cast
  suffices Complex.exp (-x) = Complex.exp (-y) * Complex.exp (-(x - y)) by rw [this]; ring
  rw [← Complex.exp_add]; congr 1; abel

set_option backward.isDefEq.respectTransparency false in
/-- Recurrence formula for the Beta function. -/
theorem betaIntegral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
    u * betaIntegral u (v + 1) = v * betaIntegral (u + 1) v := by
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_betaIntegral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ u * (1 - (x : ℂ)) ^ v
  have hu' : 0 < re (u + 1) := by rw [add_re, one_re]; positivity
  have hv' : 0 < re (v + 1) := by rw [add_re, one_re]; positivity
  have hc : ContinuousOn F (Icc 0 1) := by
    refine (continuousOn_of_forall_continuousAt fun x hx => ?_).mul
        (continuousOn_of_forall_continuousAt fun x hx => ?_)
    · refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) hu).comp continuous_ofReal.continuousAt
      rw [ofReal_re]; exact hx.1
    · refine (continuousAt_cpow_const_of_re_pos (Or.inl ?_) hv).comp (by fun_prop)
      rw [sub_re, one_re, ofReal_re, sub_nonneg]
      exact hx.2
  have hder : ∀ x : ℝ, x ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt F (u * ((x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ v) -
        v * ((x : ℂ) ^ u * (1 - (x : ℂ)) ^ (v - 1))) x := by
    intro x hx
    have U : HasDerivAt (fun y : ℂ => y ^ u) (u * (x : ℂ) ^ (u - 1)) ↑x := by
      have := @HasDerivAt.cpow_const _ _ _ u (hasDerivAt_id (x : ℂ)) (Or.inl ?_)
      · simp only [id_eq, mul_one] at this
        exact this
      · rw [id_eq, ofReal_re]; exact hx.1
    have V : HasDerivAt (fun y : ℂ => (1 - y) ^ v) (-v * (1 - (x : ℂ)) ^ (v - 1)) ↑x := by
      have A := @HasDerivAt.cpow_const _ _ _ v (hasDerivAt_id (1 - (x : ℂ))) (Or.inl ?_)
      swap; · rw [id, sub_re, one_re, ofReal_re, sub_pos]; exact hx.2
      simp_rw [id] at A
      have B : HasDerivAt (fun y : ℂ => 1 - y) (-1) ↑x := by
        apply HasDerivAt.const_sub; apply hasDerivAt_id
      convert HasDerivAt.comp (↑x) A B using 1
      ring
    convert (U.mul V).comp_ofReal using 1
    ring
  have h_int := ((betaIntegral_convergent hu hv').const_mul u).sub
    ((betaIntegral_convergent hu' hv).const_mul v)
  rw [add_sub_cancel_right, add_sub_cancel_right] at h_int
  have int_ev := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hder h_int
  have hF0 : F 0 = 0 := by
    simp only [F, mul_eq_zero, ofReal_zero, cpow_eq_zero_iff, Ne,
      true_and, sub_zero, one_cpow, one_ne_zero, or_false]
    contrapose! hu; rw [hu, zero_re]
  have hF1 : F 1 = 0 := by
    simp only [F, mul_eq_zero, ofReal_one, one_cpow, one_ne_zero, sub_self, cpow_eq_zero_iff,
      Ne, true_and, false_or]
    contrapose! hv; rw [hv, zero_re]
  rw [hF0, hF1, sub_zero, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at int_ev
  · rw [betaIntegral, betaIntegral, ← sub_eq_zero]
    convert int_ev <;> ring
  · apply IntervalIntegrable.const_mul
    convert betaIntegral_convergent hu hv'; ring
  · apply IntervalIntegrable.const_mul
    convert betaIntegral_convergent hu' hv; ring

/-- Explicit formula for the Beta function when second argument is a positive integer. -/
theorem betaIntegral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
    betaIntegral u (n + 1) = n ! / ∏ j ∈ Finset.range (n + 1), (u + j) := by
  induction n generalizing u with
  | zero =>
    rw [Nat.cast_zero, zero_add, betaIntegral_eval_one_right hu, Nat.factorial_zero, Nat.cast_one]
    simp
  | succ n IH =>
    have := betaIntegral_recurrence hu (?_ : 0 < re n.succ)
    swap; · rw [← ofReal_natCast, ofReal_re]; positivity
    rw [mul_comm u _, ← eq_div_iff] at this
    swap; · contrapose! hu; rw [hu, zero_re]
    rw [this, Finset.prod_range_succ', Nat.cast_succ, IH]
    swap; · rw [add_re, one_re]; positivity
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ←
      mul_div_assoc, ← div_div]
    congr 3 with j : 1
    push_cast; abel

end Complex

end BetaIntegral

section LimitFormula

/-! ## The Euler limit formula -/


namespace Complex

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
We will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℂ) (n : ℕ) :=
  (n : ℂ) ^ s * n ! / ∏ j ∈ Finset.range (n + 1), (s + j)

theorem GammaSeq_eq_betaIntegral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
    GammaSeq s n = (n : ℂ) ^ s * betaIntegral s (n + 1) := by
  rw [GammaSeq, betaIntegral_eval_nat_add_one_right hs n, ← mul_div_assoc]

theorem GammaSeq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq (s + 1) n / s = n / (n + 1 + s) * GammaSeq s n := by
  conv_lhs => rw [GammaSeq, Finset.prod_range_succ, div_div]
  conv_rhs =>
    rw [GammaSeq, Finset.prod_range_succ', Nat.cast_zero, add_zero, div_mul_div_comm, ← mul_assoc,
      ← mul_assoc, mul_comm _ (Finset.prod _ _)]
  congr 3
  · rw [cpow_add _ _ (Nat.cast_ne_zero.mpr hn), cpow_one, mul_comm]
  · refine Finset.prod_congr (by rfl) fun x _ => ?_
    push_cast; ring
  · abel

set_option backward.isDefEq.respectTransparency false in
theorem GammaSeq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq s n = ∫ x : ℝ in 0..n, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) := by
  have : ∀ x : ℝ, x = x / n * n := by intro x; rw [div_mul_cancel₀]; exact Nat.cast_ne_zero.mpr hn
  conv_rhs => enter [1, x, 2, 1]; rw [this x]
  rw [GammaSeq_eq_betaIntegral_of_re_pos hs]
  have := intervalIntegral.integral_comp_div (a := 0) (b := n)
    (fun x => ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ) (Nat.cast_ne_zero.mpr hn)
  dsimp only at this
  rw [betaIntegral, this, real_smul, zero_div, div_self, add_sub_cancel_right,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  swap; · exact Nat.cast_ne_zero.mpr hn
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  push_cast
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have A : (n : ℂ) ^ s = (n : ℂ) ^ (s - 1) * n := by
    conv_lhs => rw [(by ring : s = s - 1 + 1), cpow_add _ _ hn']
    simp
  have B : ((x : ℂ) * ↑n) ^ (s - 1) = (x : ℂ) ^ (s - 1) * (n : ℂ) ^ (s - 1) := by
    rw [← ofReal_natCast,
      mul_cpow_ofReal_nonneg hx.1.le (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).le]
  rw [A, B, cpow_natCast]; ring

/-- The main technical lemma for `GammaSeq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
theorem approx_Gamma_integral_tendsto_Gamma_integral {s : ℂ} (hs : 0 < re s) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in 0..n, ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)) atTop
      (𝓝 <| Gamma s) := by
  rw [Gamma_eq_integral hs]
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : ℕ → ℝ → ℂ := fun n =>
    indicator (Ioc 0 (n : ℝ)) fun x : ℝ => ((1 - x / n) ^ n : ℝ) * (x : ℂ) ^ (s - 1)
  -- integrability of f
  have f_ible : ∀ n : ℕ, Integrable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    rw [integrable_indicator_iff (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)), IntegrableOn,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ← IntegrableOn, ←
      intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ n)]
    apply IntervalIntegrable.continuousOn_mul
    · refine intervalIntegral.intervalIntegrable_cpow' ?_
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · apply Continuous.continuousOn
      continuity
  -- pointwise limit of f
  have f_tends : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      Tendsto (fun n : ℕ => f n x) atTop (𝓝 <| ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1)) := by
    intro x hx
    apply Tendsto.congr'
    · change ∀ᶠ n : ℕ in atTop, ↑((1 - x / n) ^ n) * (x : ℂ) ^ (s - 1) = f n x
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      rw [Nat.ceil_le] at hn
      dsimp only [f]
      rw [indicator_of_mem]
      exact ⟨hx, hn⟩
    · simp_rw [mul_comm]
      refine (Tendsto.comp (continuous_ofReal.tendsto _) ?_).const_mul _
      convert Real.tendsto_one_add_div_pow_exp (-x) using 1
      ext1 n
      rw [neg_div, ← sub_eq_add_neg]
  -- let `convert` identify the remaining goals
  convert tendsto_integral_of_dominated_convergence _ (fun n => (f_ible n).1)
    (Real.GammaIntegral_convergent hs) _
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ f_tends)) using 1
  -- limit of f is the integrand we want
  · ext1 n
    rw [MeasureTheory.integral_indicator (measurableSet_Ioc : MeasurableSet (Ioc (_ : ℝ) _)),
      intervalIntegral.integral_of_le (by positivity : 0 ≤ (n : ℝ)),
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  -- f is uniformly bounded by the Gamma integrand
  · intro n
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [mem_Ioi, f] at hx ⊢
    rcases lt_or_ge (n : ℝ) x with (hxn | hxn)
    · rw [indicator_of_notMem (notMem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)]
      positivity
    · rw [indicator_of_mem (mem_Ioc.mpr ⟨mem_Ioi.mp hx, hxn⟩), norm_mul, Complex.norm_of_nonneg
          (pow_nonneg (sub_nonneg.mpr <| div_le_one_of_le₀ hxn <| by positivity) _),
          norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
      gcongr
      exact one_sub_div_pow_le_exp_neg hxn

/-- Euler's limit formula for the complex Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℂ) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) := by
  suffices ∀ m : ℕ, -↑m < re s → Tendsto (GammaSeq s) atTop (𝓝 <| GammaAux m s) by
    rw [Gamma]
    apply this
    rw [neg_lt]
    rcases lt_or_ge 0 (re s) with (hs | hs)
    · exact (neg_neg_of_pos hs).trans_le (Nat.cast_nonneg _)
    · refine (Nat.lt_floor_add_one _).trans_le ?_
      rw [sub_eq_neg_add, Nat.floor_add_one (neg_nonneg.mpr hs), Nat.cast_add_one]
  intro m
  induction m generalizing s with intro hs
  | zero => -- Base case: `0 < re s`, so Gamma is given by the integral formula
    rw [Nat.cast_zero, neg_zero] at hs
    rw [← Gamma_eq_GammaAux]
    · refine Tendsto.congr' ?_ (approx_Gamma_integral_tendsto_Gamma_integral hs)
      refine (eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn => ?_)
      exact (GammaSeq_eq_approx_Gamma_integral hs hn).symm
    · rwa [Nat.cast_zero, neg_lt_zero]
  | succ m IH => -- Induction step: use recurrence formulae in `s` for Gamma and GammaSeq
    rw [Nat.cast_succ, neg_add, ← sub_eq_add_neg, sub_lt_iff_lt_add, ← one_re, ← add_re] at hs
    rw [GammaAux]
    have := @Tendsto.congr' _ _ _ ?_ _ _
      ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn => ?_)) ((IH _ hs).div_const s)
    pick_goal 3; · exact GammaSeq_add_one_left s hn -- doesn't work if inlined?
    conv at this => arg 1; intro n; rw [mul_comm]
    rwa [← mul_one (GammaAux m (s + 1) / s), tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this
    simp_rw [add_assoc]
    exact tendsto_natCast_div_add_atTop (1 + s)

end Complex

end LimitFormula

section GammaReflection

/-! ## The reflection formula -/


namespace Complex

theorem GammaSeq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq z n * GammaSeq (1 - z) n =
      n / (n + ↑1 - z) * (↑1 / (z * ∏ j ∈ Finset.range n, (↑1 - z ^ 2 / ((j : ℂ) + 1) ^ 2))) := by
  -- also true for n = 0 but we don't need it
  have aux : ∀ a b c d : ℂ, a * b * (c * d) = a * c * (b * d) := by intros; ring
  rw [GammaSeq, GammaSeq, div_mul_div_comm, aux, ← pow_two]
  have : (n : ℂ) ^ z * (n : ℂ) ^ (1 - z) = n := by
    rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr hn), add_sub_cancel, cpow_one]
  rw [this, Finset.prod_range_succ', Finset.prod_range_succ, aux, ← Finset.prod_mul_distrib,
    Nat.cast_zero, add_zero, add_comm (1 - z) n, ← add_sub_assoc]
  have : ∀ j : ℕ, (z + ↑(j + 1)) * (↑1 - z + ↑j) =
      ((j + 1) ^ 2 :) * (↑1 - z ^ 2 / ((j : ℂ) + 1) ^ 2) := by
    intro j
    push_cast
    have : (j : ℂ) + 1 ≠ 0 := by rw [← Nat.cast_succ, Nat.cast_ne_zero]; exact Nat.succ_ne_zero j
    field
  simp_rw [this]
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, Finset.prod_pow,
    Finset.prod_range_add_one_eq_factorial, Nat.cast_pow,
    (by intros; ring : ∀ a b c d : ℂ, a * b * (c * d) = a * (d * (b * c))), ← div_div,
    mul_div_cancel_right₀, ← div_div, mul_comm z _, mul_one_div]
  exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr <| by positivity)

/-- Euler's reflection formula for the complex Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) := by
  have pi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
  by_cases hs : sin (↑π * z) = 0
  · -- first deal with silly case z = integer
    rw [hs, div_zero]
    rw [← neg_eq_zero, ← Complex.sin_neg, ← mul_neg, Complex.sin_eq_zero_iff, mul_comm] at hs
    obtain ⟨k, hk⟩ := hs
    rw [mul_eq_mul_right_iff, eq_false (ofReal_ne_zero.mpr pi_pos.ne'), or_false,
      neg_eq_iff_eq_neg] at hk
    rw [hk]
    cases k
    · rw [Int.ofNat_eq_natCast, Int.cast_natCast, Complex.Gamma_neg_nat_eq_zero, zero_mul]
    · rw [Int.cast_negSucc, neg_neg, Nat.cast_add, Nat.cast_one, add_comm, sub_add_cancel_left,
        Complex.Gamma_neg_nat_eq_zero, mul_zero]
  refine tendsto_nhds_unique ((GammaSeq_tendsto_Gamma z).mul (GammaSeq_tendsto_Gamma <| 1 - z)) ?_
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)) := by rw [one_mul]
  convert Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn =>
    (GammaSeq_mul z hn).symm)) (Tendsto.mul _ _)
  · convert tendsto_natCast_div_add_atTop (1 - z) using 1; ext1 n; rw [add_sub_assoc]
  · have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π) := by simp
    convert tendsto_const_nhds.div _ (div_ne_zero hs pi_ne)
    rw [← tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne, div_mul_cancel₀ _ pi_ne]
    convert tendsto_euler_sin_prod z using 1
    ext1 n; rw [mul_comm, ← mul_assoc]

/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 := by
  by_cases h_im : s.im = 0
  · have : s = ↑s.re := by
      conv_lhs => rw [← Complex.re_add_im s]
      rw [h_im, ofReal_zero, zero_mul, add_zero]
    rw [this, Gamma_ofReal, ofReal_ne_zero]
    refine Real.Gamma_ne_zero fun n => ?_
    specialize hs n
    contrapose hs
    rwa [this, ← ofReal_natCast, ← ofReal_neg, ofReal_inj]
  · have : sin (↑π * s) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k
      apply_fun im
      rw [im_ofReal_mul, ← ofReal_intCast, ← ofReal_mul, ofReal_im]
      exact mul_ne_zero Real.pi_pos.ne' h_im
    have A := div_ne_zero (ofReal_ne_zero.mpr Real.pi_pos.ne') this
    rw [← Complex.Gamma_mul_Gamma_one_sub s, mul_ne_zero_iff] at A
    exact A.1

theorem Gamma_eq_zero_iff (s : ℂ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m := by
  constructor
  · contrapose!; exact Gamma_ne_zero
  · rintro ⟨m, rfl⟩; exact Gamma_neg_nat_eq_zero m

/-- A weaker, but easier-to-apply, version of `Complex.Gamma_ne_zero`. -/
theorem Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gamma s ≠ 0 := by
  refine Gamma_ne_zero fun m => ?_
  contrapose! hs
  simpa only [hs, neg_re, ← ofReal_natCast, ofReal_re, neg_nonpos] using Nat.cast_nonneg _

end Complex

namespace Real

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def GammaSeq (s : ℝ) (n : ℕ) :=
  (n : ℝ) ^ s * n ! / ∏ j ∈ Finset.range (n + 1), (s + j)

/-- Euler's limit formula for the real Gamma function. -/
theorem GammaSeq_tendsto_Gamma (s : ℝ) : Tendsto (GammaSeq s) atTop (𝓝 <| Gamma s) := by
  suffices Tendsto ((↑) ∘ GammaSeq s : ℕ → ℂ) atTop (𝓝 <| Complex.Gamma s) by
    exact (Complex.continuous_re.tendsto (Complex.Gamma ↑s)).comp this
  convert Complex.GammaSeq_tendsto_Gamma s
  ext1 n
  dsimp only [GammaSeq, Function.comp_apply, Complex.GammaSeq]
  push_cast
  rw [Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_natCast]

/-- Euler's reflection formula for the real Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (s : ℝ) : Gamma s * Gamma (1 - s) = π / sin (π * s) := by
  simp_rw [← Complex.ofReal_inj, Complex.ofReal_div, Complex.ofReal_sin, Complex.ofReal_mul, ←
    Complex.Gamma_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
  exact Complex.Gamma_mul_Gamma_one_sub s

end Real

end GammaReflection

section InvGamma

open scoped Real

namespace Complex

/-! ## The reciprocal Gamma function

We show that the reciprocal Gamma function `1 / Γ(s)` is entire. These lemmas show that (in this
case at least) mathlib's conventions for division by zero do actually give a mathematically useful
answer! (These results are useful in the theory of zeta and L-functions.) -/


/-- A reformulation of the Gamma recurrence relation which is true for `s = 0` as well. -/
theorem one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s : ℂ) :
    (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ := by
  rcases ne_or_eq s 0 with (h | rfl)
  · rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h]
  · rw [zero_add, Gamma_zero, inv_zero, zero_mul]

/-- The reciprocal of the Gamma function is differentiable everywhere
(including the points where Gamma itself is not). -/
theorem differentiable_one_div_Gamma : Differentiable ℂ fun s : ℂ => (Gamma s)⁻¹ := fun s ↦ by
  rcases exists_nat_gt (-s.re) with ⟨n, hs⟩
  induction n generalizing s with
  | zero =>
    rw [Nat.cast_zero, neg_lt_zero] at hs
    suffices ∀ m : ℕ, s ≠ -↑m from (differentiableAt_Gamma _ this).inv (Gamma_ne_zero this)
    rintro m rfl
    apply hs.not_ge
    simp
  | succ n ihn =>
    rw [funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
    specialize ihn (s + 1) (by rwa [add_re, one_re, neg_add', sub_lt_iff_lt_add, ← Nat.cast_succ])
    exact differentiableAt_id.mul (ihn.comp s (f := fun s => s + 1) <|
      differentiableAt_id.add_const (1 : ℂ))

lemma betaIntegral_eq_Gamma_mul_div (u v : ℂ) (hu : 0 < u.re) (hv : 0 < v.re) :
    betaIntegral u v = Gamma u * Gamma v / Gamma (u + v) := by
  rw [Gamma_mul_Gamma_eq_betaIntegral hu hv,
      mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (add_pos hu hv))]

end Complex

end InvGamma

section Doubling

/-!
## The doubling formula for Gamma

We prove the doubling formula for arbitrary real or complex arguments, by analytic continuation from
the positive real case. (Knowing that `Γ⁻¹` is analytic everywhere makes this much simpler, since we
do not have to do any special-case handling for the poles of `Γ`.)
-/


namespace Complex

theorem Gamma_mul_Gamma_add_half (s : ℂ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : ℂ) ^ (1 - 2 * s) * ↑(√π) := by
  suffices (fun z => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) = fun z =>
      (Gamma (2 * z))⁻¹ * (2 : ℂ) ^ (2 * z - 1) / ↑(√π) by
    convert congr_arg Inv.inv (congr_fun this s) using 1
    · rw [mul_inv, inv_inv, inv_inv]
    · rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ← cpow_neg, neg_sub]
  have h1 : AnalyticOnNhd ℂ (fun z : ℂ => (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine (differentiable_one_div_Gamma.mul ?_).differentiableOn
    exact differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have h2 : AnalyticOnNhd ℂ
      (fun z => (Gamma (2 * z))⁻¹ * (2 : ℂ) ^ (2 * z - 1) / ↑(√π)) univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    refine (Differentiable.mul ?_ (differentiable_const _)).differentiableOn
    apply Differentiable.mul
    · exact differentiable_one_div_Gamma.comp (differentiable_id.const_mul _)
    · refine fun t => DifferentiableAt.const_cpow ?_ (Or.inl two_ne_zero)
      exact DifferentiableAt.sub_const (differentiableAt_id.const_mul _) _
  have h3 : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]; constructor
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt
    · exact eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht => ofReal_ne_one.mpr ht)
  refine AnalyticOnNhd.eq_of_frequently_eq h1 h2 (h3.frequently ?_)
  refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
  refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht => ?_)
  rw [← mul_inv, Gamma_ofReal, (by simp : (t : ℂ) + 1 / 2 = ↑(t + 1 / 2)), Gamma_ofReal, ←
    ofReal_mul, Gamma_mul_Gamma_add_half_of_pos ht, ofReal_mul, ofReal_mul, ← Gamma_ofReal,
    mul_inv, mul_inv, (by simp : 2 * (t : ℂ) = ↑(2 * t)), Gamma_ofReal,
    ofReal_cpow zero_le_two, show (2 : ℝ) = (2 : ℂ) by norm_cast, ← cpow_neg, ofReal_sub,
    ofReal_one, neg_sub, ← div_eq_mul_inv]

end Complex

namespace Real

open Complex

theorem Gamma_mul_Gamma_add_half (s : ℝ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * (2 : ℝ) ^ (1 - 2 * s) * √π := by
  rw [← ofReal_inj]
  simpa only [← Gamma_ofReal, ofReal_cpow zero_le_two, ofReal_mul, ofReal_add, ofReal_div,
    ofReal_sub] using Complex.Gamma_mul_Gamma_add_half ↑s

end Real

end Doubling
