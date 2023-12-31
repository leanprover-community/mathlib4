/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjugateExponents

#align_import analysis.mean_inequalities from "leanprover-community/mathlib"@"8f9fea08977f7e450770933ee6abb20733b47c92"

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
Young's inequality, Hölder inequality, and Minkowski inequality. Versions for integrals of some of
these inequalities are available in `MeasureTheory.MeanInequalities`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `Real` namespace, and a version for
`NNReal`-valued functions is in the `NNReal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `Finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `Real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `StrictConvexOn` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/


universe u v

open Finset Classical BigOperators NNReal ENNReal

set_option linter.uppercaseLean3 false

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLEArithMean

/-! ### AM-GM inequality -/


namespace Real

/-- AM-GM inequality: the **geometric mean is less than or equal to the arithmetic mean**, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i in s, z i ^ w i ≤ ∑ i in s, w i * z i := by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
      exact zero_rpow hwi
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  · simp only [not_exists, not_and, Ne.def, Classical.not_not] at A
    have := convexOn_exp.map_sum_le hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, (· ∘ ·), smul_eq_mul, mul_comm (w _) (log _)] at this
    convert this using 1 <;> [apply prod_congr rfl;apply sum_congr rfl] <;> intro i hi
    · cases' eq_or_lt_of_le (hz i hi) with hz hz
      · simp [A i hi hz.symm]
      · exact rpow_def_of_pos hz _
    · cases' eq_or_lt_of_le (hz i hi) with hz hz
      · simp [A i hi hz.symm]
      · rw [exp_log hz]
#align real.geom_mean_le_arith_mean_weighted Real.geom_mean_le_arith_mean_weighted

/-- AM-GM inequality: the **geometric mean is less than or equal to the arithmetic mean**. --/
theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : 0 < ∑ i in s, w i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i in s, z i ^ w i) ^ (∑ i in s, w i)⁻¹  ≤  (∑ i in s, w i * z i) / (∑ i in s, w i) := by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i in s, w i) z ?_ ?_ hz using 2
  · rw [← finset_prod_rpow _ _ (fun i hi => rpow_nonneg_of_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv, rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc, ← Finset.sum_mul, mul_comm]
  · exact fun _ hi => div_nonneg (hw _ hi) (le_of_lt hw')
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel (by linarith)

theorem geom_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i in s, z i ^ w i = x :=
  calc
    ∏ i in s, z i ^ w i = ∏ i in s, x ^ w i := by
      refine' prod_congr rfl fun i hi => _
      rcases eq_or_ne (w i) 0 with h₀ | h₀
      · rw [h₀, rpow_zero, rpow_zero]
      · rw [hx i hi h₀]
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw, hw', rpow_one]
      have : (∑ i in s, w i) ≠ 0 := by
        rw [hw']
        exact one_ne_zero
      obtain ⟨i, his, hi⟩ := exists_ne_zero_of_sum_ne_zero this
      rw [← hx i his hi]
      exact hz i his
#align real.geom_mean_weighted_of_constant Real.geom_mean_weighted_of_constant

theorem arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw' : ∑ i in s, w i = 1)
    (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) : ∑ i in s, w i * z i = x :=
  calc
    ∑ i in s, w i * z i = ∑ i in s, w i * x := by
      refine' sum_congr rfl fun i hi => _
      rcases eq_or_ne (w i) 0 with hwi | hwi
      · rw [hwi, zero_mul, zero_mul]
      · rw [hx i hi hwi]
    _ = x := by rw [← sum_mul, hw', one_mul]
#align real.arith_mean_weighted_of_constant Real.arith_mean_weighted_of_constant

theorem geom_mean_eq_arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i in s, z i ^ w i = ∑ i in s, w i * z i := by
  rw [geom_mean_weighted_of_constant, arith_mean_weighted_of_constant] <;> assumption
#align real.geom_mean_eq_arith_mean_weighted_of_constant Real.geom_mean_eq_arith_mean_weighted_of_constant

end Real

namespace NNReal

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for `NNReal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) :
    (∏ i in s, z i ^ (w i : ℝ)) ≤ ∑ i in s, w i * z i :=
  mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg
#align nnreal.geom_mean_le_arith_mean_weighted NNReal.geom_mean_le_arith_mean_weighted

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for two `NNReal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
    w₁ + w₂ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]
#align nnreal.geom_mean_le_arith_mean2_weighted NNReal.geom_mean_le_arith_mean2_weighted

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
    w₁ + w₂ + w₃ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]
#align nnreal.geom_mean_le_arith_mean3_weighted NNReal.geom_mean_le_arith_mean3_weighted

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
    w₁ + w₂ + w₃ + w₄ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) * p₄ ^ (w₄ : ℝ) ≤
        w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]
#align nnreal.geom_mean_le_arith_mean4_weighted NNReal.geom_mean_le_arith_mean4_weighted

end NNReal

namespace Real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ <|
    NNReal.coe_eq.1 <| by assumption
#align real.geom_mean_le_arith_mean2_weighted Real.geom_mean_le_arith_mean2_weighted

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      ⟨p₃, hp₃⟩ <|
    NNReal.coe_eq.1 hw
#align real.geom_mean_le_arith_mean3_weighted Real.geom_mean_le_arith_mean3_weighted

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
      ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ <|
    NNReal.coe_eq.1 <| by assumption
#align real.geom_mean_le_arith_mean4_weighted Real.geom_mean_le_arith_mean4_weighted

end Real

end GeomMeanLEArithMean

section Young

/-! ### Young's inequality -/


namespace Real

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.IsConjugateExponent q) : a * b ≤ a ^ p / p + b ^ q / q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, _root_.div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.one_div_nonneg hpq.symm.one_div_nonneg
      (rpow_nonneg_of_nonneg ha p) (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj
#align real.young_inequality_of_nonneg Real.young_inequality_of_nonneg

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q :=
  calc
    a * b ≤ |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := (abs_mul a b)
    _ ≤ |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq
#align real.young_inequality Real.young_inequality

end Real

namespace NNReal

/-- Young's inequality, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.  -/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ (p : ℝ) / p + b ^ (q : ℝ) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, NNReal.coe_eq.2 hpq⟩
#align nnreal.young_inequality NNReal.young_inequality

/-- Young's inequality, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    a * b ≤ a ^ p / Real.toNNReal p + b ^ q / Real.toNNReal q := by
  nth_rw 1 [← Real.coe_toNNReal p hpq.nonneg]
  nth_rw 1 [← Real.coe_toNNReal q hpq.symm.nonneg]
  exact young_inequality a b hpq.one_lt_nnreal hpq.inv_add_inv_conj_nnreal
#align nnreal.young_inequality_real NNReal.young_inequality_real

end NNReal

namespace ENNReal

/-- Young's inequality, `ℝ≥0∞` version with real conjugate exponents. -/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    a * b ≤ a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q := by
  by_cases h : a = ⊤ ∨ b = ⊤
  · refine' le_trans le_top (le_of_eq _)
    repeat rw [div_eq_mul_inv]
    cases' h with h h <;> rw [h] <;> simp [h, hpq.pos, hpq.symm.pos]
  push_neg at h
  -- if a ≠ ⊤ and b ≠ ⊤, use the nnreal version: nnreal.young_inequality_real
  rw [← coe_toNNReal h.left, ← coe_toNNReal h.right, ← coe_mul, coe_rpow_of_nonneg _ hpq.nonneg,
    coe_rpow_of_nonneg _ hpq.symm.nonneg, ENNReal.ofReal, ENNReal.ofReal, ←
    @coe_div (Real.toNNReal p) _ (by simp [hpq.pos]), ←
    @coe_div (Real.toNNReal q) _ (by simp [hpq.symm.pos]), ← coe_add, coe_le_coe]
  exact NNReal.young_inequality_real a.toNNReal b.toNNReal hpq
#align ennreal.young_inequality ENNReal.young_inequality

end ENNReal

end Young

section HolderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace NNReal

private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.IsConjugateExponent q) (hf : ∑ i in s, f i ^ p ≤ 1) (hg : ∑ i in s, g i ^ q ≤ 1) :
    ∑ i in s, f i * g i ≤ 1 := by
  have hp_ne_zero : Real.toNNReal p ≠ 0 := (zero_lt_one.trans hpq.one_lt_nnreal).ne.symm
  have hq_ne_zero : Real.toNNReal q ≠ 0 := (zero_lt_one.trans hpq.symm.one_lt_nnreal).ne.symm
  calc
    ∑ i in s, f i * g i ≤ ∑ i in s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i) (g i) hpq
    _ = (∑ i in s, f i ^ p) / Real.toNNReal p + (∑ i in s, g i ^ q) / Real.toNNReal q := by
      rw [sum_add_distrib, sum_div, sum_div]
    _ ≤ 1 / Real.toNNReal p + 1 / Real.toNNReal q := by
      refine' add_le_add _ _
      · rwa [div_le_iff hp_ne_zero, div_mul_cancel _ hp_ne_zero]
      · rwa [div_le_iff hq_ne_zero, div_mul_cancel _ hq_ne_zero]
    _ = 1 := hpq.inv_add_inv_conj_nnreal

private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.IsConjugateExponent q) (hf : ∑ i in s, f i ^ p = 0) :
    ∑ i in s, f i * g i ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne.def, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    ∑ i in s, f i * g i ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  by_cases hF_zero : ∑ i in s, f i ^ p = 0
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hF_zero
  by_cases hG_zero : ∑ i in s, g i ^ q = 0
  · calc
      ∑ i in s, f i * g i = ∑ i in s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ ≤ (∑ i in s, g i ^ q) ^ (1 / q) * (∑ i in s, f i ^ p) ^ (1 / p) :=
        (inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hG_zero)
      _ = (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := mul_comm _ _
  let f' i := f i / (∑ i in s, f i ^ p) ^ (1 / p)
  let g' i := g i / (∑ i in s, g i ^ q) ^ (1 / q)
  suffices (∑ i in s, f' i * g' i) ≤ 1 by
    simp_rw [div_mul_div_comm, ← sum_div] at this
    rwa [div_le_iff, one_mul] at this
    refine' mul_ne_zero _ _
    · rw [Ne.def, rpow_eq_zero_iff, not_and_or]
      exact Or.inl hF_zero
    · rw [Ne.def, rpow_eq_zero_iff, not_and_or]
      exact Or.inl hG_zero
  refine' inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eq _) (le_of_eq _)
  · simp_rw [div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel hpq.ne_zero, rpow_one,
      div_self hF_zero]
  · simp_rw [div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel hpq.symm.ne_zero,
      rpow_one, div_self hG_zero]
#align nnreal.inner_le_Lp_mul_Lq NNReal.inner_le_Lp_mul_Lq

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_hasSum`. -/
theorem inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  have H₁ : ∀ s : Finset ι,
      ∑ i in s, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
    intro s
    refine' le_trans (inner_le_Lp_mul_Lq s f g hpq) (mul_le_mul _ _ bot_le bot_le)
    · rw [NNReal.rpow_le_rpow_iff (one_div_pos.mpr hpq.pos)]
      exact sum_le_tsum _ (fun _ _ => zero_le _) hf
    · rw [NNReal.rpow_le_rpow_iff (one_div_pos.mpr hpq.symm.pos)]
      exact sum_le_tsum _ (fun _ _ => zero_le _) hg
  have bdd : BddAbove (Set.range fun s => ∑ i in s, f i * g i) := by
    refine' ⟨(∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q), _⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  exact ⟨H₂, tsum_le_of_sum_le H₂ H₁⟩
#align nnreal.inner_le_Lp_mul_Lq_tsum NNReal.inner_le_Lp_mul_Lq_tsum

theorem summable_mul_of_Lp_Lq {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (inner_le_Lp_mul_Lq_tsum hpq hf hg).1
#align nnreal.summable_mul_of_Lp_Lq NNReal.summable_mul_of_Lp_Lq

theorem inner_le_Lp_mul_Lq_tsum' {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.IsConjugateExponent q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (inner_le_Lp_mul_Lq_tsum hpq hf hg).2
#align nnreal.inner_le_Lp_mul_Lq_tsum' NNReal.inner_le_Lp_mul_Lq_tsum'

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum`.  -/
theorem inner_le_Lp_mul_Lq_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p q : ℝ}
    (hpq : p.IsConjugateExponent q) (hf : HasSum (fun i => f i ^ p) (A ^ p))
    (hg : HasSum (fun i => g i ^ q) (B ^ q)) : ∃ C, C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  obtain ⟨H₁, H₂⟩ := inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq, rpow_inv_rpow_self hpq.symm.ne_zero]
  refine' ⟨∑' i, f i * g i, _, _⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hpq.ne_zero] using H₁.hasSum
#align nnreal.inner_le_Lp_mul_Lq_has_sum NNReal.inner_le_Lp_mul_Lq_hasSum

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (f : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, f i) ^ p ≤ (card s : ℝ≥0) ^ (p - 1) * ∑ i in s, f i ^ p := by
  cases' eq_or_lt_of_le hp with hp hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.IsConjugateExponent q := by rw [Real.isConjugateExponent_iff hp]
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [NNReal.mul_rpow, ← NNReal.rpow_mul, hp₁, hq, one_mul, one_rpow, rpow_one,
    Pi.one_apply, sum_const, Nat.smul_one_eq_coe] using
    NNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg
#align nnreal.rpow_sum_le_const_mul_sum_rpow NNReal.rpow_sum_le_const_mul_sum_rpow

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i in s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem isGreatest_Lp (f : ι → ℝ≥0) {p q : ℝ} (hpq : p.IsConjugateExponent q) :
    IsGreatest ((fun g : ι → ℝ≥0 => ∑ i in s, f i * g i) '' { g | ∑ i in s, g i ^ q ≤ 1 })
      ((∑ i in s, f i ^ p) ^ (1 / p)) := by
  constructor
  · use fun i => f i ^ p / f i / (∑ i in s, f i ^ p) ^ (1 / q)
    by_cases hf : ∑ i in s, f i ^ p = 0
    · simp [hf, hpq.ne_zero, hpq.symm.ne_zero]
    · have A : p + q - q ≠ 0 := by simp [hpq.ne_zero]
      have B : ∀ y : ℝ≥0, y * y ^ p / y = y ^ p := by
        refine' fun y => mul_div_cancel_left_of_imp fun h => _
        simp [h, hpq.ne_zero]
      simp only [Set.mem_setOf_eq, div_rpow, ← sum_div, ← rpow_mul,
        div_mul_cancel _ hpq.symm.ne_zero, rpow_one, div_le_iff hf, one_mul, hpq.mul_eq_add, ←
        rpow_sub' _ A, _root_.add_sub_cancel, le_refl, true_and_iff, ← mul_div_assoc, B]
      rw [div_eq_iff, ← rpow_add hf, hpq.inv_add_inv_conj, rpow_one]
      simpa [hpq.symm.ne_zero] using hf
  · rintro _ ⟨g, hg, rfl⟩
    apply le_trans (inner_le_Lp_mul_Lq s f g hpq)
    simpa only [mul_one] using
      mul_le_mul_left' (NNReal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) _
#align nnreal.is_greatest_Lp NNReal.isGreatest_Lp

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `NNReal`-valued functions. -/
theorem Lp_add_le (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp);
  · simp [Finset.sum_add_distrib]
  have hpq := Real.isConjugateExponent_conjugateExponent hp
  have := isGreatest_Lp s (f + g) hpq
  simp only [Pi.add_apply, add_mul, sum_add_distrib] at this
  rcases this.1 with ⟨φ, hφ, H⟩
  rw [← H]
  exact
    add_le_add ((isGreatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩) ((isGreatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)
#align nnreal.Lp_add_le NNReal.Lp_add_le

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, convenient if the
infinite sums are already expressed as `p`-th powers, see `Lp_add_le_hasSum_of_nonneg`. -/
theorem Lp_add_le_tsum {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have H₁ : ∀ s : Finset ι,
      (∑ i in s, (f i + g i) ^ p) ≤
        ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p := by
    intro s
    rw [← NNReal.rpow_one_div_le_iff pos]
    refine' le_trans (Lp_add_le s f g hp) (add_le_add _ _) <;>
        rw [NNReal.rpow_le_rpow_iff (one_div_pos.mpr pos)] <;>
      refine' sum_le_tsum _ (fun _ _ => zero_le _) _
    exacts [hf, hg]
  have bdd : BddAbove (Set.range fun s => ∑ i in s, (f i + g i) ^ p) := by
    refine' ⟨((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p, _⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  refine' ⟨H₂, _⟩
  rw [NNReal.rpow_one_div_le_iff pos]
  refine' tsum_le_of_sum_le H₂ H₁
#align nnreal.Lp_add_le_tsum NNReal.Lp_add_le_tsum

theorem summable_Lp_add {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum hp hf hg).1
#align nnreal.summable_Lp_add NNReal.summable_Lp_add

theorem Lp_add_le_tsum' {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum hp hf hg).2
#align nnreal.Lp_add_le_tsum' NNReal.Lp_add_le_tsum'

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, convenient if the
infinite sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`.  -/
theorem Lp_add_le_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p : ℝ} (hp : 1 ≤ p)
    (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  have hp' : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by rw [hg.tsum_eq, rpow_inv_rpow_self hp']
  refine' ⟨(∑' i, (f i + g i) ^ p) ^ (1 / p), _, _⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hp'] using H₁.hasSum
#align nnreal.Lp_add_le_has_sum NNReal.Lp_add_le_hasSum

end NNReal

namespace Real

variable (f g : ι → ℝ) {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : IsConjugateExponent p q) :
    ∑ i in s, f i * g i ≤ (∑ i in s, |f i| ^ p) ^ (1 / p) * (∑ i in s, |g i| ^ q) ^ (1 / q) := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.inner_le_Lp_mul_Lq s (fun i => ⟨_, abs_nonneg (f i)⟩) (fun i => ⟨_, abs_nonneg (g i)⟩)
        hpq)
  push_cast at this
  refine' le_trans (sum_le_sum fun i _ => _) this
  simp only [← abs_mul, le_abs_self]
#align real.inner_le_Lp_mul_Lq Real.inner_le_Lp_mul_Lq

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ`-valued functions. -/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i in s, |f i|) ^ p ≤ (card s : ℝ) ^ (p - 1) * ∑ i in s, |f i| ^ p := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this
#align real.rpow_sum_le_const_mul_sum_rpow Real.rpow_sum_le_const_mul_sum_rpow

-- for some reason `exact_mod_cast` can't replace this argument
/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `Real`-valued functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i in s, |f i + g i| ^ p) ^ (1 / p) ≤
      (∑ i in s, |f i| ^ p) ^ (1 / p) + (∑ i in s, |g i| ^ p) ^ (1 / p) := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.Lp_add_le s (fun i => ⟨_, abs_nonneg (f i)⟩) (fun i => ⟨_, abs_nonneg (g i)⟩) hp)
  push_cast at this
  refine' le_trans (rpow_le_rpow _ (sum_le_sum fun i _ => _) _) this <;>
    simp [sum_nonneg, rpow_nonneg_of_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add,
      rpow_le_rpow]
#align real.Lp_add_le Real.Lp_add_le

variable {f g}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : IsConjugateExponent p q) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i in s, f i * g i ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  convert inner_le_Lp_mul_Lq s f g hpq using 3 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi]
#align real.inner_le_Lp_mul_Lq_of_nonneg Real.inner_le_Lp_mul_Lq_of_nonneg

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `ℝ`-valued functions.
For an alternative version, convenient if the infinite sums are already expressed as `p`-th powers,
see `inner_le_Lp_mul_Lq_hasSum_of_nonneg`. -/
theorem inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.IsConjugateExponent q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  -- After leanprover/lean4#2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at *
  exact NNReal.inner_le_Lp_mul_Lq_tsum hpq hf_sum hg_sum
#align real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.inner_le_Lp_mul_Lq_tsum_of_nonneg

theorem summable_mul_of_Lp_Lq_of_nonneg (hpq : p.IsConjugateExponent q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1
#align real.summable_mul_of_Lp_Lq_of_nonneg Real.summable_mul_of_Lp_Lq_of_nonneg

theorem inner_le_Lp_mul_Lq_tsum_of_nonneg' (hpq : p.IsConjugateExponent q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2
#align real.inner_le_Lp_mul_Lq_tsum_of_nonneg' Real.inner_le_Lp_mul_Lq_tsum_of_nonneg'

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum_of_nonneg`.  -/
theorem inner_le_Lp_mul_Lq_hasSum_of_nonneg (hpq : p.IsConjugateExponent q) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : HasSum (fun i => f i ^ p) (A ^ p)) (hg_sum : HasSum (fun i => g i ^ q) (B ^ q)) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  -- After leanprover/lean4#2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ := NNReal.inner_le_Lp_mul_Lq_hasSum hpq hf_sum hg_sum
  refine' ⟨C, C.prop, hC, _⟩
  norm_cast
#align real.inner_le_Lp_mul_Lq_has_sum_of_nonneg Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with nonnegative `ℝ`-valued
functions. -/
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i in s, f i) ^ p ≤ (card s : ℝ) ^ (p - 1) * ∑ i in s, f i ^ p := by
  convert rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi]
#align real.rpow_sum_le_const_mul_sum_rpow_of_nonneg Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  convert Lp_add_le s f g hp using 2 <;> [skip;congr 1;congr 1] <;> apply sum_congr rfl <;>
      intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]
#align real.Lp_add_le_of_nonneg Real.Lp_add_le_of_nonneg

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are already expressed as `p`-th powers, see `Lp_add_le_hasSum_of_nonneg`. -/
theorem Lp_add_le_tsum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (Summable fun i => (f i + g i) ^ p) ∧
      (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤
        (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  -- After leanprover/lean4#2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast0 at *
  exact NNReal.Lp_add_le_tsum hp hf_sum hg_sum
#align real.Lp_add_le_tsum_of_nonneg Real.Lp_add_le_tsum_of_nonneg

theorem summable_Lp_add_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1
#align real.summable_Lp_add_of_nonneg Real.summable_Lp_add_of_nonneg

theorem Lp_add_le_tsum_of_nonneg' (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2
#align real.Lp_add_le_tsum_of_nonneg' Real.Lp_add_le_tsum_of_nonneg'

/-- Minkowski inequality: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `ℝ`-valued functions. For an alternative version, convenient if the infinite
sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
theorem Lp_add_le_hasSum_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hfA : HasSum (fun i => f i ^ p) (A ^ p))
    (hgB : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, 0 ≤ C ∧ C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  -- After leanprover/lean4#2734, `norm_cast` needs help with beta reduction.
  beta_reduce at hfA hgB
  norm_cast at hfA hgB
  obtain ⟨C, hC₁, hC₂⟩ := NNReal.Lp_add_le_hasSum hp hfA hgB
  use C
  -- After leanprover/lean4#2734, `norm_cast` needs help with beta reduction.
  beta_reduce
  norm_cast
  exact ⟨zero_le _, hC₁, hC₂⟩
#align real.Lp_add_le_has_sum_of_nonneg Real.Lp_add_le_hasSum_of_nonneg

end Real

namespace ENNReal

variable (f g : ι → ℝ≥0∞) {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : p.IsConjugateExponent q) :
    ∑ i in s, f i * g i ≤ (∑ i in s, f i ^ p) ^ (1 / p) * (∑ i in s, g i ^ q) ^ (1 / q) := by
  by_cases H : (∑ i in s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i in s, g i ^ q) ^ (1 / q) = 0
  · replace H : (∀ i ∈ s, f i = 0) ∨ ∀ i ∈ s, g i = 0
    · simpa [ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
        sum_eq_zero_iff_of_nonneg] using H
    have : ∀ i ∈ s, f i * g i = 0 := fun i hi => by cases' H with H H <;> simp [H i hi]
    have : ∑ i in s, f i * g i = ∑ i in s, 0 := sum_congr rfl this
    simp [this]
  push_neg at H
  by_cases H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ q) ^ (1 / q) = ⊤
  · cases' H' with H' H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ s, g i ≠ ⊤
  · simpa [ENNReal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
      ENNReal.sum_eq_top_iff, not_or] using H'
  have :=
    ENNReal.coe_le_coe.2
      (@NNReal.inner_le_Lp_mul_Lq _ s (fun i => ENNReal.toNNReal (f i))
        (fun i => ENNReal.toNNReal (g i)) _ _ hpq)
  simp [← ENNReal.coe_rpow_of_nonneg, le_of_lt hpq.pos, le_of_lt hpq.one_div_pos,
    le_of_lt hpq.symm.pos, le_of_lt hpq.symm.one_div_pos] at this
  convert this using 1 <;> [skip; congr 2] <;> [skip; skip; simp; skip; simp] <;>
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [H'.1 i hi, H'.2 i hi, -WithZero.coe_mul, WithTop.coe_mul.symm]
#align ennreal.inner_le_Lp_mul_Lq ENNReal.inner_le_Lp_mul_Lq

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0∞`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i in s, f i) ^ p ≤ (card s : ℝ≥0∞) ^ (p - 1) * ∑ i in s, f i ^ p := by
  cases' eq_or_lt_of_le hp with hp hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.IsConjugateExponent q := by rw [Real.isConjugateExponent_iff hp]
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul, hp₁, hq, coe_one,
    one_mul, one_rpow, rpow_one, Pi.one_apply, sum_const, Nat.smul_one_eq_coe] using
    ENNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg
#align ennreal.rpow_sum_le_const_mul_sum_rpow ENNReal.rpow_sum_le_const_mul_sum_rpow

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞` valued nonnegative
functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i in s, f i ^ p) ^ (1 / p) + (∑ i in s, g i ^ p) ^ (1 / p) := by
  by_cases H' : (∑ i in s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i in s, g i ^ p) ^ (1 / p) = ⊤
  · cases' H' with H' H' <;> simp [H', -one_div]
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ s, g i ≠ ⊤
  · simpa [ENNReal.rpow_eq_top_iff, asymm pos, pos, ENNReal.sum_eq_top_iff, not_or] using H'
  have :=
    ENNReal.coe_le_coe.2
      (@NNReal.Lp_add_le _ s (fun i => ENNReal.toNNReal (f i)) (fun i => ENNReal.toNNReal (g i)) _
        hp)
  push_cast [← ENNReal.coe_rpow_of_nonneg, le_of_lt pos, le_of_lt (one_div_pos.2 pos)] at this
  convert this using 2 <;> [skip; congr 1; congr 1] <;>
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [H'.1 i hi, H'.2 i hi]
#align ennreal.Lp_add_le ENNReal.Lp_add_le

end ENNReal

end HolderMinkowski
