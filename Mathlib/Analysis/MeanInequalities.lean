/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne, Jireh Loreaux
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Real.ConjExponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
HM-GM inequality, Young's inequality, Hölder inequality, and Minkowski inequality. Versions for
integrals of some of these inequalities are available in
`Mathlib/MeasureTheory/Integral/MeanInequalities.lean`.

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


### HM-GM inequality:

The inequality says that the harmonic mean of a tuple of positive numbers is less than or equal
to their geometric mean. We prove the weighted version of this inequality: if $w$ and $z$
are two positive vectors and $\sum_{i\in s} w_i=1$, then
$$
1/(\sum_{i\in s} w_i/z_i) ≤ \prod_{i\in s} z_i^{w_i}
$$
The classical version is proven as a special case of this inequality for $w_i=\frac{1}{n}$.

The inequalities are proven only for real-valued positive functions on `Finset`s, and namespaced in
`Real`. The weighted version follows as a corollary of the weighted AM-GM inequality.

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

public section


universe u v

open Finset NNReal ENNReal
open scoped BigOperators

noncomputable section

variable {ι : Type u} (s : Finset ι)

section GeomMeanLEArithMean

/-! ### AM-GM inequality -/


namespace Real

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases! A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · exact sum_nonneg fun j hj => mul_nonneg (hw j hj) (hz j hj)
    · rw [hzi]
      exact zero_rpow hwi
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  · have := convexOn_exp.map_sum_le hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert this using 1 <;> [apply prod_congr rfl; apply sum_congr rfl] <;> intro i hi
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · exact rpow_def_of_pos hz _
    · rcases eq_or_lt_of_le (hz i hi) with hz | hz
      · simp [A i hi hz.symm]
      · rw [exp_log hz]

/-- **AM-GM inequality**: The **geometric mean is less than or equal to the arithmetic mean. -/
theorem geom_mean_le_arith_mean {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / (∑ i ∈ s, w i) := by
  convert geom_mean_le_arith_mean_weighted s (fun i => (w i) / ∑ i ∈ s, w i) z ?_ ?_ hz using 2
  · rw [← finset_prod_rpow _ _ (fun i hi => rpow_nonneg (hz _ hi) _) _]
    refine Finset.prod_congr rfl (fun _ ih => ?_)
    rw [div_eq_mul_inv, rpow_mul (hz _ ih)]
  · simp_rw [div_eq_mul_inv, mul_assoc, mul_comm, ← mul_assoc, ← Finset.sum_mul, mul_comm]
  · exact fun _ hi => div_nonneg (hw _ hi) (le_of_lt hw')
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (by linarith)

theorem geom_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i ∈ s, z i ^ w i = x :=
  calc
    ∏ i ∈ s, z i ^ w i = ∏ i ∈ s, x ^ w i := by
      refine prod_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with h₀ | h₀
      · rw [h₀, rpow_zero, rpow_zero]
      · rw [hx i hi h₀]
    _ = x := by
      rw [← rpow_sum_of_nonneg _ hw, hw', rpow_one]
      have : (∑ i ∈ s, w i) ≠ 0 := by
        rw [hw']
        exact one_ne_zero
      obtain ⟨i, his, hi⟩ := exists_ne_zero_of_sum_ne_zero this
      rw [← hx i his hi]
      exact hz i his

theorem arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) : ∑ i ∈ s, w i * z i = x :=
  calc
    ∑ i ∈ s, w i * z i = ∑ i ∈ s, w i * x := by
      refine sum_congr rfl fun i hi => ?_
      rcases eq_or_ne (w i) 0 with hwi | hwi
      · rw [hwi, zero_mul, zero_mul]
      · rw [hx i hi hwi]
    _ = x := by rw [← sum_mul, hw', one_mul]

theorem geom_mean_eq_arith_mean_weighted_of_constant (w z : ι → ℝ) (x : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (hx : ∀ i ∈ s, w i ≠ 0 → z i = x) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i := by
  rw [geom_mean_weighted_of_constant, arith_mean_weighted_of_constant] <;> assumption

/-- **AM-GM inequality - equality condition**: This theorem provides the equality condition for the
*positive* weighted version of the AM-GM inequality for real-valued nonnegative functions. -/
theorem geom_mean_eq_arith_mean_weighted_iff' (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, z j = ∑ i ∈ s, w i * z i := by
  by_cases! A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0
  · rcases A with ⟨i, his, hzi, hwi⟩
    rw [prod_eq_zero his]
    · constructor
      · intro h
        rw [← h]
        intro j hj
        apply eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_lt (hw j hj)).symm
        apply (sum_eq_zero_iff_of_nonneg ?_).mp h.symm j hj
        exact fun i hi => (mul_nonneg_iff_of_pos_left (hw i hi)).mpr (hz i hi)
      · intro h
        convert h i his
        exact hzi.symm
    · rw [hzi]
      exact zero_rpow hwi
  · have hz' := fun i h => lt_of_le_of_ne (hz i h) (fun a => (ne_of_gt (hw i h)) (A i h a.symm))
    have := strictConvexOn_exp.map_sum_eq_iff hw hw' fun i _ => Set.mem_univ <| log (z i)
    simp only [exp_sum, smul_eq_mul, mul_comm (w _) (log _)] at this
    convert this using 1
    · apply Eq.congr <;>
      [apply prod_congr rfl; apply sum_congr rfl] <;>
      intro i hi <;>
      simp only [exp_mul, exp_log (hz' i hi)]
    · constructor <;> intro h j hj
      · rw [← arith_mean_weighted_of_constant s w _ (log (z j)) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [mul_comm, h j hj, h x hx]
      · rw [← arith_mean_weighted_of_constant s w _ (z j) hw' fun i _ => congrFun rfl]
        apply sum_congr rfl
        intro x hx
        simp only [log_injOn_pos (hz' j hj) (hz' x hx), h j hj, h x hx]

/-- **AM-GM inequality - equality condition**: This theorem provides the equality condition for the
weighted version of the AM-GM inequality for real-valued nonnegative functions. -/
theorem geom_mean_eq_arith_mean_weighted_iff (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i = ∑ i ∈ s, w i * z i ↔ ∀ j ∈ s, w j ≠ 0 → z j = ∑ i ∈ s, w i * z i := by
  have h (i) (_ : i ∈ s) : w i * z i ≠ 0 → w i ≠ 0 := by apply left_ne_zero_of_mul
  have h' (i) (_ : i ∈ s) : z i ^ w i ≠ 1 → w i ≠ 0 := by
    by_contra! ⟨h1, h2⟩
    simp only [h2, rpow_zero, ne_self_iff_false] at h1
  rw [← sum_filter_of_ne h, ← prod_filter_of_ne h', geom_mean_eq_arith_mean_weighted_iff']
  · simp
  · simp +contextual [(hw _ _).lt_iff_ne']
  · rwa [sum_filter_ne_zero]
  · simp_all only [ne_eq, mul_eq_zero, not_or, not_false_eq_true, implies_true, mem_filter]

/-- **AM-GM inequality - strict inequality condition**: This theorem provides the strict inequality
condition for the *positive* weighted version of the AM-GM inequality for real-valued nonnegative
functions. -/
theorem geom_mean_lt_arith_mean_weighted_iff_of_pos (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ^ w i < ∑ i ∈ s, w i * z i ↔ ∃ j ∈ s, ∃ k ∈ s, z j ≠ z k := by
  constructor
  · intro h
    by_contra! h_contra
    rw [(geom_mean_eq_arith_mean_weighted_iff' s w z hw hw' hz).mpr ?_] at h
    · exact (lt_self_iff_false _).mp h
    · intro j hjs
      rw [← arith_mean_weighted_of_constant s w (fun _ => z j) (z j) hw' fun _ _ => congrFun rfl]
      apply sum_congr rfl (fun x a => congrArg (HMul.hMul (w x)) (h_contra j hjs x a))
  · rintro ⟨j, hjs, k, hks, hzjk⟩
    have := geom_mean_le_arith_mean_weighted s w z (fun i a => le_of_lt (hw i a)) hw' hz
    by_contra! h
    apply le_antisymm this at h
    apply (geom_mean_eq_arith_mean_weighted_iff' s w z hw hw' hz).mp at h
    simp only [h j hjs, h k hks, ne_eq, not_true_eq_false] at hzjk

end Real

namespace NNReal

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for `NNReal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i ∈ s, w i = 1) :
    (∏ i ∈ s, z i ^ (w i : ℝ)) ≤ ∑ i ∈ s, w i * z i :=
  mod_cast
    Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ => (w i).coe_nonneg)
      (by assumption_mod_cast) fun i _ => (z i).coe_nonneg

/-- **AM-GM inequality**: The geometric mean is less than or equal to the arithmetic mean, weighted
version for two `NNReal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
    w₁ + w₂ = 1 → p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one] using
    geom_mean_le_arith_mean_weighted univ ![w₁, w₂] ![p₁, p₂]

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
    w₁ + w₂ + w₃ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃] ![p₁, p₂, p₃]

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
    w₁ + w₂ + w₃ + w₄ = 1 →
      p₁ ^ (w₁ : ℝ) * p₂ ^ (w₂ : ℝ) * p₃ ^ (w₃ : ℝ) * p₄ ^ (w₄ : ℝ) ≤
        w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ := by
  simpa only [Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero, add_zero, mul_one, ← add_assoc,
    mul_assoc] using geom_mean_le_arith_mean_weighted univ ![w₁, w₂, w₃, w₄] ![p₁, p₂, p₃, p₄]

end NNReal

namespace Real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) : p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
  NNReal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ <|
    NNReal.coe_inj.1 <| by assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
  NNReal.geom_mean_le_arith_mean3_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩
      ⟨p₃, hp₃⟩ <|
    NNReal.coe_inj.1 hw

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
    p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
  NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩
      ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ <|
    NNReal.coe_inj.1 <| by assumption

end Real

end GeomMeanLEArithMean

section HarmMeanLEGeomMean

/-! ### HM-GM inequality -/

namespace Real

/-- **HM-GM inequality**: The harmonic mean is less than or equal to the geometric mean, weighted
version for real-valued nonnegative functions. -/
theorem harm_mean_le_geom_mean_weighted (w z : ι → ℝ) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i / z i)⁻¹ ≤ ∏ i ∈ s, z i ^ w i := by
  have : ∏ i ∈ s, (1 / z) i ^ w i ≤ ∑ i ∈ s, w i * (1 / z) i :=
    geom_mean_le_arith_mean_weighted s w (1 / z) (fun i hi ↦ le_of_lt (hw i hi)) hw'
    (fun i hi ↦ one_div_nonneg.2 (le_of_lt (hz i hi)))
  have p_pos : 0 < ∏ i ∈ s, (z i)⁻¹ ^ w i :=
    prod_pos fun i hi => rpow_pos_of_pos (inv_pos.2 (hz i hi)) _
  have s_pos : 0 < ∑ i ∈ s, w i * (z i)⁻¹ :=
    sum_pos (fun i hi => mul_pos (hw i hi) (inv_pos.2 (hz i hi))) hs
  norm_num at this
  rw [← inv_le_inv₀ s_pos p_pos] at this
  apply le_trans this
  have p_pos₂ : 0 < (∏ i ∈ s, (z i) ^ w i)⁻¹ :=
    inv_pos.2 (prod_pos fun i hi => rpow_pos_of_pos ((hz i hi)) _)
  rw [← inv_inv (∏ i ∈ s, z i ^ w i), inv_le_inv₀ p_pos p_pos₂, ← Finset.prod_inv_distrib]
  gcongr
  · exact fun i hi ↦ inv_nonneg.mpr (Real.rpow_nonneg (le_of_lt (hz i hi)) _)
  · rw [Real.inv_rpow]; apply fun i hi ↦ le_of_lt (hz i hi); assumption


/-- **HM-GM inequality**: The **harmonic mean is less than or equal to the geometric mean. -/
theorem harm_mean_le_geom_mean {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (z : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) (hw' : 0 < ∑ i ∈ s, w i) (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i) / (∑ i ∈ s, w i / z i) ≤ (∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ := by
  have := harm_mean_le_geom_mean_weighted s (fun i => (w i) / ∑ i ∈ s, w i) z hs ?_ ?_ hz
  · simp only at this
    set n := ∑ i ∈ s, w i
    nth_rw 1 [div_eq_mul_inv, (show n = (n⁻¹)⁻¹ by simp), ← mul_inv, Finset.mul_sum _ _ n⁻¹]
    simp_rw [inv_mul_eq_div n ((w _) / (z _)), div_right_comm _ _ n]
    convert this
    rw [← Real.finset_prod_rpow s _ (fun i hi ↦ Real.rpow_nonneg (le_of_lt <| hz i hi) _)]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [← Real.rpow_mul (le_of_lt <| hz i hi) (w _) n⁻¹, div_eq_mul_inv (w _) n]
  · exact fun i hi ↦ div_pos (hw i hi) hw'
  · simp_rw [div_eq_mul_inv (w _) (∑ i ∈ s, w i), ← Finset.sum_mul _ _ (∑ i ∈ s, w i)⁻¹]
    exact mul_inv_cancel₀ hw'.ne'

end Real

end HarmMeanLEGeomMean


section Young

/-! ### Young's inequality -/


namespace Real

/-- **Young's inequality**, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpq : p.HolderConjugate q) : a * b ≤ a ^ p / p + b ^ q / q := by
  simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, _root_.div_eq_inv_mul] using
    geom_mean_le_arith_mean2_weighted hpq.inv_nonneg hpq.symm.inv_nonneg
      (rpow_nonneg ha p) (rpow_nonneg hb q) hpq.inv_add_inv_eq_one

/-- **Young's inequality**, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q :=
  calc
    a * b ≤ |a * b| := le_abs_self (a * b)
    _ = |a| * |b| := abs_mul a b
    _ ≤ |a| ^ p / p + |b| ^ q / q :=
      Real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

end Real

namespace NNReal

/-- **Young's inequality**, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators. -/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ (p : ℝ) / p + b ^ (q : ℝ) / q :=
  Real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg hpq.coe

/-- **Young's inequality**, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / Real.toNNReal p + b ^ q / Real.toNNReal q := by
  simpa [Real.coe_toNNReal, hpq.nonneg, hpq.symm.nonneg] using young_inequality a b hpq.toNNReal

end NNReal

namespace ENNReal

/-- **Young's inequality**, `ℝ≥0∞` version with real conjugate exponents. -/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ a ^ p / ENNReal.ofReal p + b ^ q / ENNReal.ofReal q := by
  by_cases! h : a = ⊤ ∨ b = ⊤
  · refine le_trans le_top (le_of_eq ?_)
    repeat rw [div_eq_mul_inv]
    rcases h with h | h <;> rw [h] <;> simp [hpq.pos, hpq.symm.pos]
  -- if a ≠ ⊤ and b ≠ ⊤, use the nnreal version: nnreal.young_inequality_real
  rw [← coe_toNNReal h.left, ← coe_toNNReal h.right, ← coe_mul, ← coe_rpow_of_nonneg _ hpq.nonneg,
    ← coe_rpow_of_nonneg _ hpq.symm.nonneg, ENNReal.ofReal, ENNReal.ofReal, ←
    @coe_div (Real.toNNReal p) _ (by simp [hpq.pos]), ←
    @coe_div (Real.toNNReal q) _ (by simp [hpq.symm.pos]), ← coe_add, coe_le_coe]
  exact NNReal.young_inequality_real a.toNNReal b.toNNReal hpq

end ENNReal

end Young

section HoelderMinkowski

/-! ### Hölder's and Minkowski's inequalities -/


namespace NNReal

private theorem inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p ≤ 1) (hg : ∑ i ∈ s, g i ^ q ≤ 1) :
    ∑ i ∈ s, f i * g i ≤ 1 := by
  have hp : 0 < p.toNNReal := zero_lt_one.trans hpq.toNNReal.lt
  have hq : 0 < q.toNNReal := zero_lt_one.trans hpq.toNNReal.symm.lt
  calc
    ∑ i ∈ s, f i * g i ≤ ∑ i ∈ s, (f i ^ p / Real.toNNReal p + g i ^ q / Real.toNNReal q) :=
      Finset.sum_le_sum fun i _ => young_inequality_real (f i) (g i) hpq
    _ = (∑ i ∈ s, f i ^ p) / Real.toNNReal p + (∑ i ∈ s, g i ^ q) / Real.toNNReal q := by
      rw [sum_add_distrib, sum_div, sum_div]
    _ ≤ 1 / Real.toNNReal p + 1 / Real.toNNReal q := by
      refine add_le_add ?_ ?_ <;> rwa [div_le_iff₀, div_mul_cancel₀] <;> positivity
    _ = 1 := by simp_rw [one_div, hpq.toNNReal.inv_add_inv_eq_one]

private theorem inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι → ℝ≥0) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : ∑ i ∈ s, f i ^ p = 0) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul,
    inv_eq_zero, Ne, not_false_iff, le_zero_iff, mul_eq_zero]
  intro i his
  left
  rw [sum_eq_zero_iff] at hf
  exact (rpow_eq_zero_iff.mp (hf i his)).left

set_option backward.isDefEq.respectTransparency false in
/-- **Hölder inequality**: The scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  obtain hf | hf := eq_zero_or_pos (∑ i ∈ s, f i ^ p)
  · exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hf
  obtain hg | hg := eq_zero_or_pos (∑ i ∈ s, g i ^ q)
  · calc
      ∑ i ∈ s, f i * g i = ∑ i ∈ s, g i * f i := by
        congr with i
        rw [mul_comm]
      _ ≤ (∑ i ∈ s, g i ^ q) ^ (1 / q) * (∑ i ∈ s, f i ^ p) ^ (1 / p) :=
        (inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hg)
      _ = (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := mul_comm _ _
  let f' i := f i / (∑ i ∈ s, f i ^ p) ^ (1 / p)
  let g' i := g i / (∑ i ∈ s, g i ^ q) ^ (1 / q)
  suffices (∑ i ∈ s, f' i * g' i) ≤ 1 by
    simp_rw [f', g', div_mul_div_comm, ← sum_div] at this
    rwa [div_le_iff₀, one_mul] at this
    positivity
  refine inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eq ?_) (le_of_eq ?_)
  · simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.ne_zero, rpow_one,
      div_self hf.ne']
  · simp_rw [g', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel₀ hpq.symm.ne_zero,
      rpow_one, div_self hg.ne']

/-- **Hölder inequality**: The (`r`-power of the) `L^r` norm of two functions is bounded by the
product of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q`, and `r` form a
`Real.HolderTriple`. -/
theorem Lr_rpow_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
  have := hpqr.holderConjugate_div_div
  have hp := hpqr.pos
  have hq := hpqr.symm.pos
  have hr := hpqr.pos'
  calc ∑ i ∈ s, (f i * g i) ^ r
    _ = ∑ i ∈ s, (f i) ^ r * (g i) ^ r := s.sum_congr rfl fun i hi ↦ mul_rpow ..
    _ ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
      apply inner_le_Lp_mul_Lq s _ _ this |>.trans_eq
      congr! 2
      all_goals try simp only [fieldEq]
      all_goals
        refine s.sum_congr rfl fun i hi ↦ by simp [← rpow_mul, ← mul_div_assoc, hr.ne']

/-- **Hölder inequality**: The `L^r` norm of two functions is bounded by the
product of their `L^p` and `L^q` norms when `p`, `q`, and `r` form a `Real.HolderTriple`. -/
theorem Lr_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q r : ℝ} (hpqr : p.HolderTriple q r) :
    (∑ i ∈ s, (f i * g i) ^ r) ^ (1 / r) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  convert rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos' : 0 < 1 / r) |>.mpr <|
    Lr_rpow_le_Lp_mul_Lq s f g hpqr using 1
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

set_option backward.isDefEq.respectTransparency false in
/-- **Weighted Hölder inequality**. -/
lemma inner_le_weight_mul_Lp (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  calc
    _ = ∑ i ∈ s, w i ^ (1 - p⁻¹) * (w i ^ p⁻¹ * f i) := ?_
    _ ≤ (∑ i ∈ s, (w i ^ (1 - p⁻¹)) ^ (1 - p⁻¹)⁻¹) ^ (1 / (1 - p⁻¹)⁻¹) *
          (∑ i ∈ s, (w i ^ p⁻¹ * f i) ^ p) ^ (1 / p) :=
        inner_le_Lp_mul_Lq _ _ _ (.symm <| Real.holderConjugate_iff.mpr ⟨hp, by simp⟩)
    _ = _ := ?_
  · congr with i
    rw [← mul_assoc, ← rpow_of_add_eq _ one_ne_zero, rpow_one]
    simp
  · have hp₀ : p ≠ 0 := by positivity
    have hp₁ : 1 - p⁻¹ ≠ 0 := by simp [sub_eq_zero, hp.ne']
    simp [mul_rpow, div_inv_eq_mul, one_mul, one_div, hp₀, hp₁]

/-- **Hölder inequality**: The (`r`-power of the) `L^r` norm of two functions is bounded by the
product of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q`, and `r` form a
`Real.HolderTriple`. A version for `NNReal`-valued functions. For an alternative version,
convenient if the infinite sums are already expressed as powers, see `inner_le_Lp_mul_Lq_hasSum`. -/
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  have H₁ : ∀ s : Finset ι,
      ∑ i ∈ s, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
    intro s
    obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
    refine le_trans (Lr_rpow_le_Lp_mul_Lq s f g hpqr) (mul_le_mul ?_ ?_ bot_le bot_le)
    · rw [NNReal.rpow_le_rpow_iff (by positivity)]
      exact hf.sum_le_tsum _ (fun _ _ => zero_le _)
    · rw [NNReal.rpow_le_rpow_iff (by positivity)]
      exact hg.sum_le_tsum _ (fun _ _ => zero_le _)
  have bdd : BddAbove (Set.range fun s => ∑ i ∈ s, (f i * g i) ^ r) := by
    refine ⟨(∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q), ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  exact ⟨H₂, H₂.tsum_le_of_sum_le H₁⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_hasSum`. -/
theorem summable_and_inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpq hf hg

theorem summable_mul_rpow_of_Lp_Lq {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).1

theorem summable_mul_of_Lp_Lq {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).1

theorem Lr_rpow_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg).2

theorem Lr_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q r : ℝ} (hpqr : p.HolderTriple q r)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  convert rpow_le_rpow_iff (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos') |>.mpr <|
    Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf hg
  have hr := hpqr.pos'.ne'
  simp only [← rpow_mul, mul_rpow]
  field_simp

theorem inner_le_Lp_mul_Lq_tsum {f g : ι → ℝ≥0} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : Summable fun i => f i ^ p) (hg : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum hpq hf hg).2

@[deprecated (since := "2026-02-12")] alias inner_le_Lp_mul_Lq_tsum' := inner_le_Lp_mul_Lq_tsum

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum`. -/
theorem inner_le_Lp_mul_Lq_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : HasSum (fun i => f i ^ p) (A ^ p))
    (hg : HasSum (fun i => g i ^ q) (B ^ q)) : ∃ C, C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  obtain ⟨H₁, H₂⟩ := summable_and_inner_le_Lp_mul_Lq_tsum hpq hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hpq.ne_zero]
  have hB : B = (∑' i : ι, g i ^ q) ^ (1 / q) := by
    rw [hg.tsum_eq, rpow_inv_rpow_self hpq.symm.ne_zero]
  refine ⟨∑' i, f i * g i, ?_, ?_⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hpq.ne_zero] using H₁.hasSum

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (f : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (#s : ℝ≥0) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [NNReal.mul_rpow, ← NNReal.rpow_mul, hp₁, hq, one_mul, one_rpow, rpow_one,
    Pi.one_apply, sum_const, Nat.smul_one_eq_cast] using
    NNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i ∈ s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem isGreatest_Lp (f : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest ((fun g : ι → ℝ≥0 => ∑ i ∈ s, f i * g i) '' { g | ∑ i ∈ s, g i ^ q ≤ 1 })
      ((∑ i ∈ s, f i ^ p) ^ (1 / p)) := by
  constructor
  · use fun i => f i ^ p / f i / (∑ i ∈ s, f i ^ p) ^ (1 / q)
    obtain hf | hf := eq_zero_or_pos (∑ i ∈ s, f i ^ p)
    · simp [hf, hpq.ne_zero, hpq.symm.ne_zero]
    · have A : p + q - q ≠ 0 := by simp [hpq.ne_zero]
      have B : ∀ y : ℝ≥0, y * y ^ p / y = y ^ p := by
        refine fun y => mul_div_cancel_left_of_imp fun h => ?_
        simp [h, hpq.ne_zero]
      simp only [Set.mem_setOf_eq, div_rpow, ← sum_div, ← rpow_mul,
        div_mul_cancel₀ _ hpq.symm.ne_zero, rpow_one, div_le_iff₀ hf, one_mul, hpq.mul_eq_add, ←
        rpow_sub' A, add_sub_cancel_right, le_refl, true_and, ← mul_div_assoc, B]
      rw [div_eq_iff, ← rpow_add hf.ne', one_div, one_div, hpq.inv_add_inv_eq_one, rpow_one]
      simpa [hpq.symm.ne_zero] using hf.ne'
  · rintro _ ⟨g, hg, rfl⟩
    apply le_trans (inner_le_Lp_mul_Lq s f g hpq)
    simpa only [mul_one] using
      mul_le_mul_right (NNReal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) _

/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `NNReal`-valued functions. -/
theorem Lp_add_le (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with (rfl | hp)
  · simp [Finset.sum_add_distrib]
  have hpq := Real.HolderConjugate.conjExponent hp
  have := isGreatest_Lp s (f + g) hpq
  simp only [Pi.add_apply, add_mul, sum_add_distrib] at this
  rcases this.1 with ⟨φ, hφ, H⟩
  rw [← H]
  exact
    add_le_add ((isGreatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩) ((isGreatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
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
      (∑ i ∈ s, (f i + g i) ^ p) ≤
        ((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p := by
    intro s
    rw [one_div, ← NNReal.rpow_inv_le_iff pos, ← one_div]
    refine le_trans (Lp_add_le s f g hp) (add_le_add ?_ ?_) <;>
        rw [NNReal.rpow_le_rpow_iff (one_div_pos.mpr pos)] <;>
      refine Summable.sum_le_tsum _ (fun _ _ => zero_le _) ?_
    exacts [hf, hg]
  have bdd : BddAbove (Set.range fun s => ∑ i ∈ s, (f i + g i) ^ p) := by
    refine ⟨((∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p)) ^ p, ?_⟩
    rintro a ⟨s, rfl⟩
    exact H₁ s
  have H₂ : Summable _ := (hasSum_of_isLUB _ (isLUB_ciSup bdd)).summable
  refine ⟨H₂, ?_⟩
  rw [one_div, NNReal.rpow_inv_le_iff pos, ← one_div]
  exact H₂.tsum_le_of_sum_le H₁

theorem summable_Lp_add {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) : Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum hp hf hg).1

theorem Lp_add_le_tsum' {f g : ι → ℝ≥0} {p : ℝ} (hp : 1 ≤ p) (hf : Summable fun i => f i ^ p)
    (hg : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum hp hf hg).2

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
equal to the infinite sum of the `L_p`-seminorms of the summands, if these infinite sums both
exist. A version for `NNReal`-valued functions. For an alternative version, convenient if the
infinite sums are not already expressed as `p`-th powers, see `Lp_add_le_tsum_of_nonneg`. -/
theorem Lp_add_le_hasSum {f g : ι → ℝ≥0} {A B : ℝ≥0} {p : ℝ} (hp : 1 ≤ p)
    (hf : HasSum (fun i => f i ^ p) (A ^ p)) (hg : HasSum (fun i => g i ^ p) (B ^ p)) :
    ∃ C, C ≤ A + B ∧ HasSum (fun i => (f i + g i) ^ p) (C ^ p) := by
  have hp' : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  obtain ⟨H₁, H₂⟩ := Lp_add_le_tsum hp hf.summable hg.summable
  have hA : A = (∑' i : ι, f i ^ p) ^ (1 / p) := by rw [hf.tsum_eq, rpow_inv_rpow_self hp']
  have hB : B = (∑' i : ι, g i ^ p) ^ (1 / p) := by rw [hg.tsum_eq, rpow_inv_rpow_self hp']
  refine ⟨(∑' i, (f i + g i) ^ p) ^ (1 / p), ?_, ?_⟩
  · simpa [hA, hB] using H₂
  · simpa only [rpow_self_rpow_inv hp'] using H₁.hasSum

end NNReal

namespace Real

variable (f g : ι → ℝ) {p q r : ℝ}

/-- **Hölder inequality**: the sum of (the `r`-powers of) the product of two functions is bounded by
the product of their `L^p` and `L^q` norms when `p`, `q` and `r` form a `Real.HolderTriple`.
Version for sums over finite sets, with real-valued functions. -/
theorem Lr_rpow_le_Lp_mul_Lq (hpqr : HolderTriple p q r) :
    ∑ i ∈ s, |f i * g i| ^ r ≤ (∑ i ∈ s, |f i| ^ p) ^ (r / p) * (∑ i ∈ s, |g i| ^ q) ^ (r / q) := by
  simpa using NNReal.coe_le_coe.2 <| NNReal.Lr_rpow_le_Lp_mul_Lq s (fun i ↦ ⟨_, abs_nonneg (f i)⟩)
    (fun i ↦ ⟨_, abs_nonneg (g i)⟩) hpqr

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : HolderConjugate p q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := by
  refine le_trans (sum_le_sum fun i _ ↦ ?_) (by simpa using Lr_rpow_le_Lp_mul_Lq s f g hpq)
  simp only [← abs_mul, le_abs_self]

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ`-valued functions. -/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i|) ^ p ≤ (#s : ℝ) ^ (p - 1) * ∑ i ∈ s, |f i| ^ p := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => ⟨_, abs_nonneg (f i)⟩) hp)
  push_cast at this
  exact this

set_option backward.isDefEq.respectTransparency false in
-- for some reason `exact_mod_cast` can't replace this argument
/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `Real`-valued functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i ∈ s, |f i + g i| ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) + (∑ i ∈ s, |g i| ^ p) ^ (1 / p) := by
  have :=
    NNReal.coe_le_coe.2
      (NNReal.Lp_add_le s (fun i => ⟨_, abs_nonneg (f i)⟩) (fun i => ⟨_, abs_nonneg (g i)⟩) hp)
  push_cast at this
  refine le_trans (rpow_le_rpow ?_ (sum_le_sum fun i _ => ?_) ?_) this <;>
    simp [sum_nonneg, rpow_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add_le,
      rpow_le_rpow]

variable {f g}

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  convert inner_le_Lp_mul_Lq s f g hpq using 3 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi]

/-- **Hölder inequality**: the sum of (the `r`-power of) the product of two functions is bounded
by (the `r`-power of) the product of their `L^p` and `L^q` norms, when `p`, `q`, `r` form a
`Real.HolderTriple`. -/
theorem Lr_rpow_le_Lp_mul_Lq_of_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ} {p q r : ℝ}
    (hpqr : p.HolderTriple q r) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∑ i ∈ s, (f i * g i) ^ r ≤ (∑ i ∈ s, f i ^ p) ^ (r / p) * (∑ i ∈ s, g i ^ q) ^ (r / q) := by
  convert Lr_rpow_le_Lp_mul_Lq s f g hpqr using 3 with i hi
  · rw [abs_of_nonneg (mul_nonneg (hf i hi) (hg i hi))]
  all_goals
    congr! with i hi
    exact Eq.symm (abs_of_nonneg (by grind))

/-- **Weighted Hölder inequality**. -/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  lift w to ι → ℝ≥0 using hw
  lift f to ι → ℝ≥0 using hf
  beta_reduce at *
  norm_cast at *
  exact NNReal.inner_le_weight_mul_Lp _ hp _ _

/-- **Weighted Hölder inequality** in terms of `Finset.expect`. -/
lemma compact_inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) {w f : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    𝔼 i ∈ s, w i * f i ≤ (𝔼 i ∈ s, w i) ^ (1 - p⁻¹) * (𝔼 i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  simp_rw [expect_eq_sum_div_card]
  rw [div_rpow, div_rpow, div_mul_div_comm, ← rpow_add', sub_add_cancel, rpow_one]
  · gcongr
    exact inner_le_weight_mul_Lp_of_nonneg s hp _ _ hw hf
  any_goals simp
  · exact sum_nonneg fun i _ ↦ by have := hw i; have := hf i; positivity
  · exact sum_nonneg fun i _ ↦ by have := hw i; positivity

/-- **Hölder inequality**: the sum of (the `r`-powers of) two functions is bounded by the product
of (the `r`-powers of) their `L^p` and `L^q` norms when `p`, `q` and `r` form a `Real.HolderTriple`.
A version for `ℝ`-valued functions. -/
theorem summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => (f i * g i) ^ r) ∧
      ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at *
  exact NNReal.summable_and_Lr_rpow_le_Lp_mul_Lq_tsum hpqr hf_sum hg_sum

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `ℝ`-valued functions.
For an alternative version, convenient if the infinite sums are already expressed as `p`-th powers,
see `inner_le_Lp_mul_Lq_hasSum_of_nonneg`. -/
theorem summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p)
    (hg_sum : Summable fun i => g i ^ q) :
    (Summable fun i => f i * g i) ∧
      ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  simpa using summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum

theorem summable_Lr_of_Lp_Lq_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => (f i * g i) ^ r :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).1

theorem summable_mul_of_Lp_Lq_of_nonneg (hpq : p.HolderConjugate q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    Summable fun i => f i * g i :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).1

theorem Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, (f i * g i) ^ r ≤ (∑' i, f i ^ p) ^ (r / p) * (∑' i, g i ^ q) ^ (r / q) :=
  (summable_and_Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum).2

theorem Lr_le_Lp_mul_Lq_tsum_of_nonneg (hpqr : p.HolderTriple q r) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    (∑' i, (f i * g i) ^ r) ^ (1 / r) ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  -- It's really inconvenient that `positivity` can't use `∀` hypotheses.
  have hf' : 0 ≤ ∑' i, f i ^ p := tsum_nonneg fun i ↦ rpow_nonneg (hf i) p
  have hg' : 0 ≤ ∑' i, g i ^ q := tsum_nonneg fun i ↦ rpow_nonneg (hg i) q
  obtain ⟨hp, hq, hr⟩ := hpqr.all_pos
  convert rpow_le_rpow_iff (tsum_nonneg fun i ↦ rpow_nonneg (mul_nonneg (hf i) (hg i)) r)
    (by apply mul_nonneg; all_goals apply rpow_nonneg; assumption)
    (inv_eq_one_div r ▸ inv_pos.mpr hpqr.pos') |>.mpr <|
    Lr_rpow_le_Lp_mul_Lq_tsum_of_nonneg hpqr hf hg hf_sum hg_sum using 1
  rw [mul_rpow (rpow_nonneg hf' _) (rpow_nonneg hg' _), ← Real.rpow_mul hg', ← Real.rpow_mul hf']
  field_simp

theorem inner_le_Lp_mul_Lq_tsum_of_nonneg (hpq : p.HolderConjugate q) (hf : ∀ i, 0 ≤ f i)
    (hg : ∀ i, 0 ≤ g i) (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) :=
  (summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hf_sum hg_sum).2

@[deprecated (since := "2026-02-12")]
alias inner_le_Lp_mul_Lq_of_nonneg' := inner_le_Lp_mul_Lq_of_nonneg

/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. A version for `NNReal`-valued
functions. For an alternative version, convenient if the infinite sums are not already expressed as
`p`-th powers, see `inner_le_Lp_mul_Lq_tsum_of_nonneg`. -/
theorem inner_le_Lp_mul_Lq_hasSum_of_nonneg (hpq : p.HolderConjugate q) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : HasSum (fun i => f i ^ p) (A ^ p)) (hg_sum : HasSum (fun i => g i ^ q) (B ^ q)) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ A * B ∧ HasSum (fun i => f i * g i) C := by
  lift f to ι → ℝ≥0 using hf
  lift g to ι → ℝ≥0 using hg
  lift A to ℝ≥0 using hA
  lift B to ℝ≥0 using hB
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast at hf_sum hg_sum
  obtain ⟨C, hC, H⟩ := NNReal.inner_le_Lp_mul_Lq_hasSum hpq hf_sum hg_sum
  refine ⟨C, C.prop, hC, ?_⟩
  norm_cast

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with nonnegative `ℝ`-valued
functions. -/
theorem rpow_sum_le_const_mul_sum_rpow_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ p ≤ (#s : ℝ) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  convert rpow_sum_le_const_mul_sum_rpow s f hp using 2 <;> apply sum_congr rfl <;> intro i hi <;>
    simp only [abs_of_nonneg, hf i hi]

/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  convert Lp_add_le s f g hp using 2 <;> [skip; congr 1; congr 1] <;> apply sum_congr rfl <;>
      intro i hi <;>
    simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
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
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at *
  norm_cast0 at *
  exact NNReal.Lp_add_le_tsum hp hf_sum hg_sum

theorem summable_Lp_add_of_nonneg (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    Summable fun i => (f i + g i) ^ p :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).1

theorem Lp_add_le_tsum_of_nonneg' (hp : 1 ≤ p) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable fun i => f i ^ p) (hg_sum : Summable fun i => g i ^ p) :
    (∑' i, (f i + g i) ^ p) ^ (1 / p) ≤ (∑' i, f i ^ p) ^ (1 / p) + (∑' i, g i ^ p) ^ (1 / p) :=
  (Lp_add_le_tsum_of_nonneg hp hf hg hf_sum hg_sum).2

/-- **Minkowski inequality**: the `L_p` seminorm of the infinite sum of two vectors is less than or
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
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce at hfA hgB
  norm_cast at hfA hgB
  obtain ⟨C, hC₁, hC₂⟩ := NNReal.Lp_add_le_hasSum hp hfA hgB
  use C
  -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
  beta_reduce
  norm_cast
  exact ⟨zero_le _, hC₁, hC₂⟩

end Real

namespace ENNReal

variable (f g : ι → ℝ≥0∞) {p q : ℝ}

-- TODO: fix the non-terminal simp on the last line
set_option linter.flexible false in
/-- **Hölder inequality**: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) := by
  by_cases! H : (∑ i ∈ s, f i ^ p) ^ (1 / p) = 0 ∨ (∑ i ∈ s, g i ^ q) ^ (1 / q) = 0
  · replace H : (∀ i ∈ s, f i = 0) ∨ ∀ i ∈ s, g i = 0 := by
      simpa [ENNReal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
        sum_eq_zero_iff_of_nonneg] using H
    have : ∀ i ∈ s, f i * g i = 0 := fun i hi => by rcases H with H | H <;> simp [H i hi]
    simp [sum_eq_zero this]
  by_cases H' : (∑ i ∈ s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i ∈ s, g i ^ q) ^ (1 / q) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ s, g i ≠ ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
      ENNReal.sum_eq_top, not_or] using H'
  have := ENNReal.coe_le_coe.2 (@NNReal.inner_le_Lp_mul_Lq _ s (fun i => ENNReal.toNNReal (f i))
    (fun i => ENNReal.toNNReal (g i)) _ _ hpq)
  simp [ENNReal.coe_rpow_of_nonneg, hpq.pos.le, hpq.symm.pos.le] at this
  convert this using 1 <;> [skip; congr 2] <;> [skip; skip; simp; skip; simp] <;>
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp [H'.1 i hi, H'.2 i hi, -WithZero.coe_mul]

set_option backward.isDefEq.respectTransparency false in
/-- **Weighted Hölder inequality**. -/
lemma inner_le_weight_mul_Lp_of_nonneg (s : Finset ι) {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0∞) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  have hp₀ : 0 < p := by positivity
  have hp₁ : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  by_cases! H : (∑ i ∈ s, w i) ^ (1 - p⁻¹) = 0 ∨ (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ = 0
  · replace H : (∀ i ∈ s, w i = 0) ∨ ∀ i ∈ s, w i = 0 ∨ f i = 0 := by
      simpa [hp₀, hp₁, hp₀.not_gt, hp₁.not_gt, sum_eq_zero_iff_of_nonneg] using H
    have (i) (hi : i ∈ s) : w i * f i = 0 := by rcases H with H | H <;> simp [H i hi]
    simp [sum_eq_zero this]
  by_cases H' : (∑ i ∈ s, w i) ^ (1 - p⁻¹) = ⊤ ∨ (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div, -sum_eq_zero_iff, -rpow_eq_zero_iff, H]
  replace H' : (∀ i ∈ s, w i ≠ ⊤) ∧ ∀ i ∈ s, w i * f i ^ p ≠ ⊤ := by
    simpa [rpow_eq_top_iff, hp₀, hp₁, hp₀.not_gt, hp₁.not_gt, sum_eq_top, not_or] using H'
  have := coe_le_coe.2 <| NNReal.inner_le_weight_mul_Lp s hp.le (fun i ↦ ENNReal.toNNReal (w i))
    fun i ↦ ENNReal.toNNReal (f i)
  rw [coe_mul] at this
  simp_rw [coe_rpow_of_nonneg _ <| inv_nonneg.2 hp₀.le, coe_finset_sum, ← ENNReal.toNNReal_rpow,
    ← ENNReal.toNNReal_mul, sum_congr rfl fun i hi ↦ coe_toNNReal (H'.2 i hi)] at this
  simp only [toNNReal_mul, coe_mul, sub_nonneg, hp₁.le, coe_rpow_of_nonneg, coe_finset_sum] at this
  convert this using 2 with i hi
  · obtain hw | hw := eq_or_ne (w i) 0
    · simp [hw]
    rw [coe_toNNReal (H'.1 _ hi), coe_toNNReal]
    simpa [mul_eq_top, hw, hp₀, hp₀.not_gt, H'.1 _ hi] using H'.2 _ hi
  · convert rfl with i hi
    exact coe_toNNReal (H'.1 _ hi)

/-- For `1 ≤ p`, the `p`-th power of the sum of `f i` is bounded above by a constant times the
sum of the `p`-th powers of `f i`. Version for sums over finite sets, with `ℝ≥0∞`-valued functions.
-/
theorem rpow_sum_le_const_mul_sum_rpow (hp : 1 ≤ p) :
    (∑ i ∈ s, f i) ^ p ≤ (card s : ℝ≥0∞) ^ (p - 1) * ∑ i ∈ s, f i ^ p := by
  rcases eq_or_lt_of_le hp with hp | hp
  · simp [← hp]
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := .conjExponent hp
  have hp₁ : 1 / p * p = 1 := one_div_mul_cancel hpq.ne_zero
  have hq : 1 / q * p = p - 1 := by
    rw [← hpq.div_conj_eq_sub_one]
    ring
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg, ← ENNReal.rpow_mul, hp₁, hq, coe_one,
    one_mul, one_rpow, rpow_one, Pi.one_apply, sum_const, Nat.smul_one_eq_cast] using
    ENNReal.rpow_le_rpow (inner_le_Lp_mul_Lq s 1 f hpq.symm) hpq.nonneg

/-- **Minkowski inequality**: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞`-valued nonnegative
functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) := by
  by_cases H' : (∑ i ∈ s, f i ^ p) ^ (1 / p) = ⊤ ∨ (∑ i ∈ s, g i ^ p) ^ (1 / p) = ⊤
  · rcases H' with H' | H' <;> simp [H', -one_div]
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ ∀ i ∈ s, g i ≠ ⊤ := by
    simpa [ENNReal.rpow_eq_top_iff, asymm pos, pos, ENNReal.sum_eq_top, not_or] using H'
  have :=
    ENNReal.coe_le_coe.2
      (@NNReal.Lp_add_le _ s (fun i => ENNReal.toNNReal (f i)) (fun i => ENNReal.toNNReal (g i)) _
        hp)
  push_cast [ENNReal.coe_rpow_of_nonneg, le_of_lt pos, le_of_lt (one_div_pos.2 pos)] at this
  simp_all

end ENNReal

end HoelderMinkowski
