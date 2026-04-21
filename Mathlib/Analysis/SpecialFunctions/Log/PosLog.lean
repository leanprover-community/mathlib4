/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Positive Part of the Logarithm

This file defines the function `Real.posLog = r ↦ max 0 (log r)` and introduces the notation
`log⁺`. For a finite length-`n` sequence `f i` of reals, it establishes the following standard
estimates.

- `theorem posLog_prod : log⁺ (∏ i, f i) ≤ ∑ i, log⁺ (f i)`

- `theorem posLog_sum : log⁺ (∑ i, f i) ≤ log n + ∑ i, log⁺ (f i)`

See `Mathlib/Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean` for the presentation of
`log⁺` as a Circle Average.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Real

variable {x y : ℝ}

/-!
## Definition, Notation and Reformulations
-/

/-- Definition: the positive part of the logarithm. -/
noncomputable def posLog : ℝ → ℝ := fun r ↦ max 0 (log r)

/-- Notation `log⁺` for the positive part of the logarithm. -/
scoped notation "log⁺" => posLog

/-- Definition of the positive part of the logarithm, formulated as a theorem. -/
theorem posLog_def : log⁺ x = max 0 (log x) := rfl

/-!
## Elementary Properties
-/

/-- Presentation of `log` in terms of its positive part. -/
theorem posLog_sub_posLog_inv : log⁺ x - log⁺ x⁻¹ = log x := by
  rw [posLog_def, posLog_def, log_inv]
  by_cases! h : 0 ≤ log x
  · simp [h]
  · simp [neg_nonneg.1 (Left.nonneg_neg_iff.2 h.le)]

/-- Presentation of `log⁺` in terms of `log`. -/
theorem half_mul_log_add_log_abs : 2⁻¹ * (log x + |log x|) = log⁺ x := by
  by_cases! hr : 0 ≤ log x
  · simp [posLog, hr, abs_of_nonneg]
    ring
  · simp [posLog, hr.le, abs_of_nonpos]

@[simp] lemma posLog_zero : log⁺ 0 = 0 := by simp [posLog]

@[simp] lemma posLog_one : log⁺ 1 = 0 := by simp [posLog]

/-- The positive part of `log` is never negative. -/
theorem posLog_nonneg : 0 ≤ log⁺ x := by simp [posLog]

/-- The function `log⁺` is even. -/
@[simp] theorem posLog_neg (x : ℝ) : log⁺ (-x) = log⁺ x := by simp [posLog]

/-- The function `log⁺` is even. -/
@[simp] theorem posLog_abs (x : ℝ) : log⁺ |x| = log⁺ x := by simp [posLog]

/-- The function `log⁺` is zero in the interval [-1,1]. -/
theorem posLog_eq_zero_iff (x : ℝ) : log⁺ x = 0 ↔ |x| ≤ 1 := by
  rw [← posLog_abs, ← log_nonpos_iff (abs_nonneg x)]
  simp [posLog]

/-- The function `log⁺` equals `log` outside of the interval (-1,1). -/
theorem posLog_eq_log (hx : 1 ≤ |x|) : log⁺ x = log x := by
  simp only [posLog, sup_eq_right]
  rw [← log_abs]
  apply log_nonneg hx

/-- The function `log⁺` equals `log` for all natural numbers. -/
theorem log_of_nat_eq_posLog {n : ℕ} : log⁺ n = log n := by
  by_cases hn : n = 0
  · simp [hn, posLog]
  · simp [posLog_eq_log, Nat.one_le_iff_ne_zero.2 hn]

/-- The function `log⁺` equals `log (max 1 _)` for non-negative real numbers. -/
theorem posLog_eq_log_max_one (hx : 0 ≤ x) : log⁺ x = log (max 1 x) := by
  grind [le_abs, posLog_eq_log, log_one, max_eq_left, log_nonpos, posLog_def]

/-- The function `log⁺` is monotone on the positive axis. -/
theorem monotoneOn_posLog : MonotoneOn log⁺ (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [posLog, le_sup_iff, sup_le_iff, le_refl, true_and]
  by_cases! h : log x ≤ 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 h)) hxy
    simp only [this, and_true, ge_iff_le]
    linarith

@[gcongr]
lemma posLog_le_posLog (hx : 0 ≤ x) (hxy : x ≤ y) : log⁺ x ≤ log⁺ y :=
  monotoneOn_posLog hx (hx.trans hxy) hxy

/-- The function `log⁺` commutes with taking powers. -/
@[simp] lemma posLog_pow (n : ℕ) (x : ℝ) : log⁺ (x ^ n) = n * log⁺ x := by
  by_cases hn : n = 0
  · simp_all
  by_cases hx : |x| ≤ 1
  · simp_all [pow_le_one₀, (posLog_eq_zero_iff _).2]
  rw [not_le] at hx
  have : 1 ≤ |x ^ n| := by simp_all [one_le_pow₀, hx.le]
  simp [posLog_eq_log this, posLog_eq_log hx.le]

/-!
## Estimates for Products
-/

/-- Estimate for `log⁺` of a product. See `Real.posLog_prod` for a variant involving
multiple factors. -/
theorem posLog_mul : log⁺ (x * y) ≤ log⁺ x + log⁺ y := by
  by_cases ha : x = 0
  · simp [ha, posLog]
  by_cases hb : y = 0
  · simp [hb, posLog]
  unfold posLog
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

/-- Estimate for `log⁺` of a product. Special case of `Real.posLog_mul` where one of
the factors is a natural number. -/
theorem posLog_nat_mul {n : ℕ} : log⁺ (n * x) ≤ log n + log⁺ x := by
  rw [← log_of_nat_eq_posLog]
  exact posLog_mul

/-- Estimate for `log⁺` of a product. See `Real.posLog_mul` for a variant with
only two factors. -/
theorem posLog_prod {α : Type*} (s : Finset α) (f : α → ℝ) :
    log⁺ (∏ t ∈ s, f t) ≤ ∑ t ∈ s, log⁺ (f t) := by
  classical
  induction s using Finset.induction with
  | empty => simp [posLog]
  | insert a s ha hs =>
    calc log⁺ (∏ t ∈ insert a s, f t)
    _ = log⁺ (f a * ∏ t ∈ s, f t) := by rw [Finset.prod_insert ha]
    _ ≤ log⁺ (f a) + log⁺ (∏ t ∈ s, f t) := posLog_mul
    _ ≤ log⁺ (f a) + ∑ t ∈ s, log⁺ (f t) := add_le_add (by rfl) hs
    _ = ∑ t ∈ insert a s, log⁺ (f t) := by rw [Finset.sum_insert ha]

/-!
## Estimates for Sums
-/

-- TODO: non-terminal simp followed by positivity
set_option linter.flexible false in
/-- Estimate for `log⁺` of a sum. See `Real.posLog_add` for a variant involving
just two summands. -/
theorem posLog_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    log⁺ (∑ t ∈ s, f t) ≤ log (s.card) + ∑ t ∈ s, log⁺ (f t) := by
  -- Trivial case: empty sum
  by_cases! hs : s = ∅
  · simp [hs, posLog]
  -- Nontrivial case: Obtain maximal element…
  obtain ⟨t_max, ht_max⟩ := s.exists_max_image (fun t ↦ |f t|) hs
  -- …then calculate
  calc log⁺ (∑ t ∈ s, f t)
  _ = log⁺ |∑ t ∈ s, f t| := by
    rw [Real.posLog_abs]
  _ ≤ log⁺ (∑ t ∈ s, |f t|) := by
    apply monotoneOn_posLog (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ ≤ log⁺ (∑ t ∈ s, |f t_max|) := by
    apply monotoneOn_posLog (by simp [Finset.sum_nonneg]) (by simp; positivity)
    apply Finset.sum_le_sum (fun i ih ↦ ht_max.2 i ih)
  _ = log⁺ (s.card * |f t_max|) := by
    simp [Finset.sum_const]
  _ ≤ log s.card + log⁺ |f t_max| := posLog_nat_mul
  _ ≤ log s.card + ∑ t ∈ s, log⁺ (f t) := by
    gcongr
    rw [posLog_abs]
    apply Finset.single_le_sum (fun _ _ ↦ posLog_nonneg) ht_max.1

/--
Variant of `posLog_sum` for norms of elements in normed additive commutative
groups, using monotonicity of `log⁺` and the triangle inequality.
-/
lemma posLog_norm_sum_le {E : Type*} [SeminormedAddCommGroup E] {α : Type*} (s : Finset α)
    (f : α → E) :
    log⁺ ‖∑ t ∈ s, f t‖ ≤ log s.card + ∑ t ∈ s, log⁺ ‖f t‖ := by
  grw [norm_sum_le, posLog_sum]

/--
Estimate for `log⁺` of a sum. See `Real.posLog_sum` for a variant involving multiple summands.
-/
theorem posLog_add : log⁺ (x + y) ≤ log 2 + log⁺ x + log⁺ y := by
  convert posLog_sum Finset.univ ![x, y] using 1 <;> simp [add_assoc]

/--
Variant of `posLog_add` for norms of elements in normed additive commutative groups, using
monotonicity of `log⁺` and the triangle inequality.
-/
lemma posLog_norm_add_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    log⁺ ‖a + b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖ + log 2 := by
  grw [norm_add_le, posLog_add, add_rotate]

end Real
