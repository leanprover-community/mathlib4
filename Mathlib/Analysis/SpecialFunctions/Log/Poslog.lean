/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Positive Part of the Logarithm

This file defines the function `log⁺ = r ↦ max 0 (log r)`, and establishes
standard estimates.
-/

open Real

/-!
## Definition, Notation and Reformulations
-/
/-- Definition: the real part of the logarithm. -/
noncomputable def Real.poslog : ℝ → ℝ := fun r ↦ max 0 (log r)

/-- Notation `log⁺` for the real part of the logarithm. -/
notation "log⁺" => poslog

/-- Definition of the real part of the logarithm, formulated as a theorem. -/
theorem Real.poslog_def {r : ℝ} : log⁺ r = max 0 (log r) := rfl

/-!
## Elementary Properties
-/
/-- Presentation of `log` in terms of its positive part. -/
theorem Real.log_eq_poslog_sub_poslog_inv {r : ℝ} : log r = log⁺ r - log⁺ r⁻¹ := by
  rw [poslog_def, poslog_def, log_inv]
  by_cases h : 0 ≤ log r
  · simp [h]
  · rw [not_le] at h
    simp [neg_nonneg.1 (Left.nonneg_neg_iff.2 h.le)]

/-- Presentation of `log⁺` in terms of `log`. -/
theorem Real.poslog_eq_half_mul_log_add_log_abs {r : ℝ} : log⁺ r = 2⁻¹ * (log r + |log r|) := by
  by_cases hr : 0 ≤ log r
  · simp [poslog, hr, abs_of_nonneg]
    ring
  · simp [poslog, le_of_not_ge hr, abs_of_nonpos]

/-- The positive part of `log` is never negative. -/
theorem Real.poslog_nonneg {x : ℝ} : 0 ≤ log⁺ x := by simp [poslog]

/-- The function `log⁺` is even. -/
theorem Real.poslog_neg (x : ℝ) : log⁺ x = log⁺ (-x) := by simp [poslog]

/-- The function `log⁺` is even. -/
theorem Real.poslog_abs (x : ℝ) : log⁺ |x| = log⁺ x := by simp [poslog]

/-- The function `log⁺` is zero in the interval [-1,1]. -/
theorem Real.poslog_eq_zero_iff (x : ℝ) : log⁺ x = 0 ↔ |x| ≤ 1 := by
  rw [← poslog_abs, ← log_nonpos_iff (abs_nonneg x)]
  simp [poslog]

/-- The function `log⁺` equals `log` outside of in the interval (-1,1). -/
theorem Real.poslog_eq_log {x : ℝ} (hx : 1 ≤ |x|) : log⁺ x = log x := by
  simp [poslog]
  rw [← log_abs]
  apply log_nonneg hx

/-- The function `log⁺` equals `log` for all natural numbers. -/
theorem Real.poslog_eq_log_of_nat {n : ℕ} : log n = log⁺ n := by
  by_cases hn : n = 0
  · simp [hn, poslog]
  · simp [poslog_eq_log, Nat.one_le_iff_ne_zero.2 hn]

/-- The function `log⁺` is monotone in the positive axis. -/
theorem Real.monotoneOn_poslog : MonotoneOn log⁺ (Set.Ici 0) := by
  intro x hx y hy hxy
  simp [poslog]
  by_cases h : log x ≤ 0
  · tauto
  · right
    have := log_le_log (lt_trans Real.zero_lt_one ((log_pos_iff hx).1 (not_le.1 h))) hxy
    simp [this]
    linarith

/-!
## Estimates for Products
-/
/-- Estimate for `log⁺` of a product. See `Real.poslog_prod` for a variant involving
multiple factors. -/
theorem Real.poslog_mul {a b : ℝ} :
    log⁺ (a * b) ≤ log⁺ a + log⁺ b := by
  by_cases ha : a = 0
  · simp [ha, poslog]
  by_cases hb : b = 0
  · simp [hb, poslog]
  unfold poslog
  nth_rw 1 [← add_zero 0, log_mul ha hb]
  exact max_add_add_le_max_add_max

/-- Estimate for `log⁺` of a product. Special case of `Real.poslog_mul` where one of
the factors is a natural number. -/
theorem Real.poslog_mul_nat {n : ℕ} {a : ℝ} :
    log⁺ (n * a) ≤ log n + log⁺ a := by
  rw [poslog_eq_log_of_nat]
  exact poslog_mul

/-- Estimate for `log⁺` of a product. See `Real.poslog_prod` for a variant with
only two factors. -/
theorem Real.poslog_prod {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    log⁺ (∏ t ∈ s, f t) ≤ ∑ t ∈ s, log⁺ (f t) := by
  apply Finset.induction (p := fun (S : Finset α) ↦ (log⁺ (∏ t ∈ S, f t) ≤ ∑ t ∈ S, log⁺ (f t)))
  · -- Empty set
    simp [poslog]
  · -- Non empty set
    intro a s ha hs
    calc log⁺ (∏ t ∈ insert a s, f t)
    _ = log⁺ (f a * ∏ t ∈ s, f t) := by rw [Finset.prod_insert ha]
    _ ≤ log⁺ (f a) + log⁺ (∏ t ∈ s, f t) := poslog_mul
    _ ≤ log⁺ (f a) + ∑ t ∈ s, log⁺ (f t) := add_le_add (by rfl) hs
    _ = ∑ t ∈ insert a s, log⁺ (f t) := by rw [Finset.sum_insert ha]

/-!
## Estimates for Sums
-/
/-- Estimate for `log⁺` of a sum. See `Real.poslog_add` for a variant involving
multiple summands. -/
theorem Real.poslog_sum {α : Type} (s : Finset α) (f : α → ℝ) :
    log⁺ (∑ t ∈ s, f t) ≤ log (s.card) + ∑ t ∈ s, log⁺ (f t) := by
  -- Trivial case: empty sum
  by_cases hs : s = ∅
  · simp [hs, poslog]
  -- Nontrivial case: Obtain maximal element…
  obtain ⟨t_max, ht_max⟩ := s.exists_max_image (fun t ↦ |f t|)
    (Finset.nonempty_iff_ne_empty.mpr hs)
  -- …then calculate
  calc log⁺ (∑ t ∈ s, f t)
  _ = log⁺ |∑ t ∈ s, f t| := by
    rw [Real.poslog_abs]
  _ ≤ log⁺ (∑ t ∈ s, |f t|) := by
    apply monotoneOn_poslog (by simp) (by simp [Finset.sum_nonneg])
    simp [Finset.abs_sum_le_sum_abs]
  _ ≤ log⁺ (∑ t ∈ s, |f t_max|) := by
    apply monotoneOn_poslog (by simp [Finset.sum_nonneg]) (by simp [Finset.sum_nonneg]; positivity)
    apply Finset.sum_le_sum (fun i ih ↦ ht_max.2 i ih)
  _ = log⁺ (s.card * |f t_max|) := by
    simp [Finset.sum_const]
  _ ≤ log s.card + log⁺ |f t_max| := poslog_mul_nat
  _ ≤ log s.card + ∑ t ∈ s, log⁺ (f t) := by
    apply add_le_add (by rfl)
    rw [poslog_abs]
    apply Finset.single_le_sum (fun _ _ ↦ poslog_nonneg) ht_max.1

/-- Estimate for `log⁺` of a sum. See `Real.poslog_add` for a variant with only
two summands. -/
theorem Real.poslog_add {a b : ℝ} : log⁺ (a + b) ≤ log 2 + log⁺ a + log⁺ b := by
  convert Real.poslog_sum (Finset.univ : Finset (Fin 2))
    (fun i => match i with | 0 => a | 1 => b : Fin 2 → ℝ) using 1
  <;> simp [add_assoc]
