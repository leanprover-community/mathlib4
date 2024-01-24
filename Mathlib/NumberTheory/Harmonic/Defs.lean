/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
-/

import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Interval

/-!

This file defines the harmonic numbers.

* `Mathilb/NumberTheory/Harmonic/Int.lean` proves that the `n`th harmonic number is not an integer.
* `Mathlib/NumberTheory/Harmonic/Bounds.lean` provides basic log bounds.

-/

open BigOperators

/-- The nth-harmonic number defined as a finset sum of consecutive reciprocals. -/
def harmonic : ℕ → ℚ := fun n => ∑ i in Finset.range n, (↑(i + 1))⁻¹

@[simp]
lemma harmonic_zero : harmonic 0 = 0 :=
  rfl

@[simp]
lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹ := by
  apply Finset.sum_range_succ

lemma harmonic_pos {n : ℕ} (Hn : n ≠ 0) : 0 < harmonic n :=
  Finset.sum_pos (fun _ _ => inv_pos.mpr (by norm_cast; linarith))
  (by rwa [Finset.nonempty_range_iff])

lemma harmonic_eq_sum_Icc {n : ℕ} :  harmonic n = ∑ i in Finset.Icc 1 n, (↑i)⁻¹ := by
  unfold harmonic
  rw[Finset.range_eq_Ico, Finset.sum_Ico_add' (fun (i:ℕ) => (i:ℚ)⁻¹) 0 n (c:=1),
    Nat.Ico_succ_right]
