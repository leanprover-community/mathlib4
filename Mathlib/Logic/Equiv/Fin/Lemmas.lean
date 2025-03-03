/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Lawrence Wu.
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

variable {n : ℕ}

theorem lt_finRotate_iff_ne_neg_one [NeZero n] (i : Fin n) :
    i < finRotate _ i ↔ i ≠ -1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last, ne_eq, not_iff_not, ←Fin.neg_last, neg_neg]

lemma finRotate_succ_symm_apply [NeZero n] (i : Fin n) : (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_succ_apply, sub_add_cancel]

lemma coe_finRotate_symm_of_ne_zero [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    ((finRotate _).symm i : ℕ) = i - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rwa [finRotate_succ_symm_apply, Fin.val_sub_one_of_ne_zero]

theorem finRotate_symm_lt_iff_ne_zero [NeZero n] (i : Fin n) :
    (finRotate _).symm i < i ↔ i ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨fun hi hc ↦ ?_, fun hi ↦ ?_⟩
  · simp only [hc, Fin.last_add_one, Fin.not_lt_zero] at hi
  · rw [Fin.lt_iff_val_lt_val, coe_finRotate_symm_of_ne_zero hi]
    apply Nat.sub_lt (Nat.zero_lt_of_ne_zero <| (Fin.val_ne_zero_iff _).mpr hi)
      (Nat.zero_lt_one)
