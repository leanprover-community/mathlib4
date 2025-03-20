/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Lawrence Wu
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Maximum order cyclic permutations on `Fin n`

This file defines `finRotate`, which corresponds to the cycle `(1, ..., n)` on `Fin n`, and proves
various lemmas about it.

-/

open Nat

variable {n : ℕ}

/-- Rotate `Fin n` one step to the right. -/
def finRotate : ∀ n, Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | n + 1 => finAddFlip.trans (finCongr (Nat.add_comm 1 n))

@[simp] lemma finRotate_zero : finRotate 0 = Equiv.refl _ := rfl

lemma finRotate_succ (n : ℕ) :
    finRotate (n + 1) = finAddFlip.trans (finCongr (Nat.add_comm 1 n)) := rfl

theorem finRotate_of_lt {k : ℕ} (h : k < n) :
    finRotate (n + 1) ⟨k, h.trans_le n.le_succ⟩ = ⟨k + 1, Nat.succ_lt_succ h⟩ := by
  ext
  dsimp [finRotate_succ]
  simp [finAddFlip_apply_mk_left h, Nat.add_comm]

theorem finRotate_last' : finRotate (n + 1) ⟨n, by omega⟩ = ⟨0, Nat.zero_lt_succ _⟩ := by
  dsimp [finRotate_succ]
  rw [finAddFlip_apply_mk_right le_rfl]
  simp

theorem finRotate_last : finRotate (n + 1) (Fin.last _) = 0 :=
  finRotate_last'

theorem Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n → α) (a : α) :
    @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α) a v (finRotate _ i) := by
  ext ⟨i, h⟩
  by_cases h' : i < n
  · rw [finRotate_of_lt h', Fin.snoc, Fin.cons, dif_pos h']
    rfl
  · have h'' : n = i := by
      simp only [not_lt] at h'
      exact (Nat.eq_of_le_of_lt_succ h' h).symm
    subst h''
    rw [finRotate_last', Fin.snoc, Fin.cons, dif_neg (lt_irrefl _)]
    rfl

@[simp]
theorem finRotate_one : finRotate 1 = Equiv.refl _ :=
  Subsingleton.elim _ _

@[simp] theorem finRotate_succ_apply (i : Fin (n + 1)) : finRotate (n + 1) i = i + 1 := by
  cases n
  · exact @Subsingleton.elim (Fin 1) _ _ _
  obtain rfl | h := Fin.eq_or_lt_of_le i.le_last
  · simp [finRotate_last]
  · cases i
    simp only [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.val_mk] at h
    simp [finRotate_of_lt h, Fin.ext_iff, Fin.add_def, Nat.mod_eq_of_lt (Nat.succ_lt_succ h)]

theorem finRotate_apply_zero : finRotate n.succ 0 = 1 := by
  simp

theorem coe_finRotate_of_ne_last {i : Fin n.succ} (h : i ≠ Fin.last n) :
    (finRotate (n + 1) i : ℕ) = i + 1 := by
  rw [finRotate_succ_apply]
  have : (i : ℕ) < n := Fin.val_lt_last h
  exact Fin.val_add_one_of_lt this

theorem coe_finRotate (i : Fin n.succ) :
    (finRotate n.succ i : ℕ) = if i = Fin.last n then (0 : ℕ) else i + 1 := by
  rw [finRotate_succ_apply, Fin.val_add_one i]

theorem lt_finRotate_iff_ne_last (i : Fin (n + 1)) :
    i < finRotate _ i ↔ i ≠ Fin.last n := by
  refine ⟨fun hi hc ↦ ?_, fun hi ↦ ?_⟩
  · simp only [hc, finRotate_succ_apply, Fin.last_add_one, Fin.not_lt_zero] at hi
  · rw [Fin.lt_iff_val_lt_val, coe_finRotate_of_ne_last hi, Nat.lt_add_one_iff]

theorem lt_finRotate_iff_ne_neg_one [NeZero n] (i : Fin n) :
    i < finRotate _ i ↔ i ≠ -1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [lt_finRotate_iff_ne_last, ne_eq, not_iff_not, ←Fin.neg_last, neg_neg]

@[simp] lemma finRotate_succ_symm_apply [NeZero n] (i : Fin n) : (finRotate _).symm i = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  apply (finRotate n.succ).symm_apply_eq.mpr
  rw [finRotate_succ_apply, sub_add_cancel]

lemma coe_finRotate_symm_of_ne_zero [NeZero n] {i : Fin n} (hi : i ≠ 0) :
    ((finRotate _).symm i : ℕ) = i - 1 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  rwa [finRotate_succ_symm_apply, Fin.val_sub_one_of_ne_zero]

theorem finRotate_symm_lt_iff_ne_zero [NeZero n] (i : Fin n) :
    (finRotate _).symm i < i ↔ i ≠ 0 := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨fun hi hc ↦ ?_, fun hi ↦ ?_⟩
  · simp only [hc, Fin.last_add_one, Fin.not_lt_zero] at hi
  · rw [Fin.lt_iff_val_lt_val, coe_finRotate_symm_of_ne_zero hi]
    apply sub_lt (zero_lt_of_ne_zero <| Fin.val_ne_zero_iff.mpr hi) Nat.zero_lt_one
