/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Basic

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.
-/

open Fin

namespace Fin

lemma even_of_val {n : ℕ} {k : Fin n} (h : Even k.val) : Even k := by
  haveI : NeZero n := ⟨Nat.not_eq_zero_of_lt k.2⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

lemma odd_of_val {n : ℕ} [NeZero n] {k : Fin n} (h : Odd k.val) : Odd k := by
  haveI : NeZero n := ⟨Nat.not_eq_zero_of_lt k.2⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

lemma even_of_odd {n : ℕ} (hn : Odd n) (k : Fin n) : Even k := by
  haveI : NeZero n := ⟨Nat.not_eq_zero_of_lt k.2⟩
  apply k.val.even_or_odd.elim
  · intro hk
    exact even_of_val hk
  · intro hk
    simpa using (Odd.add_odd hk hn).natCast (α := Fin n)

lemma odd_of_odd {n : ℕ} [NeZero n] (hn : Odd n) (k : Fin n) : Odd k := by
  haveI : NeZero n := ⟨Nat.not_eq_zero_of_lt k.2⟩
  apply k.val.even_or_odd.elim
  · intro hk
    simpa using (Even.add_odd hk hn).natCast (R := Fin n)
  · intro hk
    exact odd_of_val hk

lemma even_val_iff {n : ℕ} (hn : Even n) {k : Fin n} : Even k.val ↔ Even k := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨even_of_val, ?_⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]

lemma odd_val_iff {n : ℕ} [NeZero n] (hn : Even n) {k : Fin n} : Odd k.val ↔ Odd k := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨odd_of_val, ?_⟩
  rintro ⟨l, rfl⟩
  match l.val.lt_or_ge n with
  | Or.inl hl =>
    have hl'' : (2 * l).val = 2 * l.val := by
      rw [two_mul l, l.val.two_mul]
      exact Nat.mod_eq_of_lt (Nat.add_lt_add hl hl)
    have hle'' : 2 * l.val + 1 < n + n := by
      rw [l.val.two_mul]
      exact Nat.add_succ_lt_add hl hl
    rw [Nat.val_add_eq_mod, hl'']
    simp [Nat.mod_eq_of_lt hle'']
  | Or.inr hl =>
    have hll''' : (l + l).val < n + n := by
      fin_omega
    have hll'''' : (l + l).val + 1 < n + n := by
      have e2 : Even (l + l).val := by
        exact (even_val_iff (even_add_self n)).mpr (even_add_self l)
      apply add_one_lt_of_even_and_even_and_lt e2 (even_add_self n) hll'''
    let x : ℕ := l.val - n
    have hxxll : x + x = (l + l).val := by
      rw [val_add_eq_ite]
      simp [Nat.add_le_add hl hl]
      omega
    have hxl' : 2 * x + 1 = (2 * l + 1).val := by
      rw [two_mul l, two_mul x]
      rw [hxxll]
      rw [@Nat.val_add_eq_of_sum_lt (n + n) (l + l) 1]
      · simp
        apply (Nat.one_mod_eq_one.mpr n.add_self_ne_one).symm
      · rw [one_val_cast (one_le_of_ne_zero_and_even (NeZero.ne (n + n)) (even_add_self n))]
        exact hll''''
    rw [← hxl']
    exact odd_two_mul_add_one x

/-- In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even. -/
lemma even_iff {n : ℕ} {k : Fin n} : Even k ↔ Odd n ∨ Even k.val := by
  refine ⟨fun hk ↦ ?_, or_imp.2 ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (even_val_iff hn).2 hk

/-  constructor
  · rintro ⟨k, rfl⟩
    rw [or_iff_not_imp_left, ← Nat.even_iff_not_odd]
    rintro ⟨n, rfl⟩
    rw [val_add_eq_ite]
    split_ifs with h
    exacts [(Nat.even_sub h).2 (by simp), ⟨k, rfl⟩]
  · intro h
    rcases em (Even k.val) with ⟨l, hl⟩ | hk
    · lift l to Fin n using lt_of_le_of_lt (hl.symm ▸ le_add_self) k.2
      refine ⟨l, ext ?_⟩
      rw [Fin.val_add, ← hl, Nat.mod_eq_of_lt k.2]
    · rcases h.resolve_right hk with ⟨n, rfl⟩; clear h
      rcases Nat.odd_iff_not_even.2 hk with ⟨l, hl⟩
      use ↑(l + n + 1)
      calc
        k = (↑(2 * l + 1) : Fin (2 * n + 1)) := by rw [← hl, cast_val_eq_self]
        _ = ↑((2 * l + 1) + (2 * n + 1)) := by
          rw [Nat.cast_add (2 * l + 1), Fin.natCast_self, add_zero]
        _ = _ := by simp only [← Nat.cast_add, two_mul, add_comm, add_left_comm, add_assoc] -/

-- lemma odd_iff {n : ℕ} [NeZero n] {k : Fin n} : Odd k ↔ Odd n ∨ Odd k.val := by

end Fin
