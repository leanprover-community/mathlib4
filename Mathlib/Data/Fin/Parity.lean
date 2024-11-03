/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs

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
    have h2l : (2 * l).val = l.val + l.val := by
      rw [two_mul l]
      exact Nat.mod_eq_of_lt (Nat.add_lt_add hl hl)
    rw [val_add_eq_mod, h2l]
    simp [Nat.mod_eq_of_lt (Nat.add_succ_lt_add hl hl)]
  | Or.inr hl =>
    let x : ℕ := l.val - n
    have hxxll : x + x = (l + l).val := by
      rw [val_add_eq_ite]
      simp [Nat.add_le_add hl hl]
      omega
    have hxl : 2 * x + 1 = (2 * l + 1).val := by
      rw [two_mul l, two_mul x]
      rw [hxxll]
      rw [@val_add_eq_of_sum_lt (n + n) (l + l) 1]
      · simp
        apply (Nat.one_mod_eq_one.mpr n.add_self_ne_one).symm
      · rw [one_val_cast (Nat.one_lt_of_ne_zero_and_even (NeZero.ne (n + n)) (even_add_self n))]
        apply Nat.add_one_lt_of_even_and_even_and_lt
          ((even_val_iff (even_add_self n)).mpr (even_add_self l)) (even_add_self n) ?_
        fin_omega
    rw [← hxl]
    exact odd_two_mul_add_one x

/-- In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even. -/
lemma even_iff {n : ℕ} {k : Fin n} : Even k ↔ Odd n ∨ Even k.val := by
  refine ⟨fun hk ↦ ?_, or_imp.2 ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (even_val_iff hn).2 hk

-- lemma odd_iff {n : ℕ} [NeZero n] {k : Fin n} : Odd k ↔ Odd n ∨ Odd k.val := by

end Fin
