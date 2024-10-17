/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Sub.Canonical
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Algebra.Group.Fin
import Mathlib.Data.ZMod.Defs

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.
-/

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
  obtain hk | hk : Even k.val ∨ Even (k.val + n) := by simp_all [parity_simps, em]
  · exact even_of_val hk
  · simpa using hk.natCast (α := Fin n)

lemma odd_of_odd {n : ℕ} [NeZero n] (hn : Odd n) (k : Fin n) : Odd k := by
  obtain hk | hk : Odd k.val ∨ Odd (k.val + n) := by simp_all [parity_simps, (em _).symm]
  · exact odd_of_val hk
  · simpa using hk.natCast (R := Fin n)

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
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [parity_simps, Nat.even_sub, *]
  

/-- In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even. -/
lemma even_iff {n : ℕ} {k : Fin n} : Even k ↔ Odd n ∨ Even k.val := by
  refine ⟨fun hk ↦ ?_, or_imp.2 ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [Nat.odd_iff_not_even, ← imp_iff_not_or]
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
