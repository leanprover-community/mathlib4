/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Iván Renison
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.

We also prove a lemma about parity of `Fin.succAbove i j + Fin.predAbove j i`
which can be used to prove `d ∘ d = 0` for de Rham cohomologies.
-/

open Fin

namespace Fin

open Fin.CommRing

variable {n : ℕ} {k : Fin n}

theorem even_succAbove_add_predAbove (i : Fin (n + 1)) (j : Fin n) :
    Even (i.succAbove j + j.predAbove i : ℕ) ↔ Odd (i + j : ℕ) := by
  rcases lt_or_ge j.castSucc i with hji | hij
  · have : 1 ≤ (i : ℕ) := (Nat.zero_le j).trans_lt hji
    simp [succAbove_of_castSucc_lt _ _ hji, predAbove_of_castSucc_lt _ _ hji, this, iff_comm,
      parity_simps]
  · simp [succAbove_of_le_castSucc _ _ hij, predAbove_of_le_castSucc _ _ hij,
      ← Nat.not_even_iff_odd, not_iff, not_iff_comm, parity_simps]

lemma neg_one_pow_succAbove_add_predAbove {R : Type*} [Monoid R] [HasDistribNeg R]
    (i : Fin (n + 1)) (j : Fin n) :
    (-1 : R) ^ (i.succAbove j + j.predAbove i : ℕ) = -(-1) ^ (i + j : ℕ) := by
  rw [← neg_one_mul (_ ^ _), ← pow_succ', neg_one_pow_congr]
  rw [even_succAbove_add_predAbove, Nat.even_add_one, Nat.not_even_iff_odd]

lemma even_of_val (h : Even k.val) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

lemma odd_of_val [NeZero n] (h : Odd k.val) : Odd k := by
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast

lemma even_of_odd (hn : Odd n) (k : Fin n) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rcases k.val.even_or_odd with hk | hk
  · exact even_of_val hk
  · simpa using (hk.add_odd hn).natCast (α := Fin n)

lemma odd_of_odd [NeZero n] (hn : Odd n) (k : Fin n) : Odd k := by
  rcases k.val.even_or_odd with hk | hk
  · simpa using (Even.add_odd hk hn).natCast (R := Fin n)
  · exact odd_of_val hk

lemma even_iff_of_even (hn : Even n) : Even k ↔ Even k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, even_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]

lemma odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ Odd k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, odd_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add, val_mul, coe_ofNat_eq_mod, coe_ofNat_eq_mod]
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.odd_iff]
  rw [Nat.mod_mod_of_dvd _ ⟨n, (two_mul n).symm⟩, ← Nat.odd_iff, Nat.odd_add_one,
    Nat.not_odd_iff_even]
  simp

/-- In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even. -/
lemma even_iff : Even k ↔ (Odd n ∨ Even k.val) := by
  refine ⟨fun hk ↦ ?_, or_imp.mpr ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (even_iff_of_even hn).mp hk

lemma even_iff_imp : Even k ↔ (Even n → Even k.val) := by
  rw [imp_iff_not_or, Nat.not_even_iff_odd]
  exact even_iff

/-- In `Fin n`, all elements are odd for odd `n`,
otherwise an element is odd iff its `Fin.val` value is odd. -/
lemma odd_iff [NeZero n] : Odd k ↔ Odd n ∨ Odd k.val := by
  refine ⟨fun hk ↦ ?_, or_imp.mpr ⟨(odd_of_odd · k), odd_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (odd_iff_of_even hn).mp hk

lemma odd_iff_imp [NeZero n] : Odd k ↔ (Even n → Odd k.val) := by
  rw [imp_iff_not_or, Nat.not_even_iff_odd]
  exact odd_iff

lemma even_iff_mod_of_even (hn : Even n) : Even k ↔ k.val % 2 = 0 := by
  rw [even_iff_of_even hn]
  exact Nat.even_iff

lemma odd_iff_mod_of_even [NeZero n] (hn : Even n) : Odd k ↔ k.val % 2 = 1 := by
  rw [odd_iff_of_even hn]
  exact Nat.odd_iff

lemma not_odd_iff_even_of_even [NeZero n] (hn : Even n) : ¬Odd k ↔ Even k := by
  rw [even_iff_of_even hn, odd_iff_of_even hn]
  exact Nat.not_odd_iff_even

lemma not_even_iff_odd_of_even [NeZero n] (hn : Even n) : ¬Even k ↔ Odd k := by
  rw [even_iff_of_even hn, odd_iff_of_even hn]
  exact Nat.not_even_iff_odd

lemma odd_add_one_iff_even [NeZero n] : Odd (k + 1) ↔ Even k :=
  ⟨fun ⟨k, hk⟩ ↦ add_right_cancel hk ▸ even_two_mul k, Even.add_one⟩

lemma even_add_one_iff_odd [NeZero n] : Even (k + 1) ↔ Odd k :=
  ⟨fun ⟨k, hk⟩ ↦ eq_sub_iff_add_eq.mpr hk ▸ (Even.add_self k).sub_odd odd_one, Odd.add_one⟩

end Fin
