/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Parity

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.
-/

lemma Even.natCast {R : Type*} [AddMonoidWithOne R] {n : ℕ} (hn : Even n) : Even (n : R) :=
  hn.map <| Nat.castAddMonoidHom R

lemma Odd.natCast {R : Type*} [Semiring R] {n : ℕ} (hn : Odd n) : Odd (n : R) :=
  hn.map <| Nat.castRingHom R

namespace Fin

/-- In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even. -/
lemma even_iff {n : ℕ} {k : Fin n} : Even k ↔ Odd n ∨ Even k.val := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [or_iff_not_imp_left, ← Nat.even_iff_not_odd]
    rintro ⟨n, rfl⟩
    rw [val_add_eq_ite]
    split_ifs
    exacts [Even.tsub ⟨k, rfl⟩ ⟨n, rfl⟩, ⟨k, rfl⟩]
  · intro h
    rcases em (Even k.val) with ⟨l, hl⟩ | hk
    · lift l to Fin n using lt_of_le_of_lt (hl.symm ▸ le_add_self) k.2
      refine ⟨l, ext ?_⟩
      rw [Fin.val_add, ← hl, Nat.mod_eq_of_lt k.2]
    · rcases h.resolve_right hk with ⟨n, rfl⟩; clear h
      rcases Nat.odd_iff_not_even.2 hk with ⟨l, hl⟩
      use ↑(l + n + 1)
      calc
        k = (↑(2 * l + 1) : Fin _) := by rw [← hl, cast_val_eq_self]
        _ = ↑((2 * l + 1) + (2 * n + 1)) := by
          rw [Nat.cast_add (2 * l + 1), Fin.nat_cast_self, add_zero]
        _ = _ := by simp only [← Nat.cast_add, two_mul, add_comm, add_left_comm, add_assoc]

end Fin
