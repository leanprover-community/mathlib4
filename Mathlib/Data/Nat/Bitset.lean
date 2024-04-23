/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Combinatorics.Colex

/-!
# Bitset

Given `n : ℕ`, we define `Nat.bitSet n`, which is the `Finset` of indices that have a `1` in the
binary expansion of `n`. We show that this function is the inverse of `fun s ↦ ∑ i in s, 2^i`,
and therefore that it gives an order isomorphism from `ℕ` to `Colex ℕ`.

The latter proof uses the machinery in `Combinatorics.Colex`, which is why this doesn't appear
in an earlier file. The implementation of `Nat.bitSet` is a direct recursive definition,
which seems cleaner than the other option of using `Nat.bits` and therefore the `List` API.

TODO : Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

open Finset BigOperators

namespace Nat

variable {a n : ℕ} {s : Finset ℕ}

/-- The function which maps the natural number `∑ i in s, 2^i` to the Finset `s`.
This could also be defined using `Nat.bits`, but it seems easier to avoid the `List` api.  -/
def bitSet (n : ℕ) : Finset ℕ := by
  induction' n using binaryRec with b _ s
  · exact ∅
  cases b
  · exact image (· + 1) s
  · exact insert 0 (image (· + 1) s)

theorem bitSet_bit_true (n : ℕ) : bitSet (bit true n) = insert 0 (image (· + 1) (bitSet n)) :=
  binaryRec_eq rfl _ _

theorem bitSet_bit_false (n : ℕ) : bitSet (bit false n) = image (· + 1) (bitSet n) :=
  binaryRec_eq rfl _ _

@[simp] theorem bitSet_two_mul_add (n : ℕ) : bitSet (2*n + 1) =
    insert 0 (image (· + 1) (bitSet n)) := by
  rw [← bitSet_bit_true, bit_true, bit1_val]

@[simp] theorem bitSet_two_mul (n : ℕ) : bitSet (2*n) =
    image (· + 1) (bitSet n) := by
  rw [← bitSet_bit_false, bit_false, bit0_val]

@[simp] theorem bitSet_zero : bitSet 0 = ∅ := rfl

@[simp] theorem bitSet_one : bitSet 1 = {0} := rfl

@[simp] theorem bitSet_two_pow (k : ℕ) : bitSet (2^k) = {k} := by
  induction' k using Nat.recAux with k ih; rfl
  rw [pow_add, pow_one, mul_comm, bitSet_two_mul, ih, image_singleton]

theorem twoPowSum_bitSet (n : ℕ) : ∑ i in n.bitSet, 2 ^ i = n := by
  induction' n using binaryRec with b n hs; rfl
  cases b
  · rw [bitSet_bit_false, sum_image (by simp), bit_false, bit0_val]
    simp_rw [pow_add, pow_one, ← Finset.sum_mul, mul_comm 2]
    simpa using hs
  rw [bitSet_bit_true, bit_true, sum_insert (by simp), bit1_val, sum_image (by simp),
    pow_zero, add_comm, add_left_inj]
  simp_rw [pow_add, pow_one, ← Finset.sum_mul, mul_comm 2]
  simpa using hs

theorem lt_geomSum_of_mem (hn : 2 ≤ n) (hi : a ∈ s) : a < ∑ i in s, n^i :=
  (lt_pow_self hn a).trans_le (single_le_sum (by simp) hi)

theorem two_pow_le_of_mem_bitSet (ha : a ∈ n.bitSet) : 2^a ≤ n := by
  rw [← twoPowSum_bitSet n]
  exact single_le_sum (by simp) ha

theorem not_mem_bitSet_self (n : ℕ) : n ∉ n.bitSet :=
  fun h ↦ (lt_two_pow n).not_le <| two_pow_le_of_mem_bitSet h

theorem bitSet_twoPowSum (s : Finset ℕ) : bitSet (∑ i in s, 2^i) = s := by
  rw [← (geomSum_injective rfl.le).eq_iff, twoPowSum_bitSet]

/-- The equivalence between `ℕ` and `Finset ℕ` that maps `∑ i in s, 2^i` to `s`.-/
@[simps] def equivBitSet : ℕ ≃ Finset ℕ where
  toFun := bitSet
  invFun s := ∑ i in s, 2^i
  left_inv := twoPowSum_bitSet
  right_inv := bitSet_twoPowSum

/-- The equivalence `equivBitSet` enumerates `Finset ℕ` in colexicographic order. -/
@[simps] def orderIsoColex : ℕ ≃o Colex ℕ where
  toFun n := Colex.toColex (equivBitSet n)
  invFun s := equivBitSet.symm s.ofColex
  left_inv n := equivBitSet.symm_apply_apply n
  right_inv s :=  Finset.toColex_inj.2 (equivBitSet.apply_symm_apply s.ofColex)
  map_rel_iff' := by
    simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le), twoPowSum_bitSet]

end Nat
