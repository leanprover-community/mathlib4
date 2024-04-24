/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Combinatorics.Colex

/-!
# Bit Indices

Given `n : ℕ`, we define `Nat.bitIndices n`, which is the `Finset` of indices of `1`s in the
binary expansion of `n`. We show that this function is the inverse of `fun s ↦ ∑ i in s, 2^i`,
and therefore that it gives an order isomorphism from `ℕ` to `Colex ℕ`.

The latter proof uses the machinery in `Combinatorics.Colex`, which is why this doesn't appear
in an earlier file. The implementation of `Nat.bitIndices` is a direct recursive definition,
which is definitionally cleaner than the other option of using `Nat.bits` and the `List` API.

TODO : Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

open Finset BigOperators

namespace Nat

variable {a n : ℕ} {s : Finset ℕ}

/-- The function which maps the natural number `∑ i in s, 2^i` to the Finset `s`. -/
def bitIndices (n : ℕ) : Finset ℕ := by
  induction' n using binaryRec with b _ s
  · exact ∅
  cases b
  · exact s.map (addRightEmbedding 1)
  · exact (s.map (addRightEmbedding 1)).cons 0 (by simp)

@[simp] theorem bitIndices_zero : bitIndices 0 = ∅ := rfl

@[simp] theorem bitIndices_one : bitIndices 1 = {0} := rfl

theorem bitIndices_bit_true (n : ℕ) :
    bitIndices (bit true n) = ((bitIndices n).map (addRightEmbedding 1)).cons 0 (by simp) :=
  binaryRec_eq rfl _ _

theorem bitIndices_bit_false (n : ℕ) :
    bitIndices (bit false n) = (bitIndices n).map (addRightEmbedding 1) :=
  binaryRec_eq rfl _ _

@[simp] theorem bitIndices_two_mul_add (n : ℕ) : bitIndices (2*n + 1) =
    ((bitIndices n).map (addRightEmbedding 1)).cons 0 (by simp) := by
  rw [← bitIndices_bit_true, bit_true, bit1_val]

@[simp] theorem bitIndices_two_mul (n : ℕ) : bitIndices (2*n) =
    (bitIndices n).map (addRightEmbedding 1) := by
  rw [← bitIndices_bit_false, bit_false, bit0_val]

@[simp] theorem bitIndices_two_pow (k : ℕ) : bitIndices (2^k) = {k} := by
  induction' k using Nat.recAux with k ih; rfl
  rw [pow_add, pow_one, mul_comm, bitIndices_two_mul, ih, map_singleton, addRightEmbedding_apply]

theorem twoPowSum_bitIndices (n : ℕ) : ∑ i in n.bitIndices, 2 ^ i = n := by
  induction' n using binaryRec with b n hs; rfl
  have ih : ∑ i in bitIndices n, 2 ^ (i+1) = 2 * n := by simp [pow_add, ← sum_mul, hs, mul_comm 2]
  cases b
  · simp [bitIndices_bit_false, bit0_val, ih]
  simp [bitIndices_bit_true, ih, bit1_val, add_comm 1]

theorem lt_geomSum_of_mem (hn : 2 ≤ n) (hi : a ∈ s) : a < ∑ i in s, n^i :=
  (lt_pow_self hn a).trans_le (single_le_sum (by simp) hi)

theorem two_pow_le_of_mem_bitIndices (ha : a ∈ n.bitIndices) : 2^a ≤ n := by
  rw [← twoPowSum_bitIndices n]
  exact single_le_sum (by simp) ha

theorem not_mem_bitIndices_self (n : ℕ) : n ∉ n.bitIndices :=
  fun h ↦ (lt_two_pow n).not_le <| two_pow_le_of_mem_bitIndices h

theorem bitIndices_twoPowSum (s : Finset ℕ) : bitIndices (∑ i in s, 2^i) = s := by
  rw [← (geomSum_injective rfl.le).eq_iff, twoPowSum_bitIndices]

/-- The equivalence between `ℕ` and `Finset ℕ` that maps `∑ i in s, 2^i` to `s`.-/
@[simps] def equivBitIndices : ℕ ≃ Finset ℕ where
  toFun := bitIndices
  invFun s := ∑ i in s, 2^i
  left_inv := twoPowSum_bitIndices
  right_inv := bitIndices_twoPowSum

/-- The equivalence `Nat.equivBitIndices` enumerates `Finset ℕ` in colexicographic order. -/
@[simps] def orderIsoColex : ℕ ≃o Colex ℕ where
  toFun n := Colex.toColex (equivBitIndices n)
  invFun s := equivBitIndices.symm s.ofColex
  left_inv n := equivBitIndices.symm_apply_apply n
  right_inv s :=  Finset.toColex_inj.2 (equivBitIndices.apply_symm_apply s.ofColex)
  map_rel_iff' := by
    simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le), twoPowSum_bitIndices]

end Nat
