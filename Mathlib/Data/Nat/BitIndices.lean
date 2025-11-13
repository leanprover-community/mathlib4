/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise

/-!
# Bit Indices

Given `n : ℕ`, we define `Nat.bitIndices n`, which is the `List` of indices of `1`s in the
binary expansion of `n`. If `s : Finset ℕ` and `n = ∑ i ∈ s, 2^i`, then
`Nat.bitIndices n` is the sorted list of elements of `s`.

The lemma `twoPowSum_bitIndices` proves that summing `2 ^ i` over this list gives `n`.
This is used in `Combinatorics.colex` to construct a bijection `equivBitIndices : ℕ ≃ Finset ℕ`.

## TODO

Relate the material in this file to `Nat.digits` and `Nat.bits`.
-/

open List
namespace Nat

variable {a n : ℕ}

/-- The function which maps each natural number `∑ i ∈ s, 2^i` to the list of
elements of `s` in increasing order. -/
def bitIndices (n : ℕ) : List ℕ :=
  @binaryRec (fun _ ↦ List ℕ) [] (fun b _ s ↦ b.casesOn (s.map (· + 1)) (0 :: s.map (· + 1))) n

@[simp] theorem bitIndices_zero : bitIndices 0 = [] := by simp [bitIndices]

@[simp] theorem bitIndices_one : bitIndices 1 = [0] := by simp [bitIndices]

theorem bitIndices_bit_true (n : ℕ) :
    bitIndices (bit true n) = 0 :: ((bitIndices n).map (· + 1)) :=
  binaryRec_eq _ _ (.inl rfl)

theorem bitIndices_bit_false (n : ℕ) :
    bitIndices (bit false n) = (bitIndices n).map (· + 1) :=
  binaryRec_eq _ _ (.inl rfl)

@[simp] theorem bitIndices_two_mul_add_one (n : ℕ) :
    bitIndices (2 * n + 1) = 0 :: (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_true, bit_true]

@[simp] theorem bitIndices_two_mul (n : ℕ) :
    bitIndices (2 * n) = (bitIndices n).map (· + 1) := by
  rw [← bitIndices_bit_false, bit_false]

@[simp] theorem bitIndices_sorted {n : ℕ} : n.bitIndices.Sorted (· < ·) := by
  induction n using binaryRec with
  | zero => simp
  | bit b n hs =>
    suffices List.Pairwise (fun a b ↦ a < b) n.bitIndices by
      cases b <;> simpa [List.Sorted, bit_false, bit_true, List.pairwise_map]
    exact List.Pairwise.imp (by simp) hs

@[simp] theorem bitIndices_two_pow_mul (k n : ℕ) :
    bitIndices (2^k * n) = (bitIndices n).map (· + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_comm, pow_add, pow_one, mul_assoc, bitIndices_two_mul, ih, List.map_map, comp_add_right]
    simp [add_comm (a := 1)]

@[simp] theorem bitIndices_two_pow (k : ℕ) : bitIndices (2^k) = [k] := by
  rw [← mul_one (a := 2^k), bitIndices_two_pow_mul]; simp

@[simp] theorem twoPowSum_bitIndices (n : ℕ) : (n.bitIndices.map (fun i ↦ 2 ^ i)).sum = n := by
  induction n using binaryRec with
  | zero => simp
  | bit b n hs =>
    have hrw : (fun i ↦ 2^i) ∘ (fun x ↦ x+1) = fun i ↦ 2 * 2 ^ i := by
      ext i; simp [pow_add, mul_comm]
    cases b
    · simpa [hrw, List.sum_map_mul_left]
    simp [hrw, List.sum_map_mul_left, hs, add_comm (a := 1)]

/-- Together with `Nat.twoPowSum_bitIndices`, this implies a bijection between `ℕ` and `Finset ℕ`.
See `Finset.equivBitIndices` for this bijection. -/
theorem bitIndices_twoPowsum {L : List ℕ} (hL : List.Sorted (· < ·) L) :
    (L.map (fun i ↦ 2^i)).sum.bitIndices = L := by
  cases L with | nil => simp | cons a L =>
  obtain ⟨haL, hL⟩ := sorted_cons.1 hL
  simp_rw [Nat.lt_iff_add_one_le] at haL
  have h' : ∃ (L₀ : List ℕ), L₀.Sorted (· < ·) ∧ L = L₀.map (· + a + 1) := by
    refine ⟨L.map (· - (a+1)), ?_, ?_⟩
    · rwa [Sorted, pairwise_map, Pairwise.and_mem,
        Pairwise.iff (S := fun x y ↦ x ∈ L ∧ y ∈ L ∧ x < y), ← Pairwise.and_mem]
      simp only [and_congr_right_iff]
      exact fun x y hx _ ↦ by rw [tsub_lt_tsub_iff_right (haL _ hx)]
    have h' : ∀ x ∈ L, ((fun x ↦ x + a + 1) ∘ (fun x ↦ x - (a + 1))) x = x := fun x hx ↦ by
      simp only [add_assoc, Function.comp_apply]; rw [tsub_add_cancel_of_le (haL _ hx)]
    simp [List.map_congr_left h']
  obtain ⟨L₀, hL₀, rfl⟩ := h'
  have hrw : (2^·) ∘ (· + a + 1) = fun i ↦ 2^a * (2 * 2^i) := by
    ext x; simp only [Function.comp_apply, pow_add, pow_one]; ac_rfl
  simp only [List.map_cons, List.map_map, List.sum_map_mul_left, List.sum_cons, hrw]
  nth_rw 1 [← mul_one (a := 2^a)]
  rw [← mul_add, bitIndices_two_pow_mul, add_comm, bitIndices_two_mul_add_one,
    bitIndices_twoPowsum hL₀]
  simp [add_comm (a := 1), add_assoc]
termination_by L.length

theorem two_pow_le_of_mem_bitIndices (ha : a ∈ n.bitIndices) : 2^a ≤ n := by
  rw [← twoPowSum_bitIndices n]
  exact List.single_le_sum (by simp) _ <| mem_map_of_mem ha

theorem notMem_bitIndices_self (n : ℕ) : n ∉ n.bitIndices :=
  fun h ↦ (n.lt_two_pow_self).not_ge <| two_pow_le_of_mem_bitIndices h

@[deprecated (since := "2025-05-23")] alias not_mem_bitIndices_self := notMem_bitIndices_self

end Nat
