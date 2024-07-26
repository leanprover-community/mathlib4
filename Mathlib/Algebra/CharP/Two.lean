/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.ExpChar
import Mathlib.GroupTheory.OrderOfElement

/-!
# Lemmas about rings of characteristic two

This file contains results about `CharP R 2`, in the `CharTwo` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[Fact (Prime 2)]` argument.
-/


variable {R ι : Type*}

namespace CharTwo

section Semiring

variable [Semiring R] [CharP R 2]

theorem two_eq_zero : (2 : R) = 0 := by rw [← Nat.cast_two, CharP.cast_eq_zero]

@[simp]
theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_smul R x, two_eq_zero, zero_smul]

end Semiring

section Ring

variable [Ring R] [CharP R 2]

@[simp]
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul R x, two_eq_zero, zero_smul]

theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq

@[simp]
theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq]

theorem sub_eq_add' : HSub.hSub = ((· + ·) : R → R → R) :=
  funext fun x => funext fun y => sub_eq_add x y

end Ring

section CommSemiring

variable [CommSemiring R] [CharP R 2]

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_pow_char _ _ _

theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, add_sq]

theorem list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  list_sum_pow_char _ _

theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  simp_rw [← pow_two, list_sum_sq]

theorem multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  multiset_sum_pow_char _ _

theorem multiset_sum_mul_self (l : Multiset R) :
    l.sum * l.sum = (Multiset.map (fun x => x * x) l).sum := by simp_rw [← pow_two, multiset_sum_sq]

theorem sum_sq (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 :=
  sum_pow_char _ _ _

theorem sum_mul_self (s : Finset ι) (f : ι → R) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by simp_rw [← pow_two, sum_sq]

end CommSemiring

end CharTwo

section ringChar

variable [Ring R]

theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_one, ← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

@[simp]
theorem orderOf_neg_one [Nontrivial R] : orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 := by
  split_ifs with h
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h

end ringChar
