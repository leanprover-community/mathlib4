/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.OrderOfElement

/-!
# Lemmas about rings of characteristic two

This file contains results about `CharP R 2`, in the `CharTwo` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[Fact (Prime 2)]` argument.
-/

assert_not_exists Algebra LinearMap

variable {R ι : Type*}

namespace CharTwo

section AddMonoidWithOne

variable [AddMonoidWithOne R]

theorem two_eq_zero [CharP R 2] : (2 : R) = 0 := by
  rw [← Nat.cast_two, CharP.cast_eq_zero]

/-- The only hypotheses required to build a `CharP R 2` instance are `1 ≠ 0` and `2 = 0`. -/
theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff n := by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

end AddMonoidWithOne

section Semiring

variable [Semiring R] [CharP R 2]

@[scoped simp]
theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_smul R x, two_eq_zero, zero_smul]

@[scoped simp]
protected theorem two_nsmul (x : R) : 2 • x = 0 := by rw [two_smul, add_self_eq_zero]

end Semiring

section Ring

variable [Ring R] [CharP R 2]

@[scoped simp]
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq

@[scoped simp]
theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq]

@[deprecated sub_eq_add (since := "2024-10-24")]
theorem sub_eq_add' : HSub.hSub = (· + · : R → R → R) :=
  funext₂ sub_eq_add

theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  rw [← sub_eq_iff_eq_add, sub_eq_add]

theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  rw [← eq_sub_iff_add_eq, sub_eq_add]

@[scoped simp]
protected theorem two_zsmul (x : R) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul, add_self_eq_zero]

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

section CharP

variable [Ring R]

lemma CharP.orderOf_eq_two_iff [Nontrivial R] [NoZeroDivisors R] (p : ℕ)
    (hp : p ≠ 2) [CharP R p] {x : R} : orderOf x = 2 ↔ x = -1 := by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h ↦ hp ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))

end CharP
