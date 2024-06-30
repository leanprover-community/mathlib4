/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Multiset.Antidiagonal
import Mathlib.Data.Multiset.Sections

#align_import algebra.big_operators.multiset.lemmas from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Lemmas about `Multiset.sum` and `Multiset.prod` requiring extra algebra imports -/


variable {ι α β : Type*}

namespace Multiset
section CommMonoid
variable [CommMonoid α] [HasDistribNeg α]

@[simp] lemma prod_map_neg (s : Multiset α) : (s.map Neg.neg).prod = (-1) ^ card s * s.prod :=
  Quotient.inductionOn s (by simp)
#align multiset.prod_map_neg Multiset.prod_map_neg

end CommMonoid

section CommMonoidWithZero
variable [CommMonoidWithZero α] {s : Multiset α}

lemma prod_eq_zero (h : (0 : α) ∈ s) : s.prod = 0 := by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩; simp [hs', Multiset.prod_cons]
#align multiset.prod_eq_zero Multiset.prod_eq_zero

variable [NoZeroDivisors α] [Nontrivial α] {s : Multiset α}

@[simp] lemma prod_eq_zero_iff : s.prod = 0 ↔ (0 : α) ∈ s :=
  Quotient.inductionOn s fun l ↦ by rw [quot_mk_to_coe, prod_coe]; exact List.prod_eq_zero_iff
#align multiset.prod_eq_zero_iff Multiset.prod_eq_zero_iff

lemma prod_ne_zero (h : (0 : α) ∉ s) : s.prod ≠ 0 := mt prod_eq_zero_iff.1 h
#align multiset.prod_ne_zero Multiset.prod_ne_zero

end CommMonoidWithZero

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring α] {a : α} {s : Multiset ι} {f : ι → α}

lemma sum_map_mul_left : sum (s.map fun i ↦ a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]
#align multiset.sum_map_mul_left Multiset.sum_map_mul_left

lemma sum_map_mul_right : sum (s.map fun i ↦ f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]
#align multiset.sum_map_mul_right Multiset.sum_map_mul_right

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring α] {s : Multiset α} {a : α}

lemma dvd_sum : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
  Multiset.induction_on s (fun _ ↦ dvd_zero _) fun x s ih h ↦ by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy ↦ h _ <| mem_cons.2 <| Or.inr hy)
#align multiset.dvd_sum Multiset.dvd_sum

end NonUnitalSemiring

section CommSemiring
variable [CommSemiring α]

lemma prod_map_sum {s : Multiset (Multiset α)} :
    prod (s.map sum) = sum ((Sections s).map prod) :=
  Multiset.induction_on s (by simp) fun a s ih ↦ by
    simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right]
#align multiset.prod_map_sum Multiset.prod_map_sum

lemma prod_map_add {s : Multiset ι} {f g : ι → α} :
    prod (s.map fun i ↦ f i + g i) =
      sum ((antidiagonal s).map fun p ↦ (p.1.map f).prod * (p.2.map g).prod) := by
  refine s.induction_on ?_ fun a s ih ↦ ?_
  · simp only [map_zero, prod_zero, antidiagonal_zero, map_singleton, mul_one, sum_singleton]
  · simp only [map_cons, prod_cons, ih, sum_map_mul_left.symm, add_mul, mul_left_comm (f a),
      mul_left_comm (g a), sum_map_add, antidiagonal_cons, Prod.map_apply, id_eq, map_add, map_map,
      Function.comp_apply, mul_assoc, sum_add]
    exact add_comm _ _
#align multiset.prod_map_add Multiset.prod_map_add

end CommSemiring
end Multiset

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring α] (s : Multiset α)

theorem multiset_sum_right (a : α) (h : ∀ b ∈ s, Commute a b) : Commute a s.sum := by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe, sum_coe]
  exact Commute.list_sum_right _ _ h
#align commute.multiset_sum_right Commute.multiset_sum_right

theorem multiset_sum_left (b : α) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b :=
  ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm
#align commute.multiset_sum_left Commute.multiset_sum_left

end Commute
