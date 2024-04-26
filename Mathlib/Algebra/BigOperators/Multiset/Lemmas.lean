/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
import Mathlib.Algebra.BigOperators.List.Lemmas
import Mathlib.Algebra.BigOperators.Multiset.Basic

#align_import algebra.big_operators.multiset.lemmas from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Lemmas about `Multiset.sum` and `Multiset.prod` requiring extra algebra imports -/


variable {α : Type*}

namespace Multiset
section CommMonoid
variable [CommMonoid α] {s : Multiset α} {a : α}

lemma dvd_prod : a ∈ s → a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h => by simpa using List.dvd_prod h) a
#align multiset.dvd_prod Multiset.dvd_prod

@[simp] lemma prod_map_neg [HasDistribNeg α] (s : Multiset α) :
    (s.map Neg.neg).prod = (-1) ^ card s * s.prod := Quotient.inductionOn s (by simp)
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

section NonUnitalSemiring
variable [NonUnitalSemiring α] {s : Multiset α} {a : α}

lemma dvd_sum : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
  Multiset.induction_on s (fun _ ↦ dvd_zero _) fun x s ih h ↦ by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy ↦ h _ <| mem_cons.2 <| Or.inr hy)
#align multiset.dvd_sum Multiset.dvd_sum

end NonUnitalSemiring
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
