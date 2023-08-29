/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser
-/
import Mathlib.Data.List.BigOperators.Lemmas
import Mathlib.Algebra.BigOperators.Multiset.Basic

#align_import algebra.big_operators.multiset.lemmas from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # Lemmas about `Multiset.sum` and `Multiset.prod` requiring extra algebra imports -/


variable {α : Type*}

namespace Multiset

theorem dvd_prod [CommMonoid α] {s : Multiset α} {a : α} : a ∈ s → a ∣ s.prod :=
  Quotient.inductionOn s (fun l a h => by simpa using List.dvd_prod h) a
                                          -- 🎉 no goals
#align multiset.dvd_prod Multiset.dvd_prod

@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid α] {m : Multiset α} :
    m.prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
  Quotient.inductionOn m fun l => by simpa using List.prod_eq_one_iff l
                                     -- 🎉 no goals
#align multiset.prod_eq_one_iff Multiset.prod_eq_one_iff
#align multiset.sum_eq_zero_iff Multiset.sum_eq_zero_iff

end Multiset

@[simp]
lemma CanonicallyOrderedCommSemiring.multiset_prod_pos {R} [CanonicallyOrderedCommSemiring R]
    [Nontrivial R] {m : Multiset R} : 0 < m.prod ↔ (∀ x ∈ m, (0 : R) < x) := by
  rcases m with ⟨l⟩
  -- ⊢ 0 < Multiset.prod (Quot.mk Setoid.r l) ↔ ∀ (x : R), x ∈ Quot.mk Setoid.r l → …
  rw [Multiset.quot_mk_to_coe'', Multiset.coe_prod]
  -- ⊢ 0 < List.prod l ↔ ∀ (x : R), x ∈ ↑l → 0 < x
  exact CanonicallyOrderedCommSemiring.list_prod_pos
  -- 🎉 no goals

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring α] (s : Multiset α)

theorem multiset_sum_right (a : α) (h : ∀ b ∈ s, Commute a b) : Commute a s.sum := by
  induction s using Quotient.inductionOn
  -- ⊢ Commute a (sum (Quotient.mk (List.isSetoid α) a✝))
  rw [quot_mk_to_coe, coe_sum]
  -- ⊢ Commute a (List.sum a✝)
  exact Commute.list_sum_right _ _ h
  -- 🎉 no goals
#align commute.multiset_sum_right Commute.multiset_sum_right

theorem multiset_sum_left (b : α) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b :=
  ((Commute.multiset_sum_right _ _) fun _ ha => (h _ ha).symm).symm
#align commute.multiset_sum_left Commute.multiset_sum_left

end Commute
