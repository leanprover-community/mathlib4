/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Algebra.BigOperators.Monoid.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Rotate

/-!
# Sums and products from lists

This file provides further results about `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List


section Group

variable [Group G]

lemma prod_rotate_eq_one_of_prod_eq_one :
    ∀ {l : List G} (_ : l.prod = 1) (n : ℕ), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl
    rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq,
      ← one_mul (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_cancel, mul_one]

end Group

variable [DecidableEq α]

end List


namespace List

section Alternating

variable [CommGroup α]

@[to_additive]
theorem alternatingProd_append :
    ∀ l₁ l₂ : List α,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternatingProd_cons, alternatingProd_append, length_cons, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]

@[to_additive]
theorem alternatingProd_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternatingProd_nil, one_zpow, reverse_nil]
  | a :: l => by
    simp_rw [reverse_cons, alternatingProd_append, alternatingProd_reverse,
      alternatingProd_singleton, alternatingProd_cons, length_reverse, length, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]

end Alternating

end List
