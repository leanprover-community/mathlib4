/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `Multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the cartesian product `Multiset.product`.
* `Multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

assert_not_exists MonoidWithZero

variable {F ι M N : Type*}

namespace Multiset

section CommMonoid

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

/-- Product of a multiset given a commutative monoid structure on `M`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      /-- Sum of a multiset given a commutative additive monoid structure on `M`.
      `sum {a, b, c} = a + b + c` -/]
def prod : Multiset M → M :=
  foldr (· * ·) 1

@[to_additive]
theorem prod_eq_foldr (s : Multiset M) :
    prod s = foldr (· * ·) 1 s :=
  rfl

@[to_additive]
theorem prod_eq_foldl (s : Multiset M) :
    prod s = foldl (· * ·) 1 s :=
  (foldr_swap _ _ _).trans (by simp [mul_comm])

@[to_additive (attr := simp, norm_cast)]
theorem prod_coe (l : List M) : prod ↑l = l.prod := rfl

@[to_additive (attr := simp)]
theorem prod_toList (s : Multiset M) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [prod_coe]

@[to_additive (attr := simp, grind =)]
theorem prod_zero : @prod M _ 0 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _

@[to_additive (attr := simp)]
theorem prod_singleton (a : M) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, prod_zero]

@[to_additive]
theorem prod_pair (a b : M) : ({a, b} : Multiset M).prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]

@[to_additive]
theorem pow_count [DecidableEq M] (a : M) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, prod_replicate]

@[to_additive]
theorem prod_hom_rel (s : Multiset ι) {r : M → N → Prop} {f : ι → M} {g : ι → N}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).prod (s.map g).prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, map_coe, prod_coe]

@[to_additive]
theorem prod_map_one : prod (m.map fun _ => (1 : M)) = 1 := by
  rw [map_const', prod_replicate, one_pow]

@[to_additive]
theorem prod_induction (p : M → Prop) (s : Multiset M) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.prod := by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) 1 p s p_mul p_one p_s

@[to_additive]
theorem prod_induction_nonempty (p : M → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

end CommMonoid

end Multiset
