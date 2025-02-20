/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.BigOperators.Monoid.List.Basic

/-!
# Sums and products from lists

This file provides basic results about `List.prod`, `List.sum`, which calculate the product and sum
of elements of a list and `List.alternatingProd`, `List.alternatingSum`, their alternating
counterparts.
-/
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section CommMonoid
variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}



section Group

variable [Group G]

/-- This is the `List.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `List.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_inv_reverse xs]

/-- A non-commutative variant of `List.prod_reverse` -/
@[to_additive "A non-commutative variant of `List.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹ := by
  simp [prod_inv_reverse]

/-- Counterpart to `List.prod_take_succ` when we have an inverse operation -/
@[to_additive (attr := simp)
  "Counterpart to `List.sum_take_succ` when we have a negation operation"]
theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p : i < L.length), (L.drop (i + 1)).prod = L[i]⁻¹ * (L.drop i).prod
  | [], _, p => False.elim (Nat.not_lt_zero _ p)
  | _ :: _, 0, _ => by simp
  | _ :: xs, i + 1, p => prod_drop_succ xs i (Nat.lt_of_succ_lt_succ p)

/-- Cancellation of a telescoping product. -/
@[to_additive "Cancellation of a telescoping sum."]
theorem prod_range_div' (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f k / f (k + 1)).prod = f 0 / f n := by
  induction n with
  | zero => exact (div_self' (f 0)).symm
  | succ n h =>
    rw [range_succ, map_append, map_singleton, prod_append, prod_singleton, h, div_mul_div_cancel]

end Group

section CommGroup

variable [CommGroup G]

/-- This is the `List.prod` version of `mul_inv` -/
@[to_additive "This is the `List.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]

/-- Cancellation of a telescoping product. -/
@[to_additive "Cancellation of a telescoping sum."]
theorem prod_range_div (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f (k + 1) / f k).prod = f n / f 0 := by
  have h : ((·⁻¹) ∘ fun k ↦ f (k + 1) / f k) = fun k ↦ f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj, prod_inv, map_map, inv_div, h, prod_range_div']

/-- Alternative version of `List.prod_set` when the list is over a group -/
@[to_additive "Alternative version of `List.sum_set` when the list is over a group"]
theorem prod_set' (L : List G) (n : ℕ) (a : G) :
    (L.set n a).prod = L.prod * if hn : n < L.length then L[n]⁻¹ * a else 1 := by
  refine (prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp only [take_of_length_le (le_of_not_lt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_lt hn).trans n.le_succ)]

@[to_additive]
lemma prod_map_ite_eq {A : Type*} [DecidableEq A] (l : List A) (f g : A → G) (a : A) :
    (l.map fun x => if x = a then f x else g x).prod
      = (f a / g a) ^ (l.count a) * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, nodup_cons, ne_eq, mem_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, div_pow, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm, mul_inv_cancel_left, beq_self_eq_true]
    · simp only [hx, ite_false, ne_comm.mp hx, add_zero, mul_assoc, mul_comm (g x) _, beq_iff_eq]

end CommGroup


section Alternating

section

variable [One α] [Mul α] [Inv α]

@[to_additive (attr := simp)]
theorem alternatingProd_nil : alternatingProd ([] : List α) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem alternatingProd_singleton (a : α) : alternatingProd [a] = a :=
  rfl

@[to_additive]
theorem alternatingProd_cons_cons' (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl

end

@[to_additive]
theorem alternatingProd_cons_cons [DivInvMonoid α] (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons_cons']

variable [CommGroup α]

@[to_additive]
theorem alternatingProd_cons' :
    ∀ (a : α) (l : List α), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternatingProd_nil, inv_one, mul_one, alternatingProd_singleton]
  | a, b :: l => by
    rw [alternatingProd_cons_cons', alternatingProd_cons' b l, mul_inv, inv_inv, mul_assoc]

@[to_additive (attr := simp)]
theorem alternatingProd_cons (a : α) (l : List α) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons']

end Alternating

end CommMonoid

end List
