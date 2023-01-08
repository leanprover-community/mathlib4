/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best

! This file was ported from Lean 3 source module data.list.big_operators.lemmas
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic
import Mathbin.Algebra.Group.Opposite
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.GroupWithZero.Commute
import Mathbin.Algebra.GroupWithZero.Divisibility
import Mathbin.Algebra.Order.WithZero
import Mathbin.Algebra.Ring.Basic
import Mathbin.Algebra.Ring.Divisibility
import Mathbin.Algebra.Ring.Commute
import Mathbin.Data.Int.Units
import Mathbin.Data.Set.Basic

/-! # Lemmas about `list.sum` and `list.prod` requiring extra algebra imports -/


open MulOpposite List

variable {ι α M N P M₀ G R : Type _}

namespace Commute

theorem list_sum_right [NonUnitalNonAssocSemiring R] (a : R) (l : List R)
    (h : ∀ b ∈ l, Commute a b) : Commute a l.Sum :=
  by
  induction' l with x xs ih
  · exact Commute.zero_right _
  · rw [List.sum_cons]
    exact (h _ <| mem_cons_self _ _).add_right (ih fun j hj => h _ <| mem_cons_of_mem _ hj)
#align commute.list_sum_right Commute.list_sum_right

theorem list_sum_left [NonUnitalNonAssocSemiring R] (b : R) (l : List R)
    (h : ∀ a ∈ l, Commute a b) : Commute l.Sum b :=
  ((Commute.list_sum_right _ _) fun x hx => (h _ hx).symm).symm
#align commute.list_sum_left Commute.list_sum_left

end Commute

namespace List

@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod [Monoid M] [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) : n ^ l.length ≤ l.Prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h
#align list.pow_card_le_prod List.pow_card_le_prod

@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid M] (l : List M) :
    l.Prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, fun h => by
    rw [eq_repeat.2 ⟨rfl, h⟩, prod_repeat, one_pow]⟩
#align list.prod_eq_one_iff List.prod_eq_one_iff

/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.Prod = -1) : (-1 : ℤ) ∈ l :=
  by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact
    Or.resolve_left
        (int.is_unit_iff.mp
          (prod_is_unit_iff.mp (h.symm ▸ IsUnit.neg isUnit_one : IsUnit l.prod) x h₁))
        h₂ ▸
      h₁
#align list.neg_one_mem_of_prod_eq_neg_one List.neg_one_mem_of_prod_eq_neg_one

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.Sum :=
  by
  induction' L with j L IH h; · simp
  rw [sum_cons, length, add_comm]
  exact add_le_add (h _ (Set.mem_insert _ _)) (IH fun i hi => h i (Set.mem_union_right _ hi))
#align list.length_le_sum_of_one_le List.length_le_sum_of_one_le

theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.Prod :=
  by
  let ⟨s, t, h⟩ := mem_split ha
  rw [h, prod_append, prod_cons, mul_left_comm]
  exact dvd_mul_right _ _
#align list.dvd_prod List.dvd_prod

theorem dvd_sum [Semiring R] {a} {l : List R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.Sum :=
  by
  induction' l with x l ih
  · exact dvd_zero _
  · rw [List.sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun x hx => h x (mem_cons_of_mem _ hx))
#align list.dvd_sum List.dvd_sum

section Alternating

variable [CommGroup α]

@[to_additive]
theorem alternating_prod_append :
    ∀ l₁ l₂ : List α,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternating_prod_cons, alternating_prod_append, length_cons, pow_succ,
      neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]
#align list.alternating_prod_append List.alternating_prod_append

@[to_additive]
theorem alternating_prod_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternating_prod_nil, one_zpow, reverse_nil]
  | a :: l =>
    by
    simp_rw [reverse_cons, alternating_prod_append, alternating_prod_reverse,
      alternating_prod_singleton, alternating_prod_cons, length_reverse, length, pow_succ, neg_mul,
      one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]
#align list.alternating_prod_reverse List.alternating_prod_reverse

end Alternating

theorem sum_map_mul_left [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => r * f b).Sum = r * (L.map f).Sum :=
  sum_map_hom L f <| AddMonoidHom.mulLeft r
#align list.sum_map_mul_left List.sum_map_mul_left

theorem sum_map_mul_right [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => f b * r).Sum = (L.map f).Sum * r :=
  sum_map_hom L f <| AddMonoidHom.mulRight r
#align list.sum_map_mul_right List.sum_map_mul_right

end List

namespace MulOpposite

open List

variable [Monoid M]

theorem op_list_prod : ∀ l : List M, op l.Prod = (l.map op).reverse.Prod
  | [] => rfl
  | x :: xs => by
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, op_list_prod]
#align mul_opposite.op_list_prod MulOpposite.op_list_prod

theorem MulOpposite.unop_list_prod (l : List Mᵐᵒᵖ) : l.Prod.unop = (l.map unop).reverse.Prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse,
    op_comp_unop, map_id]
#align mul_opposite.unop_list_prod MulOpposite.unop_list_prod

end MulOpposite

section MonoidHom

variable [Monoid M] [Monoid N]

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
theorem unop_map_list_prod {F : Type _} [MonoidHomClass F M Nᵐᵒᵖ] (f : F) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]
#align unop_map_list_prod unop_map_list_prod

namespace MonoidHom

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements.

Deprecated, use `_root_.unop_map_list_prod` instead. -/
protected theorem unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  unop_map_list_prod f l
#align monoid_hom.unop_map_list_prod MonoidHom.unop_map_list_prod

end MonoidHom

end MonoidHom

