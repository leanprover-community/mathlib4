/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best

! This file was ported from Lean 3 source module data.list.big_operators.basic
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Forall2

/-!
# Sums and products from lists

This file provides basic results about `list.prod`, `list.sum`, which calculate the product and sum
of elements of a list and `list.alternating_prod`, `list.alternating_sum`, their alternating
counterparts. These are defined in [`data.list.defs`](./defs).
-/


variable {ι α M N P M₀ G R : Type _}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[simp, to_additive]
theorem prod_nil : ([] : List M).Prod = 1 :=
  rfl
#align list.prod_nil List.prod_nil

@[to_additive]
theorem prod_singleton : [a].Prod = a :=
  one_mul a
#align list.prod_singleton List.prod_singleton

@[simp, to_additive]
theorem prod_cons : (a :: l).Prod = a * l.Prod :=
  calc
    (a :: l).Prod = foldl (· * ·) (a * 1) l := by
      simp only [List.prod, foldl_cons, one_mul, mul_one]
    _ = _ := foldl_assoc
    
#align list.prod_cons List.prod_cons

@[simp, to_additive]
theorem prod_append : (l₁ ++ l₂).Prod = l₁.Prod * l₂.Prod :=
  calc
    (l₁ ++ l₂).Prod = foldl (· * ·) (foldl (· * ·) 1 l₁ * 1) l₂ := by simp [List.prod]
    _ = l₁.Prod * l₂.Prod := foldl_assoc
    
#align list.prod_append List.prod_append

@[to_additive]
theorem prod_concat : (l.concat a).Prod = l.Prod * a := by
  rw [concat_eq_append, prod_append, prod_singleton]
#align list.prod_concat List.prod_concat

@[simp, to_additive]
theorem prod_join {l : List (List M)} : l.join.Prod = (l.map List.prod).Prod := by
  induction l <;> [rfl, simp only [*, List.join, map, prod_append, prod_cons]]
#align list.prod_join List.prod_join

@[to_additive]
theorem prod_eq_foldr : l.Prod = foldr (· * ·) 1 l :=
  (List.recOn l rfl) fun a l ihl => by rw [prod_cons, foldr_cons, ihl]
#align list.prod_eq_foldr List.prod_eq_foldr

@[simp, to_additive]
theorem prod_repeat (a : M) (n : ℕ) : (repeat a n).Prod = a ^ n :=
  by
  induction' n with n ih
  · rw [pow_zero]
    rfl
  · rw [List.repeat_succ, List.prod_cons, ih, pow_succ]
#align list.prod_repeat List.prod_repeat

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.Prod = m ^ l.length := by
  rw [← prod_repeat, ← list.eq_repeat.mpr ⟨rfl, h⟩]
#align list.prod_eq_pow_card List.prod_eq_pow_card

@[to_additive]
theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).Prod (l.map g).Prod :=
  List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]
#align list.prod_hom_rel List.prod_hom_rel

@[to_additive]
theorem prod_hom (l : List M) {F : Type _} [MonoidHomClass F M N] (f : F) :
    (l.map f).Prod = f l.Prod :=
  by
  simp only [Prod, foldl_map, ← map_one f]
  exact l.foldl_hom _ _ _ 1 (map_mul f)
#align list.prod_hom List.prod_hom

@[to_additive]
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
    (l.map fun i => f (f₁ i) (f₂ i)).Prod = f (l.map f₁).Prod (l.map f₂).Prod :=
  by
  simp only [Prod, foldl_map]
  convert l.foldl_hom₂ (fun a b => f a b) _ _ _ _ _ fun a b i => _
  · exact hf'.symm
  · exact hf _ _ _ _
#align list.prod_hom₂ List.prod_hom₂

@[simp, to_additive]
theorem prod_map_mul {α : Type _} [CommMonoid α] {l : List ι} {f g : ι → α} :
    (l.map fun i => f i * g i).Prod = (l.map f).Prod * (l.map g).Prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align list.prod_map_mul List.prod_map_mul

@[simp]
theorem prod_map_neg {α} [CommMonoid α] [HasDistribNeg α] (l : List α) :
    (l.map Neg.neg).Prod = (-1) ^ l.length * l.Prod :=
  by
  convert @prod_map_mul α α _ l (fun _ => -1) id
  · ext
    rw [neg_one_mul]
    rfl
  · convert (prod_repeat _ _).symm
    rw [eq_repeat]
    use l.length_map _
    intro
    rw [mem_map]
    rintro ⟨_, _, rfl⟩
    rfl
  · rw [l.map_id]
#align list.prod_map_neg List.prod_map_neg

@[to_additive]
theorem prod_map_hom (L : List ι) (f : ι → M) {G : Type _} [MonoidHomClass G M N] (g : G) :
    (L.map (g ∘ f)).Prod = g (L.map f).Prod := by rw [← prod_hom, map_map]
#align list.prod_map_hom List.prod_map_hom

@[to_additive]
theorem prod_is_unit : ∀ {L : List M} (u : ∀ m ∈ L, IsUnit m), IsUnit L.Prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_is_unit fun m mt => u m (mem_cons_of_mem h mt))
#align list.prod_is_unit List.prod_is_unit

@[to_additive]
theorem prod_is_unit_iff {α : Type _} [CommMonoid α] {L : List α} :
    IsUnit L.Prod ↔ ∀ m ∈ L, IsUnit m :=
  by
  refine' ⟨fun h => _, prod_is_unit⟩
  induction' L with m L ih
  · exact fun m' h' => False.elim (not_mem_nil m' h')
  rw [prod_cons, IsUnit.mul_iff] at h
  exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H
#align list.prod_is_unit_iff List.prod_is_unit_iff

@[simp, to_additive]
theorem prod_take_mul_prod_drop : ∀ (L : List M) (i : ℕ), (L.take i).Prod * (L.drop i).Prod = L.Prod
  | [], i => by simp [Nat.zero_le]
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop]
#align list.prod_take_mul_prod_drop List.prod_take_mul_prod_drop

@[simp, to_additive]
theorem prod_take_succ :
    ∀ (L : List M) (i : ℕ) (p), (L.take (i + 1)).Prod = (L.take i).Prod * L.nthLe i p
  | [], i, p => by cases p
  | h :: t, 0, _ => by simp
  | h :: t, n + 1, _ => by
    dsimp
    rw [prod_cons, prod_cons, prod_take_succ, mul_assoc]
#align list.prod_take_succ List.prod_take_succ

/-- A list with product not one must have positive length. -/
@[to_additive "A list with sum not zero must have positive length."]
theorem length_pos_of_prod_ne_one (L : List M) (h : L.Prod ≠ 1) : 0 < L.length :=
  by
  cases L
  · contrapose h
    simp
  · simp
#align list.length_pos_of_prod_ne_one List.length_pos_of_prod_ne_one

/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos "A list with positive sum must have positive length."]
theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.Prod) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne'
#align list.length_pos_of_one_lt_prod List.length_pos_of_one_lt_prod

/-- A list with product less than one must have positive length. -/
@[to_additive "A list with negative sum must have positive length."]
theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.Prod < 1) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.Ne
#align list.length_pos_of_prod_lt_one List.length_pos_of_prod_lt_one

@[to_additive]
theorem prod_update_nth :
    ∀ (L : List M) (n : ℕ) (a : M),
      (L.updateNth n a).Prod =
        ((L.take n).Prod * if n < L.length then a else 1) * (L.drop (n + 1)).Prod
  | x :: xs, 0, a => by simp [update_nth]
  | x :: xs, i + 1, a => by simp [update_nth, prod_update_nth xs i a, mul_assoc]
  | [], _, _ => by simp [update_nth, (Nat.zero_le _).not_lt, Nat.zero_le]
#align list.prod_update_nth List.prod_update_nth

open MulOpposite

/-- We'd like to state this as `L.head * L.tail.prod = L.prod`, but because `L.head` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.nth 0).get_or_else 1`.
-/
@[to_additive
      "We'd like to state this as `L.head + L.tail.sum = L.sum`, but because `L.head`\nrelies on an inhabited instance to return a garbage value on the empty list, this is not possible.\nInstead, we write the statement in terms of `(L.nth 0).get_or_else 0`."]
theorem nth_zero_mul_tail_prod (l : List M) : (l.nth 0).getOrElse 1 * l.tail.Prod = l.Prod := by
  cases l <;> simp
#align list.nth_zero_mul_tail_prod List.nth_zero_mul_tail_prod

/-- Same as `nth_zero_mul_tail_prod`, but avoiding the `list.head` garbage complication by requiring
the list to be nonempty. -/
@[to_additive
      "Same as `nth_zero_add_tail_sum`, but avoiding the `list.head` garbage complication\nby requiring the list to be nonempty."]
theorem head_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.head * l.tail.Prod = l.Prod := by cases l <;> [contradiction, simp]
#align list.head_mul_tail_prod_of_ne_nil List.head_mul_tail_prod_of_ne_nil

@[to_additive]
theorem Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.Prod := by
  induction' l with z l IH
  · simp
  · rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)
#align commute.list_prod_right Commute.list_prod_right

@[to_additive]
theorem Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) : Commute l.Prod y :=
  ((Commute.list_prod_right _ _) fun x hx => (h _ hx).symm).symm
#align commute.list_prod_left Commute.list_prod_left

@[to_additive sum_le_sum]
theorem Forall₂.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.Prod ≤ l₂.Prod := by
  induction' h with a b la lb hab ih ih'
  · rfl
  · simpa only [prod_cons] using mul_le_mul' hab ih'
#align list.forall₂.prod_le_prod' List.Forall₂.prod_le_prod'

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum
      "If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,\nthen `l₁.sum ≤ l₂.sum`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead\nof `∀ a ∈ l₂, 0 ≤ a` but this lemma is not yet in `mathlib`."]
theorem Sublist.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.Prod ≤ l₂.Prod :=
  by
  induction h; · rfl
  case cons l₁ l₂ a ih ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  case cons2 l₁ l₂ a ih ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁⊢
    exact mul_le_mul_left' (ih' h₁.2) _
#align list.sublist.prod_le_prod' List.Sublist.prod_le_prod'

@[to_additive sum_le_sum]
theorem SublistForall₂.prod_le_prod' [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.Prod ≤ l₂.Prod :=
  let ⟨l, hall, hsub⟩ := sublist_forall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁
#align list.sublist_forall₂.prod_le_prod' List.SublistForall₂.prod_le_prod'

@[to_additive sum_le_sum]
theorem prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).Prod ≤ (l.map g).Prod :=
  forall₂.prod_le_prod' <| by simpa
#align list.prod_le_prod' List.prod_le_prod'

@[to_additive sum_lt_sum]
theorem prod_lt_prod' [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).Prod < (l.map g).Prod :=
  by
  induction' l with i l ihl; · rcases h₂ with ⟨_, ⟨⟩, _⟩
  simp only [ball_cons, bex_cons, map_cons, prod_cons] at h₁ h₂⊢
  cases h₂
  exacts[mul_lt_mul_of_lt_of_le h₂ (prod_le_prod' h₁.2), mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 h₂]
#align list.prod_lt_prod' List.prod_lt_prod'

@[to_additive]
theorem prod_lt_prod_of_ne_nil [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (hlt : ∀ i ∈ l, f i < g i) : (l.map f).Prod < (l.map g).Prod :=
  (prod_lt_prod' f g fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩
#align list.prod_lt_prod_of_ne_nil List.prod_lt_prod_of_ne_nil

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.Prod ≤ n ^ l.length := by simpa only [map_id'', map_const, prod_repeat] using prod_le_prod' h
#align list.prod_le_pow_card List.prod_le_pow_card

@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' [LinearOrder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h : (l.map f).Prod < (l.map g).Prod) : ∃ i ∈ l, f i < g i :=
  by
  contrapose! h
  exact prod_le_prod' h
#align list.exists_lt_of_prod_lt' List.exists_lt_of_prod_lt'

@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' [LinearOrder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).Prod ≤ (l.map g).Prod) : ∃ x ∈ l, f x ≤ g x :=
  by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h
#align list.exists_le_of_prod_le' List.exists_le_of_prod_le'

@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.Prod :=
  by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [covariant_class M M (function.swap (*)) (≤)]
  induction' l with hd tl ih;
  · rfl
  rw [prod_cons]
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))
#align list.one_le_prod_of_one_le List.one_le_prod_of_one_le

end Monoid

section MonoidWithZero

variable [MonoidWithZero M₀]

/-- If zero is an element of a list `L`, then `list.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`list.prod_eq_zero_iff`. -/
theorem prod_eq_zero {L : List M₀} (h : (0 : M₀) ∈ L) : L.Prod = 0 :=
  by
  induction' L with a L ihL
  · exact absurd h (not_mem_nil _)
  · rw [prod_cons]
    cases' (mem_cons_iff _ _ _).1 h with ha hL
    exacts[mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)]
#align list.prod_eq_zero List.prod_eq_zero

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`list.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp]
theorem prod_eq_zero_iff [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} :
    L.Prod = 0 ↔ (0 : M₀) ∈ L := by
  induction' L with a L ihL
  · simp
  · rw [prod_cons, mul_eq_zero, ihL, mem_cons_iff, eq_comm]
#align list.prod_eq_zero_iff List.prod_eq_zero_iff

theorem prod_ne_zero [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} (hL : (0 : M₀) ∉ L) :
    L.Prod ≠ 0 :=
  mt prod_eq_zero_iff.1 hL
#align list.prod_ne_zero List.prod_ne_zero

end MonoidWithZero

section Group

variable [Group G]

/-- This is the `list.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `list.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List G, L.Prod⁻¹ = (L.map fun x => x⁻¹).reverse.Prod
  | [] => by simp
  | x :: xs => by simp [prod_inv_reverse xs]
#align list.prod_inv_reverse List.prod_inv_reverse

/-- A non-commutative variant of `list.prod_reverse` -/
@[to_additive "A non-commutative variant of `list.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.Prod = (L.map fun x => x⁻¹).Prod⁻¹ := by
  simp [prod_inv_reverse]
#align list.prod_reverse_noncomm List.prod_reverse_noncomm

/-- Counterpart to `list.prod_take_succ` when we have an inverse operation -/
@[simp, to_additive "Counterpart to `list.sum_take_succ` when we have an negation operation"]
theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p), (L.drop (i + 1)).Prod = (L.nthLe i p)⁻¹ * (L.drop i).Prod
  | [], i, p => False.elim (Nat.not_lt_zero _ p)
  | x :: xs, 0, p => by simp
  | x :: xs, i + 1, p => prod_drop_succ xs i _
#align list.prod_drop_succ List.prod_drop_succ

end Group

section CommGroup

variable [CommGroup G]

/-- This is the `list.prod` version of `mul_inv` -/
@[to_additive "This is the `list.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List G, L.Prod⁻¹ = (L.map fun x => x⁻¹).Prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]
#align list.prod_inv List.prod_inv

/-- Alternative version of `list.prod_update_nth` when the list is over a group -/
@[to_additive "Alternative version of `list.sum_update_nth` when the list is over a group"]
theorem prod_update_nth' (L : List G) (n : ℕ) (a : G) :
    (L.updateNth n a).Prod = L.Prod * if hn : n < L.length then (L.nthLe n hn)⁻¹ * a else 1 :=
  by
  refine' (prod_update_nth L n a).trans _
  split_ifs with hn hn
  ·
    rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).Prod, ←
      mul_assoc (take n L).Prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  ·
    simp only [take_all_of_le (le_of_not_lt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_lt hn).trans n.le_succ)]
#align list.prod_update_nth' List.prod_update_nth'

end CommGroup

@[to_additive]
theorem eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).Prod = (L'.take i).Prod) : L = L' :=
  by
  apply ext_le h fun i h₁ h₂ => _
  have : (L.take (i + 1)).Prod = (L'.take (i + 1)).Prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (le_of_lt h₁)] at this
  convert mul_left_cancel this
#align list.eq_of_prod_take_eq List.eq_of_prod_take_eq

@[to_additive]
theorem monotone_prod_take [CanonicallyOrderedMonoid M] (L : List M) :
    Monotone fun i => (L.take i).Prod :=
  by
  apply monotone_nat_of_le_succ fun n => _
  cases' lt_or_le n L.length with h h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_all_of_le h, take_all_of_le (le_trans h (Nat.le_succ _))]
#align list.monotone_prod_take List.monotone_prod_take

@[to_additive sum_pos]
theorem one_lt_prod_of_one_lt [OrderedCommMonoid M] :
    ∀ (l : List M) (hl : ∀ x ∈ l, (1 : M) < x) (hl₂ : l ≠ []), 1 < l.Prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
  | a :: b :: l, hl₁, hl₂ =>
    by
    simp only [forall_eq_or_imp, List.mem_cons _ a] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt hl₁.2 (l.cons_ne_nil b))
#align list.one_lt_prod_of_one_lt List.one_lt_prod_of_one_lt

@[to_additive]
theorem single_le_prod [OrderedCommMonoid M] {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
    ∀ x ∈ l, x ≤ l.Prod := by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁⊢
  constructor
  · exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  · exact fun x H => le_mul_of_one_le_of_le hl₁.1 (l_ih hl₁.right x H)
#align list.single_le_prod List.single_le_prod

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one [OrderedCommMonoid M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.Prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)
#align list.all_one_of_le_one_le_of_prod_eq_one List.all_one_of_le_one_le_of_prod_eq_one

/-- Slightly more general version of `list.prod_eq_one_iff` for a non-ordered `monoid` -/
@[to_additive
      "Slightly more general version of `list.sum_eq_zero_iff`\n  for a non-ordered `add_monoid`"]
theorem prod_eq_one [Monoid M] {l : List M} (hl : ∀ x ∈ l, x = (1 : M)) : l.Prod = 1 :=
  by
  induction' l with i l hil
  · rfl
  rw [List.prod_cons, hil fun x hx => hl _ (mem_cons_of_mem i hx), hl _ (mem_cons_self i l),
    one_mul]
#align list.prod_eq_one List.prod_eq_one

@[to_additive]
theorem exists_mem_ne_one_of_prod_ne_one [Monoid M] {l : List M} (h : l.Prod ≠ 1) :
    ∃ x ∈ l, x ≠ (1 : M) := by simpa only [not_forall] using mt prod_eq_one h
#align list.exists_mem_ne_one_of_prod_ne_one List.exists_mem_ne_one_of_prod_ne_one

-- TODO: develop theory of tropical rings
theorem sum_le_foldr_max [AddMonoid M] [AddMonoid N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.Sum ≤ (l.map f).foldr max 0 :=
  by
  induction' l with hd tl IH
  · simpa using h0
  simp only [List.sum_cons, List.foldr_map, List.foldr] at IH⊢
  exact (hadd _ _).trans (max_le_max le_rfl IH)
#align list.sum_le_foldr_max List.sum_le_foldr_max

@[simp, to_additive]
theorem prod_erase [DecidableEq M] [CommMonoid M] {a} :
    ∀ {l : List M}, a ∈ l → a * (l.erase a).Prod = l.Prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    · simp only [List.erase, if_pos, prod_cons]
    · simp only [List.erase, if_neg (mt Eq.symm Ne), prod_cons, prod_erase h, mul_left_comm a b]
#align list.prod_erase List.prod_erase

@[simp, to_additive]
theorem prod_map_erase [DecidableEq ι] [CommMonoid M] (f : ι → M) {a} :
    ∀ {l : List ι}, a ∈ l → f a * ((l.erase a).map f).Prod = (l.map f).Prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    ·
      simp only [map, erase_cons_tail _ Ne.symm, prod_cons, prod_map_erase h,
        mul_left_comm (f a) (f b)]
#align list.prod_map_erase List.prod_map_erase

@[simp]
theorem sum_const_nat (m n : ℕ) : sum (List.repeat m n) = m * n := by
  induction n <;> [rfl, simp only [*, repeat_succ, sum_cons, Nat.mul_succ, add_comm]]
#align list.sum_const_nat List.sum_const_nat

/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
theorem prod_pos [StrictOrderedSemiring R] (l : List R) (h : ∀ a ∈ l, (0 : R) < a) : 0 < l.Prod :=
  by
  induction' l with a l ih
  · simp
  · rw [prod_cons]
    exact mul_pos (h _ <| mem_cons_self _ _) (ih fun a ha => h a <| mem_cons_of_mem _ ha)
#align list.prod_pos List.prod_pos

/-!
Several lemmas about sum/head/tail for `list ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/


/-- This relies on `default ℕ = 0`. -/
theorem head_add_tail_sum (L : List ℕ) : L.head + L.tail.Sum = L.Sum :=
  by
  cases L
  · simp
    rfl
  · simp
#align list.head_add_tail_sum List.head_add_tail_sum

/-- This relies on `default ℕ = 0`. -/
theorem head_le_sum (L : List ℕ) : L.head ≤ L.Sum :=
  Nat.le.intro (head_add_tail_sum L)
#align list.head_le_sum List.head_le_sum

/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.Sum = L.Sum - L.head := by
  rw [← head_add_tail_sum L, add_comm, add_tsub_cancel_right]
#align list.tail_sum List.tail_sum

section Alternating

section

variable [One α] [Mul α] [Inv α]

@[simp, to_additive]
theorem alternating_prod_nil : alternatingProd ([] : List α) = 1 :=
  rfl
#align list.alternating_prod_nil List.alternating_prod_nil

@[simp, to_additive]
theorem alternating_prod_singleton (a : α) : alternatingProd [a] = a :=
  rfl
#align list.alternating_prod_singleton List.alternating_prod_singleton

@[to_additive]
theorem alternating_prod_cons_cons' (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl
#align list.alternating_prod_cons_cons' List.alternating_prod_cons_cons'

end

@[to_additive]
theorem alternating_prod_cons_cons [DivInvMonoid α] (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, alternating_prod_cons_cons']
#align list.alternating_prod_cons_cons List.alternating_prod_cons_cons

variable [CommGroup α]

@[to_additive]
theorem alternating_prod_cons' :
    ∀ (a : α) (l : List α), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternating_prod_nil, inv_one, mul_one, alternating_prod_singleton]
  | a, b :: l => by
    rw [alternating_prod_cons_cons', alternating_prod_cons' b l, mul_inv, inv_inv, mul_assoc]
#align list.alternating_prod_cons' List.alternating_prod_cons'

@[simp, to_additive]
theorem alternating_prod_cons (a : α) (l : List α) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternating_prod_cons']
#align list.alternating_prod_cons List.alternating_prod_cons

end Alternating

end List

section MonoidHom

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map_list_prod {F : Type _} [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.Prod = (l.map f).Prod :=
  (l.prod_hom f).symm
#align map_list_prod map_list_prod

namespace MonoidHom

/-- Deprecated, use `_root_.map_list_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_list_sum` instead."]
protected theorem map_list_prod (f : M →* N) (l : List M) : f l.Prod = (l.map f).Prod :=
  map_list_prod f l
#align monoid_hom.map_list_prod MonoidHom.map_list_prod

end MonoidHom

end MonoidHom

