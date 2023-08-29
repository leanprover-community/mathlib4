/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.List.Forall2

#align_import data.list.big_operators.basic from "leanprover-community/mathlib"@"6c5f73fd6f6cc83122788a80a27cdd54663609f4"

/-!
# Sums and products from lists

This file provides basic results about `List.prod`, `List.sum`, which calculate the product and sum
of elements of a list and `List.alternating_prod`, `List.alternating_sum`, their alternating
counterparts. These are defined in [`Data.List.Defs`](./defs).
-/


variable {ι α M N P M₀ G R : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[to_additive (attr := simp)]
theorem prod_nil : ([] : List M).prod = 1 :=
  rfl
#align list.prod_nil List.prod_nil
#align list.sum_nil List.sum_nil

@[to_additive]
theorem prod_singleton : [a].prod = a :=
  one_mul a
#align list.prod_singleton List.prod_singleton
#align list.sum_singleton List.sum_singleton

@[to_additive (attr := simp)]
theorem prod_cons : (a :: l).prod = a * l.prod :=
  calc
    (a :: l).prod = foldl (· * ·) (a * 1) l :=
      by simp only [List.prod, foldl_cons, one_mul, mul_one]
         -- 🎉 no goals
    _ = _ := foldl_assoc
#align list.prod_cons List.prod_cons
#align list.sum_cons List.sum_cons

@[to_additive (attr := simp)]
theorem prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
  calc
    (l₁ ++ l₂).prod = foldl (· * ·) (foldl (· * ·) 1 l₁ * 1) l₂ := by simp [List.prod]
                                                                      -- 🎉 no goals
    _ = l₁.prod * l₂.prod := foldl_assoc
#align list.prod_append List.prod_append
#align list.sum_append List.sum_append

@[to_additive]
theorem prod_concat : (l.concat a).prod = l.prod * a := by
  rw [concat_eq_append, prod_append, prod_singleton]
  -- 🎉 no goals
#align list.prod_concat List.prod_concat
#align list.sum_concat List.sum_concat

@[to_additive (attr := simp)]
theorem prod_join {l : List (List M)} : l.join.prod = (l.map List.prod).prod := by
  induction l <;> [rfl; simp only [*, List.join, map, prod_append, prod_cons]]
  -- 🎉 no goals
#align list.prod_join List.prod_join
#align list.sum_join List.sum_join

@[to_additive]
theorem prod_eq_foldr : ∀ {l : List M}, l.prod = foldr (· * ·) 1 l
  | [] => rfl
  | cons a l => by rw [prod_cons, foldr_cons, prod_eq_foldr]
                   -- 🎉 no goals
#align list.prod_eq_foldr List.prod_eq_foldr
#align list.sum_eq_foldr List.sum_eq_foldr

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  induction' n with n ih
  -- ⊢ prod (replicate Nat.zero a) = a ^ Nat.zero
  · rw [pow_zero]
    -- ⊢ prod (replicate Nat.zero a) = 1
    rfl
    -- 🎉 no goals
  · rw [replicate_succ, prod_cons, ih, pow_succ]
    -- 🎉 no goals
#align list.prod_replicate List.prod_replicate
#align list.sum_replicate List.sum_replicate

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.prod = m ^ l.length := by
  rw [← prod_replicate, ← List.eq_replicate.mpr ⟨rfl, h⟩]
  -- 🎉 no goals
#align list.prod_eq_pow_card List.prod_eq_pow_card
#align list.sum_eq_card_nsmul List.sum_eq_card_nsmul

@[to_additive]
theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).prod (l.map g).prod :=
  List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]
                                   -- 🎉 no goals
#align list.prod_hom_rel List.prod_hom_rel
#align list.sum_hom_rel List.sum_hom_rel

@[to_additive]
theorem prod_hom (l : List M) {F : Type*} [MonoidHomClass F M N] (f : F) :
    (l.map f).prod = f l.prod := by
  simp only [prod, foldl_map, ← map_one f]
  -- ⊢ foldl (fun x y => x * ↑f y) (↑f 1) l = ↑f (foldl (fun x x_1 => x * x_1) 1 l)
  exact l.foldl_hom f (· * ·) (· * f ·) 1 (fun x y => (map_mul f x y).symm)
  -- 🎉 no goals
#align list.prod_hom List.prod_hom
#align list.sum_hom List.sum_hom

@[to_additive]
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  simp only [prod, foldl_map]
  -- ⊢ foldl (fun x y => x * f (f₁ y) (f₂ y)) 1 l = f (foldl (fun x y => x * f₁ y)  …
  -- Porting note: next 3 lines used to be
  -- convert l.foldl_hom₂ (fun a b => f a b) _ _ _ _ _ fun a b i => _
  -- · exact hf'.symm
  -- · exact hf _ _ _ _
  rw [← l.foldl_hom₂ (fun a b => f a b), hf']
  -- ⊢ ∀ (a : M) (b : N) (i : ι), f (a * f₁ i) (b * f₂ i) = f a b * f (f₁ i) (f₂ i)
  intros
  -- ⊢ f (a✝ * f₁ i✝) (b✝ * f₂ i✝) = f a✝ b✝ * f (f₁ i✝) (f₂ i✝)
  exact hf _ _ _ _
  -- 🎉 no goals
#align list.prod_hom₂ List.prod_hom₂
#align list.sum_hom₂ List.sum_hom₂

@[to_additive (attr := simp)]
theorem prod_map_mul {α : Type*} [CommMonoid α] {l : List ι} {f g : ι → α} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align list.prod_map_mul List.prod_map_mul
#align list.sum_map_add List.sum_map_add

@[simp]
theorem prod_map_neg {α} [CommMonoid α] [HasDistribNeg α] (l : List α) :
    (l.map Neg.neg).prod = (-1) ^ l.length * l.prod := by
  simpa only [id_eq, neg_mul, one_mul, map_const', prod_replicate, map_id]
    using @prod_map_mul α α _ l (fun _ => -1) id
#align list.prod_map_neg List.prod_map_neg

@[to_additive]
theorem prod_map_hom (L : List ι) (f : ι → M) {G : Type*} [MonoidHomClass G M N] (g : G) :
    (L.map (g ∘ f)).prod = g (L.map f).prod := by rw [← prod_hom, map_map]
                                                  -- 🎉 no goals
#align list.prod_map_hom List.prod_map_hom
#align list.sum_map_hom List.sum_map_hom

@[to_additive]
theorem prod_isUnit : ∀ {L : List M} (_ : ∀ m ∈ L, IsUnit m), IsUnit L.prod
  | [], _ => by simp
                -- 🎉 no goals
  | h :: t, u => by
    simp only [List.prod_cons]
    -- ⊢ IsUnit (h * prod t)
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))
    -- 🎉 no goals
#align list.prod_is_unit List.prod_isUnit
#align list.sum_is_add_unit List.sum_isAddUnit

@[to_additive]
theorem prod_isUnit_iff {α : Type*} [CommMonoid α] {L : List α} :
    IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m := by
  refine' ⟨fun h => _, prod_isUnit⟩
  -- ⊢ ∀ (m : α), m ∈ L → IsUnit m
  induction' L with m L ih
  -- ⊢ ∀ (m : α), m ∈ [] → IsUnit m
  · exact fun m' h' => False.elim (not_mem_nil m' h')
    -- 🎉 no goals
  rw [prod_cons, IsUnit.mul_iff] at h
  -- ⊢ ∀ (m_1 : α), m_1 ∈ m :: L → IsUnit m_1
  exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H
  -- 🎉 no goals
#align list.prod_is_unit_iff List.prod_isUnit_iff
#align list.sum_is_add_unit_iff List.sum_isAddUnit_iff

@[to_additive (attr := simp)]
theorem prod_take_mul_prod_drop : ∀ (L : List M) (i : ℕ), (L.take i).prod * (L.drop i).prod = L.prod
  | [], i => by simp [Nat.zero_le]
                -- 🎉 no goals
  | L, 0 => by simp
               -- 🎉 no goals
  | h :: t, n + 1 => by
    dsimp
    -- ⊢ prod (h :: take n t) * prod (drop n t) = prod (h :: t)
    rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop t]
    -- 🎉 no goals
#align list.prod_take_mul_prod_drop List.prod_take_mul_prod_drop
#align list.sum_take_add_sum_drop List.sum_take_add_sum_drop

@[to_additive (attr := simp)]
theorem prod_take_succ :
    ∀ (L : List M) (i : ℕ) (p), (L.take (i + 1)).prod = (L.take i).prod * L.nthLe i p
  | [], i, p => by cases p
                   -- 🎉 no goals
  | h :: t, 0, _ => rfl
  | h :: t, n + 1, p => by
    dsimp
    -- ⊢ prod (h :: take (n + 1) t) = prod (h :: take n t) * nthLe (h :: t) (n + 1) p
    rw [prod_cons, prod_cons, prod_take_succ t n (Nat.lt_of_succ_lt_succ p), mul_assoc,
      nthLe_cons, dif_neg (Nat.add_one_ne_zero _)]
    simp
    -- 🎉 no goals
#align list.prod_take_succ List.prod_take_succ
#align list.sum_take_succ List.sum_take_succ

/-- A list with product not one must have positive length. -/
@[to_additive "A list with sum not zero must have positive length."]
theorem length_pos_of_prod_ne_one (L : List M) (h : L.prod ≠ 1) : 0 < L.length := by
  cases L
  -- ⊢ 0 < length []
  · contrapose h
    -- ⊢ ¬prod [] ≠ 1
    simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align list.length_pos_of_prod_ne_one List.length_pos_of_prod_ne_one
#align list.length_pos_of_sum_ne_zero List.length_pos_of_sum_ne_zero

/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos "A list with positive sum must have positive length."]
theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.prod) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne'
#align list.length_pos_of_one_lt_prod List.length_pos_of_one_lt_prod
#align list.length_pos_of_sum_pos List.length_pos_of_sum_pos

/-- A list with product less than one must have positive length. -/
@[to_additive "A list with negative sum must have positive length."]
theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.prod < 1) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne
#align list.length_pos_of_prod_lt_one List.length_pos_of_prod_lt_one
#align list.length_pos_of_sum_neg List.length_pos_of_sum_neg

@[to_additive]
theorem prod_set :
    ∀ (L : List M) (n : ℕ) (a : M),
      (L.set n a).prod =
        ((L.take n).prod * if n < L.length then a else 1) * (L.drop (n + 1)).prod
  | x :: xs, 0, a => by simp [set]
                        -- 🎉 no goals
  | x :: xs, i + 1, a => by simp [set, prod_set xs i a, mul_assoc, Nat.succ_eq_add_one]
                            -- 🎉 no goals
  | [], _, _ => by simp [set, (Nat.zero_le _).not_lt, Nat.zero_le]
                   -- 🎉 no goals
#align list.prod_update_nth List.prod_set
#align list.sum_update_nth List.sum_set

open MulOpposite

/-- We'd like to state this as `L.headI * L.tail.prod = L.prod`, but because `L.headI` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.get? 0).getD 1`.
-/
@[to_additive "We'd like to state this as `L.headI + L.tail.sum = L.sum`, but because `L.headI`
  relies on an inhabited instance to return a garbage value on the empty list, this is not possible.
  Instead, we write the statement in terms of `(L.get? 0).getD 0`."]
theorem get?_zero_mul_tail_prod (l : List M) : (l.get? 0).getD 1 * l.tail.prod = l.prod := by
  cases l <;> simp
  -- ⊢ Option.getD (get? [] 0) 1 * prod (tail []) = prod []
              -- 🎉 no goals
              -- 🎉 no goals
#align list.nth_zero_mul_tail_prod List.get?_zero_mul_tail_prod
#align list.nth_zero_add_tail_sum List.get?_zero_add_tail_sum

/-- Same as `get?_zero_mul_tail_prod`, but avoiding the `List.headI` garbage complication by
  requiring the list to be nonempty. -/
@[to_additive "Same as `get?_zero_add_tail_sum`, but avoiding the `List.headI` garbage complication
  by requiring the list to be nonempty."]
theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.headI * l.tail.prod = l.prod := by cases l <;> [contradiction; simp]
                                         -- 🎉 no goals
#align list.head_mul_tail_prod_of_ne_nil List.headI_mul_tail_prod_of_ne_nil
#align list.head_add_tail_sum_of_ne_nil List.headI_add_tail_sum_of_ne_nil

@[to_additive]
theorem _root_.Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.prod := by
  induction' l with z l IH
  -- ⊢ Commute y (prod [])
  · simp
    -- 🎉 no goals
  · rw [List.forall_mem_cons] at h
    -- ⊢ Commute y (prod (z :: l))
    rw [List.prod_cons]
    -- ⊢ Commute y (z * prod l)
    exact Commute.mul_right h.1 (IH h.2)
    -- 🎉 no goals
#align commute.list_prod_right Commute.list_prod_right
#align add_commute.list_sum_right AddCommute.list_sum_right

@[to_additive]
theorem _root_.Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) :
    Commute l.prod y :=
  ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm
#align commute.list_prod_left Commute.list_prod_left
#align add_commute.list_sum_left AddCommute.list_sum_left

@[to_additive sum_le_sum]
theorem Forall₂.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.prod ≤ l₂.prod := by
  induction' h with a b la lb hab ih ih'
  -- ⊢ prod [] ≤ prod []
  · rfl
    -- 🎉 no goals
  · simpa only [prod_cons] using mul_le_mul' hab ih'
    -- 🎉 no goals
#align list.forall₂.prod_le_prod' List.Forall₂.prod_le_prod'
#align list.forall₂.sum_le_sum List.Forall₂.sum_le_sum

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum "If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,
  then `l₁.sum ≤ l₂.sum`.
  One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead of `∀ a ∈ l₂, 0 ≤ a`
  but this lemma is not yet in `mathlib`."]
theorem Sublist.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.prod ≤ l₂.prod := by
  induction h
  case slnil => rfl
  -- ⊢ prod l₁✝ ≤ prod (a✝¹ :: l₂✝)
  -- 🎉 no goals
  case cons l₁ l₂ a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  case cons₂ l₁ l₂ a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact mul_le_mul_left' (ih' h₁.2) _
#align list.sublist.prod_le_prod' List.Sublist.prod_le_prod'
#align list.sublist.sum_le_sum List.Sublist.sum_le_sum

@[to_additive sum_le_sum]
theorem SublistForall₂.prod_le_prod' [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.prod ≤ l₂.prod :=
  let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁
#align list.sublist_forall₂.prod_le_prod' List.SublistForall₂.prod_le_prod'
#align list.sublist_forall₂.sum_le_sum List.SublistForall₂.sum_le_sum

@[to_additive sum_le_sum]
theorem prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).prod ≤ (l.map g).prod :=
  Forall₂.prod_le_prod' <| by simpa
                              -- 🎉 no goals
#align list.prod_le_prod' List.prod_le_prod'
#align list.sum_le_sum List.sum_le_sum

@[to_additive sum_lt_sum]
theorem prod_lt_prod' [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod := by
  induction' l with i l ihl
  -- ⊢ prod (map f []) < prod (map g [])
  · rcases h₂ with ⟨_, ⟨⟩, _⟩
    -- 🎉 no goals
  simp only [forall_mem_cons, exists_mem_cons, map_cons, prod_cons] at h₁ h₂ ⊢
  -- ⊢ f i * prod (map f l) < g i * prod (map g l)
  cases h₂
  -- ⊢ f i * prod (map f l) < g i * prod (map g l)
  · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
    -- 🎉 no goals
  · exact mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 ‹_›
    -- 🎉 no goals
#align list.prod_lt_prod' List.prod_lt_prod'
#align list.sum_lt_sum List.sum_lt_sum

@[to_additive]
theorem prod_lt_prod_of_ne_nil [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (hlt : ∀ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod :=
  (prod_lt_prod' f g fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩
#align list.prod_lt_prod_of_ne_nil List.prod_lt_prod_of_ne_nil
#align list.sum_lt_sum_of_ne_nil List.sum_lt_sum_of_ne_nil

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.prod ≤ n ^ l.length := by
      simpa only [map_id'', map_const', prod_replicate] using prod_le_prod' h
      -- 🎉 no goals
#align list.prod_le_pow_card List.prod_le_pow_card
#align list.sum_le_card_nsmul List.sum_le_card_nsmul

@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' [LinearOrder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h : (l.map f).prod < (l.map g).prod) : ∃ i ∈ l, f i < g i := by
  contrapose! h
  -- ⊢ prod (map g l) ≤ prod (map f l)
  exact prod_le_prod' h
  -- 🎉 no goals
#align list.exists_lt_of_prod_lt' List.exists_lt_of_prod_lt'
#align list.exists_lt_of_sum_lt List.exists_lt_of_sum_lt

@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' [LinearOrder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).prod ≤ (l.map g).prod) : ∃ x ∈ l, f x ≤ g x := by
  contrapose! h
  -- ⊢ prod (map g l) < prod (map f l)
  exact prod_lt_prod_of_ne_nil hl _ _ h
  -- 🎉 no goals
#align list.exists_le_of_prod_le' List.exists_le_of_prod_le'
#align list.exists_le_of_sum_le List.exists_le_of_sum_le

@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.prod := by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [covariant_class M M (function.swap (*)) (≤)]
  induction' l with hd tl ih
  -- ⊢ 1 ≤ prod []
  · rfl
    -- 🎉 no goals
  rw [prod_cons]
  -- ⊢ 1 ≤ hd * prod tl
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))
  -- 🎉 no goals
#align list.one_le_prod_of_one_le List.one_le_prod_of_one_le
#align list.sum_nonneg List.sum_nonneg

end Monoid

section MonoidWithZero

variable [MonoidWithZero M₀]

/-- If zero is an element of a list `L`, then `List.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`List.prod_eq_zero_iff`. -/
theorem prod_eq_zero {L : List M₀} (h : (0 : M₀) ∈ L) : L.prod = 0 := by
  induction' L with a L ihL
  -- ⊢ prod [] = 0
  · exact absurd h (not_mem_nil _)
    -- 🎉 no goals
  · rw [prod_cons]
    -- ⊢ a * prod L = 0
    cases' mem_cons.1 h with ha hL
    -- ⊢ a * prod L = 0
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)]
    -- 🎉 no goals
#align list.prod_eq_zero List.prod_eq_zero

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`List.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp]
theorem prod_eq_zero_iff [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} :
    L.prod = 0 ↔ (0 : M₀) ∈ L := by
  induction' L with a L ihL
  -- ⊢ prod [] = 0 ↔ 0 ∈ []
  · simp
    -- 🎉 no goals
  · rw [prod_cons, mul_eq_zero, ihL, mem_cons, eq_comm]
    -- 🎉 no goals
#align list.prod_eq_zero_iff List.prod_eq_zero_iff

theorem prod_ne_zero [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} (hL : (0 : M₀) ∉ L) :
    L.prod ≠ 0 :=
  mt prod_eq_zero_iff.1 hL
#align list.prod_ne_zero List.prod_ne_zero

end MonoidWithZero

section Group

variable [Group G]

/-- This is the `List.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `List.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
             -- 🎉 no goals
  | x :: xs => by simp [prod_inv_reverse xs]
                  -- 🎉 no goals
#align list.prod_inv_reverse List.prod_inv_reverse
#align list.sum_neg_reverse List.sum_neg_reverse

/-- A non-commutative variant of `List.prod_reverse` -/
@[to_additive "A non-commutative variant of `List.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹ := by
  simp [prod_inv_reverse]
  -- 🎉 no goals
#align list.prod_reverse_noncomm List.prod_reverse_noncomm
#align list.sum_reverse_noncomm List.sum_reverse_noncomm

set_option linter.deprecated false in
/-- Counterpart to `List.prod_take_succ` when we have an inverse operation -/
@[to_additive (attr := simp)
  "Counterpart to `List.sum_take_succ` when we have a negation operation"]
theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p), (L.drop (i + 1)).prod = (L.nthLe i p)⁻¹ * (L.drop i).prod
  | [], i, p => False.elim (Nat.not_lt_zero _ p)
  | x :: xs, 0, _ => by simp [nthLe]
                        -- 🎉 no goals
  | x :: xs, i + 1, p => prod_drop_succ xs i _
#align list.prod_drop_succ List.prod_drop_succ
#align list.sum_drop_succ List.sum_drop_succ

end Group

section CommGroup

variable [CommGroup G]

/-- This is the `List.prod` version of `mul_inv` -/
@[to_additive "This is the `List.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).prod
  | [] => by simp
             -- 🎉 no goals
  | x :: xs => by simp [mul_comm, prod_inv xs]
                  -- 🎉 no goals
#align list.prod_inv List.prod_inv
#align list.sum_neg List.sum_neg

/-- Alternative version of `List.prod_set` when the list is over a group -/
@[to_additive "Alternative version of `List.sum_set` when the list is over a group"]
theorem prod_set' (L : List G) (n : ℕ) (a : G) :
    (L.set n a).prod = L.prod * if hn : n < L.length then (L.nthLe n hn)⁻¹ * a else 1 := by
  refine (prod_set L n a).trans ?_
  -- ⊢ (prod (take n L) * if n < length L then a else 1) * prod (drop (n + 1) L) =  …
  split_ifs with hn
  -- ⊢ prod (take n L) * a * prod (drop (n + 1) L) = prod L * ((nthLe L n hn)⁻¹ * a)
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp only [take_all_of_le (le_of_not_lt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_lt hn).trans n.le_succ)]
#align list.prod_update_nth' List.prod_set'
#align list.sum_update_nth' List.sum_set'

end CommGroup

@[to_additive]
theorem eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).prod = (L'.take i).prod) : L = L' := by
  refine ext_get h fun i h₁ h₂ => ?_
  -- ⊢ get L { val := i, isLt := h₁ } = get L' { val := i, isLt := h₂ }
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  -- ⊢ get L { val := i, isLt := h₁ } = get L' { val := i, isLt := h₂ }
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (le_of_lt h₁)] at this
  -- ⊢ get L { val := i, isLt := h₁ } = get L' { val := i, isLt := h₂ }
  convert mul_left_cancel this
  -- 🎉 no goals
#align list.eq_of_prod_take_eq List.eq_of_prod_take_eq
#align list.eq_of_sum_take_eq List.eq_of_sum_take_eq

@[to_additive]
theorem monotone_prod_take [CanonicallyOrderedMonoid M] (L : List M) :
    Monotone fun i => (L.take i).prod := by
  refine' monotone_nat_of_le_succ fun n => _
  -- ⊢ prod (take n L) ≤ prod (take (n + 1) L)
  cases' lt_or_le n L.length with h h
  -- ⊢ prod (take n L) ≤ prod (take (n + 1) L)
  · rw [prod_take_succ _ _ h]
    -- ⊢ prod (take n L) ≤ prod (take n L) * nthLe L n h
    exact le_self_mul
    -- 🎉 no goals
  · simp [take_all_of_le h, take_all_of_le (le_trans h (Nat.le_succ _))]
    -- 🎉 no goals
#align list.monotone_prod_take List.monotone_prod_take
#align list.monotone_sum_take List.monotone_sum_take

@[to_additive sum_pos]
theorem one_lt_prod_of_one_lt [OrderedCommMonoid M] :
    ∀ (l : List M) (_ : ∀ x ∈ l, (1 : M) < x) (_ : l ≠ []), 1 < l.prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
                    -- 🎉 no goals
  | a :: b :: l, hl₁, _ => by
    simp only [forall_eq_or_imp, List.mem_cons] at hl₁
    -- ⊢ 1 < prod (a :: b :: l)
    rw [List.prod_cons]
    -- ⊢ 1 < a * prod (b :: l)
    apply one_lt_mul_of_lt_of_le' hl₁.1
    -- ⊢ 1 ≤ prod (b :: l)
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt _ (l.cons_ne_nil b))
    -- ⊢ ∀ (x : M), x ∈ b :: l → 1 < x
    intro x hx; cases hx
    -- ⊢ 1 < x
                -- ⊢ 1 < b
    · exact hl₁.2.1
      -- 🎉 no goals
    · exact hl₁.2.2 _ ‹_›
      -- 🎉 no goals
#align list.one_lt_prod_of_one_lt List.one_lt_prod_of_one_lt
#align list.sum_pos List.sum_pos

@[to_additive]
theorem single_le_prod [OrderedCommMonoid M] {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
    ∀ x ∈ l, x ≤ l.prod := by
  induction l
  -- ⊢ ∀ (x : M), x ∈ [] → x ≤ prod []
  · simp
    -- 🎉 no goals
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  -- ⊢ head✝ ≤ head✝ * prod tail✝ ∧ ∀ (x : M), x ∈ tail✝ → x ≤ head✝ * prod tail✝
  constructor
  -- ⊢ head✝ ≤ head✝ * prod tail✝
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  -- ⊢ ∀ (x : M), x ∈ tail✝ → x ≤ head✝ * prod tail✝
  -- 🎉 no goals
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)
  -- 🎉 no goals
  -- 🎉 no goals
#align list.single_le_prod List.single_le_prod
#align list.single_le_sum List.single_le_sum

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one [OrderedCommMonoid M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)
#align list.all_one_of_le_one_le_of_prod_eq_one List.all_one_of_le_one_le_of_prod_eq_one
#align list.all_zero_of_le_zero_le_of_sum_eq_zero List.all_zero_of_le_zero_le_of_sum_eq_zero

/-- Slightly more general version of `List.prod_eq_one_iff` for a non-ordered `Monoid` -/
@[to_additive
      "Slightly more general version of `List.sum_eq_zero_iff` for a non-ordered `AddMonoid`"]
theorem prod_eq_one [Monoid M] {l : List M} (hl : ∀ x ∈ l, x = (1 : M)) : l.prod = 1 := by
  induction' l with i l hil
  -- ⊢ prod [] = 1
  · rfl
    -- 🎉 no goals
  rw [List.prod_cons, hil fun x hx => hl _ (mem_cons_of_mem i hx), hl _ (mem_cons_self i l),
    one_mul]
#align list.prod_eq_one List.prod_eq_one
#align list.sum_eq_zero List.sum_eq_zero

@[to_additive]
theorem exists_mem_ne_one_of_prod_ne_one [Monoid M] {l : List M} (h : l.prod ≠ 1) :
    ∃ x ∈ l, x ≠ (1 : M) := by simpa only [not_forall, exists_prop] using mt prod_eq_one h
                               -- 🎉 no goals
#align list.exists_mem_ne_one_of_prod_ne_one List.exists_mem_ne_one_of_prod_ne_one
#align list.exists_mem_ne_zero_of_sum_ne_zero List.exists_mem_ne_zero_of_sum_ne_zero

-- TODO: develop theory of tropical rings
theorem sum_le_foldr_max [AddMonoid M] [AddMonoid N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.sum ≤ (l.map f).foldr max 0 := by
  induction' l with hd tl IH
  -- ⊢ f (sum []) ≤ foldr max 0 (map f [])
  · simpa using h0
    -- 🎉 no goals
  simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
  -- ⊢ f (hd + sum tl) ≤ max (f hd) (foldr (fun x y => max (f x) y) 0 tl)
  exact (hadd _ _).trans (max_le_max le_rfl IH)
  -- 🎉 no goals
#align list.sum_le_foldr_max List.sum_le_foldr_max

@[to_additive (attr := simp)]
theorem prod_erase [DecidableEq M] [CommMonoid M] {a} :
    ∀ {l : List M}, a ∈ l → a * (l.erase a).prod = l.prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    -- ⊢ a * prod (List.erase (a :: l) a) = prod (a :: l)
    · simp only [List.erase, if_pos, prod_cons, beq_self_eq_true]
      -- 🎉 no goals
    · simp only [List.erase, beq_false_of_ne ne.symm, prod_cons, prod_erase h, mul_left_comm a b]
      -- 🎉 no goals
#align list.prod_erase List.prod_erase
#align list.sum_erase List.sum_erase

@[to_additive (attr := simp)]
theorem prod_map_erase [DecidableEq ι] [CommMonoid M] (f : ι → M) {a} :
    ∀ {l : List ι}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := Decidable.List.eq_or_ne_mem_of_mem h
    -- ⊢ f a * prod (map f (List.erase (a :: l) a)) = prod (map f (a :: l))
    · simp only [map, erase_cons_head, prod_cons]
      -- 🎉 no goals
    · simp only [map, erase_cons_tail _ ne.symm, prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]
#align list.prod_map_erase List.prod_map_erase
#align list.sum_map_erase List.sum_map_erase

theorem sum_const_nat (m n : ℕ) : sum (replicate m n) = m * n :=
  sum_replicate m n
#align list.sum_const_nat List.sum_const_nat

/-- The product of a list of positive natural numbers is positive,
and likewise for any nontrivial ordered semiring. -/
theorem prod_pos [StrictOrderedSemiring R] (l : List R) (h : ∀ a ∈ l, (0 : R) < a) :
    0 < l.prod := by
  induction' l with a l ih
  -- ⊢ 0 < prod []
  · simp
    -- 🎉 no goals
  · rw [prod_cons]
    -- ⊢ 0 < a * prod l
    exact mul_pos (h _ <| mem_cons_self _ _) (ih fun a ha => h a <| mem_cons_of_mem _ ha)
    -- 🎉 no goals
#align list.prod_pos List.prod_pos

/-- A variant of `List.prod_pos` for `CanonicallyOrderedCommSemiring`. -/
@[simp] lemma _root_.CanonicallyOrderedCommSemiring.list_prod_pos
    {α : Type*} [CanonicallyOrderedCommSemiring α] [Nontrivial α] :
    ∀ {l : List α}, 0 < l.prod ↔ (∀ x ∈ l, (0 : α) < x)
  | [] => by simp
             -- 🎉 no goals
  | (x :: xs) => by simp_rw [prod_cons, forall_mem_cons, CanonicallyOrderedCommSemiring.mul_pos,
    list_prod_pos]
#align canonically_ordered_comm_semiring.list_prod_pos CanonicallyOrderedCommSemiring.list_prod_pos

/-!
Several lemmas about sum/head/tail for `List ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/

/-- This relies on `default ℕ = 0`. -/
theorem headI_add_tail_sum (L : List ℕ) : L.headI + L.tail.sum = L.sum := by
  cases L <;> simp
  -- ⊢ headI [] + sum (tail []) = sum []
              -- 🎉 no goals
              -- 🎉 no goals
#align list.head_add_tail_sum List.headI_add_tail_sum

/-- This relies on `default ℕ = 0`. -/
theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum :=
  Nat.le.intro (headI_add_tail_sum L)
#align list.head_le_sum List.headI_le_sum

/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  rw [← headI_add_tail_sum L, add_comm, @add_tsub_cancel_right]
  -- 🎉 no goals
#align list.tail_sum List.tail_sum

section Alternating

section

variable [One α] [Mul α] [Inv α]

@[to_additive (attr := simp)]
theorem alternatingProd_nil : alternatingProd ([] : List α) = 1 :=
  rfl
#align list.alternating_prod_nil List.alternatingProd_nil
#align list.alternating_sum_nil List.alternatingSum_nil

@[to_additive (attr := simp)]
theorem alternatingProd_singleton (a : α) : alternatingProd [a] = a :=
  rfl
#align list.alternating_prod_singleton List.alternatingProd_singleton
#align list.alternating_sum_singleton List.alternatingSum_singleton

@[to_additive]
theorem alternatingProd_cons_cons' (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl
#align list.alternating_prod_cons_cons' List.alternatingProd_cons_cons'
#align list.alternating_sum_cons_cons' List.alternatingSum_cons_cons'

end

@[to_additive]
theorem alternatingProd_cons_cons [DivInvMonoid α] (a b : α) (l : List α) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons_cons']
  -- 🎉 no goals
#align list.alternating_prod_cons_cons List.alternatingProd_cons_cons
#align list.alternating_sum_cons_cons List.alternatingSum_cons_cons

variable [CommGroup α]

@[to_additive]
theorem alternatingProd_cons' :
    ∀ (a : α) (l : List α), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternatingProd_nil, inv_one, mul_one, alternatingProd_singleton]
                -- 🎉 no goals
  | a, b :: l => by
    rw [alternatingProd_cons_cons', alternatingProd_cons' b l, mul_inv, inv_inv, mul_assoc]
    -- 🎉 no goals
#align list.alternating_prod_cons' List.alternatingProd_cons'
#align list.alternating_sum_cons' List.alternatingSum_cons'

@[to_additive (attr := simp)]
theorem alternatingProd_cons (a : α) (l : List α) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons']
  -- 🎉 no goals
#align list.alternating_prod_cons List.alternatingProd_cons
#align list.alternating_sum_cons List.alternatingSum_cons

end Alternating

lemma sum_nat_mod (l : List ℕ) (n : ℕ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Nat.add_mod, *]
  -- ⊢ sum [] % n = sum (map (fun x => x % n) []) % n
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.sum_nat_mod List.sum_nat_mod

lemma prod_nat_mod (l : List ℕ) (n : ℕ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Nat.mul_mod, *]
  -- ⊢ prod [] % n = prod (map (fun x => x % n) []) % n
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.prod_nat_mod List.prod_nat_mod

lemma sum_int_mod (l : List ℤ) (n : ℤ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Int.add_emod, *]
  -- ⊢ sum [] % n = sum (map (fun x => x % n) []) % n
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.sum_int_mod List.sum_int_mod

lemma prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]
  -- ⊢ prod [] % n = prod (map (fun x => x % n) []) % n
                  -- 🎉 no goals
                  -- 🎉 no goals
#align list.prod_int_mod List.prod_int_mod

end List

section MonoidHom

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map_list_prod {F : Type*} [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod = (l.map f).prod :=
  (l.prod_hom f).symm
#align map_list_prod map_list_prod
#align map_list_sum map_list_sum

namespace MonoidHom

/-- Deprecated, use `_root_.map_list_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_list_sum` instead."]
protected theorem map_list_prod (f : M →* N) (l : List M) : f l.prod = (l.map f).prod :=
  map_list_prod f l
#align monoid_hom.map_list_prod MonoidHom.map_list_prod
#align add_monoid_hom.map_list_sum AddMonoidHom.map_list_sum

end MonoidHom

end MonoidHom
