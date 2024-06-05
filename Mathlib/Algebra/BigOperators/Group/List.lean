/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Units
import Mathlib.Data.List.Perm
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.Rotate

#align_import data.list.big_operators.basic from "leanprover-community/mathlib"@"6c5f73fd6f6cc83122788a80a27cdd54663609f4"

/-!
# Sums and products from lists

This file provides basic results about `List.prod`, `List.sum`, which calculate the product and sum
of elements of a list and `List.alternatingProd`, `List.alternatingSum`, their alternating
counterparts.
-/

-- Make sure we haven't imported `Data.Nat.Order.Basic`
assert_not_exists OrderedSub
assert_not_exists Ring

variable {ι α β M N P G : Type*}

namespace List
section Defs

/-- Product of a list.

`List.prod [a, b, c] = ((1 * a) * b) * c` -/
@[to_additive "Sum of a list.\n\n`List.sum [a, b, c] = ((0 + a) + b) + c`"]
def prod {α} [Mul α] [One α] : List α → α :=
  foldl (· * ·) 1
#align list.prod List.prod
#align list.sum List.sum

/-- The alternating sum of a list. -/
def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t
#align list.alternating_sum List.alternatingSum

/-- The alternating product of a list. -/
@[to_additive existing]
def alternatingProd {G : Type*} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternatingProd t
#align list.alternating_prod List.alternatingProd

end Defs

section MulOneClass

variable [MulOneClass M] {l : List M} {a : M}

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
theorem prod_one_cons : (1 :: l).prod = l.prod := by
  rw [prod, foldl, mul_one]

@[to_additive]
theorem prod_map_one {l : List ι} :
    (l.map fun _ => (1 : M)).prod = 1 := by
  induction l with
  | nil => rfl
  | cons hd tl ih => rw [map_cons, prod_one_cons, ih]

end MulOneClass

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[to_additive (attr := simp)]
theorem prod_cons : (a :: l).prod = a * l.prod :=
  calc
    (a :: l).prod = foldl (· * ·) (a * 1) l := by
      simp only [List.prod, foldl_cons, one_mul, mul_one]
    _ = _ := foldl_assoc
#align list.prod_cons List.prod_cons
#align list.sum_cons List.sum_cons

@[to_additive]
lemma prod_induction
    (p : M → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ l, p x) :
    p l.prod := by
  induction' l with a l ih
  · simpa
  rw [List.prod_cons]
  simp only [Bool.not_eq_true, List.mem_cons, forall_eq_or_imp] at base
  exact hom _ _ (base.1) (ih base.2)

@[to_additive (attr := simp)]
theorem prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
  calc
    (l₁ ++ l₂).prod = foldl (· * ·) (foldl (· * ·) 1 l₁ * 1) l₂ := by simp [List.prod]
    _ = l₁.prod * l₂.prod := foldl_assoc
#align list.prod_append List.prod_append
#align list.sum_append List.sum_append

@[to_additive]
theorem prod_concat : (l.concat a).prod = l.prod * a := by
  rw [concat_eq_append, prod_append, prod_singleton]
#align list.prod_concat List.prod_concat
#align list.sum_concat List.sum_concat

@[to_additive (attr := simp)]
theorem prod_join {l : List (List M)} : l.join.prod = (l.map List.prod).prod := by
  induction l <;> [rfl; simp only [*, List.join, map, prod_append, prod_cons]]
#align list.prod_join List.prod_join
#align list.sum_join List.sum_join

@[to_additive]
theorem prod_eq_foldr : ∀ {l : List M}, l.prod = foldr (· * ·) 1 l
  | [] => rfl
  | cons a l => by rw [prod_cons, foldr_cons, prod_eq_foldr]
#align list.prod_eq_foldr List.prod_eq_foldr
#align list.sum_eq_foldr List.sum_eq_foldr

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  induction' n with n ih
  · rw [pow_zero]
    rfl
  · rw [replicate_succ, prod_cons, ih, pow_succ']
#align list.prod_replicate List.prod_replicate
#align list.sum_replicate List.sum_replicate

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.prod = m ^ l.length := by
  rw [← prod_replicate, ← List.eq_replicate.mpr ⟨rfl, h⟩]
#align list.prod_eq_pow_card List.prod_eq_pow_card
#align list.sum_eq_card_nsmul List.sum_eq_card_nsmul

@[to_additive]
theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).prod (l.map g).prod :=
  List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]
#align list.prod_hom_rel List.prod_hom_rel
#align list.sum_hom_rel List.sum_hom_rel

@[to_additive]
theorem rel_prod {R : M → N → Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod :=
  rel_foldl hf h
#align list.rel_prod List.rel_prod
#align list.rel_sum List.rel_sum

@[to_additive]
theorem prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    (l.map f).prod = f l.prod := by
  simp only [prod, foldl_map, ← map_one f]
  exact l.foldl_hom f (· * ·) (· * f ·) 1 (fun x y => (map_mul f x y).symm)
#align list.prod_hom List.prod_hom
#align list.sum_hom List.sum_hom

@[to_additive]
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  simp only [prod, foldl_map]
  -- Porting note: next 3 lines used to be
  -- convert l.foldl_hom₂ (fun a b => f a b) _ _ _ _ _ fun a b i => _
  -- · exact hf'.symm
  -- · exact hf _ _ _ _
  rw [← l.foldl_hom₂ (fun a b => f a b), hf']
  intros
  exact hf _ _ _ _
#align list.prod_hom₂ List.prod_hom₂
#align list.sum_hom₂ List.sum_hom₂

@[to_additive (attr := simp)]
theorem prod_map_mul {α : Type*} [CommMonoid α] {l : List ι} {f g : ι → α} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align list.prod_map_mul List.prod_map_mul
#align list.sum_map_add List.sum_map_add

@[to_additive]
theorem prod_map_hom (L : List ι) (f : ι → M) {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) :
    (L.map (g ∘ f)).prod = g (L.map f).prod := by rw [← prod_hom, map_map]
#align list.prod_map_hom List.prod_map_hom
#align list.sum_map_hom List.sum_map_hom

@[to_additive]
theorem prod_isUnit : ∀ {L : List M}, (∀ m ∈ L, IsUnit m) → IsUnit L.prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))
#align list.prod_is_unit List.prod_isUnit
#align list.sum_is_add_unit List.sum_isAddUnit

@[to_additive]
theorem prod_isUnit_iff {α : Type*} [CommMonoid α] {L : List α} :
    IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m := by
  refine ⟨fun h => ?_, prod_isUnit⟩
  induction' L with m L ih
  · exact fun m' h' => False.elim (not_mem_nil m' h')
  rw [prod_cons, IsUnit.mul_iff] at h
  exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H
#align list.prod_is_unit_iff List.prod_isUnit_iff
#align list.sum_is_add_unit_iff List.sum_isAddUnit_iff

@[to_additive (attr := simp)]
theorem prod_take_mul_prod_drop : ∀ (L : List M) (i : ℕ), (L.take i).prod * (L.drop i).prod = L.prod
  | [], i => by simp [Nat.zero_le]
  | L, 0 => by simp
  | h :: t, n + 1 => by
    dsimp
    rw [prod_cons, prod_cons, mul_assoc, prod_take_mul_prod_drop t]
#align list.prod_take_mul_prod_drop List.prod_take_mul_prod_drop
#align list.sum_take_add_sum_drop List.sum_take_add_sum_drop

@[to_additive (attr := simp)]
theorem prod_take_succ :
    ∀ (L : List M) (i : ℕ) (p), (L.take (i + 1)).prod = (L.take i).prod * L.get ⟨i, p⟩
  | [], i, p => by cases p
  | h :: t, 0, _ => rfl
  | h :: t, n + 1, p => by
    dsimp
    rw [prod_cons, prod_cons, prod_take_succ t n (Nat.lt_of_succ_lt_succ p), mul_assoc]
#align list.prod_take_succ List.prod_take_succ
#align list.sum_take_succ List.sum_take_succ

/-- A list with product not one must have positive length. -/
@[to_additive "A list with sum not zero must have positive length."]
theorem length_pos_of_prod_ne_one (L : List M) (h : L.prod ≠ 1) : 0 < L.length := by
  cases L
  · simp at h
  · simp
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
  | x :: xs, i + 1, a => by
    simp [set, prod_set xs i a, mul_assoc, Nat.succ_eq_add_one, Nat.add_lt_add_iff_right]
  | [], _, _ => by simp [set, (Nat.zero_le _).not_lt, Nat.zero_le]
#align list.prod_update_nth List.prod_set
#align list.sum_update_nth List.sum_set

/-- We'd like to state this as `L.headI * L.tail.prod = L.prod`, but because `L.headI` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `(L.get? 0).getD 1`.
-/
@[to_additive "We'd like to state this as `L.headI + L.tail.sum = L.sum`, but because `L.headI`
  relies on an inhabited instance to return a garbage value on the empty list, this is not possible.
  Instead, we write the statement in terms of `(L.get? 0).getD 0`."]
theorem get?_zero_mul_tail_prod (l : List M) : (l.get? 0).getD 1 * l.tail.prod = l.prod := by
  cases l <;> simp
#align list.nth_zero_mul_tail_prod List.get?_zero_mul_tail_prod
#align list.nth_zero_add_tail_sum List.get?_zero_add_tail_sum

/-- Same as `get?_zero_mul_tail_prod`, but avoiding the `List.headI` garbage complication by
  requiring the list to be nonempty. -/
@[to_additive "Same as `get?_zero_add_tail_sum`, but avoiding the `List.headI` garbage complication
  by requiring the list to be nonempty."]
theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.headI * l.tail.prod = l.prod := by cases l <;> [contradiction; simp]
#align list.head_mul_tail_prod_of_ne_nil List.headI_mul_tail_prod_of_ne_nil
#align list.head_add_tail_sum_of_ne_nil List.headI_add_tail_sum_of_ne_nil

@[to_additive]
theorem _root_.Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.prod := by
  induction' l with z l IH
  · simp
  · rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)
#align commute.list_prod_right Commute.list_prod_right
#align add_commute.list_sum_right AddCommute.list_sum_right

@[to_additive]
theorem _root_.Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) :
    Commute l.prod y :=
  ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm
#align commute.list_prod_left Commute.list_prod_left
#align add_commute.list_sum_left AddCommute.list_sum_left

@[to_additive] lemma prod_range_succ (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = ((range n).map f).prod * f n := by
  rw [range_succ, map_append, map_singleton, prod_append, prod_cons, prod_nil, mul_one]
#align list.prod_range_succ List.prod_range_succ
#align list.sum_range_succ List.sum_range_succ

/-- A variant of `prod_range_succ` which pulls off the first term in the product rather than the
last. -/
@[to_additive
"A variant of `sum_range_succ` which pulls off the first term in the sum rather than the last."]
lemma prod_range_succ' (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = f 0 * ((range n).map fun i ↦ f i.succ).prod :=
  Nat.recOn n (show 1 * f 0 = f 0 * 1 by rw [one_mul, mul_one]) fun _ hd => by
    rw [List.prod_range_succ, hd, mul_assoc, ← List.prod_range_succ]
#align list.prod_range_succ' List.prod_range_succ'
#align list.sum_range_succ' List.sum_range_succ'

@[to_additive] lemma prod_eq_one (hl : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction' l with i l hil
  · rfl
  rw [List.prod_cons, hil fun x hx ↦ hl _ (mem_cons_of_mem i hx), hl _ (mem_cons_self i l), one_mul]
#align list.prod_eq_one List.prod_eq_one
#align list.sum_eq_zero List.sum_eq_zero

@[to_additive] lemma exists_mem_ne_one_of_prod_ne_one (h : l.prod ≠ 1) :
    ∃ x ∈ l, x ≠ (1 : M) := by simpa only [not_forall, exists_prop] using mt prod_eq_one h
#align list.exists_mem_ne_one_of_prod_ne_one List.exists_mem_ne_one_of_prod_ne_one
#align list.exists_mem_ne_zero_of_sum_ne_zero List.exists_mem_ne_zero_of_sum_ne_zero

@[to_additive]
lemma prod_erase_of_comm [DecidableEq M] (ha : a ∈ l) (comm : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) :
    a * (l.erase a).prod = l.prod := by
  induction' l with b l ih
  · simp only [not_mem_nil] at ha
  obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
  · simp only [erase_cons_head, prod_cons]
  rw [List.erase, beq_false_of_ne ne.symm, List.prod_cons, List.prod_cons, ← mul_assoc,
    comm a ha b (l.mem_cons_self b), mul_assoc,
    ih h fun x hx y hy ↦ comm _ (List.mem_cons_of_mem b hx) _ (List.mem_cons_of_mem b hy)]

@[to_additive]
lemma prod_map_eq_pow_single [DecidableEq α] {l : List α} (a : α) (f : α → M)
    (hf : ∀ a', a' ≠ a → a' ∈ l → f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction' l with a' as h generalizing a
  · rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  · specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ']
    · rw [hf a' (Ne.symm ha') (List.mem_cons_self a' as), one_mul, add_zero]
#align list.prod_map_eq_pow_single List.prod_map_eq_pow_single
#align list.sum_map_eq_nsmul_single List.sum_map_eq_nsmul_single

@[to_additive]
lemma prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a', a' ≠ a → a' ∈ l → a' = 1) :
    l.prod = a ^ l.count a :=
  _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)
#align list.prod_eq_pow_single List.prod_eq_pow_single
#align list.sum_eq_nsmul_single List.sum_eq_nsmul_single

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements. -/
@[to_additive "If elements of a list additively commute with each other, then their sum does not
depend on the order of elements."]
lemma Perm.prod_eq' (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) : l₁.prod = l₂.prod := by
  refine h.foldl_eq' ?_ _
  apply Pairwise.forall_of_forall
  · intro x y h z
    exact (h z).symm
  · intros; rfl
  · apply hc.imp
    intro a b h z
    rw [mul_assoc z, mul_assoc z, h]
#align list.perm.prod_eq' List.Perm.prod_eq'
#align list.perm.sum_eq' List.Perm.sum_eq'

end Monoid

section CommMonoid
variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

@[to_additive (attr := simp)]
lemma prod_erase [DecidableEq M] (ha : a ∈ l) : a * (l.erase a).prod = l.prod :=
  prod_erase_of_comm ha fun x _ y _ ↦ mul_comm x y
#align list.prod_erase List.prod_erase
#align list.sum_erase List.sum_erase

@[to_additive (attr := simp)]
lemma prod_map_erase [DecidableEq α] (f : α → M) {a} :
    ∀ {l : List α}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail _ (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]
#align list.prod_map_erase List.prod_map_erase
#align list.sum_map_erase List.sum_map_erase

@[to_additive] lemma Perm.prod_eq (h : Perm l₁ l₂) : prod l₁ = prod l₂ := h.fold_op_eq
#align list.perm.prod_eq List.Perm.prod_eq
#align list.perm.sum_eq List.Perm.sum_eq

@[to_additive] lemma prod_reverse (l : List M) : prod l.reverse = prod l := (reverse_perm l).prod_eq
#align list.prod_reverse List.prod_reverse
#align list.sum_reverse List.sum_reverse

@[to_additive]
lemma prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    ∀ l l' : List M,
      l.prod * l'.prod =
        (zipWith (· * ·) l l').prod * (l.drop l'.length).prod * (l'.drop l.length).prod
  | [], ys => by simp [Nat.zero_le]
  | xs, [] => by simp [Nat.zero_le]
  | x :: xs, y :: ys => by
    simp only [drop, length, zipWith_cons_cons, prod_cons]
    conv =>
      lhs; rw [mul_assoc]; right; rw [mul_comm, mul_assoc]; right
      rw [mul_comm, prod_mul_prod_eq_prod_zipWith_mul_prod_drop xs ys]
    simp [mul_assoc]
#align list.prod_mul_prod_eq_prod_zip_with_mul_prod_drop List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop
#align list.sum_add_sum_eq_sum_zip_with_add_sum_drop List.sum_add_sum_eq_sum_zipWith_add_sum_drop

@[to_additive]
lemma prod_mul_prod_eq_prod_zipWith_of_length_eq (l l' : List M) (h : l.length = l'.length) :
    l.prod * l'.prod = (zipWith (· * ·) l l').prod := by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h, drop_length, h, drop_length, prod_nil, mul_one, mul_one]
#align list.prod_mul_prod_eq_prod_zip_with_of_length_eq List.prod_mul_prod_eq_prod_zipWith_of_length_eq
#align list.sum_add_sum_eq_sum_zip_with_of_length_eq List.sum_add_sum_eq_sum_zipWith_of_length_eq

end CommMonoid

@[to_additive]
lemma eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).prod = (L'.take i).prod) : L = L' := by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (le_of_lt h₁)] at this
  convert mul_left_cancel this
#align list.eq_of_prod_take_eq List.eq_of_prod_take_eq
#align list.eq_of_sum_take_eq List.eq_of_sum_take_eq

section Group

variable [Group G]

/-- This is the `List.prod` version of `mul_inv_rev` -/
@[to_additive "This is the `List.sum` version of `add_neg_rev`"]
theorem prod_inv_reverse : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_inv_reverse xs]
#align list.prod_inv_reverse List.prod_inv_reverse
#align list.sum_neg_reverse List.sum_neg_reverse

/-- A non-commutative variant of `List.prod_reverse` -/
@[to_additive "A non-commutative variant of `List.sum_reverse`"]
theorem prod_reverse_noncomm : ∀ L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹ := by
  simp [prod_inv_reverse]
#align list.prod_reverse_noncomm List.prod_reverse_noncomm
#align list.sum_reverse_noncomm List.sum_reverse_noncomm

/-- Counterpart to `List.prod_take_succ` when we have an inverse operation -/
@[to_additive (attr := simp)
  "Counterpart to `List.sum_take_succ` when we have a negation operation"]
theorem prod_drop_succ :
    ∀ (L : List G) (i : ℕ) (p), (L.drop (i + 1)).prod = (L.get ⟨i, p⟩)⁻¹ * (L.drop i).prod
  | [], i, p => False.elim (Nat.not_lt_zero _ p)
  | x :: xs, 0, _ => by simp
  | x :: xs, i + 1, p => prod_drop_succ xs i _
#align list.prod_drop_succ List.prod_drop_succ
#align list.sum_drop_succ List.sum_drop_succ

/-- Cancellation of a telescoping product. -/
@[to_additive "Cancellation of a telescoping sum."]
theorem prod_range_div' (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f k / f (k + 1)).prod = f 0 / f n := by
  induction' n with n h
  · exact (div_self' (f 0)).symm
  · rw [range_succ, map_append, map_singleton, prod_append, prod_singleton, h, div_mul_div_cancel']

lemma prod_rotate_eq_one_of_prod_eq_one :
    ∀ {l : List G} (_ : l.prod = 1) (n : ℕ), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := le_of_lt (Nat.mod_lt _ (by simp))
    rw [← List.take_append_drop (n % List.length (a :: l)) (a :: l)] at hl;
      rw [← rotate_mod, rotate_eq_drop_append_take this, List.prod_append, mul_eq_one_iff_inv_eq, ←
        one_mul (List.prod _)⁻¹, ← hl, List.prod_append, mul_assoc, mul_inv_self, mul_one]
#align list.prod_rotate_eq_one_of_prod_eq_one List.prod_rotate_eq_one_of_prod_eq_one

end Group

section CommGroup

variable [CommGroup G]

/-- This is the `List.prod` version of `mul_inv` -/
@[to_additive "This is the `List.sum` version of `add_neg`"]
theorem prod_inv : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]
#align list.prod_inv List.prod_inv
#align list.sum_neg List.sum_neg

/-- Cancellation of a telescoping product. -/
@[to_additive "Cancellation of a telescoping sum."]
theorem prod_range_div (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f (k + 1) / f k).prod = f n / f 0 := by
  have h : ((·⁻¹) ∘ fun k ↦ f (k + 1) / f k) = fun k ↦ f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj, prod_inv, map_map, inv_div, h, prod_range_div']

/-- Alternative version of `List.prod_set` when the list is over a group -/
@[to_additive "Alternative version of `List.sum_set` when the list is over a group"]
theorem prod_set' (L : List G) (n : ℕ) (a : G) :
    (L.set n a).prod = L.prod * if hn : n < L.length then (L.get ⟨n, hn⟩)⁻¹ * a else 1 := by
  refine (prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp only [take_all_of_le (le_of_not_lt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_lt hn).trans n.le_succ)]
#align list.prod_update_nth' List.prod_set'
#align list.sum_update_nth' List.sum_set'

end CommGroup

theorem sum_const_nat (m n : ℕ) : sum (replicate m n) = m * n :=
  sum_replicate m n
#align list.sum_const_nat List.sum_const_nat

/-!
Several lemmas about sum/head/tail for `List ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/

/-- This relies on `default ℕ = 0`. -/
theorem headI_add_tail_sum (L : List ℕ) : L.headI + L.tail.sum = L.sum := by
  cases L <;> simp
#align list.head_add_tail_sum List.headI_add_tail_sum

/-- This relies on `default ℕ = 0`. -/
theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum :=
  Nat.le.intro (headI_add_tail_sum L)
#align list.head_le_sum List.headI_le_sum

/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  rw [← headI_add_tail_sum L, add_comm, Nat.add_sub_cancel_right]
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
#align list.alternating_prod_cons_cons List.alternatingProd_cons_cons
#align list.alternating_sum_cons_cons List.alternatingSum_cons_cons

variable [CommGroup α]

@[to_additive]
theorem alternatingProd_cons' :
    ∀ (a : α) (l : List α), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternatingProd_nil, inv_one, mul_one, alternatingProd_singleton]
  | a, b :: l => by
    rw [alternatingProd_cons_cons', alternatingProd_cons' b l, mul_inv, inv_inv, mul_assoc]
#align list.alternating_prod_cons' List.alternatingProd_cons'
#align list.alternating_sum_cons' List.alternatingSum_cons'

@[to_additive (attr := simp)]
theorem alternatingProd_cons (a : α) (l : List α) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons']
#align list.alternating_prod_cons List.alternatingProd_cons
#align list.alternating_sum_cons List.alternatingSum_cons

end Alternating

lemma sum_nat_mod (l : List ℕ) (n : ℕ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction' l with a l ih
  · simp only [Nat.zero_mod, map_nil]
  · simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)
#align list.sum_nat_mod List.sum_nat_mod

lemma prod_nat_mod (l : List ℕ) (n : ℕ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction' l with a l ih
  · simp only [Nat.zero_mod, map_nil]
  · simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)
#align list.prod_nat_mod List.prod_nat_mod

lemma sum_int_mod (l : List ℤ) (n : ℤ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Int.add_emod, *]
#align list.sum_int_mod List.sum_int_mod

lemma prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]
#align list.prod_int_mod List.prod_int_mod

variable [DecidableEq α]

/-- Summing the count of `x` over a list filtered by some `p` is just `countP` applied to `p` -/
theorem sum_map_count_dedup_filter_eq_countP (p : α → Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countP p := by
  induction' l with a as h
  · simp
  · simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    congr 1
    · refine _root_.trans ?_ h
      by_cases ha : a ∈ as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_not_mem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · by_cases hp : p a
      · refine _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h]) ?_
        simp [hp, count_dedup]
      · refine _root_.trans (List.sum_eq_zero fun n hn => ?_) (by simp [hp])
        obtain ⟨a', ha'⟩ := List.mem_map.1 hn
        split_ifs at ha' with ha
        · simp only [ha, mem_filter, mem_dedup, find?, mem_cons, true_or, hp,
            and_false, false_and] at ha'
        · exact ha'.2.symm
#align list.sum_map_count_dedup_filter_eq_countp List.sum_map_count_dedup_filter_eq_countP

theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countP (fun _ => True) l
#align list.sum_map_count_dedup_eq_length List.sum_map_count_dedup_eq_length

end List

section MonoidHom

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod = (l.map f).prod :=
  (l.prod_hom f).symm
#align map_list_prod map_list_prod
#align map_list_sum map_list_sum

namespace MonoidHom

-- original lemma deprecated on 2023-01-10; additivised lemma on 2024-05-02
/-- Deprecated, use `_root_.map_list_prod` instead. -/
@[to_additive (attr := deprecated) "Deprecated, use `_root_.map_list_sum` instead."]
protected theorem map_list_prod (f : M →* N) (l : List M) : f l.prod = (l.map f).prod :=
  map_list_prod f l
#align monoid_hom.map_list_prod MonoidHom.map_list_prod
#align add_monoid_hom.map_list_sum AddMonoidHom.map_list_sum

end MonoidHom

end MonoidHom

@[simp] lemma Nat.sum_eq_listSum (l : List ℕ) : Nat.sum l = l.sum :=
  (List.foldl_eq_foldr Nat.add_comm Nat.add_assoc _ _).symm

namespace List

lemma length_sigma {σ : α → Type*} (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map fun a ↦ length (l₂ a)).sum := by simp [length_sigma']
#align list.length_sigma List.length_sigma

lemma ranges_join (l : List ℕ) : l.ranges.join = range l.sum := by simp [ranges_join']

/-- Any entry of any member of `l.ranges` is strictly smaller than `l.sum`. -/
lemma mem_mem_ranges_iff_lt_sum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ l.ranges, n ∈ s) ↔ n < l.sum := by simp [mem_mem_ranges_iff_lt_natSum]

@[simp]
theorem length_join (L : List (List α)) : length (join L) = sum (map length L) := by
  induction L <;> [rfl; simp only [*, join, map, sum_cons, length_append]]
#align list.length_join List.length_join

lemma countP_join (p : α → Bool) : ∀ L : List (List α), countP p L.join = (L.map (countP p)).sum
  | [] => rfl
  | a :: l => by rw [join, countP_append, map_cons, sum_cons, countP_join _ l]
#align list.countp_join List.countP_join

lemma count_join [BEq α] (L : List (List α)) (a : α) : L.join.count a = (L.map (count a)).sum :=
  countP_join _ _
#align list.count_join List.count_join

@[simp]
theorem length_bind (l : List α) (f : α → List β) :
    length (List.bind l f) = sum (map (length ∘ f) l) := by rw [List.bind, length_join, map_map]
#align list.length_bind List.length_bind

lemma countP_bind (p : β → Bool) (l : List α) (f : α → List β) :
    countP p (l.bind f) = sum (map (countP p ∘ f) l) := by rw [List.bind, countP_join, map_map]

lemma count_bind [BEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.bind f) = sum (map (count x ∘ f) l) := countP_bind _ _ _
#align list.count_bind List.count_bind

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
lemma take_sum_join (L : List (List α)) (i : ℕ) :
    L.join.take ((L.map length).take i).sum = (L.take i).join := by simpa using take_sum_join' _ _
#align list.take_sum_join List.take_sum_join

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
lemma drop_sum_join (L : List (List α)) (i : ℕ) :
    L.join.drop ((L.map length).take i).sum = (L.drop i).join := by simpa using drop_sum_join' _ _
#align list.drop_sum_join List.drop_sum_join

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
lemma drop_take_succ_join_eq_get (L : List (List α)) (i : Fin L.length) :
    (L.join.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum = get L i := by
  simpa using drop_take_succ_join_eq_get' _ _

end List


namespace List

/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.prod = -1) : (-1 : ℤ) ∈ l := by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁
#align list.neg_one_mem_of_prod_eq_neg_one List.neg_one_mem_of_prod_eq_neg_one

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum := by
  induction' L with j L IH h; · simp
  rw [sum_cons, length, add_comm]
  exact Nat.add_le_add (h _ (mem_cons_self _ _)) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))
#align list.length_le_sum_of_one_le List.length_le_sum_of_one_le

theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.prod := by
  let ⟨s, t, h⟩ := append_of_mem ha
  rw [h, prod_append, prod_cons, mul_left_comm]
  exact dvd_mul_right _ _
#align list.dvd_prod List.dvd_prod

theorem Sublist.prod_dvd_prod [CommMonoid M] {l₁ l₂ : List M} (h : l₁ <+ l₂) :
    l₁.prod ∣ l₂.prod := by
  obtain ⟨l, hl⟩ := h.exists_perm_append
  rw [hl.prod_eq, prod_append]
  exact dvd_mul_right _ _

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
#align list.alternating_prod_append List.alternatingProd_append
#align list.alternating_sum_append List.alternatingSum_append

@[to_additive]
theorem alternatingProd_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternatingProd_nil, one_zpow, reverse_nil]
  | a :: l => by
    simp_rw [reverse_cons, alternatingProd_append, alternatingProd_reverse,
      alternatingProd_singleton, alternatingProd_cons, length_reverse, length, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]
#align list.alternating_prod_reverse List.alternatingProd_reverse
#align list.alternating_sum_reverse List.alternatingSum_reverse

end Alternating

end List

open List

namespace MulOpposite
variable [Monoid M]

lemma op_list_prod : ∀ l : List M, op l.prod = (l.map op).reverse.prod := by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, ih]
#align mul_opposite.op_list_prod MulOpposite.op_list_prod

lemma unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop = (l.map unop).reverse.prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse,
    op_comp_unop, map_id]
#align mul_opposite.unop_list_prod MulOpposite.unop_list_prod

end MulOpposite

section MonoidHom
variable [Monoid M] [Monoid N]

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
lemma unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
    (f : F) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]
#align unop_map_list_prod unop_map_list_prod

namespace MonoidHom

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
@[deprecated _root_.unop_map_list_prod]
protected theorem unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod :=
  unop_map_list_prod f l
#align monoid_hom.unop_map_list_prod MonoidHom.unop_map_list_prod

end MonoidHom
end MonoidHom
