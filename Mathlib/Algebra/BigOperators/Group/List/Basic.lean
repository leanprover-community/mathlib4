/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Order.RelClasses
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Int.Defs

/-!
# Sums and products from lists

This file provides basic results about `List.prod`, `List.sum`, which calculate the product and sum
of elements of a list and `List.alternatingProd`, `List.alternatingSum`, their alternating
counterparts.
-/
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[to_additive]
theorem prod_eq_foldl : ∀ {l : List M}, l.prod = foldl (· * ·) 1 l
  | [] => rfl
  | cons a l => by
    rw [prod_cons, prod_eq_foldl, ← foldl_assoc (α := M) (op := (· * ·))]
    simp

@[to_additive (attr := simp)]
theorem prod_append : (l₁ ++ l₂).prod = l₁.prod * l₂.prod :=
  calc
    (l₁ ++ l₂).prod = foldr (· * ·) (1 * foldr (· * ·) 1 l₂) l₁ := by simp [List.prod]
    _ = l₁.prod * l₂.prod := foldr_assoc

@[to_additive]
theorem prod_concat : (l.concat a).prod = l.prod * a := by
  rw [concat_eq_append, prod_append, prod_singleton]

@[to_additive (attr := simp)]
theorem prod_flatten {l : List (List M)} : l.flatten.prod = (l.map List.prod).prod := by
  induction l with
  | nil => simp
  | cons head tail ih => simp only [*, List.flatten, map, prod_append, prod_cons]

open scoped Relator in
@[to_additive]
theorem rel_prod {R : M → N → Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod :=
  rel_foldr hf h

@[to_additive]
theorem prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (hl : l ≠ []) : (l.map f).prod = f l.prod :=
  match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

@[to_additive]
theorem prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    (l.map f).prod = f l.prod := by
  simp only [prod, foldr_map, ← map_one f]
  exact l.foldr_hom f (fun x y => (map_mul f x y).symm)

@[to_additive]
theorem prod_hom₂_nonempty {l : List ι} (f : M → N → P)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) (hl : l ≠ []) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  match l, hl with | x :: xs, hl => induction xs generalizing x <;> simp_all

@[to_additive]
theorem prod_hom₂ (l : List ι) (f : M → N → P) (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι → M) (f₂ : ι → N) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  rw [prod, prod, prod, foldr_map, foldr_map, foldr_map,
    ← l.foldr_hom₂ f _ _ (fun x y => f (f₁ x) (f₂ x) * y) _ _ (by simp [hf]), hf']

@[to_additive (attr := simp)]
theorem prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι → M} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
theorem prod_map_hom (L : List ι) (f : ι → M) {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) :
    (L.map (g ∘ f)).prod = g (L.map f).prod := by rw [← prod_hom, map_map]

@[to_additive (attr := simp)]
theorem prod_take_mul_prod_drop (L : List M) (i : ℕ) :
    (L.take i).prod * (L.drop i).prod = L.prod := by
  simp [← prod_append]

@[to_additive (attr := simp)]
theorem prod_take_succ (L : List M) (i : ℕ) (p : i < L.length) :
    (L.take (i + 1)).prod = (L.take i).prod * L[i] := by
  rw [← take_concat_get' _ _ p, prod_append]
  simp

/-- A list with product not one must have positive length. -/
@[to_additive "A list with sum not zero must have positive length."]
theorem length_pos_of_prod_ne_one (L : List M) (h : L.prod ≠ 1) : 0 < L.length := by
  cases L
  · simp at h
  · simp

/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos "A list with positive sum must have positive length."]
theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.prod) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne'

/-- A list with product less than one must have positive length. -/
@[to_additive "A list with negative sum must have positive length."]
theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.prod < 1) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne

@[to_additive]
theorem prod_set :
    ∀ (L : List M) (n : ℕ) (a : M),
      (L.set n a).prod =
        ((L.take n).prod * if n < L.length then a else 1) * (L.drop (n + 1)).prod
  | x :: xs, 0, a => by simp [set]
  | x :: xs, i + 1, a => by
    simp [set, prod_set xs i a, mul_assoc, Nat.add_lt_add_iff_right]
  | [], _, _ => by simp [set, (Nat.zero_le _).not_gt]

/-- We'd like to state this as `L.headI * L.tail.prod = L.prod`, but because `L.headI` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `L[0]?.getD 1`.
-/
@[to_additive "We'd like to state this as `L.headI + L.tail.sum = L.sum`, but because `L.headI`
  relies on an inhabited instance to return a garbage value on the empty list, this is not possible.
  Instead, we write the statement in terms of `L[0]?.getD 0`."]
theorem getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.prod := by
  cases l <;> simp

@[deprecated (since := "2025-02-15")] alias get?_zero_mul_tail_prod := getElem?_zero_mul_tail_prod
@[deprecated (since := "2025-02-15")] alias get?_zero_add_tail_sum := getElem?_zero_add_tail_sum

/-- Same as `get?_zero_mul_tail_prod`, but avoiding the `List.headI` garbage complication by
  requiring the list to be nonempty. -/
@[to_additive "Same as `get?_zero_add_tail_sum`, but avoiding the `List.headI` garbage complication
  by requiring the list to be nonempty."]
theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l ≠ []) :
    l.headI * l.tail.prod = l.prod := by cases l <;> [contradiction; simp]

@[to_additive]
theorem _root_.Commute.list_prod_right (l : List M) (y : M) (h : ∀ x ∈ l, Commute y x) :
    Commute y l.prod := by
  induction l with
  | nil => simp
  | cons z l IH =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)

@[to_additive]
theorem _root_.Commute.list_prod_left (l : List M) (y : M) (h : ∀ x ∈ l, Commute x y) :
    Commute l.prod y :=
  ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm

@[to_additive] lemma prod_range_succ (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = ((range n).map f).prod * f n := by
  rw [range_succ, map_append, map_singleton, prod_append, prod_cons, prod_nil, mul_one]

/-- A variant of `prod_range_succ` which pulls off the first term in the product rather than the
last. -/
@[to_additive
"A variant of `sum_range_succ` which pulls off the first term in the sum rather than the last."]
lemma prod_range_succ' (f : ℕ → M) (n : ℕ) :
    ((range n.succ).map f).prod = f 0 * ((range n).map fun i ↦ f i.succ).prod := by
  rw [range_succ_eq_map]
  simp [Function.comp_def]

@[to_additive] lemma prod_eq_one (hl : ∀ x ∈ l, x = 1) : l.prod = 1 := by
  induction l with
  | nil => rfl
  | cons i l hil =>
    rw [List.prod_cons, hil fun x hx ↦ hl _ (mem_cons_of_mem i hx),
      hl _ mem_cons_self, one_mul]

@[to_additive] lemma exists_mem_ne_one_of_prod_ne_one (h : l.prod ≠ 1) :
    ∃ x ∈ l, x ≠ (1 : M) := by simpa only [not_forall, exists_prop] using mt prod_eq_one h

@[to_additive]
lemma prod_erase_of_comm [DecidableEq M] (ha : a ∈ l) (comm : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) :
    a * (l.erase a).prod = l.prod := by
  induction l with
  | nil => simp only [not_mem_nil] at ha
  | cons b l ih =>
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
    · simp only [erase_cons_head, prod_cons]
    rw [List.erase, beq_false_of_ne ne.symm, List.prod_cons, List.prod_cons, ← mul_assoc,
      comm a ha b mem_cons_self, mul_assoc,
      ih h fun x hx y hy ↦ comm _ (List.mem_cons_of_mem b hx) _ (List.mem_cons_of_mem b hy)]

@[to_additive]
lemma prod_map_eq_pow_single [DecidableEq α] {l : List α} (a : α) (f : α → M)
    (hf : ∀ a', a' ≠ a → a' ∈ l → f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction l generalizing a with
  | nil => rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  | cons a' as h =>
    specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    simp only [beq_iff_eq]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ']
    · rw [hf a' ha' mem_cons_self, one_mul, add_zero]

@[to_additive]
lemma prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a', a' ≠ a → a' ∈ l → a' = 1) :
    l.prod = a ^ l.count a :=
  _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)

end Monoid

section CommMonoid
variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

@[to_additive (attr := simp)]
lemma prod_erase [DecidableEq M] (ha : a ∈ l) : a * (l.erase a).prod = l.prod :=
  prod_erase_of_comm ha fun x _ y _ ↦ mul_comm x y

@[to_additive (attr := simp)]
lemma prod_map_erase [DecidableEq α] (f : α → M) {a} :
    ∀ {l : List α}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]

@[to_additive] lemma Perm.prod_eq (h : Perm l₁ l₂) : prod l₁ = prod l₂ := h.foldr_op_eq

@[to_additive (attr := simp)]
lemma prod_reverse (l : List M) : prod l.reverse = prod l := (reverse_perm l).prod_eq

@[to_additive]
lemma prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    ∀ l l' : List M,
      l.prod * l'.prod =
        (zipWith (· * ·) l l').prod * (l.drop l'.length).prod * (l'.drop l.length).prod
  | [], ys => by simp
  | xs, [] => by simp
  | x :: xs, y :: ys => by
    simp only [drop, length, zipWith_cons_cons, prod_cons]
    conv =>
      lhs; rw [mul_assoc]; right; rw [mul_comm, mul_assoc]; right
      rw [mul_comm, prod_mul_prod_eq_prod_zipWith_mul_prod_drop xs ys]
    simp [mul_assoc]

@[to_additive]
lemma prod_mul_prod_eq_prod_zipWith_of_length_eq (l l' : List M) (h : l.length = l'.length) :
    l.prod * l'.prod = (zipWith (· * ·) l l').prod := by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h, drop_length, h, drop_length, prod_nil, mul_one, mul_one]

@[to_additive]
lemma prod_map_ite (p : α → Prop) [DecidablePred p] (f g : α → M) (l : List α) :
    (l.map fun a => if p a then f a else g a).prod =
      ((l.filter p).map f).prod * ((l.filter fun a ↦ ¬p a).map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, filter_cons, prod_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : p x
    · simp only [hx, ↓reduceIte, decide_not, decide_true, map_cons, prod_cons, not_true_eq_false,
        decide_false, Bool.false_eq_true, mul_assoc]
    · simp only [hx, ↓reduceIte, decide_not, decide_false, Bool.false_eq_true, not_false_eq_true,
      decide_true, map_cons, prod_cons, mul_left_comm]

@[to_additive]
lemma prod_map_filter_mul_prod_map_filter_not (p : α → Prop) [DecidablePred p] (f : α → M)
    (l : List α) :
    ((l.filter p).map f).prod * ((l.filter fun x => ¬p x).map f).prod = (l.map f).prod := by
  rw [← prod_map_ite]
  simp only [ite_self]

end CommMonoid

@[to_additive]
lemma eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).prod = (L'.take i).prod) : L = L' := by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁, prod_take_succ L' i h₂, h' i (le_of_lt h₁)] at this
  convert mul_left_cancel this

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
  · simp only [take_of_length_le (le_of_not_gt hn), prod_nil, mul_one,
      drop_eq_nil_of_le ((le_of_not_gt hn).trans n.le_succ)]

@[to_additive]
lemma prod_map_ite_eq {A : Type*} [DecidableEq A] (l : List A) (f g : A → G) (a : A) :
    (l.map fun x => if x = a then f x else g x).prod
      = (f a / g a) ^ (l.count a) * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, beq_self_eq_true]
    · simp only [hx, ite_false, add_zero, mul_assoc, mul_comm (g x) _, beq_iff_eq]

end CommGroup

theorem sum_const_nat (m n : ℕ) : sum (replicate m n) = m * n :=
  sum_replicate m n

/-!
Several lemmas about sum/head/tail for `List ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/

/-- This relies on `default ℕ = 0`. -/
theorem headI_add_tail_sum (L : List ℕ) : L.headI + L.tail.sum = L.sum := by
  cases L <;> simp

/-- This relies on `default ℕ = 0`. -/
theorem headI_le_sum (L : List ℕ) : L.headI ≤ L.sum :=
  Nat.le.intro (headI_add_tail_sum L)

/-- This relies on `default ℕ = 0`. -/
theorem tail_sum (L : List ℕ) : L.tail.sum = L.sum - L.headI := by
  rw [← headI_add_tail_sum L, add_comm, Nat.add_sub_cancel_right]

section Alternating

section

variable [One G] [Mul G] [Inv G]

@[to_additive (attr := simp)]
theorem alternatingProd_nil : alternatingProd ([] : List G) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem alternatingProd_singleton (a : G) : alternatingProd [a] = a :=
  rfl

@[to_additive]
theorem alternatingProd_cons_cons' (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl

end

@[to_additive]
theorem alternatingProd_cons_cons [DivInvMonoid G] (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons_cons']

variable [CommGroup G]

@[to_additive]
theorem alternatingProd_cons' :
    ∀ (a : G) (l : List G), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternatingProd_nil, inv_one, mul_one, alternatingProd_singleton]
  | a, b :: l => by
    rw [alternatingProd_cons_cons', alternatingProd_cons' b l, mul_inv, inv_inv, mul_assoc]

@[to_additive (attr := simp)]
theorem alternatingProd_cons (a : G) (l : List G) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, alternatingProd_cons']

end Alternating

lemma sum_nat_mod (l : List ℕ) (n : ℕ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)

lemma prod_nat_mod (l : List ℕ) (n : ℕ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)

lemma sum_int_mod (l : List ℤ) (n : ℤ) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Int.add_emod, *]

lemma prod_int_mod (l : List ℤ) (n : ℤ) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]

end List

section MonoidHom

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod = (l.map f).prod :=
  (l.prod_hom f).symm

namespace MonoidHom

@[to_additive]
protected theorem map_list_prod (f : M →* N) (l : List M) : f l.prod = (l.map f).prod :=
  map_list_prod f l

end MonoidHom

end MonoidHom

namespace List

/-- In a flatten, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the flatten of the first `i` sublists. -/
lemma take_sum_flatten (L : List (List α)) (i : ℕ) :
    L.flatten.take ((L.map length).take i).sum = (L.take i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_length_add_append, *]

/-- In a flatten, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
lemma drop_sum_flatten (L : List (List α)) (i : ℕ) :
    L.flatten.drop ((L.map length).take i).sum = (L.drop i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [*]

@[deprecated (since := "2024-10-25")] alias take_sum_join' := take_sum_flatten
@[deprecated (since := "2024-10-25")] alias drop_sum_join' := drop_sum_flatten

end List


namespace List

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons j L IH =>
    rw [sum_cons, length, add_comm]
    exact Nat.add_le_add (h _ mem_cons_self) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))

end List
