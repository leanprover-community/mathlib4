/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Big operators on a list in ordered groups

This file contains the results concerning the interaction of list big operators with ordered
groups/monoids.
-/

variable {ι α M N : Type*}

namespace List
section Monoid
variable [Monoid M]

@[to_additive sum_le_sum]
lemma Forall₂.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.prod ≤ l₂.prod := by
  induction h with
  | nil => rfl
  | cons hab ih ih' => simpa only [prod_cons] using mul_le_mul' hab ih'

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum "If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,
  then `l₁.sum ≤ l₂.sum`.
  One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead of `∀ a ∈ l₂, 0 ≤ a`
  but this lemma is not yet in `mathlib`."]
lemma Sublist.prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.prod ≤ l₂.prod := by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons₂ a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact mul_le_mul_left' (ih' h₁.2) _

@[to_additive sum_le_sum]
lemma SublistForall₂.prod_le_prod' [Preorder M]
    [MulRightMono M] [MulLeftMono M]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.prod ≤ l₂.prod :=
  let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁

@[to_additive sum_le_sum]
lemma prod_le_prod' [Preorder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).prod ≤ (l.map g).prod :=
  Forall₂.prod_le_prod' <| by simpa

@[to_additive sum_lt_sum]
lemma prod_lt_prod' [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod := by
  induction' l with i l ihl
  · rcases h₂ with ⟨_, ⟨⟩, _⟩
  simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
  simp only [mem_cons, exists_eq_or_imp] at h₂
  cases h₂
  · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
  · exact mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 ‹_›

@[to_additive]
lemma prod_lt_prod_of_ne_nil [Preorder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (hlt : ∀ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod :=
  (prod_lt_prod' f g fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩

@[to_additive sum_le_card_nsmul]
lemma prod_le_pow_card [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.prod ≤ n ^ l.length := by
  simpa only [map_id', map_const', prod_replicate] using prod_le_prod' h

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod [Preorder M] [MulRightMono M]
    [MulLeftMono M] (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) :
    n ^ l.length ≤ l.prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h

@[to_additive exists_lt_of_sum_lt]
lemma exists_lt_of_prod_lt' [LinearOrder M] [MulRightMono M]
    [MulLeftMono M] {l : List ι} (f g : ι → M)
    (h : (l.map f).prod < (l.map g).prod) : ∃ i ∈ l, f i < g i := by
  contrapose! h
  exact prod_le_prod' h

@[to_additive exists_le_of_sum_le]
lemma exists_le_of_prod_le' [LinearOrder M] [MulLeftStrictMono M]
    [MulLeftMono M] [MulRightStrictMono M]
    [MulRightMono M] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).prod ≤ (l.map g).prod) : ∃ x ∈ l, f x ≤ g x := by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le [Preorder M] [MulLeftMono M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.prod := by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [covariant_class M M (function.swap (*)) (≤)]
  induction' l with hd tl ih
  · rfl
  rw [prod_cons]
  exact one_le_mul (hl₁ hd mem_cons_self) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

@[to_additive]
lemma max_prod_le (l : List α) (f g : α → M) [LinearOrder M]
    [MulLeftMono M] [MulRightMono M] :
    max (l.map f).prod (l.map g).prod ≤ (l.map fun i ↦ max (f i) (g i)).prod := by
  rw [max_le_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply le_max_left
  · apply le_max_right

@[to_additive]
lemma prod_min_le [LinearOrder M] [MulLeftMono M]
    [MulRightMono M] (l : List α) (f g : α → M) :
    (l.map fun i ↦ min (f i) (g i)).prod ≤ min (l.map f).prod (l.map g).prod := by
  rw [le_min_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply min_le_left
  · apply min_le_right

end Monoid

-- TODO: develop theory of tropical rings
lemma sum_le_foldr_max [AddZeroClass M] [Zero N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.sum ≤ (l.map f).foldr max 0 := by
  induction' l with hd tl IH
  · simpa using h0
  simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
  exact (hadd _ _).trans (max_le_max le_rfl IH)

@[to_additive sum_pos]
lemma one_lt_prod_of_one_lt [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] :
    ∀ l : List M, (∀ x ∈ l, (1 : M) < x) → l ≠ [] → 1 < l.prod
  | [], _, h => (h rfl).elim
  | [b], h, _ => by simpa using h
  | a :: b :: l, hl₁, _ => by
    simp only [forall_eq_or_imp, List.mem_cons] at hl₁
    rw [List.prod_cons]
    apply one_lt_mul_of_lt_of_le' hl₁.1
    apply le_of_lt ((b :: l).one_lt_prod_of_one_lt _ (l.cons_ne_nil b))
    intro x hx; cases hx
    · exact hl₁.2.1
    · exact hl₁.2.2 _ ‹_›

/-- See also `List.le_prod_of_mem`. -/
@[to_additive "See also `List.le_sum_of_mem`."]
lemma single_le_prod [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
    ∀ x ∈ l, x ≤ l.prod := by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  constructor
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M]
    {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)

section CanonicallyOrderedMul
variable [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M] {l : List M}

@[to_additive] lemma prod_eq_one_iff [IsOrderedMonoid M] : l.prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, fun h => by
    rw [List.eq_replicate_iff.2 ⟨_, h⟩, prod_replicate, one_pow]
    · exact (length l)
    · rfl⟩

@[to_additive] lemma monotone_prod_take (L : List M) : Monotone fun i => (L.take i).prod := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases lt_or_ge n L.length with h | h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_of_length_le h, take_of_length_le (le_trans h (Nat.le_succ _))]

/-- See also `List.single_le_prod`. -/
@[to_additive "See also `List.single_le_sum`."]
theorem le_prod_of_mem {xs : List M} {x : M} (h₁ : x ∈ xs) : x ≤ xs.prod := by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · simp
    · specialize ih h₁
      simp only [List.prod_cons]
      exact le_mul_left ih

end CanonicallyOrderedMul

end List
