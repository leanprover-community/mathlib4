/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.OrderDual

/-!
# Big operators on a list in ordered groups

This file contains the results concerning the interaction of list big operators with ordered
groups/monoids.
-/

variable {ι α M N P M₀ G R : Type*}

namespace List
section Monoid
variable [Monoid M]

@[to_additive sum_le_sum]
lemma Forall₂.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : Forall₂ (· ≤ ·) l₁ l₂) :
    l₁.prod ≤ l₂.prod := by
  induction' h with a b la lb hab ih ih'
  · rfl
  · simpa only [prod_cons] using mul_le_mul' hab ih'
#align list.forall₂.prod_le_prod' List.Forall₂.prod_le_prod'
#align list.forall₂.sum_le_sum List.Forall₂.sum_le_sum

/-- If `l₁` is a sublist of `l₂` and all elements of `l₂` are greater than or equal to one, then
`l₁.prod ≤ l₂.prod`. One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 1 ≤ a` instead
of `∀ a ∈ l₂, 1 ≤ a` but this lemma is not yet in `mathlib`. -/
@[to_additive sum_le_sum "If `l₁` is a sublist of `l₂` and all elements of `l₂` are nonnegative,
  then `l₁.sum ≤ l₂.sum`.
  One can prove a stronger version assuming `∀ a ∈ l₂.diff l₁, 0 ≤ a` instead of `∀ a ∈ l₂, 0 ≤ a`
  but this lemma is not yet in `mathlib`."]
lemma Sublist.prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l₁ l₂ : List M} (h : l₁ <+ l₂)
    (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) : l₁.prod ≤ l₂.prod := by
  induction h with
  | slnil => rfl
  | cons a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact (ih' h₁.2).trans (le_mul_of_one_le_left' h₁.1)
  | cons₂ a _ ih' =>
    simp only [prod_cons, forall_mem_cons] at h₁ ⊢
    exact mul_le_mul_left' (ih' h₁.2) _
#align list.sublist.prod_le_prod' List.Sublist.prod_le_prod'
#align list.sublist.sum_le_sum List.Sublist.sum_le_sum

@[to_additive sum_le_sum]
lemma SublistForall₂.prod_le_prod' [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    {l₁ l₂ : List M} (h : SublistForall₂ (· ≤ ·) l₁ l₂) (h₁ : ∀ a ∈ l₂, (1 : M) ≤ a) :
    l₁.prod ≤ l₂.prod :=
  let ⟨_, hall, hsub⟩ := sublistForall₂_iff.1 h
  hall.prod_le_prod'.trans <| hsub.prod_le_prod' h₁
#align list.sublist_forall₂.prod_le_prod' List.SublistForall₂.prod_le_prod'
#align list.sublist_forall₂.sum_le_sum List.SublistForall₂.sum_le_sum

@[to_additive sum_le_sum]
lemma prod_le_prod' [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).prod ≤ (l.map g).prod :=
  Forall₂.prod_le_prod' <| by simpa
#align list.prod_le_prod' List.prod_le_prod'
#align list.sum_le_sum List.sum_le_sum

@[to_additive sum_lt_sum]
lemma prod_lt_prod' [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h₁ : ∀ i ∈ l, f i ≤ g i) (h₂ : ∃ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod := by
  induction' l with i l ihl
  · rcases h₂ with ⟨_, ⟨⟩, _⟩
  simp only [forall_mem_cons, map_cons, prod_cons] at h₁ ⊢
  simp only [mem_cons, exists_eq_or_imp] at h₂
  cases h₂
  · exact mul_lt_mul_of_lt_of_le ‹_› (prod_le_prod' h₁.2)
  · exact mul_lt_mul_of_le_of_lt h₁.1 <| ihl h₁.2 ‹_›
#align list.prod_lt_prod' List.prod_lt_prod'
#align list.sum_lt_sum List.sum_lt_sum

@[to_additive]
lemma prod_lt_prod_of_ne_nil [Preorder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (hlt : ∀ i ∈ l, f i < g i) : (l.map f).prod < (l.map g).prod :=
  (prod_lt_prod' f g fun i hi => (hlt i hi).le) <|
    (exists_mem_of_ne_nil l hl).imp fun i hi => ⟨hi, hlt i hi⟩
#align list.prod_lt_prod_of_ne_nil List.prod_lt_prod_of_ne_nil
#align list.sum_lt_sum_of_ne_nil List.sum_lt_sum_of_ne_nil

@[to_additive sum_le_card_nsmul]
lemma prod_le_pow_card [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] (l : List M) (n : M) (h : ∀ x ∈ l, x ≤ n) :
    l.prod ≤ n ^ l.length := by
      simpa only [map_id', map_const', prod_replicate] using prod_le_prod' h
#align list.prod_le_pow_card List.prod_le_pow_card
#align list.sum_le_card_nsmul List.sum_le_card_nsmul

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod [Preorder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) :
    n ^ l.length ≤ l.prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h
#align list.pow_card_le_prod List.pow_card_le_prod
#align list.card_nsmul_le_sum List.card_nsmul_le_sum

@[to_additive exists_lt_of_sum_lt]
lemma exists_lt_of_prod_lt' [LinearOrder M] [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] {l : List ι} (f g : ι → M)
    (h : (l.map f).prod < (l.map g).prod) : ∃ i ∈ l, f i < g i := by
  contrapose! h
  exact prod_le_prod' h
#align list.exists_lt_of_prod_lt' List.exists_lt_of_prod_lt'
#align list.exists_lt_of_sum_lt List.exists_lt_of_sum_lt

@[to_additive exists_le_of_sum_le]
lemma exists_le_of_prod_le' [LinearOrder M] [CovariantClass M M (· * ·) (· < ·)]
    [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (Function.swap (· * ·)) (· < ·)]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] {l : List ι} (hl : l ≠ []) (f g : ι → M)
    (h : (l.map f).prod ≤ (l.map g).prod) : ∃ x ∈ l, f x ≤ g x := by
  contrapose! h
  exact prod_lt_prod_of_ne_nil hl _ _ h
#align list.exists_le_of_prod_le' List.exists_le_of_prod_le'
#align list.exists_le_of_sum_le List.exists_le_of_sum_le

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.prod := by
  -- We don't use `pow_card_le_prod` to avoid assumption
  -- [covariant_class M M (function.swap (*)) (≤)]
  induction' l with hd tl ih
  · rfl
  rw [prod_cons]
  exact one_le_mul (hl₁ hd (mem_cons_self hd tl)) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))
#align list.one_le_prod_of_one_le List.one_le_prod_of_one_le
#align list.sum_nonneg List.sum_nonneg

end Monoid

-- TODO: develop theory of tropical rings
lemma sum_le_foldr_max [AddMonoid M] [AddMonoid N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.sum ≤ (l.map f).foldr max 0 := by
  induction' l with hd tl IH
  · simpa using h0
  simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
  exact (hadd _ _).trans (max_le_max le_rfl IH)
#align list.sum_le_foldr_max List.sum_le_foldr_max

@[to_additive sum_pos]
lemma one_lt_prod_of_one_lt [OrderedCommMonoid M] :
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
#align list.one_lt_prod_of_one_lt List.one_lt_prod_of_one_lt
#align list.sum_pos List.sum_pos

@[to_additive]
lemma single_le_prod [OrderedCommMonoid M] {l : List M} (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) :
    ∀ x ∈ l, x ≤ l.prod := by
  induction l
  · simp
  simp_rw [prod_cons, forall_mem_cons] at hl₁ ⊢
  constructor
  case cons.left => exact le_mul_of_one_le_right' (one_le_prod_of_one_le hl₁.2)
  case cons.right hd tl ih => exact fun x H => le_mul_of_one_le_of_le hl₁.1 (ih hl₁.right x H)
#align list.single_le_prod List.single_le_prod
#align list.single_le_sum List.single_le_sum

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one [OrderedCommMonoid M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) (hl₂ : l.prod = 1) {x : M} (hx : x ∈ l) : x = 1 :=
  _root_.le_antisymm (hl₂ ▸ single_le_prod hl₁ _ hx) (hl₁ x hx)
#align list.all_one_of_le_one_le_of_prod_eq_one List.all_one_of_le_one_le_of_prod_eq_one
#align list.all_zero_of_le_zero_le_of_sum_eq_zero List.all_zero_of_le_zero_le_of_sum_eq_zero

section CanonicallyOrderedCommMonoid
variable [CanonicallyOrderedCommMonoid M] {l : List M}

@[to_additive] lemma prod_eq_one_iff : l.prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, fun h => by
    rw [List.eq_replicate.2 ⟨_, h⟩, prod_replicate, one_pow]
    · exact (length l)
    · rfl⟩
#align list.prod_eq_one_iff List.prod_eq_one_iff
#align list.sum_eq_zero_iff List.sum_eq_zero_iff

@[to_additive] lemma monotone_prod_take (L : List M) : Monotone fun i => (L.take i).prod := by
  refine monotone_nat_of_le_succ fun n => ?_
  cases' lt_or_le n L.length with h h
  · rw [prod_take_succ _ _ h]
    exact le_self_mul
  · simp [take_all_of_le h, take_all_of_le (le_trans h (Nat.le_succ _))]
#align list.monotone_prod_take List.monotone_prod_take
#align list.monotone_sum_take List.monotone_sum_take

end CanonicallyOrderedCommMonoid
end List
