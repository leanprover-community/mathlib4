/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity.Core

#align_import algebra.big_operators.order from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Big operators on a finset in ordered groups

This file contains the results concerning the interaction of multiset big operators with ordered
groups/monoids.
-/

open Function

variable {ι α β M N G k R : Type*}

namespace Finset

section OrderedCommMonoid

variable [CommMonoid M] [OrderedCommMonoid N]

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x ∈ s, g x) ≤ ∏ x ∈ s, f (g x)`. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred (f : M → N) (p : M → Prop)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  rw [Multiset.map_map]
  rfl
#align finset.le_prod_nonempty_of_submultiplicative_on_pred Finset.le_prod_nonempty_of_submultiplicative_on_pred
#align finset.le_sum_nonempty_of_subadditive_on_pred Finset.le_sum_nonempty_of_subadditive_on_pred

/-- Let `{x | p x}` be an additive subsemigroup of an additive commutative monoid `M`. Let
`f : M → N` be a map subadditive on `{x | p x}`, i.e., `p x → p y → f (x + y) ≤ f x + f y`. Let
`g i`, `i ∈ s`, be a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative (f : M → N) (h_mul : ∀ x y, f (x * y) ≤ f x * f y)
    {s : Finset ι} (hs : s.Nonempty) (g : ι → M) : f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ ↦ True) (fun x y _ _ ↦ h_mul x y)
    (fun _ _ _ _ ↦ trivial) g s hs fun _ _ ↦ trivial
#align finset.le_prod_nonempty_of_submultiplicative Finset.le_prod_nonempty_of_submultiplicative
#align finset.le_sum_nonempty_of_subadditive Finset.le_sum_nonempty_of_subadditive

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred (f : M → N) (p : M → Prop) (h_one : f 1 = 1)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) {s : Finset ι} (hs : ∀ i ∈ s, p (g i)) : f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs
#align finset.le_prod_of_submultiplicative_on_pred Finset.le_prod_of_submultiplicative_on_pred
#align finset.le_sum_of_subadditive_on_pred Finset.le_sum_of_subadditive_on_pred

/-- Let `{x | p x}` be a subsemigroup of a commutative additive monoid `M`. Let `f : M → N` be a map
such that `f 0 = 0` and `f` is subadditive on `{x | p x}`, i.e. `p x → p y → f (x + y) ≤ f x + f y`.
Let `g i`, `i ∈ s`, be a finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ x ∈ s, g x) ≤ ∑ x ∈ s, f (g x)`. -/
add_decl_doc le_sum_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i)`. -/
@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative (f : M → N) (h_one : f 1 = 1)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  refine le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) ?_
  rw [Multiset.map_map]
  rfl
#align finset.le_prod_of_submultiplicative Finset.le_prod_of_submultiplicative
#align finset.le_sum_of_subadditive Finset.le_sum_of_subadditive

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y`, `f 0 = 0`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f (g i)`. -/
add_decl_doc le_sum_of_subadditive

variable {f g : ι → N} {s t : Finset ι}

/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i ∈ s, f i ≤ ∏ i ∈ s, g i`. -/
@[to_additive sum_le_sum]
theorem prod_le_prod' (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
  Multiset.prod_map_le_prod_map f g h
#align finset.prod_le_prod' Finset.prod_le_prod'
#align finset.sum_le_sum Finset.sum_le_sum

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then
`∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`. -/
add_decl_doc sum_le_sum

/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then `s.prod f ≤ s.prod g`.

This is a variant (beta-reduced) version of the standard lemma `Finset.prod_le_prod'`, convenient
for the `gcongr` tactic. -/
@[to_additive (attr := gcongr) GCongr.sum_le_sum]
theorem _root_.GCongr.prod_le_prod' (h : ∀ i ∈ s, f i ≤ g i) : s.prod f ≤ s.prod g :=
  s.prod_le_prod' h

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then `s.sum f ≤ s.sum g`.

This is a variant (beta-reduced) version of the standard lemma `Finset.sum_le_sum`, convenient
for the `gcongr` tactic. -/
add_decl_doc GCongr.sum_le_sum

@[to_additive sum_nonneg]
theorem one_le_prod' (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)
#align finset.one_le_prod' Finset.one_le_prod'
#align finset.sum_nonneg Finset.sum_nonneg

@[to_additive Finset.sum_nonneg']
theorem one_le_prod'' (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i :=
  Finset.one_le_prod' fun i _ ↦ h i
#align finset.one_le_prod'' Finset.one_le_prod''
#align finset.sum_nonneg' Finset.sum_nonneg'

@[to_additive sum_nonpos]
theorem prod_le_one' (h : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 :=
  (prod_le_prod' h).trans_eq (by rw [prod_const_one])
#align finset.prod_le_one' Finset.prod_le_one'
#align finset.sum_nonpos Finset.sum_nonpos

@[to_additive sum_le_sum_of_subset_of_nonneg]
theorem prod_le_prod_of_subset_of_one_le' (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]
#align finset.prod_le_prod_of_subset_of_one_le' Finset.prod_le_prod_of_subset_of_one_le'
#align finset.sum_le_sum_of_subset_of_nonneg Finset.sum_le_sum_of_subset_of_nonneg

@[to_additive sum_mono_set_of_nonneg]
theorem prod_mono_set_of_one_le' (hf : ∀ x, 1 ≤ f x) : Monotone fun s ↦ ∏ x ∈ s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le' hst fun x _ _ ↦ hf x
#align finset.prod_mono_set_of_one_le' Finset.prod_mono_set_of_one_le'
#align finset.sum_mono_set_of_nonneg Finset.sum_mono_set_of_nonneg

@[to_additive sum_le_univ_sum_of_nonneg]
theorem prod_le_univ_prod_of_one_le' [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ ↦ w a
#align finset.prod_le_univ_prod_of_one_le' Finset.prod_le_univ_prod_of_one_le'
#align finset.sum_le_univ_sum_of_nonneg Finset.sum_le_univ_sum_of_nonneg

-- Porting note (#11215): TODO -- The two next lemmas give the same lemma in additive version
@[to_additive sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_one_le' :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.not_mem_empty _ h), fun _ ↦ rfl⟩) ?_
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff' (H _ <| mem_insert_self _ _) (one_le_prod' this),
      forall_mem_insert, ih this]
#align finset.prod_eq_one_iff_of_one_le' Finset.prod_eq_one_iff_of_one_le'
#align finset.sum_eq_zero_iff_of_nonneg Finset.sum_eq_zero_iff_of_nonneg

@[to_additive sum_eq_zero_iff_of_nonpos]
theorem prod_eq_one_iff_of_le_one' :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  @prod_eq_one_iff_of_one_le' _ Nᵒᵈ _ _ _
#align finset.prod_eq_one_iff_of_le_one' Finset.prod_eq_one_iff_of_le_one'

@[to_additive single_le_sum]
theorem single_le_prod' (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) : f a ≤ ∏ x ∈ s, f x :=
  calc
    f a = ∏ i ∈ {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i ∈ s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi
#align finset.single_le_prod' Finset.single_le_prod'
#align finset.single_le_sum Finset.single_le_sum

@[to_additive]
lemma mul_le_prod {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
    f i * f j ≤ ∏ k ∈ s, f k :=
  calc
    f i * f j = ∏ k ∈ .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ ≤ ∏ k ∈ s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ ↦ hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ s.card := by
  refine (Multiset.prod_le_pow_card (s.val.map f) n ?_).trans ?_
  · simpa using h
  · simp
#align finset.prod_le_pow_card Finset.prod_le_pow_card
#align finset.sum_le_card_nsmul Finset.sum_le_card_nsmul

@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ s.card ≤ s.prod f := @Finset.prod_le_pow_card _ Nᵒᵈ _ _ _ _ h
#align finset.pow_card_le_prod Finset.pow_card_le_prod
#align finset.card_nsmul_le_sum Finset.card_nsmul_le_sum

theorem card_biUnion_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι → Finset β) (n : ℕ)
    (h : ∀ a ∈ s, (f a).card ≤ n) : (s.biUnion f).card ≤ s.card * n :=
  card_biUnion_le.trans <| sum_le_card_nsmul _ _ _ h
#align finset.card_bUnion_le_card_mul Finset.card_biUnion_le_card_mul

variable {ι' : Type*} [DecidableEq ι']

-- Porting note: Mathport warning: expanding binder collection (y «expr ∉ » t)
@[to_additive sum_fiberwise_le_sum_of_sum_fiber_nonneg]
theorem prod_fiberwise_le_prod_of_one_le_prod_fiber' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ y ∉ t, (1 : N) ≤ ∏ x ∈ s.filter fun x ↦ g x = y, f x) :
    (∏ y ∈ t, ∏ x ∈ s.filter fun x ↦ g x = y, f x) ≤ ∏ x ∈ s, f x :=
  calc
    (∏ y ∈ t, ∏ x ∈ s.filter fun x ↦ g x = y, f x) ≤
        ∏ y ∈ t ∪ s.image g, ∏ x ∈ s.filter fun x ↦ g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ ↦ h y
    _ = ∏ x ∈ s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _
#align finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'
#align finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg

-- Porting note: Mathport warning: expanding binder collection (y «expr ∉ » t)
@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ y ∉ t, ∏ x ∈ s.filter fun x ↦ g x = y, f x ≤ 1) :
    ∏ x ∈ s, f x ≤ ∏ y ∈ t, ∏ x ∈ s.filter fun x ↦ g x = y, f x :=
  @prod_fiberwise_le_prod_of_one_le_prod_fiber' _ Nᵒᵈ _ _ _ _ _ _ _ h
#align finset.prod_le_prod_fiberwise_of_prod_fiber_le_one' Finset.prod_le_prod_fiberwise_of_prod_fiber_le_one'
#align finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos Finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos

end OrderedCommMonoid

theorem abs_sum_le_sum_abs {G : Type*} [LinearOrderedAddCommGroup G] (f : ι → G) (s : Finset ι) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := le_sum_of_subadditive _ abs_zero abs_add s f
#align finset.abs_sum_le_sum_abs Finset.abs_sum_le_sum_abs

theorem abs_sum_of_nonneg {G : Type*} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i ∈ s, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]
#align finset.abs_sum_of_nonneg Finset.abs_sum_of_nonneg

theorem abs_sum_of_nonneg' {G : Type*} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]
#align finset.abs_sum_of_nonneg' Finset.abs_sum_of_nonneg'

section Pigeonhole

variable [DecidableEq β]

theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, (s.filter fun x ↦ f x = a).card ≤ n) :
    s.card ≤ n * t.card :=
  calc
    s.card = ∑ a ∈ t, (s.filter fun x ↦ f x = a).card := card_eq_sum_card_fiberwise Hf
    _ ≤ ∑ _a ∈ t, n := sum_le_sum hn
    _ = _ := by simp [mul_comm]
#align finset.card_le_mul_card_image_of_maps_to Finset.card_le_mul_card_image_of_maps_to

theorem card_le_mul_card_image {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ a ∈ s.image f, (s.filter fun x ↦ f x = a).card ≤ n) : s.card ≤ n * (s.image f).card :=
  card_le_mul_card_image_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn
#align finset.card_le_mul_card_image Finset.card_le_mul_card_image

theorem mul_card_image_le_card_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, n ≤ (s.filter fun x ↦ f x = a).card) :
    n * t.card ≤ s.card :=
  calc
    n * t.card = ∑ _a ∈ t, n := by simp [mul_comm]
    _ ≤ ∑ a ∈ t, (s.filter fun x ↦ f x = a).card := sum_le_sum hn
    _ = s.card := by rw [← card_eq_sum_card_fiberwise Hf]
#align finset.mul_card_image_le_card_of_maps_to Finset.mul_card_image_le_card_of_maps_to

theorem mul_card_image_le_card {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ a ∈ s.image f, n ≤ (s.filter fun x ↦ f x = a).card) : n * (s.image f).card ≤ s.card :=
  mul_card_image_le_card_of_maps_to (fun _ ↦ mem_image_of_mem _) n hn
#align finset.mul_card_image_le_card Finset.mul_card_image_le_card

end Pigeonhole

section DoubleCounting

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

/-- If every element belongs to at most `n` Finsets, then the sum of their sizes is at most `n`
times how many they are. -/
theorem sum_card_inter_le (h : ∀ a ∈ s, (B.filter (a ∈ ·)).card ≤ n) :
    (∑ t ∈ B, (s ∩ t).card) ≤ s.card * n := by
  refine le_trans ?_ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
#align finset.sum_card_inter_le Finset.sum_card_inter_le

/-- If every element belongs to at most `n` Finsets, then the sum of their sizes is at most `n`
times how many they are. -/
theorem sum_card_le [Fintype α] (h : ∀ a, (B.filter (a ∈ ·)).card ≤ n) :
    ∑ s ∈ B, s.card ≤ Fintype.card α * n :=
  calc
    ∑ s ∈ B, s.card = ∑ s ∈ B, (univ ∩ s).card := by simp_rw [univ_inter]
    _ ≤ Fintype.card α * n := sum_card_inter_le fun a _ ↦ h a
#align finset.sum_card_le Finset.sum_card_le

/-- If every element belongs to at least `n` Finsets, then the sum of their sizes is at least `n`
times how many they are. -/
theorem le_sum_card_inter (h : ∀ a ∈ s, n ≤ (B.filter (a ∈ ·)).card) :
    s.card * n ≤ ∑ t ∈ B, (s ∩ t).card := by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
#align finset.le_sum_card_inter Finset.le_sum_card_inter

/-- If every element belongs to at least `n` Finsets, then the sum of their sizes is at least `n`
times how many they are. -/
theorem le_sum_card [Fintype α] (h : ∀ a, n ≤ (B.filter (a ∈ ·)).card) :
    Fintype.card α * n ≤ ∑ s ∈ B, s.card :=
  calc
    Fintype.card α * n ≤ ∑ s ∈ B, (univ ∩ s).card := le_sum_card_inter fun a _ ↦ h a
    _ = ∑ s ∈ B, s.card := by simp_rw [univ_inter]
#align finset.le_sum_card Finset.le_sum_card

/-- If every element belongs to exactly `n` Finsets, then the sum of their sizes is `n` times how
many they are. -/
theorem sum_card_inter (h : ∀ a ∈ s, (B.filter (a ∈ ·)).card = n) :
    (∑ t ∈ B, (s ∩ t).card) = s.card * n :=
  (sum_card_inter_le fun a ha ↦ (h a ha).le).antisymm (le_sum_card_inter fun a ha ↦ (h a ha).ge)
#align finset.sum_card_inter Finset.sum_card_inter

/-- If every element belongs to exactly `n` Finsets, then the sum of their sizes is `n` times how
many they are. -/
theorem sum_card [Fintype α] (h : ∀ a, (B.filter (a ∈ ·)).card = n) :
    ∑ s ∈ B, s.card = Fintype.card α * n := by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ ↦ h a, univ_inter]
#align finset.sum_card Finset.sum_card

theorem card_le_card_biUnion {s : Finset ι} {f : ι → Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
    (hf : ∀ i ∈ s, (f i).Nonempty) : s.card ≤ (s.biUnion f).card := by
  rw [card_biUnion hs, card_eq_sum_ones]
  exact sum_le_sum fun i hi ↦ (hf i hi).card_pos
#align finset.card_le_card_bUnion Finset.card_le_card_biUnion

theorem card_le_card_biUnion_add_card_fiber {s : Finset ι} {f : ι → Finset α}
    (hs : (s : Set ι).PairwiseDisjoint f) :
    s.card ≤ (s.biUnion f).card + (s.filter fun i ↦ f i = ∅).card := by
  rw [← Finset.filter_card_add_filter_neg_card_eq_card fun i ↦ f i = ∅, add_comm]
  exact
    add_le_add_right
      ((card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi ↦
            nonempty_of_ne_empty <| (mem_filter.1 hi).2).trans <|
        card_le_card <| biUnion_subset_biUnion_of_subset_left _ <| filter_subset _ _)
      _
#align finset.card_le_card_bUnion_add_card_fiber Finset.card_le_card_biUnion_add_card_fiber

theorem card_le_card_biUnion_add_one {s : Finset ι} {f : ι → Finset α} (hf : Injective f)
    (hs : (s : Set ι).PairwiseDisjoint f) : s.card ≤ (s.biUnion f).card + 1 :=
  (card_le_card_biUnion_add_card_fiber hs).trans <|
    add_le_add_left
      (card_le_one.2 fun _ hi _ hj ↦ hf <| (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) _
#align finset.card_le_card_bUnion_add_one Finset.card_le_card_biUnion_add_one

end DoubleCounting

section CanonicallyOrderedCommMonoid

variable [CanonicallyOrderedCommMonoid M] {f : ι → M} {s t : Finset ι}

/-- In a canonically-ordered monoid, a product bounds each of its terms.

See also `Finset.single_le_prod'`. -/
@[to_additive "In a canonically-ordered additive monoid, a sum bounds each of its terms.

See also `Finset.single_le_sum`."]
lemma _root_.CanonicallyOrderedCommMonoid.single_le_prod {i : ι} (hi : i ∈ s) :
    f i ≤ ∏ j ∈ s, f j :=
  single_le_prod' (fun _ _ ↦ one_le _) hi

@[to_additive (attr := simp) sum_eq_zero_iff]
theorem prod_eq_one_iff' : ∏ x ∈ s, f x = 1 ↔ ∀ x ∈ s, f x = 1 :=
  prod_eq_one_iff_of_one_le' fun x _ ↦ one_le (f x)
#align finset.prod_eq_one_iff' Finset.prod_eq_one_iff'
#align finset.sum_eq_zero_iff Finset.sum_eq_zero_iff

@[to_additive sum_le_sum_of_subset]
theorem prod_le_prod_of_subset' (h : s ⊆ t) : ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x :=
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ ↦ one_le _
#align finset.prod_le_prod_of_subset' Finset.prod_le_prod_of_subset'
#align finset.sum_le_sum_of_subset Finset.sum_le_sum_of_subset

@[to_additive sum_mono_set]
theorem prod_mono_set' (f : ι → M) : Monotone fun s ↦ ∏ x ∈ s, f x := fun _ _ hs ↦
  prod_le_prod_of_subset' hs
#align finset.prod_mono_set' Finset.prod_mono_set'
#align finset.sum_mono_set Finset.sum_mono_set

@[to_additive sum_le_sum_of_ne_zero]
theorem prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  classical calc
    ∏ x ∈ s, f x = (∏ x ∈ s.filter fun x ↦ f x = 1, f x) *
        ∏ x ∈ s.filter fun x ↦ f x ≠ 1, f x := by
      rw [← prod_union, filter_union_filter_neg_eq]
      exact disjoint_filter.2 fun _ _ h n_h ↦ n_h h
    _ ≤ ∏ x ∈ t, f x :=
      mul_le_of_le_one_of_le
        (prod_le_one' <| by simp only [mem_filter, and_imp]; exact fun _ _ ↦ le_of_eq)
        (prod_le_prod_of_subset' <| by simpa only [subset_iff, mem_filter, and_imp] )
#align finset.prod_le_prod_of_ne_one' Finset.prod_le_prod_of_ne_one'
#align finset.sum_le_sum_of_ne_zero Finset.sum_le_sum_of_ne_zero

end CanonicallyOrderedCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}

@[to_additive sum_lt_sum]
theorem prod_lt_prod' (hle : ∀ i ∈ s, f i ≤ g i) (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  Multiset.prod_lt_prod' hle hlt
#align finset.prod_lt_prod' Finset.prod_lt_prod'
#align finset.sum_lt_sum Finset.sum_lt_sum

@[to_additive sum_lt_sum_of_nonempty]
theorem prod_lt_prod_of_nonempty' (hs : s.Nonempty) (hlt : ∀ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i :=
  Multiset.prod_lt_prod_of_nonempty' (by aesop) hlt
#align finset.prod_lt_prod_of_nonempty' Finset.prod_lt_prod_of_nonempty'
#align finset.sum_lt_sum_of_nonempty Finset.sum_lt_sum_of_nonempty

/-- In an ordered commutative monoid, if each factor `f i` of one nontrivial finite product is
strictly less than the corresponding factor `g i` of another nontrivial finite product, then
`s.prod f < s.prod g`.

This is a variant (beta-reduced) version of the standard lemma `Finset.prod_lt_prod_of_nonempty'`,
convenient for the `gcongr` tactic. -/
@[to_additive (attr := gcongr) GCongr.sum_lt_sum_of_nonempty]
theorem _root_.GCongr.prod_lt_prod_of_nonempty' (hs : s.Nonempty) (Hlt : ∀ i ∈ s, f i < g i) :
    s.prod f < s.prod g :=
  s.prod_lt_prod_of_nonempty' hs Hlt

/-- In an ordered additive commutative monoid, if each summand `f i` of one nontrivial finite sum is
strictly less than the corresponding summand `g i` of another nontrivial finite sum, then
`s.sum f < s.sum g`.

This is a variant (beta-reduced) version of the standard lemma `Finset.sum_lt_sum_of_nonempty`,
convenient for the `gcongr` tactic. -/
add_decl_doc GCongr.sum_lt_sum_of_nonempty

-- Porting note (#11215): TODO -- calc indentation
@[to_additive sum_lt_sum_of_subset]
theorem prod_lt_prod_of_subset' (h : s ⊆ t) {i : ι} (ht : i ∈ t) (hs : i ∉ s) (hlt : 1 < f i)
    (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) : ∏ j ∈ s, f j < ∏ j ∈ t, f j := by
  classical calc
    ∏ j ∈ s, f j < ∏ j ∈ insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j ∈ s, f j) hlt
    _ ≤ ∏ j ∈ t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
        simp only [mem_insert, not_or] at h'x
        exact hle x hx h'x.2
#align finset.prod_lt_prod_of_subset' Finset.prod_lt_prod_of_subset'
#align finset.sum_lt_sum_of_subset Finset.sum_lt_sum_of_subset

@[to_additive single_lt_sum]
theorem single_lt_prod' {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s) (hlt : 1 < f j)
    (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) : f i < ∏ k ∈ s, f k :=
  calc
    f i = ∏ k ∈ {i}, f k := by rw [prod_singleton]
    _ < ∏ k ∈ s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki ↦ hle k hks (mt mem_singleton.2 hki)
#align finset.single_lt_prod' Finset.single_lt_prod'
#align finset.single_lt_sum Finset.single_lt_sum

@[to_additive sum_pos]
theorem one_lt_prod (h : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) : 1 < ∏ i ∈ s, f i :=
  lt_of_le_of_lt (by rw [prod_const_one]) <| prod_lt_prod_of_nonempty' hs h
#align finset.one_lt_prod Finset.one_lt_prod
#align finset.sum_pos Finset.sum_pos

@[to_additive]
theorem prod_lt_one (h : ∀ i ∈ s, f i < 1) (hs : s.Nonempty) : ∏ i ∈ s, f i < 1 :=
  (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])
#align finset.prod_lt_one Finset.prod_lt_one
#align finset.sum_neg Finset.sum_neg

@[to_additive sum_pos']
theorem one_lt_prod' (h : ∀ i ∈ s, 1 ≤ f i) (hs : ∃ i ∈ s, 1 < f i) : 1 < ∏ i ∈ s, f i :=
  prod_const_one.symm.trans_lt <| prod_lt_prod' h hs
#align finset.one_lt_prod' Finset.one_lt_prod'
#align finset.sum_pos' Finset.sum_pos'

@[to_additive]
theorem prod_lt_one' (h : ∀ i ∈ s, f i ≤ 1) (hs : ∃ i ∈ s, f i < 1) : ∏ i ∈ s, f i < 1 :=
  prod_const_one.le.trans_lt' <| prod_lt_prod' h hs
#align finset.prod_lt_one' Finset.prod_lt_one'
#align finset.sum_neg' Finset.sum_neg'

@[to_additive]
theorem prod_eq_prod_iff_of_le {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) :
    ((∏ i ∈ s, f i) = ∏ i ∈ s, g i) ↔ ∀ i ∈ s, f i = g i := by
  classical
    revert h
    refine Finset.induction_on s (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.not_mem_empty _ h),
      fun _ ↦ rfl⟩) fun a s ha ih H ↦ ?_
    specialize ih fun i ↦ H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.forall_mem_insert, ← ih]
    exact
      mul_eq_mul_iff_eq_and_eq (H a (s.mem_insert_self a))
        (Finset.prod_le_prod' fun i ↦ H i ∘ Finset.mem_insert_of_mem)
#align finset.prod_eq_prod_iff_of_le Finset.prod_eq_prod_iff_of_le
#align finset.sum_eq_sum_iff_of_le Finset.sum_eq_sum_iff_of_le

variable [DecidableEq ι]

@[to_additive] lemma prod_sdiff_le_prod_sdiff :
    ∏ i ∈ s \ t, f i ≤ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← mul_le_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter];
  simpa only [inter_comm] using disjoint_sdiff_inter t s

@[to_additive] lemma prod_sdiff_lt_prod_sdiff :
    ∏ i ∈ s \ t, f i < ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i < ∏ i ∈ t, f i := by
  rw [← mul_lt_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter];
  simpa only [inter_comm] using disjoint_sdiff_inter t s

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}

@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' (Hlt : ∏ i ∈ s, f i < ∏ i ∈ s, g i) : ∃ i ∈ s, f i < g i := by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle
#align finset.exists_lt_of_prod_lt' Finset.exists_lt_of_prod_lt'
#align finset.exists_lt_of_sum_lt Finset.exists_lt_of_sum_lt

@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt
#align finset.exists_le_of_prod_le' Finset.exists_le_of_prod_le'
#align finset.exists_le_of_sum_le Finset.exists_le_of_sum_le

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M) (h₁ : ∏ i ∈ s, f i = 1)
    (h₂ : ∃ i ∈ s, f i ≠ 1) : ∃ i ∈ s, 1 < f i := by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂
  apply ne_of_lt
  calc
    ∏ j ∈ s, f j < ∏ j ∈ s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one
#align finset.exists_one_lt_of_prod_one_of_exists_ne_one' Finset.exists_one_lt_of_prod_one_of_exists_ne_one'
#align finset.exists_pos_of_sum_zero_of_exists_nonzero Finset.exists_pos_of_sum_zero_of_exists_nonzero

end LinearOrderedCancelCommMonoid

end Finset

namespace Fintype
section OrderedCommMonoid
variable [Fintype ι] [OrderedCommMonoid M] {f : ι → M}

@[to_additive (attr := mono) sum_mono]
theorem prod_mono' : Monotone fun f : ι → M ↦ ∏ i, f i := fun _ _ hfg ↦
  Finset.prod_le_prod' fun x _ ↦ hfg x
#align fintype.prod_mono' Fintype.prod_mono'
#align fintype.sum_mono Fintype.sum_mono

@[to_additive sum_nonneg]
lemma one_le_prod (hf : 1 ≤ f) : 1 ≤ ∏ i, f i := Finset.one_le_prod' fun _ _ ↦ hf _

@[to_additive] lemma prod_le_one (hf : f ≤ 1) : ∏ i, f i ≤ 1 := Finset.prod_le_one' fun _ _ ↦ hf _

@[to_additive]
lemma prod_eq_one_iff_of_one_le (hf : 1 ≤ f) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_one_le' fun i _ ↦ hf i).trans <| by simp [Function.funext_iff]

@[to_additive]
lemma prod_eq_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i = 1 ↔ f = 1 :=
  (Finset.prod_eq_one_iff_of_le_one' fun i _ ↦ hf i).trans <| by simp [Function.funext_iff]

end OrderedCommMonoid

section OrderedCancelCommMonoid
variable [Fintype ι] [OrderedCancelCommMonoid M] {f : ι → M}

@[to_additive sum_strictMono]
theorem prod_strictMono' : StrictMono fun f : ι → M ↦ ∏ x, f x :=
  fun _ _ hfg ↦
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ ↦ hle i) ⟨i, Finset.mem_univ i, hlt⟩
#align fintype.prod_strict_mono' Fintype.prod_strictMono'
#align fintype.sum_strict_mono Fintype.sum_strictMono

@[to_additive sum_pos]
lemma one_lt_prod (hf : 1 < f) : 1 < ∏ i, f i :=
  Finset.one_lt_prod' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2

@[to_additive]
lemma prod_lt_one (hf : f < 1) : ∏ i, f i < 1 :=
  Finset.prod_lt_one' (fun _ _ ↦ hf.le _) <| by simpa using (Pi.lt_def.1 hf).2

@[to_additive sum_pos_iff_of_nonneg]
lemma one_lt_prod_iff_of_one_le (hf : 1 ≤ f) : 1 < ∏ i, f i ↔ 1 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]

@[to_additive]
lemma prod_lt_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i < 1 ↔ f < 1 := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]

end OrderedCancelCommMonoid
end Fintype

namespace Multiset

theorem finset_sum_eq_sup_iff_disjoint [DecidableEq α] {β : Type*} {i : Finset β}
    {f : β → Multiset α} :
    i.sum f = i.sup f ↔
      ∀ᵉ (x ∈ i) (y ∈ i), x ≠ y → Multiset.Disjoint (f x) (f y) := by
  induction' i using Finset.cons_induction_on with z i hz hr
  · simp only [Finset.not_mem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero, eq_self_iff_true]
  · simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union,
      forall_eq_or_imp, Ne, not_true_eq_false, IsEmpty.forall_iff, true_and_iff,
      imp_and, forall_and, ← hr, @eq_comm _ z]
    have := fun x (H : x ∈ i) => ne_of_mem_of_not_mem H hz
    simp (config := { contextual := true }) only [this, not_false_iff, true_imp_iff]
    simp_rw [← disjoint_finset_sum_left, ← disjoint_finset_sum_right, disjoint_comm, ← and_assoc,
      and_self_iff]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))
#align multiset.finset_sum_eq_sup_iff_disjoint Multiset.finset_sum_eq_sup_iff_disjoint

theorem sup_powerset_len {α : Type*} [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (card x + 1)) fun k => x.powersetCard k) = x.powerset := by
  convert bind_powerset_len x using 1
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powersetCard x h)
#align multiset.sup_powerset_len Multiset.sup_powerset_len

end Multiset

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

/-- The `positivity` extension which proves that `∑ i ∈ s, f i` is nonnegative if `f` is, and
positive if each `f i` is and `s` is nonempty.

TODO: The following example does not work
```
example (s : Finset ℕ) (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f n) : 0 ≤ s.sum f := by positivity
```
because `compareHyp` can't look for assumptions behind binders.
-/
@[positivity Finset.sum _ _]
def evalFinsetSum : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.sum $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) := ← (do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      let .some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(OrderedCancelAddCommMonoid $α) | pure none
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody
      return some q(@sum_pos $ι $α $pα' $f $s (fun i _ ↦ $pr i) $ps))
    -- Try to show that the sum is positive
    if let some p_pos := p_pos then
      return .positive p_pos
    -- Fall back to showing that the sum is nonnegative
    else
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let pα' ← synthInstanceQ q(OrderedAddCommMonoid $α)
      assertInstancesCommute
      return .nonnegative q(@sum_nonneg $ι $α $pα' $f $s fun i _ ↦ $pr i)
  | _ => throwError "not Finset.sum"

end Mathlib.Meta.Positivity
