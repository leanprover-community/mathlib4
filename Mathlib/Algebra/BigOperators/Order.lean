/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.GCongr.Core

#align_import algebra.big_operators.order from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Results about big operators with values in an ordered algebraic structure.

Mostly monotonicity results for the `∏` and `∑` operations.

-/

open Function

open BigOperators

variable {ι α β M N G k R : Type*}

namespace Finset

section OrderedCommMonoid

variable [CommMonoid M] [OrderedCommMonoid N]

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x in s, g x) ≤ ∏ x in s, f (g x)`. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred (f : M → N) (p : M → Prop)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i in s, g i) ≤ ∏ i in s, f (g i) := by
  refine' le_trans (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ _ _) _
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  rw [Multiset.map_map]
  rfl
#align finset.le_prod_nonempty_of_submultiplicative_on_pred Finset.le_prod_nonempty_of_submultiplicative_on_pred
#align finset.le_sum_nonempty_of_subadditive_on_pred Finset.le_sum_nonempty_of_subadditive_on_pred

/-- Let `{x | p x}` be an additive subsemigroup of an additive commutative monoid `M`. Let
`f : M → N` be a map subadditive on `{x | p x}`, i.e., `p x → p y → f (x + y) ≤ f x + f y`. Let
`g i`, `i ∈ s`, be a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative (f : M → N) (h_mul : ∀ x y, f (x * y) ≤ f x * f y)
    {s : Finset ι} (hs : s.Nonempty) (g : ι → M) : f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun _ ↦ True) (fun x y _ _ ↦ h_mul x y)
    (fun _ _ _ _ ↦ trivial) g s hs fun _ _ ↦ trivial
#align finset.le_prod_nonempty_of_submultiplicative Finset.le_prod_nonempty_of_submultiplicative
#align finset.le_sum_nonempty_of_subadditive Finset.le_sum_nonempty_of_subadditive

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive

/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred (f : M → N) (p : M → Prop) (h_one : f 1 = 1)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) {s : Finset ι} (hs : ∀ i ∈ s, p (g i)) : f (∏ i in s, g i) ≤ ∏ i in s, f (g i) := by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs
#align finset.le_prod_of_submultiplicative_on_pred Finset.le_prod_of_submultiplicative_on_pred
#align finset.le_sum_of_subadditive_on_pred Finset.le_sum_of_subadditive_on_pred

/-- Let `{x | p x}` be a subsemigroup of a commutative additive monoid `M`. Let `f : M → N` be a map
such that `f 0 = 0` and `f` is subadditive on `{x | p x}`, i.e. `p x → p y → f (x + y) ≤ f x + f y`.
Let `g i`, `i ∈ s`, be a finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ x in s, g x) ≤ ∑ x in s, f (g x)`. -/
add_decl_doc le_sum_of_subadditive_on_pred

/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative (f : M → N) (h_one : f 1 = 1)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i in s, g i) ≤ ∏ i in s, f (g i) := by
  refine' le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) _
  rw [Multiset.map_map]
  rfl
#align finset.le_prod_of_submultiplicative Finset.le_prod_of_submultiplicative
#align finset.le_sum_of_subadditive Finset.le_sum_of_subadditive

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y`, `f 0 = 0`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_of_subadditive

variable {f g : ι → N} {s t : Finset ι}

/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i in s, f i ≤ ∏ i in s, g i`. -/
@[to_additive sum_le_sum]
theorem prod_le_prod' (h : ∀ i ∈ s, f i ≤ g i) : ∏ i in s, f i ≤ ∏ i in s, g i :=
  Multiset.prod_map_le_prod_map f g h
#align finset.prod_le_prod' Finset.prod_le_prod'
#align finset.sum_le_sum Finset.sum_le_sum

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then
`∑ i in s, f i ≤ ∑ i in s, g i`. -/
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
theorem one_le_prod' (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i in s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)
#align finset.one_le_prod' Finset.one_le_prod'
#align finset.sum_nonneg Finset.sum_nonneg

@[to_additive Finset.sum_nonneg']
theorem one_le_prod'' (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i : ι in s, f i :=
  Finset.one_le_prod' fun i _ ↦ h i
#align finset.one_le_prod'' Finset.one_le_prod''
#align finset.sum_nonneg' Finset.sum_nonneg'

@[to_additive sum_nonpos]
theorem prod_le_one' (h : ∀ i ∈ s, f i ≤ 1) : ∏ i in s, f i ≤ 1 :=
  (prod_le_prod' h).trans_eq (by rw [prod_const_one])
#align finset.prod_le_one' Finset.prod_le_one'
#align finset.sum_nonpos Finset.sum_nonpos

@[to_additive sum_le_sum_of_subset_of_nonneg]
theorem prod_le_prod_of_subset_of_one_le' (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i in s, f i ≤ ∏ i in t, f i := by
  classical calc
      ∏ i in s, f i ≤ (∏ i in t \ s, f i) * ∏ i in s, f i :=
        le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]
#align finset.prod_le_prod_of_subset_of_one_le' Finset.prod_le_prod_of_subset_of_one_le'
#align finset.sum_le_sum_of_subset_of_nonneg Finset.sum_le_sum_of_subset_of_nonneg

@[to_additive sum_mono_set_of_nonneg]
theorem prod_mono_set_of_one_le' (hf : ∀ x, 1 ≤ f x) : Monotone fun s ↦ ∏ x in s, f x :=
  fun _ _ hst ↦ prod_le_prod_of_subset_of_one_le' hst fun x _ _ ↦ hf x
#align finset.prod_mono_set_of_one_le' Finset.prod_mono_set_of_one_le'
#align finset.sum_mono_set_of_nonneg Finset.sum_mono_set_of_nonneg

@[to_additive sum_le_univ_sum_of_nonneg]
theorem prod_le_univ_prod_of_one_le' [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x in s, f x ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ ↦ w a
#align finset.prod_le_univ_prod_of_one_le' Finset.prod_le_univ_prod_of_one_le'
#align finset.sum_le_univ_sum_of_nonneg Finset.sum_le_univ_sum_of_nonneg

-- Porting Note: TODO -- The two next lemmas give the same lemma in additive version
@[to_additive sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_one_le' :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i in s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.not_mem_empty _ h), fun _ ↦ rfl⟩) ?_
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff' (H _ <| mem_insert_self _ _) (one_le_prod' this),
      forall_mem_insert, ih this]
#align finset.prod_eq_one_iff_of_one_le' Finset.prod_eq_one_iff_of_one_le'
#align finset.sum_eq_zero_iff_of_nonneg Finset.sum_eq_zero_iff_of_nonneg

@[to_additive existing sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_le_one' :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i in s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  @prod_eq_one_iff_of_one_le' _ Nᵒᵈ _ _ _
#align finset.prod_eq_one_iff_of_le_one' Finset.prod_eq_one_iff_of_le_one'
-- Porting note: there is no align for the additive version since it aligns to the
-- same one as the previous lemma

@[to_additive single_le_sum]
theorem single_le_prod' (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) : f a ≤ ∏ x in s, f x :=
  calc
    f a = ∏ i in {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i in s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi
#align finset.single_le_prod' Finset.single_le_prod'
#align finset.single_le_sum Finset.single_le_sum

@[to_additive]
lemma mul_le_prod {i j : ι} (hf : ∀ i ∈ s, 1 ≤ f i) (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
    f i * f j ≤ ∏ k in s, f k :=
  calc
    f i * f j = ∏ k in .cons i {j} (by simpa), f k := by rw [prod_cons, prod_singleton]
    _ ≤ ∏ k in s, f k := by
      refine prod_le_prod_of_subset_of_one_le' ?_ fun k hk _ ↦ hf k hk
      simp [cons_subset, *]

@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.prod f ≤ n ^ s.card := by
  refine' (Multiset.prod_le_pow_card (s.val.map f) n _).trans _
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
    (h : ∀ (y) (_ : y ∉ t), (1 : N) ≤ ∏ x in s.filter fun x ↦ g x = y, f x) :
    (∏ y in t, ∏ x in s.filter fun x ↦ g x = y, f x) ≤ ∏ x in s, f x :=
  calc
    (∏ y in t, ∏ x in s.filter fun x ↦ g x = y, f x) ≤
        ∏ y in t ∪ s.image g, ∏ x in s.filter fun x ↦ g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' (subset_union_left _ _) fun y _ ↦ h y
    _ = ∏ x in s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _
#align finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'
#align finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg

-- Porting note: Mathport warning: expanding binder collection (y «expr ∉ » t)
@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ (y) (_ : y ∉ t), ∏ x in s.filter fun x ↦ g x = y, f x ≤ 1) :
    ∏ x in s, f x ≤ ∏ y in t, ∏ x in s.filter fun x ↦ g x = y, f x :=
  @prod_fiberwise_le_prod_of_one_le_prod_fiber' _ Nᵒᵈ _ _ _ _ _ _ _ h
#align finset.prod_le_prod_fiberwise_of_prod_fiber_le_one' Finset.prod_le_prod_fiberwise_of_prod_fiber_le_one'
#align finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos Finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos

end OrderedCommMonoid

theorem abs_sum_le_sum_abs {G : Type*} [LinearOrderedAddCommGroup G] (f : ι → G) (s : Finset ι) :
    |∑ i in s, f i| ≤ ∑ i in s, |f i| := le_sum_of_subadditive _ abs_zero abs_add s f
#align finset.abs_sum_le_sum_abs Finset.abs_sum_le_sum_abs

theorem abs_sum_of_nonneg {G : Type*} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i ∈ s, 0 ≤ f i) : |∑ i : ι in s, f i| = ∑ i : ι in s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]
#align finset.abs_sum_of_nonneg Finset.abs_sum_of_nonneg

theorem abs_sum_of_nonneg' {G : Type*} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i, 0 ≤ f i) : |∑ i : ι in s, f i| = ∑ i : ι in s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]
#align finset.abs_sum_of_nonneg' Finset.abs_sum_of_nonneg'

theorem abs_prod {R : Type*} [LinearOrderedCommRing R] {f : ι → R} {s : Finset ι} :
    |∏ x in s, f x| = ∏ x in s, |f x| :=
  map_prod absHom _ _
#align finset.abs_prod Finset.abs_prod

section Pigeonhole

variable [DecidableEq β]

theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, (s.filter fun x ↦ f x = a).card ≤ n) :
    s.card ≤ n * t.card :=
  calc
    s.card = ∑ a in t, (s.filter fun x ↦ f x = a).card := card_eq_sum_card_fiberwise Hf
    _ ≤ ∑ _a in t, n := sum_le_sum hn
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
    n * t.card = ∑ _a in t, n := by simp [mul_comm]
    _ ≤ ∑ a in t, (s.filter fun x ↦ f x = a).card := sum_le_sum hn
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
theorem sum_card_inter_le (h : ∀ a ∈ s, (B.filter <| (· ∈ ·) a).card ≤ n) :
    (∑ t in B, (s ∩ t).card) ≤ s.card * n := by
  refine' le_trans _ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
#align finset.sum_card_inter_le Finset.sum_card_inter_le

/-- If every element belongs to at most `n` Finsets, then the sum of their sizes is at most `n`
times how many they are. -/
theorem sum_card_le [Fintype α] (h : ∀ a, (B.filter <| (· ∈ ·) a).card ≤ n) :
    ∑ s in B, s.card ≤ Fintype.card α * n :=
  calc
    ∑ s in B, s.card = ∑ s in B, (univ ∩ s).card := by simp_rw [univ_inter]
    _ ≤ Fintype.card α * n := sum_card_inter_le fun a _ ↦ h a
#align finset.sum_card_le Finset.sum_card_le

/-- If every element belongs to at least `n` Finsets, then the sum of their sizes is at least `n`
times how many they are. -/
theorem le_sum_card_inter (h : ∀ a ∈ s, n ≤ (B.filter <| (· ∈ ·) a).card) :
    s.card * n ≤ ∑ t in B, (s ∩ t).card := by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
#align finset.le_sum_card_inter Finset.le_sum_card_inter

/-- If every element belongs to at least `n` Finsets, then the sum of their sizes is at least `n`
times how many they are. -/
theorem le_sum_card [Fintype α] (h : ∀ a, n ≤ (B.filter <| (· ∈ ·) a).card) :
    Fintype.card α * n ≤ ∑ s in B, s.card :=
  calc
    Fintype.card α * n ≤ ∑ s in B, (univ ∩ s).card := le_sum_card_inter fun a _ ↦ h a
    _ = ∑ s in B, s.card := by simp_rw [univ_inter]
#align finset.le_sum_card Finset.le_sum_card

/-- If every element belongs to exactly `n` Finsets, then the sum of their sizes is `n` times how
many they are. -/
theorem sum_card_inter (h : ∀ a ∈ s, (B.filter <| (· ∈ ·) a).card = n) :
    (∑ t in B, (s ∩ t).card) = s.card * n :=
  (sum_card_inter_le fun a ha ↦ (h a ha).le).antisymm (le_sum_card_inter fun a ha ↦ (h a ha).ge)
#align finset.sum_card_inter Finset.sum_card_inter

/-- If every element belongs to exactly `n` Finsets, then the sum of their sizes is `n` times how
many they are. -/
theorem sum_card [Fintype α] (h : ∀ a, (B.filter <| (· ∈ ·) a).card = n) :
    ∑ s in B, s.card = Fintype.card α * n := by
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
        card_le_of_subset <| biUnion_subset_biUnion_of_subset_left _ <| filter_subset _ _)
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

@[to_additive (attr := simp) sum_eq_zero_iff]
theorem prod_eq_one_iff' : ∏ x in s, f x = 1 ↔ ∀ x ∈ s, f x = 1 :=
  prod_eq_one_iff_of_one_le' fun x _ ↦ one_le (f x)
#align finset.prod_eq_one_iff' Finset.prod_eq_one_iff'
#align finset.sum_eq_zero_iff Finset.sum_eq_zero_iff

@[to_additive sum_le_sum_of_subset]
theorem prod_le_prod_of_subset' (h : s ⊆ t) : ∏ x in s, f x ≤ ∏ x in t, f x :=
  prod_le_prod_of_subset_of_one_le' h fun _ _ _ ↦ one_le _
#align finset.prod_le_prod_of_subset' Finset.prod_le_prod_of_subset'
#align finset.sum_le_sum_of_subset Finset.sum_le_sum_of_subset

@[to_additive sum_mono_set]
theorem prod_mono_set' (f : ι → M) : Monotone fun s ↦ ∏ x in s, f x := fun _ _ hs ↦
  prod_le_prod_of_subset' hs
#align finset.prod_mono_set' Finset.prod_mono_set'
#align finset.sum_mono_set Finset.sum_mono_set

@[to_additive sum_le_sum_of_ne_zero]
theorem prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) :
    ∏ x in s, f x ≤ ∏ x in t, f x := by
  classical calc
    ∏ x in s, f x = (∏ x in s.filter fun x ↦ f x = 1, f x) *
        ∏ x in s.filter fun x ↦ f x ≠ 1, f x := by
      rw [← prod_union, filter_union_filter_neg_eq]
      exact disjoint_filter.2 fun _ _ h n_h ↦ n_h h
    _ ≤ ∏ x in t, f x :=
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
    ∏ i in s, f i < ∏ i in s, g i :=
  Multiset.prod_lt_prod' hle hlt
#align finset.prod_lt_prod' Finset.prod_lt_prod'
#align finset.sum_lt_sum Finset.sum_lt_sum

@[to_additive sum_lt_sum_of_nonempty]
theorem prod_lt_prod_of_nonempty' (hs : s.Nonempty) (hlt : ∀ i ∈ s, f i < g i) :
    ∏ i in s, f i < ∏ i in s, g i :=
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

-- Porting note: TODO -- calc indentation
@[to_additive sum_lt_sum_of_subset]
theorem prod_lt_prod_of_subset' (h : s ⊆ t) {i : ι} (ht : i ∈ t) (hs : i ∉ s) (hlt : 1 < f i)
    (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) : ∏ j in s, f j < ∏ j in t, f j := by
  classical calc
    ∏ j in s, f j < ∏ j in insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j in s, f j) hlt
    _ ≤ ∏ j in t, f j := by
      apply prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
        simp only [mem_insert, not_or] at h'x
        exact hle x hx h'x.2
#align finset.prod_lt_prod_of_subset' Finset.prod_lt_prod_of_subset'
#align finset.sum_lt_sum_of_subset Finset.sum_lt_sum_of_subset

@[to_additive single_lt_sum]
theorem single_lt_prod' {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s) (hlt : 1 < f j)
    (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) : f i < ∏ k in s, f k :=
  calc
    f i = ∏ k in {i}, f k := by rw [prod_singleton]
    _ < ∏ k in s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki ↦ hle k hks (mt mem_singleton.2 hki)
#align finset.single_lt_prod' Finset.single_lt_prod'
#align finset.single_lt_sum Finset.single_lt_sum

@[to_additive sum_pos]
theorem one_lt_prod (h : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) : 1 < ∏ i in s, f i :=
  lt_of_le_of_lt (by rw [prod_const_one]) <| prod_lt_prod_of_nonempty' hs h
#align finset.one_lt_prod Finset.one_lt_prod
#align finset.sum_pos Finset.sum_pos

@[to_additive]
theorem prod_lt_one (h : ∀ i ∈ s, f i < 1) (hs : s.Nonempty) : ∏ i in s, f i < 1 :=
  (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])
#align finset.prod_lt_one Finset.prod_lt_one
#align finset.sum_neg Finset.sum_neg

@[to_additive sum_pos']
theorem one_lt_prod' (h : ∀ i ∈ s, 1 ≤ f i) (hs : ∃ i ∈ s, 1 < f i) : 1 < ∏ i in s, f i :=
  prod_const_one.symm.trans_lt <| prod_lt_prod' h hs
#align finset.one_lt_prod' Finset.one_lt_prod'
#align finset.sum_pos' Finset.sum_pos'

@[to_additive]
theorem prod_lt_one' (h : ∀ i ∈ s, f i ≤ 1) (hs : ∃ i ∈ s, f i < 1) : ∏ i in s, f i < 1 :=
  prod_const_one.le.trans_lt' <| prod_lt_prod' h hs
#align finset.prod_lt_one' Finset.prod_lt_one'
#align finset.sum_neg' Finset.sum_neg'

@[to_additive]
theorem prod_eq_prod_iff_of_le {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) :
    ((∏ i in s, f i) = ∏ i in s, g i) ↔ ∀ i ∈ s, f i = g i := by
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
    ∏ i in s \ t, f i ≤ ∏ i in t \ s, f i ↔ ∏ i in s, f i ≤ ∏ i in t, f i := by
  rw [← mul_le_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter];
  simpa only [inter_comm] using disjoint_sdiff_inter t s

@[to_additive] lemma prod_sdiff_lt_prod_sdiff :
    ∏ i in s \ t, f i < ∏ i in t \ s, f i ↔ ∏ i in s, f i < ∏ i in t, f i := by
  rw [← mul_lt_mul_iff_right, ← prod_union (disjoint_sdiff_inter _ _), sdiff_union_inter,
    ← prod_union, inter_comm, sdiff_union_inter];
  simpa only [inter_comm] using disjoint_sdiff_inter t s

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}

@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' (Hlt : ∏ i in s, f i < ∏ i in s, g i) : ∃ i ∈ s, f i < g i := by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle
#align finset.exists_lt_of_prod_lt' Finset.exists_lt_of_prod_lt'
#align finset.exists_lt_of_sum_lt Finset.exists_lt_of_sum_lt

@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i in s, f i ≤ ∏ i in s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt
#align finset.exists_le_of_prod_le' Finset.exists_le_of_prod_le'
#align finset.exists_le_of_sum_le Finset.exists_le_of_sum_le

@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M) (h₁ : ∏ i in s, f i = 1)
    (h₂ : ∃ i ∈ s, f i ≠ 1) : ∃ i ∈ s, 1 < f i := by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂
  apply ne_of_lt
  calc
    ∏ j in s, f j < ∏ j in s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one
#align finset.exists_one_lt_of_prod_one_of_exists_ne_one' Finset.exists_one_lt_of_prod_one_of_exists_ne_one'
#align finset.exists_pos_of_sum_zero_of_exists_nonzero Finset.exists_pos_of_sum_zero_of_exists_nonzero

end LinearOrderedCancelCommMonoid

section OrderedCommSemiring

variable [OrderedCommSemiring R] {f g : ι → R} {s t : Finset ι}

open Classical

-- this is also true for an ordered commutative multiplicative monoid with zero
theorem prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i in s, f i :=
  prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0
#align finset.prod_nonneg Finset.prod_nonneg

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid. -/
theorem prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i in s, f i ≤ ∏ i in s, g i := by
  induction' s using Finset.induction with a s has ih h
  · simp
  · simp only [prod_insert has]
    apply mul_le_mul
    · exact h1 a (mem_insert_self a s)
    · refine ih (fun x H ↦ h0 _ ?_) (fun x H ↦ h1 _ ?_) <;> exact mem_insert_of_mem H
    · apply prod_nonneg fun x H ↦ h0 x (mem_insert_of_mem H)
    · apply le_trans (h0 a (mem_insert_self a s)) (h1 a (mem_insert_self a s))
#align finset.prod_le_prod Finset.prod_le_prod

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`.

This is a variant (beta-reduced) version of the standard lemma `Finset.prod_le_prod`, convenient
for the `gcongr` tactic. -/
@[gcongr]
theorem _root_.GCongr.prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    s.prod f ≤ s.prod g :=
  s.prod_le_prod h0 h1

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `Finset.prod_le_one'` for the case of an ordered commutative multiplicative monoid. -/
theorem prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i in s, f i ≤ 1 := by
  convert ← prod_le_prod h0 h1
  exact Finset.prod_const_one
#align finset.prod_le_one Finset.prod_le_one

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `OrderedCommSemiring`. -/
theorem prod_add_prod_le {i : ι} {f g h : ι → R} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
    (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) : ((∏ i in s, g i) + ∏ i in s, h i) ≤ ∏ i in s, f i := by
  simp_rw [prod_eq_mul_prod_diff_singleton hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    refine add_le_add ?_ ?_ <;>
    · refine mul_le_mul_of_nonneg_left ?_ ?_
      · refine prod_le_prod ?_ ?_
        <;> simp (config := { contextual := true }) [*]
      · try apply_assumption
        try assumption
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    intro j h1j h2j
    exact le_trans (hg j h1j) (hgf j h1j h2j)
#align finset.prod_add_prod_le Finset.prod_add_prod_le

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [StrictOrderedCommSemiring R] {f g : ι → R} {s : Finset ι}

-- This is also true for an ordered commutative multiplicative monoid with zero
theorem prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i in s, f i :=
  prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0
#align finset.prod_pos Finset.prod_pos

theorem prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i in s, f i < ∏ i in s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _)]
  apply mul_lt_mul hilt
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact le_of_lt <| (hf i hi).trans hilt

theorem prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i in s, f i < ∏ i in s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end StrictOrderedCommSemiring

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring R] {f g h : ι → R} {s : Finset ι} {i : ι}

/-- Note that the name is to match `CanonicallyOrderedCommSemiring.mul_pos`. -/
@[simp] lemma _root_.CanonicallyOrderedCommSemiring.prod_pos [Nontrivial R] :
    0 < ∏ i in s, f i ↔ (∀ i ∈ s, (0 : R) < f i) :=
  CanonicallyOrderedCommSemiring.multiset_prod_pos.trans Multiset.forall_mem_map_iff
#align canonically_ordered_comm_semiring.prod_pos CanonicallyOrderedCommSemiring.prod_pos

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `CanonicallyOrderedCommSemiring`.
-/
theorem prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
    (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ((∏ i in s, g i) + ∏ i in s, h i) ≤ ∏ i in s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi]
    refine' le_trans _ (mul_le_mul_right' h2i _)
    rw [right_distrib]
    apply add_le_add <;> apply mul_le_mul_left' <;> apply prod_le_prod' <;>
            simp only [and_imp, mem_sdiff, mem_singleton] <;>
          intros <;>
        apply_assumption <;>
      assumption
#align finset.prod_add_prod_le' Finset.prod_add_prod_le'

end CanonicallyOrderedCommSemiring

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
lemma one_le_prod (hf : 1 ≤ f) : 1 ≤ ∏ i, f i := Finset.one_le_prod' λ _ _ ↦ hf _

@[to_additive] lemma prod_le_one (hf : f ≤ 1) : ∏ i, f i ≤ 1 := Finset.prod_le_one' λ _ _ ↦ hf _

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
  Finset.one_lt_prod' (λ _ _ ↦ hf.le _) $ by simpa using (Pi.lt_def.1 hf).2

@[to_additive]
lemma prod_lt_one (hf : f < 1) : ∏ i, f i < 1 :=
  Finset.prod_lt_one' (λ _ _ ↦ hf.le _) $ by simpa using (Pi.lt_def.1 hf).2

@[to_additive sum_pos_iff_of_nonneg]
lemma one_lt_prod_iff_of_one_le (hf : 1 ≤ f) : 1 < ∏ i, f i ↔ 1 < f := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, one_lt_prod]

@[to_additive]
lemma prod_lt_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i < 1 ↔ f < 1 := by
  obtain rfl | hf := hf.eq_or_lt <;> simp [*, prod_lt_one]

@[to_additive]
lemma prod_eq_one_iff_of_one_le (hf : 1 ≤ f) : ∏ i, f i = 1 ↔ f = 1 := by
  simpa only [(one_le_prod hf).not_gt_iff_eq, hf.not_gt_iff_eq]
    using (one_lt_prod_iff_of_one_le hf).not

@[to_additive]
lemma prod_eq_one_iff_of_le_one (hf : f ≤ 1) : ∏ i, f i = 1 ↔ f = 1 := by
  simpa only [(prod_le_one hf).not_gt_iff_eq, hf.not_gt_iff_eq, eq_comm]
    using (prod_lt_one_iff_of_le_one hf).not

end OrderedCancelCommMonoid
end Fintype

namespace WithTop

open Finset

/-- A product of finite numbers is still finite -/
theorem prod_lt_top [CommMonoidWithZero R] [NoZeroDivisors R] [Nontrivial R] [DecidableEq R] [LT R]
    {s : Finset ι} {f : ι → WithTop R} (h : ∀ i ∈ s, f i ≠ ⊤) : ∏ i in s, f i < ⊤ :=
  prod_induction f (fun a ↦ a < ⊤) (fun _ _ h₁ h₂ ↦ mul_lt_top' h₁ h₂) (coe_lt_top 1)
    fun a ha ↦ WithTop.lt_top_iff_ne_top.2 (h a ha)
#align with_top.prod_lt_top WithTop.prod_lt_top

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff [AddCommMonoid M] {s : Finset ι} {f : ι → WithTop M} :
    ∑ i in s, f i = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  induction s using Finset.cons_induction <;> simp [*]
#align with_top.sum_eq_top_iff WithTop.sum_eq_top_iff

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff [AddCommMonoid M] [LT M] {s : Finset ι} {f : ι → WithTop M} :
    ∑ i in s, f i < ⊤ ↔ ∀ i ∈ s, f i < ⊤ := by
  simp only [WithTop.lt_top_iff_ne_top, ne_eq, sum_eq_top_iff, not_exists, not_and]
#align with_top.sum_lt_top_iff WithTop.sum_lt_top_iff

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top [AddCommMonoid M] [LT M] {s : Finset ι} {f : ι → WithTop M}
    (h : ∀ i ∈ s, f i ≠ ⊤) : ∑ i in s, f i < ⊤ :=
  sum_lt_top_iff.2 fun i hi => WithTop.lt_top_iff_ne_top.2 (h i hi)
#align with_top.sum_lt_top WithTop.sum_lt_top

end WithTop

section AbsoluteValue

variable {S : Type*}

theorem AbsoluteValue.sum_le [Semiring R] [OrderedSemiring S] (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι → R) : abv (∑ i in s, f i) ≤ ∑ i in s, abv (f i) :=
  Finset.le_sum_of_subadditive abv (map_zero _) abv.add_le _ _
#align absolute_value.sum_le AbsoluteValue.sum_le

theorem IsAbsoluteValue.abv_sum [Semiring R] [OrderedSemiring S] (abv : R → S) [IsAbsoluteValue abv]
    (f : ι → R) (s : Finset ι) : abv (∑ i in s, f i) ≤ ∑ i in s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _
#align is_absolute_value.abv_sum IsAbsoluteValue.abv_sum

nonrec theorem AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [LinearOrderedCommRing S]
    (abv : AbsoluteValue R S) (f : ι → R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  map_prod abv f s
#align absolute_value.map_prod AbsoluteValue.map_prod

theorem IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [LinearOrderedCommRing S]
    (abv : R → S) [IsAbsoluteValue abv] (f : ι → R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _
#align is_absolute_value.map_prod IsAbsoluteValue.map_prod

end AbsoluteValue
