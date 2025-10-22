/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum

/-!
# Big operators

In this file we prove theorems about products and sums indexed by a `Finset`.
-/

-- TODO: assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction OrderedCommMonoid
assert_not_exists Finset.preimage Finset.sigma Fintype.piFinset
assert_not_exists Finset.piecewise Set.indicator MonoidHom.coeFn Function.support IsSquare

open Fin Function

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

namespace Finset

section CommMonoid
variable [CommMonoid M] {f g : ι → M}

@[to_additive]
lemma prod_eq_fold (s : Finset ι) (f : ι → M) : ∏ i ∈ s, f i = s.fold (β := M) (· * ·) 1 f := rfl

@[to_additive (attr := simp)]
theorem prod_cons (h : a ∉ s) : ∏ x ∈ cons a s h, f x = f a * ∏ x ∈ s, f x :=
  fold_cons h

/-- Variant of `prod_cons` not applied to a function. -/
@[to_additive (attr := grind =)]
theorem prod_cons' (h : a ∉ s) :
    Finset.prod (cons a s h) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_cons h]

@[to_additive (attr := simp)]
theorem prod_insert [DecidableEq ι] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x :=
  fold_insert

/-- Variant of `prod_insert` not applied to a function. -/
@[to_additive (attr := grind =)]
theorem prod_insert' [DecidableEq ι] (h : a ∉ s) :
    Finset.prod (insert a s) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_insert h]

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`. -/
@[to_additive (attr := simp) /-- The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`. -/]
theorem prod_insert_of_eq_one_if_notMem [DecidableEq ι] (h : a ∉ s → f a = 1) :
    ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by
  by_cases hm : a ∈ s
  · simp_rw [insert_eq_of_mem hm]
  · rw [prod_insert hm, h hm, one_mul]

@[deprecated (since := "2025-05-23")]
alias sum_insert_of_eq_zero_if_not_mem := sum_insert_of_eq_zero_if_notMem

@[to_additive existing, deprecated (since := "2025-05-23")]
alias prod_insert_of_eq_one_if_not_mem := prod_insert_of_eq_one_if_notMem

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `f a = 1`. -/
@[to_additive /-- The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`. -/]
theorem prod_insert_one [DecidableEq ι] (h : f a = 1) : ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by
  simp [h]

@[to_additive (attr := simp)]
theorem prod_singleton (f : ι → M) (a : ι) : ∏ x ∈ singleton a, f x = f a :=
  Eq.trans fold_singleton <| mul_one _

/-- Variant of `prod_singleton` not applied to a function. -/
@[to_additive (attr := grind =)]
theorem prod_singleton' (a : ι) :
    Finset.prod (singleton a) = fun (f : ι → M) => f a := by
  funext f
  simp

@[to_additive]
theorem prod_pair [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    (∏ x ∈ ({a, b} : Finset ι), f x) = f a * f b := by
  rw [prod_insert (notMem_singleton.2 h), prod_singleton]

@[to_additive (attr := simp)]
theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ → ι} :
    Set.InjOn g s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x) :=
  fold_image

@[to_additive]
lemma prod_attach (s : Finset ι) (f : ι → M) : ∏ x ∈ s.attach, f x = ∏ x ∈ s, f x := by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[to_additive (attr := congr)]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr

@[to_additive]
theorem prod_eq_one (h : ∀ x ∈ s, f x = 1) : ∏ x ∈ s, f x = 1 := calc
  ∏ x ∈ s, f x = ∏ _x ∈ s, 1 := prod_congr rfl h
  _ = 1 := prod_const_one

/-- In a monoid whose only unit is `1`, a product is equal to `1` iff all factors are `1`. -/
@[to_additive (attr := simp)
/-- In an additive monoid whose only unit is `0`, a sum is equal to `0` iff all terms are `0`. -/]
lemma prod_eq_one_iff [Subsingleton Mˣ] : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction s using Finset.cons_induction <;> simp [*]

@[deprecated (since := "2025-03-31")] alias prod_eq_one_iff' := prod_eq_one_iff

@[to_additive]
theorem prod_disjUnion (h) :
    ∏ x ∈ s₁.disjUnion s₂ h, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  refine Eq.trans ?_ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]
theorem prod_disjiUnion (s : Finset κ) (t : κ → Finset ι) (h) :
    ∏ x ∈ s.disjiUnion t h, f x = ∏ i ∈ s, ∏ x ∈ t i, f x := by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]
theorem prod_union_inter [DecidableEq ι] :
    (∏ x ∈ s₁ ∪ s₂, f x) * ∏ x ∈ s₁ ∩ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x :=
  fold_union_inter

@[to_additive]
theorem prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) :
    ∏ x ∈ s₁ ∪ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]
theorem prod_filter_mul_prod_filter_not
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] (f : ι → M) :
    (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, f x = ∏ x ∈ s, f x := by
  have := Classical.decEq ι
  rw [← prod_union (disjoint_filter_filter_neg s s p), filter_union_filter_neg_eq]

@[to_additive]
lemma prod_filter_not_mul_prod_filter (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    [∀ x, Decidable (¬p x)] (f : ι → M) :
    (∏ x ∈ s with ¬p x, f x) * ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x := by
  rw [mul_comm, prod_filter_mul_prod_filter_not]

@[to_additive]
theorem prod_filter_xor (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    (∏ x ∈ s with (Xor' (p x) (q x)), f x) =
      (∏ x ∈ s with (p x ∧ ¬ q x), f x) * (∏ x ∈ s with (q x ∧ ¬ p x), f x) := by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor']

@[to_additive]
theorem _root_.IsCompl.prod_mul_prod [Fintype ι] {s t : Finset ι} (h : IsCompl s t) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i, f i :=
  (Finset.prod_disjUnion h.disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive /-- Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. -/]
lemma prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
lemma prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
theorem prod_sdiff [DecidableEq ι] (h : s₁ ⊆ s₂) :
    (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[to_additive]
theorem prod_subset_one_on_sdiff [DecidableEq ι] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i ∈ s₁, f i = ∏ i ∈ s₂, g i := by
  rw [← prod_sdiff h, prod_eq_one hg, one_mul]
  exact prod_congr rfl hfg

@[to_additive]
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x :=
  haveI := Classical.decEq ι
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]
theorem prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι ⊕ κ → M) :
    ∏ x ∈ s.disjSum t, f x = (∏ x ∈ s, f (Sum.inl x)) * ∏ x ∈ t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr, prod_disjUnion, prod_map, prod_map]
  rfl

@[deprecated (since := "2025-06-11")]
alias sum_disj_sum := sum_disjSum

@[to_additive existing, deprecated (since := "2025-06-11")]
alias prod_disj_sum := prod_disjSum

@[to_additive]
lemma prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι ⊕ κ)) (f : ι ⊕ κ → M) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by
  rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum, Finset.toLeft_disjSum,
    Finset.toRight_disjSum]

@[to_additive]
theorem prod_sumElim (s : Finset ι) (t : Finset κ) (f : ι → M) (g : κ → M) :
    ∏ x ∈ s.disjSum t, Sum.elim f g x = (∏ x ∈ s, f x) * ∏ x ∈ t, g x := by simp

@[to_additive]
theorem prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ → Finset ι}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by
  rw [← disjiUnion_eq_biUnion _ _ hs, prod_disjiUnion]

section bij
variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

@[to_additive]
lemma prod_of_injOn (e : ι → κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
    (h' : ∀ i ∈ t, i ∉ e '' s → g i = 1) (h : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ j ∈ t, g j := by
  classical
  exact (prod_nbij e (fun a ↦ mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans <|
    prod_subset (image_subset_iff.2 hest) <| by simpa using h'

variable [DecidableEq κ]

@[to_additive]
lemma prod_fiberwise_eq_prod_filter (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s with g i ∈ t, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]
lemma prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : κ → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s with g i ∈ t, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        prod_congr rfl fun j _ ↦ prod_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]
    _ = _ := prod_fiberwise_eq_prod_filter _ _ _ _

@[to_additive]
lemma prod_fiberwise_of_maps_to {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : ι → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq_of_maps_to h]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]
lemma prod_fiberwise_of_maps_to' {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : κ → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        prod_congr rfl fun y _ ↦ prod_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
    _ = _ := prod_fiberwise_of_maps_to h _

variable [Fintype κ]

@[to_additive]
lemma prod_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → M) :
    ∏ j, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i :=
  prod_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _

@[to_additive]
lemma prod_fiberwise' (s : Finset ι) (g : ι → κ) (f : κ → M) :
    ∏ j, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) :=
  prod_fiberwise_of_maps_to' (fun _ _ ↦ mem_univ _) _

end bij

@[to_additive (attr := simp)]
lemma prod_diag [DecidableEq ι] (s : Finset ι) (f : ι × ι → M) :
    ∏ i ∈ s.diag, f i = ∏ i ∈ s, f (i, i) := by
  apply prod_nbij' Prod.fst (fun i ↦ (i, i)) <;> simp

@[to_additive]
theorem prod_image' [DecidableEq ι] {s : Finset κ} {g : κ → ι} (h : κ → M)
    (eq : ∀ i ∈ s, f (g i) = ∏ j ∈ s with g j = g i, h j) :
    ∏ a ∈ s.image g, f a = ∏ i ∈ s, h i :=
  calc
    ∏ a ∈ s.image g, f a = ∏ a ∈ s.image g, ∏ j ∈ s with g j = a, h j :=
      (prod_congr rfl) fun _a hx =>
        let ⟨i, his, hi⟩ := mem_image.1 hx
        hi ▸ eq i his
    _ = ∏ i ∈ s, h i := prod_fiberwise_of_maps_to (fun _ => mem_image_of_mem g) _

@[to_additive]
theorem prod_mul_distrib : ∏ x ∈ s, f x * g x = (∏ x ∈ s, f x) * ∏ x ∈ s, g x :=
  Eq.trans (by rw [one_mul]; rfl) fold_op_distrib

@[to_additive]
lemma prod_mul_prod_comm (f g h i : ι → M) :
    (∏ a ∈ s, f a * g a) * ∏ a ∈ s, h a * i a = (∏ a ∈ s, f a * h a) * ∏ a ∈ s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
theorem prod_filter_of_ne {p : ι → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x :=
  (prod_subset (filter_subset _ _)) fun x => by
    classical
      rw [not_imp_comm, mem_filter]
      exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

-- If we use `[DecidableEq M]` here, some rewrites fail because they find a wrong `Decidable`
-- instance first; `{∀ x, Decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
theorem prod_filter_ne_one (s : Finset ι) [∀ x, Decidable (f x ≠ 1)] :
    ∏ x ∈ s with f x ≠ 1, f x = ∏ x ∈ s, f x :=
  prod_filter_of_ne fun _ _ => id

@[to_additive]
theorem prod_filter (p : ι → Prop) [DecidablePred p] (f : ι → M) :
    ∏ a ∈ s with p a, f a = ∏ a ∈ s, if p a then f a else 1 :=
  calc
    ∏ a ∈ s with p a, f a = ∏ a ∈ s with p a, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a ∈ s, if p a then f a else 1 := by
      { refine prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter, not_and] at h
        exact if_neg (by simpa using h hs) }

@[to_additive]
theorem prod_eq_single_of_mem {s : Finset ι} {f : ι → M} (a : ι) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : ∏ x ∈ s, f x = f a := by
  calc
    ∏ x ∈ s, f x = ∏ x ∈ {a}, f x := by
      { refine (prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]
theorem prod_eq_single {s : Finset ι} {f : ι → M} (a : ι) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1)
    (h₁ : a ∉ s → f a = 1) : ∏ x ∈ s, f x = f a :=
  haveI := Classical.decEq ι
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
    (prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans <|
      prod_const_one.trans (h₁ this).symm

@[to_additive]
lemma prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) :
    ∏ x ∈ s, f x = if a ∈ s then f a else 1 := by
  by_cases h : a ∈ s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : ∀ b ∈ s, f b = 1 := by aesop
    simp +contextual [h₀]

@[to_additive]
lemma prod_union_eq_left [DecidableEq ι] (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₁, f a :=
  Eq.symm <|
    prod_subset subset_union_left fun _a ha ha' ↦ hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]
lemma prod_union_eq_right [DecidableEq ι] (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₂, f a := by rw [union_comm, prod_union_eq_left hs]

/-- The products of two functions `f g : ι → M` over finite sets `s₁ s₂ : Finset ι`
are equal if the functions agree on `s₁ ∩ s₂`, `f = 1` and `g = 1` on the respective
set differences. -/
@[to_additive /-- The sum of two functions `f g : ι → M` over finite sets `s₁ s₂ : Finset ι`
are equal if the functions agree on `s₁ ∩ s₂`, `f = 0` and `g = 0` on the respective
set differences. -/]
lemma prod_congr_of_eq_on_inter {ι M : Type*} {s₁ s₂ : Finset ι} {f g : ι → M} [CommMonoid M]
    (h₁ : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) (h₂ : ∀ a ∈ s₂, a ∉ s₁ → g a = 1)
    (h : ∀ a ∈ s₁, a ∈ s₂ → f a = g a) :
    ∏ a ∈ s₁, f a = ∏ a ∈ s₂, g a := by
  classical
  conv_lhs => rw [← sdiff_union_inter s₁ s₂, prod_union_eq_right (by simp_all)]
  conv_rhs => rw [← sdiff_union_inter s₂ s₁, prod_union_eq_right (by simp_all), inter_comm]
  exact prod_congr rfl (by simpa)

@[to_additive]
theorem prod_eq_mul_of_mem {s : Finset ι} {f : ι → M} (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' ⊆ s := by grind
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
theorem prod_eq_mul {s : Finset ι} {f : ι → M} (a b : ι) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq ι; by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      _root_.trans
        (prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one

/-- A product over `s.subtype p` equals one over `{x ∈ s | p x}`. -/
@[to_additive (attr := simp)
/-- A sum over `s.subtype p` equals one over `{x ∈ s | p x}`. -/]
theorem prod_subtype_eq_prod_filter (f : ι → M) {p : ι → Prop} [DecidablePred p] :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s with p x, f x := by
  have := prod_map (s.subtype p) (Function.Embedding.subtype _) f
  simp_all

/-- If all elements of a `Finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive /-- If all elements of a `Finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`. -/]
theorem prod_subtype_of_mem (f : ι → M) {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s, f x := by
  rw [prod_subtype_eq_prod_filter, filter_true_of_mem]
  simpa using h

/-- A product of a function over a `Finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `Finset`. -/
@[to_additive /-- A sum of a function over a `Finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `Finset`. -/]
theorem prod_subtype_map_embedding {p : ι → Prop} {s : Finset { x // p x }} {f : { x // p x } → M}
    {g : ι → M} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x ∈ s.map (Function.Embedding.subtype _), g x) = ∏ x ∈ s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
theorem prod_coe_sort : ∏ i : s, f i = ∏ i ∈ s, f i := prod_attach _ _

@[to_additive]
theorem prod_finset_coe (f : ι → M) (s : Finset ι) : (∏ i : (s : Set ι), f i) = ∏ i ∈ s, f i :=
  prod_coe_sort s f

variable {f s}

@[to_additive]
theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : ∀ x, x ∈ s ↔ p x)
    (f : ι → M) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr!

@[to_additive]
theorem prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i :=
  (Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive /-- The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`. -/]
theorem prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· ∈ s)] (f : ι → M) (g : s → M)
    (w : ∀ x (hx : x ∈ s), f x = g ⟨x, hx⟩) (w' : ∀ x ∉ s, f x = 1) : ∏ i, f i = ∏ i, g i := by
  rw [← prod_subset s.toFinset.subset_univ (by simpa), prod_subtype (p := (· ∈ s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

@[to_additive]
theorem prod_extend_by_one [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i :=
  (prod_congr rfl) fun _i hi => if_pos hi

@[to_additive]
theorem prod_eq_prod_extend (f : s → M) : ∏ x, f x = ∏ x ∈ s, Subtype.val.extend f 1 x := by
  rw [univ_eq_attach, ← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

@[to_additive]
theorem prod_bij_ne_one {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}
    (i : ∀ a ∈ s, f a ≠ 1 → κ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
    (i_inj : ∀ a₁ h₁₁ h₁₂ a₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, i a h₁ h₂ = b) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  classical
  calc
    ∏ x ∈ s, f x = ∏ x ∈ s with f x ≠ 1, f x := by rw [prod_filter_ne_one]
    _ = ∏ x ∈ t with g x ≠ 1, g x :=
      prod_bij (fun a ha => i a (mem_filter.mp ha).1 <| by simpa using (mem_filter.mp ha).2)
        ?_ ?_ ?_ ?_
    _ = ∏ x ∈ t, g x := prod_filter_ne_one _
  · grind
  · solve_by_elim
  · intro b hb
    refine (mem_filter.mp hb).elim fun h₁ h₂ ↦ ?_
    obtain ⟨a, ha₁, ha₂, eq⟩ := i_surj b h₁ fun H ↦ by rw [H] at h₂; simp at h₂
    exact ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩
  · solve_by_elim

@[to_additive]
theorem exists_ne_one_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  classical
    rw [← prod_filter_ne_one] at h
    rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩
    exact ⟨x, (mem_filter.1 hx).1, by simpa using (mem_filter.1 hx).2⟩

@[to_additive]
theorem prod_range_succ_comm (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = f n * ∏ x ∈ range n, f x := by
  rw [range_add_one, prod_insert notMem_range_self]

@[to_additive]
theorem prod_range_succ (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = (∏ x ∈ range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
theorem prod_range_succ' (f : ℕ → M) :
    ∀ n : ℕ, (∏ k ∈ range (n + 1), f k) = (∏ k ∈ range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]

@[to_additive]
theorem eventually_constant_prod {u : ℕ → M} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k ∈ range n, u k) = ∏ k ∈ range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, prod_range_succ, hm, hu]

@[to_additive]
theorem prod_range_add (f : ℕ → M) (n m : ℕ) :
    (∏ x ∈ range (n + m), f x) = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive sum_range_one]
theorem prod_range_one (f : ℕ → M) : ∏ k ∈ range 1, f k = f 0 := by
  rw [range_one, prod_singleton]

open List

@[to_additive]
theorem prod_list_map_count [DecidableEq ι] (l : List ι) (f : ι → M) :
    (l.map f).prod = ∏ m ∈ l.toFinset, f m ^ l.count m := by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a ∈ s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (notMem_erase _ _),
      prod_insert (notMem_erase _ _), ← mul_assoc, count_cons_self, pow_succ']
    congr 1
    refine prod_congr rfl fun x hx => ?_
    rw [count_cons_of_ne (ne_of_mem_erase hx).symm]
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_toFinset.2 has), pow_one]
  grind [Finset.prod_congr]

@[to_additive]
theorem prod_list_count [DecidableEq M] (s : List M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by simpa using prod_list_map_count s id

@[to_additive]
theorem prod_list_count_of_subset [DecidableEq M] (m : List M) (s : Finset M)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]

open Multiset

@[to_additive]
theorem prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
    (f : ι → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]
theorem prod_multiset_count [DecidableEq M] (s : Multiset M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  convert prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
theorem prod_multiset_count_of_subset [DecidableEq M] (m : Multiset M) (s : Finset M)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms up to `n`.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive /-- For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we
can verify that it's equal to a different function just by checking differences of adjacent terms
up to `n`.

This is a discrete analogue of the fundamental theorem of calculus. -/]
theorem prod_range_induction (f s : ℕ → M) (base : s 0 = 1)
    (n : ℕ) (step : ∀ k < n, s (k + 1) = s k * f k) :
    ∏ k ∈ Finset.range n, f k = s n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ, step _ (Nat.lt_succ_self _), hk]
    exact fun _ hl ↦ step _ (Nat.lt_succ_of_lt hl)

@[to_additive (attr := simp)]
theorem prod_const (b : M) : ∏ _x ∈ s, b = b ^ #s :=
  (congr_arg _ <| s.val.map_const b).trans <| Multiset.prod_replicate #s b

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card {b : M} (hf : ∀ a ∈ s, f a = b) : ∏ a ∈ s, f a = b ^ #s :=
  (prod_congr rfl hf).trans <| prod_const _

@[to_additive card_nsmul_add_sum]
theorem pow_card_mul_prod {b : M} : b ^ #s * ∏ a ∈ s, f a = ∏ a ∈ s, b * f a :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive sum_add_card_nsmul]
theorem prod_mul_pow_card {b : M} : (∏ a ∈ s, f a) * b ^ #s = ∏ a ∈ s, f a * b :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive]
theorem pow_eq_prod_const (b : M) : ∀ n, b ^ n = ∏ _k ∈ range n, b := by simp

@[to_additive sum_nsmul_assoc]
lemma prod_pow_eq_pow_sum (s : Finset ι) (f : ι → ℕ) (a : M) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
  cons_induction (by simp) (fun _ _ _ _ ↦ by simp [prod_cons, sum_cons, pow_add, *]) s

@[to_additive]
theorem prod_flip {n : ℕ} (f : ℕ → M) :
    (∏ r ∈ range (n + 1), f (n - r)) = ∏ k ∈ range (n + 1), f k := by
  induction n with
  | zero => rw [prod_range_one, prod_range_one]
  | succ n ih =>
    rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]

/-- The difference with `Finset.prod_ninvolution` is that the involution is allowed to use
membership of the domain of the product, rather than being a non-dependent function. -/
@[to_additive /-- The difference with `Finset.sum_ninvolution` is that the involution is allowed to
use membership of the domain of the sum, rather than being a non-dependent function. -/]
lemma prod_involution (g : ∀ a ∈ s, ι) (hg₁ : ∀ a ha, f a * f (g a ha) = 1)
    (hg₃ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
    (g_mem : ∀ a ha, g a ha ∈ s) (hg₄ : ∀ a ha, g (g a ha) (g_mem a ha) = a) :
    ∏ x ∈ s, f x = 1 := by
  classical
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have : {x, g x hx} ⊆ s := by simp [insert_subset_iff, hx, g_mem]
  suffices h : ∏ x ∈ s \ {x, g x hx}, f x = 1 by
    rw [← prod_sdiff this, h, one_mul]
    cases eq_or_ne (g x hx) x with
    | inl hx' => simpa [hx'] using hg₃ x hx
    | inr hx' => grind
  suffices h₃ : ∀ a (ha : a ∈ s \ {x, g x hx}), g a (sdiff_subset ha) ∈ s \ {x, g x hx} from
    ih (s \ {x, g x hx}) (ssubset_iff.2 ⟨x, by simp [insert_subset_iff, hx]⟩) _
      (by simp [hg₁]) (fun _ _ => hg₃ _ _) h₃ (fun _ _ => hg₄ _ _)
  grind

/-- The difference with `Finset.prod_involution` is that the involution is a non-dependent function,
rather than being allowed to use membership of the domain of the product. -/
@[to_additive /-- The difference with `Finset.sum_involution` is that the involution is a
non-dependent function, rather than being allowed to use membership of the domain of the sum. -/]
lemma prod_ninvolution (g : ι → ι) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 :=
  prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `Finset.prod_image`. -/
@[to_additive /-- The sum of the composition of functions `f` and `g`, is the sum over
`b ∈ s.image g` of `f b` times of the cardinality of the fibre of `b`. See also
`Finset.sum_image`. -/]
theorem prod_comp [DecidableEq κ] (f : κ → M) (g : ι → κ) :
    ∏ a ∈ s, f (g a) = ∏ b ∈ s.image g, f b ^ #{a ∈ s | g a = b} := by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ ↦ mem_image_of_mem _]

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive /-- A sum can be partitioned into a sum of sums, each equivalent under a setoid. -/]
theorem prod_partition (R : Setoid ι) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive /-- If we can partition a sum into subsets that cancel out, then the whole sum
cancels. -/]
theorem prod_cancels_of_partition_cancels (R : Setoid ι) [DecidableRel R]
    (h : ∀ x ∈ s, ∏ a ∈ s with R a x, f a = 1) : ∏ x ∈ s, f x = 1 := by
  rw [prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

/-- If a product of a `Finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq /-- If a sum of a `Finset` of size at most 1 has a given
value, so do the terms in that sum. -/]
theorem eq_of_card_le_one_of_prod_eq {s : Finset ι} (hc : #s ≤ 1) {f : ι → M} {b : M}
    (h : ∏ x ∈ s, f x = b) : ∀ x ∈ s, f x = b := by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    grind

/-- Taking a product over `s : Finset ι` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `Multiset.prod_map_erase` for the `Multiset` version. -/
@[to_additive /-- Taking a sum over `s : Finset ι` is the same as adding the value on a single
element `f a` to the sum over `s.erase a`.

See `Multiset.sum_map_erase` for the `Multiset` version. -/]
theorem mul_prod_erase [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  rw [← prod_insert (notMem_erase a s), insert_erase h]

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive /-- A variant of `Finset.add_sum_erase` with the addition swapped. -/]
theorem prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `Finset`. -/
@[to_additive /-- If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `Finset`. -/]
theorem prod_erase [DecidableEq ι] (s : Finset ι) {f : ι → M} {a : ι} (h : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine prod_subset sdiff_subset fun x hx hnx => ?_
  grind

@[to_additive]
theorem prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
    [MulLeftStrictMono κ] {s : Finset ι} {d : ι} (hd : d ∈ s) {f : ι → κ}
    (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by
  conv in ∏ m ∈ s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `Finset`. -/
@[to_additive /-- If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `Finset`. -/]
theorem eq_one_of_prod_eq_one {s : Finset ι} {f : ι → M} {a : ι} (hp : ∏ x ∈ s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (notMem_singleton.1 ha),
        prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive]
lemma prod_mul_eq_prod_mul_of_exists {s : Finset ι} {f : ι → M} {b₁ b₂ : M}
    (a : ι) (ha : a ∈ s) (h : f a * b₁ = f a * b₂) :
    (∏ a ∈ s, f a) * b₁ = (∏ a ∈ s, f a) * b₂ := by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc, mul_comm, mul_assoc, mul_comm b₁, h, ← mul_assoc, mul_comm _ (f a)]

@[to_additive]
lemma prod_filter_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {n : κ} {I : Finset κ}
    (hn : n ∈ I) (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ j ∈ I with f j = f n, g (f j) = g (f n) := by
  classical
  have h j (hj : j ∈ {i ∈ I | f i = f n}.erase n) : g (f j) = 1 := by
    simp only [mem_erase, mem_filter] at hj
    exact hf hj.2.1 hn hj.1 hj.2.2
  rw [← mul_one (g (f n)), ← prod_eq_one h,
    ← mul_prod_erase {i ∈ I | f i = f n} (fun i ↦ g (f i)) <| mem_filter.mpr ⟨hn, by rfl⟩]

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 1`.
The conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
/-- A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 0`.
The conclusion is the same as in `sum_image`. -/]
lemma prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {I : Finset κ}
    (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 1`. The
conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
/-- A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 0`. The
conclusion is the same as in `sum_image`. -/]
lemma prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ → ι} {g : ι → M}
    (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  refine prod_image_of_pairwise_eq_one <| hf_disj.imp fun i j hdisj hfij ↦ ?_
  rw [Function.onFun, ← hfij, disjoint_self] at hdisj
  rw [hdisj, hg_bot]

@[to_additive]
theorem prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι → M) (h : s.Nonempty) :
    ∏ x ∈ s, f x = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]

lemma prod_dvd_prod_of_dvd (f g : ι → M) (h : ∀ i ∈ s, f i ∣ g i) :
    ∏ i ∈ s, f i ∣ ∏ i ∈ s, g i :=
  Multiset.prod_dvd_prod_of_dvd _ _ h

@[to_additive]
theorem prod_map_equiv (e : ι ≃ κ) : (s.map e).prod (f ∘ e.symm) = s.prod f := by simp

@[to_additive]
theorem prod_comp_equiv {f : κ → M} (e : ι ≃ κ) : s.prod (f ∘ e) = (s.map e).prod f := by simp

end CommMonoid

section CancelCommMonoid
variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι → M}

@[to_additive]
lemma prod_sdiff_eq_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i = ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i = ∏ i ∈ t, f i :=
  eq_comm.trans <| eq_iff_eq_of_mul_eq_mul <| by
    rw [← prod_union disjoint_sdiff_self_left, ← prod_union disjoint_sdiff_self_left,
      sdiff_union_self_eq_union, sdiff_union_self_eq_union, union_comm]

@[to_additive]
lemma prod_sdiff_ne_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i ≠ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≠ ∏ i ∈ t, f i :=
  prod_sdiff_eq_prod_sdiff_iff.not

end CancelCommMonoid

section CommGroup
variable [CommGroup G] [DecidableEq ι] {f : ι → G}

@[to_additive]
lemma prod_insert_div (ha : a ∉ s) (f : ι → G) :
    (∏ x ∈ insert a s, f x) / f a = ∏ x ∈ s, f x := by simp [ha]

@[to_additive (attr := simp)]
theorem prod_erase_eq_div {a : ι} (h : a ∈ s) : ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]

/-- A telescoping product along `{0, ..., n - 1}` of a commutative-group-valued function reduces to
the ratio of the last and first factors. -/
@[to_additive /-- A telescoping sum along `{0, ..., n - 1}` of a function valued in a commutative
additive group reduces to the difference of the last and first terms. -/]
lemma prod_range_div (f : ℕ → G) (n : ℕ) : (∏ i ∈ range n, f (i + 1) / f i) = f n / f 0 := by
  apply prod_range_induction <;> simp

@[to_additive]
lemma prod_range_div' (f : ℕ → G) (n : ℕ) : (∏ i ∈ range n, f i / f (i + 1)) = f 0 / f n := by
  apply prod_range_induction <;> simp

@[to_additive]
lemma eq_prod_range_div (f : ℕ → G) (n : ℕ) : f n = f 0 * ∏ i ∈ range n, f (i + 1) / f i := by
  rw [prod_range_div, mul_div_cancel]

@[to_additive]
lemma eq_prod_range_div' (f : ℕ → G) (n : ℕ) :
    f n = ∏ i ∈ range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

@[to_additive]
lemma prod_range_add_div_prod_range (f : ℕ → G) (n m : ℕ) :
    (∏ k ∈ range (n + m), f k) / ∏ k ∈ range n, f k = ∏ k ∈ Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive (attr := simp)]
lemma prod_sdiff_eq_div (h : s₁ ⊆ s₂) : ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[to_additive]
theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

end CommGroup

section OrderedSub
variable [AddCommMonoid M] [PartialOrder M] [Sub M] [OrderedSub M] [AddLeftMono M]
  [AddLeftReflectLE M] [ExistsAddOfLE M]

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function reduces to the difference of
the last and first terms when the function we are summing is monotone. -/
lemma sum_range_tsub {f : ℕ → M} (h : Monotone f) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n _
    have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]

lemma sum_tsub_distrib (s : Finset ι) {f g : ι → M} (hfg : ∀ x ∈ s, g x ≤ f x) :
    ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := Multiset.sum_map_tsub _ hfg

end OrderedSub

section Nat

lemma card_eq_sum_ones (s : Finset ι) : #s = ∑ _ ∈ s, 1 := by simp

theorem sum_const_nat {m : ℕ} {f : ι → ℕ} (h₁ : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁

lemma sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι → κ) : ∑ j ∈ t, #{i ∈ s | g i = j} = #{i ∈ s | g i ∈ t} := by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

@[simp] 
theorem card_disjiUnion (s : Finset ι) (t : ι → Finset M) (h) :
    #(s.disjiUnion t h) = ∑ a ∈ s, #(t a) :=
  Multiset.card_bind _ _

theorem card_biUnion [DecidableEq M] {t : ι → Finset M} (h : s.toSet.PairwiseDisjoint t) :
    #(s.biUnion t) = ∑ u ∈ s, #(t u) := by simpa using sum_biUnion h (M := ℕ) (f := 1)

theorem card_biUnion_le [DecidableEq M] {s : Finset ι} {t : ι → Finset M} :
    #(s.biUnion t) ≤ ∑ a ∈ s, #(t a) :=
  haveI := Classical.decEq ι
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) ≤ #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ ≤ ∑ a ∈ insert a s, #(t a) := by grind

theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M}
    (H : s.toSet.MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b} := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

theorem card_eq_sum_card_image [DecidableEq M] (f : ι → M) (s : Finset ι) :
    #s = ∑ b ∈ s.image f, #{a ∈ s | f a = b} :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

end Nat
end Finset

namespace Fintype
variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid M]

@[to_additive]
lemma prod_of_injective (e : ι → κ) (he : Injective e) (f : ι → M) (g : κ → M)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j :=
  prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ ↦ h i)

@[to_additive]
lemma prod_fiberwise [DecidableEq κ] (g : ι → κ) (f : ι → M) :
    ∏ j, ∏ i : {i // g i = j}, f i = ∏ i, f i := by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]
lemma prod_fiberwise' [DecidableEq κ] (g : ι → κ) (f : κ → M) :
    ∏ j, ∏ _i : {i // g i = j}, f j = ∏ i, f (g i) := by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ ↦ _).symm

@[to_additive]
theorem prod_unique [Unique ι] (f : ι → M) : ∏ x : ι, f x = f default := by
  rw [univ_unique, prod_singleton]

@[to_additive]
theorem prod_subsingleton [Subsingleton ι] (f : ι → M) (a : ι) : ∏ x : ι, f x = f a := by
  have : Unique ι := uniqueOfSubsingleton a
  rw [prod_unique f, Subsingleton.elim default a]

@[to_additive] theorem prod_Prop (f : Prop → M) : ∏ p, f p = f True * f False := by simp

@[to_additive]
theorem prod_subtype_mul_prod_subtype (p : ι → Prop) (f : ι → M) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

@[to_additive] lemma prod_subset {s : Finset ι} {f : ι → M} (h : ∀ i, f i ≠ 1 → i ∈ s) :
    ∏ i ∈ s, f i = ∏ i, f i :=
  Finset.prod_subset s.subset_univ <| by simpa [not_imp_comm (a := _ ∈ s)]

end CommMonoid
end Fintype

namespace List

@[to_additive]
theorem prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι → M) :
    ∀ {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨notMem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp notMem), prod_toFinset _ hl]

@[simp]
theorem sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : ℕ)).symm

end List

namespace Multiset

@[simp]
lemma mem_sum {a : M} {s : Finset ι} {m : ι → Multiset M} :
    a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  induction s using Finset.cons_induction with grind

@[deprecated Multiset.mem_sum (since := "2025-08-24")]
theorem _root_.Finset.mem_sum {f : ι → Multiset M} (s : Finset ι) (b : M) :
    (b ∈ ∑ x ∈ s, f x) ↔ ∃ a ∈ s, b ∈ f a := Multiset.mem_sum

variable [DecidableEq ι]

theorem toFinset_sum_count_eq (s : Multiset ι) : ∑ a ∈ s.toFinset, s.count a = card s := by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : ℕ))).symm

@[simp] lemma sum_count_eq_card {s : Finset ι} {m : Multiset ι} (hms : ∀ a ∈ m, a ∈ s) :
    ∑ a ∈ s, m.count a = card m := by
  rw [← toFinset_sum_count_eq, ← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[simp]
theorem toFinset_sum_count_nsmul_eq (s : Multiset ι) :
    ∑ a ∈ s.toFinset, s.count a • {a} = s := by
  rw [← Finset.sum_multiset_map_count, Multiset.sum_map_singleton]

theorem exists_smul_of_dvd_count (s : Multiset ι) {k : ℕ}
    (h : ∀ a : ι, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset ι, s = k • u := by
  use ∑ a ∈ s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x ∈ s.toFinset, k • (count x s / k) • ({x} : Multiset ι)) =
      ∑ x ∈ s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, toFinset_sum_count_nsmul_eq]

@[to_additive]
theorem prod_sum {ι : Type*} [CommMonoid M] (f : ι → Multiset M) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by
  induction s using Finset.cons_induction with grind

end Multiset

@[to_additive (attr := simp)]
lemma IsUnit.prod_iff [CommMonoid M] {f : ι → M} :
    IsUnit (∏ a ∈ s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with grind

@[to_additive]
lemma IsUnit.prod_univ_iff [Fintype ι] [CommMonoid M] {f : ι → M} :
    IsUnit (∏ a, f a) ↔ ∀ a, IsUnit (f a) := by simp

theorem nat_abs_sum_le (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  induction s using Finset.cons_induction with grind
