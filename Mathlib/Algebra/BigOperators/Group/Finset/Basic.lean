/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Piecewise
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod

/-!
# Big operators

In this file we prove theorems about products and sums indexed by a `Finset`.

-/

-- TODO
-- assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction OrderedCommMonoid
assert_not_exists Finset.preimage Finset.sigma Fintype.piFinset

variable {ι κ α β γ : Type*}

open Fin Function

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

@[to_additive]
theorem prod_eq_fold [CommMonoid β] (s : Finset α) (f : α → β) :
    ∏ x ∈ s, f x = s.fold ((· * ·) : β → β → β) 1 f :=
  rfl

end Finset

@[to_additive]
theorem MonoidHom.coe_finset_prod [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α) :
    ⇑(∏ x ∈ s, f x) = ∏ x ∈ s, ⇑(f x) :=
  map_prod (MonoidHom.coeFn β γ) _ _

/-- See also `Finset.prod_apply`, with the same conclusion but with the weaker hypothesis
`f : α → β → γ` -/
@[to_additive (attr := simp)
  "See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
  `f : α → β → γ`"]
theorem MonoidHom.finset_prod_apply [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α)
    (b : β) : (∏ x ∈ s, f x) b = ∏ x ∈ s, f x b :=
  map_prod (MonoidHom.eval b) _ _

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[to_additive (attr := simp)]
theorem prod_cons (h : a ∉ s) : ∏ x ∈ cons a s h, f x = f a * ∏ x ∈ s, f x :=
  fold_cons h

@[to_additive (attr := simp)]
theorem prod_insert [DecidableEq α] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x :=
  fold_insert

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`. -/
@[to_additive (attr := simp) "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`."]
theorem prod_insert_of_eq_one_if_not_mem [DecidableEq α] (h : a ∉ s → f a = 1) :
    ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by
  by_cases hm : a ∈ s
  · simp_rw [insert_eq_of_mem hm]
  · rw [prod_insert hm, h hm, one_mul]

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `f a = 1`. -/
@[to_additive (attr := simp) "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`."]
theorem prod_insert_one [DecidableEq α] (h : f a = 1) : ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x :=
  prod_insert_of_eq_one_if_not_mem fun _ => h

@[to_additive]
theorem prod_insert_div {M : Type*} [CommGroup M] [DecidableEq α] (ha : a ∉ s) {f : α → M} :
    (∏ x ∈ insert a s, f x) / f a = ∏ x ∈ s, f x := by simp [ha]

@[to_additive (attr := simp)]
theorem prod_singleton (f : α → β) (a : α) : ∏ x ∈ singleton a, f x = f a :=
  Eq.trans fold_singleton <| mul_one _

@[to_additive]
theorem prod_pair [DecidableEq α] {a b : α} (h : a ≠ b) :
    (∏ x ∈ ({a, b} : Finset α), f x) = f a * f b := by
  rw [prod_insert (not_mem_singleton.2 h), prod_singleton]

@[to_additive (attr := simp)]
theorem prod_image [DecidableEq α] {s : Finset γ} {g : γ → α} :
    (∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x) :=
  fold_image

@[to_additive]
lemma prod_attach (s : Finset α) (f : α → β) : ∏ x ∈ s.attach, f x = ∏ x ∈ s, f x := by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[to_additive (attr := congr)]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr

@[to_additive]
theorem prod_eq_one {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 1) : ∏ x ∈ s, f x = 1 :=
  calc
    ∏ x ∈ s, f x = ∏ _x ∈ s, 1 := Finset.prod_congr rfl h
    _ = 1 := Finset.prod_const_one

@[to_additive]
theorem prod_disjUnion (h) :
    ∏ x ∈ s₁.disjUnion s₂ h, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  refine Eq.trans ?_ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]
theorem prod_disjiUnion (s : Finset ι) (t : ι → Finset α) (h) :
    ∏ x ∈ s.disjiUnion t h, f x = ∏ i ∈ s, ∏ x ∈ t i, f x := by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]
theorem prod_union_inter [DecidableEq α] :
    (∏ x ∈ s₁ ∪ s₂, f x) * ∏ x ∈ s₁ ∩ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x :=
  fold_union_inter

@[to_additive]
theorem prod_union [DecidableEq α] (h : Disjoint s₁ s₂) :
    ∏ x ∈ s₁ ∪ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]
theorem prod_filter_mul_prod_filter_not
    (s : Finset α) (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] (f : α → β) :
    (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, f x = ∏ x ∈ s, f x := by
  have := Classical.decEq α
  rw [← prod_union (disjoint_filter_filter_neg s s p), filter_union_filter_neg_eq]

@[to_additive]
lemma prod_filter_not_mul_prod_filter (s : Finset α) (p : α → Prop) [DecidablePred p]
    [∀ x, Decidable (¬p x)] (f : α → β) :
    (∏ x ∈ s with ¬p x, f x) * ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x := by
  rw [mul_comm, prod_filter_mul_prod_filter_not]

@[to_additive]
theorem prod_filter_xor (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (∏ x ∈ s with (Xor' (p x) (q x)), f x) =
      (∏ x ∈ s with (p x ∧ ¬ q x), f x) * (∏ x ∈ s with (q x ∧ ¬ p x), f x) := by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor']

/-- In a monoid whose only unit is `1`, a product is equal to `1` iff all factors are `1`. -/
@[to_additive (attr := simp)
"In a monoid whose only unit is `0`, a sum is equal to `0` iff all terms are `0`."]
lemma prod_eq_one_iff [Subsingleton βˣ] : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction' s using Finset.cons_induction with i s hi ih <;> simp [*]

@[deprecated (since := "2025-03-31")] alias prod_eq_one_iff' := prod_eq_one_iff

end CommMonoid

end Finset

section

open Finset

variable [Fintype α] [CommMonoid β]

@[to_additive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i, f i :=
  (Finset.prod_disjUnion h.disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

end

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
theorem prod_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) :
    (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[to_additive]
theorem prod_subset_one_on_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i ∈ s₁, f i = ∏ i ∈ s₂, g i := by
  rw [← prod_sdiff h, prod_eq_one hg, one_mul]
  exact prod_congr rfl hfg

@[to_additive]
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x :=
  haveI := Classical.decEq α
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]
theorem prod_disj_sum (s : Finset α) (t : Finset γ) (f : α ⊕ γ → β) :
    ∏ x ∈ s.disjSum t, f x = (∏ x ∈ s, f (Sum.inl x)) * ∏ x ∈ t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr, prod_disjUnion, prod_map, prod_map]
  rfl

@[to_additive]
lemma prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (α ⊕ γ)) (f : α ⊕ γ → β) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by
  rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disj_sum, Finset.toLeft_disjSum,
    Finset.toRight_disjSum]

@[to_additive]
theorem prod_sumElim (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β) :
    ∏ x ∈ s.disjSum t, Sum.elim f g x = (∏ x ∈ s, f x) * ∏ x ∈ t, g x := by simp

@[deprecated (since := "2025-02-20")] alias prod_sum_elim := prod_sumElim
@[deprecated (since := "2025-02-20")] alias sum_sum_elim := sum_sumElim

@[to_additive]
theorem prod_biUnion [DecidableEq α] {s : Finset γ} {t : γ → Finset α}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by
  rw [← disjiUnion_eq_biUnion _ _ hs, prod_disjiUnion]

section bij
variable {ι κ α : Type*} [CommMonoid α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α}

@[to_additive]
lemma prod_of_injOn (e : ι → κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
    (h' : ∀ i ∈ t, i ∉ e '' s → g i = 1) (h : ∀ i ∈ s, f i = g (e i))  :
    ∏ i ∈ s, f i = ∏ j ∈ t, g j := by
  classical
  exact (prod_nbij e (fun a ↦ mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans <|
    prod_subset (image_subset_iff.2 hest) <| by simpa using h'

variable [DecidableEq κ]

@[to_additive]
lemma prod_fiberwise_eq_prod_filter (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s with g i ∈ t, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq]

@[to_additive]
lemma prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : κ → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s with g i ∈ t, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        prod_congr rfl fun j _ ↦ prod_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]
    _ = _ := prod_fiberwise_eq_prod_filter _ _ _ _

@[to_additive]
lemma prod_fiberwise_of_maps_to {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : ι → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq_of_maps_to h]

@[to_additive]
lemma prod_fiberwise_of_maps_to' {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : κ → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        prod_congr rfl fun y _ ↦ prod_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
    _ = _ := prod_fiberwise_of_maps_to h _

variable [Fintype κ]

@[to_additive]
lemma prod_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → α) :
    ∏ j, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i :=
  prod_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _

@[to_additive]
lemma prod_fiberwise' (s : Finset ι) (g : ι → κ) (f : κ → α) :
    ∏ j, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) :=
  prod_fiberwise_of_maps_to' (fun _ _ ↦ mem_univ _) _

end bij

@[to_additive (attr := simp)]
lemma prod_diag [DecidableEq α] (s : Finset α) (f : α × α → β) :
    ∏ i ∈ s.diag, f i = ∏ i ∈ s, f (i, i) := by
  apply prod_nbij' Prod.fst (fun i ↦ (i, i)) <;> simp

@[to_additive]
theorem prod_image' [DecidableEq α] {s : Finset ι} {g : ι → α} (h : ι → β)
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
lemma prod_mul_prod_comm (f g h i : α → β) :
    (∏ a ∈ s, f a * g a) * ∏ a ∈ s, h a * i a = (∏ a ∈ s, f a * h a) * ∏ a ∈ s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
theorem prod_filter_of_ne {p : α → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x :=
  (prod_subset (filter_subset _ _)) fun x => by
    classical
      rw [not_imp_comm, mem_filter]
      exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

-- If we use `[DecidableEq β]` here, some rewrites fail because they find a wrong `Decidable`
-- instance first; `{∀ x, Decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
theorem prod_filter_ne_one (s : Finset α) [∀ x, Decidable (f x ≠ 1)] :
    ∏ x ∈ s with f x ≠ 1, f x = ∏ x ∈ s, f x :=
  prod_filter_of_ne fun _ _ => id

@[to_additive]
theorem prod_filter (p : α → Prop) [DecidablePred p] (f : α → β) :
    ∏ a ∈ s with p a, f a = ∏ a ∈ s, if p a then f a else 1 :=
  calc
    ∏ a ∈ s with p a, f a = ∏ a ∈ s with p a, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a ∈ s, if p a then f a else 1 := by
      { refine prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter, not_and] at h
        exact if_neg (by simpa using h hs) }

@[to_additive]
theorem prod_eq_single_of_mem {s : Finset α} {f : α → β} (a : α) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : ∏ x ∈ s, f x = f a := by
  haveI := Classical.decEq α
  calc
    ∏ x ∈ s, f x = ∏ x ∈ {a}, f x := by
      { refine (prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]
theorem prod_eq_single {s : Finset α} {f : α → β} (a : α) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1)
    (h₁ : a ∉ s → f a = 1) : ∏ x ∈ s, f x = f a :=
  haveI := Classical.decEq α
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
    (prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans <|
      prod_const_one.trans (h₁ this).symm

@[to_additive]
lemma prod_union_eq_left [DecidableEq α] (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₁, f a :=
  Eq.symm <|
    prod_subset subset_union_left fun _a ha ha' ↦ hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]
lemma prod_union_eq_right [DecidableEq α] (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₂, f a := by rw [union_comm, prod_union_eq_left hs]

@[to_additive]
theorem prod_eq_mul_of_mem {s : Finset α} {f : α → β} (a b : α) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq α; let s' := ({a, b} : Finset α)
  have hu : s' ⊆ s := by
    refine insert_subset_iff.mpr ?_
    apply And.intro ha
    apply singleton_subset_iff.mpr hb
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by
    intro c hc hcs
    apply h₀ c hc
    apply not_or.mp
    intro hab
    apply hcs
    rw [mem_insert, mem_singleton]
    exact hab
  rw [← prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
theorem prod_eq_mul {s : Finset α} {f : α → β} (a b : α) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq α; by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
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
"A sum over `s.subtype p` equals one over `{x ∈ s | p x}`."]
theorem prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [DecidablePred p] :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s with p x, f x := by
  have := prod_map (s.subtype p) (Function.Embedding.subtype _) f
  simp_all

/-- If all elements of a `Finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive "If all elements of a `Finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`."]
theorem prod_subtype_of_mem (f : α → β) {p : α → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s, f x := by
  rw [prod_subtype_eq_prod_filter, filter_true_of_mem]
  simpa using h

/-- A product of a function over a `Finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `Finset`. -/
@[to_additive "A sum of a function over a `Finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `Finset`."]
theorem prod_subtype_map_embedding {p : α → Prop} {s : Finset { x // p x }} {f : { x // p x } → β}
    {g : α → β} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x ∈ s.map (Function.Embedding.subtype _), g x) = ∏ x ∈ s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
theorem prod_coe_sort : ∏ i : s, f i = ∏ i ∈ s, f i := prod_attach _ _

@[to_additive]
theorem prod_finset_coe (f : α → β) (s : Finset α) : (∏ i : (s : Set α), f i) = ∏ i ∈ s, f i :=
  prod_coe_sort s f

variable {f s}

@[to_additive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x)
    (f : α → β) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr!

@[to_additive]
theorem prod_set_coe (s : Set α) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i :=
(Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive "The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`."]
theorem prod_congr_set {α : Type*} [CommMonoid α] {β : Type*} [Fintype β] (s : Set β)
    [DecidablePred (· ∈ s)] (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩)
    (w' : ∀ x : β, x ∉ s → f x = 1) : Finset.univ.prod f = Finset.univ.prod g := by
  rw [← @Finset.prod_subset _ _ s.toFinset Finset.univ f _ (by simp)]
  · rw [Finset.prod_subtype]
    · apply Finset.prod_congr rfl
      exact fun ⟨x, h⟩ _ => w x h
    · simp
  · rintro x _ h
    exact w' x (by simpa using h)

@[to_additive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p}
    [DecidablePred fun x => ¬p x] (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
  calc
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x ∈ s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x ∈ s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x ∈ s | p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x : {x ∈ s | ¬p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ (prod_attach _ _).symm (prod_attach _ _).symm
    _ = (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
          ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x _hx ↦
        congr_arg h (dif_pos <| by simpa using (mem_filter.mp x.2).2))
        (prod_congr rfl fun x _hx => congr_arg h (dif_neg <| by simpa using (mem_filter.mp x.2).2))

@[to_additive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {_hp : DecidablePred p} (f g : α → γ)
    (h : γ → β) :
    (∏ x ∈ s, h (if p x then f x else g x)) =
      (∏ x ∈ s with p x, h (f x)) * ∏ x ∈ s with ¬p x, h (g x) :=
  (prod_apply_dite _ _ _).trans <| congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

@[to_additive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) :
    ∏ x ∈ s, (if hx : p x then f x hx else g x hx) =
      (∏ x : {x ∈ s | p x}, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
lemma prod_dite_of_false {p : α → Prop} {_ : DecidablePred p} (h : ∀ i ∈ s, ¬ p i)
    (f : ∀ i, p i → β) (g : ∀ i, ¬ p i → β) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, g i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]
lemma prod_ite_of_false {p : α → Prop} {_ : DecidablePred p} (h : ∀ x ∈ s, ¬p x) (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, g x :=
  (prod_dite_of_false h _ _).trans (prod_attach _ _)

@[to_additive]
lemma prod_dite_of_true {p : α → Prop} {_ : DecidablePred p} (h : ∀ i ∈ s, p i) (f : ∀ i, p i → β)
    (g : ∀ i, ¬ p i → β) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]
lemma prod_ite_of_true {p : α → Prop} {_ : DecidablePred p} (h : ∀ x ∈ s, p x) (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, f x :=
  (prod_dite_of_true h _ _).trans (prod_attach _ _)

@[to_additive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_false h _ _

@[to_additive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (f x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_true h _ _

@[to_additive]
theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
    ∏ i ∈ s, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i :=
  (prod_congr rfl) fun _i hi => if_pos hi

@[to_additive]
theorem prod_eq_prod_extend (f : s → β) : ∏ x, f x = ∏ x ∈ s, Subtype.val.extend f 1 x := by
  rw [univ_eq_attach, ← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

@[to_additive (attr := simp)]
theorem prod_ite_mem [DecidableEq α] (s t : Finset α) (f : α → β) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]

@[to_additive]
lemma prod_attach_eq_prod_dite [Fintype α] (s : Finset α) (f : s → β) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite, Finset.univ_eq_attach, Finset.prod_const_one, mul_one]
  congr
  · ext; simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

@[to_additive (attr := simp)]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
    ∏ x ∈ s, (if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[to_additive (attr := simp)]
theorem prod_dite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, x = a → β) :
    ∏ x ∈ s, (if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `Finset.prod_ite_eq` is that the arguments to `Eq` are swapped. -/
@[to_additive (attr := simp) "A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped."]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
theorem prod_ite_eq_of_mem [DecidableEq α] (s : Finset α) (a : α) (b : α → β) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  simp only [prod_ite_eq, if_pos h]

/-- The difference with `Finset.prod_ite_eq_of_mem` is that the arguments to `Eq` are swapped. -/
@[to_additive]
theorem prod_ite_eq_of_mem' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) (h : a ∈ s) :
    (∏ x ∈ s, if x = a then b x else 1) = b a := by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle' [DecidableEq α] (a : α) (x : β) (s : Finset α) :
    ∏ a' ∈ s, Pi.mulSingle a x a' = if a ∈ s then x else 1 :=
  prod_dite_eq' _ _ _

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle {β : α → Type*} [DecidableEq α] [∀ a, CommMonoid (β a)] (a : α)
    (f : ∀ a, β a) (s : Finset α) :
    (∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1 :=
  prod_dite_eq _ _ _

@[to_additive]
lemma mulSupport_prod (s : Finset ι) (f : ι → α → β) :
    mulSupport (fun x ↦ ∏ i ∈ s, f i x) ⊆ ⋃ i ∈ s, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, nmem_mulSupport]
  exact fun x ↦ prod_eq_one

section indicator
open Set
variable {κ : Type*}

/-- Consider a product of `g i (f i)` over a finset.  Suppose `g` is a function such as
`n ↦ (· ^ n)`, which maps a second argument of `1` to `1`. Then if `f` is replaced by the
corresponding multiplicative indicator function, the finset may be replaced by a possibly larger
finset without changing the value of the product. -/
@[to_additive "Consider a sum of `g i (f i)` over a finset.  Suppose `g` is a function such as
`n ↦ (n • ·)`, which maps a second argument of `0` to `0` (or a weighted sum of `f i * h i` or
`f i • h i`, where `f` gives the weights that are multiplied by some other function `h`). Then if
`f` is replaced by the corresponding indicator function, the finset may be replaced by a possibly
larger finset without changing the value of the sum."]
lemma prod_mulIndicator_subset_of_eq_one [One α] (f : ι → α) (g : ι → α → β) {s t : Finset ι}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    ∏ i ∈ t, g i (mulIndicator ↑s f i) = ∏ i ∈ s, g i (f i) := by
  calc
    _ = ∏ i ∈ s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn ↦ by simp [hn, hg]]
    _ = _ := prod_congr rfl fun i hi ↦ congr_arg _ <| mulIndicator_of_mem hi f

/-- Taking the product of an indicator function over a possibly larger finset is the same as
taking the original function over the original finset. -/
@[to_additive "Summing an indicator function over a possibly larger `Finset` is the same as summing
  the original function over the original finset."]
lemma prod_mulIndicator_subset (f : ι → β) {s t : Finset ι} (h : s ⊆ t) :
    ∏ i ∈ t, mulIndicator (↑s) f i = ∏ i ∈ s, f i :=
  prod_mulIndicator_subset_of_eq_one _ (fun _ ↦ id) h fun _ ↦ rfl

@[to_additive]
lemma prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι → κ → β) (t : ι → Set κ) (g : ι → κ)
    [DecidablePred fun i ↦ g i ∈ t i] :
    ∏ i ∈ s, mulIndicator (t i) (f i) (g i) = ∏ i ∈ s with g i ∈ t i, f i (g i) := by
  refine (prod_filter_mul_prod_filter_not s (fun i ↦ g i ∈ t i) _).symm.trans <|
     Eq.trans (congr_arg₂ (· * ·) ?_ ?_) (mul_one _)
  · exact prod_congr rfl fun x hx ↦ mulIndicator_of_mem (mem_filter.1 hx).2 _
  · exact prod_eq_one fun x hx ↦ mulIndicator_of_not_mem (mem_filter.1 hx).2 _

@[to_additive]
lemma prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι → β) :
    ∏ i ∈ s, (t : Set ι).mulIndicator f i = ∏ i ∈ s ∩ t, f i := by
  rw [← filter_mem_eq_inter, prod_mulIndicator_eq_prod_filter]; rfl

@[to_additive]
lemma mulIndicator_prod (s : Finset ι) (t : Set κ) (f : ι → κ → β) :
    mulIndicator t (∏ i ∈ s, f i) = ∏ i ∈ s, mulIndicator t (f i) :=
  map_prod (mulIndicatorHom _ _) _ _

variable {κ : Type*}
@[to_additive]
lemma mulIndicator_biUnion (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (hs : (s : Set ι).PairwiseDisjoint t) :
    mulIndicator (⋃ i ∈ s, t i) f = fun a ↦ ∏ i ∈ s, mulIndicator (t i) f a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    ext j
    rw [coe_cons, Set.pairwiseDisjoint_insert_of_not_mem (Finset.mem_coe.not.2 hi)] at hs
    classical
    rw [prod_cons, cons_eq_insert, set_biUnion_insert, mulIndicator_union_of_not_mem_inter, ih hs.1]
    exact (Set.disjoint_iff.mp (Set.disjoint_iUnion₂_right.mpr hs.2) ·)

@[to_additive]
lemma mulIndicator_biUnion_apply (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (h : (s : Set ι).PairwiseDisjoint t) (x : κ) :
    mulIndicator (⋃ i ∈ s, t i) f x = ∏ i ∈ s, mulIndicator (t i) f x := by
  rw [mulIndicator_biUnion s t h]

end indicator

@[to_additive]
theorem prod_bij_ne_one {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}
    (i : ∀ a ∈ s, f a ≠ 1 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
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
  · intros a ha
    refine (mem_filter.mp ha).elim ?_
    intros h₁ h₂
    refine (mem_filter.mpr ⟨hi a h₁ _, ?_⟩)
    specialize h a h₁ fun H ↦ by rw [H] at h₂; simp at h₂
    rwa [← h]
  · intros a₁ ha₁ a₂ ha₂
    refine (mem_filter.mp ha₁).elim fun _ha₁₁ _ha₁₂ ↦ ?_
    refine (mem_filter.mp ha₂).elim fun _ha₂₁ _ha₂₂ ↦ ?_
    apply i_inj
  · intros b hb
    refine (mem_filter.mp hb).elim fun h₁ h₂ ↦ ?_
    obtain ⟨a, ha₁, ha₂, eq⟩ := i_surj b h₁ fun H ↦ by rw [H] at h₂; simp at h₂
    exact ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩
  · refine (fun a ha => (mem_filter.mp ha).elim fun h₁ h₂ ↦ ?_)
    exact h a h₁ fun H ↦ by rw [H] at h₂; simp at h₂

@[to_additive]
theorem exists_ne_one_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  classical
    rw [← prod_filter_ne_one] at h
    rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩
    exact ⟨x, (mem_filter.1 hx).1, by simpa using (mem_filter.1 hx).2⟩

@[to_additive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = f n * ∏ x ∈ range n, f x := by
  rw [range_succ, prod_insert not_mem_range_self]

@[to_additive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = (∏ x ∈ range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
theorem prod_range_succ' (f : ℕ → β) :
    ∀ n : ℕ, (∏ k ∈ range (n + 1), f k) = (∏ k ∈ range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]

@[to_additive]
theorem eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k ∈ range n, u k) = ∏ k ∈ range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, prod_range_succ, hm, hu]

@[to_additive]
theorem prod_range_add (f : ℕ → β) (n m : ℕ) :
    (∏ x ∈ range (n + m), f x) = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive]
theorem prod_range_add_div_prod_range {α : Type*} [CommGroup α] (f : ℕ → α) (n m : ℕ) :
    (∏ k ∈ range (n + m), f k) / ∏ k ∈ range n, f k = ∏ k ∈ Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive sum_range_one]
theorem prod_range_one (f : ℕ → β) : ∏ k ∈ range 1, f k = f 0 := by
  rw [range_one, prod_singleton]

open List

@[to_additive]
theorem prod_list_map_count [DecidableEq α] (l : List α) {M : Type*} [CommMonoid M] (f : α → M) :
    (l.map f).prod = ∏ m ∈ l.toFinset, f m ^ l.count m := by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a ∈ s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (not_mem_erase _ _),
      prod_insert (not_mem_erase _ _), ← mul_assoc, count_cons_self, pow_succ']
    congr 1
    refine prod_congr rfl fun x hx => ?_
    rw [count_cons_of_ne (ne_of_mem_erase hx).symm]
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_toFinset.2 has), pow_one]
  congr 1
  refine prod_congr rfl fun x hx => ?_
  rw [count_cons_of_ne]
  rintro rfl
  exact has hx

@[to_additive]
theorem prod_list_count [DecidableEq α] [CommMonoid α] (s : List α) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by simpa using prod_list_map_count s id

@[to_additive]
theorem prod_list_count_of_subset [DecidableEq α] [CommMonoid α] (m : List α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]

open Multiset

@[to_additive]
theorem prod_multiset_map_count [DecidableEq α] (s : Multiset α) {M : Type*} [CommMonoid M]
    (f : α → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]
theorem prod_multiset_count [DecidableEq α] [CommMonoid α] (s : Multiset α) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  convert prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
theorem prod_multiset_count_of_subset [DecidableEq α] [CommMonoid α] (m : Multiset α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive "For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can
verify that it's equal to a different function just by checking differences of adjacent terms.

This is a discrete analogue of the fundamental theorem of calculus."]
theorem prod_range_induction (f s : ℕ → β) (base : s 0 = 1)
    (step : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
    ∏ k ∈ Finset.range n, f k = s n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk => simp only [hk, Finset.prod_range_succ, step, mul_comm]

/-- A telescoping product along `{0, ..., n - 1}` of a commutative group valued function reduces to
the ratio of the last and first factors. -/
@[to_additive "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued
function reduces to the difference of the last and first terms."]
theorem prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ range n, f (i + 1) / f i) = f n / f 0 := by apply prod_range_induction <;> simp

@[to_additive]
theorem prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ range n, f i / f (i + 1)) = f 0 / f n := by apply prod_range_induction <;> simp

@[to_additive]
theorem eq_prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i ∈ range n, f (i + 1) / f i := by rw [prod_range_div, mul_div_cancel]

@[to_additive]
theorem eq_prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i ∈ range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
theorem sum_range_tsub [AddCommMonoid α] [PartialOrder α] [Sub α] [OrderedSub α]
    [AddLeftMono α] [AddLeftReflectLE α] [ExistsAddOfLE α]
    {f : ℕ → α} (h : Monotone f) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n
    have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]

theorem sum_tsub_distrib [AddCommMonoid α] [PartialOrder α] [ExistsAddOfLE α]
    [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)] [Sub α]
    [OrderedSub α] (s : Finset ι) {f g : ι → α} (hfg : ∀ x ∈ s, g x ≤ f x) :
    ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := sum_map_tsub _ hfg

@[to_additive (attr := simp)]
theorem prod_const (b : β) : ∏ _x ∈ s, b = b ^ #s :=
  (congr_arg _ <| s.val.map_const b).trans <| Multiset.prod_replicate #s b

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card {b : β} (hf : ∀ a ∈ s, f a = b) : ∏ a ∈ s, f a = b ^ #s :=
  (prod_congr rfl hf).trans <| prod_const _

@[to_additive card_nsmul_add_sum]
theorem pow_card_mul_prod {b : β} : b ^ #s * ∏ a ∈ s, f a = ∏ a ∈ s, b * f a :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive sum_add_card_nsmul]
theorem prod_mul_pow_card {b : β} : (∏ a ∈ s, f a) * b ^ #s = ∏ a ∈ s, f a * b :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive]
theorem pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏ _k ∈ range n, b := by simp

@[to_additive sum_nsmul_assoc]
lemma prod_pow_eq_pow_sum (s : Finset ι) (f : ι → ℕ) (a : β) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
  cons_induction (by simp) (fun _ _ _ _ ↦ by simp [prod_cons, sum_cons, pow_add, *]) s

@[to_additive]
theorem prod_flip {n : ℕ} (f : ℕ → β) :
    (∏ r ∈ range (n + 1), f (n - r)) = ∏ k ∈ range (n + 1), f k := by
  induction n with
  | zero => rw [prod_range_one, prod_range_one]
  | succ n ih =>
    rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]

/-- The difference with `Finset.prod_ninvolution` is that the involution is allowed to use
membership of the domain of the product, rather than being a non-dependent function. -/
@[to_additive "The difference with `Finset.sum_ninvolution` is that the involution is allowed to use
membership of the domain of the sum, rather than being a non-dependent function."]
lemma prod_involution (g : ∀ a ∈ s, α) (hg₁ : ∀ a ha, f a * f (g a ha) = 1)
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
    | inr hx' => rw [prod_pair hx'.symm, hg₁]
  suffices h₃ : ∀ a (ha : a ∈ s \ {x, g x hx}), g a (sdiff_subset ha) ∈ s \ {x, g x hx} from
    ih (s \ {x, g x hx}) (ssubset_iff.2 ⟨x, by simp [insert_subset_iff, hx]⟩) _
      (by simp [hg₁]) (fun _ _ => hg₃ _ _) h₃ (fun _ _ => hg₄ _ _)
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or, g_mem, true_and]
  rintro a ⟨ha₁, ha₂, ha₃⟩
  refine ⟨fun h => by simp [← h, hg₄] at ha₃, fun h => ?_⟩
  have : g (g a ha₁) (g_mem _ _) = g (g x hx) (g_mem _ _) := by simp only [h]
  exact ha₂ (by simpa [hg₄] using this)

/-- The difference with `Finset.prod_involution` is that the involution is a non-dependent function,
rather than being allowed to use membership of the domain of the product. -/
@[to_additive "The difference with `Finset.sum_involution` is that the involution is a non-dependent
function, rather than being allowed to use membership of the domain of the sum."]
lemma prod_ninvolution (g : α → α) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 :=
  prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `Finset.prod_image`. -/
@[to_additive "The sum of the composition of functions `f` and `g`, is the sum over `b ∈ s.image g`
of `f b` times of the cardinality of the fibre of `b`. See also `Finset.sum_image`."]
theorem prod_comp [DecidableEq γ] (f : γ → β) (g : α → γ) :
    ∏ a ∈ s, f (g a) = ∏ b ∈ s.image g, f b ^ #{a ∈ s | g a = b} := by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ ↦ mem_image_of_mem _]

@[to_additive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
    (∏ x ∈ s, (t.piecewise f g) x) = (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, g x := by
  simp only [piecewise]
  rw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

@[to_additive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by
  convert (s.prod_piecewise t f f).symm
  simp (config := { unfoldPartialApp := true }) [Finset.piecewise]

@[to_additive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  convert (s.prod_inter_mul_prod_diff {i} f).symm
  simp [h]

@[to_additive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_diff_singleton h, mul_comm]

@[to_additive]
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = f a * ∏ i ∈ {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[to_additive]
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = (∏ i ∈ {a}ᶜ, f i) * f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f

theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton ha]
    exact dvd_mul_right _ _

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
theorem prod_partition (R : Setoid α) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
theorem prod_cancels_of_partition_cancels (R : Setoid α) [DecidableRel R]
    (h : ∀ x ∈ s, ∏ a ∈ s with R a x, f a = 1) : ∏ x ∈ s, f x = 1 := by
  rw [prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

@[to_additive]
theorem prod_update_of_not_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∉ s) (f : α → β)
    (b : β) : ∏ x ∈ s, Function.update f i b x = ∏ x ∈ s, f x := by
  apply prod_congr rfl
  intros j hj
  have : j ≠ i := by
    rintro rfl
    exact h hj
  simp [this]

@[to_additive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
    ∏ x ∈ s, Function.update f i b x = b * ∏ x ∈ s \ singleton i, f x := by
  rw [update_eq_piecewise, prod_piecewise]
  simp [h]

/-- If a product of a `Finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq "If a sum of a `Finset` of size at most 1 has a given
value, so do the terms in that sum."]
theorem eq_of_card_le_one_of_prod_eq {s : Finset α} (hc : #s ≤ 1) {f : α → β} {b : β}
    (h : ∏ x ∈ s, f x = b) : ∀ x ∈ s, f x = b := by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    obtain ⟨x2, hx2⟩ := h1
    rw [hx2, mem_singleton] at hx
    simp_rw [hx2] at h
    rw [hx]
    rw [prod_singleton] at h
    exact h

/-- Taking a product over `s : Finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `Multiset.prod_map_erase` for the `Multiset` version. -/
@[to_additive "Taking a sum over `s : Finset α` is the same as adding the value on a single element
`f a` to the sum over `s.erase a`.

See `Multiset.sum_map_erase` for the `Multiset` version."]
theorem mul_prod_erase [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  rw [← prod_insert (not_mem_erase a s), insert_erase h]

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `Finset.add_sum_erase` with the addition swapped."]
theorem prod_erase_mul [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `Finset`. -/
@[to_additive "If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `Finset`."]
theorem prod_erase [DecidableEq α] (s : Finset α) {f : α → β} {a : α} (h : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine prod_subset sdiff_subset fun x hx hnx => ?_
  rw [sdiff_singleton_eq_erase] at hnx
  rwa [eq_of_mem_of_not_mem_erase hx hnx]

/-- See also `Finset.prod_ite_zero`. -/
@[to_additive "See also `Finset.sum_boole`."]
theorem prod_ite_one (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : β) :
    ∏ i ∈ s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hpi]
    exact fun j hj hji ↦ if_neg fun hpj ↦ hji <| h _ hj _ hi hpj hpi
  · push_neg at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive]
theorem prod_erase_lt_of_one_lt {γ : Type*} [DecidableEq α] [CommMonoid γ] [LT γ]
    [MulLeftStrictMono γ] {s : Finset α} {d : α} (hd : d ∈ s) {f : α → γ}
    (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by
  conv in ∏ m ∈ s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.not_mem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `Finset`. -/
@[to_additive "If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `Finset`."]
theorem eq_one_of_prod_eq_one {s : Finset α} {f : α → β} {a : α} (hp : ∏ x ∈ s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (not_mem_singleton.1 ha),
        prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive sum_boole_nsmul]
theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∏ x ∈ s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp

theorem prod_dvd_prod_of_dvd {S : Finset α} (g1 g2 : α → β) (h : ∀ a ∈ S, g1 a ∣ g2 a) :
    S.prod g1 ∣ S.prod g2 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a T haT IH =>
    rw [Finset.prod_cons, Finset.prod_cons]
    rw [Finset.forall_mem_cons] at h
    exact mul_dvd_mul h.1 <| IH h.2

@[to_additive]
lemma prod_mul_eq_prod_mul_of_exists {s : Finset α} {f : α → β} {b₁ b₂ : β}
    (a : α) (ha : a ∈ s) (h : f a * b₁ = f a * b₂) :
    (∏ a ∈ s, f a) * b₁ = (∏ a ∈ s, f a) * b₂ := by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc, mul_comm, mul_assoc, mul_comm b₁, h, ← mul_assoc, mul_comm _ (f a)]

@[to_additive]
lemma isSquare_prod {s : Finset ι} [CommMonoid α] (f : ι → α)
    (h : ∀ c ∈ s, IsSquare (f c)) : IsSquare (∏ i ∈ s, f i) := by
  rw [isSquare_iff_exists_sq]
  use (∏ (x : s), ((isSquare_iff_exists_sq _).mp (h _ x.2)).choose)
  rw [@sq, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort]
  congr
  ext i
  rw [← @sq]
  exact ((isSquare_iff_exists_sq _).mp (h _ i.2)).choose_spec

end CommMonoid

section CancelCommMonoid
variable [DecidableEq ι] [CancelCommMonoid α] {s t : Finset ι} {f : ι → α}

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

theorem card_eq_sum_ones (s : Finset α) : #s = ∑ _ ∈ s, 1 := by simp

theorem sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁

lemma sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι → κ) : ∑ j ∈ t, #{i ∈ s | g i = j} = #{i ∈ s | g i ∈ t} := by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

lemma card_filter (p) [DecidablePred p] (s : Finset ι) :
    #{i ∈ s | p i} = ∑ i ∈ s, ite (p i) 1 0 := by simp [sum_ite]

section CommGroup

variable [CommGroup β] [DecidableEq α]

@[to_additive (attr := simp)]
theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) :
    ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[to_additive]
theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

@[to_additive (attr := simp)]
theorem prod_erase_eq_div {a : α} (h : a ∈ s) :
    ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]

end CommGroup

@[simp]
theorem card_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    #(s.disjiUnion t h) = ∑ a ∈ s, #(t a) :=
  Multiset.card_bind _ _

theorem card_biUnion [DecidableEq β] {t : α → Finset β} (h : s.toSet.PairwiseDisjoint t) :
    #(s.biUnion t) = ∑ u ∈ s, #(t u) := by simpa using sum_biUnion h (β := ℕ) (f := 1)

theorem card_biUnion_le [DecidableEq β] {s : Finset α} {t : α → Finset β} :
    #(s.biUnion t) ≤ ∑ a ∈ s, #(t a) :=
  haveI := Classical.decEq α
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) ≤ #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ ≤ ∑ a ∈ insert a s, #(t a) := by rw [sum_insert has]; exact Nat.add_le_add_left ih _

theorem card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (H : s.toSet.MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b} := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

theorem card_eq_sum_card_image [DecidableEq β] (f : α → β) (s : Finset α) :
    #s = ∑ b ∈ s.image f, #{a ∈ s | f a = b} :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

theorem mem_sum {f : α → Multiset β} (s : Finset α) (b : β) :
    (b ∈ ∑ x ∈ s, f x) ↔ ∃ a ∈ s, b ∈ f a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hi ih => simp [sum_cons, ih, or_and_right, exists_or]

@[to_additive]
theorem prod_unique_nonempty {α β : Type*} [CommMonoid β] [Unique α] (s : Finset α) (f : α → β)
    (h : s.Nonempty) : ∏ x ∈ s, f x = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]

section Image_Overlap

variable {α β ι : Type*} [DecidableEq α]

@[to_additive]
lemma prod_filter_of_pairwise_eq_one [CommMonoid β] {f : ι → α} {g : α → β} {n : ι} {I : Finset ι}
    (hn : n ∈ I) (hf : (I : Set ι).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
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
"A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 0`.
The conclusion is the same as in `sum_image`."]
lemma prod_image_of_pairwise_eq_one [CommMonoid β] {f : ι → α} {g : α → β} {I : Finset ι}
    (hf : (I : Set ι).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 1`. The
conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
"A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 0`. The
conclusion is the same as in `sum_image`."
]
lemma prod_image_of_disjoint [CommMonoid β] [PartialOrder α] [OrderBot α] {f : ι → α} {g : α → β}
    (hg_bot : g ⊥ = 1) {I : Finset ι} (hf_disj : (I : Set ι).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  refine prod_image_of_pairwise_eq_one <| hf_disj.imp fun i j (hdisj : Disjoint _ _) hfij ↦ ?_
  rw [← hfij, disjoint_self] at hdisj
  rw [hdisj, hg_bot]

end Image_Overlap

end Finset

namespace Fintype
variable {ι κ α : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid α]

@[to_additive]
lemma prod_of_injective (e : ι → κ) (he : Injective e) (f : ι → α) (g : κ → α)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j :=
  prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ ↦ h i)

@[to_additive]
lemma prod_fiberwise [DecidableEq κ] (g : ι → κ) (f : ι → α) :
    ∏ j, ∏ i : {i // g i = j}, f i = ∏ i, f i := by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]
lemma prod_fiberwise' [DecidableEq κ] (g : ι → κ) (f : κ → α) :
    ∏ j, ∏ _i : {i // g i = j}, f j = ∏ i, f (g i) := by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ ↦ _).symm

@[to_additive]
theorem prod_unique {α β : Type*} [CommMonoid β] [Unique α] [Fintype α] (f : α → β) :
    ∏ x : α, f x = f default := by rw [univ_unique, prod_singleton]

@[to_additive]
theorem prod_subsingleton {α β : Type*} [CommMonoid β] [Subsingleton α] [Fintype α] (f : α → β)
    (a : α) : ∏ x : α, f x = f a := by
  have : Unique α := uniqueOfSubsingleton a
  rw [prod_unique f, Subsingleton.elim default a]

@[to_additive] theorem prod_Prop {β} [CommMonoid β] (f : Prop → β) :
    ∏ p, f p = f True * f False := by simp

@[to_additive]
theorem prod_subtype_mul_prod_subtype {α β : Type*} [Fintype α] [CommMonoid β] (p : α → Prop)
    (f : α → β) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]

@[to_additive] lemma prod_subset {s : Finset ι} {f : ι → α} (h : ∀ i, f i ≠ 1 → i ∈ s) :
    ∏ i ∈ s, f i = ∏ i, f i :=
  Finset.prod_subset s.subset_univ <| by simpa [not_imp_comm (a := _ ∈ s)]

@[to_additive]
lemma prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : α) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [prod_ite_one univ p (by simpa using h)]

variable [DecidableEq ι]

@[to_additive]
lemma prod_ite_mem (s : Finset ι) (f : ι → α) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  simp

/-- See also `Finset.prod_dite_eq`. -/
@[to_additive "See also `Finset.sum_dite_eq`."] lemma prod_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_dite_eq'`. -/
@[to_additive "See also `Finset.sum_dite_eq'`."] lemma prod_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    ∏ j, (if h : j = i then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq`. -/
@[to_additive "See also `Finset.sum_ite_eq`."]
lemma prod_ite_eq (i : ι) (f : ι → α) : ∏ j, (if i = j then f j else 1) = f i := by
  rw [Finset.prod_ite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq'`. -/
@[to_additive "See also `Finset.sum_ite_eq'`."]
lemma prod_ite_eq' (i : ι) (f : ι → α) : ∏ j, (if j = i then f j else 1) = f i := by
  rw [Finset.prod_ite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_pi_mulSingle`. -/
@[to_additive "See also `Finset.sum_pi_single`."]
lemma prod_pi_mulSingle {α : ι → Type*} [∀ i, CommMonoid (α i)] (i : ι) (f : ∀ i, α i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := prod_dite_eq _ _

/-- See also `Finset.prod_pi_mulSingle'`. -/
@[to_additive "See also `Finset.sum_pi_single'`."]
lemma prod_pi_mulSingle' (i : ι) (a : α) : ∏ j, Pi.mulSingle i a j = a := prod_dite_eq' _ _

end CommMonoid
end Fintype

namespace List

@[to_additive]
theorem prod_toFinset {M : Type*} [DecidableEq α] [CommMonoid M] (f : α → M) :
    ∀ {l : List α} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨not_mem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp not_mem), prod_toFinset _ hl]

@[simp]
theorem sum_toFinset_count_eq_length [DecidableEq α] (l : List α) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : ℕ)).symm

end List

namespace Multiset

@[simp]
lemma mem_sum {s : Finset ι} {m : ι → Multiset α} : a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  induction s using Finset.cons_induction <;> simp [*]

variable [DecidableEq α]

theorem toFinset_sum_count_eq (s : Multiset α) : ∑ a ∈ s.toFinset, s.count a = card s := by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : ℕ))).symm

@[simp] lemma sum_count_eq_card {s : Finset α} {m : Multiset α} (hms : ∀ a ∈ m, a ∈ s) :
    ∑ a ∈ s, m.count a = card m := by
  rw [← toFinset_sum_count_eq, ← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[simp]
theorem toFinset_sum_count_nsmul_eq (s : Multiset α) :
    ∑ a ∈ s.toFinset, s.count a • {a} = s := by
  rw [← Finset.sum_multiset_map_count, Multiset.sum_map_singleton]

theorem exists_smul_of_dvd_count (s : Multiset α) {k : ℕ}
    (h : ∀ a : α, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset α, s = k • u := by
  use ∑ a ∈ s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x ∈ s.toFinset, k • (count x s / k) • ({x} : Multiset α)) =
      ∑ x ∈ s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, toFinset_sum_count_nsmul_eq]

@[to_additive]
theorem prod_sum {α : Type*} {ι : Type*} [CommMonoid α] (f : ι → Multiset α) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, Multiset.prod_zero]
  | cons a s has ih => rw [Finset.sum_cons, Finset.prod_cons, Multiset.prod_add, ih]

end Multiset

@[to_additive (attr := simp)]
lemma IsUnit.prod_iff [CommMonoid β] : IsUnit (∏ a ∈ s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha hs => rw [Finset.prod_cons, IsUnit.mul_iff, hs, Finset.forall_mem_cons]

@[to_additive]
lemma IsUnit.prod_univ_iff [Fintype α] [CommMonoid β] : IsUnit (∏ a, f a) ↔ ∀ a, IsUnit (f a) := by
  simp

theorem nat_abs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, Int.natAbs_zero, le_refl]
  | cons i s his IH =>
    simp only [Finset.sum_cons, not_false_iff]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left IH _)

set_option linter.style.longFile 1600
