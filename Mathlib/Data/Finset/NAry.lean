/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite

#align_import data.finset.n_ary from "leanprover-community/mathlib"@"eba7871095e834365616b5e43c8c7bb0b37058d0"

/-!
# N-ary images of finsets

This file defines `Finset.image₂`, the binary image of finsets. This is the finset version of
`Set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to `Data.Set.NAry`, `Order.Filter.NAry` and `Data.Option.NAry`. Please
keep them in sync.

We do not define `Finset.image₃` as its only purpose would be to prove properties of `Finset.image₂`
and `Set.image2` already fulfills this task.
-/


open Function Set

variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*}

namespace Finset

variable [DecidableEq α'] [DecidableEq β'] [DecidableEq γ] [DecidableEq γ'] [DecidableEq δ]
  [DecidableEq δ'] [DecidableEq ε] [DecidableEq ε'] {f f' : α → β → γ} {g g' : α → β → γ → δ}
  {s s' : Finset α} {t t' : Finset β} {u u' : Finset γ} {a a' : α} {b b' : β} {c : γ}

/-- The image of a binary function `f : α → β → γ` as a function `Finset α → Finset β → Finset γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) : Finset γ :=
  (s ×ˢ t).image <| uncurry f
#align finset.image₂ Finset.image₂

@[simp]
theorem mem_image₂ : c ∈ image₂ f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c := by
  simp [image₂, and_assoc]
  -- 🎉 no goals
#align finset.mem_image₂ Finset.mem_image₂

@[simp, norm_cast]
theorem coe_image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (image₂ f s t : Set γ) = Set.image2 f s t :=
  Set.ext fun _ => mem_image₂
#align finset.coe_image₂ Finset.coe_image₂

theorem card_image₂_le (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (image₂ f s t).card ≤ s.card * t.card :=
  card_image_le.trans_eq <| card_product _ _
#align finset.card_image₂_le Finset.card_image₂_le

theorem card_image₂_iff :
    (image₂ f s t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2 := by
  rw [← card_product, ← coe_product]
  -- ⊢ card (image₂ f s t) = card (s ×ˢ t) ↔ InjOn (fun x => f x.fst x.snd) ↑(s ×ˢ t)
  exact card_image_iff
  -- 🎉 no goals
#align finset.card_image₂_iff Finset.card_image₂_iff

theorem card_image₂ (hf : Injective2 f) (s : Finset α) (t : Finset β) :
    (image₂ f s t).card = s.card * t.card :=
  (card_image_of_injective _ hf.uncurry).trans <| card_product _ _
#align finset.card_image₂ Finset.card_image₂

theorem mem_image₂_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image₂ f s t :=
  mem_image₂.2 ⟨a, b, ha, hb, rfl⟩
#align finset.mem_image₂_of_mem Finset.mem_image₂_of_mem

theorem mem_image₂_iff (hf : Injective2 f) : f a b ∈ image₂ f s t ↔ a ∈ s ∧ b ∈ t := by
  rw [← mem_coe, coe_image₂, mem_image2_iff hf, mem_coe, mem_coe]
  -- 🎉 no goals
#align finset.mem_image₂_iff Finset.mem_image₂_iff

theorem image₂_subset (hs : s ⊆ s') (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s' t' := by
  rw [← coe_subset, coe_image₂, coe_image₂]
  -- ⊢ image2 f ↑s ↑t ⊆ image2 f ↑s' ↑t'
  exact image2_subset hs ht
  -- 🎉 no goals
#align finset.image₂_subset Finset.image₂_subset

theorem image₂_subset_left (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s t' :=
  image₂_subset Subset.rfl ht
#align finset.image₂_subset_left Finset.image₂_subset_left

theorem image₂_subset_right (hs : s ⊆ s') : image₂ f s t ⊆ image₂ f s' t :=
  image₂_subset hs Subset.rfl
#align finset.image₂_subset_right Finset.image₂_subset_right

theorem image_subset_image₂_left (hb : b ∈ t) : s.image (fun a => f a b) ⊆ image₂ f s t :=
  image_subset_iff.2 fun _ ha => mem_image₂_of_mem ha hb
#align finset.image_subset_image₂_left Finset.image_subset_image₂_left

theorem image_subset_image₂_right (ha : a ∈ s) : t.image (fun b => f a b) ⊆ image₂ f s t :=
  image_subset_iff.2 fun _ => mem_image₂_of_mem ha
#align finset.image_subset_image₂_right Finset.image_subset_image₂_right

theorem forall_image₂_iff {p : γ → Prop} :
    (∀ z ∈ image₂ f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, forall_image2_iff]
  -- 🎉 no goals
#align finset.forall_image₂_iff Finset.forall_image₂_iff

@[simp]
theorem image₂_subset_iff : image₂ f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_image₂_iff
#align finset.image₂_subset_iff Finset.image₂_subset_iff

theorem image₂_subset_iff_left : image₂ f s t ⊆ u ↔ ∀ a ∈ s, (t.image fun b => f a b) ⊆ u := by
  simp_rw [image₂_subset_iff, image_subset_iff]
  -- 🎉 no goals
#align finset.image₂_subset_iff_left Finset.image₂_subset_iff_left

theorem image₂_subset_iff_right : image₂ f s t ⊆ u ↔ ∀ b ∈ t, (s.image fun a => f a b) ⊆ u := by
  simp_rw [image₂_subset_iff, image_subset_iff, @forall₂_swap α]
  -- 🎉 no goals
#align finset.image₂_subset_iff_right Finset.image₂_subset_iff_right

@[simp]
theorem image₂_nonempty_iff : (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  rw [← coe_nonempty, coe_image₂]
  -- ⊢ Set.Nonempty (image2 f ↑s ↑t) ↔ Finset.Nonempty s ∧ Finset.Nonempty t
  exact image2_nonempty_iff
  -- 🎉 no goals
#align finset.image₂_nonempty_iff Finset.image₂_nonempty_iff

theorem Nonempty.image₂ (hs : s.Nonempty) (ht : t.Nonempty) : (image₂ f s t).Nonempty :=
  image₂_nonempty_iff.2 ⟨hs, ht⟩
#align finset.nonempty.image₂ Finset.Nonempty.image₂

theorem Nonempty.of_image₂_left (h : (s.image₂ f t).Nonempty) : s.Nonempty :=
  (image₂_nonempty_iff.1 h).1
#align finset.nonempty.of_image₂_left Finset.Nonempty.of_image₂_left

theorem Nonempty.of_image₂_right (h : (s.image₂ f t).Nonempty) : t.Nonempty :=
  (image₂_nonempty_iff.1 h).2
#align finset.nonempty.of_image₂_right Finset.Nonempty.of_image₂_right

@[simp]
theorem image₂_empty_left : image₂ f ∅ t = ∅ :=
  coe_injective <| by simp
                      -- 🎉 no goals
#align finset.image₂_empty_left Finset.image₂_empty_left

@[simp]
theorem image₂_empty_right : image₂ f s ∅ = ∅ :=
  coe_injective <| by simp
                      -- 🎉 no goals
#align finset.image₂_empty_right Finset.image₂_empty_right

@[simp]
theorem image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp_rw [← not_nonempty_iff_eq_empty, image₂_nonempty_iff, not_and_or]
  -- 🎉 no goals
#align finset.image₂_eq_empty_iff Finset.image₂_eq_empty_iff

@[simp]
theorem image₂_singleton_left : image₂ f {a} t = t.image fun b => f a b :=
  ext fun x => by simp
                  -- 🎉 no goals
#align finset.image₂_singleton_left Finset.image₂_singleton_left

@[simp]
theorem image₂_singleton_right : image₂ f s {b} = s.image fun a => f a b :=
  ext fun x => by simp
                  -- 🎉 no goals
#align finset.image₂_singleton_right Finset.image₂_singleton_right

theorem image₂_singleton_left' : image₂ f {a} t = t.image (f a) :=
  image₂_singleton_left
#align finset.image₂_singleton_left' Finset.image₂_singleton_left'

theorem image₂_singleton : image₂ f {a} {b} = {f a b} := by simp
                                                            -- 🎉 no goals
#align finset.image₂_singleton Finset.image₂_singleton

theorem image₂_union_left [DecidableEq α] : image₂ f (s ∪ s') t = image₂ f s t ∪ image₂ f s' t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s ∪ ↑s') ↑t = image2 f ↑s ↑t ∪ image2 f ↑s' ↑t
    exact image2_union_left
    -- 🎉 no goals
#align finset.image₂_union_left Finset.image₂_union_left

theorem image₂_union_right [DecidableEq β] : image₂ f s (t ∪ t') = image₂ f s t ∪ image₂ f s t' :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s) (↑t ∪ ↑t') = image2 f ↑s ↑t ∪ image2 f ↑s ↑t'
    exact image2_union_right
    -- 🎉 no goals
#align finset.image₂_union_right Finset.image₂_union_right

@[simp]
theorem image₂_insert_left [DecidableEq α] :
    image₂ f (insert a s) t = (t.image fun b => f a b) ∪ image₂ f s t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (insert a ↑s) ↑t = (fun b => f a b) '' ↑t ∪ image2 f ↑s ↑t
    exact image2_insert_left
    -- 🎉 no goals
#align finset.image₂_insert_left Finset.image₂_insert_left

@[simp]
theorem image₂_insert_right [DecidableEq β] :
    image₂ f s (insert b t) = (s.image fun a => f a b) ∪ image₂ f s t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s) (insert b ↑t) = (fun a => f a b) '' ↑s ∪ image2 f ↑s ↑t
    exact image2_insert_right
    -- 🎉 no goals
#align finset.image₂_insert_right Finset.image₂_insert_right

theorem image₂_inter_left [DecidableEq α] (hf : Injective2 f) :
    image₂ f (s ∩ s') t = image₂ f s t ∩ image₂ f s' t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s ∩ ↑s') ↑t = image2 f ↑s ↑t ∩ image2 f ↑s' ↑t
    exact image2_inter_left hf
    -- 🎉 no goals
#align finset.image₂_inter_left Finset.image₂_inter_left

theorem image₂_inter_right [DecidableEq β] (hf : Injective2 f) :
    image₂ f s (t ∩ t') = image₂ f s t ∩ image₂ f s t' :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s) (↑t ∩ ↑t') = image2 f ↑s ↑t ∩ image2 f ↑s ↑t'
    exact image2_inter_right hf
    -- 🎉 no goals
#align finset.image₂_inter_right Finset.image₂_inter_right

theorem image₂_inter_subset_left [DecidableEq α] :
    image₂ f (s ∩ s') t ⊆ image₂ f s t ∩ image₂ f s' t :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s ∩ ↑s') ↑t ⊆ image2 f ↑s ↑t ∩ image2 f ↑s' ↑t
    exact image2_inter_subset_left
    -- 🎉 no goals
#align finset.image₂_inter_subset_left Finset.image₂_inter_subset_left

theorem image₂_inter_subset_right [DecidableEq β] :
    image₂ f s (t ∩ t') ⊆ image₂ f s t ∩ image₂ f s t' :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s) (↑t ∩ ↑t') ⊆ image2 f ↑s ↑t ∩ image2 f ↑s ↑t'
    exact image2_inter_subset_right
    -- 🎉 no goals
#align finset.image₂_inter_subset_right Finset.image₂_inter_subset_right

theorem image₂_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f ↑s ↑t = image2 f' ↑s ↑t
    exact image2_congr h
    -- 🎉 no goals
#align finset.image₂_congr Finset.image₂_congr

/-- A common special case of `image₂_congr` -/
theorem image₂_congr' (h : ∀ a b, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  image₂_congr fun a _ b _ => h a b
#align finset.image₂_congr' Finset.image₂_congr'

theorem subset_image₂ {s : Set α} {t : Set β} (hu : ↑u ⊆ image2 f s t) :
    ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ image₂ f s' t' := by
  apply @Finset.induction_on' γ _ _ u
  -- ⊢ ∃ s' t', ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ ∅ ⊆ image₂ f s' t'
  · use ∅; use ∅; simp only [coe_empty];
    -- ⊢ ∃ t', ↑∅ ⊆ s ∧ ↑t' ⊆ t ∧ ∅ ⊆ image₂ f ∅ t'
           -- ⊢ ↑∅ ⊆ s ∧ ↑∅ ⊆ t ∧ ∅ ⊆ image₂ f ∅ ∅
                  -- ⊢ ∅ ⊆ s ∧ ∅ ⊆ t ∧ ∅ ⊆ image₂ f ∅ ∅
    exact ⟨Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
    -- 🎉 no goals
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  -- ⊢ ∃ s' t', ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ insert a u ⊆ image₂ f s' t'
  obtain ⟨x, y, hx, hy, ha⟩ := hu ha
  -- ⊢ ∃ s' t', ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ insert a u ⊆ image₂ f s' t'
  haveI := Classical.decEq α
  -- ⊢ ∃ s' t', ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ insert a u ⊆ image₂ f s' t'
  haveI := Classical.decEq β
  -- ⊢ ∃ s' t', ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ insert a u ⊆ image₂ f s' t'
  refine' ⟨insert x s', insert y t', _⟩
  -- ⊢ ↑(insert x s') ⊆ s ∧ ↑(insert y t') ⊆ t ∧ insert a u ⊆ image₂ f (insert x s' …
  simp_rw [coe_insert, Set.insert_subset_iff]
  -- ⊢ (x ∈ s ∧ ↑s' ⊆ s) ∧ (y ∈ t ∧ ↑t' ⊆ t) ∧ insert a u ⊆ image₂ f (insert x s')  …
  exact
    ⟨⟨hx, hs⟩, ⟨hy, hs'⟩,
      insert_subset_iff.2
        ⟨mem_image₂.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩,
          h.trans <| image₂_subset (subset_insert _ _) <| subset_insert _ _⟩⟩
#align finset.subset_image₂ Finset.subset_image₂

variable (s t)

theorem card_image₂_singleton_left (hf : Injective (f a)) : (image₂ f {a} t).card = t.card := by
  rw [image₂_singleton_left, card_image_of_injective _ hf]
  -- 🎉 no goals
#align finset.card_image₂_singleton_left Finset.card_image₂_singleton_left

theorem card_image₂_singleton_right (hf : Injective fun a => f a b) :
    (image₂ f s {b}).card = s.card := by rw [image₂_singleton_right, card_image_of_injective _ hf]
                                         -- 🎉 no goals
#align finset.card_image₂_singleton_right Finset.card_image₂_singleton_right

theorem image₂_singleton_inter [DecidableEq β] (t₁ t₂ : Finset β) (hf : Injective (f a)) :
    image₂ f {a} (t₁ ∩ t₂) = image₂ f {a} t₁ ∩ image₂ f {a} t₂ := by
  simp_rw [image₂_singleton_left, image_inter _ _ hf]
  -- 🎉 no goals
#align finset.image₂_singleton_inter Finset.image₂_singleton_inter

theorem image₂_inter_singleton [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective fun a => f a b) :
    image₂ f (s₁ ∩ s₂) {b} = image₂ f s₁ {b} ∩ image₂ f s₂ {b} := by
  simp_rw [image₂_singleton_right, image_inter _ _ hf]
  -- 🎉 no goals
#align finset.image₂_inter_singleton Finset.image₂_inter_singleton

theorem card_le_card_image₂_left {s : Finset α} (hs : s.Nonempty) (hf : ∀ a, Injective (f a)) :
    t.card ≤ (image₂ f s t).card := by
  obtain ⟨a, ha⟩ := hs
  -- ⊢ card t ≤ card (image₂ f s t)
  rw [← card_image₂_singleton_left _ (hf a)]
  -- ⊢ card (image₂ f {a} t) ≤ card (image₂ f s t)
  exact card_le_of_subset (image₂_subset_right <| singleton_subset_iff.2 ha)
  -- 🎉 no goals
#align finset.card_le_card_image₂_left Finset.card_le_card_image₂_left

theorem card_le_card_image₂_right {t : Finset β} (ht : t.Nonempty)
    (hf : ∀ b, Injective fun a => f a b) : s.card ≤ (image₂ f s t).card := by
  obtain ⟨b, hb⟩ := ht
  -- ⊢ card s ≤ card (image₂ f s t)
  rw [← card_image₂_singleton_right _ (hf b)]
  -- ⊢ card (image₂ (fun a => f a) s {b}) ≤ card (image₂ f s t)
  exact card_le_of_subset (image₂_subset_left <| singleton_subset_iff.2 hb)
  -- 🎉 no goals
#align finset.card_le_card_image₂_right Finset.card_le_card_image₂_right

variable {s t}

theorem biUnion_image_left : (s.biUnion fun a => t.image <| f a) = image₂ f s t :=
  coe_injective <| by
    push_cast
    -- ⊢ ⋃ (x : α) (_ : x ∈ ↑s), f x '' ↑t = image2 f ↑s ↑t
    exact Set.iUnion_image_left _
    -- 🎉 no goals
#align finset.bUnion_image_left Finset.biUnion_image_left

theorem biUnion_image_right : (t.biUnion fun b => s.image fun a => f a b) = image₂ f s t :=
  coe_injective <| by
    push_cast
    -- ⊢ ⋃ (x : β) (_ : x ∈ ↑t), (fun a => f a x) '' ↑s = image2 f ↑s ↑t
    exact Set.iUnion_image_right _
    -- 🎉 no goals
#align finset.bUnion_image_right Finset.biUnion_image_right

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Finset.image₂` of those operations.

The proof pattern is `image₂_lemma operation_lemma`. For example, `image₂_comm mul_comm` proves that
`image₂ (*) f g = image₂ (*) g f` in a `CommSemigroup`.
-/

theorem image_image₂ (f : α → β → γ) (g : γ → δ) :
    (image₂ f s t).image g = image₂ (fun a b => g (f a b)) s t :=
  coe_injective <| by
    push_cast
    -- ⊢ g '' image2 f ↑s ↑t = image2 (fun a b => g (f a b)) ↑s ↑t
    exact image_image2 _ _
    -- 🎉 no goals
#align finset.image_image₂ Finset.image_image₂

theorem image₂_image_left (f : γ → β → δ) (g : α → γ) :
    image₂ f (s.image g) t = image₂ (fun a b => f (g a) b) s t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (g '' ↑s) ↑t = image2 (fun a b => f (g a) b) ↑s ↑t
    exact image2_image_left _ _
    -- 🎉 no goals
#align finset.image₂_image_left Finset.image₂_image_left

theorem image₂_image_right (f : α → γ → δ) (g : β → γ) :
    image₂ f s (t.image g) = image₂ (fun a b => f a (g b)) s t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s) (g '' ↑t) = image2 (fun a b => f a (g b)) ↑s ↑t
    exact image2_image_right _ _
    -- 🎉 no goals
#align finset.image₂_image_right Finset.image₂_image_right

@[simp]
theorem image₂_mk_eq_product [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    image₂ Prod.mk s t = s ×ˢ t := by ext; simp [Prod.ext_iff]
                                      -- ⊢ a✝ ∈ image₂ Prod.mk s t ↔ a✝ ∈ s ×ˢ t
                                           -- 🎉 no goals
#align finset.image₂_mk_eq_product Finset.image₂_mk_eq_product

@[simp]
theorem image₂_curry (f : α × β → γ) (s : Finset α) (t : Finset β) :
    image₂ (curry f) s t = (s ×ˢ t).image f := by
  classical rw [← image₂_mk_eq_product, image_image₂]; dsimp [curry]
  -- 🎉 no goals
#align finset.image₂_curry Finset.image₂_curry

@[simp]
theorem image_uncurry_product (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (s ×ˢ t).image (uncurry f) = image₂ f s t := by rw [← image₂_curry, curry_uncurry]
                                                    -- 🎉 no goals
#align finset.image_uncurry_product Finset.image_uncurry_product

theorem image₂_swap (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = image₂ (fun a b => f b a) t s :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f ↑s ↑t = image2 (fun a b => f b a) ↑t ↑s
    exact image2_swap _ _ _
    -- 🎉 no goals
#align finset.image₂_swap Finset.image₂_swap

@[simp]
theorem image₂_left [DecidableEq α] (h : t.Nonempty) : image₂ (fun x _ => x) s t = s :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 (fun x x_1 => x) ↑s ↑t = ↑s
    exact image2_left h
    -- 🎉 no goals
#align finset.image₂_left Finset.image₂_left

@[simp]
theorem image₂_right [DecidableEq β] (h : s.Nonempty) : image₂ (fun _ y => y) s t = t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 (fun x y => y) ↑s ↑t = ↑t
    exact image2_right h
    -- 🎉 no goals
#align finset.image₂_right Finset.image₂_right

theorem image₂_assoc {γ : Type*} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε}
    {g' : β → γ → ε'} (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image₂ f (image₂ g s t) u = image₂ f' s (image₂ g' t u) :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (image2 g ↑s ↑t) ↑u = image2 f' (↑s) (image2 g' ↑t ↑u)
    exact image2_assoc h_assoc
    -- 🎉 no goals
#align finset.image₂_assoc Finset.image₂_assoc

theorem image₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image₂ f s t = image₂ g t s :=
  (image₂_swap _ _ _).trans <| by simp_rw [h_comm]
                                  -- 🎉 no goals
#align finset.image₂_comm Finset.image₂_comm

theorem image₂_left_comm {γ : Type*} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ}
    {f' : α → γ → δ'} {g' : β → δ' → ε} (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image₂ f s (image₂ g t u) = image₂ g' t (image₂ f' s u) :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (↑s) (image2 g ↑t ↑u) = image2 g' (↑t) (image2 f' ↑s ↑u)
    exact image2_left_comm h_left_comm
    -- 🎉 no goals
#align finset.image₂_left_comm Finset.image₂_left_comm

theorem image₂_right_comm {γ : Type*} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ}
    {f' : α → γ → δ'} {g' : δ' → β → ε} (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image₂ f (image₂ g s t) u = image₂ g' (image₂ f' s u) t :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (image2 g ↑s ↑t) ↑u = image2 g' (image2 f' ↑s ↑u) ↑t
    exact image2_right_comm h_right_comm
    -- 🎉 no goals
#align finset.image₂_right_comm Finset.image₂_right_comm

theorem image₂_image₂_image₂_comm {γ δ : Type*} {u : Finset γ} {v : Finset δ} [DecidableEq ζ]
    [DecidableEq ζ'] [DecidableEq ν] {f : ε → ζ → ν} {g : α → β → ε} {h : γ → δ → ζ}
    {f' : ε' → ζ' → ν} {g' : α → γ → ε'} {h' : β → δ → ζ'}
    (h_comm : ∀ a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image₂ f (image₂ g s t) (image₂ h u v) = image₂ f' (image₂ g' s u) (image₂ h' t v) :=
  coe_injective <| by
    push_cast
    -- ⊢ image2 f (image2 g ↑s ↑t) (image2 h ↑u ↑v) = image2 f' (image2 g' ↑s ↑u) (im …
    exact image2_image2_image2_comm h_comm
    -- 🎉 no goals
#align finset.image₂_image₂_image₂_comm Finset.image₂_image₂_image₂_comm

theorem image_image₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image₂ f s t).image g = image₂ f' (s.image g₁) (t.image g₂) :=
  coe_injective <| by
    push_cast
    -- ⊢ g '' image2 f ↑s ↑t = image2 f' (g₁ '' ↑s) (g₂ '' ↑t)
    exact image_image2_distrib h_distrib
    -- 🎉 no goals
#align finset.image_image₂_distrib Finset.image_image₂_distrib

/-- Symmetric statement to `Finset.image₂_image_left_comm`. -/
theorem image_image₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image₂ f s t).image g = image₂ f' (s.image g') t :=
  coe_injective <| by
    push_cast
    -- ⊢ g '' image2 f ↑s ↑t = image2 f' (g' '' ↑s) ↑t
    exact image_image2_distrib_left h_distrib
    -- 🎉 no goals
#align finset.image_image₂_distrib_left Finset.image_image₂_distrib_left

/-- Symmetric statement to `Finset.image_image₂_right_comm`. -/
theorem image_image₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image₂ f s t).image g = image₂ f' s (t.image g') :=
  coe_injective <| by
    push_cast
    -- ⊢ g '' image2 f ↑s ↑t = image2 f' (↑s) (g' '' ↑t)
    exact image_image2_distrib_right h_distrib
    -- 🎉 no goals
#align finset.image_image₂_distrib_right Finset.image_image₂_distrib_right

/-- Symmetric statement to `Finset.image_image₂_distrib_left`. -/
theorem image₂_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image₂ f (s.image g) t = (image₂ f' s t).image g' :=
  (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm
#align finset.image₂_image_left_comm Finset.image₂_image_left_comm

/-- Symmetric statement to `Finset.image_image₂_distrib_right`. -/
theorem image_image₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image₂ f s (t.image g) = (image₂ f' s t).image g' :=
  (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm
#align finset.image_image₂_right_comm Finset.image_image₂_right_comm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image₂_distrib_subset_left {γ : Type*} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ}
    {f₁ : α → β → β'} {f₂ : α → γ → γ'} {g' : β' → γ' → ε}
    (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image₂ f s (image₂ g t u) ⊆ image₂ g' (image₂ f₁ s t) (image₂ f₂ s u) :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s) (image2 g ↑t ↑u) ⊆ image2 g' (image2 f₁ ↑s ↑t) (image2 f₂ ↑s ↑u)
    exact Set.image2_distrib_subset_left h_distrib
    -- 🎉 no goals
#align finset.image₂_distrib_subset_left Finset.image₂_distrib_subset_left

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image₂_distrib_subset_right {γ : Type*} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ}
    {f₁ : α → γ → α'} {f₂ : β → γ → β'} {g' : α' → β' → ε}
    (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image₂ f (image₂ g s t) u ⊆ image₂ g' (image₂ f₁ s u) (image₂ f₂ t u) :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (image2 g ↑s ↑t) ↑u ⊆ image2 g' (image2 f₁ ↑s ↑u) (image2 f₂ ↑t ↑u)
    exact Set.image2_distrib_subset_right h_distrib
    -- 🎉 no goals
#align finset.image₂_distrib_subset_right Finset.image₂_distrib_subset_right

theorem image_image₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image₂ f s t).image g = image₂ f' (t.image g₁) (s.image g₂) := by
  rw [image₂_swap f]
  -- ⊢ image g (image₂ (fun a b => f b a) t s) = image₂ f' (image g₁ t) (image g₂ s)
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _
  -- 🎉 no goals
#align finset.image_image₂_antidistrib Finset.image_image₂_antidistrib

/-- Symmetric statement to `Finset.image₂_image_left_anticomm`. -/
theorem image_image₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image₂ f s t).image g = image₂ f' (t.image g') s :=
  coe_injective <| by
    push_cast
    -- ⊢ g '' image2 f ↑s ↑t = image2 f' (g' '' ↑t) ↑s
    exact image_image2_antidistrib_left h_antidistrib
    -- 🎉 no goals
#align finset.image_image₂_antidistrib_left Finset.image_image₂_antidistrib_left

/-- Symmetric statement to `Finset.image_image₂_right_anticomm`. -/
theorem image_image₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image₂ f s t).image g = image₂ f' t (s.image g') :=
  coe_injective <| by
    push_cast
    -- ⊢ g '' image2 f ↑s ↑t = image2 f' (↑t) (g' '' ↑s)
    exact image_image2_antidistrib_right h_antidistrib
    -- 🎉 no goals
#align finset.image_image₂_antidistrib_right Finset.image_image₂_antidistrib_right

/-- Symmetric statement to `Finset.image_image₂_antidistrib_left`. -/
theorem image₂_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image₂ f (s.image g) t = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm
#align finset.image₂_image_left_anticomm Finset.image₂_image_left_anticomm

/-- Symmetric statement to `Finset.image_image₂_antidistrib_right`. -/
theorem image_image₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image₂ f s (t.image g) = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm
#align finset.image_image₂_right_anticomm Finset.image_image₂_right_anticomm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`Finset.image₂ f`. -/
theorem image₂_left_identity {f : α → γ → γ} {a : α} (h : ∀ b, f a b = b) (t : Finset γ) :
    image₂ f {a} t = t :=
  coe_injective <| by rw [coe_image₂, coe_singleton, Set.image2_left_identity h]
                      -- 🎉 no goals
#align finset.image₂_left_identity Finset.image₂_left_identity

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`Finset.image₂ f`. -/
theorem image₂_right_identity {f : γ → β → γ} {b : β} (h : ∀ a, f a b = a) (s : Finset γ) :
    image₂ f s {b} = s := by rw [image₂_singleton_right, funext h, image_id']
                             -- 🎉 no goals
#align finset.image₂_right_identity Finset.image₂_right_identity

/-- If each partial application of `f` is injective, and images of `s` under those partial
applications are disjoint (but not necessarily distinct!), then the size of `t` divides the size of
`finset.image₂ f s t`. -/
theorem card_dvd_card_image₂_right (hf : ∀ a ∈ s, Injective (f a))
    (hs : ((fun a => t.image <| f a) '' s).PairwiseDisjoint id) : t.card ∣ (image₂ f s t).card := by
  classical
  induction' s using Finset.induction with a s _ ih
  · simp
  specialize ih (forall_of_forall_insert hf)
    (hs.subset <| Set.image_subset _ <| coe_subset.2 <| subset_insert _ _)
  rw [image₂_insert_left]
  by_cases h : Disjoint (image (f a) t) (image₂ f s t)
  · rw [card_union_eq h]
    exact (card_image_of_injective _ <| hf _ <| mem_insert_self _ _).symm.dvd.add ih
  simp_rw [← biUnion_image_left, disjoint_biUnion_right, not_forall] at h
  obtain ⟨b, hb, h⟩ := h
  rwa [union_eq_right_iff_subset.2]
  exact (hs.eq (Set.mem_image_of_mem _ <| mem_insert_self _ _)
      (Set.mem_image_of_mem _ <| mem_insert_of_mem hb) h).trans_subset
    (image_subset_image₂_right hb)
#align finset.card_dvd_card_image₂_right Finset.card_dvd_card_image₂_right

/-- If each partial application of `f` is injective, and images of `t` under those partial
applications are disjoint (but not necessarily distinct!), then the size of `s` divides the size of
`finset.image₂ f s t`. -/
theorem card_dvd_card_image₂_left (hf : ∀ b ∈ t, Injective fun a => f a b)
    (ht : ((fun b => s.image fun a => f a b) '' t).PairwiseDisjoint id) :
    s.card ∣ (image₂ f s t).card := by rw [← image₂_swap]; exact card_dvd_card_image₂_right hf ht
                                       -- ⊢ card s ∣ card (image₂ (fun b a => f a b) t s)
                                                           -- 🎉 no goals
#align finset.card_dvd_card_image₂_left Finset.card_dvd_card_image₂_left

variable [DecidableEq α] [DecidableEq β]

theorem image₂_inter_union_subset_union :
    image₂ f (s ∩ s') (t ∪ t') ⊆ image₂ f s t ∪ image₂ f s' t' :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s ∩ ↑s') (↑t ∪ ↑t') ⊆ image2 f ↑s ↑t ∪ image2 f ↑s' ↑t'
    exact Set.image2_inter_union_subset_union
    -- 🎉 no goals
#align finset.image₂_inter_union_subset_union Finset.image₂_inter_union_subset_union

theorem image₂_union_inter_subset_union :
    image₂ f (s ∪ s') (t ∩ t') ⊆ image₂ f s t ∪ image₂ f s' t' :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s ∪ ↑s') (↑t ∩ ↑t') ⊆ image2 f ↑s ↑t ∪ image2 f ↑s' ↑t'
    exact Set.image2_union_inter_subset_union
    -- 🎉 no goals
#align finset.image₂_union_inter_subset_union Finset.image₂_union_inter_subset_union

theorem image₂_inter_union_subset {f : α → α → β} {s t : Finset α} (hf : ∀ a b, f a b = f b a) :
    image₂ f (s ∩ t) (s ∪ t) ⊆ image₂ f s t :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s ∩ ↑t) (↑s ∪ ↑t) ⊆ image2 f ↑s ↑t
    exact image2_inter_union_subset hf
    -- 🎉 no goals
#align finset.image₂_inter_union_subset Finset.image₂_inter_union_subset

theorem image₂_union_inter_subset {f : α → α → β} {s t : Finset α} (hf : ∀ a b, f a b = f b a) :
    image₂ f (s ∪ t) (s ∩ t) ⊆ image₂ f s t :=
  coe_subset.1 <| by
    push_cast
    -- ⊢ image2 f (↑s ∪ ↑t) (↑s ∩ ↑t) ⊆ image2 f ↑s ↑t
    exact image2_union_inter_subset hf
    -- 🎉 no goals
#align finset.image₂_union_inter_subset Finset.image₂_union_inter_subset

end Finset

namespace Set

variable [DecidableEq γ] {s : Set α} {t : Set β}

@[simp]
theorem toFinset_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Fintype s] [Fintype t]
    [Fintype (image2 f s t)] : (image2 f s t).toFinset = Finset.image₂ f s.toFinset t.toFinset :=
  Finset.coe_injective <| by simp
                             -- 🎉 no goals
#align set.to_finset_image2 Set.toFinset_image2

theorem Finite.toFinset_image2 (f : α → β → γ) (hs : s.Finite) (ht : t.Finite)
    (hf := hs.image2 f ht) : hf.toFinset = Finset.image₂ f hs.toFinset ht.toFinset :=
  Finset.coe_injective <| by simp
                             -- 🎉 no goals
#align set.finite.to_finset_image2 Set.Finite.toFinset_image2

end Set
