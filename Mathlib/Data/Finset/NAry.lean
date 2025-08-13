/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Lattice.Image

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

variable [DecidableEq α'] [DecidableEq β'] [DecidableEq γ] [DecidableEq γ']
  [DecidableEq δ'] [DecidableEq ε] [DecidableEq ε'] {f f' : α → β → γ} {g g' : α → β → γ → δ}
  {s s' : Finset α} {t t' : Finset β} {u u' : Finset γ} {a a' : α} {b b' : β} {c : γ}

/-- The image of a binary function `f : α → β → γ` as a function `Finset α → Finset β → Finset γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) : Finset γ :=
  (s ×ˢ t).image <| uncurry f

@[simp]
theorem mem_image₂ : c ∈ image₂ f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := by
  simp [image₂, and_assoc]

@[simp, norm_cast]
theorem coe_image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (image₂ f s t : Set γ) = Set.image2 f s t :=
  Set.ext fun _ => mem_image₂

theorem card_image₂_le (f : α → β → γ) (s : Finset α) (t : Finset β) :
    #(image₂ f s t) ≤ #s * #t :=
  card_image_le.trans_eq <| card_product _ _

theorem card_image₂_iff :
    #(image₂ f s t) = #s * #t ↔ (s ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2 := by
  rw [← card_product, ← coe_product]
  exact card_image_iff

theorem card_image₂ (hf : Injective2 f) (s : Finset α) (t : Finset β) :
    #(image₂ f s t) = #s * #t :=
  (card_image_of_injective _ hf.uncurry).trans <| card_product _ _

theorem mem_image₂_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image₂ f s t :=
  mem_image₂.2 ⟨a, ha, b, hb, rfl⟩

theorem mem_image₂_iff (hf : Injective2 f) : f a b ∈ image₂ f s t ↔ a ∈ s ∧ b ∈ t := by
  rw [← mem_coe, coe_image₂, mem_image2_iff hf, mem_coe, mem_coe]

@[gcongr]
theorem image₂_subset (hs : s ⊆ s') (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s' t' := by
  rw [← coe_subset, coe_image₂, coe_image₂]
  exact image2_subset hs ht

theorem image₂_subset_left (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s t' :=
  image₂_subset Subset.rfl ht

theorem image₂_subset_right (hs : s ⊆ s') : image₂ f s t ⊆ image₂ f s' t :=
  image₂_subset hs Subset.rfl

theorem image_subset_image₂_left (hb : b ∈ t) : s.image (fun a => f a b) ⊆ image₂ f s t :=
  image_subset_iff.2 fun _ ha => mem_image₂_of_mem ha hb

theorem image_subset_image₂_right (ha : a ∈ s) : t.image (fun b => f a b) ⊆ image₂ f s t :=
  image_subset_iff.2 fun _ => mem_image₂_of_mem ha

lemma forall_mem_image₂ {p : γ → Prop} :
    (∀ z ∈ image₂ f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, forall_mem_image2]

lemma exists_mem_image₂ {p : γ → Prop} :
    (∃ z ∈ image₂ f s t, p z) ↔ ∃ x ∈ s, ∃ y ∈ t, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, exists_mem_image2]

@[simp]
theorem image₂_subset_iff : image₂ f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_mem_image₂

theorem image₂_subset_iff_left : image₂ f s t ⊆ u ↔ ∀ a ∈ s, (t.image fun b => f a b) ⊆ u := by
  simp_rw [image₂_subset_iff, image_subset_iff]

theorem image₂_subset_iff_right : image₂ f s t ⊆ u ↔ ∀ b ∈ t, (s.image fun a => f a b) ⊆ u := by
  simp_rw [image₂_subset_iff, image_subset_iff, @forall₂_swap α]

@[simp]
theorem image₂_nonempty_iff : (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  rw [← coe_nonempty, coe_image₂]
  exact image2_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.image₂ (hs : s.Nonempty) (ht : t.Nonempty) : (image₂ f s t).Nonempty :=
  image₂_nonempty_iff.2 ⟨hs, ht⟩

theorem Nonempty.of_image₂_left (h : (s.image₂ f t).Nonempty) : s.Nonempty :=
  (image₂_nonempty_iff.1 h).1

theorem Nonempty.of_image₂_right (h : (s.image₂ f t).Nonempty) : t.Nonempty :=
  (image₂_nonempty_iff.1 h).2

@[simp]
theorem image₂_empty_left : image₂ f ∅ t = ∅ :=
  coe_injective <| by simp

@[simp]
theorem image₂_empty_right : image₂ f s ∅ = ∅ :=
  coe_injective <| by simp

@[simp]
theorem image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp_rw [← not_nonempty_iff_eq_empty, image₂_nonempty_iff, not_and_or]

@[simp]
theorem image₂_singleton_left : image₂ f {a} t = t.image fun b => f a b :=
  ext fun x => by simp

@[simp]
theorem image₂_singleton_right : image₂ f s {b} = s.image fun a => f a b :=
  ext fun x => by simp

theorem image₂_singleton_left' : image₂ f {a} t = t.image (f a) :=
  image₂_singleton_left

theorem image₂_singleton : image₂ f {a} {b} = {f a b} := by simp

theorem image₂_union_left [DecidableEq α] : image₂ f (s ∪ s') t = image₂ f s t ∪ image₂ f s' t :=
  coe_injective <| by
    push_cast
    exact image2_union_left

theorem image₂_union_right [DecidableEq β] : image₂ f s (t ∪ t') = image₂ f s t ∪ image₂ f s t' :=
  coe_injective <| by
    push_cast
    exact image2_union_right

@[simp]
theorem image₂_insert_left [DecidableEq α] :
    image₂ f (insert a s) t = (t.image fun b => f a b) ∪ image₂ f s t :=
  coe_injective <| by
    push_cast
    exact image2_insert_left

@[simp]
theorem image₂_insert_right [DecidableEq β] :
    image₂ f s (insert b t) = (s.image fun a => f a b) ∪ image₂ f s t :=
  coe_injective <| by
    push_cast
    exact image2_insert_right

theorem image₂_inter_left [DecidableEq α] (hf : Injective2 f) :
    image₂ f (s ∩ s') t = image₂ f s t ∩ image₂ f s' t :=
  coe_injective <| by
    push_cast
    exact image2_inter_left hf

theorem image₂_inter_right [DecidableEq β] (hf : Injective2 f) :
    image₂ f s (t ∩ t') = image₂ f s t ∩ image₂ f s t' :=
  coe_injective <| by
    push_cast
    exact image2_inter_right hf

theorem image₂_inter_subset_left [DecidableEq α] :
    image₂ f (s ∩ s') t ⊆ image₂ f s t ∩ image₂ f s' t :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_subset_left

theorem image₂_inter_subset_right [DecidableEq β] :
    image₂ f s (t ∩ t') ⊆ image₂ f s t ∩ image₂ f s t' :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_subset_right

theorem image₂_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  coe_injective <| by
    push_cast
    exact image2_congr h

/-- A common special case of `image₂_congr` -/
theorem image₂_congr' (h : ∀ a b, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  image₂_congr fun a _ b _ => h a b

variable (s t)

theorem card_image₂_singleton_left (hf : Injective (f a)) : #(image₂ f {a} t) = #t := by
  rw [image₂_singleton_left, card_image_of_injective _ hf]

theorem card_image₂_singleton_right (hf : Injective fun a => f a b) :
    #(image₂ f s {b}) = #s := by rw [image₂_singleton_right, card_image_of_injective _ hf]

theorem image₂_singleton_inter [DecidableEq β] (t₁ t₂ : Finset β) (hf : Injective (f a)) :
    image₂ f {a} (t₁ ∩ t₂) = image₂ f {a} t₁ ∩ image₂ f {a} t₂ := by
  simp_rw [image₂_singleton_left, image_inter _ _ hf]

theorem image₂_inter_singleton [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective fun a => f a b) :
    image₂ f (s₁ ∩ s₂) {b} = image₂ f s₁ {b} ∩ image₂ f s₂ {b} := by
  simp_rw [image₂_singleton_right, image_inter _ _ hf]

theorem card_le_card_image₂_left {s : Finset α} (ha : a ∈ s) (hf : Injective (f a)) :
    #t ≤ #(image₂ f s t) :=
  card_le_card_of_injOn (f a) (fun _ hb ↦ mem_image₂_of_mem ha hb) hf.injOn

theorem card_le_card_image₂_right {t : Finset β} (hb : b ∈ t) (hf : Injective (f · b)) :
    #s ≤ #(image₂ f s t) :=
  card_le_card_of_injOn (f · b) (fun _ ha ↦ mem_image₂_of_mem ha hb) hf.injOn

variable {s t}

theorem biUnion_image_left : (s.biUnion fun a => t.image <| f a) = image₂ f s t :=
  coe_injective <| by
    push_cast
    exact Set.iUnion_image_left _

theorem biUnion_image_right : (t.biUnion fun b => s.image fun a => f a b) = image₂ f s t :=
  coe_injective <| by
    push_cast
    exact Set.iUnion_image_right _

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Finset.image₂` of those operations.

The proof pattern is `image₂_lemma operation_lemma`. For example, `image₂_comm mul_comm` proves that
`image₂ (*) f g = image₂ (*) g f` in a `CommSemigroup`.
-/

section
variable [DecidableEq δ]

theorem image_image₂ (f : α → β → γ) (g : γ → δ) :
    (image₂ f s t).image g = image₂ (fun a b => g (f a b)) s t :=
  coe_injective <| by
    push_cast
    exact image_image2 _ _

theorem image₂_image_left (f : γ → β → δ) (g : α → γ) :
    image₂ f (s.image g) t = image₂ (fun a b => f (g a) b) s t :=
  coe_injective <| by
    push_cast
    exact image2_image_left _ _

theorem image₂_image_right (f : α → γ → δ) (g : β → γ) :
    image₂ f s (t.image g) = image₂ (fun a b => f a (g b)) s t :=
  coe_injective <| by
    push_cast
    exact image2_image_right _ _

@[simp]
theorem image₂_mk_eq_product [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    image₂ Prod.mk s t = s ×ˢ t := by ext; simp [Prod.ext_iff]

@[simp]
theorem image₂_curry (f : α × β → γ) (s : Finset α) (t : Finset β) :
    image₂ (curry f) s t = (s ×ˢ t).image f := rfl

@[simp]
theorem image_uncurry_product (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (s ×ˢ t).image (uncurry f) = image₂ f s t := rfl

theorem image₂_swap (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = image₂ (fun a b => f b a) t s :=
  coe_injective <| by
    push_cast
    exact image2_swap _ _ _

@[simp]
theorem image₂_left [DecidableEq α] (h : t.Nonempty) : image₂ (fun x _ => x) s t = s :=
  coe_injective <| by
    push_cast
    exact image2_left h

@[simp]
theorem image₂_right [DecidableEq β] (h : s.Nonempty) : image₂ (fun _ y => y) s t = t :=
  coe_injective <| by
    push_cast
    exact image2_right h

theorem image₂_assoc {γ : Type*} {u : Finset γ}
    {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε}
    {g' : β → γ → ε'} (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image₂ f (image₂ g s t) u = image₂ f' s (image₂ g' t u) :=
  coe_injective <| by
    push_cast
    exact image2_assoc h_assoc

theorem image₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image₂ f s t = image₂ g t s :=
  (image₂_swap _ _ _).trans <| by simp_rw [h_comm]

theorem image₂_left_comm {γ : Type*} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ}
    {f' : α → γ → δ'} {g' : β → δ' → ε} (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image₂ f s (image₂ g t u) = image₂ g' t (image₂ f' s u) :=
  coe_injective <| by
    push_cast
    exact image2_left_comm h_left_comm

theorem image₂_right_comm {γ : Type*} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ}
    {f' : α → γ → δ'} {g' : δ' → β → ε} (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image₂ f (image₂ g s t) u = image₂ g' (image₂ f' s u) t :=
  coe_injective <| by
    push_cast
    exact image2_right_comm h_right_comm

theorem image₂_image₂_image₂_comm {γ δ : Type*} {u : Finset γ} {v : Finset δ} [DecidableEq ζ]
    [DecidableEq ζ'] [DecidableEq ν] {f : ε → ζ → ν} {g : α → β → ε} {h : γ → δ → ζ}
    {f' : ε' → ζ' → ν} {g' : α → γ → ε'} {h' : β → δ → ζ'}
    (h_comm : ∀ a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image₂ f (image₂ g s t) (image₂ h u v) = image₂ f' (image₂ g' s u) (image₂ h' t v) :=
  coe_injective <| by
    push_cast
    exact image2_image2_image2_comm h_comm

theorem image_image₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image₂ f s t).image g = image₂ f' (s.image g₁) (t.image g₂) :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib h_distrib

/-- Symmetric statement to `Finset.image₂_image_left_comm`. -/
theorem image_image₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image₂ f s t).image g = image₂ f' (s.image g') t :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib_left h_distrib

/-- Symmetric statement to `Finset.image_image₂_right_comm`. -/
theorem image_image₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image₂ f s t).image g = image₂ f' s (t.image g') :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib_right h_distrib

/-- Symmetric statement to `Finset.image_image₂_distrib_left`. -/
theorem image₂_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image₂ f (s.image g) t = (image₂ f' s t).image g' :=
  (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm

/-- Symmetric statement to `Finset.image_image₂_distrib_right`. -/
theorem image_image₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image₂ f s (t.image g) = (image₂ f' s t).image g' :=
  (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image₂_distrib_subset_left {γ : Type*} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ}
    {f₁ : α → β → β'} {f₂ : α → γ → γ'} {g' : β' → γ' → ε}
    (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image₂ f s (image₂ g t u) ⊆ image₂ g' (image₂ f₁ s t) (image₂ f₂ s u) :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_distrib_subset_left h_distrib

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image₂_distrib_subset_right {γ : Type*} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ}
    {f₁ : α → γ → α'} {f₂ : β → γ → β'} {g' : α' → β' → ε}
    (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image₂ f (image₂ g s t) u ⊆ image₂ g' (image₂ f₁ s u) (image₂ f₂ t u) :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_distrib_subset_right h_distrib

theorem image_image₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image₂ f s t).image g = image₂ f' (t.image g₁) (s.image g₂) := by
  rw [image₂_swap f]
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _

/-- Symmetric statement to `Finset.image₂_image_left_anticomm`. -/
theorem image_image₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image₂ f s t).image g = image₂ f' (t.image g') s :=
  coe_injective <| by
    push_cast
    exact image_image2_antidistrib_left h_antidistrib

/-- Symmetric statement to `Finset.image_image₂_right_anticomm`. -/
theorem image_image₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image₂ f s t).image g = image₂ f' t (s.image g') :=
  coe_injective <| by
    push_cast
    exact image_image2_antidistrib_right h_antidistrib

/-- Symmetric statement to `Finset.image_image₂_antidistrib_left`. -/
theorem image₂_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image₂ f (s.image g) t = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `Finset.image_image₂_antidistrib_right`. -/
theorem image_image₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image₂ f s (t.image g) = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`Finset.image₂ f`. -/
theorem image₂_left_identity {f : α → γ → γ} {a : α} (h : ∀ b, f a b = b) (t : Finset γ) :
    image₂ f {a} t = t :=
  coe_injective <| by rw [coe_image₂, coe_singleton, Set.image2_left_identity h]

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`Finset.image₂ f`. -/
theorem image₂_right_identity {f : γ → β → γ} {b : β} (h : ∀ a, f a b = a) (s : Finset γ) :
    image₂ f s {b} = s := by rw [image₂_singleton_right, funext h, image_id']

/-- If each partial application of `f` is injective, and images of `s` under those partial
applications are disjoint (but not necessarily distinct!), then the size of `t` divides the size of
`Finset.image₂ f s t`. -/
theorem card_dvd_card_image₂_right (hf : ∀ a ∈ s, Injective (f a))
    (hs : ((fun a => t.image <| f a) '' s).PairwiseDisjoint id) : #t ∣ #(image₂ f s t) := by
  classical
  induction' s using Finset.induction with a s _ ih
  · simp
  specialize ih (forall_of_forall_insert hf)
    (hs.subset <| Set.image_mono <| coe_subset.2 <| subset_insert _ _)
  rw [image₂_insert_left]
  by_cases h : Disjoint (image (f a) t) (image₂ f s t)
  · rw [card_union_of_disjoint h]
    exact Nat.dvd_add (card_image_of_injective _ <| hf _ <| mem_insert_self _ _).symm.dvd ih
  simp_rw [← biUnion_image_left, disjoint_biUnion_right, not_forall] at h
  obtain ⟨b, hb, h⟩ := h
  rwa [union_eq_right.2]
  exact (hs.eq (Set.mem_image_of_mem _ <| mem_insert_self _ _)
      (Set.mem_image_of_mem _ <| mem_insert_of_mem hb) h).trans_subset
    (image_subset_image₂_right hb)

/-- If each partial application of `f` is injective, and images of `t` under those partial
applications are disjoint (but not necessarily distinct!), then the size of `s` divides the size of
`Finset.image₂ f s t`. -/
theorem card_dvd_card_image₂_left (hf : ∀ b ∈ t, Injective fun a => f a b)
    (ht : ((fun b => s.image fun a => f a b) '' t).PairwiseDisjoint id) :
    #s ∣ #(image₂ f s t) := by rw [← image₂_swap]; exact card_dvd_card_image₂_right hf ht

/-- If a `Finset` is a subset of the image of two `Set`s under a binary operation,
then it is a subset of the `Finset.image₂` of two `Finset` subsets of these `Set`s. -/
theorem subset_set_image₂ {s : Set α} {t : Set β} (hu : ↑u ⊆ image2 f s t) :
    ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ image₂ f s' t' := by
  rw [← Set.image_prod, subset_set_image_iff] at hu
  rcases hu with ⟨u, hu, rfl⟩
  classical
  use u.image Prod.fst, u.image Prod.snd
  simp only [coe_image, Set.image_subset_iff, image₂_image_left, image₂_image_right,
    image_subset_iff]
  exact ⟨fun _ h ↦ (hu h).1, fun _ h ↦ (hu h).2, fun x hx ↦ mem_image₂_of_mem hx hx⟩

end
section UnionInter

variable [DecidableEq α] [DecidableEq β]

theorem image₂_inter_union_subset_union :
    image₂ f (s ∩ s') (t ∪ t') ⊆ image₂ f s t ∪ image₂ f s' t' :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_inter_union_subset_union

theorem image₂_union_inter_subset_union :
    image₂ f (s ∪ s') (t ∩ t') ⊆ image₂ f s t ∪ image₂ f s' t' :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_union_inter_subset_union

theorem image₂_inter_union_subset {f : α → α → β} {s t : Finset α} (hf : ∀ a b, f a b = f b a) :
    image₂ f (s ∩ t) (s ∪ t) ⊆ image₂ f s t :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_union_subset hf

theorem image₂_union_inter_subset {f : α → α → β} {s t : Finset α} (hf : ∀ a b, f a b = f b a) :
    image₂ f (s ∪ t) (s ∩ t) ⊆ image₂ f s t :=
  coe_subset.1 <| by
    push_cast
    exact image2_union_inter_subset hf

end UnionInter

section SemilatticeSup

variable [SemilatticeSup δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
lemma sup'_image₂_le {g : γ → δ} {a : δ} (h : (image₂ f s t).Nonempty) :
    sup' (image₂ f s t) h g ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, g (f x y) ≤ a := by
  rw [sup'_le_iff, forall_mem_image₂]

lemma sup'_image₂_left (g : γ → δ) (h : (image₂ f s t).Nonempty) :
    sup' (image₂ f s t) h g =
      sup' s h.of_image₂_left fun x ↦ sup' t h.of_image₂_right (g <| f x ·) := by
  simp only [image₂, sup'_image, sup'_product_left]; rfl

lemma sup'_image₂_right (g : γ → δ) (h : (image₂ f s t).Nonempty) :
    sup' (image₂ f s t) h g =
      sup' t h.of_image₂_right fun y ↦ sup' s h.of_image₂_left (g <| f · y) := by
  simp only [image₂, sup'_image, sup'_product_right]; rfl

variable [OrderBot δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
lemma sup_image₂_le {g : γ → δ} {a : δ} :
    sup (image₂ f s t) g ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, g (f x y) ≤ a := by
  rw [Finset.sup_le_iff, forall_mem_image₂]

variable (s t)

lemma sup_image₂_left (g : γ → δ) : sup (image₂ f s t) g = sup s fun x ↦ sup t (g <| f x ·) := by
  simp only [image₂, sup_image, sup_product_left]; rfl

lemma sup_image₂_right (g : γ → δ) : sup (image₂ f s t) g = sup t fun y ↦ sup s (g <| f · y) := by
  simp only [image₂, sup_image, sup_product_right]; rfl

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
lemma le_inf'_image₂ {g : γ → δ} {a : δ} (h : (image₂ f s t).Nonempty) :
    a ≤ inf' (image₂ f s t) h g ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ g (f x y) := by
  rw [le_inf'_iff, forall_mem_image₂]

lemma inf'_image₂_left (g : γ → δ) (h : (image₂ f s t).Nonempty) :
    inf' (image₂ f s t) h g =
      inf' s h.of_image₂_left fun x ↦ inf' t h.of_image₂_right (g <| f x ·) :=
  sup'_image₂_left (δ := δᵒᵈ) g h

lemma inf'_image₂_right (g : γ → δ) (h : (image₂ f s t).Nonempty) :
    inf' (image₂ f s t) h g =
      inf' t h.of_image₂_right fun y ↦ inf' s h.of_image₂_left (g <| f · y) :=
  sup'_image₂_right (δ := δᵒᵈ) g h

variable [OrderTop δ]

@[simp (default + 1)] -- otherwise `simp` doesn't use `forall_mem_image₂`
lemma le_inf_image₂ {g : γ → δ} {a : δ} :
    a ≤ inf (image₂ f s t) g ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ g (f x y) :=
  sup_image₂_le (δ := δᵒᵈ)

variable (s t)

lemma inf_image₂_left (g : γ → δ) : inf (image₂ f s t) g = inf s fun x ↦ inf t (g ∘ f x) :=
  sup_image₂_left (δ := δᵒᵈ) ..

lemma inf_image₂_right (g : γ → δ) : inf (image₂ f s t) g = inf t fun y ↦ inf s (g <| f · y) :=
  sup_image₂_right (δ := δᵒᵈ) ..

end SemilatticeInf

end Finset

open Finset

namespace Fintype
variable {ι : Type*} {α β γ : ι → Type*} [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (γ i)]

lemma piFinset_image₂ (f : ∀ i, α i → β i → γ i) (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ image₂ (f i) (s i) (t i)) =
      image₂ (fun a b i ↦ f _ (a i) (b i)) (piFinset s) (piFinset t) := by
  ext; simp only [mem_piFinset, mem_image₂, Classical.skolem, forall_and, funext_iff]

end Fintype

namespace Set

variable [DecidableEq γ] {s : Set α} {t : Set β}

@[simp]
theorem toFinset_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Fintype s] [Fintype t]
    [Fintype (image2 f s t)] : (image2 f s t).toFinset = Finset.image₂ f s.toFinset t.toFinset :=
  Finset.coe_injective <| by simp

theorem Finite.toFinset_image2 (f : α → β → γ) (hs : s.Finite) (ht : t.Finite)
    (hf := hs.image2 f ht) : hf.toFinset = Finset.image₂ f hs.toFinset ht.toFinset :=
  Finset.coe_injective <| by simp

end Set
