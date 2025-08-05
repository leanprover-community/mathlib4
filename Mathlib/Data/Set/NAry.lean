/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Set.Prod

/-!
# N-ary images of sets

This file defines `Set.image2`, the binary image of sets.
This is mostly useful to define pointwise operations and `Set.seq`.

## Notes

This file is very similar to `Data.Finset.NAry`, to `Order.Filter.NAry`, and to
`Data.Option.NAry`. Please keep them in sync.
-/

open Function

namespace Set
variable {α α' β β' γ γ' δ δ' ε ε' ζ ζ' ν : Type*} {f f' : α → β → γ}
variable {s s' : Set α} {t t' : Set β} {u : Set γ} {v : Set δ} {a : α} {b : β}

theorem mem_image2_iff (hf : Injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by
    rintro ⟨a', ha', b', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
@[gcongr]
theorem image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)

theorem image2_subset_left (ht : t ⊆ t') : image2 f s t ⊆ image2 f s t' :=
  image2_subset Subset.rfl ht

theorem image2_subset_right (hs : s ⊆ s') : image2 f s t ⊆ image2 f s' t :=
  image2_subset hs Subset.rfl

theorem image_subset_image2_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ image2 f s t :=
  forall_mem_image.2 fun _ ha => mem_image2_of_mem ha hb

theorem image_subset_image2_right (ha : a ∈ s) : f a '' t ⊆ image2 f s t :=
  forall_mem_image.2 fun _ => mem_image2_of_mem ha

lemma forall_mem_image2 {p : γ → Prop} :
    (∀ z ∈ image2 f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) := by aesop

lemma exists_mem_image2 {p : γ → Prop} :
    (∃ z ∈ image2 f s t, p z) ↔ ∃ x ∈ s, ∃ y ∈ t, p (f x y) := by aesop

@[simp]
theorem image2_subset_iff {u : Set γ} : image2 f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_mem_image2

theorem image2_subset_iff_left : image2 f s t ⊆ u ↔ ∀ a ∈ s, (fun b => f a b) '' t ⊆ u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage]

theorem image2_subset_iff_right : image2 f s t ⊆ u ↔ ∀ b ∈ t, (fun a => f a b) '' s ⊆ u := by
  simp_rw [image2_subset_iff, image_subset_iff, subset_def, mem_preimage, @forall₂_swap α]

variable (f)

@[simp]
lemma image_prod : (fun x : α × β ↦ f x.1 x.2) '' s ×ˢ t = image2 f s t :=
  ext fun _ ↦ by simp [and_assoc]

@[simp] lemma image_uncurry_prod (s : Set α) (t : Set β) : uncurry f '' s ×ˢ t = image2 f s t :=
  image_prod _

@[simp] lemma image2_mk_eq_prod : image2 Prod.mk s t = s ×ˢ t := ext <| by simp

@[simp]
lemma image2_curry (f : α × β → γ) (s : Set α) (t : Set β) :
    image2 (fun a b ↦ f (a, b)) s t = f '' s ×ˢ t := by
  simp [← image_uncurry_prod, uncurry]

theorem image2_swap (s : Set α) (t : Set β) : image2 f s t = image2 (fun a b => f b a) t s := by
  ext
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, rfl⟩

variable {f}

theorem image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t := by
  simp_rw [← image_prod, union_prod, image_union]

theorem image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' := by
  rw [← image2_swap, image2_union_left, image2_swap f, image2_swap f]

lemma image2_inter_left (hf : Injective2 f) :
    image2 f (s ∩ s') t = image2 f s t ∩ image2 f s' t := by
  simp_rw [← image_uncurry_prod, inter_prod, image_inter hf.uncurry]

lemma image2_inter_right (hf : Injective2 f) :
    image2 f s (t ∩ t') = image2 f s t ∩ image2 f s t' := by
  simp_rw [← image_uncurry_prod, prod_inter, image_inter hf.uncurry]

@[simp]
theorem image2_empty_left : image2 f ∅ t = ∅ :=
  ext <| by simp

@[simp]
theorem image2_empty_right : image2 f s ∅ = ∅ :=
  ext <| by simp

theorem Nonempty.image2 : s.Nonempty → t.Nonempty → (image2 f s t).Nonempty :=
  fun ⟨_, ha⟩ ⟨_, hb⟩ => ⟨_, mem_image2_of_mem ha hb⟩

@[simp]
theorem image2_nonempty_iff : (image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun ⟨_, a, ha, b, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.image2 h.2⟩

theorem Nonempty.of_image2_left (h : (Set.image2 f s t).Nonempty) : s.Nonempty :=
  (image2_nonempty_iff.1 h).1

theorem Nonempty.of_image2_right (h : (Set.image2 f s t).Nonempty) : t.Nonempty :=
  (image2_nonempty_iff.1 h).2

@[simp]
theorem image2_eq_empty_iff : image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty, image2_nonempty_iff, not_and_or]
  simp [not_nonempty_iff_eq_empty]

theorem Subsingleton.image2 (hs : s.Subsingleton) (ht : t.Subsingleton) (f : α → β → γ) :
    (image2 f s t).Subsingleton := by
  rw [← image_prod]
  apply (hs.prod ht).image

theorem image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
  Monotone.map_inf_le (fun _ _ ↦ image2_subset_right) s s'

theorem image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
  Monotone.map_inf_le (fun _ _ ↦ image2_subset_left) t t'

@[simp]
theorem image2_singleton_left : image2 f {a} t = f a '' t :=
  ext fun x => by simp

@[simp]
theorem image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s :=
  ext fun x => by simp

theorem image2_singleton : image2 f {a} {b} = {f a b} := by simp

@[simp]
theorem image2_insert_left : image2 f (insert a s) t = (fun b => f a b) '' t ∪ image2 f s t := by
  rw [insert_eq, image2_union_left, image2_singleton_left]

@[simp]
theorem image2_insert_right : image2 f s (insert b t) = (fun a => f a b) '' s ∪ image2 f s t := by
  rw [insert_eq, image2_union_right, image2_singleton_right]

@[congr]
theorem image2_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image2 f s t = image2 f' s t := by
  ext
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨a, ha, b, hb, by rw [h a ha b hb]⟩

/-- A common special case of `image2_congr` -/
theorem image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
  image2_congr fun a _ b _ => h a b

theorem image_image2 (f : α → β → γ) (g : γ → δ) :
    g '' image2 f s t = image2 (fun a b => g (f a b)) s t := by
  simp only [← image_prod, image_image]

theorem image2_image_left (f : γ → β → δ) (g : α → γ) :
    image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t := by
  ext; simp

theorem image2_image_right (f : α → γ → δ) (g : β → γ) :
    image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t := by
  ext; simp

@[simp]
theorem image2_left (h : t.Nonempty) : image2 (fun x _ => x) s t = s := by
  simp [nonempty_def.mp h, Set.ext_iff]

@[simp]
theorem image2_right (h : s.Nonempty) : image2 (fun _ y => y) s t = t := by
  simp [nonempty_def.mp h, Set.ext_iff]

lemma image2_range (f : α' → β' → γ) (g : α → α') (h : β → β') :
    image2 f (range g) (range h) = range fun x : α × β ↦ f (g x.1) (h x.2) := by
  simp_rw [← image_univ, image2_image_left, image2_image_right, ← image_prod, univ_prod_univ]

theorem image2_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
  eq_of_forall_subset_iff fun _ ↦ by simp only [image2_subset_iff, forall_mem_image2, h_assoc]

theorem image2_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image2 f s t = image2 g t s :=
  (image2_swap _ _ _).trans <| by simp_rw [h_comm]

theorem image2_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image2 f s (image2 g t u) = image2 g' t (image2 f' s u) := by
  rw [image2_swap f', image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _

theorem image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image2 f (image2 g s t) u = image2 g' (image2 f' s u) t := by
  rw [image2_swap g, image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _

theorem image2_image2_image2_comm {f : ε → ζ → ν} {g : α → β → ε} {h : γ → δ → ζ} {f' : ε' → ζ' → ν}
    {g' : α → γ → ε'} {h' : β → δ → ζ'}
    (h_comm : ∀ a b c d, f (g a b) (h c d) = f' (g' a c) (h' b d)) :
    image2 f (image2 g s t) (image2 h u v) = image2 f' (image2 g' s u) (image2 h' t v) := by
  ext; constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, _, ⟨c, hc, d, hd, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, c, hc, rfl⟩, _, ⟨b, hb, d, hd, rfl⟩, (h_comm _ _ _ _).symm⟩
  · rintro ⟨_, ⟨a, ha, c, hc, rfl⟩, _, ⟨b, hb, d, hd, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, b, hb, rfl⟩, _, ⟨c, hc, d, hd, rfl⟩, h_comm _ _ _ _⟩

theorem image_image2_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image2 f s t).image g = image2 f' (s.image g₁) (t.image g₂) := by
  simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

/-- Symmetric statement to `Set.image2_image_left_comm`. -/
theorem image_image2_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image2 f s t).image g = image2 f' (s.image g') t :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_right_comm`. -/
theorem image_image2_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image2 f s t).image g = image2 f' s (t.image g') :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_distrib_left`. -/
theorem image2_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image2 f (s.image g) t = (image2 f' s t).image g' :=
  (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm

/-- Symmetric statement to `Set.image_image2_distrib_right`. -/
theorem image_image2_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image2 f s (t.image g) = (image2 f' s t).image g' :=
  (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image2_distrib_subset_left {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'}
    {f₂ : α → γ → γ'} {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image2 f s (image2 g t u) ⊆ image2 g' (image2 f₁ s t) (image2 f₂ s u) := by
  rintro _ ⟨a, ha, _, ⟨b, hb, c, hc, rfl⟩, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hb) (mem_image2_of_mem ha hc)

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image2_distrib_subset_right {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'}
    {f₂ : β → γ → β'} {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image2 f (image2 g s t) u ⊆ image2 g' (image2 f₁ s u) (image2 f₂ t u) := by
  rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hc) (mem_image2_of_mem hb hc)

theorem image_image2_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image2 f s t).image g = image2 f' (t.image g₁) (s.image g₂) := by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _

/-- Symmetric statement to `Set.image2_image_left_anticomm`. -/
theorem image_image2_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image2 f s t).image g = image2 f' (t.image g') s :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_right_anticomm`. -/
theorem image_image2_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image2 f s t).image g = image2 f' t (s.image g') :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']

/-- Symmetric statement to `Set.image_image2_antidistrib_left`. -/
theorem image2_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image2 f (s.image g) t = (image2 f' t s).image g' :=
  (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `Set.image_image2_antidistrib_right`. -/
theorem image_image2_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image2 f s (t.image g) = (image2 f' t s).image g' :=
  (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`Set.image2 f`. -/
lemma image2_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (t : Set β) :
    image2 f {a} t = t := by
  rw [image2_singleton_left, show f a = id from funext h, image_id]

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`Set.image2 f`. -/
lemma image2_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (s : Set α) :
    image2 f s {b} = s := by
  rw [image2_singleton_right, funext h, image_id']

theorem image2_inter_union_subset_union :
    image2 f (s ∩ s') (t ∪ t') ⊆ image2 f s t ∪ image2 f s' t' := by
  rw [image2_union_right]
  exact
    union_subset_union (image2_subset_right inter_subset_left)
      (image2_subset_right inter_subset_right)

theorem image2_union_inter_subset_union :
    image2 f (s ∪ s') (t ∩ t') ⊆ image2 f s t ∪ image2 f s' t' := by
  rw [image2_union_left]
  exact
    union_subset_union (image2_subset_left inter_subset_left)
      (image2_subset_left inter_subset_right)

theorem image2_inter_union_subset {f : α → α → β} {s t : Set α} (hf : ∀ a b, f a b = f b a) :
    image2 f (s ∩ t) (s ∪ t) ⊆ image2 f s t := by
  rw [inter_comm]
  exact image2_inter_union_subset_union.trans (union_subset (image2_comm hf).subset Subset.rfl)

theorem image2_union_inter_subset {f : α → α → β} {s t : Set α} (hf : ∀ a b, f a b = f b a) :
    image2 f (s ∪ t) (s ∩ t) ⊆ image2 f s t := by
  rw [image2_comm hf]
  exact image2_inter_union_subset hf

end Set
