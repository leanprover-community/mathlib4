/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Hom.Set

#align_import order.antichain from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.adj` for `G : SimpleGraph α`, this corresponds to independent sets of `G`.

## Definitions

* `IsAntichain r s`: Any two elements of `s : Set α` are unrelated by `r : α → α → Prop`.
* `IsStrongAntichain r s`: Any two elements of `s : Set α` are not related by `r : α → α → Prop`
  to a common element.
* `IsAntichain.mk r s`: Turns `s` into an antichain by keeping only the "maximal" elements.
-/


open Function Set

section General

variable {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : Set α} {a b : α}

protected theorem Symmetric.compl (h : Symmetric r) : Symmetric rᶜ := fun _ _ hr hr' =>
  hr <| h hr'
#align symmetric.compl Symmetric.compl

/-- An antichain is a set such that no two distinct elements are related. -/
def IsAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise rᶜ
#align is_antichain IsAntichain

namespace IsAntichain

protected theorem subset (hs : IsAntichain r s) (h : t ⊆ s) : IsAntichain r t :=
  hs.mono h
#align is_antichain.subset IsAntichain.subset

theorem mono (hs : IsAntichain r₁ s) (h : r₂ ≤ r₁) : IsAntichain r₂ s :=
  hs.mono' <| compl_le_compl h
#align is_antichain.mono IsAntichain.mono

theorem mono_on (hs : IsAntichain r₁ s) (h : s.Pairwise fun ⦃a b⦄ => r₂ a b → r₁ a b) :
    IsAntichain r₂ s :=
  hs.imp_on <| h.imp fun _ _ h h₁ h₂ => h₁ <| h h₂
#align is_antichain.mono_on IsAntichain.mono_on

protected theorem eq (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r a b) :
    a = b :=
  Set.Pairwise.eq hs ha hb <| not_not_intro h
#align is_antichain.eq IsAntichain.eq

protected theorem eq' (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r b a) :
    a = b :=
  (hs.eq hb ha h).symm
#align is_antichain.eq' IsAntichain.eq'

protected theorem isAntisymm (h : IsAntichain r univ) : IsAntisymm α r :=
  ⟨fun _ _ ha _ => h.eq trivial trivial ha⟩
#align is_antichain.is_antisymm IsAntichain.isAntisymm

protected theorem subsingleton [IsTrichotomous α r] (h : IsAntichain r s) : s.Subsingleton := by
  rintro a ha b hb
  -- ⊢ a = b
  obtain hab | hab | hab := trichotomous_of r a b
  · exact h.eq ha hb hab
    -- 🎉 no goals
  · exact hab
    -- 🎉 no goals
  · exact h.eq' ha hb hab
    -- 🎉 no goals
#align is_antichain.subsingleton IsAntichain.subsingleton

protected theorem flip (hs : IsAntichain r s) : IsAntichain (flip r) s := fun _ ha _ hb h =>
  hs hb ha h.symm
#align is_antichain.flip IsAntichain.flip

theorem swap (hs : IsAntichain r s) : IsAntichain (swap r) s :=
  hs.flip
#align is_antichain.swap IsAntichain.swap

theorem image (hs : IsAntichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) :
    IsAntichain r' (f '' s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr
  -- ⊢ False
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr)
  -- 🎉 no goals
#align is_antichain.image IsAntichain.image

theorem preimage (hs : IsAntichain r s) {f : β → α} (hf : Injective f)
    (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) : IsAntichain r' (f ⁻¹' s) := fun _ hb _ hc hbc hr =>
  hs hb hc (hf.ne hbc) <| h hr
#align is_antichain.preimage IsAntichain.preimage

theorem _root_.isAntichain_insert :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b ∧ ¬r b a :=
  Set.pairwise_insert
#align is_antichain_insert isAntichain_insert

protected theorem insert (hs : IsAntichain r s) (hl : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r b a)
    (hr : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) : IsAntichain r (insert a s) :=
  isAntichain_insert.2 ⟨hs, fun _ hb hab => ⟨hr hb hab, hl hb hab⟩⟩
#align is_antichain.insert IsAntichain.insert

theorem _root_.isAntichain_insert_of_symmetric (hr : Symmetric r) :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b :=
  pairwise_insert_of_symmetric hr.compl
#align is_antichain_insert_of_symmetric isAntichain_insert_of_symmetric

theorem insert_of_symmetric (hs : IsAntichain r s) (hr : Symmetric r)
    (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) : IsAntichain r (insert a s) :=
  (isAntichain_insert_of_symmetric hr).2 ⟨hs, h⟩
#align is_antichain.insert_of_symmetric IsAntichain.insert_of_symmetric

theorem image_relEmbedding (hs : IsAntichain r s) (φ : r ↪r r') : IsAntichain r' (φ '' s) := by
  intro b hb b' hb' h₁ h₂
  -- ⊢ False
  rw [Set.mem_image] at hb hb'
  -- ⊢ False
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  -- ⊢ False
  exact hs has has' (fun haa' => h₁ (by rw [haa'])) (φ.map_rel_iff.mp h₂)
  -- 🎉 no goals
#align is_antichain.image_rel_embedding IsAntichain.image_relEmbedding

theorem preimage_relEmbedding {t : Set β} (ht : IsAntichain r' t) (φ : r ↪r r') :
    IsAntichain r (φ ⁻¹' t) := fun _ ha _s ha' hne hle =>
  ht ha ha' (fun h => hne (φ.injective h)) (φ.map_rel_iff.mpr hle)
#align is_antichain.preimage_rel_embedding IsAntichain.preimage_relEmbedding

theorem image_relIso (hs : IsAntichain r s) (φ : r ≃r r') : IsAntichain r' (φ '' s) :=
  hs.image_relEmbedding φ
#align is_antichain.image_rel_iso IsAntichain.image_relIso

theorem preimage_relIso {t : Set β} (hs : IsAntichain r' t) (φ : r ≃r r') :
    IsAntichain r (φ ⁻¹' t) :=
  hs.preimage_relEmbedding φ
#align is_antichain.preimage_rel_iso IsAntichain.preimage_relIso

theorem image_relEmbedding_iff {φ : r ↪r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  ⟨fun h => (φ.injective.preimage_image s).subst (h.preimage_relEmbedding φ), fun h =>
    h.image_relEmbedding φ⟩
#align is_antichain.image_rel_embedding_iff IsAntichain.image_relEmbedding_iff

theorem image_relIso_iff {φ : r ≃r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')
#align is_antichain.image_rel_iso_iff IsAntichain.image_relIso_iff

theorem image_embedding [LE α] [LE β] (hs : IsAntichain (· ≤ ·) s) (φ : α ↪o β) :
    IsAntichain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _
#align is_antichain.image_embedding IsAntichain.image_embedding

theorem preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsAntichain (· ≤ ·) t) (φ : α ↪o β) :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
#align is_antichain.preimage_embedding IsAntichain.preimage_embedding

theorem image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsAntichain (· ≤ ·) (φ '' s) ↔ IsAntichain (· ≤ ·) s :=
  image_relEmbedding_iff
#align is_antichain.image_embedding_iff IsAntichain.image_embedding_iff

theorem image_iso [LE α] [LE β] (hs : IsAntichain (· ≤ ·) s) (φ : α ≃o β) :
    IsAntichain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _
#align is_antichain.image_iso IsAntichain.image_iso

theorem image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsAntichain (· ≤ ·) (φ '' s) ↔ IsAntichain (· ≤ ·) s :=
  image_relEmbedding_iff
#align is_antichain.image_iso_iff IsAntichain.image_iso_iff

theorem preimage_iso [LE α] [LE β] {t : Set β} (ht : IsAntichain (· ≤ ·) t) (φ : α ≃o β) :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
#align is_antichain.preimage_iso IsAntichain.preimage_iso

theorem preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) ↔ IsAntichain (· ≤ ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩
#align is_antichain.preimage_iso_iff IsAntichain.preimage_iso_iff

theorem to_dual [LE α] (hs : IsAntichain (· ≤ ·) s) : @IsAntichain αᵒᵈ (· ≤ ·) s :=
  fun _ ha _ hb hab => hs hb ha hab.symm
#align is_antichain.to_dual IsAntichain.to_dual

theorem to_dual_iff [LE α] : IsAntichain (· ≤ ·) s ↔ @IsAntichain αᵒᵈ (· ≤ ·) s :=
  ⟨to_dual, to_dual⟩
#align is_antichain.to_dual_iff IsAntichain.to_dual_iff

theorem image_compl [BooleanAlgebra α] (hs : IsAntichain (· ≤ ·) s) :
    IsAntichain (· ≤ ·) (compl '' s) :=
  (hs.image_embedding (OrderIso.compl α).toOrderEmbedding).flip
#align is_antichain.image_compl IsAntichain.image_compl

theorem preimage_compl [BooleanAlgebra α] (hs : IsAntichain (· ≤ ·) s) :
    IsAntichain (· ≤ ·) (compl ⁻¹' s) := fun _ ha _ ha' hne hle =>
  hs ha' ha (fun h => hne (compl_inj_iff.mp h.symm)) (compl_le_compl hle)
#align is_antichain.preimage_compl IsAntichain.preimage_compl

end IsAntichain

theorem isAntichain_singleton (a : α) (r : α → α → Prop) : IsAntichain r {a} :=
  pairwise_singleton _ _
#align is_antichain_singleton isAntichain_singleton

theorem Set.Subsingleton.isAntichain (hs : s.Subsingleton) (r : α → α → Prop) : IsAntichain r s :=
  hs.pairwise _
#align set.subsingleton.is_antichain Set.Subsingleton.isAntichain

section Preorder

variable [Preorder α]

theorem IsAntichain.not_lt (hs : IsAntichain (· ≤ ·) s) (ha : a ∈ s) (hb : b ∈ s) : ¬a < b :=
  fun h => hs ha hb h.ne h.le
#align is_antichain.not_lt IsAntichain.not_lt

theorem isAntichain_and_least_iff : IsAntichain (· ≤ ·) s ∧ IsLeast s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun b hb => h.1.eq' hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    -- ⊢ IsAntichain (fun x x_1 => x ≤ x_1) {a} ∧ IsLeast {a} a
    exact ⟨isAntichain_singleton _ _, isLeast_singleton⟩⟩
    -- 🎉 no goals
#align is_antichain_and_least_iff isAntichain_and_least_iff

theorem isAntichain_and_greatest_iff : IsAntichain (· ≤ ·) s ∧ IsGreatest s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun b hb => h.1.eq hb h.2.1 (h.2.2 hb)⟩, by
    rintro rfl
    -- ⊢ IsAntichain (fun x x_1 => x ≤ x_1) {a} ∧ IsGreatest {a} a
    exact ⟨isAntichain_singleton _ _, isGreatest_singleton⟩⟩
    -- 🎉 no goals
#align is_antichain_and_greatest_iff isAntichain_and_greatest_iff

theorem IsAntichain.least_iff (hs : IsAntichain (· ≤ ·) s) : IsLeast s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_least_iff
#align is_antichain.least_iff IsAntichain.least_iff

theorem IsAntichain.greatest_iff (hs : IsAntichain (· ≤ ·) s) : IsGreatest s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_greatest_iff
#align is_antichain.greatest_iff IsAntichain.greatest_iff

theorem IsLeast.antichain_iff (hs : IsLeast s a) : IsAntichain (· ≤ ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_least_iff
#align is_least.antichain_iff IsLeast.antichain_iff

theorem IsGreatest.antichain_iff (hs : IsGreatest s a) : IsAntichain (· ≤ ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_greatest_iff
#align is_greatest.antichain_iff IsGreatest.antichain_iff

theorem IsAntichain.bot_mem_iff [OrderBot α] (hs : IsAntichain (· ≤ ·) s) : ⊥ ∈ s ↔ s = {⊥} :=
  isLeast_bot_iff.symm.trans hs.least_iff
#align is_antichain.bot_mem_iff IsAntichain.bot_mem_iff

theorem IsAntichain.top_mem_iff [OrderTop α] (hs : IsAntichain (· ≤ ·) s) : ⊤ ∈ s ↔ s = {⊤} :=
  isGreatest_top_iff.symm.trans hs.greatest_iff
#align is_antichain.top_mem_iff IsAntichain.top_mem_iff

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem isAntichain_iff_forall_not_lt :
    IsAntichain (· ≤ ·) s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬a < b :=
  ⟨fun hs _ ha _ => hs.not_lt ha, fun hs _ ha _ hb h h' => hs ha hb <| h'.lt_of_ne h⟩
#align is_antichain_iff_forall_not_lt isAntichain_iff_forall_not_lt

end PartialOrder

/-! ### Strong antichains -/


/-- A strong (upward) antichain is a set such that no two distinct elements are related to a common
element. -/
def IsStrongAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise fun a b => ∀ c, ¬r a c ∨ ¬r b c
#align is_strong_antichain IsStrongAntichain

namespace IsStrongAntichain

protected theorem subset (hs : IsStrongAntichain r s) (h : t ⊆ s) : IsStrongAntichain r t :=
  hs.mono h
#align is_strong_antichain.subset IsStrongAntichain.subset

theorem mono (hs : IsStrongAntichain r₁ s) (h : r₂ ≤ r₁) : IsStrongAntichain r₂ s :=
  hs.mono' fun _ _ hab c => (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)
#align is_strong_antichain.mono IsStrongAntichain.mono

theorem eq (hs : IsStrongAntichain r s) {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hac : r a c)
    (hbc : r b c) : a = b :=
  (Set.Pairwise.eq hs ha hb) fun h =>
    False.elim <| (h c).elim (not_not_intro hac) (not_not_intro hbc)
#align is_strong_antichain.eq IsStrongAntichain.eq

protected theorem isAntichain [IsRefl α r] (h : IsStrongAntichain r s) : IsAntichain r s :=
  h.imp fun _ b hab => (hab b).resolve_right (not_not_intro <| refl _)
#align is_strong_antichain.is_antichain IsStrongAntichain.isAntichain

protected theorem subsingleton [IsDirected α r] (h : IsStrongAntichain r s) : s.Subsingleton :=
  fun a ha b hb =>
  let ⟨_, hac, hbc⟩ := directed_of r a b
  h.eq ha hb hac hbc
#align is_strong_antichain.subsingleton IsStrongAntichain.subsingleton

protected theorem flip [IsSymm α r] (hs : IsStrongAntichain r s) : IsStrongAntichain (flip r) s :=
  fun _ ha _ hb h c => (hs ha hb h c).imp (mt <| symm_of r) (mt <| symm_of r)
#align is_strong_antichain.flip IsStrongAntichain.flip

theorem swap [IsSymm α r] (hs : IsStrongAntichain r s) : IsStrongAntichain (swap r) s :=
  hs.flip
#align is_strong_antichain.swap IsStrongAntichain.swap

theorem image (hs : IsStrongAntichain r s) {f : α → β} (hf : Surjective f)
    (h : ∀ a b, r' (f a) (f b) → r a b) : IsStrongAntichain r' (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c
  -- ⊢ ¬r' (f a) c ∨ ¬r' (f b) c
  obtain ⟨c, rfl⟩ := hf c
  -- ⊢ ¬r' (f a) (f c) ∨ ¬r' (f b) (f c)
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt <| h _ _) (mt <| h _ _)
  -- 🎉 no goals
#align is_strong_antichain.image IsStrongAntichain.image

theorem preimage (hs : IsStrongAntichain r s) {f : β → α} (hf : Injective f)
    (h : ∀ a b, r' a b → r (f a) (f b)) : IsStrongAntichain r' (f ⁻¹' s) := fun _ ha _ hb hab _ =>
  (hs ha hb (hf.ne hab) _).imp (mt <| h _ _) (mt <| h _ _)
#align is_strong_antichain.preimage IsStrongAntichain.preimage

theorem _root_.isStrongAntichain_insert :
    IsStrongAntichain r (insert a s) ↔
      IsStrongAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬r a c ∨ ¬r b c :=
  Set.pairwise_insert_of_symmetric fun _ _ h c => (h c).symm
#align is_strong_antichain_insert isStrongAntichain_insert

protected theorem insert (hs : IsStrongAntichain r s)
    (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬r a c ∨ ¬r b c) : IsStrongAntichain r (insert a s) :=
  isStrongAntichain_insert.2 ⟨hs, h⟩
#align is_strong_antichain.insert IsStrongAntichain.insert

end IsStrongAntichain

theorem Set.Subsingleton.isStrongAntichain (hs : s.Subsingleton) (r : α → α → Prop) :
    IsStrongAntichain r s :=
  hs.pairwise _
#align set.subsingleton.is_strong_antichain Set.Subsingleton.isStrongAntichain

end General

/-! ### Weak antichains -/


section Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] {s t : Set (∀ i, α i)}
  {a b c : ∀ i, α i}


@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

/-- A weak antichain in `Π i, α i` is a set such that no two distinct elements are strongly less
than each other. -/
def IsWeakAntichain (s : Set (∀ i, α i)) : Prop :=
  IsAntichain (· ≺ ·) s
#align is_weak_antichain IsWeakAntichain

namespace IsWeakAntichain

protected theorem subset (hs : IsWeakAntichain s) : t ⊆ s → IsWeakAntichain t :=
  IsAntichain.subset hs
#align is_weak_antichain.subset IsWeakAntichain.subset

protected theorem eq (hs : IsWeakAntichain s) : a ∈ s → b ∈ s → a ≺ b → a = b :=
  IsAntichain.eq hs
#align is_weak_antichain.eq IsWeakAntichain.eq

protected theorem insert (hs : IsWeakAntichain s) :
    (∀ ⦃b⦄, b ∈ s → a ≠ b → ¬b ≺ a) →
      (∀ ⦃b⦄, b ∈ s → a ≠ b → ¬a ≺ b) → IsWeakAntichain (insert a s) :=
  IsAntichain.insert hs
#align is_weak_antichain.insert IsWeakAntichain.insert

end IsWeakAntichain

theorem _root_.isWeakAntichain_insert :
    IsWeakAntichain (insert a s) ↔ IsWeakAntichain s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬a ≺ b ∧ ¬b ≺ a :=
  isAntichain_insert
#align is_weak_antichain_insert isWeakAntichain_insert

protected theorem IsAntichain.isWeakAntichain (hs : IsAntichain (· ≤ ·) s) : IsWeakAntichain s :=
  hs.mono fun _ _ => le_of_strongLT
#align is_antichain.is_weak_antichain IsAntichain.isWeakAntichain

theorem Set.Subsingleton.isWeakAntichain (hs : s.Subsingleton) : IsWeakAntichain s :=
  hs.isAntichain _
#align set.subsingleton.is_weak_antichain Set.Subsingleton.isWeakAntichain

end Pi
