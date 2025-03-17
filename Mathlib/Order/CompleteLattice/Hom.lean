/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.CompleteLattice.Instances
import Mathlib.Order.Hom.Set

/-!
# Complete lattices and monotone functions
-/

open Function OrderDual Set

section

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*} [CompleteLattice α]
    {f g s : ι → α} {a b : α}

theorem Monotone.le_map_iSup [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    ⨆ i, f (s i) ≤ f (iSup s) :=
  iSup_le fun _ => hf <| le_iSup _ _

theorem Antitone.le_map_iInf [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    ⨆ i, f (s i) ≤ f (iInf s) :=
  hf.dual_left.le_map_iSup

theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨆ (i) (j), s i j) :=
  iSup₂_le fun _ _ => hf <| le_iSup₂ _ _

theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _

theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    ⨆ a ∈ s, f a ≤ f (sSup s) := by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _

theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    ⨆ a ∈ s, f a ≤ f (sInf s) :=
  hf.dual_left.le_map_sSup

theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]

theorem OrderIso.map_iInf [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_iSup f.dual _

theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a ∈ s, f a := by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]

theorem OrderIso.map_sInf [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_sSup f.dual _

theorem Monotone.iSup_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : ⨆ x, f (s x) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)

theorem Monotone.iInf_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : ⨅ x, f (s x) = ⨅ y, f y :=
  le_antisymm (iInf_mono' fun x => (hs x).imp fun _ hi => hf hi) (le_iInf_comp _ _)

theorem Antitone.map_iSup_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (iSup s) ≤ ⨅ i, f (s i) :=
  le_iInf fun _ => hf <| le_iSup _ _

theorem Monotone.map_iInf_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (iInf s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_iSup_le

theorem Antitone.map_iSup₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iInf₂ _

theorem Monotone.map_iInf₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iSup₂ _

theorem Antitone.map_sSup_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (sSup s) ≤ ⨅ a ∈ s, f a := by
  rw [sSup_eq_iSup]
  exact hf.map_iSup₂_le _

theorem Monotone.map_sInf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (sInf s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_sSup_le

theorem OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = sSup (f.symm ⁻¹' s) := by
  rw [map_sSup, ← sSup_image, f.image_eq_preimage]

theorem OrderIso.map_sInf_eq_sInf_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = sInf (f.symm ⁻¹' s) := by
  rw [map_sInf, ← sInf_image, f.image_eq_preimage]

end

section CompleteLattice

variable {α β : Type*} {ι : Sort*} [Preorder α] [CompleteLattice β] {s : Set (α → β)}
  {f : ι → α → β}

protected lemma Monotone.sSup (hs : ∀ f ∈ s, Monotone f) : Monotone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

protected lemma Monotone.sInf (hs : ∀ f ∈ s, Monotone f) : Monotone (sInf s) :=
  fun _ _ h ↦ iInf_mono fun f ↦ hs f f.2 h

protected lemma Antitone.sSup (hs : ∀ f ∈ s, Antitone f) : Antitone (sSup s) :=
  fun _ _ h ↦ iSup_mono fun f ↦ hs f f.2 h

protected lemma Antitone.sInf (hs : ∀ f ∈ s, Antitone f) : Antitone (sInf s) :=
  fun _ _ h ↦ iInf_mono fun f ↦ hs f f.2 h

protected lemma Monotone.iSup (hf : ∀ i, Monotone (f i)) : Monotone (⨆ i, f i) :=
  Monotone.sSup (by simpa)
protected lemma Monotone.iInf (hf : ∀ i, Monotone (f i)) : Monotone (⨅ i, f i) :=
  Monotone.sInf (by simpa)
protected lemma Antitone.iSup (hf : ∀ i, Antitone (f i)) : Antitone (⨆ i, f i) :=
  Antitone.sSup (by simpa)
protected lemma Antitone.iInf (hf : ∀ i, Antitone (f i)) : Antitone (⨅ i, f i) :=
  Antitone.sInf (by simpa)

end CompleteLattice
