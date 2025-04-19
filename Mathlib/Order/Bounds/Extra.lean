/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Prod

/-!
# Extra results

Further results for `upperBounds` and `lowerBounds`

-/

open Set

universe u v

variable {α : Type u} {β : Type v}
variable [Preorder α] [Preorder β] {f : α → β}

lemma Dominated.image_of_monotone {s₁ s₂ : Set α} (h : Dominated s₁ s₂) (Hf : Monotone f) :
    Dominated (f '' s₁) (f '' s₂) := fun a ha => by
  obtain ⟨c, hcs, hcfa⟩ := ha
  obtain ⟨d, hdd, hcd⟩ := h c hcs
  simp only [mem_image, exists_exists_and_eq_and]
  rw [← hcfa]
  exact ⟨d, ⟨hdd, Hf hcd⟩⟩

lemma Dominated.image_of_antitone {s₁ s₂ : Set α} (h : Dominated s₁ s₂) (Hf : Antitone f) :
    Codominated (f '' s₁) (f '' s₂) := fun a ha => by
  obtain ⟨c, hcs, hcfa⟩ := ha
  obtain ⟨d, hdd, hcd⟩ := h c hcs
  simp only [mem_image, exists_exists_and_eq_and]
  rw [← hcfa]
  exact ⟨d, ⟨hdd, Hf hcd⟩⟩

lemma Codominated.image_of_monotone {s₁ s₂ : Set α} (h : Codominated s₁ s₂) (Hf : Monotone f) :
    Codominated (f '' s₁) (f '' s₂) := fun a ha => by
  obtain ⟨c, hcs, hcfa⟩ := ha
  obtain ⟨d, hdd, hcd⟩ := h c hcs
  simp only [mem_image, exists_exists_and_eq_and]
  rw [← hcfa]
  exact ⟨d, ⟨hdd, Hf hcd⟩⟩

lemma Codominated.image_of_antitone {s₁ s₂ : Set α} (h : Codominated s₁ s₂) (Hf : Antitone f) :
    Dominated (f '' s₁) (f '' s₂) := fun a ha => by
  obtain ⟨c, hcs, hcfa⟩ := ha
  obtain ⟨d, hdd, hcd⟩ := h c hcs
  simp only [mem_image, exists_exists_and_eq_and]
  rw [← hcfa]
  exact ⟨d, ⟨hdd, Hf hcd⟩⟩

lemma DirectedOn.dominated_fst_image_times_snd_image {d : Set (α × β)}
    (hd : DirectedOn (· ≤ ·) d) : Dominated ((Prod.fst '' d) ×ˢ (Prod.snd '' d)) d :=
  fun ⟨p₁, p₂⟩ hp => by
    simp at hp
    obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hp
    obtain ⟨q, ⟨hq₁, ⟨⟨hq₂, _⟩, ⟨_, hq₃⟩⟩⟩⟩ := hd (p₁, r₁) hr₁ (r₂, p₂) hr₂
    exact ⟨q, ⟨hq₁, ⟨hq₂, hq₃⟩⟩⟩

lemma Monotone.upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β → γ}
    (Hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) := le_antisymm
  (upperBounds_mono_of_dominated
    (fun _ ha => (Dominated.image_of_monotone hd.dominated_fst_image_times_snd_image Hg) _ ha))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))
