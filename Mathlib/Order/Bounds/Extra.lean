/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.UpperLower.Closure

/-!
# Extra results

-/

open Function Set

open OrderDual (toDual ofDual)

universe u v

variable {α : Type u} {β : Type v}

section

variable [Preorder α] [Preorder β]

lemma prod_all_dom2 {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    (Prod.fst '' d) ×ˢ (Prod.snd '' d) ⊆ lowerClosure d :=
  fun p hp => DirectedOn.prod_all_dominated hd p hp

end

namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

include Hf in
lemma upperBounds_image_congr_of_subset {s₁ s₂ : Set α}
    (hs₁ : s₁ ⊆ s₂) (hs₂ : ∀ a ∈ s₂, ∃ b ∈ s₁, a ≤ b) :
    upperBounds (f '' s₁) = upperBounds (f '' s₂) := by
  apply upperBounds_congr_of_subset (image_mono hs₁)
  intro a ⟨c, hc⟩
  obtain ⟨d,hd⟩ := hs₂ c hc.1
  exact ⟨f d, ⟨(mem_image _ _ _).mpr ⟨d,⟨hd.1,rfl⟩⟩, le_of_eq_of_le hc.2.symm (Hf hd.2)⟩⟩

include Hf in
lemma lowerBounds_image_congr_of_subset {s₁ s₂ : Set α}
    (hs₁ : s₁ ⊆ s₂) (hs₂ : ∀ a ∈ s₂, ∃ b ∈ s₁, b ≤ a) :
    lowerBounds (f '' s₁) = lowerBounds (f '' s₂) := by
  apply lowerBounds_congr_of_subset (image_mono hs₁)
  intro a ⟨c, hc⟩
  obtain ⟨d,hd⟩ := hs₂ c hc.1
  exact ⟨f d, ⟨(mem_image _ _ _).mpr ⟨d,⟨hd.1,rfl⟩⟩, le_of_le_of_eq (Hf hd.2) hc.2⟩⟩

lemma upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β → γ}
    (Hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) :=
  Hg.upperBounds_image_congr_of_subset subset_fst_image_prod_snd_image (hd.prod_all_dominated)

end Monotone
