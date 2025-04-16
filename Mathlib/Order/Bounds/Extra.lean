/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.UpperLower.Closure

/-!
# Extra results

Further results for `upperBounds` and `lowerBounds`

-/

open Set

universe u v

variable {α : Type u} {β : Type v}
variable [Preorder α] [Preorder β]

lemma DirectedOn.fst_image_times_snd_image_subset_lowerClosure {d : Set (α × β)}
    (hd : DirectedOn (· ≤ ·) d) : (Prod.fst '' d) ×ˢ (Prod.snd '' d) ⊆ lowerClosure d :=
  fun ⟨p₁, p₂⟩ hp => by
    simp at hp
    obtain ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩ := hp
    obtain ⟨q, ⟨hq₁, ⟨⟨hq₂, _⟩, ⟨_, hq₃⟩⟩⟩⟩ := hd (p₁, r₁) hr₁ (r₂, p₂) hr₂
    exact ⟨q, ⟨hq₁, ⟨hq₂, hq₃⟩⟩⟩

lemma Monotone.upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β → γ}
    (Hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) := le_antisymm
  (Hg.upperBounds_image_subset_of_dominated
    (fun _ ha => hd.fst_image_times_snd_image_subset_lowerClosure ha))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))
