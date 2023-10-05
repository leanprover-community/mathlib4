/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Logic.Basic

/-!
# Extra facts and definitions about `MProd`
-/

universe u v

open Function

variable {α β : Type u} {α₁ : Type u} {α₂ : Type v} {β₁ : Type u} {β₂ : Type v}

namespace MProd

/--
`MProd.map f g : MProd α₁ β₁ → MProd α₂ β₂` maps across a pair
by applying `f` to the first component and `g` to the second.
-/
def map
    (f : α₁ → α₂) (g : β₁ → β₂) : MProd α₁ β₁ → MProd α₂ β₂
  | ⟨a, b⟩ => ⟨f a, g b⟩

@[simp]
theorem mk.eta {p : MProd α β} : MProd.mk p.1 p.2 = p :=
  rfl

@[simp]
theorem «forall» {p : MProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩

@[simp]
theorem «exists» {p : MProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ x : MProd α β, p x.1 x.2) ↔ ∀ a b, p a b :=
  MProd.forall

theorem exists' {p : α → β → Prop} : (∃ x : MProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  MProd.exists

end MProd

theorem Function.Injective.MProd_map {f : α₁ → α₂} {g : β₁ → β₂}
    (hf : Injective f) (hg : Injective g) :
    Injective (MProd.map f g) := fun _ _ h ↦
  have A := congr_arg MProd.fst h
  have B := congr_arg MProd.snd h
  congr_arg₂ MProd.mk (hf A) (hg B)
