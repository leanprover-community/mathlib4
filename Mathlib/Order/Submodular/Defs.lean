/-
Copyright (c) 2026 Alberto Schiabel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alberto Schiabel
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.Lattice

/-!
# Submodular, supermodular, and modular functions

This file defines submodular, supermodular, and modular functions on a lattice, as well as their
restrictions to a subset of the domain.

## Main definitions

* `Submodular f`: A function `f : α → β` on a lattice is submodular if
  `f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b` for all `a, b : α`.
* `Supermodular f`: A function `f : α → β` on a lattice is supermodular if
  `f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)` for all `a, b : α`.
* `Modular f`: A function `f : α → β` on a lattice is modular if
  `f (a ⊓ b) + f (a ⊔ b) = f a + f b` for all `a, b : α`.
* `SubmodularOn f s`, `SupermodularOn f s`, `ModularOn f s`: The corresponding properties
  restricted to pairs `a, b ∈ s`.

## Main results

* `modular_iff_submodular_and_supermodular`: A function into a partial order is modular if and only
  if it is both submodular and supermodular.
* `modularOn_iff_submodularOn_and_supermodularOn`: The corresponding equivalence on a subset `s`.

## References

* L. Lovász, *Submodular functions and convexity*
* S. Fujishige, *Submodular Functions and Optimization*

## Tags

submodular, supermodular, modular, lattice, valuation
-/

public section

universe u v

variable {α : Type u} {β : Type v}

section Defs

variable [Lattice α] [Add β]

/-- A function `f : α → β` on a lattice is *submodular* if
`f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b` for all `a, b : α`. -/
@[expose] def Submodular [Preorder β] (f : α → β) : Prop :=
  ∀ a b, f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b

/-- A function `f : α → β` on a lattice is *supermodular* if
`f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)` for all `a, b : α`. -/
@[expose] def Supermodular [Preorder β] (f : α → β) : Prop :=
  ∀ a b, f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)

/-- A function `f : α → β` on a lattice is *modular* (also called a *valuation*) if
`f (a ⊓ b) + f (a ⊔ b) = f a + f b` for all `a, b : α`. -/
@[expose] def Modular (f : α → β) : Prop :=
  ∀ a b, f (a ⊓ b) + f (a ⊔ b) = f a + f b

/-- A function `f : α → β` on a lattice is *submodular on `s`* if
`f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b` for all `a, b ∈ s`. -/
@[expose] def SubmodularOn [Preorder β] (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b

/-- A function `f : α → β` on a lattice is *supermodular on `s`* if
`f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)` for all `a, b ∈ s`. -/
@[expose] def SupermodularOn [Preorder β] (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)

/-- A function `f : α → β` on a lattice is *modular on `s`* if
`f (a ⊓ b) + f (a ⊔ b) = f a + f b` for all `a, b ∈ s`. -/
@[expose] def ModularOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → f (a ⊓ b) + f (a ⊔ b) = f a + f b

end Defs

section Basic

variable [Lattice α] [Add β] {f : α → β} {s t : Set α}

@[simp]
theorem submodularOn_univ [Preorder β] : SubmodularOn f Set.univ ↔ Submodular f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h a _ b _ ↦ h a b⟩

@[simp]
theorem supermodularOn_univ [Preorder β] : SupermodularOn f Set.univ ↔ Supermodular f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h a _ b _ ↦ h a b⟩

@[simp]
theorem modularOn_univ : ModularOn f Set.univ ↔ Modular f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h a _ b _ ↦ h a b⟩

theorem Submodular.submodularOn [Preorder β] (hf : Submodular f) (s : Set α) :
    SubmodularOn f s :=
  fun a _ b _ ↦ hf a b

theorem Supermodular.supermodularOn [Preorder β] (hf : Supermodular f) (s : Set α) :
    SupermodularOn f s :=
  fun a _ b _ ↦ hf a b

theorem Modular.modularOn (hf : Modular f) (s : Set α) : ModularOn f s :=
  fun a _ b _ ↦ hf a b

theorem SubmodularOn.mono [Preorder β] (hf : SubmodularOn f s) (h : t ⊆ s) : SubmodularOn f t :=
  fun _ ha _ hb ↦ hf (h ha) (h hb)

theorem SupermodularOn.mono [Preorder β] (hf : SupermodularOn f s) (h : t ⊆ s) :
    SupermodularOn f t :=
  fun _ ha _ hb ↦ hf (h ha) (h hb)

theorem ModularOn.mono (hf : ModularOn f s) (h : t ⊆ s) : ModularOn f t :=
  fun _ ha _ hb ↦ hf (h ha) (h hb)

theorem Modular.submodular [Preorder β] (hf : Modular f) : Submodular f :=
  fun a b ↦ le_of_eq (hf a b)

theorem Modular.supermodular [Preorder β] (hf : Modular f) : Supermodular f :=
  fun a b ↦ ge_of_eq (hf a b)

theorem ModularOn.submodularOn [Preorder β] (hf : ModularOn f s) : SubmodularOn f s :=
  fun _ ha _ hb ↦ le_of_eq (hf ha hb)

theorem ModularOn.supermodularOn [Preorder β] (hf : ModularOn f s) : SupermodularOn f s :=
  fun _ ha _ hb ↦ ge_of_eq (hf ha hb)

theorem modular_iff_submodular_and_supermodular [PartialOrder β] :
    Modular f ↔ Submodular f ∧ Supermodular f :=
  ⟨fun h ↦ ⟨h.submodular, h.supermodular⟩,
    fun ⟨h₁, h₂⟩ a b ↦ le_antisymm (h₁ a b) (h₂ a b)⟩

theorem modularOn_iff_submodularOn_and_supermodularOn [PartialOrder β] :
    ModularOn f s ↔ SubmodularOn f s ∧ SupermodularOn f s :=
  ⟨fun h ↦ ⟨h.submodularOn, h.supermodularOn⟩,
    fun ⟨h₁, h₂⟩ _ ha _ hb ↦ le_antisymm (h₁ ha hb) (h₂ ha hb)⟩

end Basic
