/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.ULift

/-!
# Finiteness of `Set.range`

## Implementation notes

Each result in this file should come in three forms: a `Fintype` instance, a `Finite` instance
and a `Set.Finite` constructor.

## Tags

finite sets
-/

public section

assert_not_exists IsOrderedRing MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-! ### Fintype instances

Every instance here should have a corresponding `Set.Finite` constructor in the next section.
-/

section FintypeInstances

instance fintypeRange [DecidableEq α] (f : ι → α) [Fintype (PLift ι)] : Fintype (range f) :=
  Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) <| by simp

end FintypeInstances

end Set

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `Fintype` instances
in `Data.Set.Finite`. While every `Fintype` instance gives a `Finite` instance, those
instances that depend on `Fintype` or `Decidable` instances need an additional `Finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`Subtype.Finite` for subsets of a finite type.
-/


namespace Finite.Set

instance finite_range (f : ι → α) [Finite ι] : Finite (range f) := by
  classical
  have := Fintype.ofFinite (PLift ι)
  infer_instance

instance finite_replacement [Finite α] (f : α → β) :
    Finite {f x | x : α} :=
  Finite.Set.finite_range f

end Finite.Set

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

theorem finite_range (f : ι → α) [Finite ι] : (range f).Finite :=
  toFinite _

theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : ∀ i ∈ s, β) :
    {y : β | ∃ x hx, F x hx = y}.Finite := by
  have := hs.to_subtype
  simpa [range] using finite_range fun x : s => F x x.2

end SetFiniteConstructors

lemma Finite.exists_subset_finite_image_eq {f : α → β} {s : Set α} {u : Set β}
    (hu : u.Finite) (hsu : u ⊆ f '' s) :
    ∃ᵉ (t ⊆ s) (_ : t.Finite), f '' t = u := by
  have : Finite u := Finite.to_subtype hu
  choose g hg hg' using hsu
  let g' (x : u) : α := g x.property
  exact ⟨range g', fun a ha ↦ by aesop, finite_range _, by aesop⟩

/-- If an injective function from a finite domain has a different range from another function, then
the range of the first contains an element not in the range of the second. -/
lemma _root_.Function.Injective.exists_not_mem_range_of_range_ne {α γ : Type*} [Finite α]
    {f g : α → γ} (hf : Function.Injective f) (h : range f ≠ range g) : ∃ i, f i ∉ range g := by
  classical
  have := Fintype.ofFinite α
  by_contra! h_sub
  have : range f ⊆ range g := range_subset_iff.mpr h_sub
  grind [eq_of_subset_of_card_le, card_range_of_injective, Fintype.card_range_le]

end Set
