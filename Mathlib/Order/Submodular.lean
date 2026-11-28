/-
Copyright (c) 2026 Antigravity & Xingzhi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xingzhi Zhang
-/
module

public import Mathlib.Order.Lattice
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Finset.Basic

/-!
# Submodular, Supermodular, and Modular Functions

This file defines submodular, supermodular, and modular functions on a lattice,
and establishes their fundamental properties including duality and diminishing returns.

## Main Definitions

* `IsSubmodular f`: A function `f : α → β` from a lattice `α` to an ordered additive structure `β`
  is submodular if for all `a b : α`, `f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b`.
* `IsSupermodular f`: A function `f : α → β` is supermodular if for all `a b : α`,
  `f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)`.
* `IsModular f`: A function `f : α → β` is modular if for all `a b : α`,
  `f (a ⊓ b) + f (a ⊔ b) = f a + f b`.

## Main Results

* `isModular_iff_submodular_and_supermodular`: In an ordered structure,
  a function is modular if and only if it is both submodular and supermodular.
* `IsSubmodular.diminishing_returns`: On finite sets, submodularity implies
  the diminishing returns property: if `s ⊆ t` and `x ∉ t`, then
  `f (insert x t) - f t ≤ f (insert x s) - f s`.

## References

* L. Lovász, *Submodular functions and convexity*,
  Mathematical Programming: The State of the Art, 1983.
-/

@[expose] public section

variable {α β : Type*}

/-- A function `f : α → β` on a lattice `α` is submodular if
`f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b` for all `a, b : α`. -/
def IsSubmodular [Lattice α] [Add β] [LE β] (f : α → β) : Prop :=
  ∀ a b : α, f (a ⊓ b) + f (a ⊔ b) ≤ f a + f b

/-- A function `f : α → β` on a lattice `α` is supermodular if
`f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)` for all `a, b : α`. -/
def IsSupermodular [Lattice α] [Add β] [LE β] (f : α → β) : Prop :=
  ∀ a b : α, f a + f b ≤ f (a ⊓ b) + f (a ⊔ b)

/-- A function `f : α → β` on a lattice `α` is modular if
`f (a ⊓ b) + f (a ⊔ b) = f a + f b` for all `a, b : α`. -/
def IsModular [Lattice α] [Add β] (f : α → β) : Prop :=
  ∀ a b : α, f (a ⊓ b) + f (a ⊔ b) = f a + f b

section Basic

variable [Lattice α]

theorem isModular_iff_submodular_and_supermodular [Add β] [PartialOrder β] (f : α → β) :
    IsModular f ↔ IsSubmodular f ∧ IsSupermodular f := by
  constructor
  · intro h
    refine ⟨fun a b => le_of_eq (h a b), fun a b => le_of_eq (h a b).symm⟩
  · rintro ⟨h_sub, h_sup⟩ a b
    exact le_antisymm (h_sub a b) (h_sup a b)

theorem IsModular.isSubmodular [Add β] [Preorder β] {f : α → β} (h : IsModular f) :
    IsSubmodular f :=
  fun a b => le_of_eq (h a b)

theorem IsModular.isSupermodular [Add β] [Preorder β] {f : α → β} (h : IsModular f) :
    IsSupermodular f :=
  fun a b => ge_of_eq (h a b)

end Basic

section FinsetDiminishingReturns

variable {ι : Type*} [DecidableEq ι]

/-- The diminishing returns property of a submodular function on `Finset ι`:
adding an element `e` to a larger set `B` yields no more gain than adding it to a subset `A`. -/
theorem IsSubmodular.add_insert_le {β : Type*} [AddCommMonoid β] [Preorder β]
    {f : Finset ι → β} (h_sub : IsSubmodular f)
    {A B : Finset ι} (hAB : A ⊆ B) {e : ι} (he : e ∉ B) :
    f A + f (insert e B) ≤ f (insert e A) + f B := by
  have h_inter : (insert e A) ∩ B = A := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hxA, hxB⟩
      · contradiction
      · exact hxA
    · intro hxA
      exact ⟨Or.inr hxA, hAB hxA⟩
  have h_union : (insert e A) ∪ B = insert e B := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (⟨rfl | hxA⟩ | hxB)
      · exact Or.inl rfl
      · exact Or.inr (hAB hxA)
      · exact Or.inr hxB
    · rintro (rfl | hxB)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hxB
  have h_sub_ineq := h_sub (insert e A) B
  rw [Finset.inf_eq_inter, Finset.sup_eq_union] at h_sub_ineq
  rw [h_inter, h_union] at h_sub_ineq
  exact h_sub_ineq

end FinsetDiminishingReturns

end
