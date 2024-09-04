/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Finset.Basic

/-!
# Restriction of a function indexed by natural integers

Given a preorder `α` and dependent function `f : (i : α) → β i` and `a : α`, one might want
to consider the restriction of `f` to elements `≤ a`.
This is defined in this file as `Prerder.restrict a f`.
Similarly, if we have `a b : α`, `hab : a ≤ b` and `f : (i : ↑(Set.Iic b)) → β ↑i`,
one might want to restrict it to elements `≤ a`.
This is defined in this file as `Preorder.restrict₂ hab f`.

We also provide versions where the intervals are seen as finite sets, see `Preorder.frestrict`
and `Preorder.frestrict₂`.

## Main definitions
* `Preorder.restrict a f`: Restricts the function `f` to the variables indexed by elements `≤ a`.
-/

namespace Preorder

variable {α : Type*} [Preorder α] {β : α → Type*}

section Set

open Set

/-- Restrict domain of a function `f` indexed by `α` to elements `≤ a`. -/
def restrict (a : α) := (Iic a).restrict (π := β)

@[simp]
lemma restrict_def (a : α) (f : (a : α) → β a) (i : Iic a) : restrict a f i = f i := rfl

/-- If a function `f` indexed by `α` is restricted to elements `≤ β`, and `a ≤ b`,
this is the restriction to elements `≤ a`. -/
def restrict₂ {a b : α} (hab : a ≤ b) := Set.restrict₂ (π := β) (Iic_subset_Iic.2 hab)

@[simp]
lemma restrict₂_def {a b : α} (hab : a ≤ b) (f : (i : Iic b) → β i) (i : Iic a) :
    restrict₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

theorem restrict₂_comp_restrict {a b : α} (hab : a ≤ b) :
    (restrict₂ (β := β) hab) ∘ (restrict b) = restrict a := rfl

theorem restrict₂_comp_restrict₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (restrict₂ (β := β) hab) ∘ (restrict₂ hbc) = restrict₂ (hab.trans hbc) := rfl

end Set

section Finset

variable [LocallyFiniteOrderBot α]

open Finset

/-- Restrict domain of a function `f` indexed by `α` to elements `≤ α`, seen as a finite set. -/
def frestrict (a : α) := (Iic a).restrict (β := β)

@[simp]
lemma frestrict_def (a : α) (f : (a : α) → β a) (i : Iic a) : frestrict a f i = f i := rfl

/-- If a function `f` indexed by `α` is restricted to elements `≤ b`, and `a ≤ b`,
this is the restriction to elements `≤ b`. Intervals are seen as finite sets. -/
def frestrict₂ {a b : α} (hab : a ≤ b) := Finset.restrict₂ (β := β) (Iic_subset_Iic.2 hab)

@[simp]
lemma frestrict₂_def {a b : α} (hab : a ≤ b) (f : (i : Iic b) → β i) (i : Iic a) :
    frestrict₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

theorem frestrict₂_comp_frestrict {a b : α} (hab : a ≤ b) :
    (frestrict₂ (β := β) hab) ∘ (frestrict b) = frestrict a := rfl

theorem frestrict₂_comp_frestrict₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (frestrict₂ (β := β) hab) ∘ (frestrict₂ hbc) = frestrict₂ (hab.trans hbc) := rfl

end Finset

end Preorder
