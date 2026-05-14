/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Restriction of a function indexed by a preorder

Given a preorder `α` and dependent function `f : (i : α) → π i` and `a : α`, one might want
to consider the restriction of `f` to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe a f`.
Similarly, if we have `a b : α`, `hab : a ≤ b` and `f : (i : ↑(Set.Iic b)) → π ↑i`,
one might want to restrict it to elements `≤ a`.
This is defined in this file as `Preorder.restrictLe₂ hab f`.

We also provide versions where the intervals are seen as finite sets, see `Preorder.frestrictLe`
and `Preorder.frestrictLe₂`.

## Main definitions
* `Preorder.restrictLe a f`: Restricts the function `f` to the variables indexed by elements `≤ a`.
-/

@[expose] public section

namespace Preorder

variable {α : Type*} [Preorder α] {π : α → Type*}

section Set

open Set

/-- Restrict domain of a function `f` indexed by `α` to elements `≤ a`. -/
def restrictLe (a : α) := (Iic a).restrict (π := π)

@[simp]
lemma restrictLe_apply (a : α) (f : (a : α) → π a) (i : Iic a) : restrictLe a f i = f i := rfl

/-- If a function `f` indexed by `α` is restricted to elements `≤ π`, and `a ≤ b`,
this is the restriction to elements `≤ a`. -/
def restrictLe₂ {a b : α} (hab : a ≤ b) := Set.restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
lemma restrictLe₂_apply {a b : α} (hab : a ≤ b) (f : (i : Iic b) → π i) (i : Iic a) :
    restrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

theorem restrictLe₂_comp_restrictLe {a b : α} (hab : a ≤ b) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe b) = restrictLe a := rfl

theorem restrictLe₂_comp_restrictLe₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (restrictLe₂ (π := π) hab) ∘ (restrictLe₂ hbc) = restrictLe₂ (hab.trans hbc) := rfl

lemma dependsOn_restrictLe (a : α) : DependsOn (restrictLe (π := π) a) (Iic a) :=
  (Iic a).dependsOn_restrict

end Set

section Finset

variable [LocallyFiniteOrderBot α]

open Finset

/-- Restrict domain of a function `f` indexed by `α` to elements `≤ a`, seen as a finite set. -/
def frestrictLe (a : α) := (Iic a).restrict (π := π)

@[simp]
lemma frestrictLe_apply (a : α) (f : (a : α) → π a) (i : Iic a) : frestrictLe a f i = f i := rfl

/-- If a function `f` indexed by `α` is restricted to elements `≤ b`, and `a ≤ b`,
this is the restriction to elements `≤ b`. Intervals are seen as finite sets. -/
def frestrictLe₂ {a b : α} (hab : a ≤ b) := restrict₂ (π := π) (Iic_subset_Iic.2 hab)

@[simp]
lemma frestrictLe₂_apply {a b : α} (hab : a ≤ b) (f : (i : Iic b) → π i) (i : Iic a) :
    frestrictLe₂ hab f i = f ⟨i.1, Iic_subset_Iic.2 hab i.2⟩ := rfl

theorem frestrictLe₂_comp_frestrictLe {a b : α} (hab : a ≤ b) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe b) = frestrictLe a := rfl

theorem frestrictLe₂_comp_frestrictLe₂ {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    (frestrictLe₂ (π := π) hab) ∘ (frestrictLe₂ hbc) = frestrictLe₂ (hab.trans hbc) := rfl

theorem piCongrLeft_comp_restrictLe {a : α} :
    ((Equiv.IicFinsetSet a).symm.piCongrLeft (fun i : Iic a ↦ π i)) ∘ (restrictLe a) =
    frestrictLe a := rfl

theorem piCongrLeft_comp_frestrictLe {a : α} :
    ((Equiv.IicFinsetSet a).piCongrLeft (fun i : Set.Iic a ↦ π i)) ∘ (frestrictLe a) =
    restrictLe a := rfl

section updateFinset

open Function

variable [DecidableEq α]

lemma frestrictLe_updateFinset_of_le {a b : α} (hab : a ≤ b) (x : Π c, π c) (y : Π c : Iic b, π c) :
    frestrictLe a (updateFinset x _ y) = frestrictLe₂ hab y :=
  restrict_updateFinset_of_subset (Iic_subset_Iic.2 hab) ..

lemma frestrictLe_updateFinset {a : α} (x : Π a, π a) (y : Π b : Iic a, π b) :
    frestrictLe a (updateFinset x _ y) = y := restrict_updateFinset ..

@[simp]
lemma updateFinset_frestrictLe (a : α) (x : Π a, π a) : updateFinset x _ (frestrictLe a x) = x := by
  simp [frestrictLe]

end updateFinset

lemma dependsOn_frestrictLe (a : α) : DependsOn (frestrictLe (π := π) a) (Set.Iic a) :=
  coe_Iic a ▸ (Finset.Iic a).dependsOn_restrict

end Finset

end Preorder
