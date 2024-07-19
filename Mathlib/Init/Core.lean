/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Relation.Trans

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Notation, basic datatypes and type classes

This file contains alignments from lean 3 `init.core`.
-/

-- Note: we do not currently auto-align constants.

-- TODO
-- attribute [elab_as_elim, subst] Eq.subst

attribute [trans] Eq.trans
attribute [symm] Eq.symm

universe u v w

def Prod.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂

def PProd.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂

-- attribute [pp_using_anonymous_constructor] Sigma PSigma Subtype PProd And

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.

attribute [simp] insert_emptyc_eq

-- Combinator calculus
namespace Combinator

variable {α : Sort u} {β : Sort v} {γ : Sort w}
def I (a : α) := a
def K (a : α) (_b : β) := a
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

end Combinator
