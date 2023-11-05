/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

notation, basic datatypes and type classes
-/
import Mathlib.Mathport.Rename
import Std.Classes.SetNotation
import Std.Classes.Dvd
import Std.Tactic.Relation.Rfl
import Std.Tactic.Relation.Symm
import Mathlib.Tactic.Relation.Trans

/-! ### alignments from lean 3 `init.core` -/

set_option autoImplicit true






-- Note: we do not currently auto-align constants.



-- TODO
-- attribute [elab_as_elim, subst] Eq.subst

attribute [refl] Eq.refl
attribute [trans] Eq.trans
attribute [symm] Eq.symm


def Prod.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂

def PProd.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion h₁ h₂












-- attribute [pp_using_anonymous_constructor] Sigma PSigma Subtype PProd And

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.

@[deprecated AndThen]
class AndThen' (α : Type u) (β : Type v) (σ : outParam <| Type w) where
  andthen : α → β → σ





attribute [simp] insert_emptyc_eq

@[deprecated] def Std.Priority.default : Nat := 1000
@[deprecated] def Std.Priority.max : Nat := 4294967295
set_option linter.deprecated false in
@[deprecated] protected def Nat.prio := Std.Priority.default + 100
@[deprecated] def Std.Prec.max : Nat := 1024
@[deprecated] def Std.Prec.arrow : Nat := 25
set_option linter.deprecated false in
@[deprecated] def Std.Prec.maxPlus : Nat := Std.Prec.max + 10



-- Combinator calculus
namespace Combinator

def I (a : α) := a
def K (a : α) (_b : β) := a
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)

end Combinator

@[deprecated] inductive BinTree (α : Type u)
  | Empty : BinTree α
  | leaf (val : α) : BinTree α
  | node (left right : BinTree α) : BinTree α

attribute [elab_without_expected_type] BinTree.node BinTree.leaf
