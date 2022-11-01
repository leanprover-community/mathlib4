/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

notation, basic datatypes and type classes
-/
import Mathlib.Mathport.Rename
import Std.Classes.SetNotation

/-! ### alignments from lean 3 `init.core` -/

#align id id -- align this first so idDelta doesn't take priority
#align idDelta id

#align opt_param optParam
#align out_param outParam

#align idRhs id
#align punit PUnit
#align punit.star PUnit.unit
#align unit.star Unit.unit

#align thunk Thunk'

-- Note: we do not currently auto-align constants.
#align quot Quot
#align quot.mk Quot.mk
#align quot.lift Quot.lift
#align quot.ind Quot.ind

#align heq HEq
#align pprod PProd

#align and.left And.left
#align and.right And.right
#align and.elim_left And.left
#align and.elim_right And.right

-- TODO
-- attribute [refl] Eq.refl
-- attribute [elab_as_elim, subst] Eq.subst
-- attribute [trans] Eq.trans
-- attribute [symm] Eq.symm

def Prod.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ => Prod.noConfusion h₁ h₂

def PProd.mk.injArrow {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort w⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ => Prod.noConfusion h₁ h₂

#align psum PSum
#align or.intro_right Or.intro_rightₓ -- reorder implicits
#align psigma PSigma

#align bool.ff Bool.false
#align bool.tt Bool.true

-- attribute [pp_using_anonymous_constructor] Sigma PSigma Subtype PProd And

-- Generic 'has'-stripping
-- Note: we don't currently strip automatically for various reasons.
#align has_add Add
#align has_mul Mul
#align has_neg Neg
#align has_sub Sub
#align has_div Div
#align has_dvd Dvd
#align has_mod Mod
#align has_le LE
#align has_le.le LE.le
#align has_lt LT
#align has_lt.lt LT.lt
#align has_append Append
#align has_andthen AndThen'

@[deprecated AndThen]
class AndThen' (α : Type u) (β : Type v) (σ : outParam <| Type w) where
  andthen : α → β → σ

#align has_union Union
#align has_equiv HasEquivₓ -- universe levels don't match
#align has_inter Inter
#align has_sdiff Sdiff

#align has_subset HasSubset
#align has_subset.subset HasSubset.Subset
#align has_ssubset HasSSubset
#align has_ssubset.ssubset HasSSubset.SSubset
#align has_emptyc EmptyCollection
#align has_emptyc.emptyc EmptyCollection.emptyCollection
#align has_insert Insert
#align has_singleton Singleton
#align has_sep Sep
#align has_mem Membership
#align has_pow Pow

#align gt GT.gt
#align ge GE.ge

#align is_lawful_singleton LawfulSingleton

attribute [simp] insert_emptyc_eq

@[deprecated] def Std.Priority.default : Nat := 1000
@[deprecated] def Std.Priority.max : Nat := 4294967295
@[deprecated] protected def Nat.prio := Std.Priority.default + 100
@[deprecated] def Std.Prec.max : Nat := 1024
@[deprecated] def Std.Prec.arrow : Nat := 25
@[deprecated] def Std.Prec.maxPlus : Nat := Std.Prec.max + 10

#align has_sizeof SizeOf
#align has_sizeof.sizeof SizeOf.sizeOf
#align sizeof SizeOf.sizeOf

#align nat_add_zero Nat.add_zero

-- Combinator calculus
namespace Combinator

def I (a : α) := a
def K (a : α) (_b : β) := a
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
#align combinator.I Combinator.I
#align combinator.K Combinator.K
#align combinator.S Combinator.S

end Combinator

@[deprecated] inductive BinTree (α : Type u)
  | Empty : BinTree α
  | leaf (val : α) : BinTree α
  | node (left right : BinTree α) : BinTree α

attribute [elab_without_expected_type] BinTree.node BinTree.leaf
